"""
Verification of a one-shot ECPP, written by Opus 4.8 Max under the
supervision of Andrew V. Sutherland.

A one-shot ECPP is a quadruple (p, A, x0, m) with:
  - p   : the integer being proved prime
  - A   : Montgomery coefficient of  E : y^2 = x^3 + A x^2 + x   over Z/pZ
  - x0  : x-coordinate of a point P on E (the y-coordinate and B are not needed)
  - m   : an n^2-smooth integer, n = bitlength(p), with m equal to ord(P)

It proves p prime by establishing that ord(P) = m exactly modulo every prime
divisor of p, together with the bound m > (p^{1/4}+1)^2.  If p were composite
with least prime factor l <= sqrt(p), then m | #E_l(F_l) <= (sqrt(l)+1)^2
<= (p^{1/4}+1)^2 < m, a contradiction.

Target cost (FFT integer multiplication assumed):
  O(n^2 (log n)^2) bit operations and O(n^2) bits of memory.
"""

from math import gcd, isqrt


# --------------------------------------------------------------------------
# Montgomery x-only (X:Z) arithmetic on  E : y^2 = x^3 + A x^2 + x  over Z/pZ.
# Formulas depend only on A; valid on the Kummer line of E and of its twist,
# so no on-curve test of x0 is required.
# --------------------------------------------------------------------------
def xdbl(X, Z, A, p):
    """[2](X:Z).  X' = (X^2-Z^2)^2 ;  Z' = 4 X Z (X^2 + A X Z + Z^2)."""
    XX = X * X % p
    ZZ = Z * Z % p
    XZ = X * Z % p
    X2 = (XX - ZZ) * (XX - ZZ) % p
    Z2 = 4 * XZ % p * ((XX + A * XZ + ZZ) % p) % p
    return X2, Z2


def xadd(X1, Z1, X2, Z2, Xd, Zd, p):
    """Differential addition (X1:Z1)+(X2:Z2) with known difference (Xd:Zd).
    Independent of A; the difference point may be unnormalized (Zd != 1)."""
    a = (X1 - Z1) * (X2 + Z2) % p
    b = (X1 + Z1) * (X2 - Z2) % p
    s = (a + b) % p
    d = (a - b) % p
    X3 = Zd * (s * s % p) % p
    Z3 = Xd * (d * d % p) % p
    return X3, Z3


def ladder(k, XP, ZP, A, p):
    """Montgomery ladder: returns (X:Z) of k*P for P = (XP:ZP) projective.
    Maintains (R0,R1) = (jP,(j+1)P) so the difference is always P; never
    feeds the point at infinity to xadd."""
    if k == 0:
        return (1, 0)                      # O = (1:0)
    XP %= p
    ZP %= p
    if k == 1:
        return (XP, ZP)
    Xd, Zd = XP, ZP                        # fixed difference point P
    X0, Z0 = XP, ZP                        # 1*P
    X1, Z1 = xdbl(XP, ZP, A, p)            # 2*P
    for bit in bin(k)[3:]:                 # bits below the leading 1, MSB->LSB
        if bit == '0':
            X1, Z1 = xadd(X0, Z0, X1, Z1, Xd, Zd, p)
            X0, Z0 = xdbl(X0, Z0, A, p)
        else:
            X0, Z0 = xadd(X0, Z0, X1, Z1, Xd, Zd, p)
            X1, Z1 = xdbl(X1, Z1, A, p)
    return X0, Z0


# --------------------------------------------------------------------------
# Step 1: smoothness test and prime-divisor extraction.
# --------------------------------------------------------------------------
def sieve_primes(limit):
    """All primes <= limit via a single (unsegmented) bitmap.  O(limit) bits."""
    if limit < 2:
        return []
    is_p = bytearray([1]) * (limit + 1)
    is_p[0] = is_p[1] = 0
    for i in range(2, isqrt(limit) + 1):
        if is_p[i]:
            is_p[i * i::i] = bytearray(len(is_p[i * i::i]))
    return [i for i in range(2, limit + 1) if is_p[i]]


def remainder_tree(x, mods):
    """[x % mod for mod in mods] via one product tree and a descent.
    Pads to a power of two with 1's (x % 1 == 0, sliced off at the end).
    Cost O(M(B) log k), memory O(B log k) bits, B = total size of the mods."""
    if not mods:
        return []
    k = len(mods)
    size = 1
    while size < k:
        size <<= 1
    levels = [list(mods) + [1] * (size - k)]
    while len(levels[-1]) > 1:
        cur = levels[-1]
        levels.append([cur[i] * cur[i + 1] for i in range(0, len(cur), 2)])
    rems = [x % levels[-1][0]]
    for lvl in range(len(levels) - 2, -1, -1):
        cur = levels[lvl]
        rems = [rems[i >> 1] % cur[i] for i in range(len(cur))]
    return rems[:k]


def prime_divisors(m, primes, batch_bits):
    """Distinct primes (from `primes`) dividing m, found with batched
    remainder trees.  Primes are grouped so each batch product has ~batch_bits
    bits (comparable to m); m is reduced modulo the batch product once, then a
    remainder tree splits that down to each prime.  One batch is resident at a
    time, so memory stays O(sieve) = O(n^2) bits."""
    out = []
    batch = []
    bits = 0
    for q in primes:
        batch.append(q)
        bits += q.bit_length()
        if bits >= batch_bits:
            Q = 1
            for t in batch:
                Q *= t
            out += [q for q, r in zip(batch, remainder_tree(m % Q, batch)) if r == 0]
            batch, bits = [], 0
    if batch:
        Q = 1
        for t in batch:
            Q *= t
        out += [q for q, r in zip(batch, remainder_tree(m % Q, batch)) if r == 0]
    return out


def is_smooth(m, divisors):
    """True iff every prime factor of m lies among `divisors`.

    R = prod(divisors) is squarefree, so for any prime q | m we have
    v_q(R^N) = N if q | R and 0 otherwise.  Hence  m | R^N  iff every prime of m
    divides R and N >= max_q v_q(m).  The largest prime-power exponent of m is at
    most log2(m), so N = 2^ceil(log2 m) suffices: square R mod m  ceil(log2 m)
    times and test for 0.  No GCD.  (R = 1 gives 1 mod m, which is 0 iff m = 1,
    so the empty-divisor / m = 1 cases are handled with no special-casing.)"""
    R = 1
    for q in divisors:
        R *= q
    R %= m
    for _ in range((m - 1).bit_length()):       # ceil(log2 m) squarings
        R = R * R % m
    return R == 0


# --------------------------------------------------------------------------
# Step 2: order check.  After Q := (m/r)P, every leaf of the recursion holds
# (r/q)Q = (m/q)P, whose z-coordinate must be a unit mod p.  Each level multiplies
# by half the remaining primes, so the total scalar size per level is log r;
# with O(log t) levels the elliptic work is O(n M(n) log n) = O(n^2 (log n)^2).
# --------------------------------------------------------------------------
def check_orders(XQ, ZQ, primes, A, p):
    t = len(primes)
    if t == 0:
        return True
    if t == 1:
        return gcd(ZQ % p, p) == 1            # (m/q)P must not be O mod any l|p
    mid = t // 2
    L, Rr = primes[:mid], primes[mid:]
    hL = 1
    for q in L:
        hL *= q
    hR = 1
    for q in Rr:
        hR *= q
    XL, ZL = ladder(hL, XQ, ZQ, A, p)         # multiply in the first half, recurse on the second
    XR, ZR = ladder(hR, XQ, ZQ, A, p)         # multiply in the second half, recurse on the first
    return check_orders(XL, ZL, Rr, A, p) and check_orders(XR, ZR, L, A, p)


# --------------------------------------------------------------------------
# Top-level verifier.
# --------------------------------------------------------------------------
def verify(p, A, x0, m):
    """Return True iff (p, A, x0, m) is a valid generalized Pomerance certificate
    (and hence p is prime).

    A and x0 must already be reduced: 0 <= A < p and 0 <= x0 < p (out-of-range
    inputs return False rather than being reduced mod p).  m must lie below the
    Hasse bound, m < p + 1 + 2 sqrt(p), since m = ord(P) divides #E(F_p)."""
    if p <= 3 or p % 2 == 0:       # a valid certificate requires an odd prime p > 3
        return False               # (Montgomery form needs char != 2,3; the proof needs p > 3)
    if not (0 <= A < p) or not (0 <= x0 < p):   # require canonical inputs; do not reduce silently
        return False

    # (i) size: m must exceed the largest possible point order over F_q, q <= isqrt(p),
    #     and cannot exceed the Hasse bound  #E(F_p) <= p + 1 + floor(2 sqrt p)  since m | #E.
    #     #E(F_q) <= q + 1 + floor(2 sqrt q) = q + 1 + isqrt(4q), increasing in q.
    sp = isqrt(p)
    if m <= sp + 1 + isqrt(4 * sp):
        return False
    if m > p + 1 + isqrt(4 * p):
        return False

    # (ii) E is nonsingular modulo every prime divisor of p.
    if gcd((A * A - 4) % p, p) != 1:
        return False

    # (iii) m is n^2-smooth; collect its prime divisors.
    n = p.bit_length()
    primes = sieve_primes(n * n)
    divisors = prime_divisors(m, primes, batch_bits=max(64, m.bit_length()))
    if not is_smooth(m, divisors):
        return False

    # (iv) m*P = O, reached as the genuine point at infinity (X:0) with X a unit.
    #      If the ladder ever multiplies past ord(P) modulo some prime l | p it
    #      runs xADD(O, .) and collapses to the degenerate (0:0), which then makes
    #      Z = 0 spuriously.  Requiring gcd(X, p) = 1 rejects that collapse (and for
    #      composite p exposes a factor); this is what makes step (iv) sound.  A
    #      corrupt leaf in step (v) is already caught: (0:0) has Z = 0, failing the
    #      unit test there, so only this check needed strengthening.
    Xm, Zm = ladder(m, x0, 1, A, p)
    if Zm % p != 0 or gcd(Xm % p, p) != 1:
        return False

    # (v) (m/q)*P != O for every prime q | m, via the divide-and-conquer tree.
    r = 1
    for q in divisors:
        r *= q
    XQ, ZQ = ladder(m // r, x0, 1, A, p)       # Q = (m/r) P
    return check_orders(XQ, ZQ, divisors, A, p)


if __name__ == "__main__":
    import sys

    args = sys.argv[1:]
    if args == ["--test"]:
        assert verify(101, 3, 24, 24) is True     # 101 prime; P=(24,*) has order 24 = 2^3*3 > 17
        assert verify(1003, 3, 24, 24) is False   # 1003 = 17 * 59
        assert verify(2, 0, 0, 1) is False        # p must be an odd prime > 3
        assert verify(3, 0, 0, 4) is False        # ditto
        assert verify(101, 104, 24, 24) is False  # A not in [0, p)  (not reduced)
        assert verify(101, 3, 125, 24) is False   # x0 not in [0, p)
        assert verify(101, 3, 24, 123) is False   # m exceeds p + 1 + floor(2 sqrt p) = 122
        print("ok")
        sys.exit(0)

    if len(args) != 4:
        sys.stderr.write("usage: python pomerance_smooth.py <p> <A> <x0> <m>\n"
                         "       python pomerance_smooth.py --test\n")
        sys.exit(2)
    try:
        p, A, x0, m = (int(a, 0) for a in args)   # decimal or 0x-hex
    except ValueError:
        sys.stderr.write("error: p, A, x0, m must be integers\n")
        sys.exit(2)

    result = verify(p, A, x0, m)
    print(result)
    sys.exit(0 if result else 1)
