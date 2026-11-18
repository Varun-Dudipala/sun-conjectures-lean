"""Numeric test of every identity stated in PROOF_A189286.md and PROOF_A208425.md.

This is a sanity check on the write-ups, not a proof. The proofs are the Lean files.
Run:  python3 check_identities.py
"""
from fractions import Fraction
from math import comb, factorial

ok = True


def check(name, cond):
    global ok
    ok &= bool(cond)
    print(("ok   " if cond else "FAIL ") + name)


def digits(n, b):
    s = 0
    while n:
        s += n % b
        n //= b
    return s


def val(n, p):
    v = 0
    while n % p == 0:
        n //= p
        v += 1
    return v


# ---------------------------------------------------------------- A189286
T = lambda k: comb(6 * k, 3 * k) * comb(3 * k, k)
Tz = lambda k: T(k) if k >= 0 else 0
N = lambda n: sum(T(k) * T(n - k) for k in range(n + 1))
D = lambda n: (2 * n - 1) * comb(3 * n, n)
R = range(1, 121)

check("A189286 (1.1) T(k) = (6k)!/((3k)!(2k)!k!)",
      all(T(k) * factorial(3 * k) * factorial(2 * k) * factorial(k) == factorial(6 * k) for k in range(40)))
check("A189286 (1.2) C(2n,n) = 2(2n-1)Cat(n-1)",
      all(comb(2 * n, n) == 2 * (2 * n - 1) * comb(2 * n - 2, n - 1) // n and comb(2 * n - 2, n - 1) % n == 0 for n in R))
check("A189286 (1.3) v3(T(k)) = s3(k)", all(val(T(k), 3) == digits(k, 3) for k in range(1, 150)))
check("A189286 (1.3) v3(C(2n,n)C(3n,n)) = s3(n)", all(val(comb(2 * n, n) * comb(3 * n, n), 3) == digits(n, 3) for n in R))


def g(x, m):          # contribution of modulus m to v_p(T(j)) when j = x mod m
    return (1 if 2 * ((3 * x) % m) >= m else 0) + (1 if x + (2 * x) % m >= m else 0)


def g_closed(x, m):   # the closed form used in the text
    return 0 if 6 * x < m else (2 if 6 * x >= 5 * m else 1)


good = True
closed = True
for m in range(2, 90):
    for x in range(m):
        closed &= g(x, m) == g_closed(x, m)
        for y in range(m):
            r = (x + y) % m
            divides = (2 * r - 1) % m == 0
            if divides and m < 5:
                continue                      # excluded: only p >= 5 can divide 2n-1 here
            lhs = (1 if divides else 0) + (1 if r + (2 * r) % m >= m else 0)
            good &= lhs <= g(x, m) + g(y, m)
check("A189286 (1.4) closed form of g", closed)
check("A189286 (1.4) per-modulus inequality, all residues, m < 90", good)
check("A189286 Step 1: D(n) divides every T(k)T(n-k)", all(T(k) * T(n - k) % D(n) == 0 for n in range(1, 60) for k in range(n + 1)))
check("A189286 (2.1) (k+1)^2 T(k+1) = 12(6k+1)(6k+5) T(k)",
      all((k + 1) ** 2 * T(k + 1) == 12 * (6 * k + 1) * (6 * k + 5) * T(k) for k in range(60)))


def G(n, k):
    return (2 * k - 3 * (n + 2)) * k ** 2 * Tz(k) * Tz(n + 2 - k) + 432 * (3 * n + 4 - 2 * k) * k ** 2 * Tz(k) * Tz(n + 1 - k)


def summand(n, k):
    return ((n + 2) ** 3 * Tz(k) * Tz(n + 2 - k)
            - 24 * (2 * n + 3) * (18 * n * n + 54 * n + 41) * Tz(k) * Tz(n + 1 - k)
            + 20736 * (n + 1) * (3 * n + 1) * (3 * n + 5) * Tz(k) * Tz(n - k))


check("A189286 (2.2) certificate: summand(n,k) = G(n,k+1) - G(n,k)",
      all(summand(n, k) == G(n, k + 1) - G(n, k) for n in range(0, 30) for k in range(0, n + 4)))
E = lambda j: (j + 1) ** 2 * Tz(j + 1) - 12 * (6 * j + 1) * (6 * j + 5) * Tz(j)
check("A189286 (2.1) holds for all integers once T vanishes at negative arguments", all(E(j) == 0 for j in range(-8, 40)))
check("A189286 (2.2) is the stated combination of three instances of (2.1), as a formal identity",
      all(summand(n, k) - (G(n, k + 1) - G(n, k))
          == -((2 * k - 3 * n - 4) * Tz(n + 1 - k) + 432 * (3 * n + 2 - 2 * k) * Tz(n - k)) * E(k)
          + (2 * k + n + 2) * Tz(k) * (E(n + 1 - k) - 432 * E(n - k))
          for n in range(0, 25) for k in range(-3, n + 6)))
check("A189286 (2.2) G(n,0) = G(n,n+3) = 0", all(G(n, 0) == 0 and G(n, n + 3) == 0 for n in range(40)))
check("A189286 (2.3) three-term recurrence for N",
      all((n + 2) ** 3 * N(n + 2) + 20736 * (n + 1) * (3 * n + 1) * (3 * n + 5) * N(n)
          == 24 * (2 * n + 3) * (18 * n * n + 54 * n + 41) * N(n + 1) for n in range(60)))
check("A189286 (3.1) s2(m+1) + v2(m+1) = s2(m) + 1", all(digits(m + 1, 2) + val(m + 1, 2) == digits(m, 2) + 1 for m in range(0, 3000)))
check("A189286 base cases N(1) = 8*15, N(2) = 8*3915", N(1) == 8 * 15 and N(2) == 8 * 3915)
check("A189286 (3.2) v2(N(n)) = 3 s2(n)", all(val(N(n), 2) == 3 * digits(n, 2) for n in range(1, 250)))
check("A189286 (4.1) v2(D(n)) = 2 s2(n) - s2(3n)", all(val(D(n), 2) == 2 * digits(n, 2) - digits(3 * n, 2) for n in range(1, 400)))
check("A189286 theorem, n <= 250",
      all(N(n) % D(n) == 0 and (N(n) // D(n)) % 8 == 0 and (((N(n) // D(n)) // 8) % 2 == 1) == (n & (n - 1) == 0) for n in range(1, 251)))

# ---------------------------------------------------------------- A208425
a = lambda n: sum(comb(n, k) * comb(n - k, k) * comb(n + k, k) for k in range(n + 1))
primes = [p for p in range(5, 260) if p % 3 == 2 and all(p % d for d in range(2, int(p ** 0.5) + 1))]
check("A208425 (1.1) C(j,k)C(j-k,k)C(j+k,k) = C(3k,k)C(2k,k)C(j+k,3k)",
      all(comb(j, k) * comb(j - k, k) * comb(j + k, k) == comb(3 * k, k) * comb(2 * k, k) * comb(j + k, 3 * k)
          for j in range(40) for k in range(j + 1)))
check("A208425 (1.2) sum_{j<P} C(j+k,3k) = C(P+k,3k+1)",
      all(sum(comb(j + k, 3 * k) for j in range(P)) == comb(P + k, 3 * k + 1) for P in range(1, 40) for k in range(20)))
tt = lambda p, k: comb(3 * k, k) * comb(2 * k, k) * comb(p + k, 3 * k + 1)
check("A208425 (1.3) S = sum_{k<=m} t(p,k)", all(sum(a(j) for j in range(p)) == sum(tt(p, k) for k in range((p - 1) // 2 + 1)) for p in primes[:14]))


def prod_shift(p, k):
    out = 1
    for i in range(k):
        out *= p + 1 + i
    return out


check("A208425 (2.1) (3k+1) k! t(p,k) = p C(2k,k) C(p-1,2k) prod(p+1+i)",
      all((3 * k + 1) * factorial(k) * tt(p, k) == p * comb(2 * k, k) * comb(p - 1, 2 * k) * prod_shift(p, k)
          for p in primes[:14] for k in range((p - 1) // 2 + 1)))
check("A208425 (2.2) (3k+1) (t/p) = C(2k,k) mod p, and p does not divide 3k+1",
      all(tt(p, k) % p == 0 and ((3 * k + 1) * (tt(p, k) // p) - comb(2 * k, k)) % p == 0 and (3 * k + 1) % p != 0
          for p in primes for k in range((p - 1) // 2 + 1)))

chi = lambda r: (1, -1, 0)[r % 3]
psi = lambda r: (1, 1, 0, -1, -1, 0)[r % 6]
A = lambda M: sum(chi(M - j) * comb(2 * M + 2, j) for j in range(M + 1))
B = lambda m: sum(psi(m + 1 - j) * comb(m + j, j) for j in range(m + 2))
check("A208425 (3.1) chi(r+1)+chi(r)+chi(r-1) = 0 and psi(r+1) = psi(r)-psi(r-1)",
      all(chi(r + 1) + chi(r) + chi(r - 1) == 0 and psi(r + 1) == psi(r) - psi(r - 1) for r in range(-30, 30)))
check("A208425 (3.2) A(M) = sum_{k<=M} C(2k,k)", all(A(M) == sum(comb(2 * k, k) for k in range(M + 1)) for M in range(60)))
check("A208425 (3.3) B(m+1) - B(m) = C(2m+3,m+2)", all(B(m + 1) - B(m) == comb(2 * m + 3, m + 2) for m in range(60)))
check("A208425 (3.3) 2B(m) = A(m+1) + 1", all(2 * B(m) == A(m + 1) + 1 for m in range(60)))
check("A208425 (3.4) C(p-N,j) = (-1)^j C(N+j-1,j) mod p",
      all((comb(p - Nn, j) - (-1) ** j * comb(Nn + j - 1, j)) % p == 0 for p in primes[:10] for Nn in range(1, p) for j in range(0, p - Nn + 1)))
check("A208425 (3.4) chi(N-j)(-1)^j = -psi(N-j) for odd N", all(chi(Nn - j) * (-1) ** j == -psi(Nn - j) for Nn in range(1, 41, 2) for j in range(0, 60)))
check("A208425 (3.5) 3 sum_{k<r} C(2k,k) = -1 mod p, r = (p+1)/3",
      all((3 * sum(comb(2 * k, k) for k in range((p + 1) // 3)) + 1) % p == 0 for p in primes))
check("A208425 (4.1) C(2k,k) = (-4)^k C(m,k) mod p for k <= m",
      all((comb(2 * k, k) - (-4) ** k * comb((p - 1) // 2, k)) % p == 0 for p in primes for k in range((p - 1) // 2 + 1)))


# polynomials over F_p as coefficient lists
def padd(f, h, p):
    n = max(len(f), len(h))
    return trim([((f[i] if i < len(f) else 0) + (h[i] if i < len(h) else 0)) % p for i in range(n)])


def pscale(f, c, p):
    return trim([(c * x) % p for x in f])


def pmul(f, h, p):
    out = [0] * (len(f) + len(h) - 1) if f and h else []
    for i, x in enumerate(f):
        if x:
            for j, y in enumerate(h):
                out[i + j] = (out[i + j] + x * y) % p
    return trim(out)


def trim(f):
    while f and f[-1] == 0:
        f = f[:-1]
    return f


def ppow(f, e, p):
    out = [1]
    for _ in range(e):
        out = pmul(out, f, p)
    return out


def pderiv(f, p):
    return trim([(i * f[i]) % p for i in range(1, len(f))])


def peval(f, x, p):
    return sum(c * pow(x, i, p) for i, c in enumerate(f)) % p


def pcomp(f, h, p):
    out, power = [], [1]
    for c in f:
        out = padd(out, pscale(power, c, p), p)
        power = pmul(power, h, p)
    return out


def pmod_cyclo(f, p):      # remainder modulo X^2 - X + 1
    f = list(f)
    for i in range(len(f) - 1, 1, -1):
        c = f[i]
        if c:
            f[i] = 0
            f[i - 1] = (f[i - 1] + c) % p
            f[i - 2] = (f[i - 2] - c) % p
    return trim(f[:2])


inv = lambda x, p: pow(x, p - 2, p)
allok = {k: True for k in ("Q'", "rec", "Q1", "H'", "frob", "comp", "X^p", "u", "modQ", "final")}
for p in primes[:12]:
    n = (p - 5) // 6
    m, r = 3 * n + 2, 2 * n + 2
    u = [0, 1, p - 1]                                           # X(1-X)
    Q = {}
    for k in range(1, r + 1):                                   # the text needs Q_k only for 2k - 1 < p
        gk = ppow(u, k - 1, p)
        Q[k] = trim([0] + [(gk[i] * inv(i + 1, p)) % p for i in range(len(gk))])
        allok["Q'"] &= pderiv(Q[k], p) == gk
        allok["Q1"] &= (k * comb(2 * k, k) * peval(Q[k], 1, p)) % p == 2 % p
    for k in range(1, r + 1):
        if k < r:                                               # recurrence is used for 2k + 1 < p
            lhs = padd(pscale(Q[k], k, p), pscale(Q[k + 1], -(4 * k + 2), p), p)
            allok["rec"] &= lhs == pmul([1, p - 2], ppow(u, k, p), p)
        sig = sum(comb(2 * i, i) for i in range(k)) % p
        rhs = pscale(padd([1], pscale([p - 1, 2], sig, p), p), peval(Q[k], 1, p), p)   # Q_k(1)(1 + (2X-1) sigma_k)
        allok["modQ"] &= pmod_cyclo(pscale(Q[k], 2, p), p) == pmod_cyclo(rhs, p)
    F = trim([(comb(2 * k, k) * inv(3 * k + 1, p)) % p for k in range(m + 1)])
    H = pscale([0] * r + F, 3, p)                               # 3 X^r F
    allok["H'"] &= pderiv(H, p) == pmul([0] * (r - 1) + [1], ppow([1, p - 4], m, p), p)
    allok["frob"] &= ppow([1, p - 2], p, p) == trim([1] + [0] * (p - 1) + [p - 2])
    Xp = [0] * p + [1]
    rhs = padd(padd(Q[r], pscale(pmul(Xp, Q[r], p), -2, p), p), pscale(Xp, peval(Q[r], 1, p), p), p)
    allok["comp"] &= pcomp(H, u, p) == rhs
    allok["X^p"] &= pmod_cyclo(Xp, p) == [1, p - 1]
    allok["u"] &= pmod_cyclo(u, p) == [1]
    allok["final"] &= (comb(2 * r, r) * peval(F, 1, p)) % p == 2 % p and (3 * peval(F, 1, p) - peval(Q[r], 1, p)) % p == 0
check("A208425 (4.2) Q_k' = u^(k-1)", allok["Q'"])
check("A208425 (4.3) k Q_k - (4k+2) Q_(k+1) = (1-2X) u^k", allok["rec"])
check("A208425 (4.4) k C(2k,k) Q_k(1) = 2", allok["Q1"])
check("A208425 (4.5) (3 X^r F)' = X^(r-1) (1-4X)^m", allok["H'"])
check("A208425 (4.6) (1-2X)^p = 1 - 2X^p", allok["frob"])
check("A208425 (4.7) H(u) = Q_r - 2 X^p Q_r + Q_r(1) X^p", allok["comp"])
check("A208425 (4.8) u = 1 and X^p = 1 - X modulo X^2 - X + 1", allok["u"] and allok["X^p"])
check("A208425 (4.9) 2 Q_k = Q_k(1)(1 + (2X-1) sigma_k) modulo X^2 - X + 1", allok["modQ"])
check("A208425 (4.10) 3 F(1) = Q_r(1) and C(2r,r) F(1) = 2", allok["final"])


def theorem_holds(p):
    s = sum(a(k) for k in range(p))
    c = comb(2 * (p + 1) // 3, (p + 1) // 3)
    return (Fraction(s) - Fraction(2 * p, c)).numerator % (p * p) == 0


check("A208425 theorem, p = 2 and all primes p = 2 mod 3 below 260", theorem_holds(2) and all(theorem_holds(p) for p in primes))
print("\nALL CHECKS PASSED" if ok else "\nSOME CHECKS FAILED")
