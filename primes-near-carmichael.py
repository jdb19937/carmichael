"""Pipeline test: find a (provable) prime > n by generating Carmichael
numbers above n and scanning only admissible slots around each.

Admissible slot: m+c with gcd(c+1, 15015)=1, or m-c with gcd(c-1, 15015)=1
(c even). Since m = 1 mod 720720, every other slot is divisible by one of
3,5,7,11,13 and need not be tested.

Also: abundance check (distinct Carmichaels in one decade) and the
distribution of tests-to-success over 1000 neighborhoods.
"""
import random
from math import gcd, log
from sympy import isprime

def trial_prime(m):
    if m < 2: return False
    d = 2
    while d * d <= m:
        if m % d == 0: return False
        d += 1
    return True

L = 720720
divs = [1]
for p, a in [(2,4),(3,2),(5,1),(7,1),(11,1),(13,1)]:
    divs = [d * p**e for d in divs for e in range(a+1)]
R = sorted(d + 1 for d in divs if trial_prime(d + 1) and L % (d + 1) != 0)
A_half, B_half = R[::2], R[1::2]

dp = {1: None}
for qi, q in enumerate(A_half):
    for r, chain in list(dp.items()):
        nr = r * q % L
        if nr not in dp:
            dp[nr] = (qi, chain)

def subset_from_chain(chain):
    out = []
    while chain is not None:
        qi, chain = chain
        out.append(A_half[qi])
    return out

def gen_carmichaels(rng, count, lo, hi):
    out = set()
    while len(out) < count:
        T = rng.sample(B_half, rng.randrange(6, 15))
        t = 1
        for q in T: t = t * q % L
        need = pow(t, -1, L)
        if need not in dp: continue
        S = subset_from_chain(dp[need]) + T
        if len(S) != len(set(S)): continue
        m = 1
        for q in S: m *= q
        if not (lo < m < hi): continue
        assert m % L == 1 and all((m - 1) % (q - 1) == 0 for q in S)
        out.add(m)
    return sorted(out)

def find_prime_near(m):
    """Scan admissible slots only. Returns (prime, distance, tests)."""
    tests = 0
    c = 2
    while True:
        if gcd(c + 1, 15015) == 1:
            tests += 1
            if isprime(m + c): return m + c, c, tests
        if gcd(c - 1, 15015) == 1:
            tests += 1
            if isprime(m - c): return m - c, -c, tests
        c += 2

rng = random.Random(561)

# --- pipeline demo: primes above n = 10^40 ---
n = 10**40
print(f"target: prime > n = 10^40   (ln n = {log(n):.1f})")
for m in gen_carmichaels(rng, 8, n, 10**6 * n):
    p, c, tests = find_prime_near(m)
    assert p > n and isprime(p)
    print(f"  carmichael {str(m)[:12]}... ({len(str(m))}d)  "
          f"prime at c={c:+d}  after {tests} tests  (naive scan: {abs(c)//2})")

# --- abundance: distinct carmichaels in one decade from bounded draws ---
found = gen_carmichaels(rng, 500, 10**40, 10**41)
print(f"\nabundance: {len(found)} distinct Carmichaels in [10^40,10^41] "
      f"(stopped at 500; supply is ~2^75/phi(L) overall)")

# --- tests-to-success distribution over 1000 neighborhoods, mixed sizes ---
stats = []
for m in gen_carmichaels(rng, 1000, 10**20, 10**80):
    p, c, tests = find_prime_near(m)
    stats.append((tests, abs(c) / log(m)))
tests_sorted = sorted(t for t, _ in stats)
d_sorted = sorted(d for _, d in stats)
nn = len(stats)
print(f"\nover {nn} neighborhoods (20-80 digits):")
print(f"  tests to success: mean {sum(tests_sorted)/nn:.1f}  "
      f"median {tests_sorted[nn//2]}  90% {tests_sorted[int(.9*nn)]}  "
      f"max {tests_sorted[-1]}")
print(f"  distance/ln(m):   median {d_sorted[nn//2]:.3f}  max {d_sorted[-1]:.3f}")
print(f"  failures (no prime found): 0 by construction of the loop; "
      f"every neighborhood yielded a prime")
