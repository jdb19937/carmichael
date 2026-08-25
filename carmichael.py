"""Deterministic construction of certified Carmichael numbers.

Companion implementation for:
  D. Brown, "A deterministic quasi-polylogarithmic algorithm for
  constructing Carmichael numbers" (2026).

Usage:
  python3 carmichael.py            # Carmichael number > 10^20 (the paper's example)
  python3 carmichael.py 1e50       # Carmichael number > 10^50
  python3 carmichael.py 1e100 -v   # larger target, verbose

Method (the simplified variant of Remark 5.4 of the paper). By Korselt's
criterion, m is a Carmichael number iff m is composite, squarefree, and
q - 1 | m - 1 for every prime q | m. Take L = lcm(1..K) and the reservoir

    R = { q prime : q - 1 divides L },

found by testing d + 1 for each divisor d of L. A dynamic program over
residues modulo L then finds a subset S of R, of maximal log-product,
with  prod(S) = 1 (mod L)  and  prod(S) > n.  For m = prod(S) every
factor satisfies q - 1 | L | m - 1, so Korselt's criterion holds by
construction; the factor list is the certificate, and it is re-verified
from scratch before anything is returned.

Everything the search touches lives at the scale of L (a few hundred
thousand); only the final product m is large. The proof in the paper
replaces this reservoir with the shifted reservoir of Alford, Granville
and Pomerance, whose abundance is a theorem rather than a heuristic; the
subset-product step is the same.

Requires Python 3.8+, standard library only.
"""

import argparse
import sys
import time
from math import gcd, isqrt, log


# ---------------------------------------------------------------- reservoir

def is_prime(m):
    """Trial division; used only on numbers up to lcm(1..K) + 1."""
    if m < 2:
        return False
    for d in range(2, isqrt(m) + 1):
        if m % d == 0:
            return False
    return True


def lcm_factored(K):
    """lcm(1..K) as a factor list [(p, a)] with p^a <= K < p^(a+1)."""
    out = []
    for p in range(2, K + 1):
        if is_prime(p):
            a = 1
            while p ** (a + 1) <= K:
                a += 1
            out.append((p, a))
    return out


def divisors(factored):
    divs = [1]
    for p, a in factored:
        divs = [d * p**e for d in divs for e in range(a + 1)]
    return sorted(divs)


def reservoir(K):
    """(L, [q1 < q2 < ...]) with L = lcm(1..K) and each q prime, q-1 | L."""
    fac = lcm_factored(K)
    L = 1
    for p, a in fac:
        L *= p**a
    R = [d + 1 for d in divisors(fac) if is_prime(d + 1)]
    return L, R


# ------------------------------------------------------------ subset search

def best_subset(L, R, target):
    """Subset of R with product = 1 (mod L), maximal log-product.

    Deterministic dynamic program over residues modulo L. dp[r] holds
    (log-product, chain) for the best subset found with product r; chains
    are shared linked lists (prime_index, parent), so memory stays near
    O(number of residues). Returns the subset (sorted) if its log-product
    reaches target, else None.
    """
    dp = {1: (0.0, None)}
    for qi in sorted(range(len(R)), key=lambda i: -R[i]):
        q, lq = R[qi], log(R[qi])
        for r, (ls, chain) in list(dp.items()):   # snapshot: 0/1 use per prime
            nr = r * q % L
            cand = ls + lq
            if cand > dp.get(nr, (-1.0, None))[0]:
                dp[nr] = (cand, (qi, chain))
    ls, chain = dp.get(1, (-1.0, None))
    if ls < target:
        return None
    subset = []
    while chain is not None:
        qi, chain = chain
        subset.append(R[qi])
    return sorted(subset)


# ------------------------------------------------------------- construction

def carmichael_above(n, verbose=False):
    """Certified Carmichael number > n. Returns (m, factors, L)."""
    for K in (12, 16, 18, 20, 22, 24):
        L, R = reservoir(K)
        if sum(log(q) for q in R) < 1.3 * log(n) + 4 * log(L):
            continue                    # reservoir too small for this n
        if verbose:
            print(f"# L = lcm(1..{K}) = {L}, reservoir of {len(R)} primes",
                  file=sys.stderr)
        subset = best_subset(L, R, log(n) + 0.5)
        if subset is None:
            continue
        m = 1
        for q in subset:
            m *= q
        certify(m, subset, n)
        return m, subset, L
    raise RuntimeError("reservoir insufficient for this n; extend the K list")


def certify(m, factors, n):
    """Independent verification: raises AssertionError on any failure."""
    assert m > n and len(factors) >= 3
    assert len(set(factors)) == len(factors)          # squarefree
    prod = 1
    for q in factors:
        assert is_prime(q), q                         # factors are prime
        assert (m - 1) % (q - 1) == 0, q              # Korselt
        prod *= q
    assert prod == m
    for a in (2, 3, 5, 7, 11, 65537):                 # Fermat spot checks
        if gcd(a, m) == 1:
            assert pow(a, m - 1, m) == 1


# ---------------------------------------------------------------------- cli

def main():
    ap = argparse.ArgumentParser(
        description="Construct a certified Carmichael number greater than n.")
    ap.add_argument("n", nargs="?", default="1e20",
                    help="lower bound, e.g. 1000000 or 1e50 (default 1e20)")
    ap.add_argument("-v", "--verbose", action="store_true",
                    help="print search parameters to stderr")
    args = ap.parse_args()
    n = int(float(args.n))

    t0 = time.time()
    m, factors, L = carmichael_above(n, verbose=args.verbose)
    dt = time.time() - t0

    print(f"Certified Carmichael number > {args.n}  "
          f"({len(str(m))} digits, {len(factors)} prime factors, {dt:.2f}s)")
    print()
    print(f"  m = {m}")
    print()
    print("  factors:", " ".join(map(str, factors)))
    print()
    print("Certificate re-verified: squarefree, all factors prime,")
    print("q-1 | m-1 for every factor q (Korselt), Fermat checks pass.")


if __name__ == "__main__":
    main()
