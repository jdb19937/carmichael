# Lean formalization of carmichael.tex

A Lean 4 / Mathlib formalization of the main theorem of *"A deterministic
quasi-polylogarithmic algorithm for constructing Carmichael numbers"*
(`../carmichael.tex`), in two forms:

* **`main_theorem`** (paper-faithful, `E = 1/3`): assuming AGP Theorems 3
  and 3.1, a Carmichael number `m ∈ (n, n^{1+ε}]` exists together with its
  prime factorization, and the exhaustive search of the paper's Section 3
  performs at most `exp(100·ℓ₂ℓ₃)` primitive operations.
* **`main_theorem_weak`** (one assumption): the same conclusion at the
  sieve-delivered smoothness exponent `Eweak`, assuming ONLY AGP
  Theorem 3.1 — Theorem 3 is replaced by the in-project
  `smooth_shifted_weak`, proved via the Selberg sieve (fundamental theorem
  included), a uniform twin-type bound, and totient/divisor mean values,
  all from Mathlib alone.

## The theorem

```
theorem main_theorem (A : Assumptions) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (∃ m S, (∀ p ∈ S, p.Prime) ∧ 3 ≤ S.card ∧ m = ∏ p ∈ S, p ∧
        IsCarmichael m ∧ n < m ∧ (m : ℝ) ≤ (n : ℝ) ^ (1 + ε)) ∧
      opBudget A n ≤ Real.exp (C * ell2 n * ell3 n)
```

`Assumptions` contains exactly two results, both from Alford–Granville–
Pomerance, *Annals of Math.* 140 (1994): Theorem 3 at `E = 1/3`
(`smooth_shifted`, with constants `γ, x₁`) and Theorem 3.1 at `B = 2/5`
(`pigeonhole`, with constants `D, z₃`). `#print axioms` reports only
`[propext, Classical.choice, Quot.sound]` (see `AxiomCheck.lean`).

## Files

| File | Contents | Status |
|---|---|---|
| `Carmichael/Defs.lean` | `IsCarmichael`, scales `z, y, T`, reservoir, `L`, `x = L⁵`, `λ(L)`, `N*`, pool | defs |
| `Carmichael/Assumptions.lean` | The pack: AGP Thm 3 + Thm 3.1 only; `C₁ = max(48/γ, 10³)` | defs |
| `Carmichael/Korselt.lean` | Korselt's criterion, full iff | proved |
| `Carmichael/PrimeCount.lean` | Chebyshev: `π(z) ≥ z/(3 log z)` eventually, from Mathlib's ψ-bounds | proved |
| `Carmichael/RecipSum.lean` | `∑_{w<p≤z} 1/p` bound from Mertens' first theorem | proved |
| `Carmichael/ZeroSum.lean` | van Emde Boas–Kruyswijk zero-sum theorem (AGP's character proof over ℂ); to our knowledge the first formalization in any prover | proved |
| `Carmichael/Step2.lean` | Paper Lemma 4.1 (reservoir has ≥ T primes) | proved |
| `Carmichael/Step3.lean` | Paper Lemma 4.2 (shift scan halts with a `(log n)^{1.2}` pool) | proved |
| `Carmichael/Extraction.lean` | Paper Lemma 4.3 (subset product ≡ 1 mod L in `(n, n·x^{N*}]`) | proved |
| `Carmichael/Output.lean` | Paper Lemma 4.4 (output is Carmichael, in `(n, n^{1+ε}]`) | proved |
| `Carmichael/Budget.lean` | Paper Lemma 4.5: `opBudget ≤ exp(100·ℓ₂ℓ₃)` | proved |
| `Carmichael/Main.lean` | The main theorem, composing the five lemmas | proved |
| `Carmichael/SelbergBound.lean` | Fundamental theorem of the Selberg sieve (completing Mathlib's `NumberTheory.SelbergSieve`) | proved |
| `Carmichael/TwinSieve.lean` | Uniform twin-type bound `#{q ≤ t : q, mq+1 prime} ≤ C₀(m/φ(m))²t/log²t` | proved |
| `Carmichael/TotientSum.lean`, `TotientSumSq.lean`, `DivisorMean.lean` | Totient and divisor-power mean values | proved |
| `Carmichael/SmoothShifted.lean` | Weak AGP Theorem 3 (`smooth_shifted_weak`): a positive proportion of `p ≤ x` have `p−1` free of prime factors `> x^{1−E}` | proved |
| `Carmichael/LogPow.lean`, `Step2E/Step3E/ExtractionE/OutputE/BudgetE.lean` | E-generic forms of the step lemmas | proved |
| `Carmichael/WeakE.lean`, `MainWeak.lean` | Weak-exponent constants, `AssumptionsWeak` (AGP 3.1 only), `main_theorem_weak` | proved |
| `Contrib/` | Vendored third-party proofs: Mertens' first theorem + Euler–Maclaurin helper, ported from PrimeNumberTheoremAnd via anthropics/zeta-23-lean (Apache 2.0, provenance headers in files) | vendored |
| `AxiomCheck.lean` | `#guard_msgs` axiom-closure harness (15 declarations) | check |

## Design decisions

* **Assumptions as a structure, not axioms** — the theorem is conditional
  on `A : Assumptions`; nothing is postulated globally.
* **"For n large" = `∀ᶠ n in atTop`** — the paper's `n₀` is the max of the
  finitely many thresholds discharged by `filter_upwards`.
* **Running time = operation count.** `opBudget` is an explicit real bound
  on the primitive operations of the paper's algorithm, one summand per
  step; primality tests are charged trial division (`√x + 1` per candidate),
  so AKS is not used anywhere — the class `exp(O(ℓ₂ℓ₃))` absorbs `√x`, and
  it is closed under the polynomial overhead of converting unit-cost
  operations on `O(log n)`-bit integers to bit operations on any standard
  machine model (equivalently: the bound is quasi-polynomial in the input
  length `log n`, a model-robust class).
* **`n^{1+o(1)}` = `∀ ε > 0 … m ≤ n^{1+ε}`.**

## How to verify

Machine half: `make verify` (from the repo root) — full kernel-checked
build, then `AxiomCheck.lean` asserts via `#guard_msgs` that every audited
declaration depends only on `propext, Classical.choice, Quot.sound`.
Trust base: the Lean kernel and the pinned toolchain.

Human half (~250 lines, statements only — proofs never need reading):
1. `Carmichael/Defs.lean` — `IsCarmichael` and the Section-3 objects;
2. `Carmichael/Assumptions.lean` — the two AGP fields against AGP 1994
   (the only place a transcription error could invalidate the result);
3. `Carmichael/Main.lean` — the theorem statement;
4. `Carmichael/Budget.lean` — the `opBudget` definition vs the algorithm's
   loop structure (the operation-count convention);
5. `AxiomCheck.lean` — the audited declaration list.

## Building

```
lake exe cache get   # prebuilt Mathlib (~5 GB)
lake build           # builds Contrib and Carmichael; zero sorries
lake env lean AxiomCheck.lean
```

Pinned: Lean `v4.33.1`, Mathlib `v4.33.1`.

## Status

Complete: `lake build` succeeds with zero `sorry`s; every declaration
depends only on Lean's standard axioms. Open directions: prove AGP
Theorem 3 for some `E > 0` via Brun–Titchmarsh and an upper sieve (the
Selberg sieve fundamental theorem exists in Lean); upstream `korselt` and
`vebk` to Mathlib; a cost-monad refinement internalizing the operation
count.
