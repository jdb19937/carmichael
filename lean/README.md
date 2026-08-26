# Lean formalization of carmichael.tex

A Lean 4 / Mathlib formalization of the main theorem of *"A deterministic
quasi-polylogarithmic algorithm for constructing Carmichael numbers"*
(`../carmichael.tex`): assuming only AGP Theorems 3 and 3.1, a Carmichael
number `m ∈ (n, n^{1+ε}]` exists together with its prime factorization, and
the exhaustive search of the paper's Section 3 that finds it performs at
most `exp(100·ℓ₂ℓ₃)` primitive operations.

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
| `Contrib/` | Vendored third-party proofs: Mertens' first theorem + Euler–Maclaurin helper, ported from PrimeNumberTheoremAnd via anthropics/zeta-23-lean (Apache 2.0, provenance headers in files) | vendored |
| `AxiomCheck.lean` | `#print axioms` harness | check |

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

## Paper revisions this formalization produced (2026-08-25)

1. **Lemma 4.2 erratum**: the claim `∑_{q∈Q} 1/q ≤ T/√z → 0` was false
   (`T/√z → ∞`); worst-case admissible `Q` gives `∑ 1/q → log 2 ≫ 3/160`.
   Fixed by raising the step-2 reservoir floor from `√z` to `z^{99/100}`
   and bounding the sum by Mertens (Rosser–Schoenfeld citation added).
2. **Chebyshev constant**: the proof of Lemma 4.1 used `π(z) ≥ z/log z`
   (a PNT-strength constant) without citation; replaced by the elementary
   `π(z) ≥ z/(3 log z)`, with `C₁ = max(48/γ, 10³)` (formerly `16/γ`).
3. **Trial-division remark** added after the AKS lemma.

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
