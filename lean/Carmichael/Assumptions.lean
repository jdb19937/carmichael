/-
The assumption pack: the two deep Alford--Granville--Pomerance inputs of
Section 2 of the paper. Every other cited input is proved:

* Korselt's criterion [Kor]           — proved in `Carmichael/Korselt.lean`;
* van Emde Boas--Kruyswijk [EK]       — proved in `Carmichael/ZeroSum.lean`
  (the AGP character-theoretic proof, over ℂ);
* Chebyshev's lower bound             — proved in `Carmichael/PrimeCount.lean`
  (`π(z) ≥ z/(3 log z)` eventually, from Mathlib's ψ-estimates; the paper's
  constant `C₁ = max(48/γ, 10³)` is sized for the elementary constant 3);
* Mertens' second-theorem consequence — proved in `Carmichael/RecipSum.lean`
  from Mertens' first theorem, which is vendored in `Contrib/Mertens.lean`
  (ported from PrimeNumberTheoremAnd via anthropics/zeta-23-lean, Apache 2.0);
* AKS [AKS]                           — eliminated: the operation budget
  charges trial division (`√x` per test), which the bound `exp(O(ℓ₂ℓ₃))`
  absorbs; see `Carmichael/Budget.lean`.

The main theorem is conditional on `A : Assumptions`, so `#print axioms`
on the final result shows nothing beyond Lean's standard axioms.

Statement fidelity notes:
* `smooth_shifted` is [AGP, Theorem 3] specialized to `E = 1/3`, with the
  constants `γ = γ(1/3)` and `x₁ = x₁(1/3)` as named fields.
* `pigeonhole` is [AGP, Theorem 3.1] specialized to `B = 2/5 ∈ 𝓑`, with the
  constants `D = D_{2/5}` and `z₃ = z₃(2/5)` as named fields; note
  `(1-B)/2 = 3/10`, `1-B = 3/5`, `B = 2/5`, `(1-B)/32 = 3/160`.
-/
import Carmichael.Defs

namespace Carmichael

open Classical in
structure Assumptions where
  /-- The density `γ = γ(1/3) > 0` of [AGP, Theorem 3]. -/
  gamma : ℝ
  gamma_pos : 0 < gamma
  /-- The threshold `x₁ = x₁(1/3)` of [AGP, Theorem 3]. -/
  x₁ : ℕ
  /-- [AGP, Theorem 3] at `E = 1/3`: for `x ≥ x₁`, at least `γ · π(x)` primes
  `p ≤ x` have `p - 1` free of prime factors exceeding `x^{2/3}`. -/
  smooth_shifted : ∀ x : ℕ, x₁ ≤ x →
    gamma * (primePi x : ℝ) ≤
      (((Finset.range (x + 1)).filter (fun p => p.Prime ∧
        ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ (x : ℝ) ^ ((2 : ℝ) / 3))).card : ℝ)
  /-- The constant `D = D_{2/5}` of [AGP, Theorem 3.1]. -/
  D : ℝ
  /-- The threshold `z₃ = z₃(2/5)` of [AGP, Theorem 3.1]. -/
  z₃ : ℕ
  /-- [AGP, Theorem 3.1] at `B = 2/5`: if `x > z₃`, `L` is squarefree with all
  prime factors at most `x^{3/10}` and `∑_{q ∣ L} 1/q ≤ 3/160`, then some
  `k ≤ x^{3/5}` coprime to `L` makes at least a `2^{-D-2}/log x` proportion of
  the divisors `d ≤ x^{2/5}` of `L` yield primes `dk + 1 ≤ x`. -/
  pigeonhole : ∀ x L : ℕ, z₃ < x → 1 < L → Squarefree L →
    (∀ q : ℕ, q.Prime → q ∣ L → (q : ℝ) ≤ (x : ℝ) ^ ((3 : ℝ) / 10)) →
    (∑ q ∈ L.primeFactors, (1 : ℝ) / q) ≤ 3 / 160 →
    ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ (x : ℝ) ^ ((3 : ℝ) / 5) ∧ k.Coprime L ∧
      (2 : ℝ) ^ (-D - 2) / Real.log x *
        ((L.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (x : ℝ) ^ ((2 : ℝ) / 5))).card : ℝ)
      ≤ ((L.divisors.filter (fun d => d * k + 1 ≤ x ∧ (d * k + 1).Prime)).card : ℝ)

namespace Assumptions

variable (A : Assumptions)

/-- Step 1 of the algorithm: `C₁ = max(48/γ, 10³)`. The `48` makes room for
the elementary Chebyshev constant in `chebyshev_lower`
(`π(z) ≥ z/(3 log z)`). -/
noncomputable def C₁ : ℝ := max (48 / A.gamma) 1000

lemma C₁_pos : 0 < A.C₁ := lt_of_lt_of_le (by norm_num) (le_max_right _ _)

lemma le_C₁' : 48 / A.gamma ≤ A.C₁ := le_max_left _ _

lemma le_C₁ : 16 / A.gamma ≤ A.C₁ := by
  refine le_trans ?_ A.le_C₁'
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (by norm_num) (inv_nonneg.mpr A.gamma_pos.le)

lemma thousand_le_C₁ : (1000 : ℝ) ≤ A.C₁ := le_max_right _ _

end Assumptions

end Carmichael
