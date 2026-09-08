/-
The weak-E constants: choice-extraction from `smooth_shifted_weak`
(the sieve-proved weak AGP Theorem 3), the matching `C₁weak`, and the
one-field-pair assumption structure for the weak main theorem —
AGP Theorem 3.1 is the sole remaining assumed input.
-/
import Carmichael.SmoothShifted

namespace Carmichael

/-- The smoothness exponent delivered by the sieve campaign. -/
noncomputable def Eweak : ℝ := smooth_shifted_weak.choose

lemma Eweak_pos : 0 < Eweak := smooth_shifted_weak.choose_spec.1

lemma Eweak_le_half : Eweak ≤ 1 / 2 := smooth_shifted_weak.choose_spec.2.1

/-- The density constant delivered by the sieve campaign. -/
noncomputable def gammaWeak : ℝ :=
  smooth_shifted_weak.choose_spec.2.2.choose

lemma gammaWeak_pos : 0 < gammaWeak :=
  smooth_shifted_weak.choose_spec.2.2.choose_spec.1

/-- The threshold delivered by the sieve campaign. -/
noncomputable def x₁Weak : ℕ :=
  smooth_shifted_weak.choose_spec.2.2.choose_spec.2.choose

open Classical in
lemma smooth_shifted_weak_spec : ∀ x : ℕ, x₁Weak ≤ x →
    gammaWeak * (primePi x : ℝ) ≤
      (((Finset.range (x + 1)).filter (fun p => p.Prime ∧
        ∀ q : ℕ, q.Prime → q ∣ p - 1 →
          (q : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) - Eweak))).card : ℝ) :=
  smooth_shifted_weak.choose_spec.2.2.choose_spec.2.choose_spec

/-- Step 1 of the algorithm at the weak exponent: `C₁ = max(48/γ, 10³)`. -/
noncomputable def C₁weak : ℝ := max (48 / gammaWeak) 1000

lemma thousand_le_C₁weak : (1000 : ℝ) ≤ C₁weak := le_max_right _ _

lemma le_C₁weak_mul_gammaWeak : (48 : ℝ) ≤ C₁weak * gammaWeak :=
  (div_le_iff₀ gammaWeak_pos).mp (le_max_left _ _)

open Classical in
/-- The weak assumption pack: AGP Theorem 3.1 at `B = 21/100` is the sole
assumed input (Theorem 3 is replaced by the proved `smooth_shifted_weak`).
The exponents are `(1 - B)/2 = 79/200` (prime-factor bound), `1 - B = 79/100`
(shift bound) and `B = 21/100` (divisor window); the reciprocal-sum budget is
the verbatim `3/160`. -/
structure AssumptionsWeak where
  /-- The constant `D = D_{21/100}` of [AGP, Theorem 3.1]. -/
  D : ℝ
  /-- The threshold `z₃ = z₃(21/100)` of [AGP, Theorem 3.1]. -/
  z₃ : ℕ
  /-- [AGP, Theorem 3.1] at `B = 21/100`. -/
  pigeonhole : ∀ x L : ℕ, z₃ < x → 1 < L → Squarefree L →
    (∀ q : ℕ, q.Prime → q ∣ L → (q : ℝ) ≤ (x : ℝ) ^ ((79 : ℝ) / 200)) →
    (∑ q ∈ L.primeFactors, (1 : ℝ) / q) ≤ 3 / 160 →
    ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ (x : ℝ) ^ ((79 : ℝ) / 100) ∧ k.Coprime L ∧
      (2 : ℝ) ^ (-D - 2) / Real.log x *
        ((L.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (x : ℝ) ^ ((21 : ℝ) / 100))).card : ℝ)
      ≤ ((L.divisors.filter (fun d => d * k + 1 ≤ x ∧ (d * k + 1).Prime)).card : ℝ)

end Carmichael
