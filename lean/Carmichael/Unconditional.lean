/-
Route Z, the splice: Mickey's theorem — Carmichael numbers are findable in
quasipolylogarithmic time — with NO hypotheses.

`assumptionsWeak_of_logged` packages `pigeonhole_21'` (AGP Theorem 3.1 at
`B = 21/100`, `Carmichael/BMembership21.lean`) into the weak main theorem's
hypothesis pack `AssumptionsWeak`.  The pigeonhole is conditional on
`T21.DensityInputs`; its log-free field is discharged by
`ZeroDensity.logfree_of_logged` and its logged field by
`LoggedDensity.loggedDensity`, so `main_theorem_unconditional` has no
hypothesis at all: every analytic input (explicit formula, log-free and
logged zero densities, exceptional-zero census, zero-free region,
Brun–Titchmarsh, Chebyshev) is proved in this repository from Mathlib.

`main_theorem_weak_of_logged` is the intermediate form with the logged
density as its single hypothesis.
-/
import Carmichael.MainWeak
import Carmichael.BMembership21
import Carmichael.ZeroDensity
import Carmichael.LoggedDensity

set_option autoImplicit false

namespace Carmichael

open Filter

/-- The two density inputs of T2.1 from the logged one alone. -/
theorem densityInputs_of_logged (hlog : LoggedDensity) : T21.DensityInputs :=
  ⟨ZeroDensity.logfree_of_logged hlog, hlog⟩

/-- The weak assumption pack, supplied by Route Z from the logged density. -/
noncomputable def assumptionsWeak_of_logged (hlog : LoggedDensity) : AssumptionsWeak :=
  have h := pigeonhole_21' (densityInputs_of_logged hlog)
  { D := (h.choose : ℝ)
    z₃ := h.choose_spec.choose
    pigeonhole := h.choose_spec.choose_spec }

/-- **Mickey's theorem, conditional only on the logged zero density.** -/
theorem main_theorem_weak_of_logged (hlog : LoggedDensity) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (∃ m : ℕ, ∃ S : Finset ℕ,
          (∀ p ∈ S, p.Prime) ∧ 3 ≤ S.card ∧ m = ∏ p ∈ S, p ∧
          IsCarmichael m ∧
          n < m ∧ (m : ℝ) ≤ (n : ℝ) ^ (1 + ε)) ∧
        opBudgetE C₁weak Eweak n ≤ Real.exp (C * ell2 n * ell3 n) :=
  main_theorem_weak (assumptionsWeak_of_logged hlog)

/-- The weak assumption pack, with no hypothesis. -/
noncomputable def assumptionsWeak_routeZ : AssumptionsWeak :=
  assumptionsWeak_of_logged LoggedDensity.loggedDensity

/-- AGP Theorem 3.1 at `B = 21/100`, with no hypothesis. -/
theorem pigeonhole_unconditional :
    ∃ D z₃ : ℕ, ∀ x L : ℕ, z₃ < x → 1 < L → Squarefree L →
      (∀ q : ℕ, q.Prime → q ∣ L → (q : ℝ) ≤ (x : ℝ) ^ ((79 : ℝ) / 200)) →
      (∑ q ∈ L.primeFactors, (1 : ℝ) / q) ≤ 79 / 3200 →
      ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ (x : ℝ) ^ ((79 : ℝ) / 100) ∧ k.Coprime L ∧
        (2 : ℝ) ^ (-(D : ℝ) - 2) / Real.log x *
          ((L.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (x : ℝ) ^ ((21 : ℝ) / 100))).card : ℝ)
        ≤ ((L.divisors.filter (fun d => d * k + 1 ≤ x ∧ (d * k + 1).Prime)).card : ℝ) :=
  pigeonhole_21 (densityInputs_of_logged LoggedDensity.loggedDensity)

/-- **Mickey's theorem, unconditional.**  For every `ε > 0` and all large `n`
there is a Carmichael number `m ∈ (n, n^{1+ε}]`, given with its complete prime
factorization, and the operation budget of the search (every primality test
charged as trial division) is at most `exp (C · log log n · log log log n)`
for an absolute constant `C`. -/
theorem main_theorem_unconditional :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (∃ m : ℕ, ∃ S : Finset ℕ,
          (∀ p ∈ S, p.Prime) ∧ 3 ≤ S.card ∧ m = ∏ p ∈ S, p ∧
          IsCarmichael m ∧
          n < m ∧ (m : ℝ) ≤ (n : ℝ) ^ (1 + ε)) ∧
        opBudgetE C₁weak Eweak n ≤ Real.exp (C * ell2 n * ell3 n) :=
  main_theorem_weak_of_logged LoggedDensity.loggedDensity

end Carmichael
