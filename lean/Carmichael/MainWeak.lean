/-
The weak main theorem: assuming only AGP Theorem 3.1, a Carmichael number
m ∈ (n, n^{1+ε}] exists together with its complete prime factorization for
all large n, and the operation budget of the paper's algorithm (at the
sieve-delivered smoothness exponent `Eweak`, with trial division) is at
most exp(C ℓ₂ ℓ₃). Everything except the `AssumptionsWeak` field is proved
from Mathlib; in particular AGP Theorem 3 is replaced by the in-project
`smooth_shifted_weak`.
-/
import Carmichael.WeakE
import Carmichael.Step2E
import Carmichael.Step3E
import Carmichael.ExtractionE
import Carmichael.OutputE
import Carmichael.BudgetE

namespace Carmichael

open Filter

/-- Main theorem, weak form: one assumed input (AGP Theorem 3.1). -/
theorem main_theorem_weak (A : AssumptionsWeak) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (∃ m : ℕ, ∃ S : Finset ℕ,
          (∀ p ∈ S, p.Prime) ∧ 3 ≤ S.card ∧ m = ∏ p ∈ S, p ∧
          IsCarmichael m ∧
          n < m ∧ (m : ℝ) ≤ (n : ℝ) ^ (1 + ε)) ∧
        opBudgetE C₁weak Eweak n ≤ Real.exp (C * ell2 n * ell3 n) := by
  obtain ⟨C, hC, hbudget⟩ :=
    opBudgetE_le C₁weak Eweak Eweak_pos Eweak_le_half thousand_le_C₁weak
  refine ⟨C, hC, fun ε hε => ?_⟩
  filter_upwards [
    step2_succeedsE C₁weak gammaWeak Eweak x₁Weak Eweak_pos Eweak_le_half
      gammaWeak_pos le_C₁weak_mul_gammaWeak thousand_le_C₁weak
      smooth_shifted_weak_spec,
    step3_haltsE C₁weak A.D Eweak A.z₃ Eweak_pos Eweak_le_half
      thousand_le_C₁weak A.pigeonhole,
    extractionE C₁weak Eweak Eweak_pos Eweak_le_half thousand_le_C₁weak,
    output_carmichaelE C₁weak Eweak Eweak_pos Eweak_le_half
      thousand_le_C₁weak ε hε,
    hbudget] with n h2 h3 h4 h5 hb
  refine ⟨?_, hb⟩
  obtain ⟨Q, hQsub, hQcard⟩ := Finset.exists_subset_card_eq h2
  obtain ⟨k, hk, hkx, hkL, hpool⟩ := h3 Q hQsub hQcard
  obtain ⟨S, hSsub, hSne, hSmod, hSgt, hSle⟩ :=
    h4 Q hQsub hQcard k hk hkL hpool
  obtain ⟨hprime, hcard, hcarm, hupper⟩ :=
    h5 Q hQsub hQcard k hk hkL S hSsub hSne hSmod hSgt hSle
  exact ⟨∏ p ∈ S, p, S, hprime, hcard, rfl, hcarm, hSgt, hupper⟩

end Carmichael
