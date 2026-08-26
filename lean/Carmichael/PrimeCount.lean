/-
A Chebyshev-type lower bound for the prime counting function:
eventually `z / (3 * log z) ≤ π(z)`, derived from Mathlib's bounds on
the Chebyshev function `ψ`.
-/
import Carmichael.Defs
import Mathlib.NumberTheory.Chebyshev

namespace Carmichael

open Filter

/-- Our `primePi` agrees with Mathlib's `Nat.primeCounting`. -/
lemma primePi_eq_primeCounting (z : ℕ) : primePi z = Nat.primeCounting z := by
  rw [primePi, ← Nat.primesLE_eq_filter_range, Nat.primesLE_card_eq_primeCounting]

/-- A Chebyshev-type lower bound: eventually `z / (3 log z) ≤ π(z)`. -/
theorem chebyshev_lower :
    ∀ᶠ z : ℕ in Filter.atTop, (z : ℝ) / (3 * Real.log z) ≤ (primePi z : ℝ) := by
  -- Since `log = o(id)` at infinity, eventually `log x ≤ x / 20`.
  have hlogR : ∀ᶠ x : ℝ in atTop, Real.log x ≤ 1 / 20 * x := by
    filter_upwards [Real.isLittleO_log_id_atTop.def (by norm_num : (0 : ℝ) < 1 / 20),
      eventually_ge_atTop (0 : ℝ)] with x hx hx0
    have hx' : |Real.log x| ≤ 1 / 20 * |x| := by simpa [Real.norm_eq_abs] using hx
    calc Real.log x ≤ |Real.log x| := le_abs_self _
      _ ≤ 1 / 20 * |x| := hx'
      _ = 1 / 20 * x := by rw [abs_of_nonneg hx0]
  -- Transfer along `z ↦ (z : ℝ) + 1`.
  have hlogN : ∀ᶠ z : ℕ in atTop, Real.log ((z : ℝ) + 1) ≤ 1 / 20 * ((z : ℝ) + 1) :=
    (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).eventually hlogR
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  filter_upwards [hlogN, eventually_ge_atTop 2] with z hz hz2
  have hz2' : (2 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz2
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  -- Chain the two `ψ` bounds: `z log 2 - log (z+1) ≤ ψ z ≤ π(z) log z`.
  have hchain : (z : ℝ) * Real.log 2 - Real.log ((z : ℝ) + 1)
      ≤ (Nat.primeCounting z : ℝ) * Real.log z :=
    (Chebyshev.psi_ge z).trans (Chebyshev.psi_le_primeCounting_mul_log z)
  have hzlog2 : (z : ℝ) * 0.6931471803 ≤ (z : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2.le (by positivity)
  rw [primePi_eq_primeCounting, div_le_iff₀ (mul_pos (by norm_num) hlogz)]
  have hring : (Nat.primeCounting z : ℝ) * (3 * Real.log z)
      = 3 * ((Nat.primeCounting z : ℝ) * Real.log z) := by ring
  rw [hring]
  linarith

end Carmichael
