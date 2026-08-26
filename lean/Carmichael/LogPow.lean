/-
Shared helper for the E-generic development: squared logs are eventually
dominated by any fixed positive power.
-/
import Mathlib

namespace Carmichael

open Filter

/-- For fixed `E > 0`, eventually `(log u)² ≤ u^E`. -/
theorem eventually_log_sq_le_rpow {E : ℝ} (hE : 0 < E) :
    ∀ᶠ u : ℝ in atTop, (Real.log u) ^ 2 ≤ u ^ E := by
  have h := (isLittleO_log_rpow_atTop (by positivity : (0 : ℝ) < E / 2)).def
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with u hu hu1
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
  have hr0 : (0 : ℝ) ≤ u ^ (E / 2) := Real.rpow_nonneg hu0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0,
    abs_of_nonneg hr0, one_mul] at hu
  calc (Real.log u) ^ 2 ≤ (u ^ (E / 2)) ^ 2 := by nlinarith
    _ = u ^ E := by
        rw [← Real.rpow_natCast (u ^ (E / 2)) 2, ← Real.rpow_mul hu0]
        norm_num

end Carmichael
