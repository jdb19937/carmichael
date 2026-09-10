import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Route T cost budget

`B b` is the per-tick step budget of the machine layer on operands of at most
`b` bits: every arithmetic fragment of the machine, run on numbers below
`2 ^ b`, finishes within `B b` steps (one step = one label executed).  The
cubic gives room for schoolbook multiplication and long division (`O(b²)`)
together with the operand moves and copies around them.
-/

namespace Carmichael.TM

/-- The per-tick step budget of the machine layer on operands of at most `b`
bits: `64 * (b + 2) ^ 3`. -/
def B (b : ℕ) : ℕ := 64 * (b + 2) ^ 3

theorem B_mono {b b' : ℕ} (h : b ≤ b') : B b ≤ B b' := by
  unfold B
  have : (b + 2) ^ 3 ≤ (b' + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  omega

theorem one_le_B (b : ℕ) : 1 ≤ B b := by
  unfold B
  have : 1 ≤ (b + 2) ^ 3 := Nat.one_le_pow _ _ (by omega)
  omega

/-- A linear bound `c * (b + 2)` with `c ≤ 64` is within budget. -/
theorem linear_le_B {c b : ℕ} (hc : c ≤ 64) : c * (b + 2) ≤ B b := by
  unfold B
  have h1 : 1 ≤ (b + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  calc c * (b + 2) ≤ 64 * (b + 2) := Nat.mul_le_mul_right _ hc
    _ = 64 * (b + 2) * 1 := (mul_one _).symm
    _ ≤ 64 * (b + 2) * (b + 2) ^ 2 := Nat.mul_le_mul_left _ h1
    _ = 64 * (b + 2) ^ 3 := by ring

/-- A quadratic bound `c * (b + 2) ^ 2` with `c ≤ 64` is within budget. -/
theorem quad_le_B {c b : ℕ} (hc : c ≤ 64) : c * (b + 2) ^ 2 ≤ B b := by
  unfold B
  have h1 : 1 ≤ b + 2 := by omega
  calc c * (b + 2) ^ 2 ≤ 64 * (b + 2) ^ 2 := Nat.mul_le_mul_right _ hc
    _ = 64 * (b + 2) ^ 2 * 1 := (mul_one _).symm
    _ ≤ 64 * (b + 2) ^ 2 * (b + 2) := Nat.mul_le_mul_left _ h1
    _ = 64 * (b + 2) ^ 3 := by ring

/-- Anything `≤ 64 * (b + 2)` is within budget. -/
theorem le_B_of_le_linear {n b : ℕ} (h : n ≤ 64 * (b + 2)) : n ≤ B b :=
  h.trans (linear_le_B le_rfl)

/-- Anything `≤ 64 * (b + 2) ^ 2` is within budget. -/
theorem le_B_of_le_quad {n b : ℕ} (h : n ≤ 64 * (b + 2) ^ 2) : n ≤ B b :=
  h.trans (quad_le_B le_rfl)

end Carmichael.TM
