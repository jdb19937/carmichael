/-
Windowed scales (Route T).

A Turing machine cannot evaluate `⌈C₁ ℓ₂ ℓ₃⌉`, `⌈3 ℓ₂⌉`, `⌈z^{1-E}⌉` or
`⌈(log n)^{1.2}⌉` exactly, but it can compute integers within a constant
factor of them from iterated `Nat.log 2`. `InWindow` records the windows the
analysis (`Step2W`, `Step3W`, `ExtractionW`, `OutputW`) is proved for; the
exact scales `zscale`, `yscaleE`, `Tscale` of `Defs.lean` satisfy it, and so
do the machine's approximations.
-/
import Carmichael.Defs

set_option autoImplicit false

namespace Carmichael

/-- The scale window: `z ≍ C₁ ℓ₂ ℓ₃`, reservoir floor `w ≍ z^{99/100}`,
smoothness bound `y ≍ z^{1-E}`, and `T ≍ 3 ℓ₂`, each within the stated
constant factor. The floor condition is `z^{99/100} ≤ w + 1` so that the exact
floor `⌊z^{99/100}⌋₊` qualifies; membership `w < q` then gives
`z^{99/100} ≤ q`. -/
structure InWindow (C₁ E : ℝ) (n : ℕ) (z w y T : ℕ) : Prop where
  z_lo : C₁ * ell2 n * ell3 n ≤ (z : ℝ)
  z_hi : (z : ℝ) ≤ 4 * (C₁ * ell2 n * ell3 n)
  w_lo : (z : ℝ) ^ ((99 : ℝ) / 100) ≤ (w : ℝ) + 1
  w_hi : (w : ℝ) ≤ 4 * (z : ℝ) ^ ((99 : ℝ) / 100)
  y_lo : (z : ℝ) ^ ((1 : ℝ) - E) ≤ (y : ℝ)
  y_hi : (y : ℝ) ≤ 4 * (z : ℝ) ^ ((1 : ℝ) - E)
  T_lo : 3 * ell2 n ≤ (T : ℝ)
  T_hi : (T : ℝ) ≤ 5 * ell2 n

open Classical in
/-- Step 2 reservoir at windowed scales: the primes `q ∈ (w, z]` with `q - 1`
smooth up to `y`. -/
noncomputable def goodPrimesW (z w y : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter
    (fun q => q.Prime ∧ w < q ∧ SmoothUpTo y (q - 1))

/-- The exact scales of `Defs.lean` lie in the window (for `n` large enough
that `ℓ₂ ℓ₃ ≥ 1`, `E ≤ 1/2`, `C₁ ≥ 1`). -/
theorem inWindow_exact (C₁ E : ℝ) (hC : (1 : ℝ) ≤ C₁) (hE : 0 < E) (hE2 : E ≤ 1 / 2)
    (n : ℕ) (h2 : (1 : ℝ) ≤ ell2 n) (h3 : (1 : ℝ) ≤ ell3 n) :
    InWindow C₁ E n (zscale C₁ n) ⌊(zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100)⌋₊
      (yscaleE C₁ n E) (Tscale n) := by
  have hprod : (1 : ℝ) ≤ C₁ * ell2 n * ell3 n := by
    have a := mul_le_mul hC h2 zero_le_one (by linarith only [hC])
    have b := mul_le_mul a h3 zero_le_one (by linarith only [a])
    linarith only [b]
  have hz_lo : C₁ * ell2 n * ell3 n ≤ (zscale C₁ n : ℝ) := Nat.le_ceil _
  have hz1 : (1 : ℝ) ≤ (zscale C₁ n : ℝ) := le_trans hprod hz_lo
  have hz_hi : (zscale C₁ n : ℝ) ≤ 4 * (C₁ * ell2 n * ell3 n) := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ C₁ * ell2 n * ell3 n by linarith only [hprod])
    unfold zscale
    linarith only [this, hprod]
  have hz0 : (0 : ℝ) < (zscale C₁ n : ℝ) := by linarith only [hz1]
  have hw0 : (0 : ℝ) ≤ (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) := (Real.rpow_pos_of_pos hz0 _).le
  have hw1 : (1 : ℝ) ≤ (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) :=
    Real.one_le_rpow hz1 (by norm_num)
  have hy0 : (0 : ℝ) ≤ (zscale C₁ n : ℝ) ^ ((1 : ℝ) - E) := (Real.rpow_pos_of_pos hz0 _).le
  have hT2 : (0 : ℝ) ≤ 3 * ell2 n := by linarith only [h2]
  refine ⟨hz_lo, hz_hi, ?_, ?_, Nat.le_ceil _, ?_, Nat.le_ceil _, ?_⟩
  · exact (Nat.lt_floor_add_one _).le
  · have := Nat.floor_le hw0
    linarith only [this, hw0]
  · have := Nat.ceil_lt_add_one hy0
    unfold yscaleE
    have h4 : (1 : ℝ) ≤ (zscale C₁ n : ℝ) ^ ((1 : ℝ) - E) :=
      Real.one_le_rpow hz1 (by linarith only [hE2])
    linarith only [this, h4]
  · have := Nat.ceil_lt_add_one hT2
    unfold Tscale
    linarith only [this, h2]

end Carmichael
