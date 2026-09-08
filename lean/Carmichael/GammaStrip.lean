/-
Route Z, sortie I8: the Γ-bounds on the frozen strip `−101/100 ≤ Re z ≤ 3`.
Blueprint: routez/Z0b-density.md §2 (I8(a)–(d)), consumed by Lemma 4.2 and hence
by `DetectionEstimate`.  Cribs `Carmichael.Detection`'s I8(b) route (reflection +
Phragmén–Lindelöf, no complex Stirling — pinned Mathlib has none and none is
needed).

DELIVERED (fully proved, no sorry/axioms), with `C_Γ := 5184`:

* `norm_Gamma_mid`: `‖Γ z‖ ≤ 12(5/2+|y|)e^{−3|y|/2}` for `1/2 ≤ Re z ≤ 3/2`,
  at EVERY height (`Detection.norm_Gamma_le_exp_neg_im_mid` needs `|y| ≥ 1/2`;
  the `a = 1` shift of the LGrowth strip bound replaces `sin(πs/2)` by
  `cos(πs/2)`, whose zeros miss the strip, and the restriction disappears).
* `norm_Gamma_right`: `‖Γ z‖ ≤ 2592·e^{−|y|}` for `1/2 ≤ Re z ≤ 3`, walking up
  by `Γ(z) = (z−1)Γ(z−1)`.  The extra `e^{−|y|/2}` of the mid bound absorbs the
  polynomial factors, so no polynomial survives.
* `norm_Gamma_strip` (I8(c), FROZEN SHAPE, no polynomial factor):
  `‖Γ(x+iy)‖ ≤ C_Γ·(1/‖z‖ + 1/‖z+1‖ + 1)·e^{−|y|}` on `−101/100 ≤ x ≤ 3`.
* `norm_Gamma_sub_inv_le` (I8(a)): `‖Γ z − 1/z‖ ≤ C_Γ` for `0 < ‖z‖ ≤ 3/4`,
  `Re z ≥ −1/2`, via the Schwarz-lemma `dslope` bound on `ball 1 (7/8)`.
* `norm_Gamma_le_of_dist` (I8(b) on the frozen strip): `‖Γ(x+iy)‖ ≤ 201·C_Γ·
  e^{−|y|}` at distance `≥ 1/100` from `{0,−1}`.
* `integral_norm_Gamma_line_le` (I8(d)): the weighted line moment
  `∫_ℝ ‖Γ(x₀+iu)‖(1+|u|)² du ≤ 6432·C_Γ`.

DELTA vs the blueprint: I8(d)'s frozen constant is `C_Γ'' := 2010·C_Γ`, from the
exact `∫_ℝ e^{−|u|}(1+|u|)² du = 10`.  This file routes the moment through the
cruder `(1+t)²e^{−t} ≤ 8e^{−t/2}` and `∫_ℝ e^{−|u|/2} du = 4`, giving
`C_Γ'' = 8·4·201·C_Γ = 6432·C_Γ`.  Only the existence of an absolute constant is
consumed downstream.
-/
import Carmichael.Detection
import Mathlib.Analysis.Complex.Schwarz

set_option autoImplicit false

namespace Carmichael

open Complex
open scoped Real

namespace GammaStrip

/-- The absolute constant of blueprint I8. -/
def CGamma : ℝ := 5184

/-! ### Real and imaginary parts of the complex sine and cosine -/

/-- From `A² ≤ B²` and `0 ≤ B` conclude `A ≤ B`. -/
private lemma le_of_sq_le_sq₀ {A B : ℝ} (hB : 0 ≤ B) (h : A ^ 2 ≤ B ^ 2) : A ≤ B := by
  nlinarith

lemma norm_sin_sq (w : ℂ) :
    ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  have hre : (Complex.sin w).re = Real.sin w.re * Real.cosh w.im := by
    rw [Complex.sin_eq]
    simp [Complex.add_re, Complex.mul_re, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
  have him : (Complex.sin w).im = Real.cos w.re * Real.sinh w.im := by
    rw [Complex.sin_eq]
    simp [Complex.add_im, Complex.mul_im, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
      ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
  have hn : ‖Complex.sin w‖ ^ 2 = (Complex.sin w).re ^ 2 + (Complex.sin w).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [hn, hre, him]
  linear_combination (Real.sin w.re ^ 2) * Real.cosh_sq_sub_sinh_sq w.im
    + (Real.sinh w.im ^ 2) * Real.sin_sq_add_cos_sq w.re

lemma abs_sin_re_le_norm_sin (w : ℂ) : |Real.sin w.re| ≤ ‖Complex.sin w‖ :=
  le_of_sq_le_sq₀ (norm_nonneg _) (by
    rw [sq_abs, norm_sin_sq]; nlinarith [sq_nonneg (Real.sinh w.im)])

lemma abs_sinh_im_le_norm_sin (w : ℂ) : |Real.sinh w.im| ≤ ‖Complex.sin w‖ :=
  le_of_sq_le_sq₀ (norm_nonneg _) (by
    rw [sq_abs, norm_sin_sq]; nlinarith [sq_nonneg (Real.sin w.re)])

/-- `cos w = sin (π/2 − w)`, in the form needed below. -/
private lemma cos_eq_sin_sub (w : ℂ) :
    Complex.cos w = Complex.sin ((↑π / 2 : ℂ) - w) := (Complex.sin_pi_div_two_sub w).symm

lemma abs_cos_re_le_norm_cos (w : ℂ) : |Real.cos w.re| ≤ ‖Complex.cos w‖ := by
  have h := abs_sin_re_le_norm_sin ((↑π / 2 : ℂ) - w)
  rw [← cos_eq_sin_sub w] at h
  have hre : ((↑π / 2 : ℂ) - w).re = π / 2 - w.re := by
    simp [Complex.sub_re]
  rw [hre, Real.sin_pi_div_two_sub] at h
  exact h

lemma abs_sinh_im_le_norm_cos (w : ℂ) : |Real.sinh w.im| ≤ ‖Complex.cos w‖ := by
  have h := abs_sinh_im_le_norm_sin ((↑π / 2 : ℂ) - w)
  rw [← cos_eq_sin_sub w] at h
  have him : ((↑π / 2 : ℂ) - w).im = -w.im := by
    simp [Complex.sub_im]
  rw [him, Real.sinh_neg, abs_neg] at h
  exact h

/-! ### The mid strip `1/2 ≤ Re z ≤ 3/2`, at every height -/

/-- The LGrowth reflection/Phragmén–Lindelöf strip bound with the `a = 1` shift:
the `sin` becomes a `cos`, whose zeros lie off the strip. -/
lemma norm_Gamma_one_sub_mul_cos_le {s : ℂ} (h1 : -(1/2 : ℝ) ≤ s.re) (h2 : s.re ≤ 1/2) :
    ‖Complex.Gamma (1 - s) * Complex.cos (↑π * s / 2)‖ ≤ 3 * (2 + ‖s‖) := by
  have h := Carmichael.norm_Gamma_one_sub_mul_sin_le 1 h1 h2
  rw [show (↑π * (s + ((1:ℝ):ℂ)) / 2) = ↑π/2 - -(↑π * s / 2) from by push_cast; ring,
    Complex.sin_pi_div_two_sub, Complex.cos_neg] at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **Γ-decay on the mid strip at every height**: `‖Γ z‖ ≤ 12(5/2+|y|)e^{−3|y|/2}`
for `1/2 ≤ Re z ≤ 3/2`.  Unlike `Detection.norm_Gamma_le_exp_neg_im_mid` this
carries no `|y| ≥ 1/2` restriction: `cos(πs/2)` is bounded below by
`cos(π/4) > 0` on the strip, whereas `sin(πs/2)` vanishes at `s = 0`. -/
theorem norm_Gamma_mid (z : ℂ) (h1 : (1:ℝ)/2 ≤ z.re) (h2 : z.re ≤ 3/2) :
    ‖Complex.Gamma z‖ ≤ 12 * (5/2 + |z.im|) * Real.exp (-(3/2) * |z.im|) := by
  set u : ℝ := |z.im| with hu
  have hu0 : (0:ℝ) ≤ u := abs_nonneg _
  have hpi1 : (3:ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hpi2 : π ≤ 3.15 := by linarith [Real.pi_lt_d2]
  set s : ℂ := 1 - z with hsdef
  have hsre : s.re = 1 - z.re := by rw [hsdef]; simp [Complex.sub_re]
  have hsim : s.im = -z.im := by rw [hsdef]; simp [Complex.sub_im]
  have hs1 : -(1/2 : ℝ) ≤ s.re := by rw [hsre]; linarith
  have hs2 : s.re ≤ 1/2 := by rw [hsre]; linarith
  have hstrip := norm_Gamma_one_sub_mul_cos_le hs1 hs2
  rw [show (1:ℂ) - s = z from by rw [hsdef]; ring] at hstrip
  set w : ℂ := (↑π * s / 2) with hwdef
  have hwval : w = ((π/2 : ℝ) : ℂ) * s := by rw [hwdef]; push_cast; ring
  have hwre : w.re = (π/2) * s.re := by
    rw [hwval, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
  have hwim : w.im = (π/2) * s.im := by
    rw [hwval, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; ring
  -- lower bound from the real part of `w`
  have hwre_abs : |w.re| ≤ 0.7875 := by
    rw [hwre, abs_mul, abs_of_pos (by linarith : (0:ℝ) < π/2)]
    have : |s.re| ≤ 1/2 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg s.re]
  have hcosre : (0.68 : ℝ) ≤ Real.cos w.re := by
    have hb := Real.one_sub_sq_div_two_le_cos (x := w.re)
    nlinarith [abs_nonneg w.re, sq_abs w.re]
  have hA : (0.68 : ℝ) ≤ ‖Complex.cos w‖ := by
    have h := abs_cos_re_le_norm_cos w
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ Real.cos w.re)] at h
    linarith
  -- lower bound from the imaginary part of `w`
  have hwim_abs : |w.im| = π * u / 2 := by
    rw [hwim, hsim, abs_mul, abs_neg, abs_of_pos (by linarith : (0:ℝ) < π/2), ← hu]
    ring
  have hB : Real.sinh (π * u / 2) ≤ ‖Complex.cos w‖ := by
    have h := abs_sinh_im_le_norm_cos w
    rwa [Real.abs_sinh, hwim_abs] at h
  have hB' : Real.sinh (3 * u / 2) ≤ ‖Complex.cos w‖ := by
    refine le_trans (Real.sinh_le_sinh.mpr ?_) hB
    nlinarith
  have hsinh_low : (Real.exp (3 * u / 2) - 1) / 2 ≤ Real.sinh (3 * u / 2) := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (-(3 * u / 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; linarith
    linarith
  have hE : (0:ℝ) < Real.exp (3 * u / 2) := Real.exp_pos _
  have hcos_low : Real.exp (3 * u / 2) / 4 ≤ ‖Complex.cos w‖ := by
    linarith [hA, hB', hsinh_low]
  -- the numerator
  have hnorm_s : ‖s‖ ≤ 1/2 + u := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : |s.re| ≤ 1/2 := by rw [hsre, abs_le]; constructor <;> linarith
    have him : |s.im| = u := by rw [hsim, abs_neg, hu]
    linarith
  have hG0 : (0:ℝ) ≤ ‖Complex.Gamma z‖ := norm_nonneg _
  have hkey : ‖Complex.Gamma z‖ * ‖Complex.cos w‖ ≤ 3 * (5/2 + u) := by
    rw [← norm_mul]
    exact hstrip.trans (by linarith)
  have hfinal : ‖Complex.Gamma z‖ * Real.exp (3 * u / 2) ≤ 12 * (5/2 + u) := by
    nlinarith [hkey, hcos_low, hG0]
  calc ‖Complex.Gamma z‖
      = (‖Complex.Gamma z‖ * Real.exp (3 * u / 2)) * (Real.exp (3 * u / 2))⁻¹ := by
        field_simp
    _ ≤ (12 * (5/2 + u)) * (Real.exp (3 * u / 2))⁻¹ :=
        mul_le_mul_of_nonneg_right hfinal (by positivity)
    _ = 12 * (5/2 + u) * Real.exp (-(3/2) * u) := by
        rw [← Real.exp_neg]; ring_nf


/-! ### The strip `1/2 ≤ Re z ≤ 3` -/

/-- `12(2+u)(1+u)(5/2+u) ≤ 2592·e^{u/2}` for `u ≥ 0`: the extra half-exponential
of `norm_Gamma_mid` swallows the polynomial produced by the two `Γ(z+1) = zΓ(z)`
shifts.  Proved from `e^{u/6} ≥ 1 + u/6`, cubed. -/
private lemma poly_le_exp_half (u : ℝ) (hu : 0 ≤ u) :
    12 * (2 + u) * (1 + u) * (5/2 + u) ≤ 2592 * Real.exp (u/2) := by
  have h6 : (1:ℝ) + u/6 ≤ Real.exp (u/6) := by linarith [Real.add_one_le_exp (u/6)]
  have hpos : (0:ℝ) ≤ 1 + u/6 := by linarith
  have hE : (0:ℝ) < Real.exp (u/6) := Real.exp_pos _
  have hsq : (1 + u/6) * (1 + u/6) ≤ Real.exp (u/6) * Real.exp (u/6) :=
    mul_le_mul h6 h6 hpos hE.le
  have hcube : (1 + u/6) * (1 + u/6) * (1 + u/6)
      ≤ Real.exp (u/6) * Real.exp (u/6) * Real.exp (u/6) :=
    mul_le_mul hsq h6 hpos (by positivity)
  have hexp : Real.exp (u/6) * Real.exp (u/6) * Real.exp (u/6) = Real.exp (u/2) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [← hexp]
  nlinarith [hcube, hu]

/-- `norm_Gamma_mid` with the height named. -/
private lemma norm_Gamma_mid_at (z : ℂ) (h1 : (1:ℝ)/2 ≤ z.re) (h2 : z.re ≤ 3/2)
    (u : ℝ) (hueq : |z.im| = u) :
    ‖Complex.Gamma z‖ ≤ 12 * (5/2 + u) * Real.exp (-(3/2) * u) := by
  rw [← hueq]; exact norm_Gamma_mid z h1 h2

/-- `Γ(z) = (z−1)·Γ(z−1)` whenever `z ≠ 1`. -/
private lemma Gamma_eq_shift (z : ℂ) (hz : z - 1 ≠ 0) :
    Complex.Gamma z = (z - 1) * Complex.Gamma (z - 1) := by
  have h := Complex.Gamma_add_one (z - 1) hz
  rwa [sub_add_cancel] at h

set_option maxHeartbeats 1000000 in
/-- **Γ-decay on `1/2 ≤ Re z ≤ 3`**: `‖Γ z‖ ≤ 2592·e^{−|Im z|}`.  Walks up from
the mid strip by `Γ(z) = (z−1)Γ(z−1)`; the polynomial factors are absorbed by
the surplus decay `e^{−|y|/2}` of `norm_Gamma_mid`.  No Stirling. -/
theorem norm_Gamma_right (z : ℂ) (h1 : (1:ℝ)/2 ≤ z.re) (h2 : z.re ≤ 3) :
    ‖Complex.Gamma z‖ ≤ 2592 * Real.exp (-|z.im|) := by
  set u : ℝ := |z.im| with hu
  have hu0 : (0:ℝ) ≤ u := abs_nonneg _
  have hu2 : (0:ℝ) ≤ u ^ 2 := sq_nonneg u
  have hu3 : (0:ℝ) ≤ u ^ 3 := by positivity
  have hE0 : (0:ℝ) < Real.exp (-(3/2) * u) := Real.exp_pos _
  set P : ℝ := 12 * (2 + u) * (1 + u) * (5/2 + u) with hPdef
  have hP0 : (0:ℝ) ≤ P := by rw [hPdef]; positivity
  -- the polynomial-times-`e^{−3u/2}` bound
  have hmain : ‖Complex.Gamma z‖ ≤ P * Real.exp (-(3/2) * u) := by
    rcases le_or_gt z.re (3/2 : ℝ) with hA | hA
    · have h := norm_Gamma_mid_at z h1 hA u rfl
      have hfac : 12 * (5/2 + u) ≤ P := by rw [hPdef]; nlinarith [hu0, hu2, hu3]
      calc ‖Complex.Gamma z‖ ≤ 12 * (5/2 + u) * Real.exp (-(3/2) * u) := h
        _ ≤ P * Real.exp (-(3/2) * u) := mul_le_mul_of_nonneg_right hfac hE0.le
    rcases le_or_gt z.re (5/2 : ℝ) with hB | hB
    · -- one shift
      have hre1 : (z - 1).re = z.re - 1 := by simp [Complex.sub_re]
      have him1 : (z - 1).im = z.im := by simp [Complex.sub_im]
      have hne : z - 1 ≠ 0 := by
        intro h
        rw [h] at hre1
        simp at hre1
        linarith
      have hb := norm_Gamma_mid_at (z - 1) (by rw [hre1]; linarith) (by rw [hre1]; linarith)
        u (by rw [him1, hu])
      have hnz : ‖z - 1‖ ≤ 3/2 + u := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        have hr : |(z - 1).re| ≤ 3/2 := by rw [hre1, abs_le]; constructor <;> linarith
        have hi : |(z - 1).im| = u := by rw [him1, hu]
        linarith
      have hfac : (3/2 + u) * (12 * (5/2 + u)) ≤ P := by rw [hPdef]; nlinarith [hu0, hu2, hu3]
      calc ‖Complex.Gamma z‖ = ‖z - 1‖ * ‖Complex.Gamma (z - 1)‖ := by
            rw [← norm_mul, ← Gamma_eq_shift z hne]
        _ ≤ (3/2 + u) * (12 * (5/2 + u) * Real.exp (-(3/2) * u)) := by
            refine mul_le_mul hnz hb (norm_nonneg _) (by linarith)
        _ = ((3/2 + u) * (12 * (5/2 + u))) * Real.exp (-(3/2) * u) := by ring
        _ ≤ P * Real.exp (-(3/2) * u) := mul_le_mul_of_nonneg_right hfac hE0.le
    · -- two shifts
      have hre1 : (z - 1).re = z.re - 1 := by simp [Complex.sub_re]
      have him1 : (z - 1).im = z.im := by simp [Complex.sub_im]
      have hre2 : (z - 1 - 1).re = z.re - 2 := by simp [Complex.sub_re]; ring
      have him2 : (z - 1 - 1).im = z.im := by simp [Complex.sub_im]
      have hne1 : z - 1 ≠ 0 := by
        intro h; rw [h] at hre1; simp at hre1; linarith
      have hne2 : (z - 1) - 1 ≠ 0 := by
        intro h; rw [h] at hre2; simp at hre2; linarith
      have hb := norm_Gamma_mid_at (z - 1 - 1) (by rw [hre2]; linarith)
        (by rw [hre2]; linarith) u (by rw [him2, hu])
      have hn1 : ‖z - 1‖ ≤ 2 + u := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        have hr : |(z - 1).re| ≤ 2 := by rw [hre1, abs_le]; constructor <;> linarith
        have hi : |(z - 1).im| = u := by rw [him1, hu]
        linarith
      have hn2 : ‖z - 1 - 1‖ ≤ 1 + u := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        have hr : |(z - 1 - 1).re| ≤ 1 := by rw [hre2, abs_le]; constructor <;> linarith
        have hi : |(z - 1 - 1).im| = u := by rw [him2, hu]
        linarith
      have hfac : (2 + u) * ((1 + u) * (12 * (5/2 + u))) ≤ P := by rw [hPdef]; nlinarith [hu0, hu2, hu3]
      have hstep : ‖Complex.Gamma (z - 1)‖
          ≤ (1 + u) * (12 * (5/2 + u) * Real.exp (-(3/2) * u)) := by
        calc ‖Complex.Gamma (z - 1)‖ = ‖z - 1 - 1‖ * ‖Complex.Gamma (z - 1 - 1)‖ := by
              rw [← norm_mul, ← Gamma_eq_shift (z - 1) hne2]
          _ ≤ (1 + u) * (12 * (5/2 + u) * Real.exp (-(3/2) * u)) :=
              mul_le_mul hn2 hb (norm_nonneg _) (by linarith)
      calc ‖Complex.Gamma z‖ = ‖z - 1‖ * ‖Complex.Gamma (z - 1)‖ := by
            rw [← norm_mul, ← Gamma_eq_shift z hne1]
        _ ≤ (2 + u) * ((1 + u) * (12 * (5/2 + u) * Real.exp (-(3/2) * u))) := by
            refine mul_le_mul hn1 hstep (norm_nonneg _) (by linarith)
        _ = ((2 + u) * ((1 + u) * (12 * (5/2 + u)))) * Real.exp (-(3/2) * u) := by ring
        _ ≤ P * Real.exp (-(3/2) * u) := mul_le_mul_of_nonneg_right hfac hE0.le
  -- absorb the polynomial into the surplus `e^{−u/2}`
  have hEh : (0:ℝ) < Real.exp (u/2) := Real.exp_pos _
  have hEn : (0:ℝ) < Real.exp (-(u/2)) := Real.exp_pos _
  have heq : Real.exp (-(u/2)) * Real.exp (u/2) = 1 := by
    rw [← Real.exp_add]; simp
  have hPabs : P * Real.exp (-(u/2)) ≤ 2592 := by
    have hpoly : P ≤ 2592 * Real.exp (u/2) := by rw [hPdef]; exact poly_le_exp_half u hu0
    nlinarith [hpoly, hEn, heq]
  have hsplit : Real.exp (-(3/2) * u) = Real.exp (-(u/2)) * Real.exp (-u) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖Complex.Gamma z‖ ≤ P * Real.exp (-(3/2) * u) := hmain
    _ = (P * Real.exp (-(u/2))) * Real.exp (-u) := by rw [hsplit]; ring
    _ ≤ 2592 * Real.exp (-u) := mul_le_mul_of_nonneg_right hPabs (Real.exp_pos _).le


/-! ### I8(c): the full strip `−101/100 ≤ Re z ≤ 3` -/

lemma CGamma_def : CGamma = 5184 := rfl

lemma CGamma_pos : 0 < CGamma := by rw [CGamma_def]; norm_num

/-- `(ab)⁻¹ ≤ 2(a⁻¹ + b⁻¹)` for `a, b > 0` with `a + b ≥ 1`: the two poles `0`
and `−1` are a unit apart, so they never both come close. -/
private lemma inv_mul_le_two_mul_add_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : 1 ≤ a + b) : (a * b)⁻¹ ≤ 2 * (a⁻¹ + b⁻¹) := by
  have hai : (0:ℝ) < a⁻¹ := by positivity
  have hbi : (0:ℝ) < b⁻¹ := by positivity
  rw [mul_inv]
  rcases le_or_gt (1/2 : ℝ) a with h | h
  · have h2 : a⁻¹ ≤ 2 := by
      have hc : a⁻¹ * a = 1 := inv_mul_cancel₀ ha.ne'
      nlinarith
    nlinarith
  · have hb2 : (1:ℝ)/2 ≤ b := by linarith
    have h2 : b⁻¹ ≤ 2 := by
      have hc : b⁻¹ * b = 1 := inv_mul_cancel₀ hb.ne'
      nlinarith
    nlinarith

private lemma Gamma_zero' : Complex.Gamma 0 = 0 := by simp

private lemma Gamma_neg_one' : Complex.Gamma (-1) = 0 := by
  have h := Complex.Gamma_neg_nat_eq_zero 1
  norm_num at h
  exact h

set_option maxHeartbeats 1000000 in
/-- **Blueprint interface I8(c)** with `C_Γ = 5184`, in the frozen shape (no
polynomial factor): `‖Γ(x+iy)‖ ≤ C_Γ(1/‖z‖ + 1/‖z+1‖ + 1)e^{−|y|}` on the strip
`−101/100 ≤ x ≤ 3`.  Left of `Re z = 1/2` the two shifts
`Γ(z) = Γ(z+2)/(z(z+1))` produce the two pole factors; they never both blow up,
since `‖z‖ + ‖z+1‖ ≥ 1`.  At the poles `z ∈ {0,−1}` both sides are `≥ 0` with
`Γ = 0`, so no exclusion is needed. -/
theorem norm_Gamma_strip (z : ℂ) (h1 : -(101/100 : ℝ) ≤ z.re) (h2 : z.re ≤ 3) :
    ‖Complex.Gamma z‖ ≤ CGamma * (‖z‖⁻¹ + ‖z + 1‖⁻¹ + 1) * Real.exp (-|z.im|) := by
  rw [CGamma_def]
  have hia : (0:ℝ) ≤ ‖z‖⁻¹ := by positivity
  have hib : (0:ℝ) ≤ ‖z + 1‖⁻¹ := by positivity
  have hexp0 : (0:ℝ) < Real.exp (-|z.im|) := Real.exp_pos _
  rcases le_or_gt (1/2 : ℝ) z.re with hR | hL
  · calc ‖Complex.Gamma z‖ ≤ 2592 * Real.exp (-|z.im|) := norm_Gamma_right z hR h2
      _ ≤ 5184 * (‖z‖⁻¹ + ‖z + 1‖⁻¹ + 1) * Real.exp (-|z.im|) := by
          have hc : (2592:ℝ) ≤ 5184 * (‖z‖⁻¹ + ‖z + 1‖⁻¹ + 1) := by linarith
          exact mul_le_mul_of_nonneg_right hc hexp0.le
  · by_cases hz0 : z = 0
    · rw [hz0, Gamma_zero', norm_zero]
      positivity
    by_cases hz1 : z = -1
    · rw [hz1, Gamma_neg_one', norm_zero]
      positivity
    have hz1ne : z + 1 ≠ 0 := fun h => hz1 (by linear_combination h)
    have hnz : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
    have hnz1 : (0:ℝ) < ‖z + 1‖ := norm_pos_iff.mpr hz1ne
    -- `Γ(z+2) = (z+1)·z·Γ(z)`
    have hstep1 : Complex.Gamma (z + 1) = z * Complex.Gamma z := Complex.Gamma_add_one z hz0
    have hstep2 : Complex.Gamma (z + 2) = (z + 1) * Complex.Gamma (z + 1) := by
      have h := Complex.Gamma_add_one (z + 1) hz1ne
      rw [show z + 1 + 1 = z + 2 from by ring] at h
      exact h
    have hprod : Complex.Gamma (z + 2) = (z + 1) * z * Complex.Gamma z := by
      rw [hstep2, hstep1]; ring
    have hre2 : (z + 2).re = z.re + 2 := by simp [Complex.add_re]
    have him2 : (z + 2).im = z.im := by simp [Complex.add_im]
    have hb := norm_Gamma_right (z + 2) (by rw [hre2]; linarith) (by rw [hre2]; linarith)
    rw [him2] at hb
    have hG : ‖Complex.Gamma z‖ * (‖z‖ * ‖z + 1‖) ≤ 2592 * Real.exp (-|z.im|) := by
      calc ‖Complex.Gamma z‖ * (‖z‖ * ‖z + 1‖)
          = ‖(z + 1) * z * Complex.Gamma z‖ := by
            rw [norm_mul, norm_mul]; ring
        _ = ‖Complex.Gamma (z + 2)‖ := by rw [hprod]
        _ ≤ 2592 * Real.exp (-|z.im|) := hb
    have hsum : (1:ℝ) ≤ ‖z‖ + ‖z + 1‖ := by
      have h := norm_sub_le (z + 1) z
      rw [show z + 1 - z = (1:ℂ) from by ring, norm_one] at h
      linarith
    have hkey := inv_mul_le_two_mul_add_inv hnz hnz1 hsum
    have hA0 : (0:ℝ) < ‖z‖ * ‖z + 1‖ := by positivity
    calc ‖Complex.Gamma z‖
        = (‖Complex.Gamma z‖ * (‖z‖ * ‖z + 1‖)) * (‖z‖ * ‖z + 1‖)⁻¹ := by
          field_simp
      _ ≤ (2592 * Real.exp (-|z.im|)) * (‖z‖ * ‖z + 1‖)⁻¹ :=
          mul_le_mul_of_nonneg_right hG (by positivity)
      _ ≤ (2592 * Real.exp (-|z.im|)) * (2 * (‖z‖⁻¹ + ‖z + 1‖⁻¹)) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ 5184 * (‖z‖⁻¹ + ‖z + 1‖⁻¹ + 1) * Real.exp (-|z.im|) := by
          nlinarith [hexp0.le, hia, hib]

/-- **I8(b) on the frozen strip**: at distance `≥ 1/100` from `{0,−1}` the pole
factors are `≤ 100` each, so `‖Γ(x+iy)‖ ≤ 201·C_Γ·e^{−|y|}`. -/
theorem norm_Gamma_le_of_dist (z : ℂ) (h1 : -(101/100 : ℝ) ≤ z.re) (h2 : z.re ≤ 3)
    (h3 : 1/100 ≤ ‖z‖) (h4 : 1/100 ≤ ‖z + 1‖) :
    ‖Complex.Gamma z‖ ≤ 201 * CGamma * Real.exp (-|z.im|) := by
  have hnz : (0:ℝ) < ‖z‖ := by linarith
  have hnz1 : (0:ℝ) < ‖z + 1‖ := by linarith
  have hia : ‖z‖⁻¹ ≤ 100 := by
    have hc : ‖z‖⁻¹ * ‖z‖ = 1 := inv_mul_cancel₀ hnz.ne'
    have : (0:ℝ) < ‖z‖⁻¹ := by positivity
    nlinarith
  have hib : ‖z + 1‖⁻¹ ≤ 100 := by
    have hc : ‖z + 1‖⁻¹ * ‖z + 1‖ = 1 := inv_mul_cancel₀ hnz1.ne'
    have : (0:ℝ) < ‖z + 1‖⁻¹ := by positivity
    nlinarith
  have hexp0 : (0:ℝ) < Real.exp (-|z.im|) := Real.exp_pos _
  refine (norm_Gamma_strip z h1 h2).trans ?_
  have hc : CGamma * (‖z‖⁻¹ + ‖z + 1‖⁻¹ + 1) ≤ 201 * CGamma := by
    have := CGamma_pos
    nlinarith
  exact mul_le_mul_of_nonneg_right hc hexp0.le


/-! ### I8(a): `‖Γ(z) − 1/z‖ ≤ C_Γ` near the origin -/

/-- `‖Γ w‖ ≤ 41` on the mid strip at heights `≤ 7/8`. -/
private lemma norm_Gamma_mid_le_41 {w : ℂ} (h1 : (1:ℝ)/2 ≤ w.re) (h2 : w.re ≤ 3/2)
    (hu : |w.im| ≤ 7/8) : ‖Complex.Gamma w‖ ≤ 41 := by
  have h := norm_Gamma_mid w h1 h2
  have hu0 : (0:ℝ) ≤ |w.im| := abs_nonneg _
  have he : Real.exp (-(3/2) * |w.im|) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have h0 : (0:ℝ) ≤ 12 * (5/2 + |w.im|) := by positivity
  nlinarith

/-- `‖Γ w‖ ≤ 328` on the open ball `ball 1 (7/8)`. -/
private lemma norm_Gamma_ball_le {w : ℂ} (hw : w ∈ Metric.ball (1:ℂ) (7/8)) :
    ‖Complex.Gamma w‖ ≤ 328 := by
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hre : |(w - 1).re| ≤ ‖w - 1‖ := Complex.abs_re_le_norm _
  have him : |(w - 1).im| ≤ ‖w - 1‖ := Complex.abs_im_le_norm _
  have hre' : (w - 1).re = w.re - 1 := by simp [Complex.sub_re]
  have him' : (w - 1).im = w.im := by simp [Complex.sub_im]
  rw [hre'] at hre
  rw [him'] at him
  have hrl : (1:ℝ)/8 < w.re := by
    have := abs_lt.mp (lt_of_le_of_lt hre hw); linarith [this.1]
  have hrr : w.re < 15/8 := by
    have := abs_lt.mp (lt_of_le_of_lt hre hw); linarith [this.2]
  have hiu : |w.im| ≤ 7/8 := le_of_lt (lt_of_le_of_lt him hw)
  rcases le_or_gt (1/2 : ℝ) w.re with hA | hA
  · rcases le_or_gt w.re (3/2 : ℝ) with hB | hB
    · linarith [norm_Gamma_mid_le_41 hA hB hiu]
    · -- one step down
      have hne : w - 1 ≠ 0 := by
        intro h
        have : (w - 1).re = 0 := by rw [h]; simp
        rw [hre'] at this; linarith
      have hre1 : (w - 1).re = w.re - 1 := hre'
      have hb := norm_Gamma_mid_le_41 (w := w - 1) (by rw [hre1]; linarith)
        (by rw [hre1]; linarith) (by rw [him']; exact hiu)
      have hnw : ‖w - 1‖ ≤ 7/8 := hw.le
      calc ‖Complex.Gamma w‖ = ‖w - 1‖ * ‖Complex.Gamma (w - 1)‖ := by
            rw [← norm_mul, ← Gamma_eq_shift w hne]
        _ ≤ (7/8) * 41 := mul_le_mul hnw hb (norm_nonneg _) (by norm_num)
        _ ≤ 328 := by norm_num
  · -- one step up
    have hwne : w ≠ 0 := by
      intro h
      have : w.re = 0 := by rw [h]; simp
      linarith
    have hre1 : (w + 1).re = w.re + 1 := by simp [Complex.add_re]
    have him1 : (w + 1).im = w.im := by simp [Complex.add_im]
    have hb := norm_Gamma_mid_le_41 (w := w + 1) (by rw [hre1]; linarith)
      (by rw [hre1]; linarith) (by rw [him1]; exact hiu)
    have hnw : (1:ℝ)/8 ≤ ‖w‖ := by
      have := Complex.abs_re_le_norm w
      have h2 : w.re ≤ |w.re| := le_abs_self _
      linarith
    have hkey : ‖w‖ * ‖Complex.Gamma w‖ ≤ 41 := by
      rw [← norm_mul, ← Complex.Gamma_add_one w hwne]; exact hb
    nlinarith [norm_nonneg (Complex.Gamma w), hnw, hkey]

private lemma differentiableOn_Gamma_ball :
    DifferentiableOn ℂ Complex.Gamma (Metric.ball (1:ℂ) (7/8)) := by
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have hre : |(w - 1).re| ≤ ‖w - 1‖ := Complex.abs_re_le_norm _
  have hre' : (w - 1).re = w.re - 1 := by simp [Complex.sub_re]
  rw [hre'] at hre
  have hrl : (1:ℝ)/8 < w.re := by
    have := abs_lt.mp (lt_of_le_of_lt hre hw); linarith [this.1]
  refine (Complex.differentiableAt_Gamma w ?_).differentiableWithinAt
  intro m heq
  have : w.re = -(m : ℝ) := by rw [heq]; simp
  have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

private lemma mapsTo_Gamma_ball : Set.MapsTo Complex.Gamma (Metric.ball (1:ℂ) (7/8))
    (Metric.closedBall (Complex.Gamma 1) 400) := by
  intro w hw
  rw [Metric.mem_closedBall, dist_eq_norm, Complex.Gamma_one]
  calc ‖Complex.Gamma w - 1‖ ≤ ‖Complex.Gamma w‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
    _ ≤ 328 + 1 := by rw [norm_one]; linarith [norm_Gamma_ball_le hw]
    _ ≤ 400 := by norm_num

/-- **Blueprint interface I8(a)** with `C_Γ = 5184`: `‖Γ(z) − 1/z‖ ≤ C_Γ` for
`0 < ‖z‖ ≤ 3/4` and `Re z ≥ −1/2`.  Route: `Γ(z) − 1/z = (Γ(z+1) − Γ(1))/z` is
the Schwarz-lemma `dslope` of `Γ` at `1`, and `Γ` maps `ball 1 (7/8)` into
`closedBall (Γ 1) 400`, so the `dslope` is `≤ 400/(7/8) = 3200/7`. -/
theorem norm_Gamma_sub_inv_le (z : ℂ) (hz : z ≠ 0) (h1 : ‖z‖ ≤ 3/4)
    (_h2 : -(1/2 : ℝ) ≤ z.re) : ‖Complex.Gamma z - z⁻¹‖ ≤ CGamma := by
  have hmem : z + 1 ∈ Metric.ball (1:ℂ) (7/8) := by
    rw [Metric.mem_ball, dist_eq_norm, show z + 1 - 1 = z from by ring]
    linarith
  have hd := Complex.norm_dslope_le_div_of_mapsTo_ball differentiableOn_Gamma_ball
    mapsTo_Gamma_ball hmem
  have hne : z + 1 ≠ 1 := fun h => hz (by linear_combination h)
  rw [dslope_of_ne _ hne, slope_def_field, show z + 1 - 1 = z from by ring,
    Complex.Gamma_one] at hd
  have hΓ : Complex.Gamma (z + 1) = z * Complex.Gamma z := Complex.Gamma_add_one z hz
  have hkey : Complex.Gamma z - z⁻¹ = (Complex.Gamma (z + 1) - 1) / z := by
    rw [hΓ]; field_simp
  rw [hkey]
  refine hd.trans ?_
  rw [CGamma_def]; norm_num


/-! ### I8(d): the weighted line moment -/

open MeasureTheory in
private lemma integrable_exp_neg_abs_half :
    Integrable (fun u : ℝ => Real.exp (-(1/2) * |u|)) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0:ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic (a := 1/2) (by norm_num) 0).congr_fun ?_ measurableSet_Iic
    intro x hx
    simp only [Set.mem_Iic] at hx
    show Real.exp (1/2 * x) = Real.exp (-(1/2) * |x|)
    rw [abs_of_nonpos hx]
    congr 1
    ring
  · refine (integrableOn_exp_mul_Ioi (a := -(1/2)) (by norm_num) 0).congr_fun ?_
      measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    show Real.exp (-(1/2) * x) = Real.exp (-(1/2) * |x|)
    rw [abs_of_pos hx]

open MeasureTheory in
private lemma integral_exp_neg_abs_half : ∫ u : ℝ, Real.exp (-(1/2) * |u|) = 4 := by
  have h := integral_comp_abs (f := fun t : ℝ => Real.exp (-(1/2) * t))
  rw [integral_exp_mul_Ioi (by norm_num : (-(1/2):ℝ) < 0) 0] at h
  rw [h]
  norm_num

/-- `(1+t)²e^{−t} ≤ 8e^{−t/2}` for `t ≥ 0`. -/
private lemma weight_le (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ 2 * Real.exp (-t) ≤ 8 * Real.exp (-(1/2) * t) := by
  have h6 : (1:ℝ) + t/6 ≤ Real.exp (t/6) := by linarith [Real.add_one_le_exp (t/6)]
  have hpos : (0:ℝ) ≤ 1 + t/6 := by linarith
  have hE : (0:ℝ) < Real.exp (t/6) := Real.exp_pos _
  have hsq : (1 + t/6) * (1 + t/6) ≤ Real.exp (t/6) * Real.exp (t/6) :=
    mul_le_mul h6 h6 hpos hE.le
  have hcube : (1 + t/6) * (1 + t/6) * (1 + t/6)
      ≤ Real.exp (t/6) * Real.exp (t/6) * Real.exp (t/6) :=
    mul_le_mul hsq h6 hpos (by positivity)
  have hexp : Real.exp (t/6) * Real.exp (t/6) * Real.exp (t/6) = Real.exp (t/2) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hkey : (1 + t) ^ 2 ≤ 8 * Real.exp (t/2) := by
    rw [← hexp]
    nlinarith [hcube, ht, mul_nonneg ht (sq_nonneg (t - 4.5))]
  have hsplit : Real.exp (-t) = Real.exp (-(1/2) * t) * Real.exp (-(t/2)) := by
    rw [← Real.exp_add]; ring_nf
  have hinv : Real.exp (t/2) * Real.exp (-(t/2)) = 1 := by
    rw [← Real.exp_add]; simp
  have hEn : (0:ℝ) < Real.exp (-(t/2)) := Real.exp_pos _
  calc (1 + t) ^ 2 * Real.exp (-t)
      = ((1 + t) ^ 2 * Real.exp (-(t/2))) * Real.exp (-(1/2) * t) := by rw [hsplit]; ring
    _ ≤ 8 * Real.exp (-(1/2) * t) := by
        have h8 : (1 + t) ^ 2 * Real.exp (-(t/2)) ≤ 8 := by nlinarith [hkey, hEn, hinv]
        exact mul_le_mul_of_nonneg_right h8 (Real.exp_pos _).le

/-- On a vertical line at distance `≥ 1/100` from `{0,−1}`, `Γ` has no pole. -/
private lemma line_ne_neg_nat {x₀ : ℝ} (h1 : -(101/100 : ℝ) ≤ x₀)
    (h3 : 1/100 ≤ |x₀|) (h4 : 1/100 ≤ |x₀ + 1|) (u : ℝ) (m : ℕ) :
    ((x₀ : ℂ) + (u : ℂ) * Complex.I) ≠ -(m : ℂ) := by
  intro hm
  have hre : x₀ = -(m : ℝ) := by
    have := congrArg Complex.re hm
    simpa using this
  match m with
  | 0 => rw [show ((0:ℕ):ℝ) = 0 from by norm_num] at hre; rw [hre] at h3; norm_num at h3
  | 1 => rw [show ((1:ℕ):ℝ) = 1 from by norm_num] at hre; rw [hre] at h4; norm_num at h4
  | (n+2) =>
    have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
    rw [this] at hre
    linarith

open MeasureTheory in
/-- Continuity of `u ↦ Γ(x₀ + iu)` on a pole-free vertical line. -/
private lemma continuous_Gamma_line {x₀ : ℝ} (h1 : -(101/100 : ℝ) ≤ x₀)
    (h3 : 1/100 ≤ |x₀|) (h4 : 1/100 ≤ |x₀ + 1|) :
    Continuous (fun u : ℝ => Complex.Gamma ((x₀ : ℂ) + (u : ℂ) * Complex.I)) := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have hinner : Continuous (fun u : ℝ => ((x₀ : ℂ) + (u : ℂ) * Complex.I)) := by fun_prop
  have hΓ : ContinuousAt Complex.Gamma ((x₀ : ℂ) + (u : ℂ) * Complex.I) :=
    (Complex.differentiableAt_Gamma _ (line_ne_neg_nat h1 h3 h4 u)).continuousAt
  exact ContinuousAt.comp (f := fun u : ℝ => ((x₀ : ℂ) + (u : ℂ) * Complex.I)) hΓ
    hinner.continuousAt

/-- The pointwise line bound feeding I8(d). -/
private lemma line_ptwise {x₀ : ℝ} (h1 : -(101/100 : ℝ) ≤ x₀) (h2 : x₀ ≤ 3)
    (h3 : 1/100 ≤ |x₀|) (h4 : 1/100 ≤ |x₀ + 1|) (u : ℝ) :
    ‖Complex.Gamma ((x₀ : ℂ) + (u : ℂ) * Complex.I)‖ * (1 + |u|) ^ 2
      ≤ (8 * (201 * CGamma)) * Real.exp (-(1/2) * |u|) := by
  have hCpos := CGamma_pos
  have hzre : ((x₀ : ℂ) + (u : ℂ) * Complex.I).re = x₀ := by simp
  have hzim : ((x₀ : ℂ) + (u : ℂ) * Complex.I).im = u := by simp
  have hnz : 1/100 ≤ ‖(x₀ : ℂ) + (u : ℂ) * Complex.I‖ := by
    have h := Complex.abs_re_le_norm ((x₀ : ℂ) + (u : ℂ) * Complex.I)
    rw [hzre] at h; linarith
  have hz1re : ((x₀ : ℂ) + (u : ℂ) * Complex.I + 1).re = x₀ + 1 := by
    rw [Complex.add_re, hzre]; simp
  have hnz1 : 1/100 ≤ ‖(x₀ : ℂ) + (u : ℂ) * Complex.I + 1‖ := by
    have h := Complex.abs_re_le_norm ((x₀ : ℂ) + (u : ℂ) * Complex.I + 1)
    rw [hz1re] at h; linarith
  have hg := norm_Gamma_le_of_dist ((x₀ : ℂ) + (u : ℂ) * Complex.I)
    (by rw [hzre]; linarith) (by rw [hzre]; linarith) hnz hnz1
  rw [hzim] at hg
  have hw := weight_le |u| (abs_nonneg u)
  have hK0 : (0:ℝ) ≤ 201 * CGamma := by linarith
  calc ‖Complex.Gamma ((x₀ : ℂ) + (u : ℂ) * Complex.I)‖ * (1 + |u|) ^ 2
      ≤ (201 * CGamma * Real.exp (-|u|)) * (1 + |u|) ^ 2 :=
        mul_le_mul_of_nonneg_right hg (by positivity)
    _ = (201 * CGamma) * ((1 + |u|) ^ 2 * Real.exp (-|u|)) := by ring
    _ ≤ (201 * CGamma) * (8 * Real.exp (-(1/2) * |u|)) :=
        mul_le_mul_of_nonneg_left hw hK0
    _ = (8 * (201 * CGamma)) * Real.exp (-(1/2) * |u|) := by ring

open MeasureTheory in
/-- The I8(d) integrand is integrable. -/
theorem integrable_norm_Gamma_line {x₀ : ℝ} (h1 : -(101/100 : ℝ) ≤ x₀) (h2 : x₀ ≤ 3)
    (h3 : 1/100 ≤ |x₀|) (h4 : 1/100 ≤ |x₀ + 1|) :
    Integrable (fun u : ℝ =>
      ‖Complex.Gamma ((x₀ : ℂ) + (u : ℂ) * Complex.I)‖ * (1 + |u|) ^ 2) := by
  have hcont : Continuous (fun u : ℝ =>
      ‖Complex.Gamma ((x₀ : ℂ) + (u : ℂ) * Complex.I)‖ * (1 + |u|) ^ 2) :=
    ((continuous_Gamma_line h1 h3 h4).norm).mul (by fun_prop)
  refine Integrable.mono' (g := fun u : ℝ => (8 * (201 * CGamma)) * Real.exp (-(1/2) * |u|))
    (integrable_exp_neg_abs_half.const_mul _) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact line_ptwise h1 h2 h3 h4 u

open MeasureTheory in
/-- **Blueprint interface I8(d)**: the weighted line moment.  For `x₀` in the
frozen strip at distance `≥ 1/100` from `{0,−1}`,
`∫_ℝ ‖Γ(x₀+iu)‖(1+|u|)² du ≤ 6432·C_Γ`.  (The blueprint's frozen constant is
`2010·C_Γ`, from the exact `∫_ℝ e^{−|u|}(1+|u|)²du = 10`; this proof uses the
cruder `(1+t)²e^{−t} ≤ 8e^{−t/2}` and `∫_ℝ e^{−|u|/2}du = 4`.) -/
theorem integral_norm_Gamma_line_le {x₀ : ℝ} (h1 : -(101/100 : ℝ) ≤ x₀) (h2 : x₀ ≤ 3)
    (h3 : 1/100 ≤ |x₀|) (h4 : 1/100 ≤ |x₀ + 1|) :
    ∫ u : ℝ, ‖Complex.Gamma ((x₀ : ℂ) + (u : ℂ) * Complex.I)‖ * (1 + |u|) ^ 2
      ≤ 6432 * CGamma := by
  have hbound := integral_mono_of_nonneg
    (f := fun u : ℝ => ‖Complex.Gamma ((x₀ : ℂ) + (u : ℂ) * Complex.I)‖ * (1 + |u|) ^ 2)
    (g := fun u : ℝ => (8 * (201 * CGamma)) * Real.exp (-(1/2) * |u|))
    (Filter.Eventually.of_forall fun u => by positivity)
    (integrable_exp_neg_abs_half.const_mul _)
    (Filter.Eventually.of_forall fun u => line_ptwise h1 h2 h3 h4 u)
  refine hbound.trans ?_
  rw [integral_const_mul, integral_exp_neg_abs_half]
  rw [CGamma_def]
  norm_num

end GammaStrip
end Carmichael
