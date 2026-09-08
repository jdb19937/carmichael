/-
Route Z, sortie Z5 (file 1 of 2): rectangle contour integrals and the truncated
Perron kernel, self-contained over Mathlib.

MAIN RESULTS (all constants explicit numerals):

* `rectInt f z w` — the counterclockwise boundary integral of `f` over the closed
  rectangle with bottom-left corner `z` and top-right corner `w`, in exactly the
  edge convention of Mathlib's `Complex.integral_boundary_rect_eq_zero_of_...`
  (bottom − top + I·right − I·left).  The shape (though not the proofs) follows
  PNT+ (github.com/AlexKontorovich/PrimeNumberTheoremAnd, Apache 2.0),
  `ResidueCalcOnRectangles.lean`; nothing is ported verbatim.

* `rectInt_eq_zero` — Cauchy–Goursat on the rectangle (wrapper around Mathlib).

* `rectInt_inv_sub_pole` — the winding computation: if `p` lies strictly inside
  the rectangle, `∮ (s − p)⁻¹ ds = 2πi`.  Engine: explicit `Complex.log`
  antiderivatives on each edge (each edge misses the branch cut of the log
  centered at `p` that is used for it), plus `log v − log (−v) = ±πi` according
  to the sign of `Im v`.

* `rectInt_cauchy` — Cauchy integral formula on the rectangle for an entire
  function: `∮ f s/(s − p) ds = 2πi·f p` for `p` strictly inside.  Engine:
  `f s/(s − p) = f p·(s − p)⁻¹ + dslope f p s`, Mathlib's `dslope` giving the
  continuous-at-`p` difference quotient, killed by `rectInt_eq_zero` with the
  countable exceptional set `{p}`.

* `perronKernel u c T = (1/2π)·∫_{−T}^{T} u^{c+it}/(c+it) dt`, the sharp-cutoff
  truncated Perron kernel `(1/2πi)·∫_{c−iT}^{c+iT} u^s/s ds`, with the classical
  three-regime bounds (`c > 0 < T` throughout, `u > 0`):
  - `norm_perronKernel_sub_indicator_le` (far regime, `u ≠ 1`):
      `‖K(u) − 1_{u>1}‖ ≤ u^c/(T·|log u|)`;
  - `norm_perronKernel_le` (trivial regime, `c ≤ T`):
      `‖K(u)‖ ≤ u^c·(1 + log (T/c))/π` — used on the near-diagonal window,
      where it beats the far bound;
  - the far regime is proved by closing the contour with an explicit finite
    rectangle (left past the pole for `u > 1` via `rectInt_cauchy`, right and
    pole-free for `u < 1` via `rectInt_eq_zero`), the runaway edge being killed
    by an explicit choice of the far abscissa (no limits needed).

Consumed by `Carmichael.ExplicitFormula` (file 2 of Z5); see BVPLAN.md §4 item
Z5 and routez/Z0a-ledger.md §2/§7 — NOTE: the Z5 interface is re-frozen by this
sortie to the AGP p. 710 form (see the file-2 header); the kernel bounds above
are exactly what that form consumes.
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false

namespace Carmichael

open Complex Set intervalIntegral
open scoped Real Topology Interval

/-! ### Elementary helpers -/

section Helpers

lemma re_coord (x t : ℝ) : ((x : ℂ) + t * I).re = x := by simp

lemma im_coord (x t : ℝ) : ((x : ℂ) + t * I).im = t := by simp

/-- Norm of a positive real base raised to a complex exponent on a vertical or
horizontal parametrization. -/
lemma norm_cpow_coord {u : ℝ} (hu : 0 < u) (x t : ℝ) :
    ‖(u : ℂ) ^ ((x : ℂ) + t * I)‖ = u ^ x := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu, re_coord]

lemma coord_ne_zero_of_re {x t : ℝ} (hx : x ≠ 0) : ((x : ℂ) + t * I) ≠ 0 := fun h => by
  have := congrArg Complex.re h
  rw [re_coord] at this
  simp at this
  exact hx this

lemma coord_ne_zero_of_im {x t : ℝ} (ht : t ≠ 0) : ((x : ℂ) + t * I) ≠ 0 := fun h => by
  have := congrArg Complex.im h
  rw [im_coord] at this
  simp at this
  exact ht this

lemma norm_coord_ge_abs_re (x t : ℝ) : |x| ≤ ‖(x : ℂ) + t * I‖ := by
  have := Complex.abs_re_le_norm ((x : ℂ) + t * I)
  rwa [re_coord] at this

lemma norm_coord_ge_abs_im (x t : ℝ) : |t| ≤ ‖(x : ℂ) + t * I‖ := by
  have := Complex.abs_im_le_norm ((x : ℂ) + t * I)
  rwa [im_coord] at this

end Helpers

/-! ### The rectangle boundary integral -/

section RectInt

/-- The counterclockwise boundary integral of `f` over the closed rectangle with
bottom-left corner `z` and top-right corner `w` (assuming `z.re ≤ w.re`,
`z.im ≤ w.im`; the definition makes sense regardless).  The edge convention
matches Mathlib's `Complex.integral_boundary_rect_eq_zero_of_...` exactly:
bottom − top + I·(right) − I·(left). -/
noncomputable def rectInt (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (∫ x : ℝ in z.re..w.re, f (x + z.im * I)) - (∫ x : ℝ in z.re..w.re, f (x + w.im * I)) +
    I • (∫ y : ℝ in z.im..w.im, f (w.re + y * I)) -
    I • (∫ y : ℝ in z.im..w.im, f (z.re + y * I))

/-- **Cauchy–Goursat on a rectangle** (wrapper around Mathlib): the boundary
integral vanishes for a function continuous on the closed rectangle and
differentiable on the open rectangle off a countable set. -/
theorem rectInt_eq_zero {f : ℂ → ℂ} {z w : ℂ} (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f ([[z.re, w.re]] ×ℂ [[z.im, w.im]]))
    (Hd : ∀ x ∈ (Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
        Set.Ioo (min z.im w.im) (max z.im w.im)) \ s,
      DifferentiableAt ℂ f x) :
    rectInt f z w = 0 :=
  Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable f z w s hs Hc Hd

/-- The four boundary edges of the rectangle, as a set. -/
def rectFrame (z w : ℂ) : Set ℂ :=
  {s | (s.re ∈ [[z.re, w.re]] ∧ (s.im = z.im ∨ s.im = w.im)) ∨
       (s.im ∈ [[z.im, w.im]] ∧ (s.re = z.re ∨ s.re = w.re))}

lemma mem_rectFrame_horiz {z w : ℂ} {x t : ℝ} (hx : x ∈ [[z.re, w.re]])
    (ht : t = z.im ∨ t = w.im) : ((x : ℂ) + t * I) ∈ rectFrame z w := by
  left
  refine ⟨?_, ?_⟩
  · rwa [re_coord]
  · rw [im_coord]; exact ht

lemma mem_rectFrame_vert {z w : ℂ} {x t : ℝ} (ht : t ∈ [[z.im, w.im]])
    (hx : x = z.re ∨ x = w.re) : ((x : ℂ) + t * I) ∈ rectFrame z w := by
  right
  refine ⟨?_, ?_⟩
  · rwa [im_coord]
  · rw [re_coord]; exact hx

lemma rectFrame_subset (z w : ℂ) :
    rectFrame z w ⊆ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := by
  rintro s hs
  rw [Complex.mem_reProdIm]
  rcases hs with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩
  · exact ⟨h1, h2 ▸ left_mem_uIcc⟩
  · exact ⟨h1, h2 ▸ right_mem_uIcc⟩
  · exact ⟨h2 ▸ left_mem_uIcc, h1⟩
  · exact ⟨h2 ▸ right_mem_uIcc, h1⟩

lemma continuousOn_horiz {f : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (rectFrame z w))
    {t : ℝ} (ht : t = z.im ∨ t = w.im) :
    ContinuousOn (fun x : ℝ => f ((x : ℂ) + t * I)) [[z.re, w.re]] := by
  apply hf.comp ((Complex.continuous_ofReal.add continuous_const).continuousOn)
  intro x hx
  exact mem_rectFrame_horiz hx ht

lemma continuousOn_vert {f : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (rectFrame z w))
    {x : ℝ} (hx : x = z.re ∨ x = w.re) :
    ContinuousOn (fun t : ℝ => f ((x : ℂ) + t * I)) [[z.im, w.im]] := by
  apply hf.comp
  · exact (continuous_const.add ((Complex.continuous_ofReal.mul continuous_const))).continuousOn
  · intro t ht
    exact mem_rectFrame_vert ht hx

lemma intervalIntegrable_horiz {f : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (rectFrame z w))
    {t : ℝ} (ht : t = z.im ∨ t = w.im) :
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + t * I)) MeasureTheory.volume z.re w.re :=
  (continuousOn_horiz hf ht).intervalIntegrable

lemma intervalIntegrable_vert {f : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (rectFrame z w))
    {x : ℝ} (hx : x = z.re ∨ x = w.re) :
    IntervalIntegrable (fun t : ℝ => f ((x : ℂ) + t * I)) MeasureTheory.volume z.im w.im :=
  (continuousOn_vert hf hx).intervalIntegrable

/-- The boundary integral only depends on the values on the frame. -/
theorem rectInt_congr {f g : ℂ → ℂ} {z w : ℂ} (h : ∀ s ∈ rectFrame z w, f s = g s) :
    rectInt f z w = rectInt g z w := by
  unfold rectInt
  rw [intervalIntegral.integral_congr (g := fun x : ℝ => g ((x : ℂ) + z.im * I))
      (fun x hx => h _ (mem_rectFrame_horiz hx (Or.inl rfl))),
    intervalIntegral.integral_congr (g := fun x : ℝ => g ((x : ℂ) + w.im * I))
      (fun x hx => h _ (mem_rectFrame_horiz hx (Or.inr rfl))),
    intervalIntegral.integral_congr (g := fun y : ℝ => g ((w.re : ℂ) + y * I))
      (fun y hy => h _ (mem_rectFrame_vert hy (Or.inr rfl))),
    intervalIntegral.integral_congr (g := fun y : ℝ => g ((z.re : ℂ) + y * I))
      (fun y hy => h _ (mem_rectFrame_vert hy (Or.inl rfl)))]

theorem rectInt_const_mul (c : ℂ) (f : ℂ → ℂ) (z w : ℂ) :
    rectInt (fun s => c * f s) z w = c * rectInt f z w := by
  unfold rectInt
  simp only [intervalIntegral.integral_const_mul, smul_eq_mul]
  ring

theorem rectInt_add {f g : ℂ → ℂ} {z w : ℂ} (hf : ContinuousOn f (rectFrame z w))
    (hg : ContinuousOn g (rectFrame z w)) :
    rectInt (fun s => f s + g s) z w = rectInt f z w + rectInt g z w := by
  unfold rectInt
  rw [intervalIntegral.integral_add (intervalIntegrable_horiz hf (Or.inl rfl))
      (intervalIntegrable_horiz hg (Or.inl rfl)),
    intervalIntegral.integral_add (intervalIntegrable_horiz hf (Or.inr rfl))
      (intervalIntegrable_horiz hg (Or.inr rfl)),
    intervalIntegral.integral_add (intervalIntegrable_vert hf (Or.inr rfl))
      (intervalIntegrable_vert hg (Or.inr rfl)),
    intervalIntegral.integral_add (intervalIntegrable_vert hf (Or.inl rfl))
      (intervalIntegrable_vert hg (Or.inl rfl))]
  simp only [smul_eq_mul]
  ring

/-- Finite-sum version of `rectInt_add`. -/
theorem rectInt_sum {ι : Type*} (F : Finset ι) {f : ι → ℂ → ℂ} {z w : ℂ}
    (hf : ∀ i ∈ F, ContinuousOn (f i) (rectFrame z w)) :
    rectInt (fun s => ∑ i ∈ F, f i s) z w = ∑ i ∈ F, rectInt (f i) z w := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have : rectInt (fun _ => (0 : ℂ)) z w = 0 := by
      have := rectInt_const_mul 0 (fun _ => (1 : ℂ)) z w
      simpa using this
    simpa using this
  | insert a F ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ContinuousOn (f a) (rectFrame z w) := hf a (Finset.mem_insert_self a F)
    have h2 : ContinuousOn (fun s => ∑ i ∈ F, f i s) (rectFrame z w) := by
      apply continuousOn_finsetSum
      intro i hi
      exact hf i (Finset.mem_insert_of_mem hi)
    have := rectInt_add (z := z) (w := w) h1 h2
    rw [rectInt_congr (g := fun s => f a s + ∑ i ∈ F, f i s)
        (fun s _ => by rw [Finset.sum_insert ha]), this,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

end RectInt

/-! ### The winding computation: `∮ (s − p)⁻¹ ds = 2πi` -/

section Winding

/-- `log v − log (−v) = πi` in the open upper half-plane. -/
lemma log_sub_log_neg_of_im_pos {v : ℂ} (hv : 0 < v.im) :
    Complex.log v - Complex.log (-v) = π * I := by
  apply Complex.ext
  · rw [Complex.sub_re, Complex.log_re, Complex.log_re, norm_neg, sub_self]
    simp [Complex.mul_re]
  · rw [Complex.sub_im, Complex.log_im, Complex.log_im,
      Complex.arg_neg_eq_arg_sub_pi_of_im_pos hv]
    simp [Complex.mul_im]

/-- `log (−v) − log v = πi` in the open lower half-plane. -/
lemma log_neg_sub_log_of_im_neg {v : ℂ} (hv : v.im < 0) :
    Complex.log (-v) - Complex.log v = π * I := by
  apply Complex.ext
  · rw [Complex.sub_re, Complex.log_re, Complex.log_re, norm_neg, sub_self]
    simp [Complex.mul_re]
  · rw [Complex.sub_im, Complex.log_im, Complex.log_im,
      Complex.arg_neg_eq_arg_add_pi_of_im_neg hv]
    simp [Complex.mul_im]

/-- FTC on a horizontal edge at height `t ≠ Im p`, with the `Complex.log`
antiderivative. -/
lemma integral_horiz_inv {p : ℂ} {t : ℝ} (ht : t ≠ p.im) (a b : ℝ) :
    (∫ x : ℝ in a..b, ((x : ℂ) + t * I - p)⁻¹) =
      Complex.log ((b : ℂ) + t * I - p) - Complex.log ((a : ℂ) + t * I - p) := by
  have him : ∀ x : ℝ, ((x : ℂ) + t * I - p).im ≠ 0 := by
    intro x
    rw [Complex.sub_im, im_coord]
    exact sub_ne_zero.mpr ht
  have hne : ∀ x : ℝ, ((x : ℂ) + t * I - p) ≠ 0 := fun x h => him x (by rw [h]; rfl)
  have hderiv : ∀ x ∈ [[a, b]],
      HasDerivAt (fun x : ℝ => Complex.log ((x : ℂ) + t * I - p))
        (((x : ℂ) + t * I - p)⁻¹) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℂ => s + (t * I - p)) 1 (x : ℂ) :=
      (hasDerivAt_id _).add_const _
    have h2 : ((x : ℂ) + (t * I - p)) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      right
      have := him x
      rwa [sub_eq_add_neg, add_assoc, ← sub_eq_add_neg (t * I : ℂ) p] at this
    have h3 := (h1.clog h2).comp_ofReal (z := x)
    have h4 : (fun y : ℝ => Complex.log ((y : ℂ) + (t * I - p))) =
        fun y : ℝ => Complex.log ((y : ℂ) + t * I - p) := by
      funext y
      rw [add_sub_assoc]
    rw [h4] at h3
    simpa [one_div, add_sub_assoc] using h3
  have hcont : Continuous fun x : ℝ => ((x : ℂ) + t * I - p)⁻¹ := by
    apply Continuous.inv₀
    · exact (Complex.continuous_ofReal.add continuous_const).sub continuous_const
    · exact hne
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)

/-- FTC on the right vertical edge (`Re p < x`), `Complex.log` antiderivative. -/
lemma integral_vert_inv_right {p : ℂ} {x : ℝ} (hx : p.re < x) (t₁ t₂ : ℝ) :
    (∫ y : ℝ in t₁..t₂, I * ((x : ℂ) + y * I - p)⁻¹) =
      Complex.log ((x : ℂ) + t₂ * I - p) - Complex.log ((x : ℂ) + t₁ * I - p) := by
  have hre : ∀ y : ℝ, ((x : ℂ) + y * I - p).re = x - p.re := by
    intro y
    rw [Complex.sub_re, re_coord]
  have hne : ∀ y : ℝ, ((x : ℂ) + y * I - p) ≠ 0 := by
    intro y h
    have := hre y
    rw [h] at this
    simp at this
    linarith
  have hderiv : ∀ y ∈ [[t₁, t₂]],
      HasDerivAt (fun y : ℝ => Complex.log ((x : ℂ) + y * I - p))
        (I * ((x : ℂ) + y * I - p)⁻¹) y := by
    intro y _
    have h1 : HasDerivAt (fun s : ℂ => (x : ℂ) + s * I - p) I (y : ℂ) := by
      simpa using (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x : ℂ)).sub_const p
    have h2 : ((x : ℂ) + (y : ℂ) * I - p) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      rw [hre y]
      linarith
    have h3 := (h1.clog h2).comp_ofReal (z := y)
    simpa [div_eq_mul_inv] using h3
  have hcont : Continuous fun y : ℝ => I * ((x : ℂ) + y * I - p)⁻¹ := by
    apply continuous_const.mul
    apply Continuous.inv₀
    · exact (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const
    · exact hne
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)

/-- FTC on the left vertical edge (`x < Re p`), antiderivative
`y ↦ log (p − (x + y·i))`. -/
lemma integral_vert_inv_left {p : ℂ} {x : ℝ} (hx : x < p.re) (t₁ t₂ : ℝ) :
    (∫ y : ℝ in t₁..t₂, I * ((x : ℂ) + y * I - p)⁻¹) =
      Complex.log (p - ((x : ℂ) + t₂ * I)) - Complex.log (p - ((x : ℂ) + t₁ * I)) := by
  have hre : ∀ y : ℝ, (p - ((x : ℂ) + y * I)).re = p.re - x := by
    intro y
    rw [Complex.sub_re, re_coord]
  have hne : ∀ y : ℝ, (p - ((x : ℂ) + y * I)) ≠ 0 := by
    intro y h
    have := hre y
    rw [h] at this
    simp at this
    linarith
  have hint : ∀ y : ℝ, I * ((x : ℂ) + y * I - p)⁻¹ = -I / (p - ((x : ℂ) + y * I)) := by
    intro y
    have h1 : ((x : ℂ) + y * I - p) = -(p - ((x : ℂ) + y * I)) := by ring
    rw [h1, inv_neg, div_eq_mul_inv]
    ring
  have hderiv : ∀ y ∈ [[t₁, t₂]],
      HasDerivAt (fun y : ℝ => Complex.log (p - ((x : ℂ) + y * I)))
        (-I / (p - ((x : ℂ) + y * I))) y := by
    intro y _
    have h1 : HasDerivAt (fun s : ℂ => p - ((x : ℂ) + s * I)) (-I) (y : ℂ) := by
      simpa using (((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x : ℂ)).const_sub p
    have h2 : (p - ((x : ℂ) + (y : ℂ) * I)) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      rw [hre y]
      linarith
    exact (h1.clog h2).comp_ofReal (z := y)
  have hcont : Continuous fun y : ℝ => -I / (p - ((x : ℂ) + y * I)) := by
    apply continuous_const.div
    · exact continuous_const.sub
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
    · exact hne
  rw [intervalIntegral.integral_congr (g := fun y : ℝ => -I / (p - ((x : ℂ) + y * I)))
    (fun y _ => hint y)]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)

/-- **The winding lemma**: for `p` strictly inside the rectangle,
`∮ (s − p)⁻¹ ds = 2πi`. -/
theorem rectInt_inv_sub_pole {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re)
    (h3 : z.im < p.im) (h4 : p.im < w.im) :
    rectInt (fun s => (s - p)⁻¹) z w = 2 * π * I := by
  unfold rectInt
  rw [show (∫ x : ℝ in z.re..w.re, ((x : ℂ) + z.im * I - p)⁻¹) =
      Complex.log ((w.re : ℂ) + z.im * I - p) - Complex.log ((z.re : ℂ) + z.im * I - p) from
    integral_horiz_inv h3.ne z.re w.re,
    show (∫ x : ℝ in z.re..w.re, ((x : ℂ) + w.im * I - p)⁻¹) =
      Complex.log ((w.re : ℂ) + w.im * I - p) - Complex.log ((z.re : ℂ) + w.im * I - p) from
    integral_horiz_inv h4.ne' z.re w.re]
  rw [smul_eq_mul, smul_eq_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul,
    integral_vert_inv_right h2 z.im w.im, integral_vert_inv_left h1 z.im w.im]
  have e₂ : p - ((z.re : ℂ) + w.im * I) = -((z.re : ℂ) + w.im * I - p) := by ring
  have e₁ : p - ((z.re : ℂ) + z.im * I) = -((z.re : ℂ) + z.im * I - p) := by ring
  rw [e₁, e₂]
  have hA : Complex.log ((z.re : ℂ) + w.im * I - p) -
      Complex.log (-((z.re : ℂ) + w.im * I - p)) = π * I := by
    apply log_sub_log_neg_of_im_pos
    rw [Complex.sub_im, im_coord]
    linarith
  have hB : Complex.log (-((z.re : ℂ) + z.im * I - p)) -
      Complex.log ((z.re : ℂ) + z.im * I - p) = π * I := by
    apply log_neg_sub_log_of_im_neg
    rw [Complex.sub_im, im_coord]
    linarith
  linear_combination hA + hB

end Winding

/-! ### Cauchy integral formula on the rectangle, entire numerator -/

section CauchyFormula

/-- `p` strictly inside the rectangle lies off the frame. -/
lemma notMem_rectFrame {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re)
    (h3 : z.im < p.im) (h4 : p.im < w.im) : p ∉ rectFrame z w := by
  rintro (⟨-, h | h⟩ | ⟨-, h | h⟩)
  · exact absurd h h3.ne'
  · exact absurd h h4.ne
  · exact absurd h h1.ne'
  · exact absurd h h2.ne

/-- **Cauchy integral formula on a rectangle** for an entire numerator:
`∮ f(s)/(s − p) ds = 2πi·f(p)` when `p` is strictly inside. -/
theorem rectInt_cauchy {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z w p : ℂ}
    (h1 : z.re < p.re) (h2 : p.re < w.re) (h3 : z.im < p.im) (h4 : p.im < w.im) :
    rectInt (fun s => f s / (s - p)) z w = 2 * π * I * f p := by
  have hpf : p ∉ rectFrame z w := notMem_rectFrame h1 h2 h3 h4
  have hne : ∀ s ∈ rectFrame z w, s ≠ p := fun s hs h => hpf (h ▸ hs)
  -- decompose the integrand on the frame
  have key : ∀ s ∈ rectFrame z w, f s / (s - p) = f p * (s - p)⁻¹ + dslope f p s := by
    intro s hs
    rw [dslope_of_ne f (hne s hs), slope_def_field]
    have h0 : s - p ≠ 0 := sub_ne_zero.mpr (hne s hs)
    field_simp
    ring
  have cont1 : ContinuousOn (fun s : ℂ => f p * (s - p)⁻¹) (rectFrame z w) := by
    apply continuousOn_const.mul
    apply ContinuousOn.inv₀ ((continuousOn_id.sub continuousOn_const))
    intro s hs
    exact sub_ne_zero.mpr (hne s hs)
  have cont2full : ContinuousOn (dslope f p) Set.univ := by
    rw [continuousOn_dslope Filter.univ_mem]
    exact ⟨hf.continuous.continuousOn, hf.differentiableAt⟩
  have cont2 : ContinuousOn (dslope f p) (rectFrame z w) :=
    cont2full.mono (Set.subset_univ _)
  have hds0 : rectInt (dslope f p) z w = 0 := by
    apply rectInt_eq_zero {p} (Set.countable_singleton p)
    · exact cont2full.mono (Set.subset_univ _)
    · intro x hx
      have hxp : x ≠ p := by
        intro h
        exact hx.2 (h ▸ rfl)
      exact (differentiableAt_dslope_of_ne hxp).mpr (hf.differentiableAt)
  rw [rectInt_congr key, rectInt_add cont1 cont2, hds0, add_zero,
    rectInt_const_mul, rectInt_inv_sub_pole h1 h2 h3 h4]
  ring

end CauchyFormula

/-! ### The truncated Perron kernel -/

section PerronKernel

/-- `∫ u^x dx` for a positive base with `log u ≠ 0`. -/
lemma integral_const_rpow {u : ℝ} (hu : 0 < u) (hne : Real.log u ≠ 0) (a b : ℝ) :
    (∫ x : ℝ in a..b, u ^ x) = (u ^ b - u ^ a) / Real.log u := by
  have hcont : Continuous fun x : ℝ => u ^ x := by
    have h : (fun x : ℝ => u ^ x) = fun x => Real.exp (Real.log u * x) := by
      funext x
      rw [Real.rpow_def_of_pos hu, mul_comm]
    rw [h]
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hderiv : ∀ x ∈ [[a, b]],
      HasDerivAt (fun x : ℝ => u ^ x / Real.log u) (u ^ x) x := by
    intro x _
    have h := (Real.hasStrictDerivAt_const_rpow hu x).hasDerivAt.div_const (Real.log u)
    rwa [mul_div_assoc, div_self hne, mul_one] at h
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  ring

/-- The integrand of the truncated Perron kernel on the vertical line `Re s = c`. -/
noncomputable def perronIntegrand (u c t : ℝ) : ℂ :=
  (u : ℂ) ^ ((c : ℂ) + t * I) / ((c : ℂ) + t * I)

/-- The truncated Perron kernel `(1/2πi)·∫_{c−iT}^{c+iT} u^s/s ds`, as a
real-variable integral. -/
noncomputable def perronKernel (u c T : ℝ) : ℂ :=
  (1 / (2 * π) : ℝ) • ∫ t : ℝ in (-T)..T, perronIntegrand u c t

lemma norm_perronIntegrand {u : ℝ} (hu : 0 < u) (c t : ℝ) :
    ‖perronIntegrand u c t‖ = u ^ c / ‖(c : ℂ) + t * I‖ := by
  rw [perronIntegrand, norm_div, norm_cpow_coord hu]

lemma continuous_perronIntegrand {u c : ℝ} (hu : 0 < u) (hc : c ≠ 0) :
    Continuous fun t : ℝ => perronIntegrand u c t := by
  have hbase : Continuous fun t : ℝ => (c : ℂ) + (t : ℂ) * I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  apply Continuous.div
  · exact hbase.const_cpow (Or.inl (by exact_mod_cast hu.ne'))
  · exact hbase
  · intro t
    exact coord_ne_zero_of_re hc

/-- **Trivial (near-diagonal) bound** for the Perron kernel. -/
theorem norm_perronKernel_le {u c T : ℝ} (hu : 0 < u) (hc : 0 < c) (hcT : c ≤ T) :
    ‖perronKernel u c T‖ ≤ u ^ c * (1 + Real.log (T / c)) / π := by
  have hT : 0 < T := lt_of_lt_of_le hc hcT
  have hgc := continuous_perronIntegrand hu hc.ne'
  have hI1 : IntervalIntegrable (perronIntegrand u c) MeasureTheory.volume (-T) (-c) :=
    hgc.intervalIntegrable _ _
  have hI2 : IntervalIntegrable (perronIntegrand u c) MeasureTheory.volume (-c) c :=
    hgc.intervalIntegrable _ _
  have hI3 : IntervalIntegrable (perronIntegrand u c) MeasureTheory.volume c T :=
    hgc.intervalIntegrable _ _
  have e1 : (∫ t in (-T)..(-c), perronIntegrand u c t) + (∫ t in (-c)..c, perronIntegrand u c t)
      = ∫ t in (-T)..c, perronIntegrand u c t :=
    intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have e2 : (∫ t in (-T)..c, perronIntegrand u c t) + (∫ t in c..T, perronIntegrand u c t)
      = ∫ t in (-T)..T, perronIntegrand u c t :=
    intervalIntegral.integral_add_adjacent_intervals (hI1.trans hI2) hI3
  -- middle piece
  have hmid : ‖∫ t in (-c)..c, perronIntegrand u c t‖ ≤ 2 * u ^ c := by
    have hb : ∀ t ∈ Set.uIoc (-c) c, ‖perronIntegrand u c t‖ ≤ u ^ c / c := by
      intro t _
      rw [norm_perronIntegrand hu]
      have h1 : c ≤ ‖(c : ℂ) + t * I‖ := by
        have := norm_coord_ge_abs_re c t
        rwa [abs_of_pos hc] at this
      gcongr
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    calc ‖∫ t in (-c)..c, perronIntegrand u c t‖ ≤ u ^ c / c * |c - -c| := this
      _ = 2 * u ^ c := by
          rw [sub_neg_eq_add, abs_of_pos (by linarith)]
          field_simp
          ring
  -- right piece
  have hright : ‖∫ t in c..T, perronIntegrand u c t‖ ≤ u ^ c * Real.log (T / c) := by
    have hbnd : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioc c T →
        ‖perronIntegrand u c t‖ ≤ u ^ c * t⁻¹ := by
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      have ht0 : 0 < t := lt_trans hc ht.1
      rw [norm_perronIntegrand hu, div_eq_mul_inv]
      have h2 : t ≤ ‖(c : ℂ) + t * I‖ := by
        have := norm_coord_ge_abs_im c t
        rwa [abs_of_pos ht0] at this
      gcongr
    have hint : IntervalIntegrable (fun t : ℝ => u ^ c * t⁻¹) MeasureTheory.volume c T := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀ continuousOn_id
      intro t ht
      rw [Set.uIcc_of_le hcT] at ht
      exact ne_of_gt (lt_of_lt_of_le hc ht.1)
    calc ‖∫ t in c..T, perronIntegrand u c t‖ ≤ ∫ t in c..T, u ^ c * t⁻¹ :=
          intervalIntegral.norm_integral_le_of_norm_le hcT hbnd hint
      _ = u ^ c * Real.log (T / c) := by
          rw [intervalIntegral.integral_const_mul, integral_inv_of_pos hc hT]
  -- left piece
  have hleft : ‖∫ t in (-T)..(-c), perronIntegrand u c t‖ ≤ u ^ c * Real.log (T / c) := by
    have hbnd : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioc (-T) (-c) →
        ‖perronIntegrand u c t‖ ≤ u ^ c * (-t)⁻¹ := by
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      have ht0 : t < 0 := lt_of_le_of_lt ht.2 (by linarith)
      rw [norm_perronIntegrand hu, div_eq_mul_inv]
      have h2 : -t ≤ ‖(c : ℂ) + t * I‖ := by
        have := norm_coord_ge_abs_im c t
        rwa [abs_of_neg ht0] at this
      gcongr
      linarith
    have hint : IntervalIntegrable (fun t : ℝ => u ^ c * (-t)⁻¹)
        MeasureTheory.volume (-T) (-c) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀ continuous_neg.continuousOn
      intro t ht
      rw [Set.uIcc_of_le (by linarith : -T ≤ -c)] at ht
      have : t ≤ -c := ht.2
      have : 0 < -t := by linarith
      exact ne_of_gt this
    calc ‖∫ t in (-T)..(-c), perronIntegrand u c t‖ ≤ ∫ t in (-T)..(-c), u ^ c * (-t)⁻¹ :=
          intervalIntegral.norm_integral_le_of_norm_le (by linarith) hbnd hint
      _ = u ^ c * Real.log (T / c) := by
          rw [intervalIntegral.integral_const_mul]
          have h3 : (∫ t in (-T)..(-c), (-t)⁻¹) = ∫ t in c..T, t⁻¹ := by
            have := intervalIntegral.integral_comp_neg (a := -T) (b := -c)
              (fun s : ℝ => s⁻¹)
            simpa using this
          rw [h3, integral_inv_of_pos hc hT]
  -- combine
  have hcomb : ‖∫ t in (-T)..T, perronIntegrand u c t‖
      ≤ 2 * u ^ c + 2 * (u ^ c * Real.log (T / c)) := by
    rw [← e2, ← e1]
    calc ‖(∫ t in (-T)..(-c), perronIntegrand u c t) + (∫ t in (-c)..c, perronIntegrand u c t)
          + (∫ t in c..T, perronIntegrand u c t)‖
        ≤ ‖(∫ t in (-T)..(-c), perronIntegrand u c t) +
            (∫ t in (-c)..c, perronIntegrand u c t)‖ +
          ‖∫ t in c..T, perronIntegrand u c t‖ := norm_add_le _ _
      _ ≤ ‖∫ t in (-T)..(-c), perronIntegrand u c t‖ +
          ‖∫ t in (-c)..c, perronIntegrand u c t‖ +
          ‖∫ t in c..T, perronIntegrand u c t‖ := by
            have := norm_add_le (∫ t in (-T)..(-c), perronIntegrand u c t)
              (∫ t in (-c)..c, perronIntegrand u c t)
            linarith
      _ ≤ u ^ c * Real.log (T / c) + 2 * u ^ c + u ^ c * Real.log (T / c) := by
            linarith
      _ = 2 * u ^ c + 2 * (u ^ c * Real.log (T / c)) := by ring
  rw [perronKernel, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hπ : (0 : ℝ) < π := Real.pi_pos
  calc 1 / (2 * π) * ‖∫ t in (-T)..T, perronIntegrand u c t‖
      ≤ 1 / (2 * π) * (2 * u ^ c + 2 * (u ^ c * Real.log (T / c))) := by
        gcongr
    _ = u ^ c * (1 + Real.log (T / c)) / π := by
        field_simp

/-! #### Far-regime bounds via contour shifts -/

/-- Solving the rectangle identity (pole inside) for the right edge. -/
private lemma kernel_solve {B Tp R L : ℂ}
    (hrect : B - Tp + I • R - I • L = 2 * π * I) :
    R = 2 * π + I * B - I * Tp + L := by
  rw [smul_eq_mul, smul_eq_mul] at hrect
  linear_combination (-I) * hrect + (R - L - 2 * (π : ℂ)) * Complex.I_mul_I

/-- Solving the rectangle identity (no pole) for the left edge. -/
private lemma kernel_solve' {B Tp R L : ℂ}
    (hrect : B - Tp + I • R - I • L = 0) :
    L = -I * B + I * Tp + R := by
  rw [smul_eq_mul, smul_eq_mul] at hrect
  linear_combination I * hrect + (L - R) * Complex.I_mul_I

/-- Horizontal edge bound: `‖∫_a^b u^{x+it}/(x+it) dx‖ ≤ (u^a + u^b)/(|t|·|log u|)`. -/
private lemma norm_horiz_edge_le {u : ℝ} (hu0 : 0 < u) (hu1 : Real.log u ≠ 0)
    {a b t : ℝ} (hab : a ≤ b) (ht : t ≠ 0) :
    ‖∫ x : ℝ in a..b, (u : ℂ) ^ ((x : ℂ) + t * I) / ((x : ℂ) + t * I)‖
      ≤ (u ^ a + u ^ b) / (|t| * |Real.log u|) := by
  have ht0 : (0 : ℝ) < |t| := abs_pos.mpr ht
  have hbnd : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.Ioc a b →
      ‖(u : ℂ) ^ ((x : ℂ) + t * I) / ((x : ℂ) + t * I)‖ ≤ u ^ x * |t|⁻¹ := by
    refine Filter.Eventually.of_forall (fun x _ => ?_)
    rw [norm_div, norm_cpow_coord hu0, div_eq_mul_inv]
    have h2 : |t| ≤ ‖(x : ℂ) + t * I‖ := norm_coord_ge_abs_im x t
    gcongr
  have hcont : Continuous fun x : ℝ => u ^ x := by
    have h : (fun x : ℝ => u ^ x) = fun x => Real.exp (Real.log u * x) := by
      funext x
      rw [Real.rpow_def_of_pos hu0, mul_comm]
    rw [h]
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hint : IntervalIntegrable (fun x : ℝ => u ^ x * |t|⁻¹) MeasureTheory.volume a b :=
    (hcont.mul continuous_const).intervalIntegrable _ _
  calc ‖∫ x : ℝ in a..b, (u : ℂ) ^ ((x : ℂ) + t * I) / ((x : ℂ) + t * I)‖
      ≤ ∫ x : ℝ in a..b, u ^ x * |t|⁻¹ :=
        intervalIntegral.norm_integral_le_of_norm_le hab hbnd hint
    _ = (u ^ b - u ^ a) / Real.log u * |t|⁻¹ := by
        rw [intervalIntegral.integral_mul_const, integral_const_rpow hu0 hu1]
    _ ≤ (u ^ a + u ^ b) / (|t| * |Real.log u|) := by
        have hpa : (0 : ℝ) < u ^ a := Real.rpow_pos_of_pos hu0 a
        have hpb : (0 : ℝ) < u ^ b := Real.rpow_pos_of_pos hu0 b
        have key : (u ^ b - u ^ a) / Real.log u ≤ (u ^ a + u ^ b) / |Real.log u| := by
          rcases lt_or_gt_of_ne hu1 with h | h
          · rw [abs_of_neg h]
            have e : (u ^ b - u ^ a) / Real.log u = (u ^ a - u ^ b) / (-Real.log u) := by
              rw [← neg_div_neg_eq]
              ring_nf
            rw [e]
            gcongr <;> linarith
          · rw [abs_of_pos h]
            gcongr
            linarith
        calc (u ^ b - u ^ a) / Real.log u * |t|⁻¹
            ≤ (u ^ a + u ^ b) / |Real.log u| * |t|⁻¹ := by
              apply mul_le_mul_of_nonneg_right key (by positivity)
          _ = (u ^ a + u ^ b) / (|t| * |Real.log u|) := by
              have hL0 : |Real.log u| ≠ 0 := abs_ne_zero.mpr hu1
              field_simp

/-- Vertical edge bound: `‖∫ u^{x+iy}/(x+iy) dy‖ ≤ u^x/|x|·|t₂ − t₁|`. -/
private lemma norm_vert_edge_le {u : ℝ} (hu0 : 0 < u) {x t₁ t₂ : ℝ} (hx : x ≠ 0) :
    ‖∫ y : ℝ in t₁..t₂, (u : ℂ) ^ ((x : ℂ) + y * I) / ((x : ℂ) + y * I)‖
      ≤ u ^ x / |x| * |t₂ - t₁| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro y _
  rw [norm_div, norm_cpow_coord hu0]
  have h2 : |x| ≤ ‖(x : ℂ) + y * I‖ := norm_coord_ge_abs_re x y
  gcongr

/-- The rectangle identity with the pole `0` inside: the kernel line
(right edge, at `Re s = b > 0`) in terms of the far edges. -/
private lemma perron_far_identity {u : ℝ} (hu0 : 0 < u) {a b t₁ t₂ : ℝ}
    (ha : a < 0) (hb : 0 < b) (ht₁ : t₁ < 0) (ht₂ : 0 < t₂) :
    (∫ y : ℝ in t₁..t₂, (u : ℂ) ^ ((b : ℂ) + y * I) / ((b : ℂ) + y * I)) =
      2 * π + I * (∫ x : ℝ in a..b, (u : ℂ) ^ ((x : ℂ) + t₁ * I) / ((x : ℂ) + t₁ * I))
        - I * (∫ x : ℝ in a..b, (u : ℂ) ^ ((x : ℂ) + t₂ * I) / ((x : ℂ) + t₂ * I))
        + (∫ y : ℝ in t₁..t₂, (u : ℂ) ^ ((a : ℂ) + y * I) / ((a : ℂ) + y * I)) := by
  have hune : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
  have hfd : Differentiable ℂ fun s : ℂ => (u : ℂ) ^ s := fun s =>
    differentiableAt_id.const_cpow (Or.inl hune)
  have h1 : ((a : ℂ) + (t₁ : ℂ) * I).re < (0 : ℂ).re := by
    rw [re_coord, Complex.zero_re]; linarith
  have h2 : (0 : ℂ).re < ((b : ℂ) + (t₂ : ℂ) * I).re := by
    rw [re_coord, Complex.zero_re]; linarith
  have h3 : ((a : ℂ) + (t₁ : ℂ) * I).im < (0 : ℂ).im := by
    rw [im_coord, Complex.zero_im]; linarith
  have h4 : (0 : ℂ).im < ((b : ℂ) + (t₂ : ℂ) * I).im := by
    rw [im_coord, Complex.zero_im]; linarith
  have hrect := rectInt_cauchy hfd h1 h2 h3 h4
  simp only [sub_zero, Complex.cpow_zero, mul_one] at hrect
  unfold rectInt at hrect
  simp only [re_coord, im_coord] at hrect
  exact kernel_solve hrect

/-- The pole-free rectangle identity in the right half-plane: the kernel line
(left edge, at `Re s = a > 0`) in terms of the far edges. -/
private lemma perron_far_identity' {u : ℝ} (hu0 : 0 < u) {a b t₁ t₂ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ y : ℝ in t₁..t₂, (u : ℂ) ^ ((a : ℂ) + y * I) / ((a : ℂ) + y * I)) =
      -I * (∫ x : ℝ in a..b, (u : ℂ) ^ ((x : ℂ) + t₁ * I) / ((x : ℂ) + t₁ * I))
        + I * (∫ x : ℝ in a..b, (u : ℂ) ^ ((x : ℂ) + t₂ * I) / ((x : ℂ) + t₂ * I))
        + (∫ y : ℝ in t₁..t₂, (u : ℂ) ^ ((b : ℂ) + y * I) / ((b : ℂ) + y * I)) := by
  have hune : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
  have hre : ∀ s : ℂ, s ∈ [[((a : ℂ) + (t₁ : ℂ) * I).re, ((b : ℂ) + (t₂ : ℂ) * I).re]] ×ℂ
      [[((a : ℂ) + (t₁ : ℂ) * I).im, ((b : ℂ) + (t₂ : ℂ) * I).im]] → s ≠ 0 := by
    intro s hs h0
    rw [Complex.mem_reProdIm, re_coord, re_coord, Set.uIcc_of_le hab] at hs
    have : a ≤ s.re := hs.1.1
    rw [h0, Complex.zero_re] at this
    linarith
  have hrect : rectInt (fun s => (u : ℂ) ^ s / s)
      ((a : ℂ) + (t₁ : ℂ) * I) ((b : ℂ) + (t₂ : ℂ) * I) = 0 := by
    apply rectInt_eq_zero ∅ Set.countable_empty
    · apply ContinuousOn.div
      · exact (continuous_id.const_cpow (Or.inl hune)).continuousOn
      · exact continuousOn_id
      · exact fun s hs => hre s hs
    · intro s hs
      have hs' : s ∈ [[((a : ℂ) + (t₁ : ℂ) * I).re, ((b : ℂ) + (t₂ : ℂ) * I).re]] ×ℂ
          [[((a : ℂ) + (t₁ : ℂ) * I).im, ((b : ℂ) + (t₂ : ℂ) * I).im]] := by
        rw [Complex.mem_reProdIm]
        obtain ⟨h1, h2⟩ := (Complex.mem_reProdIm).mp hs.1
        constructor
        · rw [← Set.Icc_min_max]
          exact Set.Ioo_subset_Icc_self h1
        · rw [← Set.Icc_min_max]
          exact Set.Ioo_subset_Icc_self h2
      exact (differentiableAt_id.const_cpow (Or.inl hune)).div differentiableAt_id
        (hre s hs')
  unfold rectInt at hrect
  simp only [re_coord, im_coord] at hrect
  exact kernel_solve' hrect

/-- **Far-regime bound, `u > 1`** (contour shifted left past the pole). -/
theorem norm_perronKernel_sub_one_le {u c T : ℝ} (hu : 1 < u) (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel u c T - 1‖ ≤ u ^ c / (T * Real.log u) := by
  have hu0 : (0 : ℝ) < u := lt_trans one_pos hu
  have hlogu : 0 < Real.log u := Real.log_pos hu
  have hπ : (0 : ℝ) < π := Real.pi_pos
  -- the far abscissa
  set A : ℝ := max 1 (Real.log (T ^ 2 * Real.log u + 1) / Real.log u) with hAdef
  have hA1 : 1 ≤ A := le_max_left _ _
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA1
  have hApow : T ^ 2 * Real.log u ≤ u ^ A := by
    have h1 : Real.log (T ^ 2 * Real.log u + 1) / Real.log u ≤ A := le_max_right _ _
    have h2 : Real.log (T ^ 2 * Real.log u + 1) ≤ A * Real.log u := by
      rw [div_le_iff₀ hlogu] at h1
      linarith
    have h3 : (0 : ℝ) < T ^ 2 * Real.log u + 1 := by positivity
    calc T ^ 2 * Real.log u ≤ T ^ 2 * Real.log u + 1 := by linarith
      _ = Real.exp (Real.log (T ^ 2 * Real.log u + 1)) := (Real.exp_log h3).symm
      _ ≤ Real.exp (A * Real.log u) := Real.exp_le_exp.mpr h2
      _ = u ^ A := by rw [Real.rpow_def_of_pos hu0, mul_comm]
  have hid := perron_far_identity hu0 (a := -A) (b := c) (t₁ := -T) (t₂ := T)
    (by linarith) hc (by linarith) hT
  -- edge bounds
  have hucpos : (0 : ℝ) < u ^ c := Real.rpow_pos_of_pos hu0 c
  have huc1 : (1 : ℝ) ≤ u ^ c := by
    have := Real.rpow_le_rpow_of_exponent_le hu.le hc.le
    rwa [Real.rpow_zero] at this
  have huA1 : u ^ (-A : ℝ) ≤ 1 := by
    have := Real.rpow_le_rpow_of_exponent_le hu.le (by linarith : (-A : ℝ) ≤ 0)
    rwa [Real.rpow_zero] at this
  have hBbnd : ∀ t : ℝ, t ≠ 0 → |t| = T →
      ‖∫ x : ℝ in (-A)..c, (u : ℂ) ^ ((x : ℂ) + t * I) / ((x : ℂ) + t * I)‖
        ≤ 2 * u ^ c / (T * Real.log u) := by
    intro t ht habs
    calc ‖∫ x : ℝ in (-A)..c, (u : ℂ) ^ ((x : ℂ) + t * I) / ((x : ℂ) + t * I)‖
        ≤ (u ^ (-A : ℝ) + u ^ c) / (|t| * |Real.log u|) :=
          norm_horiz_edge_le hu0 hlogu.ne' (by linarith) ht
      _ ≤ 2 * u ^ c / (T * Real.log u) := by
          rw [habs, abs_of_pos hlogu]
          gcongr
          linarith
  have hLbnd : ‖∫ y : ℝ in (-T)..T, (u : ℂ) ^ (((-A : ℝ) : ℂ) + y * I) /
      (((-A : ℝ) : ℂ) + y * I)‖ ≤ 2 * u ^ c / (T * Real.log u) := by
    calc ‖∫ y : ℝ in (-T)..T, (u : ℂ) ^ (((-A : ℝ) : ℂ) + y * I) / (((-A : ℝ) : ℂ) + y * I)‖
        ≤ u ^ (-A : ℝ) / |(-A : ℝ)| * |T - -T| := norm_vert_edge_le hu0 (by linarith)
      _ ≤ u ^ (-A : ℝ) * (2 * T) := by
          rw [abs_of_neg (by linarith : (-A : ℝ) < 0), neg_neg,
            abs_of_pos (by linarith : (0:ℝ) < T - -T)]
          have h5 : u ^ (-A : ℝ) / A ≤ u ^ (-A : ℝ) := by
            apply div_le_self (Real.rpow_pos_of_pos hu0 _).le hA1
          nlinarith [Real.rpow_pos_of_pos hu0 (-A : ℝ)]
      _ ≤ 2 * u ^ c / (T * Real.log u) := by
          have h6 : u ^ (-A : ℝ) = (u ^ A)⁻¹ := Real.rpow_neg hu0.le A
          have h7 : (u ^ A)⁻¹ ≤ (T ^ 2 * Real.log u)⁻¹ := by
            rw [inv_eq_one_div, inv_eq_one_div]
            exact one_div_le_one_div_of_le (by positivity) hApow
          have h8 : u ^ (-A : ℝ) * (2 * T) ≤ (T ^ 2 * Real.log u)⁻¹ * (2 * T) := by
            rw [h6]
            gcongr
          calc u ^ (-A : ℝ) * (2 * T) ≤ (T ^ 2 * Real.log u)⁻¹ * (2 * T) := h8
            _ = 2 / (T * Real.log u) := by
                field_simp
            _ ≤ 2 * u ^ c / (T * Real.log u) := by
                gcongr
                linarith
  -- assemble
  have hkernel : perronKernel u c T - 1 = (1 / (2 * π) : ℝ) •
      (I * (∫ x : ℝ in (-A)..c, (u : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) /
          ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
        - I * (∫ x : ℝ in (-A)..c, (u : ℂ) ^ ((x : ℂ) + (T : ℂ) * I) /
          ((x : ℂ) + (T : ℂ) * I))
        + (∫ y : ℝ in (-T)..T, (u : ℂ) ^ (((-A : ℝ) : ℂ) + y * I) /
          (((-A : ℝ) : ℂ) + y * I))) := by
    rw [perronKernel]
    have hint : (∫ t : ℝ in (-T)..T, perronIntegrand u c t) =
        ∫ y : ℝ in (-T)..T, (u : ℂ) ^ ((c : ℂ) + y * I) / ((c : ℂ) + y * I) := rfl
    rw [hint, hid, Complex.real_smul, Complex.real_smul]
    have hπc : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hπ.ne'
    push_cast
    field_simp
    ring
  rw [hkernel, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have htri : ‖(I * (∫ x : ℝ in (-A)..c, (u : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) /
          ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
        - I * (∫ x : ℝ in (-A)..c, (u : ℂ) ^ ((x : ℂ) + (T : ℂ) * I) /
          ((x : ℂ) + (T : ℂ) * I))
        + (∫ y : ℝ in (-T)..T, (u : ℂ) ^ (((-A : ℝ) : ℂ) + y * I) /
          (((-A : ℝ) : ℂ) + y * I)))‖
      ≤ 6 * u ^ c / (T * Real.log u) := by
    have e1 := hBbnd (-T) (by linarith) (by rw [abs_of_neg (by linarith : (-T:ℝ) < 0)]; ring)
    have e2 := hBbnd T hT.ne' (abs_of_pos hT)
    calc _ ≤ ‖I * (∫ x : ℝ in (-A)..c, (u : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) /
            ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
          - I * (∫ x : ℝ in (-A)..c, (u : ℂ) ^ ((x : ℂ) + (T : ℂ) * I) /
            ((x : ℂ) + (T : ℂ) * I))‖
        + ‖∫ y : ℝ in (-T)..T, (u : ℂ) ^ (((-A : ℝ) : ℂ) + y * I) /
            (((-A : ℝ) : ℂ) + y * I)‖ := norm_add_le _ _
      _ ≤ ‖I * (∫ x : ℝ in (-A)..c, (u : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) /
            ((x : ℂ) + ((-T : ℝ) : ℂ) * I))‖
          + ‖I * (∫ x : ℝ in (-A)..c, (u : ℂ) ^ ((x : ℂ) + (T : ℂ) * I) /
            ((x : ℂ) + (T : ℂ) * I))‖
          + ‖∫ y : ℝ in (-T)..T, (u : ℂ) ^ (((-A : ℝ) : ℂ) + y * I) /
            (((-A : ℝ) : ℂ) + y * I)‖ := by
              have := norm_sub_le
                (I * (∫ x : ℝ in (-A)..c, (u : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) /
                  ((x : ℂ) + ((-T : ℝ) : ℂ) * I)))
                (I * (∫ x : ℝ in (-A)..c, (u : ℂ) ^ ((x : ℂ) + (T : ℂ) * I) /
                  ((x : ℂ) + (T : ℂ) * I)))
              linarith
      _ ≤ 2 * u ^ c / (T * Real.log u) + 2 * u ^ c / (T * Real.log u)
          + 2 * u ^ c / (T * Real.log u) := by
            rw [norm_mul, norm_mul, Complex.norm_I, one_mul, one_mul]
            exact add_le_add (add_le_add e1 e2) hLbnd
      _ = 6 * u ^ c / (T * Real.log u) := by ring
  calc 1 / (2 * π) * ‖_‖ ≤ 1 / (2 * π) * (6 * u ^ c / (T * Real.log u)) := by gcongr
    _ ≤ u ^ c / (T * Real.log u) := by
        have h9 : (0:ℝ) < u ^ c / (T * Real.log u) := by positivity
        have hπ3 : (3:ℝ) < π := Real.pi_gt_three
        have e : 1 / (2 * π) * (6 * u ^ c / (T * Real.log u))
            = 3 / π * (u ^ c / (T * Real.log u)) := by
          field_simp
          ring
        rw [e, div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos]
        nlinarith [mul_pos h9 (by linarith : (0:ℝ) < π - 3)]

/-- **Far-regime bound, `u < 1`** (pole-free contour shifted right). -/
theorem norm_perronKernel_le_of_lt_one {u c T : ℝ} (hu0 : 0 < u) (hu : u < 1)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel u c T‖ ≤ u ^ c / (T * |Real.log u|) := by
  have hlogneg : Real.log u < 0 := Real.log_neg hu0 hu
  have hlogu : (0 : ℝ) < -Real.log u := by linarith
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have habsL : |Real.log u| = -Real.log u := abs_of_neg hlogneg
  set L : ℝ := -Real.log u with hLdef
  set A : ℝ := max (c + 1) (c + Real.log (T ^ 2 * L + 1) / L) with hAdef
  have hAc : c + 1 ≤ A := le_max_left _ _
  have hA1 : c ≤ A := by linarith
  have hA0 : (1 : ℝ) ≤ A := by linarith
  have hApos : (0 : ℝ) < A := by linarith
  have hucpos : (0 : ℝ) < u ^ c := Real.rpow_pos_of_pos hu0 c
  have hApow : u ^ A ≤ u ^ c / (T ^ 2 * L) := by
    have h1 : c + Real.log (T ^ 2 * L + 1) / L ≤ A := le_max_right _ _
    have h1' : Real.log (T ^ 2 * L + 1) / L ≤ A - c := by linarith
    rw [div_le_iff₀ hlogu] at h1'
    have h3 : (0 : ℝ) < T ^ 2 * L + 1 := by positivity
    have hstep : u ^ (A - c) = Real.exp ((A - c) * Real.log u) := by
      rw [Real.rpow_def_of_pos hu0, mul_comm]
    have h4 : u ^ A = u ^ c * Real.exp (-((A - c) * L)) := by
      calc u ^ A = u ^ (c + (A - c)) := by ring_nf
        _ = u ^ c * u ^ (A - c) := Real.rpow_add hu0 _ _
        _ = u ^ c * Real.exp ((A - c) * Real.log u) := by rw [hstep]
        _ = u ^ c * Real.exp (-((A - c) * L)) := by
            rw [hLdef]
            ring_nf
    have h6 : T ^ 2 * L + 1 ≤ Real.exp ((A - c) * L) := by
      calc T ^ 2 * L + 1 = Real.exp (Real.log (T ^ 2 * L + 1)) := (Real.exp_log h3).symm
        _ ≤ Real.exp ((A - c) * L) := Real.exp_le_exp.mpr h1'
    have h5 : Real.exp (-((A - c) * L)) ≤ (T ^ 2 * L + 1)⁻¹ := by
      rw [Real.exp_neg, inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le h3 h6
    calc u ^ A = u ^ c * Real.exp (-((A - c) * L)) := h4
      _ ≤ u ^ c * (T ^ 2 * L + 1)⁻¹ := mul_le_mul_of_nonneg_left h5 hucpos.le
      _ ≤ u ^ c / (T ^ 2 * L) := by
          rw [div_eq_mul_inv]
          have h7 : (T ^ 2 * L + 1)⁻¹ ≤ (T ^ 2 * L)⁻¹ := by
            rw [inv_eq_one_div, inv_eq_one_div]
            exact one_div_le_one_div_of_le (by positivity) (by linarith)
          exact mul_le_mul_of_nonneg_left h7 hucpos.le
  have huA : u ^ A ≤ u ^ c := Real.rpow_le_rpow_of_exponent_ge hu0 hu.le hA1
  have hid := perron_far_identity' (u := u) (a := c) (b := A) (t₁ := -T) (t₂ := T)
    hu0 hc hA1
  -- edge bounds
  have hBbnd : ∀ t : ℝ, t ≠ 0 → |t| = T →
      ‖∫ x : ℝ in c..A, (u : ℂ) ^ ((x : ℂ) + t * I) / ((x : ℂ) + t * I)‖
        ≤ 2 * u ^ c / (T * L) := by
    intro t ht habs
    calc ‖∫ x : ℝ in c..A, (u : ℂ) ^ ((x : ℂ) + t * I) / ((x : ℂ) + t * I)‖
        ≤ (u ^ c + u ^ A) / (|t| * |Real.log u|) :=
          norm_horiz_edge_le hu0 hlogneg.ne hA1 ht
      _ ≤ 2 * u ^ c / (T * L) := by
          rw [habs, habsL]
          gcongr
          linarith
  have hRbnd : ‖∫ y : ℝ in (-T)..T, (u : ℂ) ^ ((A : ℂ) + y * I) / ((A : ℂ) + y * I)‖
      ≤ 2 * u ^ c / (T * L) := by
    calc ‖∫ y : ℝ in (-T)..T, (u : ℂ) ^ ((A : ℂ) + y * I) / ((A : ℂ) + y * I)‖
        ≤ u ^ A / |A| * |T - -T| := norm_vert_edge_le hu0 hApos.ne'
      _ ≤ u ^ A * (2 * T) := by
          rw [abs_of_pos hApos, abs_of_pos (by linarith : (0:ℝ) < T - -T)]
          have h5 : u ^ A / A ≤ u ^ A :=
            div_le_self (Real.rpow_pos_of_pos hu0 _).le hA0
          nlinarith [Real.rpow_pos_of_pos hu0 A]
      _ ≤ 2 * u ^ c / (T * L) := by
          calc u ^ A * (2 * T) ≤ u ^ c / (T ^ 2 * L) * (2 * T) := by
                have := hApow
                nlinarith [hT]
            _ = 2 * u ^ c / (T * L) := by
                field_simp
  -- assemble
  have hkernel : perronKernel u c T = (1 / (2 * π) : ℝ) •
      (-I * (∫ x : ℝ in c..A, (u : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) /
          ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
        + I * (∫ x : ℝ in c..A, (u : ℂ) ^ ((x : ℂ) + (T : ℂ) * I) /
          ((x : ℂ) + (T : ℂ) * I))
        + (∫ y : ℝ in (-T)..T, (u : ℂ) ^ ((A : ℂ) + y * I) / ((A : ℂ) + y * I))) := by
    rw [perronKernel]
    have hint : (∫ t : ℝ in (-T)..T, perronIntegrand u c t) =
        ∫ y : ℝ in (-T)..T, (u : ℂ) ^ ((c : ℂ) + y * I) / ((c : ℂ) + y * I) := rfl
    rw [hint, hid]
  rw [hkernel, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have htri : ‖(-I * (∫ x : ℝ in c..A, (u : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) /
          ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
        + I * (∫ x : ℝ in c..A, (u : ℂ) ^ ((x : ℂ) + (T : ℂ) * I) /
          ((x : ℂ) + (T : ℂ) * I))
        + (∫ y : ℝ in (-T)..T, (u : ℂ) ^ ((A : ℂ) + y * I) / ((A : ℂ) + y * I)))‖
      ≤ 6 * u ^ c / (T * L) := by
    have e1 := hBbnd (-T) (by linarith) (by rw [abs_of_neg (by linarith : (-T:ℝ) < 0)]; ring)
    have e2 := hBbnd T hT.ne' (abs_of_pos hT)
    calc _ ≤ ‖-I * (∫ x : ℝ in c..A, (u : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) /
            ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
          + I * (∫ x : ℝ in c..A, (u : ℂ) ^ ((x : ℂ) + (T : ℂ) * I) /
            ((x : ℂ) + (T : ℂ) * I))‖
        + ‖∫ y : ℝ in (-T)..T, (u : ℂ) ^ ((A : ℂ) + y * I) / ((A : ℂ) + y * I)‖ :=
          norm_add_le _ _
      _ ≤ ‖-I * (∫ x : ℝ in c..A, (u : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) /
            ((x : ℂ) + ((-T : ℝ) : ℂ) * I))‖
          + ‖I * (∫ x : ℝ in c..A, (u : ℂ) ^ ((x : ℂ) + (T : ℂ) * I) /
            ((x : ℂ) + (T : ℂ) * I))‖
          + ‖∫ y : ℝ in (-T)..T, (u : ℂ) ^ ((A : ℂ) + y * I) / ((A : ℂ) + y * I)‖ := by
            have := norm_add_le
              (-I * (∫ x : ℝ in c..A, (u : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) /
                ((x : ℂ) + ((-T : ℝ) : ℂ) * I)))
              (I * (∫ x : ℝ in c..A, (u : ℂ) ^ ((x : ℂ) + (T : ℂ) * I) /
                ((x : ℂ) + (T : ℂ) * I)))
            linarith
      _ ≤ 2 * u ^ c / (T * L) + 2 * u ^ c / (T * L) + 2 * u ^ c / (T * L) := by
            rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, one_mul, one_mul]
            exact add_le_add (add_le_add e1 e2) hRbnd
      _ = 6 * u ^ c / (T * L) := by ring
  rw [habsL]
  calc 1 / (2 * π) * ‖_‖ ≤ 1 / (2 * π) * (6 * u ^ c / (T * L)) := by gcongr
    _ ≤ u ^ c / (T * L) := by
        have h9 : (0:ℝ) < u ^ c / (T * L) := by positivity
        have hπ3 : (3:ℝ) < π := Real.pi_gt_three
        have e : 1 / (2 * π) * (6 * u ^ c / (T * L)) = 3 / π * (u ^ c / (T * L)) := by
          field_simp
          ring
        rw [e, div_mul_eq_mul_div, div_le_iff₀ Real.pi_pos]
        nlinarith [mul_pos h9 (by linarith : (0:ℝ) < π - 3)]

/-- **The combined far-regime kernel bound**:
`‖K(u) − 1_{u>1}‖ ≤ u^c/(T·|log u|)` for `u ≠ 1`. -/
theorem norm_perronKernel_sub_indicator_le {u c T : ℝ} (hu0 : 0 < u) (hu1 : u ≠ 1)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel u c T - (if 1 < u then 1 else 0)‖ ≤ u ^ c / (T * |Real.log u|) := by
  rcases lt_or_gt_of_ne hu1 with h | h
  · rw [if_neg (by linarith), sub_zero]
    exact norm_perronKernel_le_of_lt_one hu0 h hc hT
  · rw [if_pos h, abs_of_pos (Real.log_pos h)]
    exact norm_perronKernel_sub_one_le h hc hT

/-- Bridge to the contour form: `2πi·K(u) = i·∫_{−T}^{T} u^{c+it}/(c+it) dt`,
i.e. `2πi·K(u)` is the right-edge integral of `u^s/s`. -/
lemma two_pi_I_mul_perronKernel (u c T : ℝ) :
    2 * π * I * perronKernel u c T =
      I * ∫ t : ℝ in (-T)..T, perronIntegrand u c t := by
  rw [perronKernel, Complex.real_smul]
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

end PerronKernel

end Carmichael
