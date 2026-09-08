/-
Route Z, sortie Z6a: the single-modulus character-twisted mean value theorem
for Dirichlet polynomials, log-free.

Main results (all with coefficients `a : ℕ → ℂ` supported on `[1, N]` via
summation over `Finset.Icc 1 N`, modulus `d ≥ 1`, and `T ≥ 2`):

* `mean_value_chars`:
    ∑_{χ mod d} ∫_{−T}^{T} ‖∑_{n≤N} aₙ χ(n) e^{−it log n}‖² dt
      ≤ 100 (N + dT) ∑_{n≤N} ‖aₙ‖².
* `mean_value_chars_cpow`: the same bound with `n ^ (−it)` (complex `cpow`).
* `mean_value_chars_discrete`: for any finite set of points `t_r ∈ [−T, T]`
  that are 1-separated,
    ∑_{χ mod d} ∑_r ‖∑_{n≤N} aₙ χ(n) n^{−i t_r}‖²
      ≤ 200 (N + d(T+1)) ∑_{n≤N} (1 + log² n) ‖aₙ‖².

Route: Fejér-kernel majorant (the integral-kernel form of Gallagher's lemma).
The indicator of `[−T, T]` is majorized by `(16T/3) · K_β` with
`K_β = 𝓕(triangle of half-width β)`, `β = 1/(4T)`; then `K_β ≥ 0` and, by
Fourier inversion (`MeasureTheory.Integrable.fourierInv_fourier_eq`),
`∫ K_β(t) e^{iθt} dt = tri_β(θ/2π)`, which vanishes for `|θ| ≥ π/(2T)` and
lies in `[0, 1]`. After opening the square and applying character
orthogonality (`DirichletCharacter.sum_char_inv_mul_char_eq`), the surviving
pairs satisfy `m ≡ n (mod d)` and `|log(m/n)| < π/(2T)`, and are counted
directly (`≤ 4N/(dT) + 1` per `m`, via `|log(m/n)| ≥ |m−n|/max(m,n)`).
This yields the clean `N + dT` bound with no log factor; Gallagher's L²
lemma as such is not needed and is not proved separately — the kernel
identity `integral_fejer_mul_exp` plays its role.

The discrete-point corollary uses the Sobolev step
`‖S(t_r)‖² ≤ ∫_{|u−t_r|≤1/2} (2‖S(u)‖² + ‖S′(u)‖²) du` over disjoint unit
windows; the derivative polynomial pays the `(1 + log² n)` weight.
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

namespace Carmichael
namespace MeanValue

open Complex MeasureTheory Finset intervalIntegral Filter
open scoped Real ComplexConjugate FourierTransform Classical

/-! ### The triangle bump and the Fejér-type kernel -/

/-- Triangle bump of half-width `β`, height 1. -/
noncomputable def tri (β x : ℝ) : ℝ := max 0 (1 - |x| / β)

/-- The Fejér-type kernel: the Fourier transform of `tri β`
(`fourier_triC` below). -/
noncomputable def fejer (β : ℝ) : ℝ → ℝ := fun t =>
  if t = 0 then β else Real.sin (π * β * t) ^ 2 / (π ^ 2 * β * t ^ 2)

lemma tri_nonneg (β x : ℝ) : 0 ≤ tri β x := le_max_left _ _

lemma tri_le_one {β : ℝ} (hβ : 0 < β) (x : ℝ) : tri β x ≤ 1 := by
  have h : 0 ≤ |x| / β := div_nonneg (abs_nonneg x) hβ.le
  exact max_le zero_le_one (by linarith)

lemma tri_eq_zero {β x : ℝ} (hβ : 0 < β) (h : β ≤ |x|) : tri β x = 0 := by
  have h1 : (1 : ℝ) ≤ |x| / β := (one_le_div hβ).2 h
  exact max_eq_left (by linarith)

lemma tri_neg (β x : ℝ) : tri β (-x) = tri β x := by simp [tri]

lemma continuous_tri (β : ℝ) : Continuous (tri β) :=
  continuous_const.max (continuous_const.sub (continuous_abs.div_const β))

lemma hasCompactSupport_triC {β : ℝ} (hβ : 0 < β) :
    HasCompactSupport fun x => ((tri β x : ℝ) : ℂ) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -β) (b := β)) fun x hx => ?_
  rcases le_or_gt β |x| with h | h
  · rw [tri_eq_zero hβ h, Complex.ofReal_zero]
  · exact absurd (Set.mem_Icc.2 ⟨(abs_lt.1 h).1.le, (abs_lt.1 h).2.le⟩) hx

lemma integrable_triC {β : ℝ} (hβ : 0 < β) : Integrable fun x => ((tri β x : ℝ) : ℂ) :=
  (Complex.continuous_ofReal.comp (continuous_tri β)).integrable_of_hasCompactSupport
    (hasCompactSupport_triC hβ)

lemma fejer_nonneg {β : ℝ} (hβ : 0 < β) (t : ℝ) : 0 ≤ fejer β t := by
  unfold fejer
  split_ifs with h
  · exact hβ.le
  · exact div_nonneg (sq_nonneg _) (by positivity)

lemma fejer_le {β : ℝ} (hβ : 0 < β) (t : ℝ) : fejer β t ≤ β := by
  unfold fejer
  split_ifs with h
  · exact le_rfl
  · have ht2 : (0 : ℝ) < t ^ 2 := pow_two_pos_of_ne_zero h
    have hden : (0 : ℝ) < π ^ 2 * β * t ^ 2 :=
      mul_pos (mul_pos (by positivity) hβ) ht2
    have h1 : Real.sin (π * β * t) ^ 2 ≤ (π * β * t) ^ 2 := by
      rw [← sq_abs (Real.sin (π * β * t)), ← sq_abs (π * β * t)]
      exact pow_le_pow_left₀ (abs_nonneg _) Real.abs_sin_le_abs 2
    calc Real.sin (π * β * t) ^ 2 / (π ^ 2 * β * t ^ 2)
        ≤ (π * β * t) ^ 2 / (π ^ 2 * β * t ^ 2) := by gcongr
      _ = β := by field_simp

lemma fejer_measurable (β : ℝ) : Measurable (fejer β) := by
  unfold fejer
  refine Measurable.ite ?_ measurable_const ?_
  · simp only [Set.ofPred_eq_eq_singleton]
    exact measurableSet_singleton (0 : ℝ)
  · fun_prop

lemma fejer_integrable {β : ℝ} (hβ : 0 < β) : Integrable (fejer β) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (β + 1 / (π ^ 2 * β)))
    (fejer_measurable β).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (fejer_nonneg hβ t)]
  have h1t : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have key : fejer β t * (1 + t ^ 2) ≤ β + 1 / (π ^ 2 * β) := by
    rcases eq_or_ne t 0 with rfl | ht
    · have h0 : (0 : ℝ) < 1 / (π ^ 2 * β) := by positivity
      have hf0 : fejer β 0 = β := if_pos rfl
      rw [hf0]
      nlinarith
    · have h2 : fejer β t ≤ β := fejer_le hβ t
      have h3 : fejer β t * t ^ 2 ≤ 1 / (π ^ 2 * β) := by
        unfold fejer
        rw [if_neg ht]
        have ht2 : (0 : ℝ) < t ^ 2 := pow_two_pos_of_ne_zero ht
        have heq : Real.sin (π * β * t) ^ 2 / (π ^ 2 * β * t ^ 2) * t ^ 2
            = Real.sin (π * β * t) ^ 2 / (π ^ 2 * β) := by
          field_simp
        rw [heq]
        gcongr
        exact Real.sin_sq_le_one _
      calc fejer β t * (1 + t ^ 2) = fejer β t + fejer β t * t ^ 2 := by ring
        _ ≤ β + 1 / (π ^ 2 * β) := add_le_add h2 h3
  calc fejer β t = fejer β t * (1 + t ^ 2) * (1 + t ^ 2)⁻¹ := by field_simp
    _ ≤ (β + 1 / (π ^ 2 * β)) * (1 + t ^ 2)⁻¹ := by
        exact mul_le_mul_of_nonneg_right key (by positivity)

lemma fejer_lower {β : ℝ} (hβ : 0 < β) {t : ℝ} (ht : |t| ≤ 1 / (4 * β)) :
    3 / 4 * β ≤ fejer β t := by
  unfold fejer
  split_ifs with h
  · linarith
  · set u := π * β * t with hu
    have hu0 : u ≠ 0 := mul_ne_zero (mul_ne_zero Real.pi_ne_zero hβ.ne') h
    have huabs : |u| ≤ π / 4 := by
      rw [hu, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hβ]
      calc π * β * |t| ≤ π * β * (1 / (4 * β)) := by
            exact mul_le_mul_of_nonneg_left ht (by positivity)
        _ = π / 4 := by field_simp
    have hv0 : 0 < |u| := abs_pos.2 hu0
    have hsin := Real.sin_gt_sub_cube hv0
    have hpi : π < 3.15 := Real.pi_lt_d2
    have hπ0 : 0 < π := Real.pi_pos
    have hlow : 0 < 1 - |u| ^ 2 / 6 := by nlinarith
    have hbase : 0 ≤ |u| * (1 - |u| ^ 2 / 6) := mul_nonneg hv0.le hlow.le
    have hs1 : |u| * (1 - |u| ^ 2 / 6) ≤ Real.sin |u| := by nlinarith
    have hs2 : (|u| * (1 - |u| ^ 2 / 6)) ^ 2 ≤ Real.sin |u| ^ 2 := by
      exact pow_le_pow_left₀ hbase hs1 2
    have hsq : Real.sin u ^ 2 = Real.sin |u| ^ 2 := by
      rcases abs_choice u with h' | h'
      · rw [h']
      · rw [h', Real.sin_neg]; ring
    have hden : π ^ 2 * β * t ^ 2 = u ^ 2 / β := by
      rw [hu]; field_simp
    rw [hden, hsq]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < u ^ 2 / β)]
    have hueq : |u| ^ 2 = u ^ 2 := sq_abs u
    have hs_le : |u| ^ 2 ≤ 0.63 := by nlinarith [huabs, hpi, abs_nonneg u]
    have hbr : 0 ≤ 1 / 4 - |u| ^ 2 / 3 + (|u| ^ 2) ^ 2 / 36 := by
      nlinarith [hs_le, sq_nonneg (|u| ^ 2)]
    have hkey2 : 3 / 4 * |u| ^ 2 ≤ (|u| * (1 - |u| ^ 2 / 6)) ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg (|u| : ℝ)) hbr]
    have hfin : 3 / 4 * u ^ 2 ≤ Real.sin |u| ^ 2 := by nlinarith [hkey2, hs2]
    calc 3 / 4 * β * (u ^ 2 / β) = 3 / 4 * u ^ 2 := by field_simp
      _ ≤ Real.sin |u| ^ 2 := hfin

/-! ### The kernel is the Fourier transform of the triangle -/

/-- The elementary interval-integral computation behind `fourier_triC`. -/
lemma tri_cos_integral {β : ℝ} (hβ : 0 < β) (c : ℝ) :
    (∫ x in (0 : ℝ)..β, (1 - x / β) * (2 * Real.cos (c * x)))
      = if c = 0 then β else 2 * (1 - Real.cos (c * β)) / (c ^ 2 * β) := by
  split_ifs with hc
  · subst hc
    simp only [zero_mul, Real.cos_zero, mul_one]
    have hF : ∀ x : ℝ, HasDerivAt (fun y : ℝ => 2 * y - y ^ 2 / β) ((1 - x / β) * 2) x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
        simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
      have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / β) (2 * x / β) x := by
        have := (hasDerivAt_pow 2 x).div_const β
        simpa using this
      have h3 := h1.sub h2
      have h4 : (1 - x / β) * 2 = 2 - 2 * x / β := by ring
      rw [h4]
      exact h3
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
      (((continuous_const.sub (continuous_id.div_const β)).mul continuous_const).intervalIntegrable _ _)]
    field_simp
    ring
  · have hF : ∀ x : ℝ, HasDerivAt
        (fun y : ℝ => (1 - y / β) * (2 / c * Real.sin (c * y)) - 2 / (c ^ 2 * β) * Real.cos (c * y))
        ((1 - x / β) * (2 * Real.cos (c * x))) x := by
      intro x
      have h1 : HasDerivAt (fun y : ℝ => 1 - y / β) (-(1 / β)) x := by
        simpa using ((hasDerivAt_id x).div_const β).const_sub 1
      have hcx : HasDerivAt (fun y : ℝ => c * y) c x := by
        simpa using (hasDerivAt_id x).const_mul c
      have h2 : HasDerivAt (fun y : ℝ => 2 / c * Real.sin (c * y)) (2 / c * (Real.cos (c * x) * c)) x :=
        hcx.sin.const_mul (2 / c)
      have h3 : HasDerivAt (fun y : ℝ => 2 / (c ^ 2 * β) * Real.cos (c * y))
          (2 / (c ^ 2 * β) * (-Real.sin (c * x) * c)) x :=
        hcx.cos.const_mul (2 / (c ^ 2 * β))
      have h4 := (h1.mul h2).sub h3
      have h5 : (1 - x / β) * (2 * Real.cos (c * x))
          = -(1 / β) * (2 / c * Real.sin (c * x))
              + (1 - x / β) * (2 / c * (Real.cos (c * x) * c))
            - 2 / (c ^ 2 * β) * (-Real.sin (c * x) * c) := by
        field_simp
        ring
      rw [h5]
      exact h4
    rw [integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
      (((continuous_const.sub (continuous_id.div_const β)).mul
        (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id)))).intervalIntegrable _ _)]
    have hβ' : β ≠ 0 := hβ.ne'
    have hc' : c ≠ 0 := hc
    simp only [mul_zero, Real.sin_zero, Real.cos_zero]
    field_simp
    ring

/-- The Fourier transform of the (complexified) triangle bump is the Fejér
kernel. -/
lemma fourier_triC {β : ℝ} (hβ : 0 < β) (t : ℝ) :
    𝓕 (fun x : ℝ => ((tri β x : ℝ) : ℂ)) t = ((fejer β t : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have hzero : ∀ x : ℝ, x ∉ Set.Ioc (-β) β →
      Complex.exp ((-2 * π * x * t : ℝ) * Complex.I) * ((tri β x : ℝ) : ℂ) = 0 := by
    intro x hx
    rcases le_or_gt β |x| with h | h
    · rw [tri_eq_zero hβ h, Complex.ofReal_zero, mul_zero]
    · exact absurd (Set.mem_Ioc.2 ⟨(abs_lt.1 h).1, (abs_lt.1 h).2.le⟩) hx
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  rw [← integral_of_le (by linarith : -β ≤ β)]
  have hGcont : Continuous fun v : ℝ =>
      Complex.exp ((-2 * π * v * t : ℝ) * Complex.I) * ((tri β v : ℝ) : ℂ) := by
    refine Continuous.mul ?_ (Complex.continuous_ofReal.comp (continuous_tri β))
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_const)
  rw [← integral_add_adjacent_intervals (a := -β) (b := 0) (c := β)
    (hGcont.intervalIntegrable _ _) (hGcont.intervalIntegrable _ _)]
  have hneg : (∫ v in (-β)..(0 : ℝ),
      Complex.exp ((-2 * π * v * t : ℝ) * Complex.I) * ((tri β v : ℝ) : ℂ))
      = ∫ v in (0 : ℝ)..β,
        Complex.exp ((-2 * π * (-v) * t : ℝ) * Complex.I) * ((tri β (-v) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_comp_neg
      (fun v => Complex.exp ((-2 * π * v * t : ℝ) * Complex.I) * ((tri β v : ℝ) : ℂ))]
    norm_num
  have hGneg : Continuous fun v : ℝ =>
      Complex.exp ((-2 * π * -v * t : ℝ) * Complex.I) * ((tri β (-v) : ℝ) : ℂ) :=
    hGcont.comp continuous_neg
  rw [hneg, ← integral_add (hGneg.intervalIntegrable _ _) (hGcont.intervalIntegrable _ _)]
  have hcomb : Set.EqOn
      (fun v : ℝ => Complex.exp ((-2 * π * (-v) * t : ℝ) * Complex.I) * ((tri β (-v) : ℝ) : ℂ)
        + Complex.exp ((-2 * π * v * t : ℝ) * Complex.I) * ((tri β v : ℝ) : ℂ))
      (fun v : ℝ => ((tri β v * (2 * Real.cos (2 * π * t * v)) : ℝ) : ℂ))
      (Set.uIcc 0 β) := by
    intro v _
    simp only [tri_neg]
    have h2c : Complex.exp ((2 * π * t * v : ℝ) * Complex.I)
        + Complex.exp ((-(2 * π * t * v) : ℝ) * Complex.I)
        = ((2 * Real.cos (2 * π * t * v) : ℝ) : ℂ) := by
      push_cast
      rw [← Complex.two_cos]
    have e1 : ((-2 * π * -v * t : ℝ) : ℂ) = ((2 * π * t * v : ℝ) : ℂ) := by
      push_cast; ring
    have e2 : ((-2 * π * v * t : ℝ) : ℂ) = ((-(2 * π * t * v) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e1, e2, mul_comm _ ((tri β v : ℝ) : ℂ), mul_comm _ ((tri β v : ℝ) : ℂ), ← mul_add, h2c]
    push_cast
    ring
  rw [intervalIntegral.integral_congr hcomb, intervalIntegral.integral_ofReal,
    Complex.ofReal_inj]
  have hEq : Set.EqOn (fun x : ℝ => tri β x * (2 * Real.cos (2 * π * t * x)))
      (fun x : ℝ => (1 - x / β) * (2 * Real.cos ((2 * π * t) * x))) (Set.uIcc 0 β) := by
    intro x hx
    rw [Set.uIcc_of_le hβ.le] at hx
    have h1 : tri β x = 1 - x / β := by
      unfold tri
      rw [abs_of_nonneg hx.1]
      exact max_eq_right (by
        have : x / β ≤ 1 := (div_le_one hβ).2 hx.2
        linarith)
    simp only [h1]
  rw [intervalIntegral.integral_congr hEq, tri_cos_integral hβ (2 * π * t)]
  unfold fejer
  rcases eq_or_ne t 0 with rfl | ht
  · rw [if_pos (by ring), if_pos rfl]
  · have hne : 2 * π * t ≠ 0 :=
      mul_ne_zero (by positivity : (0 : ℝ) < 2 * π).ne' ht
    rw [if_neg hne, if_neg ht]
    have hcos : Real.cos (2 * π * t * β) = 1 - 2 * Real.sin (π * t * β) ^ 2 := by
      have h := Real.cos_two_mul_eq_one_sub (π * t * β)
      calc Real.cos (2 * π * t * β) = Real.cos (2 * (π * t * β)) := by ring_nf
        _ = 1 - 2 * Real.sin (π * t * β) ^ 2 := h
    rw [hcos]
    have hsin : Real.sin (π * β * t) = Real.sin (π * t * β) := by ring_nf
    rw [hsin]
    have hπ : π ≠ 0 := Real.pi_ne_zero
    field_simp
    ring

/-- **The kernel identity** (the heart of the Gallagher/Fejér method): the
twisted total mass of the kernel is the triangle bump — in particular it is
nonnegative, at most `1` after normalization, and vanishes for
`|θ| ≥ 2πβ`. Proved by Fourier inversion. -/
lemma integral_fejer_mul_exp {β : ℝ} (hβ : 0 < β) (θ : ℝ) :
    (∫ t : ℝ, ((fejer β t : ℝ) : ℂ) * Complex.exp ((θ * t : ℝ) * Complex.I))
      = ((tri β (θ / (2 * π)) : ℝ) : ℂ) := by
  have hf : Integrable fun x : ℝ => ((tri β x : ℝ) : ℂ) := integrable_triC hβ
  have hFf : 𝓕 (fun x : ℝ => ((tri β x : ℝ) : ℂ)) = fun v : ℝ => ((fejer β v : ℝ) : ℂ) :=
    funext fun v => fourier_triC hβ v
  have hf2 : Integrable (𝓕 fun x : ℝ => ((tri β x : ℝ) : ℂ)) := by
    rw [hFf]; exact (fejer_integrable hβ).ofReal
  have hcont : ContinuousAt (fun x : ℝ => ((tri β x : ℝ) : ℂ)) (θ / (2 * π)) :=
    (Complex.continuous_ofReal.comp (continuous_tri β)).continuousAt
  have h3 := hf.fourierInv_fourier_eq hf2 hcont
  rw [Real.fourierInv_eq_fourier_neg, hFf, Real.fourier_real_eq_integral_exp_smul] at h3
  rw [← h3]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  have hreal : -2 * π * v * -(θ / (2 * π)) = θ * v := by
    field_simp
  simp only [smul_eq_mul]
  rw [hreal]
  exact mul_comm _ _

/-! ### The kernel mean value bound for a single exponential polynomial -/

/-- `exp(ixt) · conj (exp(iyt)) = exp(i(x−y)t)`. -/
lemma exp_mul_conj_exp (x y t : ℝ) :
    Complex.exp ((x * t : ℝ) * Complex.I) * conj (Complex.exp ((y * t : ℝ) * Complex.I))
      = Complex.exp (((x - y) * t : ℝ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- **Kernel mean value bound.** For any finite exponential polynomial
`S(t) = ∑ᵢ cᵢ e^{i λᵢ t}` and `T ≥ 2`,
`∫_{−T}^{T} ‖S‖² ≤ 6T · Re ∑ᵢⱼ cᵢ c̄ⱼ tri_{1/(4T)}((λᵢ−λⱼ)/2π)`. -/
lemma kernel_mvt {ι : Type*} (T : ℝ) (hT : 2 ≤ T) (s : Finset ι) (c : ι → ℂ) (lam : ι → ℝ) :
    (∫ t in (-T)..T, ‖∑ i ∈ s, c i * Complex.exp ((lam i * t : ℝ) * Complex.I)‖ ^ 2)
      ≤ 6 * T * (∑ i ∈ s, ∑ j ∈ s,
          c i * conj (c j) * ((tri (1 / (4 * T)) ((lam i - lam j) / (2 * π)) : ℝ) : ℂ)).re := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hβ : (0 : ℝ) < 1 / (4 * T) := by positivity
  set S : ℝ → ℂ := fun t => ∑ i ∈ s, c i * Complex.exp ((lam i * t : ℝ) * Complex.I) with hS
  have hScont : Continuous S := by
    rw [hS]
    refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)
  set B : ℝ := ∑ i ∈ s, ‖c i‖ with hB
  have hSb : ∀ t, ‖S t‖ ≤ B := by
    intro t
    rw [hS, hB]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  -- the kernel-times-exponential is integrable
  have hKexp : ∀ θ : ℝ, Integrable fun t : ℝ =>
      ((fejer (1 / (4 * T)) t : ℝ) : ℂ) * Complex.exp ((θ * t : ℝ) * Complex.I) := by
    intro θ
    refine Integrable.mono' (fejer_integrable hβ) ?_ (Eventually.of_forall fun t => ?_)
    · refine Measurable.aestronglyMeasurable (Measurable.mul ?_ ?_)
      · exact Complex.measurable_ofReal.comp (fejer_measurable _)
      · exact (Complex.continuous_exp.comp
          ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
            continuous_const)).measurable
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (fejer_nonneg hβ t)]
  -- the kernel times ‖S‖² is integrable
  have hKu : Integrable fun t : ℝ => fejer (1 / (4 * T)) t * ‖S t‖ ^ 2 := by
    refine Integrable.mono' ((fejer_integrable hβ).const_mul (B ^ 2)) ?_
      (Eventually.of_forall fun t => ?_)
    · exact ((fejer_measurable _).mul ((hScont.norm.pow 2).measurable)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (fejer_nonneg hβ t) (by positivity))]
      have h1 : ‖S t‖ ^ 2 ≤ B ^ 2 := by
        have h2 := hSb t
        nlinarith [norm_nonneg (S t)]
      calc fejer (1 / (4 * T)) t * ‖S t‖ ^ 2 ≤ fejer (1 / (4 * T)) t * B ^ 2 :=
            mul_le_mul_of_nonneg_left h1 (fejer_nonneg hβ t)
        _ = B ^ 2 * fejer (1 / (4 * T)) t := by ring
  -- Steps 1–2: majorize the interval by the kernel over the whole line
  have hstep12 : (∫ t in (-T)..T, ‖S t‖ ^ 2)
      ≤ (16 * T / 3) * ∫ t : ℝ, fejer (1 / (4 * T)) t * ‖S t‖ ^ 2 := by
    have hmono : (∫ t in (-T)..T, ‖S t‖ ^ 2)
        ≤ ∫ t in (-T)..T, (16 * T / 3) * (fejer (1 / (4 * T)) t * ‖S t‖ ^ 2) := by
      refine integral_mono_on (by linarith) ((hScont.norm.pow 2).intervalIntegrable _ _)
        (hKu.const_mul _).intervalIntegrable fun x hx => ?_
      have hxT : |x| ≤ 1 / (4 * (1 / (4 * T))) := by
        have h1 : |x| ≤ T := abs_le.2 ⟨hx.1, hx.2⟩
        have h2 : 1 / (4 * (1 / (4 * T))) = T := by field_simp
        linarith [h2 ▸ h1]
      have hlow := fejer_lower hβ hxT
      have h0 : (0 : ℝ) ≤ ‖S x‖ ^ 2 := by positivity
      have hone : (16 * T / 3) * (3 / 4 * (1 / (4 * T))) = 1 := by
        field_simp
        norm_num
      calc ‖S x‖ ^ 2 = ((16 * T / 3) * (3 / 4 * (1 / (4 * T)))) * ‖S x‖ ^ 2 := by
            rw [hone, one_mul]
        _ ≤ (16 * T / 3) * (fejer (1 / (4 * T)) x * ‖S x‖ ^ 2) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hlow h0) (by positivity)
    refine hmono.trans ?_
    rw [intervalIntegral.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [integral_of_le (by linarith : -T ≤ T)]
    exact setIntegral_le_integral hKu
      (Eventually.of_forall fun t => mul_nonneg (fejer_nonneg hβ t) (by positivity))
  -- Step 3: identify the whole-line kernel integral with the bilinear form
  have hstep3 : (∫ t : ℝ, fejer (1 / (4 * T)) t * ‖S t‖ ^ 2)
      = (∑ i ∈ s, ∑ j ∈ s,
          c i * conj (c j) * ((tri (1 / (4 * T)) ((lam i - lam j) / (2 * π)) : ℝ) : ℂ)).re := by
    have hpt : ∀ t : ℝ, ((fejer (1 / (4 * T)) t * ‖S t‖ ^ 2 : ℝ) : ℂ)
        = ∑ p ∈ s ×ˢ s, (c p.1 * conj (c p.2)) *
            (((fejer (1 / (4 * T)) t : ℝ) : ℂ) *
              Complex.exp (((lam p.1 - lam p.2) * t : ℝ) * Complex.I)) := by
      intro t
      have h1 : ((‖S t‖ ^ 2 : ℝ) : ℂ) = S t * conj (S t) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      rw [Complex.ofReal_mul, h1]
      conv_lhs => rw [hS]
      rw [map_sum, Finset.sum_mul_sum, ← Finset.sum_product', Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [map_mul]
      have h2 : (c p.1 * Complex.exp ((lam p.1 * t : ℝ) * Complex.I)) *
          (conj (c p.2) * conj (Complex.exp ((lam p.2 * t : ℝ) * Complex.I)))
          = (c p.1 * conj (c p.2)) *
            (Complex.exp ((lam p.1 * t : ℝ) * Complex.I) *
              conj (Complex.exp ((lam p.2 * t : ℝ) * Complex.I))) := by ring
      rw [h2, exp_mul_conj_exp]
      ring
    have hC : (∫ t : ℝ, ((fejer (1 / (4 * T)) t * ‖S t‖ ^ 2 : ℝ) : ℂ))
        = ∑ i ∈ s, ∑ j ∈ s,
            c i * conj (c j) * ((tri (1 / (4 * T)) ((lam i - lam j) / (2 * π)) : ℝ) : ℂ) := by
      calc (∫ t : ℝ, ((fejer (1 / (4 * T)) t * ‖S t‖ ^ 2 : ℝ) : ℂ))
          = ∫ t : ℝ, ∑ p ∈ s ×ˢ s, (c p.1 * conj (c p.2)) *
              (((fejer (1 / (4 * T)) t : ℝ) : ℂ) *
                Complex.exp (((lam p.1 - lam p.2) * t : ℝ) * Complex.I)) :=
            integral_congr_ae (Eventually.of_forall hpt)
        _ = ∑ p ∈ s ×ˢ s, ∫ t : ℝ, (c p.1 * conj (c p.2)) *
              (((fejer (1 / (4 * T)) t : ℝ) : ℂ) *
                Complex.exp (((lam p.1 - lam p.2) * t : ℝ) * Complex.I)) :=
            integral_finsetSum _ fun p _ => (hKexp _).const_mul _
        _ = ∑ p ∈ s ×ˢ s, (c p.1 * conj (c p.2)) *
              ((tri (1 / (4 * T)) ((lam p.1 - lam p.2) / (2 * π)) : ℝ) : ℂ) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [MeasureTheory.integral_const_mul, integral_fejer_mul_exp hβ]
        _ = ∑ i ∈ s, ∑ j ∈ s,
              c i * conj (c j) * ((tri (1 / (4 * T)) ((lam i - lam j) / (2 * π)) : ℝ) : ℂ) :=
            Finset.sum_product' s s fun i j =>
              c i * conj (c j) * ((tri (1 / (4 * T)) ((lam i - lam j) / (2 * π)) : ℝ) : ℂ)
    have h4 := congrArg Complex.re hC
    rwa [integral_complex_ofReal] at h4
  have hnn : (0 : ℝ) ≤ ∫ t : ℝ, fejer (1 / (4 * T)) t * ‖S t‖ ^ 2 :=
    integral_nonneg fun t => mul_nonneg (fejer_nonneg hβ t) (by positivity)
  calc (∫ t in (-T)..T, ‖S t‖ ^ 2)
      ≤ (16 * T / 3) * ∫ t : ℝ, fejer (1 / (4 * T)) t * ‖S t‖ ^ 2 := hstep12
    _ ≤ 6 * T * ∫ t : ℝ, fejer (1 / (4 * T)) t * ‖S t‖ ^ 2 := by nlinarith
    _ = 6 * T * (∑ i ∈ s, ∑ j ∈ s,
          c i * conj (c j) * ((tri (1 / (4 * T)) ((lam i - lam j) / (2 * π)) : ℝ) : ℂ)).re := by
        rw [hstep3]

/-! ### Character orthogonality -/

/-- On units, conjugation of a Dirichlet character value is the value at the
inverse. -/
lemma conj_char_eq_inv {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {y : ZMod d}
    (hy : IsUnit y) : conj (χ y) = χ y⁻¹ := by
  have h1 : χ y * χ y⁻¹ = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit y hy, map_one]
  have hnorm : ‖χ y‖ = 1 := by
    have h2 := χ.unit_norm_eq_one hy.unit
    rwa [IsUnit.unit_spec] at h2
  rw [← Complex.inv_eq_conj hnorm]
  exact (eq_inv_of_mul_eq_one_right h1).symm

/-- Orthogonality: `∑_χ χ(x) conj (χ(y))` is `φ(d)` when `x = y` is a unit and
`0` otherwise. -/
lemma sum_char_mul_conj {d : ℕ} [NeZero d] (x y : ZMod d) :
    (∑ χ : DirichletCharacter ℂ d, χ x * conj (χ y))
      = if x = y ∧ IsUnit y then ((d.totient : ℕ) : ℂ) else 0 := by
  by_cases hy : IsUnit y
  · have h1 : ∀ χ : DirichletCharacter ℂ d, χ x * conj (χ y) = χ y⁻¹ * χ x := fun χ => by
      rw [conj_char_eq_inv χ hy, mul_comm]
    rw [Finset.sum_congr rfl fun χ _ => h1 χ,
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ hy x]
    by_cases hxy : x = y
    · rw [if_pos hxy.symm, if_pos ⟨hxy, hy⟩]
    · rw [if_neg (fun h => hxy h.symm), if_neg (fun h => hxy h.1)]
  · rw [if_neg (fun h => hy h.2)]
    refine Finset.sum_eq_zero fun χ _ => ?_
    rw [MulChar.map_nonunit χ hy, map_zero, mul_zero]

/-! ### Counting integers in a residue class inside a multiplicative window -/

/-- `log n − log m ≥ (n − m)/n` for `1 ≤ m ≤ n`. -/
lemma log_gap_lower {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    ((n : ℝ) - m) / n ≤ Real.log n - Real.log m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hm.trans hmn
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (m : ℝ) / n by positivity)
  rw [Real.log_div hm0.ne' hn0.ne'] at h
  have h2 : (m : ℝ) / n - 1 = -(((n : ℝ) - m) / n) := by
    field_simp
    ring
  linarith [h, h2]

/-- Two integers of `[1, N]` at logarithmic distance `< π/(2T)` are at
distance `≤ 2N/T`. -/
lemma window_abs_bound {m n N : ℕ} (T : ℝ) (hT : 2 ≤ T) (hm : 1 ≤ m) (hmN : m ≤ N)
    (hn : 1 ≤ n) (hnN : n ≤ N)
    (hlog : |Real.log n - Real.log m| < π / (2 * T)) : |(n : ℝ) - m| ≤ 2 * N / T := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hm.trans hmN
  have hN0 : (0 : ℝ) < N := by linarith
  have hπ : π / (2 * T) ≤ 2 / T := by
    rw [div_le_div_iff₀ (by positivity) hT0]
    nlinarith [Real.pi_lt_four]
  rcases le_total m n with hmn | hnm
  · have h1 := log_gap_lower hm hmn
    have h2 : Real.log n - Real.log m < π / (2 * T) := lt_of_le_of_lt (le_abs_self _) hlog
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hm.trans hmn
    have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
    have h3 : ((n : ℝ) - m) / N ≤ ((n : ℝ) - m) / n := by
      gcongr
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - m)]
    have h4 : ((n : ℝ) - m) / N < 2 / T := lt_of_le_of_lt (h3.trans h1) (lt_of_lt_of_le h2 hπ)
    have h5 := (div_lt_iff₀ hN0).1 h4
    calc (n : ℝ) - m ≤ 2 / T * N := h5.le
      _ = 2 * N / T := by ring
  · have hlog' : |Real.log m - Real.log n| < π / (2 * T) := by rwa [abs_sub_comm]
    have h1 := log_gap_lower hn hnm
    have h2 : Real.log m - Real.log n < π / (2 * T) := lt_of_le_of_lt (le_abs_self _) hlog'
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hn.trans hnm
    have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
    have h3 : ((m : ℝ) - n) / N ≤ ((m : ℝ) - n) / m := by
      gcongr
    rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - n)]
    have h4 : ((m : ℝ) - n) / N < 2 / T := lt_of_le_of_lt (h3.trans h1) (lt_of_lt_of_le h2 hπ)
    have h5 := (div_lt_iff₀ hN0).1 h4
    calc (m : ℝ) - n ≤ 2 / T * N := h5.le
      _ = 2 * N / T := by ring

/-- The window count: at most `4N/(dT) + 1` integers `n ∈ [1, N]` are
congruent to `m` mod `d` and within logarithmic distance `π/(2T)` of `m`. -/
lemma sum_window_le (d : ℕ) (hd : 0 < d) (T : ℝ) (hT : 2 ≤ T) (N m : ℕ)
    (hm : m ∈ Finset.Icc 1 N) :
    (∑ n ∈ Finset.Icc 1 N,
        if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
        then (1 : ℝ) else 0)
      ≤ 4 * N / (d * T) + 1 := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.1 hm
  rw [Finset.sum_boole]
  set J : ℤ := ⌊2 * (N : ℝ) / (d * T)⌋ with hJdef
  have hJ0 : 0 ≤ J := by rw [hJdef]; exact Int.floor_nonneg.2 (by positivity)
  clear_value J
  -- membership facts for elements of the filtered set
  have hfact : ∀ n ∈ Finset.Icc 1 N,
      ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T)) →
      (d : ℤ) ∣ (n : ℤ) - (m : ℤ) ∧ |(n : ℝ) - m| ≤ 2 * N / T := by
    intro n hn hcond
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.1 hn
    constructor
    · have h1 : m ≡ n [MOD d] := (ZMod.natCast_eq_natCast_iff m n d).1 hcond.1
      exact h1.dvd
    · exact window_abs_bound T hT hm1 hmN hn1 hnN hcond.2
  have hstep : (((Finset.Icc 1 N).filter fun n : ℕ =>
      (m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T)).card)
      ≤ (Finset.Icc (-J) J).card := by
    refine Finset.card_le_card_of_injOn (fun n => ((n : ℤ) - (m : ℤ)) / (d : ℤ)) ?_ ?_
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter] at hn
      obtain ⟨hdvd, habs⟩ := hfact n hn.1 hn.2
      have hjd : ((n : ℤ) - (m : ℤ)) / (d : ℤ) * (d : ℤ) = (n : ℤ) - (m : ℤ) :=
        Int.ediv_mul_cancel hdvd
      have hcast2 : ((((n : ℤ) - (m : ℤ)) / (d : ℤ) : ℤ) : ℝ) * (d : ℝ) = (n : ℝ) - m := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hjd
      have habs2 : |((((n : ℤ) - (m : ℤ)) / (d : ℤ) : ℤ) : ℝ)| * (d : ℝ) = |(n : ℝ) - m| := by
        rw [← abs_of_pos hd0, ← abs_mul, hcast2]
      have h6 : |((((n : ℤ) - (m : ℤ)) / (d : ℤ) : ℤ) : ℝ)| * (d : ℝ) ≤ 2 * N / T := by
        rw [habs2]; exact habs
      have h7 : |((((n : ℤ) - (m : ℤ)) / (d : ℤ) : ℤ) : ℝ)| ≤ 2 * N / (d * T) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < d * T)]
        have h8 := mul_le_mul_of_nonneg_right h6 hT0.le
        rw [div_mul_cancel₀ _ hT0.ne'] at h8
        nlinarith [h8]
      simp only [Finset.mem_coe, Finset.mem_Icc]
      constructor
      · rw [neg_le, hJdef]
        refine Int.le_floor.2 ?_
        calc ((-(((n : ℤ) - (m : ℤ)) / (d : ℤ)) : ℤ) : ℝ)
            = -((((n : ℤ) - (m : ℤ)) / (d : ℤ) : ℤ) : ℝ) := by push_cast; ring
          _ ≤ |((((n : ℤ) - (m : ℤ)) / (d : ℤ) : ℤ) : ℝ)| := neg_le_abs _
          _ ≤ 2 * N / (d * T) := h7
      · rw [hJdef]
        refine Int.le_floor.2 ?_
        exact (le_abs_self _).trans h7
    · intro n1 h1 n2 h2 heq
      simp only [Finset.mem_coe, Finset.mem_filter] at h1 h2
      have hdvd1 := (hfact n1 h1.1 h1.2).1
      have hdvd2 := (hfact n2 h2.1 h2.2).1
      have e1 := Int.ediv_mul_cancel hdvd1
      have e2 := Int.ediv_mul_cancel hdvd2
      have heq' : ((n1 : ℤ) - (m : ℤ)) / (d : ℤ) = ((n2 : ℤ) - (m : ℤ)) / (d : ℤ) := heq
      have h3 : (n1 : ℤ) - (m : ℤ) = (n2 : ℤ) - (m : ℤ) := by
        rw [← e1, ← e2, heq']
      have h4 : (n1 : ℤ) = (n2 : ℤ) := by omega
      exact_mod_cast h4
  have hcard : ((Finset.Icc (-J) J).card : ℝ) ≤ 4 * N / (d * T) + 1 := by
    have h1 : ((Finset.Icc (-J) J).card : ℤ) = 2 * J + 1 := by
      rw [Int.card_Icc_of_le (a := -J) (b := J) (by omega)]
      ring
    have h2 : (J : ℝ) ≤ 2 * N / (d * T) := by rw [hJdef]; exact Int.floor_le _
    have h3 : ((Finset.Icc (-J) J).card : ℝ) = 2 * (J : ℝ) + 1 := by exact_mod_cast h1
    have h4 : 2 * (2 * (N : ℝ) / (d * T)) = 4 * N / (d * T) := by ring
    rw [h3]
    linarith
  calc ((((Finset.Icc 1 N).filter fun n : ℕ =>
        (m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T)).card) : ℝ)
      ≤ ((Finset.Icc (-J) J).card : ℝ) := by exact_mod_cast hstep
    _ ≤ 4 * N / (d * T) + 1 := hcard

/-! ### The main theorem -/

/-- Per-pair bound: real part of the orthogonality-collapsed term against the
window indicator. -/
lemma term_bound (d : ℕ) [NeZero d] (T : ℝ) (hT : 2 ≤ T) (am an : ℂ) (m n : ℕ) :
    (am * conj an * ((tri (1 / (4 * T)) ((-Real.log m - -Real.log n) / (2 * π)) : ℝ) : ℂ) *
        (if (m : ZMod d) = (n : ZMod d) ∧ IsUnit ((n : ZMod d))
          then ((d.totient : ℕ) : ℂ) else 0)).re
      ≤ (d.totient : ℝ) * ((‖am‖ ^ 2 + ‖an‖ ^ 2) / 2 *
          (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
            then (1 : ℝ) else 0)) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hβ : (0 : ℝ) < 1 / (4 * T) := by positivity
  by_cases hq : ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
  · rw [if_pos hq, mul_one]
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_conj]
    have h1 : ‖((tri (1 / (4 * T)) ((-Real.log m - -Real.log n) / (2 * π)) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (tri_nonneg _ _)]
      exact tri_le_one hβ _
    have h2 : ‖(if (m : ZMod d) = (n : ZMod d) ∧ IsUnit ((n : ZMod d))
        then ((d.totient : ℕ) : ℂ) else 0)‖ ≤ (d.totient : ℝ) := by
      split_ifs
      · rw [Complex.norm_natCast]
      · simp
    have h3 : ‖am‖ * ‖an‖ ≤ (‖am‖ ^ 2 + ‖an‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖am‖ - ‖an‖)]
    calc ‖am‖ * ‖an‖ *
          ‖((tri (1 / (4 * T)) ((-Real.log m - -Real.log n) / (2 * π)) : ℝ) : ℂ)‖ *
          ‖(if (m : ZMod d) = (n : ZMod d) ∧ IsUnit ((n : ZMod d))
            then ((d.totient : ℕ) : ℂ) else 0)‖
        ≤ (‖am‖ * ‖an‖) * (d.totient : ℝ) := by
          refine mul_le_mul ?_ h2 (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          calc ‖am‖ * ‖an‖ *
              ‖((tri (1 / (4 * T)) ((-Real.log m - -Real.log n) / (2 * π)) : ℝ) : ℂ)‖
              ≤ ‖am‖ * ‖an‖ * 1 :=
                mul_le_mul_of_nonneg_left h1 (mul_nonneg (norm_nonneg _) (norm_nonneg _))
            _ = ‖am‖ * ‖an‖ := mul_one _
      _ ≤ ((‖am‖ ^ 2 + ‖an‖ ^ 2) / 2) * (d.totient : ℝ) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = (d.totient : ℝ) * ((‖am‖ ^ 2 + ‖an‖ ^ 2) / 2) := mul_comm _ _
  · rw [if_neg hq, mul_zero, mul_zero]
    by_cases hA : (m : ZMod d) = (n : ZMod d)
    · have hB : ¬|Real.log n - Real.log m| < π / (2 * T) := fun hB => hq ⟨hA, hB⟩
      have hge : π / (2 * T) ≤ |Real.log n - Real.log m| := not_lt.1 hB
      have htri : tri (1 / (4 * T)) ((-Real.log m - -Real.log n) / (2 * π)) = 0 := by
        apply tri_eq_zero hβ
        have harg : -Real.log m - -Real.log n = Real.log n - Real.log m := by ring
        rw [harg, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * π)]
        have h1 : 1 / (4 * T) * (2 * π) = π / (2 * T) := by field_simp; ring
        rw [h1]
        exact hge
      rw [htri, Complex.ofReal_zero, mul_zero, zero_mul, Complex.zero_re]
    · rw [if_neg (fun h => hA h.1), mul_zero, Complex.zero_re]

set_option maxHeartbeats 1000000 in
/-- **Character-twisted mean value theorem (Z6a, item 1; exponential form).**
For `d ≥ 1`, `T ≥ 2`, and complex coefficients supported on `[1, N]`,

  `∑_{χ mod d} ∫_{−T}^{T} ‖∑_{n ≤ N} aₙ χ(n) e^{−it·log n}‖² dt
      ≤ 100 (N + dT) ∑_{n ≤ N} ‖aₙ‖²`.

Note `e^{−it·log n} = n^{−it}`; see `mean_value_chars_cpow` for the `cpow`
form. Log-free, absolute constant `100`. -/
theorem mean_value_chars (d : ℕ) (hd : 0 < d) (T : ℝ) (hT : 2 ≤ T) (N : ℕ) (a : ℕ → ℂ) :
    (∑ χ : DirichletCharacter ℂ d,
      ∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2)
      ≤ 100 * ((N : ℝ) + d * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have : NeZero d := ⟨hd.ne'⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  -- Step A: per-character kernel bound, summed over χ
  have hA : (∑ χ : DirichletCharacter ℂ d,
      ∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2)
      ≤ 6 * T * (∑ χ : DirichletCharacter ℂ d, ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (a m * χ (m : ZMod d)) * conj (a n * χ (n : ZMod d)) *
            ((tri (1 / (4 * T)) ((-Real.log m - -Real.log n) / (2 * π)) : ℝ) : ℂ)).re := by
    have h1 : ∀ χ : DirichletCharacter ℂ d,
        (∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N,
          a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2)
        ≤ 6 * T * (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (a m * χ (m : ZMod d)) * conj (a n * χ (n : ZMod d)) *
              ((tri (1 / (4 * T)) ((-Real.log m - -Real.log n) / (2 * π)) : ℝ) : ℂ)).re :=
      fun χ => kernel_mvt T hT (Finset.Icc 1 N)
        (fun n => a n * χ (n : ZMod d)) (fun n => -Real.log n)
    calc (∑ χ : DirichletCharacter ℂ d, ∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N,
          a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2)
        ≤ ∑ χ : DirichletCharacter ℂ d,
            6 * T * (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
              (a m * χ (m : ZMod d)) * conj (a n * χ (n : ZMod d)) *
                ((tri (1 / (4 * T)) ((-Real.log m - -Real.log n) / (2 * π)) : ℝ) : ℂ)).re :=
          Finset.sum_le_sum fun χ _ => h1 χ
      _ = 6 * T * (∑ χ : DirichletCharacter ℂ d, ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (a m * χ (m : ZMod d)) * conj (a n * χ (n : ZMod d)) *
              ((tri (1 / (4 * T)) ((-Real.log m - -Real.log n) / (2 * π)) : ℝ) : ℂ)).re := by
          rw [← Finset.mul_sum]
          congr 1
          simp only [Complex.re_sum]
  -- Step B: swap sums and apply orthogonality
  have hB : (∑ χ : DirichletCharacter ℂ d, ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (a m * χ (m : ZMod d)) * conj (a n * χ (n : ZMod d)) *
          ((tri (1 / (4 * T)) ((-Real.log m - -Real.log n) / (2 * π)) : ℝ) : ℂ))
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          a m * conj (a n) *
            ((tri (1 / (4 * T)) ((-Real.log m - -Real.log n) / (2 * π)) : ℝ) : ℂ) *
            (if (m : ZMod d) = (n : ZMod d) ∧ IsUnit ((n : ZMod d))
              then ((d.totient : ℕ) : ℂ) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← sum_char_mul_conj (d := d) (m : ZMod d) (n : ZMod d), Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [map_mul]
    ring
  -- Step C: real-part bound with the window indicator
  have hC : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        a m * conj (a n) *
          ((tri (1 / (4 * T)) ((-Real.log m - -Real.log n) / (2 * π)) : ℝ) : ℂ) *
          (if (m : ZMod d) = (n : ZMod d) ∧ IsUnit ((n : ZMod d))
            then ((d.totient : ℕ) : ℂ) else 0)).re
      ≤ (d.totient : ℝ) * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (‖a m‖ ^ 2 + ‖a n‖ ^ 2) / 2 *
            (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
              then (1 : ℝ) else 0) := by
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    rw [Complex.re_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun n _ => term_bound d T hT (a m) (a n) m n
  -- Step D: symmetrize
  have hQsymm : ∀ m n : ℕ,
      (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
        then (1 : ℝ) else 0)
      = (if ((n : ZMod d) = (m : ZMod d) ∧ |Real.log m - Real.log n| < π / (2 * T))
        then (1 : ℝ) else 0) := by
    intro m n
    refine if_congr ⟨fun h => ⟨h.1.symm, by rw [abs_sub_comm]; exact h.2⟩,
      fun h => ⟨h.1.symm, by rw [abs_sub_comm]; exact h.2⟩⟩ rfl rfl
  have hsym : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        (‖a m‖ ^ 2 + ‖a n‖ ^ 2) / 2 *
          (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
            then (1 : ℝ) else 0))
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖a m‖ ^ 2 *
            (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
              then (1 : ℝ) else 0) := by
    have hswap : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖a n‖ ^ 2 / 2 *
            (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
              then (1 : ℝ) else 0))
        = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            ‖a m‖ ^ 2 / 2 *
              (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
                then (1 : ℝ) else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
      rw [hQsymm n m]
    calc (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (‖a m‖ ^ 2 + ‖a n‖ ^ 2) / 2 *
            (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
              then (1 : ℝ) else 0))
        = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            (‖a m‖ ^ 2 / 2 *
              (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
                then (1 : ℝ) else 0)
            + ‖a n‖ ^ 2 / 2 *
              (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
                then (1 : ℝ) else 0))) := by
          refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
          ring
      _ = (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            ‖a m‖ ^ 2 / 2 *
              (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
                then (1 : ℝ) else 0))
          + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
              ‖a n‖ ^ 2 / 2 *
                (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
                  then (1 : ℝ) else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [← Finset.sum_add_distrib]
      _ = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
            ‖a m‖ ^ 2 *
              (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
                then (1 : ℝ) else 0) := by
          rw [hswap, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
  -- Step E: count the window
  have hcount : (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ‖a m‖ ^ 2 *
          (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
            then (1 : ℝ) else 0))
      ≤ (4 * N / (d * T) + 1) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    rw [← Finset.mul_sum]
    calc ‖a m‖ ^ 2 * (∑ n ∈ Finset.Icc 1 N,
          if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
          then (1 : ℝ) else 0)
        ≤ ‖a m‖ ^ 2 * (4 * N / (d * T) + 1) :=
          mul_le_mul_of_nonneg_left (sum_window_le d hd T hT N m hm) (by positivity)
      _ = (4 * N / (d * T) + 1) * ‖a m‖ ^ 2 := mul_comm _ _
  -- final numeric assembly
  have htot : (d.totient : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  have htot0 : (0 : ℝ) ≤ (d.totient : ℝ) := by positivity
  have hSig0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  have hkey : 6 * T * ((d.totient : ℝ) * (4 * N / (d * T) + 1)) ≤ 100 * ((N : ℝ) + d * T) := by
    have h1 : (4 * (N : ℝ) / (d * T) + 1) = (4 * N + d * T) / (d * T) := by field_simp
    rw [h1]
    have h2 : 6 * T * ((d.totient : ℝ) * ((4 * N + d * T) / (d * T)))
        = (6 * T * (d.totient : ℝ)) * (4 * N + d * T) / (d * T) := by ring
    rw [h2, div_le_iff₀ (by positivity : (0 : ℝ) < d * T)]
    have h3 : (0 : ℝ) ≤ 4 * N + d * T := by positivity
    have h4 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    nlinarith [mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left htot (by linarith : (0 : ℝ) ≤ 6 * T)) h3,
      mul_pos hd0 hT0, mul_nonneg (mul_nonneg h4 hd0.le) hT0.le,
      sq_nonneg ((d : ℝ) * T)]
  calc (∑ χ : DirichletCharacter ℂ d,
      ∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2)
      ≤ 6 * T * (∑ χ : DirichletCharacter ℂ d, ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (a m * χ (m : ZMod d)) * conj (a n * χ (n : ZMod d)) *
            ((tri (1 / (4 * T)) ((-Real.log m - -Real.log n) / (2 * π)) : ℝ) : ℂ)).re := hA
    _ = 6 * T * (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          a m * conj (a n) *
            ((tri (1 / (4 * T)) ((-Real.log m - -Real.log n) / (2 * π)) : ℝ) : ℂ) *
            (if (m : ZMod d) = (n : ZMod d) ∧ IsUnit ((n : ZMod d))
              then ((d.totient : ℕ) : ℂ) else 0)).re := by rw [hB]
    _ ≤ 6 * T * ((d.totient : ℝ) * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          (‖a m‖ ^ 2 + ‖a n‖ ^ 2) / 2 *
            (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
              then (1 : ℝ) else 0)) :=
        mul_le_mul_of_nonneg_left hC (by positivity)
    _ = 6 * T * ((d.totient : ℝ) * ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          ‖a m‖ ^ 2 *
            (if ((m : ZMod d) = (n : ZMod d) ∧ |Real.log n - Real.log m| < π / (2 * T))
              then (1 : ℝ) else 0)) := by rw [hsym]
    _ ≤ 6 * T * ((d.totient : ℝ) * ((4 * N / (d * T) + 1) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcount htot0) (by positivity)
    _ = (6 * T * ((d.totient : ℝ) * (4 * N / (d * T) + 1))) *
          ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by ring
    _ ≤ (100 * ((N : ℝ) + d * T)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hkey hSig0
    _ = 100 * ((N : ℝ) + d * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by ring

/-- The `n ^ (−it)` (complex power) form of `mean_value_chars`. -/
theorem mean_value_chars_cpow (d : ℕ) (hd : 0 < d) (T : ℝ) (hT : 2 ≤ T) (N : ℕ) (a : ℕ → ℂ) :
    (∑ χ : DirichletCharacter ℂ d,
      ∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod d) * (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ^ 2)
      ≤ 100 * ((N : ℝ) + d * T) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have hconv : ∀ (t : ℝ), ∀ n ∈ Finset.Icc 1 N,
      (n : ℂ) ^ (-(Complex.I * (t : ℂ))) = Complex.exp ((-Real.log n * t : ℝ) * Complex.I) := by
    intro t n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    rw [Complex.cpow_def_of_ne_zero hn0]
    congr 1
    rw [show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log (Nat.cast_nonneg n)]
    push_cast
    ring
  refine le_of_le_of_eq (le_of_eq ?_) rfl |>.trans (mean_value_chars d hd T hT N a)
  refine Finset.sum_congr rfl fun χ _ => ?_
  refine intervalIntegral.integral_congr fun t _ => ?_
  have h1 : (∑ n ∈ Finset.Icc 1 N, a n * χ (n : ZMod d) * (n : ℂ) ^ (-(Complex.I * (t : ℂ))))
      = ∑ n ∈ Finset.Icc 1 N,
          a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I) :=
    Finset.sum_congr rfl fun n hn => by rw [hconv t n hn]
  rw [h1]

/-! ### The discrete-points corollary (item 3) -/

/-- Derivative of a single twisted exponential. -/
lemma hasDerivAt_exp_mul_I (lam t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp ((lam * u : ℝ) * Complex.I))
      (((lam : ℂ) * Complex.I) * Complex.exp ((lam * t : ℝ) * Complex.I)) t := by
  have h2 : (fun u : ℝ => ((lam * u : ℝ) : ℂ) * Complex.I)
      = fun u : ℝ => ((lam : ℂ) * Complex.I) * ((u : ℝ) : ℂ) := by
    funext u; push_cast; ring
  have h1 : HasDerivAt (fun u : ℝ => ((lam * u : ℝ) : ℂ) * Complex.I)
      ((lam : ℂ) * Complex.I) t := by
    rw [h2]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul ((lam : ℂ) * Complex.I)
  have h3 := h1.cexp
  convert h3 using 1
  ring

set_option maxHeartbeats 2000000 in
/-- **Discrete mean value bound (Z6a, item 3).** For any finite set `R` of
1-separated points in `[−T, T]`,

  `∑_{χ mod d} ∑_{r ∈ R} ‖∑_{n ≤ N} aₙ χ(n) n^{−i r}‖²
      ≤ 200 (N + d(T+1)) ∑_{n ≤ N} (1 + log² n) ‖aₙ‖²`,

via the Sobolev step `‖S(r)‖² ≤ ∫_{|u−r| ≤ 1/2} (2‖S‖² + ‖S′‖²)`; the
derivative polynomial pays the `(1 + log² n)` weight. -/
theorem mean_value_chars_discrete (d : ℕ) (hd : 0 < d) (T : ℝ) (hT : 2 ≤ T) (N : ℕ)
    (a : ℕ → ℂ) (R : Finset ℝ) (hRT : ∀ r ∈ R, |r| ≤ T)
    (hsep : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → 1 ≤ |r - r'|) :
    (∑ χ : DirichletCharacter ℂ d, ∑ r ∈ R, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * r : ℝ) * Complex.I)‖ ^ 2)
      ≤ 200 * ((N : ℝ) + d * (T + 1)) *
          ∑ n ∈ Finset.Icc 1 N, (1 + Real.log n ^ 2) * ‖a n‖ ^ 2 := by
  have : NeZero d := ⟨hd.ne'⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hT1 : (2 : ℝ) ≤ T + 1 := by linarith
  -- the per-character Sobolev bound
  have hper : ∀ χ : DirichletCharacter ℂ d,
      (∑ r ∈ R, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * r : ℝ) * Complex.I)‖ ^ 2)
      ≤ 2 * (∫ t in (-(T + 1))..(T + 1), ‖∑ n ∈ Finset.Icc 1 N,
            a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2)
        + ∫ t in (-(T + 1))..(T + 1), ‖∑ n ∈ Finset.Icc 1 N,
            (a n * ((-Real.log n : ℝ) : ℂ) * Complex.I) * χ (n : ZMod d) *
              Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2 := by
    intro χ
    set S : ℝ → ℂ := fun t => ∑ n ∈ Finset.Icc 1 N,
      a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I) with hSdef
    set S' : ℝ → ℂ := fun t => ∑ n ∈ Finset.Icc 1 N,
      (a n * ((-Real.log n : ℝ) : ℂ) * Complex.I) * χ (n : ZMod d) *
        Complex.exp ((-Real.log n * t : ℝ) * Complex.I) with hS'def
    have hScont : Continuous S := by
      rw [hSdef]
      refine continuous_finsetSum _ fun n _ => continuous_const.mul ?_
      exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
          continuous_const)
    have hS'cont : Continuous S' := by
      rw [hS'def]
      refine continuous_finsetSum _ fun n _ => continuous_const.mul ?_
      exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
          continuous_const)
    have hSsq : Continuous fun u : ℝ => ‖S u‖ ^ 2 := by fun_prop
    have hS'sq : Continuous fun u : ℝ => ‖S' u‖ ^ 2 := by fun_prop
    have hderiv : ∀ t : ℝ, HasDerivAt S (S' t) t := by
      intro t
      simp only [hSdef, hS'def]
      refine HasDerivAt.fun_sum fun n _ => ?_
      have h0 := (hasDerivAt_exp_mul_I (-Real.log n) t).const_mul (a n * χ (n : ZMod d))
      have hrw : a n * ((-Real.log n : ℝ) : ℂ) * Complex.I * χ (n : ZMod d) *
          Complex.exp ((-Real.log n * t : ℝ) * Complex.I)
          = a n * χ (n : ZMod d) * (((-Real.log n : ℝ) : ℂ) * Complex.I *
              Complex.exp ((-Real.log n * t : ℝ) * Complex.I)) := by ring
      rw [hrw]
      exact h0
    -- derivative of ‖S‖²
    have hFd : ∀ t : ℝ, HasDerivAt (fun u => ‖S u‖ ^ 2)
        ((S' t * conj (S t) + S t * conj (S' t)).re) t := by
      intro t
      have hconjS : HasDerivAt (fun u => conj (S u)) (conj (S' t)) t :=
        HasDerivAt.star (hderiv t)
      have h1 : HasDerivAt (fun u => S u * conj (S u))
          (S' t * conj (S t) + S t * conj (S' t)) t := (hderiv t).mul hconjS
      have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
      have h3 : (fun u => (S u * conj (S u)).re) = fun u => ‖S u‖ ^ 2 := by
        funext u
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
      rw [← h3]
      exact h2
    set D : ℝ → ℝ := fun t => (S' t * conj (S t) + S t * conj (S' t)).re with hDdef
    have hDcont : Continuous D := by
      rw [hDdef]
      exact Complex.continuous_re.comp
        (((hS'cont.mul (continuous_star.comp hScont)).add
          (hScont.mul (continuous_star.comp hS'cont))))
    have hDbound : ∀ u : ℝ, |D u| ≤ ‖S u‖ ^ 2 + ‖S' u‖ ^ 2 := by
      intro u
      rw [hDdef]
      calc |(S' u * conj (S u) + S u * conj (S' u)).re|
          ≤ ‖S' u * conj (S u) + S u * conj (S' u)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖S' u * conj (S u)‖ + ‖S u * conj (S' u)‖ := norm_add_le _ _
        _ = ‖S' u‖ * ‖S u‖ + ‖S u‖ * ‖S' u‖ := by
            rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
        _ ≤ ‖S u‖ ^ 2 + ‖S' u‖ ^ 2 := by nlinarith [sq_nonneg (‖S u‖ - ‖S' u‖)]
    -- pointwise Sobolev bound at each r ∈ R
    have hpoint : ∀ r ∈ R, ‖S r‖ ^ 2
        ≤ ∫ u in (r - 1/2)..(r + 1/2), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2) := by
      intro r _
      have hCr : ∀ v ∈ Set.Icc (r - 1/2) (r + 1/2),
          ‖S r‖ ^ 2 ≤ ‖S v‖ ^ 2 + ∫ u in (r - 1/2)..(r + 1/2), |D u| := by
        intro v hv
        have hftc : (∫ u in v..r, D u) = ‖S r‖ ^ 2 - ‖S v‖ ^ 2 :=
          integral_eq_sub_of_hasDerivAt (fun u _ => hFd u) (hDcont.intervalIntegrable _ _)
        have habs1 : |∫ u in v..r, D u| ≤ |(∫ u in v..r, |D u|)| := by
          have := intervalIntegral.norm_integral_le_abs_integral_norm
            (f := D) (a := v) (b := r) (μ := volume)
          simpa [Real.norm_eq_abs] using this
        have habs2 : |(∫ u in v..r, |D u|)| ≤ ∫ u in (r - 1/2)..(r + 1/2), |D u| := by
          have hsub : Set.uIoc v r ⊆ Set.uIoc (r - 1/2) (r + 1/2) := by
            rw [Set.uIoc_of_le (by linarith : r - 1/2 ≤ r + 1/2), Set.uIoc]
            refine Set.Ioc_subset_Ioc ?_ ?_
            · exact le_min hv.1 (by linarith)
            · exact max_le hv.2 (by linarith)
          have h5 := intervalIntegral.abs_integral_mono_interval hsub
            (Eventually.of_forall fun u => abs_nonneg (D u))
            (hDcont.abs.intervalIntegrable (μ := volume) _ _)
          refine h5.trans (le_of_eq (abs_of_nonneg ?_))
          exact intervalIntegral.integral_nonneg (by linarith) fun u _ => abs_nonneg _
        have := habs1.trans habs2
        have h4 : ‖S r‖ ^ 2 - ‖S v‖ ^ 2 ≤ |∫ u in v..r, D u| := by
          rw [hftc] at *
          exact le_abs_self _
        linarith [h4.trans this]
      have hlen : (∫ v in (r - 1/2)..(r + 1/2), ‖S r‖ ^ 2) = ‖S r‖ ^ 2 := by
        rw [intervalIntegral.integral_const]
        norm_num
      have hmono : (∫ v in (r - 1/2)..(r + 1/2), ‖S r‖ ^ 2)
          ≤ ∫ v in (r - 1/2)..(r + 1/2),
              (‖S v‖ ^ 2 + ∫ u in (r - 1/2)..(r + 1/2), |D u|) := by
        refine integral_mono_on (by linarith) (intervalIntegrable_const)
          ((hSsq.add continuous_const).intervalIntegrable _ _) hCr
      have hsplit : (∫ v in (r - 1/2)..(r + 1/2),
            (‖S v‖ ^ 2 + ∫ u in (r - 1/2)..(r + 1/2), |D u|))
          = (∫ v in (r - 1/2)..(r + 1/2), ‖S v‖ ^ 2)
            + ∫ u in (r - 1/2)..(r + 1/2), |D u| := by
        rw [intervalIntegral.integral_add (hSsq.intervalIntegrable _ _)
          intervalIntegrable_const, intervalIntegral.integral_const]
        norm_num
      have hDle : (∫ u in (r - 1/2)..(r + 1/2), |D u|)
          ≤ ∫ u in (r - 1/2)..(r + 1/2), (‖S u‖ ^ 2 + ‖S' u‖ ^ 2) := by
        refine integral_mono_on (by linarith) (hDcont.abs.intervalIntegrable _ _)
          ((by fun_prop : Continuous fun u : ℝ => ‖S u‖ ^ 2 + ‖S' u‖ ^ 2).intervalIntegrable _ _)
          fun u _ => hDbound u
      have hfin : (∫ u in (r - 1/2)..(r + 1/2), (‖S u‖ ^ 2 + (‖S u‖ ^ 2 + ‖S' u‖ ^ 2)))
          = ∫ u in (r - 1/2)..(r + 1/2), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2) := by
        refine intervalIntegral.integral_congr fun u _ => ?_
        ring
      have hSS' : Continuous fun u : ℝ => ‖S u‖ ^ 2 + ‖S' u‖ ^ 2 := by fun_prop
      have hcomb : (∫ v in (r - 1/2)..(r + 1/2), ‖S v‖ ^ 2)
            + (∫ u in (r - 1/2)..(r + 1/2), (‖S u‖ ^ 2 + ‖S' u‖ ^ 2))
          = ∫ u in (r - 1/2)..(r + 1/2), (‖S u‖ ^ 2 + (‖S u‖ ^ 2 + ‖S' u‖ ^ 2)) := by
        rw [intervalIntegral.integral_add (hSsq.intervalIntegrable _ _)
          (hSS'.intervalIntegrable _ _)]
      calc ‖S r‖ ^ 2 = ∫ v in (r - 1/2)..(r + 1/2), ‖S r‖ ^ 2 := hlen.symm
        _ ≤ (∫ v in (r - 1/2)..(r + 1/2), ‖S v‖ ^ 2)
            + ∫ u in (r - 1/2)..(r + 1/2), |D u| := hmono.trans (le_of_eq hsplit)
        _ ≤ (∫ v in (r - 1/2)..(r + 1/2), ‖S v‖ ^ 2)
            + ∫ u in (r - 1/2)..(r + 1/2), (‖S u‖ ^ 2 + ‖S' u‖ ^ 2) := by linarith
        _ = ∫ u in (r - 1/2)..(r + 1/2), (‖S u‖ ^ 2 + (‖S u‖ ^ 2 + ‖S' u‖ ^ 2)) := hcomb
        _ = ∫ u in (r - 1/2)..(r + 1/2), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2) := hfin
    -- sum the disjoint windows
    have hh : Continuous fun u : ℝ => 2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2 :=
      (continuous_const.mul hSsq).add hS'sq
    have hh0 : ∀ u : ℝ, 0 ≤ 2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2 := fun u => by positivity
    have hsum_r : (∑ r ∈ R, ∫ u in (r - 1/2)..(r + 1/2), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2))
        ≤ ∫ u in (-(T + 1))..(T + 1), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2) := by
      have hIoc : ∀ r ∈ R, (∫ u in (r - 1/2)..(r + 1/2), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2))
          = ∫ u in Set.Ioc (r - 1/2) (r + 1/2), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2) :=
        fun r _ => integral_of_le (by linarith)
      rw [Finset.sum_congr rfl hIoc]
      have hdisj : Set.Pairwise ↑R
          (Function.onFun Disjoint fun r : ℝ => Set.Ioc (r - 1/2) (r + 1/2)) := by
        intro r hr r' hr' hne
        have hsep' := hsep r hr r' hr' hne
        simp only [Function.onFun]
        rw [Set.Ioc_disjoint_Ioc]
        rcases abs_cases (r - r') with ⟨h1, _⟩ | ⟨h1, _⟩
        · calc min (r + 1/2) (r' + 1/2) ≤ r' + 1/2 := min_le_right _ _
            _ ≤ r - 1/2 := by linarith
            _ ≤ max (r - 1/2) (r' - 1/2) := le_max_left _ _
        · calc min (r + 1/2) (r' + 1/2) ≤ r + 1/2 := min_le_left _ _
            _ ≤ r' - 1/2 := by linarith
            _ ≤ max (r - 1/2) (r' - 1/2) := le_max_right _ _
      rw [← MeasureTheory.integral_biUnion_finset R (fun r _ => measurableSet_Ioc) hdisj
        (fun r _ => hh.integrableOn_Ioc)]
      rw [integral_of_le (by linarith : -(T + 1) ≤ T + 1)]
      refine setIntegral_mono_set hh.integrableOn_Ioc
        (Eventually.of_forall fun u => hh0 u) ?_
      refine LE.le.eventuallyLE ?_
      refine Set.iUnion₂_subset fun r hr => ?_
      have hrT := abs_le.1 (hRT r hr)
      exact Set.Ioc_subset_Ioc (by linarith [hrT.1]) (by linarith [hrT.2])
    have hsplit2 : (∫ u in (-(T + 1))..(T + 1), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2))
        = 2 * (∫ u in (-(T + 1))..(T + 1), ‖S u‖ ^ 2)
          + ∫ u in (-(T + 1))..(T + 1), ‖S' u‖ ^ 2 := by
      rw [intervalIntegral.integral_add
        ((by fun_prop : Continuous fun u : ℝ => 2 * ‖S u‖ ^ 2).intervalIntegrable _ _)
        (hS'sq.intervalIntegrable _ _),
        intervalIntegral.integral_const_mul]
    calc (∑ r ∈ R, ‖S r‖ ^ 2)
        ≤ ∑ r ∈ R, ∫ u in (r - 1/2)..(r + 1/2), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2) :=
          Finset.sum_le_sum hpoint
      _ ≤ ∫ u in (-(T + 1))..(T + 1), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2) := hsum_r
      _ = 2 * (∫ u in (-(T + 1))..(T + 1), ‖S u‖ ^ 2)
            + ∫ u in (-(T + 1))..(T + 1), ‖S' u‖ ^ 2 := hsplit2
  -- sum over characters and apply the mean value theorem twice
  have hMV1 := mean_value_chars d hd (T + 1) hT1 N a
  have hMV2 := mean_value_chars d hd (T + 1) hT1 N
    (fun n => a n * ((-Real.log n : ℝ) : ℂ) * Complex.I)
  have hnorm2 : (∑ n ∈ Finset.Icc 1 N, ‖a n * ((-Real.log n : ℝ) : ℂ) * Complex.I‖ ^ 2)
      = ∑ n ∈ Finset.Icc 1 N, Real.log n ^ 2 * ‖a n‖ ^ 2 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  rw [hnorm2] at hMV2
  have hC0 : (0 : ℝ) ≤ (N : ℝ) + d * (T + 1) := by positivity
  have hA0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  have hB0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, Real.log n ^ 2 * ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  have hexpand : (∑ n ∈ Finset.Icc 1 N, (1 + Real.log n ^ 2) * ‖a n‖ ^ 2)
      = (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)
        + ∑ n ∈ Finset.Icc 1 N, Real.log n ^ 2 * ‖a n‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  calc (∑ χ : DirichletCharacter ℂ d, ∑ r ∈ R, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * r : ℝ) * Complex.I)‖ ^ 2)
      ≤ ∑ χ : DirichletCharacter ℂ d,
          (2 * (∫ t in (-(T + 1))..(T + 1), ‖∑ n ∈ Finset.Icc 1 N,
              a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2)
            + ∫ t in (-(T + 1))..(T + 1), ‖∑ n ∈ Finset.Icc 1 N,
                (a n * ((-Real.log n : ℝ) : ℂ) * Complex.I) * χ (n : ZMod d) *
                  Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2) :=
        Finset.sum_le_sum fun χ _ => hper χ
    _ = 2 * (∑ χ : DirichletCharacter ℂ d, ∫ t in (-(T + 1))..(T + 1),
            ‖∑ n ∈ Finset.Icc 1 N,
              a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2)
        + ∑ χ : DirichletCharacter ℂ d, ∫ t in (-(T + 1))..(T + 1),
            ‖∑ n ∈ Finset.Icc 1 N,
              (a n * ((-Real.log n : ℝ) : ℂ) * Complex.I) * χ (n : ZMod d) *
                Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 2 * (100 * ((N : ℝ) + d * (T + 1)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)
        + 100 * ((N : ℝ) + d * (T + 1)) *
            ∑ n ∈ Finset.Icc 1 N, Real.log n ^ 2 * ‖a n‖ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hMV1 (by norm_num)) hMV2
    _ ≤ 200 * ((N : ℝ) + d * (T + 1)) *
          ∑ n ∈ Finset.Icc 1 N, (1 + Real.log n ^ 2) * ‖a n‖ ^ 2 := by
        rw [hexpand]
        nlinarith [mul_nonneg hC0 hB0, mul_nonneg hC0 hA0]

end MeanValue
end Carmichael
