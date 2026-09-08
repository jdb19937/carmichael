/-
Route Z, interface I5 of routez/Z0b-density.md §2: the classical de la Vallée
Poussin zero-free region for the Riemann zeta function.  No `sorry`, no `axiom`,
no `native_decide`.

STATEMENTS (public interface in namespace `Carmichael`; the engine lemmas and the
numerals `zfK`, `zfE` in `Carmichael.ZetaZeroFree`).
 * `zeta_zero_free_region : ∃ c, 0 < c ∧ c ≤ 1/2 ∧
     ∀ s, 1 − c / log(|Im s| + 3) ≤ Re s → ζ s ≠ 0`  (the frozen I5 display).
 * `zeta_zero_re_lt : ∃ c, 0 < c ∧ c ≤ 1/2 ∧
     ∀ ρ, ζ ρ = 0 → Re ρ < 1 − c / log(|Im ρ| + 3)`  (the form §9 band (b) consumes).
 * `zeta_zero_free_region_and_zero_re_lt` — both clauses with one common `c`.
 * `LFunction_modOne_zero_free_region` — the same for
   `DirichletCharacter.LFunction (χ : DirichletCharacter ℂ 1)` via `LFunction_modOne_eq`.
 * `ZetaZeroFree.zeta_zero_re_le_of_two_le_abs_im (ρ) (hρ : ζ ρ = 0) (ht : 2 ≤ |Im ρ|)
     (hβ : 3/8 ≤ Re ρ) : Re ρ ≤ 1 − zfE / log(|Im ρ| + 2)` — the effective
   high-height statement, `zfE = 1/(7·zfK)`, `zfK = 12·520000 + 112 = 6240112`.

ROUTE (the 3-4-1 argument).  For `σ = 1 + w`, `0 < w ≤ 1/20`, and every real `t`,
 `0 ≤ 3·Re(−ζ′/ζ)(σ) + 4·Re(−ζ′/ζ)(σ+it) + Re(−ζ′/ζ)(σ+2it)`
since `−ζ′/ζ = ∑ Λ(n) n^{−s}` there and `3 + 4cos θ + cos 2θ = 2(1+cos θ)² ≥ 0`
(`re_LSeries_vonMangoldt_comb_nonneg`).  The three real parts are bounded by
 * `Re(−ζ′/ζ)(σ) ≤ 1/w + 2` (`SmallDiskZeroCount.norm_logDeriv_le_of_re_eq` at
   modulus `1`);
 * `Re(−ζ′/ζ)(σ+it) ≤ 520000·log(|t|+2) + 10 − 1/(σ−β)` when `β + it` is a zero
   with `3/8 ≤ β`, `|t| ≥ 2`, and `≤ 520000·log(|t|+2) + 10` in general
   (`re_LSeries_vonMangoldt_le_sub_zeros`).  This is the Landau input, obtained
   from the generic expansion `EF.norm_logDeriv_sub_sum_diskZeros_le` for the
   Abel-summed eta function `η = g·ζ`, `g(s) = 1 − 2^{1−s}`, on `EF.diskData_etaFun`.
   The zeros of `g` at `s_k = 1 + 2πik/log 2` are zeros of `η` and enter the
   Landau sum; the matching pole of `g′/g = log 2/(e^{v} − 1)`,
   `v = (s − s_k)·log 2`, is cancelled against them:
   `Re g′/g(s₀) ≤ Re 1/(s₀ − s_k) + 10` when `s_k` lies in the Landau disk
   (`re_gFun_logDeriv_le`), and `Re g′/g(s₀) ≤ 0` otherwise.  Every other zero
   term `Re m_ρ/(s₀−ρ) ≥ 0` is dropped.
Then `w := 1/(zfK·log(|t|+2))` gives `β ≤ 1 − 1/(7·zfK·log(|t|+2))`, and the
low-height box `|t| ≤ 2` is `ZetaBox.zeta_box_clearance` (ineffective `σ₁`), so
`c := min (zfE, (1−σ₁)·log 3, 1/2)`.

DELTAS.  The blueprint says "port of PNT+ `StrongPNT`"; the argument is the same
3-4-1 inequality, but the Landau input is this campaign's eta-function expansion
(no `ζ` growth bound on `Re s ≥ 1/4` is available here), which forces the
`g′/g` pole-cancellation above.  The constant `c` is ineffective only through
`σ₁` (the low-height box); the high-height constant `zfE` is an explicit numeral.
-/
import Carmichael.SmallDiskZeroCount
import Carmichael.ExplicitFormula
import Carmichael.ZetaBox
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false

namespace Carmichael
namespace ZetaZeroFree

open Complex Finset Metric
open ArithmeticFunction (vonMangoldt)
open scoped Classical LSeries.notation ArithmeticFunction

noncomputable section

/-! ### §A  The 3-4-1 inequality for `−ζ′/ζ = ∑ Λ(n) n^{−s}` -/

/-- Real part of the `n`-th von Mangoldt term at `σ + it`: `Λ(n) n^{−σ} cos(t log n)`. -/
lemma re_term_vonMangoldt (σ t : ℝ) (n : ℕ) :
    (LSeries.term ↗Λ ((σ : ℂ) + t * I) n).re
      = vonMangoldt n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn.ne']
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log, div_eq_mul_inv,
      ← Complex.exp_neg]
    have harg : -((Real.log n : ℂ) * ((σ : ℂ) + t * I))
        = ((Real.log n * (-σ) : ℝ) : ℂ) + ((-(t * Real.log n) : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [harg, Complex.exp_add, ← Complex.ofReal_exp, ← mul_assoc, ← Complex.ofReal_mul,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg,
      Real.rpow_def_of_pos hnr]

/-- `Re(−ζ′/ζ)(σ+it) = ∑ Λ(n) n^{−σ} cos(t log n)` for `σ > 1`, as a real series. -/
lemma re_LSeries_vonMangoldt (σ t : ℝ) (hσ : 1 < σ) :
    (LSeries ↗Λ ((σ : ℂ) + t * I)).re
      = ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n) := by
  have hs : 1 < ((σ : ℂ) + t * I).re := by simp [hσ]
  rw [LSeries, Complex.re_tsum (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)]
  exact tsum_congr (fun n => re_term_vonMangoldt σ t n)

/-- Summability of the real cosine series. -/
lemma summable_re_term_vonMangoldt (σ t : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => vonMangoldt n * (n : ℝ) ^ (-σ) * Real.cos (t * Real.log n)) := by
  have hs : 1 < ((σ : ℂ) + t * I).re := by simp [hσ]
  have h := (Complex.hasSum_re
    (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).hasSum).summable
  refine h.congr (fun n => ?_)
  exact re_term_vonMangoldt σ t n

/-- **The 3-4-1 inequality.** For `σ > 1` and every real `t`,
`0 ≤ 3·Re(−ζ′/ζ)(σ) + 4·Re(−ζ′/ζ)(σ+it) + Re(−ζ′/ζ)(σ+2it)`. -/
theorem re_LSeries_vonMangoldt_comb_nonneg (σ t : ℝ) (hσ : 1 < σ) :
    0 ≤ 3 * (LSeries ↗Λ ((σ : ℂ) + (0 : ℝ) * I)).re
        + 4 * (LSeries ↗Λ ((σ : ℂ) + t * I)).re
        + (LSeries ↗Λ ((σ : ℂ) + (2 * t : ℝ) * I)).re := by
  rw [re_LSeries_vonMangoldt σ 0 hσ, re_LSeries_vonMangoldt σ t hσ,
    re_LSeries_vonMangoldt σ (2 * t) hσ]
  have h0 := (summable_re_term_vonMangoldt σ 0 hσ).mul_left 3
  have h1 := (summable_re_term_vonMangoldt σ t hσ).mul_left 4
  have h2 := summable_re_term_vonMangoldt σ (2 * t) hσ
  rw [← tsum_mul_left, ← tsum_mul_left, ← h0.tsum_add h1, ← (h0.add h1).tsum_add h2]
  refine tsum_nonneg (fun n => ?_)
  have hΛ : 0 ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  have hpow : 0 ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hc : Real.cos (2 * t * Real.log n) = 2 * Real.cos (t * Real.log n) ^ 2 - 1 := by
    rw [mul_assoc, Real.cos_two_mul]
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [hc]
  have hsq : 0 ≤ (1 + Real.cos (t * Real.log n)) ^ 2 := sq_nonneg _
  have hprod : 0 ≤ vonMangoldt n * (n : ℝ) ^ (-σ) := mul_nonneg hΛ hpow
  nlinarith [mul_nonneg hprod hsq]

/-! ### §B  The `σ`-line bound `Re(−ζ′/ζ)(1+w) ≤ 1/w + 2` -/

/-- `−ζ′/ζ` as the von Mangoldt `L`-series, real part form. -/
lemma re_LSeries_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) :
    (LSeries ↗Λ s).re = -(deriv riemannZeta s / riemannZeta s).re := by
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_div,
    Complex.neg_re]

/-- `Re(−ζ′/ζ)(1+w) ≤ 1/w + 2` for `0 < w ≤ 1/20`. -/
lemma re_LSeries_vonMangoldt_line_le {w : ℝ} (hw0 : 0 < w) (hw : w ≤ 1/20) :
    (LSeries ↗Λ (((1 + w : ℝ) : ℂ) + (0 : ℝ) * I)).re ≤ 1 / w + 2 := by
  have hre : (((1 + w : ℝ) : ℂ) + (0 : ℝ) * I).re = 1 + w := by simp
  have hs : 1 < (((1 + w : ℝ) : ℂ) + (0 : ℝ) * I).re := by rw [hre]; linarith
  rw [re_LSeries_vonMangoldt_eq hs]
  have h := norm_logDeriv_le_of_re_eq (χ := (1 : DirichletCharacter ℂ 1)) hw0 hw hre
  rw [DirichletCharacter.LFunction_modOne_eq] at h
  have habs := Complex.abs_re_le_norm
    (deriv riemannZeta (((1 + w : ℝ) : ℂ) + (0 : ℝ) * I)
      / riemannZeta (((1 + w : ℝ) : ℂ) + (0 : ℝ) * I))
  have := (abs_le.mp (le_trans habs h)).1
  linarith


/-! ### §C  The correction factor `g(s) = 1 − 2^{1−s}` near its zeros `s_k` -/

/-- The zeros of `g`: `s_k = 1 + 2πik/log 2`. -/
def sK (k : ℤ) : ℂ := 1 + ((2 * Real.pi * k / Real.log 2 : ℝ) : ℂ) * I

lemma sK_re (k : ℤ) : (sK k).re = 1 := by
  simp only [sK, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re]
  ring

lemma sK_im (k : ℤ) : (sK k).im = 2 * Real.pi * k / Real.log 2 := by
  simp only [sK, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_im]
  ring

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

lemma log_two_ne_zero' : (Real.log 2 : ℂ) ≠ 0 := by exact_mod_cast log_two_pos.ne'

/-- `2^{1−s} = exp((1 − s)·log 2)`. -/
lemma two_cpow_eq_exp (s : ℂ) :
    (2:ℂ) ^ ((1:ℂ) - s) = cexp (((1:ℂ) - s) * (Real.log 2 : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0)]
  congr 1
  rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ← Complex.ofReal_log (by norm_num : (0:ℝ) ≤ 2)]
  ring

/-- `exp((s_k − 1)·log 2) = 1`. -/
lemma exp_sK_sub_one (k : ℤ) : cexp ((sK k - 1) * (Real.log 2 : ℂ)) = 1 := by
  have hl := log_two_ne_zero'
  have h : (sK k - 1) * (Real.log 2 : ℂ) = (k : ℂ) * (2 * Real.pi * I) := by
    simp only [sK]
    push_cast
    field_simp
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

lemma gFun_sK (k : ℤ) : EF.gFun (sK k) = 0 := by
  unfold EF.gFun
  rw [two_cpow_eq_exp, sub_eq_zero,
    show ((1:ℂ) - sK k) * (Real.log 2 : ℂ) = -((sK k - 1) * (Real.log 2 : ℂ)) by ring,
    Complex.exp_neg, exp_sK_sub_one, inv_one]

lemma sK_ne_one {k : ℤ} (hk : k ≠ 0) : sK k ≠ 1 := by
  intro h
  have him : (sK k).im = 0 := by rw [h]; simp
  rw [sK_im, div_eq_zero_iff] at him
  rcases him with h1 | h1
  · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have : (2 * Real.pi) * (k : ℝ) = 0 := h1
    rcases mul_eq_zero.mp this with h2 | h2
    · linarith [Real.pi_pos]
    · exact hk' h2
  · exact log_two_pos.ne' h1

lemma etaFun_sK {k : ℤ} (hk : k ≠ 0) : etaFun (sK k) = 0 := by
  rw [EF.etaFun_eq_mul (by rw [sK_re]; norm_num) (sK_ne_one hk), gFun_sK, zero_mul]

lemma riemannZeta_sK_ne_zero (k : ℤ) : riemannZeta (sK k) ≠ 0 :=
  riemannZeta_ne_zero_of_one_le_re (by rw [sK_re])

/-- `g′/g(s) = log 2 / (e^{v} − 1)` with `v = (s − s_k)·log 2`, for every `k`
(periodicity), whenever `g(s) ≠ 0`. -/
lemma logDeriv_gFun_eq (s : ℂ) (k : ℤ) (hg : EF.gFun s ≠ 0) :
    deriv EF.gFun s / EF.gFun s
      = (Real.log 2 : ℂ) / (cexp ((s - sK k) * (Real.log 2 : ℂ)) - 1) := by
  have hE : cexp ((s - sK k) * (Real.log 2 : ℂ))
      = (cexp (((1:ℂ) - s) * (Real.log 2 : ℂ)))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← Complex.exp_add,
      show (s - sK k) * (Real.log 2 : ℂ) + ((1:ℂ) - s) * (Real.log 2 : ℂ)
        = -((sK k - 1) * (Real.log 2 : ℂ)) by ring,
      Complex.exp_neg, exp_sK_sub_one, inv_one]
  have hg' : EF.gFun s = 1 - cexp (((1:ℂ) - s) * (Real.log 2 : ℂ)) := by
    unfold EF.gFun; rw [two_cpow_eq_exp]
  rw [EF.deriv_gFun, two_cpow_eq_exp, hE]
  rw [hg'] at hg ⊢
  set E := cexp (((1:ℂ) - s) * (Real.log 2 : ℂ)) with hEdef
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have hE1 : E⁻¹ - 1 ≠ 0 := by
    intro h
    apply hg
    have h1 : E⁻¹ = 1 := by linear_combination h
    rw [inv_eq_one] at h1
    rw [h1, sub_self]
  field_simp

/-- `‖1/(e^v − 1) − 1/v‖ ≤ 10` for `v ≠ 0`, `‖v‖ ≤ 9/10`. -/
lemma norm_inv_exp_sub_one_sub_inv_le {v : ℂ} (hv0 : v ≠ 0) (hv : ‖v‖ ≤ 9/10) :
    ‖1 / (cexp v - 1) - 1 / v‖ ≤ 10 := by
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have h1 : ‖cexp v - 1 - v‖ ≤ ‖v‖ ^ 2 :=
    Complex.norm_exp_sub_one_sub_id_le (by linarith)
  have h2 : ‖v‖ / 10 ≤ ‖cexp v - 1‖ := by
    have h3 := norm_sub_norm_le v (cexp v - 1)
    rw [norm_sub_rev v (cexp v - 1)] at h3
    nlinarith
  have hne : cexp v - 1 ≠ 0 := by
    intro h
    rw [h, norm_zero] at h2
    linarith
  rw [div_sub_div _ _ hne hv0, one_mul, mul_one, norm_div, norm_mul,
    norm_sub_rev v (cexp v - 1), div_le_iff₀ (mul_pos (by linarith) hnv)]
  nlinarith

/-- `Re 1/(e^v − 1) ≤ Re 1/v + 10` for `v ≠ 0`, `‖v‖ ≤ 9/10`. -/
lemma re_inv_exp_sub_one_le {v : ℂ} (hv0 : v ≠ 0) (hv : ‖v‖ ≤ 9/10) :
    (1 / (cexp v - 1)).re ≤ (1 / v).re + 10 := by
  have h := norm_inv_exp_sub_one_sub_inv_le hv0 hv
  have h2 := Complex.abs_re_le_norm (1 / (cexp v - 1) - 1 / v)
  rw [Complex.sub_re] at h2
  linarith [(abs_le.mp (le_trans h2 h)).2]

/-- `Re 1/(e^v − 1) ≤ 0` when `0 ≤ Re v ≤ 1/20` and `0.887 ≤ |Im v| ≤ π`. -/
lemma re_inv_exp_sub_one_nonpos {v : ℂ} (hre0 : 0 ≤ v.re) (hre : v.re ≤ 1/20)
    (him : 887/1000 ≤ |v.im|) (him' : |v.im| ≤ Real.pi) :
    (1 / (cexp v - 1)).re ≤ 0 := by
  rw [one_div, Complex.inv_re]
  apply div_nonpos_of_nonpos_of_nonneg _ (Complex.normSq_nonneg _)
  rw [Complex.sub_re, Complex.exp_re, Complex.one_re]
  have hcos : Real.cos v.im ≤ 64/100 := by
    have hmono : Real.cos |v.im| ≤ Real.cos (887/1000) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num) him' him
    have hb := Real.cos_bound (x := 887/1000)
      (by rw [abs_of_pos (by norm_num)]; norm_num)
    rw [abs_of_pos (by norm_num : (0:ℝ) < 887/1000)] at hb
    have h1 := (abs_le.mp hb).2
    have h2 : Real.cos (887/1000) ≤ 64/100 := by norm_num at h1; linarith
    rw [Real.cos_abs] at hmono
    linarith
  have hexp : Real.exp v.re ≤ 1 + 1/20 + (1/20)^2 := by
    have hb := Real.abs_exp_sub_one_sub_id_le (x := v.re)
      (by rw [abs_of_nonneg hre0]; linarith)
    have := (abs_le.mp hb).2
    nlinarith
  have hexp0 : 0 < Real.exp v.re := Real.exp_pos _
  nlinarith

/-- Multiplicity at least one: `η` vanishes at an analytic point of `Re > 0`. -/
lemma one_le_analyticOrderNatAt_etaFun {ρ : ℂ} (hρ : 0 < ρ.re)
    (han : AnalyticAt ℂ etaFun ρ) (hz : etaFun ρ = 0) :
    1 ≤ analyticOrderNatAt etaFun ρ := by
  rw [Nat.one_le_iff_ne_zero]
  intro h
  unfold analyticOrderNatAt at h
  rcases ENat.toNat_eq_zero.mp h with h0 | htop
  · exact (analyticOrderAt_ne_zero.mpr ⟨han, hz⟩) h0
  · exact analyticOrderAt_etaFun_ne_top hρ htop

/-- `Re (1/z) ≤ Re (m/z)` for `1 ≤ m` and `Re z ≥ 0`. -/
lemma re_one_div_le_re_natCast_div {m : ℕ} (hm : 1 ≤ m) {z : ℂ} (hz : 0 ≤ z.re) :
    (1 / z).re ≤ ((m : ℂ) / z).re := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hm
  push_cast
  rw [add_div, Complex.add_re]
  linarith [Census.re_natCast_div_nonneg (m := j) hz]

/-- Every `η`-zero in a Landau disk has real part `≤ 1`. -/
lemma re_le_one_of_mem_diskZeros {t : ℝ} {ρ : ℂ} (hρ : ρ ∈ EF.diskZeros etaFun t) :
    ρ.re ≤ 1 := by
  by_contra hcon
  push Not at hcon
  exact EF.diskData_etaFun.nz ρ hcon ((EF.mem_diskZeros EF.diskData_etaFun).mp hρ).2

/-- The zero terms of the Landau sum at `s₀ = (1+w) + it` are nonnegative. -/
lemma re_term_nonneg {t w : ℝ} (hw0 : 0 < w) {ρ : ℂ} (hρ : ρ ∈ EF.diskZeros etaFun t) :
    0 ≤ ((analyticOrderNatAt etaFun ρ : ℂ) / ((((1 + w : ℝ) : ℂ) + t * I) - ρ)).re := by
  apply Census.re_natCast_div_nonneg
  have h1 : ((((1 + w : ℝ) : ℂ) + t * I) - ρ).re = 1 + w - ρ.re := by simp
  rw [h1]
  linarith [re_le_one_of_mem_diskZeros hρ]

/-- **Pole cancellation for `g′/g`.**  At `s₀ = (1+w) + it`, `0 < w ≤ 1/20`, `|t| ≥ 2`:
either `Re g′/g(s₀) ≤ 10 + Re 1/(s₀ − s_k)` with `s_k` a `g`-zero in the Landau disk
(an `η`-zero which is not a `ζ`-zero), or `Re g′/g(s₀) ≤ 0`.  Packaged as
`∃ X, Re g′/g(s₀) ≤ 10 + X ∧ X ≤ ∑_{ρ ∈ DZ(η,t), ζ ρ ≠ 0} Re m_ρ/(s₀ − ρ)`. -/
lemma re_gFun_logDeriv_le {t w : ℝ} (ht : 2 ≤ |t|) (hw0 : 0 < w) (hw : w ≤ 1/20) :
    ∃ X : ℝ,
      (deriv EF.gFun (((1 + w : ℝ) : ℂ) + t * I)
          / EF.gFun (((1 + w : ℝ) : ℂ) + t * I)).re ≤ 10 + X ∧
      X ≤ ∑ ρ ∈ (EF.diskZeros etaFun t).filter (fun ρ => ¬ riemannZeta ρ = 0),
            ((analyticOrderNatAt etaFun ρ : ℂ) / ((((1 + w : ℝ) : ℂ) + t * I) - ρ)).re := by
  have hDD := EF.diskData_etaFun
  set s₀ : ℂ := ((1 + w : ℝ) : ℂ) + t * I with hs₀
  have hre : s₀.re = 1 + w := by simp [hs₀]
  have him : s₀.im = t := by simp [hs₀]
  have hs1 : 1 < s₀.re := by rw [hre]; linarith
  have hl2 := log_two_pos
  have hl2' : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hl2'' : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hπ := Real.pi_pos
  -- `g(s₀) ≠ 0` since `η(s₀) = g(s₀) ζ(s₀) ≠ 0`
  have hg : EF.gFun s₀ ≠ 0 := by
    intro h
    have hη := hDD.nz s₀ hs1
    apply hη
    rw [EF.etaFun_eq_mul (by linarith) (by intro h1; rw [h1, Complex.one_re] at hs1; linarith),
      h, zero_mul]
  -- the nearest period: `k = round(t log 2 / 2π)`, `φ = t log 2 − 2πk ∈ [−π, π]`
  set k : ℤ := round (t * Real.log 2 / (2 * Real.pi)) with hk
  set φ : ℝ := t * Real.log 2 - 2 * Real.pi * k with hφ
  have hφπ : |φ| ≤ Real.pi := by
    have h := abs_sub_round (t * Real.log 2 / (2 * Real.pi))
    have hφ' : φ = 2 * Real.pi * (t * Real.log 2 / (2 * Real.pi) - k) := by
      rw [hφ]; field_simp
    rw [hφ', abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
    nlinarith
  -- `v = (s₀ − s_k) log 2 = w log 2 + iφ`
  set v : ℂ := (s₀ - sK k) * (Real.log 2 : ℂ) with hv
  have hvre : v.re = w * Real.log 2 := by
    rw [hv, Complex.mul_re, Complex.sub_re, Complex.sub_im, hre, him, sK_re, sK_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hvim : v.im = φ := by
    rw [hv, hφ, Complex.mul_im, Complex.sub_re, Complex.sub_im, hre, him, sK_re, sK_im,
      Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring
  have hvre0 : 0 < v.re := by rw [hvre]; positivity
  have hv0 : v ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hvre0; exact lt_irrefl _ hvre0
  have hvre1 : v.re ≤ 1/20 := by rw [hvre]; nlinarith
  -- `Re g′/g(s₀) = log 2 · Re 1/(e^v − 1)`
  have hlog : (deriv EF.gFun s₀ / EF.gFun s₀).re
      = Real.log 2 * (1 / (cexp v - 1)).re := by
    rw [logDeriv_gFun_eq s₀ k hg, div_eq_mul_one_div, Complex.re_ofReal_mul]
  have hnn : ∀ ρ ∈ (EF.diskZeros etaFun t).filter (fun ρ => ¬ riemannZeta ρ = 0),
      0 ≤ ((analyticOrderNatAt etaFun ρ : ℂ) / (s₀ - ρ)).re := by
    intro ρ hρ
    exact re_term_nonneg hw0 (Finset.mem_filter.mp hρ).1
  by_cases hA : φ ^ 2 ≤ 105/64 * Real.log 2 ^ 2
  · -- Case A: `s_k` lies in the Landau disk; cancel its pole.
    have hk0 : k ≠ 0 := by
      intro hk0
      have hφt : φ = t * Real.log 2 := by rw [hφ, hk0]; simp
      have ht2 : 4 ≤ t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
      rw [hφt] at hA
      nlinarith [sq_nonneg (Real.log 2)]
    have hφ' : φ = (t - 2 * Real.pi * k / Real.log 2) * Real.log 2 := by
      rw [hφ]; field_simp
    have hdist : (t - 2 * Real.pi * k / Real.log 2) ^ 2 ≤ 105/64 := by
      rw [hφ', mul_pow] at hA
      have hl2sq : 0 < Real.log 2 ^ 2 := by positivity
      nlinarith
    have hball : sK k ∈ closedBall ((2:ℂ) + t * I) (13/8 : ℝ) := by
      rw [mem_closedBall, Complex.dist_eq]
      have hns : Complex.normSq (sK k - ((2:ℂ) + t * I)) ≤ (13/8) ^ 2 := by
        rw [Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, sK_re, sK_im, Complex.add_re, Complex.add_im,
          Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
        nlinarith
      rw [Complex.normSq_eq_norm_sq] at hns
      nlinarith [norm_nonneg (sK k - ((2:ℂ) + t * I))]
    have hmemDZ : sK k ∈ EF.diskZeros etaFun t :=
      (EF.mem_diskZeros hDD).mpr ⟨hball, etaFun_sK hk0⟩
    have hmemF : sK k ∈ (EF.diskZeros etaFun t).filter (fun ρ => ¬ riemannZeta ρ = 0) :=
      Finset.mem_filter.mpr ⟨hmemDZ, riemannZeta_sK_ne_zero k⟩
    have han : AnalyticAt ℂ etaFun (sK k) :=
      hDD.diff t (sK k) (closedBall_subset_closedBall (by norm_num) hball)
    have hm : 1 ≤ analyticOrderNatAt etaFun (sK k) :=
      one_le_analyticOrderNatAt_etaFun (by rw [sK_re]; norm_num) han (etaFun_sK hk0)
    have hre_sub : (s₀ - sK k).re = w := by rw [Complex.sub_re, hre, sK_re]; ring
    refine ⟨(1 / (s₀ - sK k)).re, ?_, ?_⟩
    · -- `Re g′/g ≤ 10 + Re 1/(s₀ − s_k)`
      have hnorm : ‖v‖ ≤ 9/10 := by
        have hns : Complex.normSq v = v.re * v.re + v.im * v.im := Complex.normSq_apply v
        rw [Complex.normSq_eq_norm_sq, hvre, hvim] at hns
        nlinarith [norm_nonneg v, sq_nonneg (Real.log 2)]
      have h1 := re_inv_exp_sub_one_le hv0 hnorm
      have h2 : Real.log 2 * (1 / v).re = (1 / (s₀ - sK k)).re := by
        rw [← Complex.re_ofReal_mul, hv]
        congr 1
        have hl := log_two_ne_zero'
        have hs : s₀ - sK k ≠ 0 := by
          intro h; rw [h, Complex.zero_re] at hre_sub; linarith
        field_simp
      rw [hlog]
      nlinarith
    · -- `Re 1/(s₀ − s_k) ≤ Re m_k/(s₀ − s_k) ≤ ∑`
      calc (1 / (s₀ - sK k)).re
          ≤ ((analyticOrderNatAt etaFun (sK k) : ℂ) / (s₀ - sK k)).re :=
            re_one_div_le_re_natCast_div hm (by rw [hre_sub]; exact hw0.le)
        _ ≤ _ := Finset.single_le_sum hnn hmemF
  · -- Case B: no `g`-zero nearby; `Re g′/g ≤ 0`.
    push Not at hA
    have hφabs : 887/1000 ≤ |φ| := by
      by_contra hcon
      push Not at hcon
      have h1 : φ ^ 2 < (887/1000) ^ 2 := by
        rw [← sq_abs φ]
        exact pow_lt_pow_left₀ hcon (abs_nonneg φ) two_ne_zero
      nlinarith
    have h0 := re_inv_exp_sub_one_nonpos hvre0.le hvre1 (by rw [hvim]; exact hφabs)
      (by rw [hvim]; exact hφπ)
    refine ⟨0, ?_, Finset.sum_nonneg hnn⟩
    rw [hlog]
    nlinarith

/-! ### §D  The Landau input at `s₀ = (1+w) + it` -/

/-- **Landau input.**  For `0 < w ≤ 1/20` and `|t| ≥ 2`,
`Re(−ζ′/ζ)((1+w) + it) ≤ 520000·log(|t|+2) + 10 − ∑_{ζ ρ = 0, ρ ∈ DZ(η,t)} Re m_ρ/(s₀−ρ)`. -/
theorem re_LSeries_vonMangoldt_le_sub_zeros {t w : ℝ} (ht : 2 ≤ |t|) (hw0 : 0 < w)
    (hw : w ≤ 1/20) :
    (LSeries ↗Λ (((1 + w : ℝ) : ℂ) + t * I)).re
      ≤ 520000 * Real.log (|t| + 2) + 10
        - ∑ ρ ∈ (EF.diskZeros etaFun t).filter (fun ρ => riemannZeta ρ = 0),
            ((analyticOrderNatAt etaFun ρ : ℂ) / ((((1 + w : ℝ) : ℂ) + t * I) - ρ)).re := by
  have hDD := EF.diskData_etaFun
  set s₀ : ℂ := ((1 + w : ℝ) : ℂ) + t * I with hs₀
  have hre : s₀.re = 1 + w := by simp [hs₀]
  have hs1 : 1 < s₀.re := by rw [hre]; linarith
  rw [re_LSeries_vonMangoldt_eq hs1]
  have hsplit := EF.logDeriv_eta_split hs1
  have hmem : s₀ ∈ closedBall ((2:ℂ) + t * I) (3/2 : ℝ) := by
    rw [mem_closedBall, Complex.dist_eq]
    have : s₀ - ((2:ℂ) + t * I) = ((1 + w - 2 : ℝ) : ℂ) := by rw [hs₀]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hη0 : etaFun s₀ ≠ 0 := hDD.nz s₀ hs1
  have hpf := EF.norm_logDeriv_sub_sum_diskZeros_le hDD t hmem hη0
  rw [one_mul] at hpf
  obtain ⟨X, hX1, hX2⟩ := re_gFun_logDeriv_le ht hw0 hw
  have hRe : (deriv riemannZeta s₀ / riemannZeta s₀).re
      = (deriv etaFun s₀ / etaFun s₀).re - (deriv EF.gFun s₀ / EF.gFun s₀).re := by
    rw [hsplit, Complex.add_re]; ring
  have hη : (∑ ρ ∈ EF.diskZeros etaFun t,
        ((analyticOrderNatAt etaFun ρ : ℂ) / (s₀ - ρ))).re - 520000 * Real.log (|t| + 2)
      ≤ (deriv etaFun s₀ / etaFun s₀).re := by
    have habs := Complex.abs_re_le_norm (deriv etaFun s₀ / etaFun s₀
      - ∑ ρ ∈ EF.diskZeros etaFun t, (analyticOrderNatAt etaFun ρ : ℂ) / (s₀ - ρ))
    rw [Complex.sub_re] at habs
    linarith [(abs_le.mp (le_trans habs hpf)).1]
  rw [Complex.re_sum, ← Finset.sum_filter_add_sum_filter_not (EF.diskZeros etaFun t)
    (fun ρ => riemannZeta ρ = 0)] at hη
  linarith

/-- The Landau input with the zero sum dropped. -/
theorem re_LSeries_vonMangoldt_le {t w : ℝ} (ht : 2 ≤ |t|) (hw0 : 0 < w) (hw : w ≤ 1/20) :
    (LSeries ↗Λ (((1 + w : ℝ) : ℂ) + t * I)).re ≤ 520000 * Real.log (|t| + 2) + 10 := by
  have h := re_LSeries_vonMangoldt_le_sub_zeros ht hw0 hw
  have hnn : 0 ≤ ∑ ρ ∈ (EF.diskZeros etaFun t).filter (fun ρ => riemannZeta ρ = 0),
      ((analyticOrderNatAt etaFun ρ : ℂ) / ((((1 + w : ℝ) : ℂ) + t * I) - ρ)).re :=
    Finset.sum_nonneg (fun ρ hρ => re_term_nonneg hw0 (Finset.mem_filter.mp hρ).1)
  linarith

/-- The Landau input with one zero `β + it` (`3/8 ≤ β ≤ 1`) retained:
`Re(−ζ′/ζ)((1+w) + it) ≤ 520000·log(|t|+2) + 10 − 1/(1 + w − β)`. -/
theorem re_LSeries_vonMangoldt_le_of_zero {t w : ℝ} (ht : 2 ≤ |t|) (hw0 : 0 < w)
    (hw : w ≤ 1/20) {β : ℝ} (hβ : 3/8 ≤ β) (hβ1 : β ≤ 1)
    (hz : riemannZeta ((β : ℂ) + t * I) = 0) :
    (LSeries ↗Λ (((1 + w : ℝ) : ℂ) + t * I)).re
      ≤ 520000 * Real.log (|t| + 2) + 10 - 1 / (1 + w - β) := by
  have hDD := EF.diskData_etaFun
  have h := re_LSeries_vonMangoldt_le_sub_zeros ht hw0 hw
  set ρ₀ : ℂ := (β : ℂ) + t * I with hρ₀
  have hρre : ρ₀.re = β := by simp [hρ₀]
  have hρ1 : ρ₀ ≠ 1 := by
    intro h1; rw [h1] at hz; exact riemannZeta_one_ne_zero hz
  have hη : etaFun ρ₀ = 0 := by
    rw [EF.etaFun_eq_mul (by rw [hρre]; linarith) hρ1, hz, mul_zero]
  have hball : ρ₀ ∈ closedBall ((2:ℂ) + t * I) (13/8 : ℝ) := by
    rw [mem_closedBall, Complex.dist_eq]
    have : ρ₀ - ((2:ℂ) + t * I) = ((β - 2 : ℝ) : ℂ) := by rw [hρ₀]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hmemDZ : ρ₀ ∈ EF.diskZeros etaFun t := (EF.mem_diskZeros hDD).mpr ⟨hball, hη⟩
  have hmemF : ρ₀ ∈ (EF.diskZeros etaFun t).filter (fun ρ => riemannZeta ρ = 0) :=
    Finset.mem_filter.mpr ⟨hmemDZ, hz⟩
  have han : AnalyticAt ℂ etaFun ρ₀ :=
    hDD.diff t ρ₀ (closedBall_subset_closedBall (by norm_num) hball)
  have hm : 1 ≤ analyticOrderNatAt etaFun ρ₀ :=
    one_le_analyticOrderNatAt_etaFun (by rw [hρre]; linarith) han hη
  have hsub : (((1 + w : ℝ) : ℂ) + t * I) - ρ₀ = ((1 + w - β : ℝ) : ℂ) := by
    rw [hρ₀]; push_cast; ring
  have hr : 0 < 1 + w - β := by linarith
  have hterm : 1 / (1 + w - β)
      ≤ ((analyticOrderNatAt etaFun ρ₀ : ℂ) / ((((1 + w : ℝ) : ℂ) + t * I) - ρ₀)).re := by
    rw [hsub, ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re]
    apply div_le_div_of_nonneg_right _ hr.le
    exact_mod_cast hm
  have hsum := Finset.single_le_sum
    (fun ρ hρ => re_term_nonneg hw0 (t := t) (w := w) (Finset.mem_filter.mp hρ).1) hmemF
  linarith

/-! ### §E  Assembly: the effective high-height region and the box -/

/-- `zfK = 12·520000 + 112`: the reciprocal scale of `w = 1/(zfK·log(|t|+2))`. -/
def zfK : ℝ := 6240112

/-- `zfE = 1/(7·zfK)`: the effective zero-free constant at height `|t| ≥ 2`. -/
def zfE : ℝ := 1 / (7 * zfK)

lemma zfK_eq : zfK = 6240112 := rfl

lemma zfK_pos : 0 < zfK := by rw [zfK_eq]; norm_num

lemma zfE_pos : 0 < zfE := by unfold zfE; have := zfK_pos; positivity

/-- `1 ≤ log(|t| + 2)` for `|t| ≥ 2` (as `log 4 = 2 log 2 > 1`). -/
lemma one_le_log_abs_add_two {t : ℝ} (ht : 2 ≤ |t|) : 1 ≤ Real.log (|t| + 2) := by
  have h4 : Real.log 4 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by linarith)
  have h2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  have := Real.log_two_gt_d9
  linarith

/-- `log(|2t| + 2) ≤ 2 log(|t| + 2)`. -/
lemma log_two_mul_le {t : ℝ} : Real.log (|2 * t| + 2) ≤ 2 * Real.log (|t| + 2) := by
  have h0 : 0 ≤ |t| := abs_nonneg t
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have h1 : Real.log (2 * |t| + 2) ≤ Real.log ((|t| + 2) ^ 2) :=
    Real.log_le_log (by linarith) (by nlinarith)
  rw [Real.log_pow] at h1
  push_cast at h1
  linarith

/-- **Effective high-height zero-free region.**  Every zero `ρ` of `ζ` with
`|Im ρ| ≥ 2` and `Re ρ ≥ 3/8` satisfies `Re ρ ≤ 1 − zfE / log(|Im ρ| + 2)`. -/
theorem zeta_zero_re_le_of_two_le_abs_im (ρ : ℂ) (hρ : riemannZeta ρ = 0)
    (ht : 2 ≤ |ρ.im|) (hβ : 3/8 ≤ ρ.re) :
    ρ.re ≤ 1 - zfE / Real.log (|ρ.im| + 2) := by
  have hz : riemannZeta ((ρ.re : ℂ) + ρ.im * I) = 0 := by rw [Complex.re_add_im]; exact hρ
  have hβ1 : ρ.re < 1 := by
    by_contra h
    push Not at h
    exact riemannZeta_ne_zero_of_one_le_re h hρ
  set t := ρ.im with htdef
  set β := ρ.re with hβdef
  set Lg := Real.log (|t| + 2) with hL
  have hL1 : 1 ≤ Lg := one_le_log_abs_add_two ht
  have hK := zfK_pos
  have hKL : 0 < zfK * Lg := by positivity
  set w := 1 / (zfK * Lg) with hw
  have hw0 : 0 < w := by positivity
  have hwK : w * (zfK * Lg) = 1 := by rw [hw]; field_simp
  have hw20 : w ≤ 1/20 := by
    rw [hw, div_le_div_iff₀ hKL (by norm_num : (0:ℝ) < 20)]
    rw [zfK_eq] at hKL ⊢
    nlinarith
  have h341 := re_LSeries_vonMangoldt_comb_nonneg (1 + w) t (by linarith)
  have hS0 := re_LSeries_vonMangoldt_line_le hw0 hw20
  have hS1 := re_LSeries_vonMangoldt_le_of_zero ht hw0 hw20 hβ hβ1.le hz
  have ht2 : 2 ≤ |2 * t| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
  have hS2 := re_LSeries_vonMangoldt_le ht2 hw0 hw20
  have hL2 : Real.log (|2 * t| + 2) ≤ 2 * Lg := log_two_mul_le
  have hr : 0 < 1 + w - β := by linarith
  have hinvw : 1 / w = zfK * Lg := by rw [hw]; field_simp
  rw [← hL] at hS1
  -- `4/(1 + w − β) ≤ 3/w + 6·520000·Lg + 56 ≤ (7/2)·zfK·Lg`
  have key : 4 * (1 / (1 + w - β)) ≤ 3 * (1 / w) + 3120000 * Lg + 56 := by linarith
  rw [hinvw] at key
  have key2 : 4 * (1 / (1 + w - β)) ≤ 7/2 * zfK * Lg := by
    rw [zfK_eq] at key ⊢; linarith
  have h4 : 4 ≤ (1 + w - β) * (7/2 * zfK * Lg) := by
    rw [mul_one_div, div_le_iff₀ hr] at key2
    calc (4:ℝ) ≤ 7/2 * zfK * Lg * (1 + w - β) := key2
      _ = (1 + w - β) * (7/2 * zfK * Lg) := by ring
  -- multiply by `w = 1/(zfK Lg)`: `4w ≤ (7/2)(1 + w − β)`, so `β ≤ 1 − w/7`
  have h5 : 4 * w ≤ 7/2 * (1 + w - β) := by
    have := mul_le_mul_of_nonneg_right h4 hw0.le
    have h6 : (1 + w - β) * (7/2 * zfK * Lg) * w = 7/2 * (1 + w - β) * (w * (zfK * Lg)) := by
      ring
    rw [h6, hwK, mul_one] at this
    linarith
  have hK' : zfK ≠ 0 := hK.ne'
  have hLg' : Lg ≠ 0 := (by linarith : (0:ℝ) < Lg).ne'
  have hE : zfE / Lg = w / 7 := by
    rw [zfE, hw]
    field_simp
  rw [hE]
  linarith


end

end ZetaZeroFree

open ZetaZeroFree

/-! ### The public interface (namespace `Carmichael`) -/

/-- **I5 (ζ zero-free region), both clauses with one common constant.** -/
theorem zeta_zero_free_region_and_zero_re_lt :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1/2 ∧
      (∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → riemannZeta s ≠ 0) ∧
      (∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re < 1 - c / Real.log (|ρ.im| + 3)) := by
  obtain ⟨σ₁, hσ₁, hbox⟩ := zeta_box_clearance 2 (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set c := min (min zfE ((1 - σ₁) * Real.log 3)) (1/2) with hc
  have hc0 : 0 < c := lt_min (lt_min zfE_pos (mul_pos (by linarith) hlog3)) (by norm_num)
  have hcE : c ≤ zfE := le_trans (min_le_left _ _) (min_le_left _ _)
  have hcσ : c ≤ (1 - σ₁) * Real.log 3 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc2 : c ≤ 1/2 := min_le_right _ _
  have main : ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → riemannZeta s ≠ 0 := by
    intro s hs hz
    have h0 : 0 ≤ |s.im| := abs_nonneg s.im
    have hlog : Real.log 3 ≤ Real.log (|s.im| + 3) :=
      Real.log_le_log (by norm_num) (by linarith)
    have hlogpos : 0 < Real.log (|s.im| + 3) := lt_of_lt_of_le hlog3 hlog
    have hsre1 : s.re < 1 := by
      by_contra h
      push Not at h
      exact riemannZeta_ne_zero_of_one_le_re h hz
    rcases le_or_gt |s.im| 2 with h2 | h2
    · -- low height: the box clearance
      have hcl : c / Real.log (|s.im| + 3) ≤ 1 - σ₁ := by
        rw [div_le_iff₀ hlogpos]
        calc c ≤ (1 - σ₁) * Real.log 3 := hcσ
          _ ≤ (1 - σ₁) * Real.log (|s.im| + 3) :=
            mul_le_mul_of_nonneg_left hlog (by linarith)
      exact hbox s (by linarith) hsre1.le h2 hz
    · -- high height: the effective region
      have hlog1 : 1 ≤ Real.log (|s.im| + 3) := by
        have := one_le_log_abs_add_two h2.le
        have h' : Real.log (|s.im| + 2) ≤ Real.log (|s.im| + 3) :=
          Real.log_le_log (by linarith) (by linarith)
        linarith
      have hβ : 3/8 ≤ s.re := by
        have hcl : c / Real.log (|s.im| + 3) ≤ 1/2 := by
          rw [div_le_iff₀ hlogpos]; nlinarith
        linarith
      have hE := zeta_zero_re_le_of_two_le_abs_im s hz h2.le hβ
      have hlt : c / Real.log (|s.im| + 3) < zfE / Real.log (|s.im| + 2) := by
        have hlog2pos : 0 < Real.log (|s.im| + 2) := by
          linarith [one_le_log_abs_add_two h2.le]
        have hll : Real.log (|s.im| + 2) < Real.log (|s.im| + 3) :=
          Real.log_lt_log (by linarith) (by linarith)
        rw [div_lt_div_iff₀ hlogpos hlog2pos]
        nlinarith [zfE_pos]
      linarith
  refine ⟨c, hc0, hc2, main, fun ρ hρ => ?_⟩
  by_contra h
  push Not at h
  exact main ρ h hρ

/-- **I5 (ζ zero-free region).** There is `c ∈ (0, 1/2]` such that `ζ(s) ≠ 0`
whenever `Re s ≥ 1 − c / log(|Im s| + 3)`. -/
theorem zeta_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1/2 ∧
      ∀ s : ℂ, 1 - c / Real.log (|s.im| + 3) ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨c, h0, h2, h, _⟩ := zeta_zero_free_region_and_zero_re_lt
  exact ⟨c, h0, h2, h⟩

/-- **I5, zero form (§9 band (b)).** There is `c ∈ (0, 1/2]` such that every zero
`ρ` of `ζ` has `Re ρ < 1 − c / log(|Im ρ| + 3)`. -/
theorem zeta_zero_re_lt :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1/2 ∧
      ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ.re < 1 - c / Real.log (|ρ.im| + 3) := by
  obtain ⟨c, h0, h2, _, h⟩ := zeta_zero_free_region_and_zero_re_lt
  exact ⟨c, h0, h2, h⟩

/-- **Conductor-1 bridge.**  The zero-free region for the Dirichlet L-function of
any (necessarily trivial) character mod 1, via `LFunction_modOne_eq`. -/
theorem LFunction_modOne_zero_free_region :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1/2 ∧
      ∀ (χ : DirichletCharacter ℂ 1) (s : ℂ),
        1 - c / Real.log (|s.im| + 3) ≤ s.re → DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨c, h0, h2, h⟩ := zeta_zero_free_region
  refine ⟨c, h0, h2, fun χ s hs => ?_⟩
  rw [DirichletCharacter.LFunction_modOne_eq]
  exact h s hs

end Carmichael
