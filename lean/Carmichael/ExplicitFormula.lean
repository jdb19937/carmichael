/-
Route Z, sortie Z5 (file 2 of 2): the truncated explicit formula for Dirichlet
L-functions, at the frozen ledger interface (routez/Z0a-ledger.md §2/§7).

MAIN RESULT (`explicit_formula`): for `χ mod N` with `χ ≠ 1 ∨ N = 1`
(this covers every primitive character, and more), `y ≥ max N 100`, `T ≥ 2`:

  ‖ψ(y,χ) − δ_χ·y + ∑_{ρ ∈ zeroFinset χ (1/2) T} ord(ρ)·y^ρ/ρ‖
    ≤ C₅·( y·log²(N·T·y)/T + y^{5/8}·log²(N·(T+2)) + log²(N·T·y) )

with `ψ(y,χ) = ∑_{n ≤ y} Λ(n)·χ(n)`, `δ_χ = 1` iff `χ = 1` (so `N = 1`, the
Riemann-zeta case), the zero sum over the distinct zeros of `L(·,χ)` in
`[1/2,1] × [−T,T]` (minus the point `1`) with multiplicity
`analyticOrderNatAt`, and `C₅ = 10^12`.

ARCHITECTURE (no functional equation, no trivial zeros, no `s = 0`):
* Series side: sharp-cutoff Perron with `Carmichael.PerronKernel` at
  `c = 1 + 1/log y`, summed against `−L′/L = ∑ Λ(n)χ(n)n^{−s}` (Mathlib
  `LSeries_twist_vonMangoldt_eq`); the near-diagonal pays `log²(Ty)` into the
  first and third error terms.
* Contour side: rectangle `[σ₁, c] × [−t₁, t₂]` with `t₁, t₂ ∈ [T, T+1]`
  pigeonholed good lines (zero-spacing census, mirroring Z4c) and
  `σ₁ ∈ [9/16, 5/8]` pigeonholed by a measure-average against the
  `|σ−β|^{−1/2}` majorant of the Z4c disk decomposition.  The rectangle is
  split into height-≤1 strips, each inside a `13/8`-disk where the generic
  factorization `f = P·h` (mirroring Z4c, made generic in `f`) turns
  `log-deriv · y^s/s` into explicitly integrable pieces; residues are
  collected by `PerronKernel.rectInt_cauchy` applied to the entire numerator
  `y^s` via `1/(s(s−ρ)) = (1/ρ)(1/(s−ρ) − 1/s)`.
* Zeros with `1/2 ≤ β ≤ σ₁` and `T < |γ| ≤ t_i` are estimated trivially
  against the disk zero-counts — this is what the `y^{5/8}` room buys.
* The `χ = 1` (ζ) case runs the same machinery on the Abel-summed eta
  function `etaFun` of `Carmichael.ZeroCount` and the elementary factor
  `g(s) = 1 − 2^{1−s}`: `ζ′/ζ = η′/η − g′/g`, the spurious `g`-zeros on
  `Re = 1` cancel between the two zero sums, and the `g`-zero at `s = 1`
  delivers the main term `y`.
-/
import Carmichael.PerronKernel
import Carmichael.PartialFractions
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

namespace Carmichael

open Complex Finset Set Metric intervalIntegral MeasureTheory Filter
open scoped Real Topology Interval

namespace EF

/-! ### Elementary real estimates -/

section Elementary

/-- Division is monotone in the numerator. -/
lemma div_le_div_right_of_pos {a b T : ℝ} (hT : 0 < T) (h : a ≤ b) :
    a / T ≤ b / T := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (by positivity)

/-- Triangle inequality for sums (name-stable local form). -/
lemma abs_add' (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  have h := abs_sub a (-b)
  simpa using h

/-- Harmonic sum bound: `∑_{j<M} 1/(j+1) ≤ 1 + log M`. -/
lemma harmonic_le (M : ℕ) :
    ∑ j ∈ Finset.range M, (1 : ℝ) / (j + 1) ≤ 1 + Real.log M := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ]
      rcases Nat.eq_zero_or_pos M with rfl | hM
      · norm_num
      have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      have hstep : (1 : ℝ) / (M + 1) ≤ Real.log (M + 1) - Real.log M := by
        have hpos : (0 : ℝ) < (M : ℝ) := by linarith
        have hpos2 : (0 : ℝ) < (M + 1 : ℝ) := by linarith
        have h1 : Real.log ((M : ℝ) / (M + 1)) ≤ (M : ℝ) / (M + 1) - 1 :=
          Real.log_le_sub_one_of_pos (by positivity)
        have h2 : Real.log ((M : ℝ) / (M + 1))
            = Real.log M - Real.log (M + 1) :=
          Real.log_div hpos.ne' hpos2.ne'
        have h3 : (M : ℝ) / (M + 1) - 1 = -(1 / (M + 1)) := by
          field_simp
          ring
        rw [h2, h3] at h1
        linarith
      have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

/-- `log x ≤ (2/δ)·x^(δ/2)` for `x ≥ 1`, `δ > 0`. -/
lemma log_le_rpow_div {x δ : ℝ} (hx : 1 ≤ x) (hδ : 0 < δ) :
    Real.log x ≤ (2 / δ) * x ^ (δ / 2) := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have h1 : Real.log (x ^ (δ / 2)) ≤ x ^ (δ / 2) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 _)
  rw [Real.log_rpow hx0] at h1
  have h2 : (0 : ℝ) < x ^ (δ / 2) := Real.rpow_pos_of_pos hx0 _
  have h3 : Real.log x ≤ (x ^ (δ / 2) - 1) * (2 / δ) := by
    have := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ 2 / δ)
    calc Real.log x = δ / 2 * Real.log x * (2 / δ) := by field_simp
      _ ≤ (x ^ (δ / 2) - 1) * (2 / δ) := this
  have h4 : (x ^ (δ / 2) - 1) * (2 / δ) = (2 / δ) * x ^ (δ / 2) - 2 / δ := by ring
  have h5 : (0:ℝ) < 2 / δ := by positivity
  linarith

/-- The weighted zeta tail: `∑' n, Λ(n)·n^{−c} ≤ 6/(c−1)²` for `1 < c ≤ 2`. -/
lemma tsum_vonMangoldt_rpow_le {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 2) :
    ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c) ≤ 6 / (c - 1) ^ 2 := by
  set δ : ℝ := c - 1 with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; linarith
  have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith
  -- termwise majorant
  have hterm : ∀ n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)
      ≤ (2 / δ) * (n : ℝ) ^ (-δ / 2 - 1) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [ArithmeticFunction.map_zero, zero_mul, Nat.cast_zero]
      positivity
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
      have h1 : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
        ArithmeticFunction.vonMangoldt_le_log
      have h2 : Real.log n ≤ (2 / δ) * (n : ℝ) ^ (δ / 2) := log_le_rpow_div hn1 hδ0
      have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-c) := Real.rpow_nonneg hn0.le _
      calc ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)
          ≤ (2 / δ) * (n : ℝ) ^ (δ / 2) * (n : ℝ) ^ (-c) := by
            apply mul_le_mul_of_nonneg_right (le_trans h1 h2) h3
        _ = (2 / δ) * (n : ℝ) ^ (δ / 2 - c) := by
            rw [mul_assoc, ← Real.rpow_add hn0]
            ring_nf
        _ ≤ (2 / δ) * (n : ℝ) ^ (-δ / 2 - 1) := by
            have : δ / 2 - c = -δ / 2 - 1 := by rw [hδdef]; ring
            rw [this]
  -- summability of the majorant
  have hsummaj : Summable (fun n : ℕ => (2 / δ) * (n : ℝ) ^ (-δ / 2 - 1)) := by
    apply Summable.mul_left
    apply Real.summable_nat_rpow.mpr
    linarith
  have hsum : Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)) := by
    apply Summable.of_nonneg_of_le (fun n => ?_) hterm hsummaj
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  -- the rpow tail bound
  have htail : ∑' n : ℕ, (n : ℝ) ^ (-δ / 2 - 1) ≤ 1 + 2 / δ := by
    have h1 : ∀ K : ℕ, ∑ k ∈ Finset.range K, (k : ℝ) ^ (-(δ / 2) - 1) ≤ 1 + 1 / (δ / 2) :=
      fun K => sum_range_rpow_le (by positivity) K
    have h2 : ∀ K : ℕ, ∑ k ∈ Finset.range K, (k : ℝ) ^ (-δ / 2 - 1) ≤ 1 + 2 / δ := by
      intro K
      have := h1 K
      have he : (-(δ / 2) - 1 : ℝ) = -δ / 2 - 1 := by ring
      have he2 : 1 + 1 / (δ / 2) = 1 + 2 / δ := by
        rw [div_div_eq_mul_div]; norm_num
      rw [he, he2] at this
      exact this
    exact Real.tsum_le_of_sum_range_le
      (fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _) h2
  calc ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)
      ≤ ∑' n : ℕ, (2 / δ) * (n : ℝ) ^ (-δ / 2 - 1) := hsum.tsum_le_tsum hterm hsummaj
    _ = (2 / δ) * ∑' n : ℕ, (n : ℝ) ^ (-δ / 2 - 1) := tsum_mul_left
    _ ≤ (2 / δ) * (1 + 2 / δ) := by
        apply mul_le_mul_of_nonneg_left htail (by positivity)
    _ ≤ (2 / δ) * (3 / δ) := by
        have hle : (1 : ℝ) + 2 / δ ≤ 3 / δ := by
          rw [← sub_nonneg]
          have : 3 / δ - (1 + 2 / δ) = (1 - δ) / δ := by field_simp; ring
          rw [this]
          positivity
        apply mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 6 / δ ^ 2 := by field_simp; ring
    _ = 6 / (c - 1) ^ 2 := by rw [hδdef]

/-- Summability of the von-Mangoldt Dirichlet tail. -/
lemma summable_vonMangoldt_rpow {c : ℝ} (hc1 : 1 < c) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)) := by
  have hδ0 : 0 < c - 1 := by linarith
  have hterm : ∀ n : ℕ, ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)
      ≤ (2 / (c-1)) * (n : ℝ) ^ (-(c-1) / 2 - 1) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [ArithmeticFunction.map_zero, zero_mul, Nat.cast_zero]
      positivity
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
      have h1 : ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
        ArithmeticFunction.vonMangoldt_le_log
      have h2 : Real.log n ≤ (2 / (c-1)) * (n : ℝ) ^ ((c-1) / 2) := log_le_rpow_div hn1 hδ0
      have h3 : (0 : ℝ) ≤ (n : ℝ) ^ (-c) := Real.rpow_nonneg hn0.le _
      calc ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)
          ≤ (2 / (c-1)) * (n : ℝ) ^ ((c-1) / 2) * (n : ℝ) ^ (-c) := by
            apply mul_le_mul_of_nonneg_right (le_trans h1 h2) h3
        _ = (2 / (c-1)) * (n : ℝ) ^ ((c-1) / 2 - c) := by
            rw [mul_assoc, ← Real.rpow_add hn0]
            ring_nf
        _ ≤ (2 / (c-1)) * (n : ℝ) ^ (-(c-1) / 2 - 1) := by
            have : (c-1) / 2 - c = -(c-1) / 2 - 1 := by ring
            rw [this]
  apply Summable.of_nonneg_of_le (fun n => ?_) hterm
  · apply Summable.mul_left
    apply Real.summable_nat_rpow.mpr
    linarith
  · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- `y^{1 + 1/log y} = e·y` for `y ≥ 100`. -/
lemma rpow_one_add_inv_log {y : ℝ} (hy : 100 ≤ y) :
    y ^ (1 + 1 / Real.log y) = Real.exp 1 * y := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hlog : Real.log y ≠ 0 := by
    have : (1 : ℝ) < y := by linarith
    exact (Real.log_pos this).ne'
  rw [Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0,
    mul_one_div, div_self hlog]
  ring

/-- `4 ≤ log y` for `y ≥ 100`. -/
lemma four_le_log {y : ℝ} (hy : 100 ≤ y) : 4 ≤ Real.log y := by
  have h1 : Real.exp 4 ≤ 100 := by
    have h : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
    have h2 : Real.exp 4 = Real.exp 1 * Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    have h0 : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    have h3 : Real.exp 1 * Real.exp 1 ≤ 7.3984 := by nlinarith
    have h4 : (0:ℝ) ≤ Real.exp 1 * Real.exp 1 := by positivity
    nlinarith
  have := Real.log_le_log (by positivity : (0:ℝ) < Real.exp 4) (le_trans h1 hy)
  rwa [Real.log_exp] at this

end Elementary

/-! ### Interval-integral helpers: `1/(1+|t|)` and `|σ−β|^{−1/2}` -/

section IntegralHelpers

lemma continuous_one_div_one_add_abs : Continuous (fun t : ℝ => 1 / (1 + |t|)) := by
  apply Continuous.div continuous_const (continuous_const.add continuous_abs)
  intro t
  have : (0:ℝ) < 1 + |t| := by positivity
  exact this.ne'

/-- `∫_u^v dt/(1+|t|) = log(1−u) + log(1+v)` for `u ≤ 0 ≤ v`. -/
lemma integral_one_div_one_add_abs {u v : ℝ} (hu : u ≤ 0) (hv : 0 ≤ v) :
    ∫ t in u..v, 1 / (1 + |t|) = Real.log (1 - u) + Real.log (1 + v) := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun t : ℝ => 1 / (1 + |t|))
      MeasureTheory.volume a b :=
    fun a b => continuous_one_div_one_add_abs.intervalIntegrable a b
  have hsplit : (∫ t in u..(0:ℝ), 1 / (1 + |t|)) + (∫ t in (0:ℝ)..v, 1 / (1 + |t|))
      = ∫ t in u..v, 1 / (1 + |t|) :=
    intervalIntegral.integral_add_adjacent_intervals (hint u 0) (hint 0 v)
  have hleft : (∫ t in u..(0:ℝ), 1 / (1 + |t|)) = Real.log (1 - u) := by
    have hcongr : (∫ t in u..(0:ℝ), 1 / (1 + |t|))
        = ∫ t in u..(0:ℝ), 1 / (1 - t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hu] at ht
      show 1 / (1 + |t|) = 1 / (1 - t)
      rw [abs_of_nonpos ht.2]
      ring_nf
    rw [hcongr]
    have hcomp : (∫ t in u..(0:ℝ), 1 / (1 - t))
        = ∫ x in (1 - 0 : ℝ)..(1 - u), 1 / x := by
      have := intervalIntegral.integral_comp_sub_left (a := u) (b := (0:ℝ))
        (fun x : ℝ => 1 / x) 1
      simp
    rw [hcomp]
    have h0 : (0 : ℝ) ∉ [[(1 - 0 : ℝ), 1 - u]] := by
      rw [Set.mem_uIcc]
      push Not
      constructor <;> intro h <;> [linarith; linarith]
    rw [integral_one_div h0]
    norm_num
  have hright : (∫ t in (0:ℝ)..v, 1 / (1 + |t|)) = Real.log (1 + v) := by
    have hcongr : (∫ t in (0:ℝ)..v, 1 / (1 + |t|))
        = ∫ t in (0:ℝ)..v, 1 / (1 + t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hv] at ht
      show 1 / (1 + |t|) = 1 / (1 + t)
      rw [abs_of_nonneg ht.1]
    rw [hcongr]
    have hcomp : (∫ t in (0:ℝ)..v, 1 / (1 + t))
        = ∫ x in (1 + 0 : ℝ)..(1 + v), 1 / x := by
      have := intervalIntegral.integral_comp_add_left (a := (0:ℝ)) (b := v)
        (fun x : ℝ => 1 / x) 1
      simp
    rw [hcomp]
    have h0 : (0 : ℝ) ∉ [[(1 + 0 : ℝ), 1 + v]] := by
      rw [Set.mem_uIcc]
      push Not
      constructor <;> intro h <;> [linarith; linarith]
    rw [integral_one_div h0]
    norm_num
  rw [← hsplit, hleft, hright]

/-- Bound form: `∫_u^v dt/(1+|t|) ≤ 2·log(1+U)` for `−U ≤ u ≤ 0 ≤ v ≤ U`. -/
lemma integral_one_div_one_add_abs_le {u v U : ℝ} (hu : u ≤ 0) (hv : 0 ≤ v)
    (hUu : -U ≤ u) (hUv : v ≤ U) :
    ∫ t in u..v, 1 / (1 + |t|) ≤ 2 * Real.log (1 + U) := by
  have hU0 : 0 ≤ U := le_trans hv hUv
  rw [integral_one_div_one_add_abs hu hv]
  have h1 : Real.log (1 - u) ≤ Real.log (1 + U) :=
    Real.log_le_log (by linarith) (by linarith)
  have h2 : Real.log (1 + v) ≤ Real.log (1 + U) :=
    Real.log_le_log (by linarith) (by linarith)
  linarith

/-- Splitting `|x|^{−1/2}` into two junk-friendly `rpow` branches. -/
lemma abs_rpow_neg_half (x : ℝ) :
    |x| ^ (-(1:ℝ)/2) = x ^ (-(1:ℝ)/2) + (-x) ^ (-(1:ℝ)/2) := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [abs_of_neg hx]
    have h1 : x ^ (-(1:ℝ)/2) = 0 := by
      rw [Real.rpow_def_of_neg hx]
      have : Real.cos (-(1:ℝ)/2 * π) = 0 := by
        rw [show (-(1:ℝ)/2 * π) = -(π/2) by ring, Real.cos_neg, Real.cos_pi_div_two]
      rw [this, mul_zero]
    rw [h1, zero_add]
  · simp [Real.zero_rpow (by norm_num : (-(1:ℝ)/2) ≠ 0)]
  · rw [abs_of_pos hx]
    have h1 : (-x) ^ (-(1:ℝ)/2) = 0 := by
      rw [Real.rpow_def_of_neg (by linarith : -x < 0)]
      have : Real.cos (-(1:ℝ)/2 * π) = 0 := by
        rw [show (-(1:ℝ)/2 * π) = -(π/2) by ring, Real.cos_neg, Real.cos_pi_div_two]
      rw [this, mul_zero]
    rw [h1, add_zero]

/-- Interval integrability of `σ ↦ |σ−β|^{−1/2}`. -/
lemma intervalIntegrable_abs_sub_rpow (β a b : ℝ) :
    IntervalIntegrable (fun σ : ℝ => |σ - β| ^ (-(1:ℝ)/2))
      MeasureTheory.volume a b := by
  have heq : (fun σ : ℝ => |σ - β| ^ (-(1:ℝ)/2))
      = fun σ : ℝ => (σ - β) ^ (-(1:ℝ)/2) + (β - σ) ^ (-(1:ℝ)/2) := by
    funext σ
    rw [abs_rpow_neg_half (σ - β)]
    ring_nf
  rw [heq]
  apply IntervalIntegrable.add
  · have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-(1:ℝ)/2))
        MeasureTheory.volume (a - β) (b - β) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have := h1.comp_sub_right β
    simpa using this
  · have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-(1:ℝ)/2))
        MeasureTheory.volume (β - a) (β - b) :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have := h1.comp_sub_left β
    simpa using this

/-- `∫_a^b |σ−β|^{−1/2} dσ ≤ 4·D^{1/2}` whenever `a ≤ b`, `b−β ≤ D`, `β−a ≤ D`. -/
lemma integral_abs_sub_rpow_le {β a b D : ℝ} (_hab : a ≤ b) (h1 : b - β ≤ D)
    (h2 : β - a ≤ D) (hD : 0 ≤ D) :
    ∫ σ in a..b, |σ - β| ^ (-(1:ℝ)/2) ≤ 4 * D ^ ((1:ℝ)/2) := by
  have heq : (fun σ : ℝ => |σ - β| ^ (-(1:ℝ)/2))
      = fun σ : ℝ => (σ - β) ^ (-(1:ℝ)/2) + (β - σ) ^ (-(1:ℝ)/2) := by
    funext σ
    rw [abs_rpow_neg_half (σ - β)]
    ring_nf
  have hint1 : IntervalIntegrable (fun σ : ℝ => (σ - β) ^ (-(1:ℝ)/2))
      MeasureTheory.volume a b := by
    have h := (intervalIntegral.intervalIntegrable_rpow'
      (a := a - β) (b := b - β) (r := -(1:ℝ)/2) (by norm_num)).comp_sub_right β
    simpa using h
  have hint2 : IntervalIntegrable (fun σ : ℝ => (β - σ) ^ (-(1:ℝ)/2))
      MeasureTheory.volume a b := by
    have h := (intervalIntegral.intervalIntegrable_rpow'
      (a := β - a) (b := β - b) (r := -(1:ℝ)/2) (by norm_num)).comp_sub_left β
    simpa using h
  rw [heq, intervalIntegral.integral_add hint1 hint2]
  -- first piece
  have hI1 : (∫ σ in a..b, (σ - β) ^ (-(1:ℝ)/2)) ≤ 2 * D ^ ((1:ℝ)/2) := by
    have hcomp : (∫ σ in a..b, (σ - β) ^ (-(1:ℝ)/2))
        = ∫ x in (a - β)..(b - β), x ^ (-(1:ℝ)/2) := by
      have := intervalIntegral.integral_comp_sub_right (a := a) (b := b)
        (fun x : ℝ => x ^ (-(1:ℝ)/2)) β
      simpa using this
    rw [hcomp, integral_rpow (Or.inl (by norm_num))]
    have he : (-(1:ℝ)/2 + 1) = 1/2 := by norm_num
    rw [he]
    have hb : (b - β) ^ ((1:ℝ)/2) ≤ D ^ ((1:ℝ)/2) := by
      rcases le_or_gt (b - β) 0 with h | h
      · rcases lt_or_eq_of_le h with h' | h'
        · rw [Real.rpow_def_of_neg h']
          have hc : Real.cos ((1:ℝ)/2 * π) = 0 := by
            rw [show ((1:ℝ)/2 * π) = π/2 by ring, Real.cos_pi_div_two]
          rw [hc, mul_zero]
          positivity
        · rw [h', Real.zero_rpow (by norm_num)]
          positivity
      · exact Real.rpow_le_rpow h.le h1 (by norm_num)
    have ha : 0 ≤ (a - β) ^ ((1:ℝ)/2) := by
      rcases le_or_gt (a - β) 0 with h | h
      · rcases lt_or_eq_of_le h with h' | h'
        · rw [Real.rpow_def_of_neg h']
          have hc : Real.cos ((1:ℝ)/2 * π) = 0 := by
            rw [show ((1:ℝ)/2 * π) = π/2 by ring, Real.cos_pi_div_two]
          rw [hc, mul_zero]
        · rw [h', Real.zero_rpow (by norm_num)]
      · positivity
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1/2)] at *
    nlinarith [hb, ha]
  -- second piece
  have hI2 : (∫ σ in a..b, (β - σ) ^ (-(1:ℝ)/2)) ≤ 2 * D ^ ((1:ℝ)/2) := by
    have hcomp : (∫ σ in a..b, (β - σ) ^ (-(1:ℝ)/2))
        = ∫ x in (β - b)..(β - a), x ^ (-(1:ℝ)/2) := by
      have := intervalIntegral.integral_comp_sub_left (a := a) (b := b)
        (fun x : ℝ => x ^ (-(1:ℝ)/2)) β
      simpa using this
    rw [hcomp, integral_rpow (Or.inl (by norm_num))]
    have he : (-(1:ℝ)/2 + 1) = 1/2 := by norm_num
    rw [he]
    have hb : (β - a) ^ ((1:ℝ)/2) ≤ D ^ ((1:ℝ)/2) := by
      rcases le_or_gt (β - a) 0 with h | h
      · rcases lt_or_eq_of_le h with h' | h'
        · rw [Real.rpow_def_of_neg h']
          have hc : Real.cos ((1:ℝ)/2 * π) = 0 := by
            rw [show ((1:ℝ)/2 * π) = π/2 by ring, Real.cos_pi_div_two]
          rw [hc, mul_zero]
          positivity
        · rw [h', Real.zero_rpow (by norm_num)]
          positivity
      · exact Real.rpow_le_rpow h.le h2 (by norm_num)
    have ha : 0 ≤ (β - b) ^ ((1:ℝ)/2) := by
      rcases le_or_gt (β - b) 0 with h | h
      · rcases lt_or_eq_of_le h with h' | h'
        · rw [Real.rpow_def_of_neg h']
          have hc : Real.cos ((1:ℝ)/2 * π) = 0 := by
            rw [show ((1:ℝ)/2 * π) = π/2 by ring, Real.cos_pi_div_two]
          rw [hc, mul_zero]
        · rw [h', Real.zero_rpow (by norm_num)]
      · positivity
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 1/2)] at *
    nlinarith [hb, ha]
  linarith

end IntegralHelpers

/-! ### The measure pigeonhole: a point below average, off a finite bad set -/

section Pigeonhole

/-- If `∫_a^b F ≤ M(b−a)` then some `σ ∈ [a,b]` outside a given finite set
has `F σ ≤ M`. -/
lemma exists_le_avg_off_finset {F : ℝ → ℝ} {a b M : ℝ} (hab : a < b)
    (hint : IntervalIntegrable F MeasureTheory.volume a b)
    (havg : ∫ σ in a..b, F σ ≤ M * (b - a)) (B : Finset ℝ) :
    ∃ σ ∈ Icc a b, σ ∉ B ∧ F σ ≤ M := by
  by_contra hcon
  push Not at hcon
  -- every point of `Ioc a b` off `B` has `M < F σ`
  have hgt : ∀ σ ∈ Ioc a b, σ ∉ B → M < F σ :=
    fun σ hσ => hcon σ (Ioc_subset_Icc_self hσ)
  set G : ℝ → ℝ := fun σ => F σ - M with hGdef
  have hGint : IntegrableOn G (Ioc a b) MeasureTheory.volume := by
    have h1 : IntegrableOn F (Ioc a b) MeasureTheory.volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hint
    exact h1.sub (integrableOn_const (C := M) (by simp))
  -- a.e. nonnegativity on `Ioc a b`
  have hBnull : MeasureTheory.volume (B : Set ℝ) = 0 :=
    (Finset.finite_toSet B).measure_zero _
  have hae : 0 ≤ᵐ[MeasureTheory.volume.restrict (Ioc a b)] G := by
    have h1 : ∀ᵐ σ ∂(MeasureTheory.volume.restrict (Ioc a b)), σ ∉ (B : Set ℝ) := by
      apply MeasureTheory.ae_restrict_of_ae
      rw [MeasureTheory.ae_iff]
      refine MeasureTheory.measure_mono_null ?_ hBnull
      intro σ hσ
      simpa using hσ
    filter_upwards [h1, MeasureTheory.ae_restrict_mem measurableSet_Ioc]
      with σ hσB hσmem
    have := hgt σ hσmem hσB
    simp only [Pi.zero_apply, hGdef]
    linarith
  -- the integral of `G` is nonpositive
  have hGle : ∫ σ in Ioc a b, G σ ≤ 0 := by
    have h1 : (∫ σ in Ioc a b, G σ) = (∫ σ in Ioc a b, F σ) - M * (b - a) := by
      rw [MeasureTheory.integral_sub
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hint)
        (integrableOn_const (C := M) (by simp))]
      congr 1
      rw [MeasureTheory.setIntegral_const, smul_eq_mul,
        MeasureTheory.measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith)]
      ring
    have h2 : (∫ σ in Ioc a b, F σ) = ∫ σ in a..b, F σ :=
      (intervalIntegral.integral_of_le hab.le).symm
    rw [h1, h2]
    linarith
  -- but its support has positive measure
  have hsupp : Ioc a b \ (B : Set ℝ) ⊆ Function.support G ∩ Ioc a b := by
    intro σ hσ
    refine ⟨?_, hσ.1⟩
    have := hgt σ hσ.1 (by simpa using hσ.2)
    simp only [Function.mem_support, hGdef]
    intro h0
    rw [sub_eq_zero] at h0
    rw [h0] at this
    exact lt_irrefl M this
  have hpos : 0 < MeasureTheory.volume (Function.support G ∩ Ioc a b) := by
    have h1 : MeasureTheory.volume (Ioc a b \ (B : Set ℝ))
        = MeasureTheory.volume (Ioc a b) := by
      apply MeasureTheory.measure_sdiff_null hBnull
    have h2 : MeasureTheory.volume (Ioc a b) = ENNReal.ofReal (b - a) := Real.volume_Ioc
    calc (0 : ENNReal) < ENNReal.ofReal (b - a) := by
          rw [ENNReal.ofReal_pos]; linarith
      _ = MeasureTheory.volume (Ioc a b \ (B : Set ℝ)) := by rw [h1, h2]
      _ ≤ MeasureTheory.volume (Function.support G ∩ Ioc a b) :=
          MeasureTheory.measure_mono hsupp
  have hGpos : 0 < ∫ σ in Ioc a b, G σ := by
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae hae hGint]
    calc (0 : ENNReal) < MeasureTheory.volume (Function.support G ∩ Ioc a b) := hpos
      _ = (MeasureTheory.volume.restrict (Ioc a b)) (Function.support G) :=
          (MeasureTheory.Measure.restrict_apply' measurableSet_Ioc).symm
  linarith

end Pigeonhole

/-! ### The series side: the Perron-weighted von Mangoldt sum -/

section SeriesSide

variable {N : ℕ}

/-- `ψ(y,χ) := ∑_{n ≤ y} Λ(n)·χ(n)` (the `n = 0` term vanishes). -/
noncomputable def psiChi (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊y⌋₊ + 1),
    (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)

/-- The sharp-cutoff Perron-weighted sum `∑ Λ(n)χ(n)·K(y/n)`. -/
noncomputable def perronSum (χ : DirichletCharacter ℂ N) (y c T : ℝ) : ℂ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
    * perronKernel (y / n) c T

/-- Far-regime kernel bound, small side. -/
lemma kernel_norm_far_small {u c T : ℝ} (hu0 : 0 < u) (hu : u ≤ 1/2)
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel u c T‖ ≤ 2 * u ^ c / T := by
  have hu1 : u < 1 := by linarith
  have h1 := norm_perronKernel_le_of_lt_one hu0 hu1 hc hT
  have hlog : (1:ℝ)/2 ≤ |Real.log u| := by
    have h2 : Real.log u ≤ Real.log (1/2) := Real.log_le_log hu0 hu
    have h3 : Real.log (1/2) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    have h4 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    rw [abs_of_neg (by rw [h3] at h2; linarith)]
    rw [h3] at h2
    linarith
  have hup : (0:ℝ) < u ^ c := Real.rpow_pos_of_pos hu0 _
  calc ‖perronKernel u c T‖ ≤ u ^ c / (T * |Real.log u|) := h1
    _ ≤ u ^ c / (T * (1/2)) := by
        apply div_le_div_of_nonneg_left hup.le (by positivity)
        apply mul_le_mul_of_nonneg_left hlog (by linarith)
    _ = 2 * u ^ c / T := by ring

/-- Far-regime kernel bound, large side. -/
lemma kernel_norm_far_big {u c T : ℝ} (hu : 2 ≤ u) (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel u c T - 1‖ ≤ 2 * u ^ c / T := by
  have hu1 : 1 < u := by linarith
  have h1 := norm_perronKernel_sub_one_le hu1 hc hT
  have hlog : (1:ℝ)/2 ≤ Real.log u := by
    have h2 : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu
    have h4 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith
  have hup : (0:ℝ) < u ^ c := Real.rpow_pos_of_pos (by linarith) _
  calc ‖perronKernel u c T - 1‖ ≤ u ^ c / (T * Real.log u) := h1
    _ ≤ u ^ c / (T * (1/2)) := by
        apply div_le_div_of_nonneg_left hup.le (by positivity)
        apply mul_le_mul_of_nonneg_left hlog (by linarith)
    _ = 2 * u ^ c / T := by ring

/-- Norm of the Perron term. -/
lemma norm_perron_term_le (χ : DirichletCharacter ℂ N) {y c T : ℝ} (n : ℕ) :
    ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
        * perronKernel (y / n) c T‖
      ≤ ArithmeticFunction.vonMangoldt n * ‖perronKernel (y / n) c T‖ := by
  rw [norm_mul, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have h1 : ‖χ (n : ZMod N)‖ ≤ 1 := χ.norm_le_one _
  have h3 : ArithmeticFunction.vonMangoldt n * ‖χ (n : ZMod N)‖
      * ‖perronKernel (y / n) c T‖
      ≤ ArithmeticFunction.vonMangoldt n * 1 * ‖perronKernel (y / n) c T‖ := by
    gcongr
  rw [mul_one] at h3
  exact h3

/-- `(y/n)^c = y^c · n^{−c}` for positive `y`, `n ≥ 1`. -/
lemma div_rpow_eq {y c : ℝ} (hy : 0 < y) {n : ℕ} (hn : 1 ≤ n) :
    (y / n) ^ c = y ^ c * (n : ℝ) ^ (-c) := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  rw [Real.div_rpow hy.le hn0.le, Real.rpow_neg hn0.le, div_eq_mul_inv]

/-- Summability of the Perron-weighted terms. -/
lemma summable_perron_term (χ : DirichletCharacter ℂ N) {y c T : ℝ}
    (hy : 100 ≤ y) (hc1 : 1 < c) (hT : 0 < T) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
      * perronKernel (y / n) c T) := by
  have hy0 : (0:ℝ) < y := by linarith
  set f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
    * perronKernel (y / n) c T with hfdef
  set R : ℕ := 2 * ⌊y⌋₊ + 2 with hRdef
  have hR2y : 2 * y ≤ (R : ℝ) := by
    have h1 : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
    have : (R : ℝ) = 2 * (⌊y⌋₊ : ℝ) + 2 := by rw [hRdef]; push_cast; ring
    rw [this]
    linarith
  suffices h : Summable (fun i : ℕ => f (i + R)) from (summable_nat_add_iff R).mp h
  apply Summable.of_norm
  have hmaj : ∀ i : ℕ, ‖f (i + R)‖
      ≤ (2 * y ^ c / T) * (ArithmeticFunction.vonMangoldt (i + R)
          * ((i + R : ℕ) : ℝ) ^ (-c)) := by
    intro i
    have hn1 : 1 ≤ i + R := by omega
    have hn0 : (0:ℝ) < ((i + R : ℕ) : ℝ) := by exact_mod_cast hn1
    have hnR : (2 : ℝ) * y ≤ ((i + R : ℕ) : ℝ) := by
      have : (R : ℝ) ≤ ((i + R : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left R i
      linarith
    have hu0 : 0 < y / ((i + R : ℕ) : ℝ) := by positivity
    have hu : y / ((i + R : ℕ) : ℝ) ≤ 1/2 := by
      refine (div_le_iff₀ hn0).mpr ?_
      linarith
    have h1 := norm_perron_term_le χ (y := y) (c := c) (T := T) (i + R)
    have h2 := kernel_norm_far_small (c := c) hu0 hu (by linarith) hT
    have h3 : (y / ((i + R : ℕ) : ℝ)) ^ c = y ^ c * ((i + R : ℕ) : ℝ) ^ (-c) :=
      div_rpow_eq hy0 hn1
    have h4 : (0:ℝ) ≤ ArithmeticFunction.vonMangoldt (i + R) :=
      ArithmeticFunction.vonMangoldt_nonneg
    calc ‖f (i + R)‖
        ≤ ArithmeticFunction.vonMangoldt (i + R)
          * ‖perronKernel (y / ((i + R : ℕ) : ℝ)) c T‖ := h1
      _ ≤ ArithmeticFunction.vonMangoldt (i + R)
          * (2 * (y / ((i + R : ℕ) : ℝ)) ^ c / T) :=
          mul_le_mul_of_nonneg_left h2 h4
      _ = (2 * y ^ c / T) * (ArithmeticFunction.vonMangoldt (i + R)
          * ((i + R : ℕ) : ℝ) ^ (-c)) := by
          rw [h3]; ring
  apply Summable.of_nonneg_of_le (fun i => norm_nonneg _) hmaj
  apply Summable.mul_left
  exact (summable_nat_add_iff R).mpr (summable_vonMangoldt_rpow hc1)

/-- Per-`n` kernel error against the sharp cutoff at `F = ⌊y⌋₊`. -/
noncomputable def kerErr (y c T : ℝ) (F : ℕ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n
    * ‖perronKernel (y / n) c T - (if n ≤ F then 1 else 0)‖

lemma kerErr_nonneg {y c T : ℝ} {F n : ℕ} : 0 ≤ kerErr y c T F n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (norm_nonneg _)

section KerErrBounds

variable {y c T : ℝ}

/-- Far-left bound: `2n ≤ ⌊y⌋₊`. -/
lemma kerErr_far_left (hy : 100 ≤ y) (hc0 : 0 < c) (hT : 0 < T) {n : ℕ}
    (hn : 2 * n ≤ ⌊y⌋₊) :
    kerErr y c T ⌊y⌋₊ n
      ≤ (2 * y ^ c / T) * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)) := by
  have hy0 : (0:ℝ) < y := by linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn1
  · simp [kerErr, ArithmeticFunction.map_zero]
  · have hnR : (n : ℝ) ≥ 1 := by exact_mod_cast hn1
    have hn0 : (0:ℝ) < (n : ℝ) := by linarith
    have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0.le
    have h2n : (2 : ℝ) * n ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hn
    have hu2 : 2 ≤ y / n := by
      rw [le_div_iff₀ hn0]
      linarith
    have hind : n ≤ ⌊y⌋₊ := by omega
    rw [kerErr, if_pos hind]
    have h1 := kernel_norm_far_big (c := c) hu2 hc0 hT
    have h3 : (y / (n : ℝ)) ^ c = y ^ c * (n : ℝ) ^ (-c) := div_rpow_eq hy0 hn1
    calc ArithmeticFunction.vonMangoldt n * ‖perronKernel (y / n) c T - 1‖
        ≤ ArithmeticFunction.vonMangoldt n * (2 * (y / (n:ℝ)) ^ c / T) :=
          mul_le_mul_of_nonneg_left h1 ArithmeticFunction.vonMangoldt_nonneg
      _ = (2 * y ^ c / T) * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)) := by
          rw [h3]; ring

/-- Far-right bound: `2y ≤ n`. -/
lemma kerErr_far_right (hy : 100 ≤ y) (hc0 : 0 < c) (hT : 0 < T) {n : ℕ}
    (hn : 2 * y ≤ (n : ℝ)) :
    kerErr y c T ⌊y⌋₊ n
      ≤ (2 * y ^ c / T) * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)) := by
  have hy0 : (0:ℝ) < y := by linarith
  have hn0 : (0:ℝ) < (n : ℝ) := by linarith
  have hn1 : 1 ≤ n := by exact_mod_cast hn0
  have hind : ¬ (n ≤ ⌊y⌋₊) := by
    intro h
    have : (n : ℝ) ≤ y := le_trans (by exact_mod_cast h) (Nat.floor_le hy0.le)
    linarith
  rw [kerErr, if_neg hind, sub_zero]
  have hu : y / (n : ℝ) ≤ 1/2 := by
    rw [div_le_iff₀ hn0]
    linarith
  have h1 := kernel_norm_far_small (c := c) (by positivity) hu hc0 hT
  have h3 : (y / (n : ℝ)) ^ c = y ^ c * (n : ℝ) ^ (-c) := div_rpow_eq hy0 hn1
  calc ArithmeticFunction.vonMangoldt n * ‖perronKernel (y / n) c T‖
      ≤ ArithmeticFunction.vonMangoldt n * (2 * (y / (n:ℝ)) ^ c / T) :=
        mul_le_mul_of_nonneg_left h1 ArithmeticFunction.vonMangoldt_nonneg
    _ = (2 * y ^ c / T) * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)) := by
        rw [h3]; ring

/-- Near-diagonal bound: `n ∈ {⌊y⌋₊, ⌊y⌋₊+1}`. -/
lemma kerErr_near (hy : 100 ≤ y) (hc1 : 1 ≤ c) (hc2 : c ≤ 2) (hT : 2 ≤ T)
    (hcT : c ≤ T) {n : ℕ} (hn : n = ⌊y⌋₊ ∨ n = ⌊y⌋₊ + 1) :
    kerErr y c T ⌊y⌋₊ n
      ≤ 3 * Real.log (2 * y) * (1 + Real.log T) := by
  have hy0 : (0:ℝ) < y := by linarith
  have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0.le
  have hfl1 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  have hfl100 : (100 : ℕ) ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnley : (n : ℝ) ≤ 2 * y := by
    rcases hn with rfl | rfl
    · linarith
    · push_cast; linarith [hfl100]
  have hu0 : 0 < y / (n : ℝ) := by positivity
  have hu2 : y / (n : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hn0]
    have : (⌊y⌋₊ : ℝ) ≥ 100 := by exact_mod_cast hfl100
    rcases hn with rfl | rfl <;> push_cast <;> nlinarith
  -- trivial kernel bound
  have hK := norm_perronKernel_le hu0 (by linarith : (0:ℝ) < c) hcT
  have hup : (y / (n:ℝ)) ^ c ≤ 4 := by
    calc (y / (n:ℝ)) ^ c ≤ 2 ^ c := Real.rpow_le_rpow hu0.le hu2 (by linarith)
      _ ≤ 2 ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two hc2
      _ = 4 := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
          norm_num
  have hlogTc : Real.log (T / c) ≤ Real.log T := by
    apply Real.log_le_log (by positivity)
    calc T / c ≤ T / 1 := by
          apply div_le_div_of_nonneg_left (by linarith) (by linarith) hc1
      _ = T := div_one T
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hπ : (3:ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hKbound : ‖perronKernel (y / n) c T‖ ≤ 2 * (1 + Real.log T) := by
    have h1 : (0:ℝ) ≤ 1 + Real.log (T / c) := by
      have := Real.log_le_log (by positivity : (0:ℝ) < T/c)
        (le_refl (T/c))
      have h2 : -1 ≤ Real.log (T / c) := by
        have h3 : (1:ℝ) ≤ T / c := by
          rw [le_div_iff₀ (by linarith)]
          linarith
        linarith [Real.log_nonneg h3]
      linarith
    calc ‖perronKernel (y / n) c T‖
        ≤ (y / (n:ℝ)) ^ c * (1 + Real.log (T / c)) / π := hK
      _ ≤ 4 * (1 + Real.log T) / 3 := by
          apply div_le_div₀ (by positivity) _ (by norm_num) hπ
          apply mul_le_mul hup (by linarith) h1 (by norm_num)
      _ ≤ 2 * (1 + Real.log T) := by
          rw [div_le_iff₀ (by norm_num : (0:ℝ) < 3)]
          nlinarith
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log (2 * y) := by
    calc ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
        ArithmeticFunction.vonMangoldt_le_log
      _ ≤ Real.log (2 * y) := Real.log_le_log hn0 hnley
  have hlog2y : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  rw [kerErr]
  have hKe : ‖perronKernel (y / n) c T - (if n ≤ ⌊y⌋₊ then 1 else 0)‖
      ≤ 2 * (1 + Real.log T) + 1 := by
    calc ‖perronKernel (y / n) c T - (if n ≤ ⌊y⌋₊ then 1 else 0)‖
        ≤ ‖perronKernel (y / n) c T‖ + ‖(if n ≤ ⌊y⌋₊ then (1:ℂ) else 0)‖ :=
          norm_sub_le _ _
      _ ≤ 2 * (1 + Real.log T) + 1 := by
          have : ‖(if n ≤ ⌊y⌋₊ then (1:ℂ) else 0)‖ ≤ 1 := by
            split <;> simp
          linarith [hKbound]
  calc ArithmeticFunction.vonMangoldt n
      * ‖perronKernel (y / n) c T - (if n ≤ ⌊y⌋₊ then 1 else 0)‖
      ≤ Real.log (2 * y) * (2 * (1 + Real.log T) + 1) := by
        apply mul_le_mul hΛ hKe (norm_nonneg _) hlog2y
    _ ≤ 3 * Real.log (2 * y) * (1 + Real.log T) := by nlinarith [hlogT0, hlog2y]

/-- Mid-left bound: `⌊y⌋₊ < 2n`, `n < ⌊y⌋₊`. -/
lemma kerErr_mid_left (hy : 100 ≤ y) (hc0 : 0 < c) (hc2 : c ≤ 2) (hT : 0 < T)
    {n : ℕ} (h2n : ⌊y⌋₊ < 2 * n) (hn : n < ⌊y⌋₊) :
    kerErr y c T ⌊y⌋₊ n
      ≤ (4 * y * Real.log (2 * y) / T) * (1 / ((⌊y⌋₊ : ℝ) - n)) := by
  have hy0 : (0:ℝ) < y := by linarith
  have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0.le
  have hfl1 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hnfl : (n : ℝ) + 1 ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hn
  have hny : (n : ℝ) < y := by linarith
  have hu1 : 1 < y / n := by
    rw [lt_div_iff₀ hn0]
    linarith
  have h2nR : (⌊y⌋₊ : ℝ) + 1 ≤ 2 * n := by exact_mod_cast h2n
  have hu2 : y / n ≤ 2 := by
    rw [div_le_iff₀ hn0]
    linarith
  have hind : n ≤ ⌊y⌋₊ := by omega
  rw [kerErr, if_pos hind]
  -- the far bound with the fine log lower bound
  have hfar := norm_perronKernel_sub_one_le hu1 hc0 hT
  have hlogu : (y - n) / y ≤ Real.log (y / n) := by
    have h1 : Real.log ((n : ℝ) / y) ≤ (n : ℝ) / y - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : Real.log ((n : ℝ) / y) = -Real.log (y / n) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    rw [h2] at h1
    have h3 : (n : ℝ) / y - 1 = -((y - n) / y) := by field_simp; ring
    rw [h3] at h1
    linarith
  have hgap : ((⌊y⌋₊ : ℝ) - n) / y ≤ (y - n) / y := by
    gcongr
  have hgap0 : (0:ℝ) < (⌊y⌋₊ : ℝ) - n := by linarith
  have hlogu0 : 0 < Real.log (y / n) := Real.log_pos hu1
  have hup : (y / (n:ℝ)) ^ c ≤ 4 := by
    calc (y / (n:ℝ)) ^ c ≤ 2 ^ c := Real.rpow_le_rpow (by positivity) hu2 hc0.le
      _ ≤ 2 ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le one_le_two hc2
      _ = 4 := by
          rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
          norm_num
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log (2 * y) := by
    calc ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
        ArithmeticFunction.vonMangoldt_le_log
      _ ≤ Real.log (2 * y) := Real.log_le_log hn0 (by linarith)
  have hlog2y : 0 ≤ Real.log (2 * y) := Real.log_nonneg (by linarith)
  have hKb : ‖perronKernel (y / n) c T - 1‖ ≤ 4 * y / (T * ((⌊y⌋₊ : ℝ) - n)) := by
    calc ‖perronKernel (y / n) c T - 1‖
        ≤ (y / (n:ℝ)) ^ c / (T * Real.log (y / n)) := hfar
      _ ≤ 4 / (T * (((⌊y⌋₊ : ℝ) - n) / y)) := by
          have hd1 : (0:ℝ) < T * (((⌊y⌋₊ : ℝ) - n) / y) :=
            mul_pos hT (div_pos hgap0 hy0)
          have hd2 : T * (((⌊y⌋₊ : ℝ) - n) / y) ≤ T * Real.log (y / n) := by
            apply mul_le_mul_of_nonneg_left _ hT.le
            linarith
          exact div_le_div₀ (by norm_num) hup hd1 hd2
      _ = 4 * y / (T * ((⌊y⌋₊ : ℝ) - n)) := by
          field_simp
  calc ArithmeticFunction.vonMangoldt n * ‖perronKernel (y / n) c T - 1‖
      ≤ Real.log (2 * y) * (4 * y / (T * ((⌊y⌋₊ : ℝ) - n))) := by
        apply mul_le_mul hΛ hKb (norm_nonneg _) hlog2y
    _ = (4 * y * Real.log (2 * y) / T) * (1 / ((⌊y⌋₊ : ℝ) - n)) := by
        field_simp

/-- Mid-right bound: `⌊y⌋₊ + 2 ≤ n`, `n ≤ 2⌊y⌋₊ + 2`. -/
lemma kerErr_mid_right (hy : 100 ≤ y) (hc0 : 0 < c) (hT : 0 < T)
    {n : ℕ} (hn : ⌊y⌋₊ + 2 ≤ n) (hnR : n ≤ 2 * ⌊y⌋₊ + 2) :
    kerErr y c T ⌊y⌋₊ n
      ≤ (3 * y * Real.log (3 * y) / T) * (1 / ((n : ℝ) - ⌊y⌋₊ - 1)) := by
  have hy0 : (0:ℝ) < y := by linarith
  have hfl : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0.le
  have hfl1 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  have hnfl : (⌊y⌋₊ : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0:ℝ) < (n : ℝ) := by linarith
  have hny : y < (n : ℝ) := by linarith
  have hn3y : (n : ℝ) ≤ 3 * y := by
    have h1 : (n : ℝ) ≤ 2 * (⌊y⌋₊ : ℝ) + 2 := by exact_mod_cast hnR
    have h100 : (100 : ℝ) ≤ (⌊y⌋₊ : ℝ) + 1 := by linarith
    nlinarith
  have hu1 : y / n < 1 := by
    rw [div_lt_one hn0]
    exact hny
  have hind : ¬ (n ≤ ⌊y⌋₊) := by omega
  rw [kerErr, if_neg hind, sub_zero]
  have hfar := norm_perronKernel_le_of_lt_one (by positivity) hu1 hc0 hT
  have hgap0 : (0:ℝ) < (n : ℝ) - ⌊y⌋₊ - 1 := by linarith
  -- `|log u| = log(n/y) ≥ (n−y)/n ≥ gap/n ≥ gap/(3y)`
  have hlogu : ((n:ℝ) - ⌊y⌋₊ - 1) / (3 * y) ≤ |Real.log (y / n)| := by
    have h1 : Real.log (y / (n:ℝ)) ≤ y / n - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hneg : Real.log (y / (n:ℝ)) < 0 := Real.log_neg (by positivity) hu1
    rw [abs_of_neg hneg]
    have h2 : Real.log ((n:ℝ) / y) ≤ (n:ℝ) / y - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log (y / (n:ℝ)) = -Real.log ((n:ℝ) / y) := by
      rw [← Real.log_inv]
      congr 1
      field_simp
    -- want: gap/(3y) ≤ log(n/y); use log(n/y) ≥ 1 − y/n = (n−y)/n
    have h4 : Real.log (y / (n:ℝ)) ≤ -( ((n:ℝ) - y) / n ) := by
      have h5 : y / (n:ℝ) - 1 = -(((n:ℝ) - y) / n) := by field_simp; ring
      rw [← h5]
      exact h1
    have h6 : ((n:ℝ) - y) / n ≤ -Real.log (y / (n:ℝ)) := by linarith
    have h7 : ((n:ℝ) - ⌊y⌋₊ - 1) / (3 * y) ≤ ((n:ℝ) - y) / n := by
      apply div_le_div₀ (by linarith) (by linarith) (by positivity) hn3y
    linarith
  have hup : (y / (n:ℝ)) ^ c ≤ 1 :=
    Real.rpow_le_one (by positivity) hu1.le hc0.le
  have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log (3 * y) := by
    calc ArithmeticFunction.vonMangoldt n ≤ Real.log n :=
        ArithmeticFunction.vonMangoldt_le_log
      _ ≤ Real.log (3 * y) := Real.log_le_log hn0 hn3y
  have hlog3y : 0 ≤ Real.log (3 * y) := Real.log_nonneg (by linarith)
  have hKb : ‖perronKernel (y / n) c T‖ ≤ 3 * y / (T * ((n:ℝ) - ⌊y⌋₊ - 1)) := by
    calc ‖perronKernel (y / n) c T‖
        ≤ (y / (n:ℝ)) ^ c / (T * |Real.log (y / n)|) := hfar
      _ ≤ 1 / (T * (((n:ℝ) - ⌊y⌋₊ - 1) / (3 * y))) := by
          have hd1 : (0:ℝ) < T * (((n:ℝ) - ⌊y⌋₊ - 1) / (3 * y)) :=
            mul_pos hT (div_pos hgap0 (by linarith))
          exact div_le_div₀ (by norm_num) hup hd1
            (mul_le_mul_of_nonneg_left hlogu hT.le)
      _ = 3 * y / (T * ((n:ℝ) - ⌊y⌋₊ - 1)) := by
          field_simp
  calc ArithmeticFunction.vonMangoldt n * ‖perronKernel (y / n) c T‖
      ≤ Real.log (3 * y) * (3 * y / (T * ((n:ℝ) - ⌊y⌋₊ - 1))) := by
        apply mul_le_mul hΛ hKb (norm_nonneg _) hlog3y
    _ = (3 * y * Real.log (3 * y) / T) * (1 / ((n : ℝ) - ⌊y⌋₊ - 1)) := by
        field_simp

end KerErrBounds

/-- Gap-sum, left of the diagonal. -/
lemma sum_inv_gap_left {F : ℕ} {s : Finset ℕ} (hs : ∀ n ∈ s, n < F) :
    ∑ n ∈ s, 1 / ((F : ℝ) - n) ≤ 1 + Real.log F := by
  have himg : ∑ n ∈ s, (1:ℝ) / ((F : ℝ) - n)
      = ∑ n ∈ s, (fun j : ℕ => (1:ℝ) / (j + 1)) (F - 1 - n) := by
    apply Finset.sum_congr rfl
    intro n hn
    have h1 : n < F := hs n hn
    have h2 : (F : ℝ) - n = ((F - 1 - n : ℕ) : ℝ) + 1 := by
      have h3 : (F - 1 - n) + (n + 1) = F := by omega
      have h4 : ((F - 1 - n : ℕ) : ℝ) + ((n : ℝ) + 1) = (F : ℝ) := by
        exact_mod_cast h3
      linarith
    rw [h2]
  rw [himg]
  have hinj : Set.InjOn (fun n => F - 1 - n) (s : Set ℕ) := by
    intro x hx z hz h
    have hx' := hs x hx
    have hz' := hs z hz
    simp only at h
    omega
  have hkey : ∑ n ∈ s, (fun j : ℕ => (1:ℝ) / (j + 1)) (F - 1 - n)
      = ∑ j ∈ s.image (fun n => F - 1 - n), (1:ℝ) / (j + 1) :=
    (Finset.sum_image (f := fun j : ℕ => (1:ℝ) / (j + 1)) hinj).symm
  rw [hkey]
  have hsub : s.image (fun n => F - 1 - n) ⊆ Finset.range F := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨n, hn, rfl⟩ := hj
    rw [Finset.mem_range]
    have := hs n hn
    omega
  calc ∑ j ∈ s.image (fun n => F - 1 - n), (1:ℝ) / (j + 1)
      ≤ ∑ j ∈ Finset.range F, (1:ℝ) / (j + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
    _ ≤ 1 + Real.log F := harmonic_le F

/-- Gap-sum, right of the diagonal. -/
lemma sum_inv_gap_right {F : ℕ} {s : Finset ℕ}
    (hs : ∀ n ∈ s, F + 2 ≤ n ∧ n ≤ 2 * F + 2) :
    ∑ n ∈ s, 1 / ((n : ℝ) - F - 1) ≤ 1 + Real.log (F + 1) := by
  have himg : ∑ n ∈ s, (1:ℝ) / ((n : ℝ) - F - 1)
      = ∑ n ∈ s, (fun j : ℕ => (1:ℝ) / (j + 1)) (n - F - 2) := by
    apply Finset.sum_congr rfl
    intro n hn
    have h1 : F + 2 ≤ n := (hs n hn).1
    have h2 : (n : ℝ) - F - 1 = ((n - F - 2 : ℕ) : ℝ) + 1 := by
      have h3 : (n - F - 2) + (F + 2) = n := by omega
      have h5 : ((n - F - 2 : ℕ) : ℝ) + ((F : ℝ) + 2) = (n : ℝ) := by
        exact_mod_cast h3
      linarith
    rw [h2]
  rw [himg]
  have hinj : Set.InjOn (fun n => n - F - 2) (s : Set ℕ) := by
    intro x hx z hz h
    have hx' := (hs x hx).1
    have hz' := (hs z hz).1
    simp only at h
    omega
  have hkey : ∑ n ∈ s, (fun j : ℕ => (1:ℝ) / (j + 1)) (n - F - 2)
      = ∑ j ∈ s.image (fun n => n - F - 2), (1:ℝ) / (j + 1) :=
    (Finset.sum_image (f := fun j : ℕ => (1:ℝ) / (j + 1)) hinj).symm
  rw [hkey]
  have hsub : s.image (fun n => n - F - 2) ⊆ Finset.range (F + 1) := by
    intro j hj
    rw [Finset.mem_image] at hj
    obtain ⟨n, hn, rfl⟩ := hj
    rw [Finset.mem_range]
    have h1 := (hs n hn).1
    have h2 := (hs n hn).2
    omega
  calc ∑ j ∈ s.image (fun n => n - F - 2), (1:ℝ) / (j + 1)
      ≤ ∑ j ∈ Finset.range (F + 1), (1:ℝ) / (j + 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
    _ ≤ 1 + Real.log (F + 1) := by
        have := harmonic_le (F + 1)
        have hcast : ((F + 1 : ℕ) : ℝ) = (F : ℝ) + 1 := by push_cast; ring
        rw [hcast] at this
        exact this

set_option maxHeartbeats 1000000 in
/-- Master series-side estimate: the Perron-weighted sum tracks `ψ(y,χ)`. -/
lemma perronSum_sub_psiChi_le (χ : DirichletCharacter ℂ N) {y T : ℝ}
    (hy : 100 ≤ y) (hT : 2 ≤ T) :
    ‖perronSum χ y (1 + 1 / Real.log y) T - psiChi χ y‖
      ≤ 200 * (y * Real.log (T * y) ^ 2 / T) + 30 * Real.log (T * y) ^ 2 := by
  classical
  have hy0 : (0:ℝ) < y := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hlogy : 4 ≤ Real.log y := four_le_log hy
  have hlogy0 : 0 < Real.log y := by linarith
  set c : ℝ := 1 + 1 / Real.log y with hcdef
  have hinvlog : 1 / Real.log y ≤ 1/4 :=
    (one_div_le_one_div_of_le (by norm_num) hlogy)
  have hinvlog0 : 0 < 1 / Real.log y := one_div_pos.mpr hlogy0
  have hc1 : 1 < c := by rw [hcdef]; linarith
  have hc54 : c ≤ 5/4 := by rw [hcdef]; linarith
  have hc2 : c ≤ 2 := by linarith
  have hcT : c ≤ T := by linarith
  have hc0 : (0:ℝ) < c := by linarith
  have hyc : y ^ c = Real.exp 1 * y := by rw [hcdef]; exact rpow_one_add_inv_log hy
  have hyc3 : y ^ c ≤ 3 * y := by
    rw [hyc]
    nlinarith [Real.exp_one_lt_d9]
  have hyc0 : (0:ℝ) < y ^ c := Real.rpow_pos_of_pos hy0 _
  set L : ℝ := Real.log (T * y) with hLdef
  have hLy : Real.log y ≤ L := by
    rw [hLdef]
    apply Real.log_le_log hy0
    nlinarith
  have hL4 : 4 ≤ L := le_trans hlogy hLy
  have hLT : Real.log T ≤ L := by
    rw [hLdef]
    apply Real.log_le_log hT0
    nlinarith
  have hL0 : (0:ℝ) < L := by linarith
  have hTy200 : 200 ≤ T * y := by nlinarith
  have hTysq : 200 * (T * y) ≤ (T * y)^2 := by nlinarith [hTy200]
  have hlog2y : Real.log (2 * y) ≤ 2 * L := by
    have h1 : 2 * y ≤ (T * y)^2 := by nlinarith [hTysq, hTy200]
    calc Real.log (2*y) ≤ Real.log ((T*y)^2) := Real.log_le_log (by linarith) h1
      _ = 2 * L := by rw [Real.log_pow, hLdef]; push_cast; ring
  have hlog3y : Real.log (3 * y) ≤ 2 * L := by
    have h1 : 3 * y ≤ (T * y)^2 := by nlinarith [hTysq, hTy200]
    calc Real.log (3*y) ≤ Real.log ((T*y)^2) := Real.log_le_log (by linarith) h1
      _ = 2 * L := by rw [Real.log_pow, hLdef]; push_cast; ring
  have h1T : 1 + Real.log T ≤ 2 * L := by linarith
  have hF100 : 100 ≤ ⌊y⌋₊ := Nat.le_floor (by exact_mod_cast hy)
  have hFle : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0.le
  have hFgt : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  set R : ℕ := 2 * ⌊y⌋₊ + 2 with hRdef
  have hRcast : (R : ℝ) = 2 * (⌊y⌋₊ : ℝ) + 2 := by rw [hRdef]; push_cast; ring
  have hR2y : 2 * y ≤ (R : ℝ) := by rw [hRcast]; linarith
  -- key numeric conversion `6/(c−1)² = 6·log²y`
  have hcsub : c - 1 = 1 / Real.log y := by rw [hcdef]; ring
  have he6 : 6 / (c - 1) ^ 2 = 6 * Real.log y ^ 2 := by
    rw [hcsub, one_div, inv_pow, div_inv_eq_mul]
  have h2ycT : (0:ℝ) ≤ 2 * y ^ c / T :=
    div_nonneg (by nlinarith [hyc0]) hT0.le
  have hconv : (2 * y ^ c / T) * (6 * Real.log y ^ 2) ≤ 36 * (y * L ^ 2 / T) := by
    rw [div_mul_eq_mul_div,
      show 36 * (y * L^2 / T) = (36 * (y * L^2)) / T by ring]
    apply div_le_div_right_of_pos hT0
    have hsq : Real.log y ^ 2 ≤ L ^ 2 := by nlinarith
    nlinarith [hyc3, hyc0, hL0]
  -- summability inputs
  have hsumΛ : Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * (n:ℝ)^(-c)) :=
    summable_vonMangoldt_rpow hc1
  have hΛtsum : ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n:ℝ)^(-c)
      ≤ 6 * Real.log y ^ 2 := by
    rw [← he6]
    exact tsum_vonMangoldt_rpow_le hc1 hc2
  have hΛnn : ∀ n : ℕ, 0 ≤ ArithmeticFunction.vonMangoldt n * (n:ℝ)^(-c) := fun n =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hfarshift : ∀ i : ℕ, kerErr y c T ⌊y⌋₊ (i + R)
      ≤ (2 * y ^ c / T) * (ArithmeticFunction.vonMangoldt (i + R)
          * ((i + R : ℕ) : ℝ) ^ (-c)) := by
    intro i
    apply kerErr_far_right hy hc0 hT0
    have : (R : ℝ) ≤ ((i + R : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left R i
    linarith
  have hsumE : Summable (kerErr y c T ⌊y⌋₊) := by
    suffices h : Summable (fun i : ℕ => kerErr y c T ⌊y⌋₊ (i + R)) from
      (summable_nat_add_iff R).mp h
    exact Summable.of_nonneg_of_le (fun i => kerErr_nonneg) hfarshift
      (((summable_nat_add_iff R).mpr hsumΛ).mul_left _)
  -- ψ as a tsum of cutoff terms
  have hψ : psiChi χ y = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ)
      * χ (n : ZMod N) * (if n ≤ ⌊y⌋₊ then 1 else 0) := by
    symm
    rw [tsum_eq_sum (s := Finset.range (⌊y⌋₊ + 1)) (fun n hn => by
      rw [Finset.mem_range] at hn
      rw [if_neg (by omega), mul_zero])]
    rw [psiChi]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_range] at hn
    rw [if_pos (by omega), mul_one]
  have hsum1 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)
      * χ (n : ZMod N) * perronKernel (y / n) c T) :=
    summable_perron_term χ hy hc1 hT0
  have hsum2 : Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)
      * χ (n : ZMod N) * (if n ≤ ⌊y⌋₊ then 1 else 0)) := by
    apply summable_of_ne_finset_zero (s := Finset.range (⌊y⌋₊ + 1))
    intro n hn
    rw [Finset.mem_range] at hn
    rw [if_neg (by omega), mul_zero]
  -- pointwise error bound
  have hptw : ∀ n : ℕ,
      ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
          * perronKernel (y / n) c T
        - (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
          * (if n ≤ ⌊y⌋₊ then 1 else 0)‖
      ≤ kerErr y c T ⌊y⌋₊ n := by
    intro n
    have h1 : (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
          * perronKernel (y / n) c T
        - (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
          * (if n ≤ ⌊y⌋₊ then 1 else 0)
        = (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
          * (perronKernel (y / n) c T - (if n ≤ ⌊y⌋₊ then 1 else 0)) := by ring
    rw [h1, kerErr, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have h2 : ‖χ (n : ZMod N)‖ ≤ 1 := χ.norm_le_one _
    have h3 : ArithmeticFunction.vonMangoldt n * ‖χ (n : ZMod N)‖
        * ‖perronKernel (y / n) c T - (if n ≤ ⌊y⌋₊ then 1 else 0)‖
        ≤ ArithmeticFunction.vonMangoldt n * 1
        * ‖perronKernel (y / n) c T - (if n ≤ ⌊y⌋₊ then 1 else 0)‖ := by
      gcongr
    rw [mul_one] at h3
    exact h3
  have hsumnorm : Summable (fun n : ℕ =>
      ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
          * perronKernel (y / n) c T
        - (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
          * (if n ≤ ⌊y⌋₊ then 1 else 0)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hptw hsumE
  -- the norm bound by the kerErr tsum
  have hnorm : ‖perronSum χ y c T - psiChi χ y‖
      ≤ ∑' n : ℕ, kerErr y c T ⌊y⌋₊ n := by
    rw [perronSum, hψ, ← Summable.tsum_sub hsum1 hsum2]
    calc ‖∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
          * perronKernel (y / n) c T
        - (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
          * (if n ≤ ⌊y⌋₊ then 1 else 0))‖
        ≤ ∑' n : ℕ, ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
          * perronKernel (y / n) c T
        - (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
          * (if n ≤ ⌊y⌋₊ then 1 else 0)‖ := norm_tsum_le_tsum_norm hsumnorm
      _ ≤ ∑' n : ℕ, kerErr y c T ⌊y⌋₊ n :=
          Summable.tsum_le_tsum hptw hsumnorm hsumE
  -- split head/tail
  have hsplitE : ∑' n : ℕ, kerErr y c T ⌊y⌋₊ n
      = (∑ n ∈ Finset.range R, kerErr y c T ⌊y⌋₊ n)
        + ∑' i : ℕ, kerErr y c T ⌊y⌋₊ (i + R) :=
    (hsumE.sum_add_tsum_nat_add R).symm
  -- tail bound
  have htail : ∑' i : ℕ, kerErr y c T ⌊y⌋₊ (i + R) ≤ 36 * (y * L^2 / T) := by
    have hs1 : Summable (fun i : ℕ => kerErr y c T ⌊y⌋₊ (i + R)) :=
      (summable_nat_add_iff R).mpr hsumE
    have hs2 : Summable (fun i : ℕ => (2 * y ^ c / T)
        * (ArithmeticFunction.vonMangoldt (i + R) * ((i + R : ℕ) : ℝ) ^ (-c))) :=
      ((summable_nat_add_iff R).mpr hsumΛ).mul_left _
    calc ∑' i : ℕ, kerErr y c T ⌊y⌋₊ (i + R)
        ≤ ∑' i : ℕ, (2 * y ^ c / T)
            * (ArithmeticFunction.vonMangoldt (i + R) * ((i + R : ℕ) : ℝ) ^ (-c)) :=
          Summable.tsum_le_tsum hfarshift hs1 hs2
      _ = (2 * y ^ c / T) * ∑' i : ℕ,
            (ArithmeticFunction.vonMangoldt (i + R) * ((i + R : ℕ) : ℝ) ^ (-c)) :=
          tsum_mul_left
      _ ≤ (2 * y ^ c / T) * ∑' n : ℕ,
            (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)) := by
          apply mul_le_mul_of_nonneg_left _ h2ycT
          have h := hsumΛ.sum_add_tsum_nat_add R
          have hhead : 0 ≤ ∑ n ∈ Finset.range R,
              ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c) :=
            Finset.sum_nonneg (fun n _ => hΛnn n)
          linarith
      _ ≤ (2 * y ^ c / T) * (6 * Real.log y ^ 2) :=
          mul_le_mul_of_nonneg_left hΛtsum h2ycT
      _ ≤ 36 * (y * L^2 / T) := hconv
  -- head bound
  have hhead : ∑ n ∈ Finset.range R, kerErr y c T ⌊y⌋₊ n
      ≤ 70 * (y * L^2 / T) + 24 * L^2 := by
    have hsplit1 := Finset.sum_filter_add_sum_filter_not (Finset.range R)
      (fun n => 2*n ≤ ⌊y⌋₊) (kerErr y c T ⌊y⌋₊)
    set s1 : Finset ℕ := (Finset.range R).filter (fun n => ¬ 2*n ≤ ⌊y⌋₊) with hs1def
    have hsplit2 := Finset.sum_filter_add_sum_filter_not s1
      (fun n => n = ⌊y⌋₊ ∨ n = ⌊y⌋₊ + 1) (kerErr y c T ⌊y⌋₊)
    set s2 : Finset ℕ := s1.filter (fun n => ¬ (n = ⌊y⌋₊ ∨ n = ⌊y⌋₊ + 1)) with hs2def
    have hsplit3 := Finset.sum_filter_add_sum_filter_not s2
      (fun n => n < ⌊y⌋₊) (kerErr y c T ⌊y⌋₊)
    -- region A: 2n ≤ ⌊y⌋₊
    have hA : ∑ n ∈ (Finset.range R).filter (fun n => 2*n ≤ ⌊y⌋₊),
        kerErr y c T ⌊y⌋₊ n ≤ 36 * (y * L^2 / T) := by
      calc ∑ n ∈ (Finset.range R).filter (fun n => 2*n ≤ ⌊y⌋₊), kerErr y c T ⌊y⌋₊ n
          ≤ ∑ n ∈ (Finset.range R).filter (fun n => 2*n ≤ ⌊y⌋₊),
              (2 * y ^ c / T) * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)) := by
            apply Finset.sum_le_sum
            intro n hn
            rw [Finset.mem_filter] at hn
            exact kerErr_far_left hy hc0 hT0 hn.2
        _ ≤ ∑ n ∈ Finset.range R,
              (2 * y ^ c / T) * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun n _ _ => mul_nonneg h2ycT (hΛnn n))
        _ = (2 * y ^ c / T) * ∑ n ∈ Finset.range R,
              (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-c)) := by
            rw [Finset.mul_sum]
        _ ≤ (2 * y ^ c / T) * (6 * Real.log y ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ h2ycT
            exact le_trans (hsumΛ.sum_le_tsum _ (fun n _ => hΛnn n)) hΛtsum
        _ ≤ 36 * (y * L^2 / T) := hconv
    -- region near
    have hnear : ∑ n ∈ s1.filter (fun n => n = ⌊y⌋₊ ∨ n = ⌊y⌋₊ + 1),
        kerErr y c T ⌊y⌋₊ n ≤ 24 * L^2 := by
      have hbnd : ∀ n ∈ s1.filter (fun n => n = ⌊y⌋₊ ∨ n = ⌊y⌋₊ + 1),
          kerErr y c T ⌊y⌋₊ n ≤ 3 * Real.log (2 * y) * (1 + Real.log T) := by
        intro n hn
        rw [Finset.mem_filter] at hn
        exact kerErr_near hy hc1.le hc2 hT hcT hn.2
      have hcard : (s1.filter (fun n => n = ⌊y⌋₊ ∨ n = ⌊y⌋₊ + 1)).card ≤ 2 := by
        have hsub : s1.filter (fun n => n = ⌊y⌋₊ ∨ n = ⌊y⌋₊ + 1)
            ⊆ {⌊y⌋₊, ⌊y⌋₊ + 1} := by
          intro n hn
          rw [Finset.mem_filter] at hn
          rcases hn.2 with h | h <;> simp [h]
        calc (s1.filter (fun n => n = ⌊y⌋₊ ∨ n = ⌊y⌋₊ + 1)).card
            ≤ ({⌊y⌋₊, ⌊y⌋₊ + 1} : Finset ℕ).card := Finset.card_le_card hsub
          _ ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      have hX0 : 0 ≤ 3 * Real.log (2 * y) * (1 + Real.log T) := by
        have ha := Real.log_nonneg (show (1:ℝ) ≤ 2*y by linarith)
        have hb := Real.log_nonneg (show (1:ℝ) ≤ T by linarith)
        nlinarith
      calc ∑ n ∈ s1.filter (fun n => n = ⌊y⌋₊ ∨ n = ⌊y⌋₊ + 1), kerErr y c T ⌊y⌋₊ n
          ≤ ∑ _n ∈ s1.filter (fun n => n = ⌊y⌋₊ ∨ n = ⌊y⌋₊ + 1),
              3 * Real.log (2 * y) * (1 + Real.log T) := Finset.sum_le_sum hbnd
        _ = ((s1.filter (fun n => n = ⌊y⌋₊ ∨ n = ⌊y⌋₊ + 1)).card : ℝ)
              * (3 * Real.log (2 * y) * (1 + Real.log T)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 2 * (3 * Real.log (2 * y) * (1 + Real.log T)) := by
            apply mul_le_mul_of_nonneg_right _ hX0
            exact_mod_cast hcard
        _ ≤ 24 * L^2 := by
            have h2y0 : 0 ≤ Real.log (2*y) :=
              Real.log_nonneg (by linarith)
            have hT0' : 0 ≤ 1 + Real.log T := by
              have := Real.log_nonneg (show (1:ℝ) ≤ T by linarith)
              linarith
            nlinarith [hlog2y, h1T, hL0]
    -- region mid-left
    have hML : ∑ n ∈ s2.filter (fun n => n < ⌊y⌋₊), kerErr y c T ⌊y⌋₊ n
        ≤ 16 * (y * L^2 / T) := by
      have hmem : ∀ n ∈ s2.filter (fun n => n < ⌊y⌋₊),
          ⌊y⌋₊ < 2*n ∧ n < ⌊y⌋₊ := by
        intro n hn
        rw [hs2def, hs1def] at hn
        simp only [Finset.mem_filter, Finset.mem_range] at hn
        exact ⟨by omega, hn.2⟩
      calc ∑ n ∈ s2.filter (fun n => n < ⌊y⌋₊), kerErr y c T ⌊y⌋₊ n
          ≤ ∑ n ∈ s2.filter (fun n => n < ⌊y⌋₊),
              (4 * y * Real.log (2 * y) / T) * (1 / ((⌊y⌋₊ : ℝ) - n)) := by
            apply Finset.sum_le_sum
            intro n hn
            exact kerErr_mid_left hy hc0 hc2 hT0 (hmem n hn).1 (hmem n hn).2
        _ = (4 * y * Real.log (2 * y) / T)
              * ∑ n ∈ s2.filter (fun n => n < ⌊y⌋₊), (1 / ((⌊y⌋₊ : ℝ) - n)) := by
            rw [Finset.mul_sum]
        _ ≤ (4 * y * Real.log (2 * y) / T) * (1 + Real.log ⌊y⌋₊) := by
            apply mul_le_mul_of_nonneg_left
            · exact sum_inv_gap_left (fun n hn => (hmem n hn).2)
            · have ha := Real.log_nonneg (show (1:ℝ) ≤ 2*y by linarith)
              exact div_nonneg
                (mul_nonneg (mul_nonneg (by norm_num) hy0.le) ha) hT0.le
        _ ≤ 16 * (y * L^2 / T) := by
            rw [div_mul_eq_mul_div,
              show 16 * (y * L^2 / T) = (16 * (y * L^2)) / T by ring]
            apply div_le_div_right_of_pos hT0
            have hlogF : Real.log ⌊y⌋₊ ≤ L := by
              rcases Nat.eq_zero_or_pos ⌊y⌋₊ with h | h
              · rw [h]; simp; linarith
              · calc Real.log ⌊y⌋₊ ≤ Real.log y :=
                    Real.log_le_log (by exact_mod_cast h) hFle
                  _ ≤ L := hLy
            have h2y0 : 0 ≤ Real.log (2*y) := Real.log_nonneg (by linarith)
            have hF1 : (1:ℝ) ≤ (⌊y⌋₊ : ℝ) := by
              have : (100:ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast hF100
              linarith
            have hlogF0 : 0 ≤ Real.log ⌊y⌋₊ := Real.log_nonneg hF1
            have hstep1 : Real.log (2*y) * (1 + Real.log ⌊y⌋₊) ≤ (2*L) * (2*L) :=
              mul_le_mul hlog2y (by linarith) (by linarith) (by linarith)
            have hprod := mul_le_mul_of_nonneg_left hstep1
              (by linarith : (0:ℝ) ≤ 4*y)
            nlinarith [hprod]
    -- region mid-right
    have hMR : ∑ n ∈ s2.filter (fun n => ¬ n < ⌊y⌋₊), kerErr y c T ⌊y⌋₊ n
        ≤ 18 * (y * L^2 / T) := by
      have hmem : ∀ n ∈ s2.filter (fun n => ¬ n < ⌊y⌋₊),
          ⌊y⌋₊ + 2 ≤ n ∧ n ≤ 2 * ⌊y⌋₊ + 2 := by
        intro n hn
        rw [hs2def, hs1def] at hn
        simp only [Finset.mem_filter, Finset.mem_range] at hn
        constructor
        · rcases hn with ⟨⟨⟨_, _⟩, hq⟩, hr⟩
          push Not at hq
          omega
        · rcases hn with ⟨⟨⟨hR', _⟩, _⟩, _⟩
          rw [hRdef] at hR'
          omega
      calc ∑ n ∈ s2.filter (fun n => ¬ n < ⌊y⌋₊), kerErr y c T ⌊y⌋₊ n
          ≤ ∑ n ∈ s2.filter (fun n => ¬ n < ⌊y⌋₊),
              (3 * y * Real.log (3 * y) / T) * (1 / ((n : ℝ) - ⌊y⌋₊ - 1)) := by
            apply Finset.sum_le_sum
            intro n hn
            exact kerErr_mid_right hy hc0 hT0 (hmem n hn).1 (hmem n hn).2
        _ = (3 * y * Real.log (3 * y) / T)
              * ∑ n ∈ s2.filter (fun n => ¬ n < ⌊y⌋₊), (1 / ((n : ℝ) - ⌊y⌋₊ - 1)) := by
            rw [Finset.mul_sum]
        _ ≤ (3 * y * Real.log (3 * y) / T) * (1 + Real.log (⌊y⌋₊ + 1)) := by
            apply mul_le_mul_of_nonneg_left
            · exact sum_inv_gap_right hmem
            · have ha := Real.log_nonneg (show (1:ℝ) ≤ 3*y by linarith)
              exact div_nonneg
                (mul_nonneg (mul_nonneg (by norm_num) hy0.le) ha) hT0.le
        _ ≤ 18 * (y * L^2 / T) := by
            rw [div_mul_eq_mul_div,
              show 18 * (y * L^2 / T) = (18 * (y * L^2)) / T by ring]
            apply div_le_div_right_of_pos hT0
            have hlogF1 : Real.log ((⌊y⌋₊ : ℝ) + 1) ≤ 2 * L := by
              calc Real.log ((⌊y⌋₊ : ℝ) + 1) ≤ Real.log (2*y) :=
                  Real.log_le_log (by positivity) (by linarith)
                _ ≤ 2 * L := hlog2y
            have h3y0 : 0 ≤ Real.log (3*y) := Real.log_nonneg (by linarith)
            have hlogF10 : 0 ≤ Real.log ((⌊y⌋₊ : ℝ) + 1) :=
              Real.log_nonneg (by
                have : (0:ℝ) ≤ (⌊y⌋₊ : ℝ) := Nat.cast_nonneg _
                linarith)
            have hstep1 : Real.log (3*y) * (1 + Real.log ((⌊y⌋₊ : ℝ) + 1))
                ≤ (2*L) * (3*L) :=
              mul_le_mul hlog3y (by linarith) (by linarith) (by linarith)
            have hprod := mul_le_mul_of_nonneg_left hstep1
              (by linarith : (0:ℝ) ≤ 3*y)
            nlinarith [hprod]
    -- assemble the head
    calc ∑ n ∈ Finset.range R, kerErr y c T ⌊y⌋₊ n
        = (∑ n ∈ (Finset.range R).filter (fun n => 2*n ≤ ⌊y⌋₊), kerErr y c T ⌊y⌋₊ n)
          + ((∑ n ∈ s1.filter (fun n => n = ⌊y⌋₊ ∨ n = ⌊y⌋₊ + 1),
              kerErr y c T ⌊y⌋₊ n)
            + ((∑ n ∈ s2.filter (fun n => n < ⌊y⌋₊), kerErr y c T ⌊y⌋₊ n)
              + ∑ n ∈ s2.filter (fun n => ¬ n < ⌊y⌋₊), kerErr y c T ⌊y⌋₊ n)) := by
          rw [hsplit3, hsplit2, hsplit1]
      _ ≤ 36 * (y * L^2 / T) + (24 * L^2 + (16 * (y * L^2 / T) + 18 * (y * L^2 / T))) := by
          gcongr
      _ ≤ 70 * (y * L^2 / T) + 24 * L^2 := by linarith
  -- grand total
  calc ‖perronSum χ y c T - psiChi χ y‖
      ≤ ∑' n : ℕ, kerErr y c T ⌊y⌋₊ n := hnorm
    _ = (∑ n ∈ Finset.range R, kerErr y c T ⌊y⌋₊ n)
        + ∑' i : ℕ, kerErr y c T ⌊y⌋₊ (i + R) := hsplitE
    _ ≤ (70 * (y * L^2 / T) + 24 * L^2) + 36 * (y * L^2 / T) := by
        linarith [hhead, htail]
    _ ≤ 200 * (y * L^2 / T) + 30 * L^2 := by
        have hyL : 0 ≤ y * L^2 / T :=
          div_nonneg (by nlinarith [sq_nonneg L]) hT0.le
        nlinarith [hL0]

end SeriesSide

/-! ### The interchange: `2π · perronSum = ∫ (−L′/L)(c+it)·y^{c+it}/(c+it) dt` -/

section Interchange

open scoped LSeries.notation ArithmeticFunction

variable {N : ℕ} [NeZero N]

/-- `(y/n)^s = y^s/n^s` in `ℂ` for real `y > 0`, `n ≥ 1`. -/
lemma ofReal_div_cpow {y : ℝ} (hy : 0 < y) {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    (((y / n : ℝ)) : ℂ) ^ s = (y : ℂ) ^ s / (n : ℂ) ^ s := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnc : ((n : ℝ) : ℂ) = (n : ℂ) := by push_cast; rfl
  have key : (((y / n : ℝ)) : ℂ) ^ s * (n : ℂ) ^ s = (y : ℂ) ^ s := by
    rw [← hnc, ← Complex.mul_cpow_ofReal_nonneg (by positivity) hn0.le]
    congr 2
    push_cast
    rw [div_mul_cancel₀]
    exact_mod_cast hn0.ne'
  have hne : (n : ℂ) ^ s ≠ 0 := by
    intro h
    rcases (Complex.cpow_eq_zero_iff _ _).mp h with ⟨h1, _⟩
    have : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    exact this h1
  field_simp [hne] at key ⊢
  linear_combination key

set_option maxHeartbeats 1000000 in
/-- The right-edge integral is `2π` times the Perron-weighted sum. -/
lemma integral_right_edge (χ : DirichletCharacter ℂ N) {y c T : ℝ}
    (hy : 100 ≤ y) (hc1 : 1 < c) (hT : 0 < T) :
    (∫ t in (-T)..T,
        (- deriv (DirichletCharacter.LFunction χ) ((c:ℂ) + (t:ℝ) * I)
            / DirichletCharacter.LFunction χ ((c:ℂ) + (t:ℝ) * I))
          * ((y:ℂ) ^ ((c:ℂ) + (t:ℝ) * I) / ((c:ℂ) + (t:ℝ) * I)))
      = ((2 * π : ℝ) : ℂ) * perronSum χ y c T := by
  have hy0 : (0:ℝ) < y := by linarith
  have hc0 : (0:ℝ) < c := by linarith
  set f : ℕ → ℝ → ℂ := fun n t => (ArithmeticFunction.vonMangoldt n : ℂ)
    * χ (n : ZMod N) * perronIntegrand (y / n) c t with hfdef
  -- pointwise identity on the line `Re s = c`
  have hpt : ∀ t : ℝ, ∑' n : ℕ, f n t
      = (- deriv (DirichletCharacter.LFunction χ) ((c:ℂ) + t * I)
          / DirichletCharacter.LFunction χ ((c:ℂ) + t * I))
        * ((y:ℂ) ^ ((c:ℂ) + t * I) / ((c:ℂ) + t * I)) := by
    intro t
    have hsre : 1 < ((c:ℂ) + t * I).re := by rw [re_coord]; exact hc1
    have hterm : ∀ n : ℕ, f n t
        = LSeries.term (↗χ * ↗Λ) ((c:ℂ) + t * I) n
          * ((y:ℂ) ^ ((c:ℂ) + t * I) / ((c:ℂ) + t * I)) := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [hfdef]
        simp [LSeries.term_zero, ArithmeticFunction.map_zero]
      · have hn0 : (n : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.cast_pos.mpr hn).ne' (α := ℝ)
        have hne : (n : ℂ) ^ ((c:ℂ) + t * I) ≠ 0 := by
          intro h
          exact hn0 ((Complex.cpow_eq_zero_iff _ _).mp h).1
        rw [hfdef]
        show (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
            * perronIntegrand (y / n) c t = _
        rw [LSeries.term_of_ne_zero hn.ne', perronIntegrand,
          ofReal_div_cpow hy0 hn]
        simp only [Pi.mul_apply]
        field_simp
    have hLsum : LSeriesSummable (↗χ * ↗Λ) ((c:ℂ) + t * I) :=
      DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hsre
    have hL := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hsre
    have hLf : DirichletCharacter.LFunction χ ((c:ℂ) + t * I)
        = LSeries (χ ·) ((c:ℂ) + t * I) :=
      DirichletCharacter.LFunction_eq_LSeries χ hsre
    have hLd : deriv (DirichletCharacter.LFunction χ) ((c:ℂ) + t * I)
        = deriv (LSeries (χ ·)) ((c:ℂ) + t * I) :=
      DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hsre
    calc ∑' n : ℕ, f n t
        = ∑' n : ℕ, LSeries.term (↗χ * ↗Λ) ((c:ℂ) + t * I) n
            * ((y:ℂ) ^ ((c:ℂ) + t * I) / ((c:ℂ) + t * I)) := tsum_congr hterm
      _ = LSeries (↗χ * ↗Λ) ((c:ℂ) + t * I)
            * ((y:ℂ) ^ ((c:ℂ) + t * I) / ((c:ℂ) + t * I)) := tsum_mul_right
      _ = (- deriv (DirichletCharacter.LFunction χ) ((c:ℂ) + t * I)
            / DirichletCharacter.LFunction χ ((c:ℂ) + t * I))
          * ((y:ℂ) ^ ((c:ℂ) + t * I) / ((c:ℂ) + t * I)) := by
          rw [hL, ← hLf, ← hLd]
  -- interval integrability of each term
  have hint : ∀ n : ℕ, IntervalIntegrable (f n) MeasureTheory.volume (-T) T := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h0 : f 0 = fun _ : ℝ => (0:ℂ) := by
        funext t
        rw [hfdef]
        simp [ArithmeticFunction.map_zero]
      rw [h0]
      exact intervalIntegrable_const
    · apply Continuous.intervalIntegrable
      apply Continuous.mul continuous_const
      have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact continuous_perronIntegrand (div_pos hy0 hn0) hc0.ne'
  -- per-term norm bound on the line
  have hnormle : ∀ (n : ℕ) (t : ℝ), ‖f n t‖
      ≤ ArithmeticFunction.vonMangoldt n * ((y / n) ^ c / c) := by
    intro n t
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hfdef]
      simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, zero_mul, norm_zero]
      positivity
    · have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hu0 : (0:ℝ) < y / n := div_pos hy0 hn0
      have h1 : ‖f n t‖ ≤ ArithmeticFunction.vonMangoldt n
          * ‖perronIntegrand (y / n) c t‖ := by
        rw [hfdef]
        show ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
          * perronIntegrand (y / n) c t‖ ≤ _
        rw [norm_mul, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        have h2 : ‖χ (n : ZMod N)‖ ≤ 1 := χ.norm_le_one _
        have h3 : ArithmeticFunction.vonMangoldt n * ‖χ (n : ZMod N)‖
            * ‖perronIntegrand (y / n) c t‖
            ≤ ArithmeticFunction.vonMangoldt n * 1
            * ‖perronIntegrand (y / n) c t‖ := by gcongr
        rw [mul_one] at h3
        exact h3
      have h4 : ‖perronIntegrand (y / n) c t‖ ≤ (y / n) ^ c / c := by
        rw [norm_perronIntegrand hu0]
        apply div_le_div_of_nonneg_left (Real.rpow_nonneg hu0.le c) hc0
        have := norm_coord_ge_abs_re c t
        rwa [abs_of_pos hc0] at this
      calc ‖f n t‖ ≤ ArithmeticFunction.vonMangoldt n
          * ‖perronIntegrand (y / n) c t‖ := h1
        _ ≤ ArithmeticFunction.vonMangoldt n * ((y / n) ^ c / c) :=
            mul_le_mul_of_nonneg_left h4 ArithmeticFunction.vonMangoldt_nonneg
  -- interchange sum and integral
  have hTle : (-T : ℝ) ≤ T := by linarith
  have hIoc : MeasureTheory.volume (Ioc (-T) T) = ENNReal.ofReal (2*T) := by
    rw [Real.volume_Ioc]
    congr 1
    ring
  have hintegrable : ∀ n : ℕ, MeasureTheory.Integrable (f n)
      (MeasureTheory.volume.restrict (Ioc (-T) T)) := by
    intro n
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hTle).mp (hint n)
  have hbnd : ∀ n : ℕ, (∫ t in Ioc (-T) T, ‖f n t‖)
      ≤ (2*T) * (ArithmeticFunction.vonMangoldt n * ((y / n) ^ c / c)) := by
    intro n
    have h1 : (∫ t in Ioc (-T) T, ‖f n t‖)
        ≤ ∫ _t in Ioc (-T) T,
            (ArithmeticFunction.vonMangoldt n * ((y / n) ^ c / c)) := by
      apply MeasureTheory.setIntegral_mono_on (hintegrable n).norm
        (MeasureTheory.integrableOn_const (C := _) (by simp))
        measurableSet_Ioc
      intro t _
      exact hnormle n t
    have h2 : (∫ _t in Ioc (-T) T,
        (ArithmeticFunction.vonMangoldt n * ((y / n) ^ c / c)))
        = (2*T) * (ArithmeticFunction.vonMangoldt n * ((y / n) ^ c / c)) := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul,
        MeasureTheory.measureReal_def, hIoc,
        ENNReal.toReal_ofReal (by linarith)]
    linarith
  have hsummajor : Summable (fun n : ℕ =>
      (2*T) * (ArithmeticFunction.vonMangoldt n * ((y / n) ^ c / c))) := by
    have heq : ∀ n : ℕ, (2*T) * (ArithmeticFunction.vonMangoldt n * ((y / n) ^ c / c))
        = ((2*T) * (y ^ c / c)) * (ArithmeticFunction.vonMangoldt n * (n:ℝ) ^ (-c)) := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [ArithmeticFunction.map_zero]
      · rw [div_rpow_eq hy0 hn]
        ring
    have h2 : Summable (fun n : ℕ =>
        ((2*T) * (y ^ c / c)) * (ArithmeticFunction.vonMangoldt n * (n:ℝ) ^ (-c))) :=
      (summable_vonMangoldt_rpow hc1).mul_left _
    exact h2.congr (fun n => (heq n).symm)
  have hsumnorms : Summable (fun n : ℕ => ∫ t in Ioc (-T) T, ‖f n t‖) := by
    apply Summable.of_nonneg_of_le _ hbnd hsummajor
    intro n
    apply MeasureTheory.integral_nonneg
    intro t
    exact norm_nonneg _
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := MeasureTheory.volume.restrict (Ioc (-T) T)) hintegrable hsumnorms
  -- per-term kernel identity
  have hπ0 : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hker : ∀ n : ℕ, (∫ t in (-T)..T, f n t)
      = ((2 * π : ℝ) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n:ZMod N)
        * perronKernel (y/n) c T) := by
    intro n
    rw [hfdef]
    show (∫ t in (-T)..T, (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
      * perronIntegrand (y / n) c t) = _
    rw [show (fun t : ℝ => (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N)
      * perronIntegrand (y / n) c t)
      = (fun t : ℝ => ((ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod N))
        * perronIntegrand (y / n) c t) from rfl]
    rw [intervalIntegral.integral_const_mul]
    rw [perronKernel, Complex.real_smul]
    push_cast
    field_simp
  -- assemble
  calc (∫ t in (-T)..T,
        (- deriv (DirichletCharacter.LFunction χ) ((c:ℂ) + (t:ℝ) * I)
            / DirichletCharacter.LFunction χ ((c:ℂ) + (t:ℝ) * I))
          * ((y:ℂ) ^ ((c:ℂ) + (t:ℝ) * I) / ((c:ℂ) + (t:ℝ) * I)))
      = ∫ t in (-T)..T, ∑' n : ℕ, f n t := by
        apply intervalIntegral.integral_congr
        intro t _
        exact (hpt t).symm
    _ = ∫ t in Ioc (-T) T, ∑' n : ℕ, f n t := intervalIntegral.integral_of_le hTle
    _ = ∑' n : ℕ, ∫ t in Ioc (-T) T, f n t := hswap.symm
    _ = ∑' n : ℕ, ∫ t in (-T)..T, f n t := by
        apply tsum_congr
        intro n
        rw [intervalIntegral.integral_of_le hTle]
    _ = ∑' n : ℕ, ((2 * π : ℝ) : ℂ) * ((ArithmeticFunction.vonMangoldt n : ℂ)
          * χ (n:ZMod N) * perronKernel (y/n) c T) := tsum_congr hker
    _ = ((2 * π : ℝ) : ℂ) * perronSum χ y c T := by
        rw [perronSum, tsum_mul_left]

end Interchange

/-! ### Generic disk machinery: `DiskData`, disk zeros, factorization -/

section GenericDisk

/-- Zeros of a not-identically-zero function analytic on an open preconnected set
meet any compact subset in a finite set. -/
lemma finite_zeros_inter_compact' {f : ℂ → ℂ} {U : Set ℂ}
    (hUc : IsPreconnected U) (hf : AnalyticOnNhd ℂ f U) {w : ℂ} (hwU : w ∈ U)
    (hw : f w ≠ 0) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    {s ∈ K | f s = 0}.Finite := by
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨x, hxK, hacc⟩ := hinf.exists_accPt_of_subset_isCompact hK
    (fun s hs => hs.1)
  have hx : AnalyticAt ℂ f x := hf x (hKU hxK)
  have hfreq : ∃ᶠ z in 𝓝[≠] x, f z = 0 := by
    have h1 := accPt_iff_frequently.mp hacc
    rw [frequently_nhdsWithin_iff]
    exact h1.mono (fun z hz => ⟨hz.2.2, hz.1⟩)
  have hev : ∀ᶠ z in 𝓝 x, f z = 0 :=
    hx.frequently_zero_iff_eventually_zero.mp hfreq
  have hEq : Set.EqOn f 0 U :=
    hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc (hKU hxK) hev
  exact hw (hEq hwU)

/-- The uniform per-disk data needed to run the contour argument on a
comparison function `f` (the L-function of a nontrivial character with
`A = N`, or the Abel-summed eta function with `A = 1`). -/
structure DiskData (f : ℂ → ℂ) (A : ℝ) : Prop where
  one_le : 1 ≤ A
  diff : ∀ t₀ : ℝ, AnalyticOnNhd ℂ f (closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ))
  low : ∀ t₀ : ℝ, 1/6 ≤ ‖f ((2:ℂ) + t₀ * I)‖
  bd : ∀ t₀ : ℝ, ∀ z ∈ closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ),
    ‖f z‖ ≤ 15 * (A * (|t₀| + 2))
  nz : ∀ s : ℂ, 1 < s.re → f s ≠ 0

namespace DiskData

variable {f : ℂ → ℂ} {A : ℝ}

lemma scale_two_le (hf : DiskData f A) (t₀ : ℝ) : 2 ≤ A * (|t₀| + 2) := by
  have h1 := hf.one_le
  have h2 : (0:ℝ) ≤ |t₀| := abs_nonneg t₀
  nlinarith

lemma center_ne_zero (hf : DiskData f A) (t₀ : ℝ) :
    f ((2:ℂ) + t₀ * I) ≠ 0 := by
  intro h
  have h6 := hf.low t₀
  rw [h, norm_zero] at h6
  linarith

lemma finite_diskZeroSet (hf : DiskData f A) (t₀ : ℝ) :
    {s ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ) | f s = 0}.Finite := by
  apply finite_zeros_inter_compact' (U := closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ))
    (convex_closedBall _ _).isPreconnected (hf.diff t₀)
    (mem_closedBall_self (by norm_num)) (hf.center_ne_zero t₀)
    (isCompact_closedBall _ _)
    (closedBall_subset_closedBall (by norm_num))

end DiskData

open scoped Classical in
/-- The distinct zeros of `f` in the closed `13/8`-disk around `2 + it₀`. -/
noncomputable def diskZeros (f : ℂ → ℂ) (t₀ : ℝ) : Finset ℂ :=
  if h : {s ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ) | f s = 0}.Finite
  then h.toFinset else ∅

lemma mem_diskZeros {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) {t₀ : ℝ} {ρ : ℂ} :
    ρ ∈ diskZeros f t₀ ↔
      ρ ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ) ∧ f ρ = 0 := by
  rw [diskZeros, dif_pos (hf.finite_diskZeroSet t₀), Set.Finite.mem_toFinset]
  rfl

/-- The Jensen mass bound for any finset of points in the `13/8`-disk. -/
lemma sum_ord_le_of_diskData {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) (t₀ : ℝ)
    {F : Finset ℂ} (hF : ∀ ρ ∈ F, ρ ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ)) :
    (∑ ρ ∈ F, analyticOrderNatAt f ρ : ℝ) ≤ 112 * Real.log (A * (|t₀| + 2)) := by
  have hX2 : (2:ℝ) ≤ A * (|t₀| + 2) := hf.scale_two_le t₀
  have hM : (1:ℝ) ≤ 15 * (A * (|t₀| + 2)) := by linarith
  have hlow : 1/6 ≤ ‖f ((2:ℂ) + t₀ * I)‖ := hf.low t₀
  have hbd : ∀ z ∈ sphere ((2:ℂ) + t₀ * I) (7/4 : ℝ),
      ‖f z‖ ≤ 15 * (A * (|t₀| + 2)) :=
    fun z hz => hf.bd t₀ z (sphere_subset_closedBall hz)
  have key := sum_analyticOrderNatAt_le (hf.diff t₀) hM hlow hbd hF
  have hlog : Real.log (6 * (15 * (A * (|t₀| + 2))))
      ≤ 8 * Real.log (A * (|t₀| + 2)) := by
    have h : (6:ℝ) * (15 * (A * (|t₀| + 2))) = 90 * (A * (|t₀| + 2)) := by ring
    rw [h]
    exact log_ninety_mul_le hX2
  linarith

/-- Finite vanishing order on the `7/4`-disk. -/
lemma ord_ne_top_of_diskData {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) (t₀ : ℝ)
    {u : ℂ} (hu : u ∈ closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ)) :
    analyticOrderAt f u ≠ ⊤ := by
  intro htop
  have hev : f =ᶠ[𝓝 u] 0 := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz using hz
  have hEq : Set.EqOn f 0 (closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ)) :=
    (hf.diff t₀).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_closedBall _ _).isPreconnected hu hev
  exact hf.center_ne_zero t₀ (hEq (mem_closedBall_self (by norm_num)))

/-- Members of `diskZeros` have multiplicity at least one. -/
lemma one_le_ord_of_mem_diskZeros {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A)
    {t₀ : ℝ} {ρ : ℂ} (hρ : ρ ∈ diskZeros f t₀) :
    1 ≤ analyticOrderNatAt f ρ := by
  obtain ⟨hρ13, hρ0⟩ := (mem_diskZeros hf).mp hρ
  have hρU : ρ ∈ closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ) :=
    closedBall_subset_closedBall (by norm_num) hρ13
  have hne0 : analyticOrderAt f ρ ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hf.diff t₀ ρ hρU, hρ0⟩
  have hnetop := ord_ne_top_of_diskData hf t₀ hρU
  rw [Nat.one_le_iff_ne_zero, analyticOrderNatAt]
  intro h0
  rcases ENat.toNat_eq_zero.mp h0 with h | h
  · exact hne0 h
  · exact hnetop h

set_option maxHeartbeats 800000 in
/-- **Generic factorization** on the `7/4`-disk: `f = ∏ (z−ρ)^{m ρ} · h` with
`h` analytic there and zero-free on the closed `13/8`-disk. -/
theorem exists_diskData_factorization {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A)
    (t₀ : ℝ) :
    ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ)) ∧
      (∀ z ∈ closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ),
        f z = (∏ ρ ∈ diskZeros f t₀, (z - ρ) ^ analyticOrderNatAt f ρ) * h z) ∧
      (∀ z ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ), h z ≠ 0) := by
  classical
  set c : ℂ := (2:ℂ) + t₀ * I with hcdef
  set U : Set ℂ := closedBall c (7/4 : ℝ) with hUdef
  set m : ℂ → ℕ := fun ρ => analyticOrderNatAt f ρ with hmdef
  have hA : AnalyticOnNhd ℂ f U := hf.diff t₀
  have hMero : MeromorphicOn f U := hA.meromorphicOn
  have hUc : IsCompact U := isCompact_closedBall c (7/4 : ℝ)
  have hordU : ∀ u ∈ U, analyticOrderAt f u ≠ ⊤ := fun u hu =>
    ord_ne_top_of_diskData hf t₀ hu
  have h₂f : ∀ u : U, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    rw [(hA u u.2).meromorphicOrderAt_eq, ne_eq, ENat.map_eq_top_iff]
    exact hordU u u.2
  have h₃f : (MeromorphicOn.divisor f U).support.Finite :=
    (MeromorphicOn.divisor f U).finiteSupport hUc
  obtain ⟨g, hg_an, hg_ne, heq⟩ := hMero.extract_zeros_poles h₂f h₃f
  have hDval : ∀ u ∈ U, MeromorphicOn.divisor f U u = (m u : ℤ) := by
    intro u hu
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hA hu,
      ← Nat.cast_analyticOrderNatAt (hordU u hu)]
    rfl
  set Z : Finset ℂ := h₃f.toFinset with hZdef
  have hZsubU : ∀ u ∈ Z, u ∈ U := fun u hu =>
    (MeromorphicOn.divisor f U).supportWithinDomain (h₃f.mem_toFinset.mp hu)
  have hZzero : ∀ u ∈ Z, f u = 0 := by
    intro u hu
    have hne : MeromorphicOn.divisor f U u ≠ 0 := h₃f.mem_toFinset.mp hu
    by_contra hfu
    have h0 : analyticOrderAt f u = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hfu)
    have h1 : m u = 0 := by rw [hmdef]; simp [analyticOrderNatAt, h0]
    rw [hDval u (hZsubU u hu), h1] at hne
    exact hne (by norm_num)
  have hKsubZ : ∀ ρ ∈ diskZeros f t₀, ρ ∈ Z := by
    intro ρ hρ
    obtain ⟨hρ13, hρ0⟩ := (mem_diskZeros hf).mp hρ
    have hρU : ρ ∈ U := closedBall_subset_closedBall (by norm_num) hρ13
    rw [hZdef, h₃f.mem_toFinset]
    show MeromorphicOn.divisor f U ρ ≠ 0
    rw [hDval ρ hρU]
    have h1 : m ρ ≠ 0 := by
      have h2 : m ρ = analyticOrderNatAt f ρ := rfl
      have h3 := one_le_ord_of_mem_diskZeros hf hρ
      rw [h2]
      omega
    exact_mod_cast h1
  have hZ13 : ∀ u ∈ Z, u ∈ closedBall c (13/8 : ℝ) → u ∈ diskZeros f t₀ :=
    fun u hu h13 => (mem_diskZeros hf).mpr ⟨h13, hZzero u hu⟩
  have hPfull : (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor f U u))
      = fun z => ∏ u ∈ Z, (z - u) ^ (m u) := by
    have hsub : (fun u => (· - u) ^ (MeromorphicOn.divisor f U u)).mulSupport ⊆ ↑Z := by
      rw [Function.FactorizedRational.mulSupport]
      intro u hu
      have : MeromorphicOn.divisor f U u ≠ 0 := hu
      simpa [hZdef, h₃f.mem_toFinset] using this
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    funext z
    rw [Finset.prod_apply]
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [Pi.pow_apply, hDval u (hZsubU u hu), zpow_natCast]
  have hProdDiff : ∀ S : Finset ℂ, Differentiable ℂ (fun z => ∏ u ∈ S, (z - u) ^ (m u)) := by
    intro S
    have hrw : (fun z => ∏ u ∈ S, (z - u) ^ (m u))
        = ∏ u ∈ S, fun z => (z - u) ^ (m u) := by
      funext z; rw [Finset.prod_apply]
    rw [hrw]
    apply Differentiable.finsetProd
    intro u _
    exact (differentiable_id.sub_const u).pow _
  have hfac : ∀ z ∈ U, f z = (∏ u ∈ Z, (z - u) ^ (m u)) * g z := by
    have heq' : f =ᶠ[Filter.codiscreteWithin U]
        fun z => (∏ u ∈ Z, (z - u) ^ (m u)) * g z := by
      filter_upwards [heq] with z hz
      calc f z = ((∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor f U u)) • g) z := hz
        _ = (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor f U u)) z * g z := by
            simp [Pi.smul_apply']
        _ = (∏ u ∈ Z, (z - u) ^ (m u)) * g z := by rw [hPfull]
    have hUacc : ∀ x ∈ U, AccPt x (𝓟 U) := fun x hx =>
      accPt_closedBall (by norm_num) hx
    exact eq_on_of_meromorphic_of_codiscreteWithin hUacc
      (fun x hx => (hA x hx).meromorphicAt)
      (fun x hx => (((hProdDiff Z).analyticAt x).mul (hg_an x hx)).meromorphicAt)
      (fun x hx => (hA x hx).continuousAt)
      (fun x hx => ((hProdDiff Z).continuous.continuousAt.mul
        (hg_an x hx).continuousAt))
      heq'
  have hKZ : diskZeros f t₀ ⊆ Z := fun ρ hρ => hKsubZ ρ hρ
  refine ⟨fun z => (∏ u ∈ Z \ diskZeros f t₀, (z - u) ^ (m u)) * g z, ?_, ?_, ?_⟩
  · intro x hx
    exact ((hProdDiff _).analyticAt x).mul (hg_an x hx)
  · intro z hz
    rw [hfac z hz, ← Finset.prod_sdiff hKZ]
    ring
  · intro z hz13
    have hzU : z ∈ U := closedBall_subset_closedBall (by norm_num) hz13
    apply mul_ne_zero
    · rw [Finset.prod_ne_zero_iff]
      intro u hu
      apply pow_ne_zero
      rw [sub_ne_zero]
      intro hzu
      rw [Finset.mem_sdiff] at hu
      exact hu.2 (hZ13 u hu.1 (hzu ▸ hz13))
    · exact hg_ne ⟨z, hzU⟩

/-- Pointwise splitting of the logarithmic derivative against a disk
factorization: `f′/f = ∑ m_ρ/(s−ρ) + h′/h` on the open `13/8`-disk. -/
lemma logDeriv_split {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) (t₀ : ℝ)
    {h : ℂ → ℂ}
    (hh_an : AnalyticOnNhd ℂ h (closedBall ((2:ℂ) + t₀*I) (7/4:ℝ)))
    (hh_fac : ∀ z ∈ closedBall ((2:ℂ) + t₀*I) (7/4:ℝ),
      f z = (∏ ρ ∈ diskZeros f t₀, (z-ρ)^(analyticOrderNatAt f ρ)) * h z)
    {s : ℂ} (hs : s ∈ ball ((2:ℂ) + t₀*I) (13/8:ℝ)) (hfs : f s ≠ 0)
    (hhs : h s ≠ 0) :
    deriv f s / f s
      = (∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℂ) / (s - ρ))
        + deriv h s / h s := by
  have hball_sub : ball ((2:ℂ) + t₀*I) (13/8:ℝ)
      ⊆ closedBall ((2:ℂ) + t₀*I) (7/4:ℝ) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  have hsU : s ∈ closedBall ((2:ℂ) + t₀*I) (7/4:ℝ) := hball_sub hs
  have hsρ : ∀ ρ ∈ diskZeros f t₀, s - ρ ≠ 0 := by
    intro ρ hρ
    rw [sub_ne_zero]
    intro hsρ
    exact hfs (hsρ ▸ ((mem_diskZeros hf).mp hρ).2)
  have hPdiff : Differentiable ℂ (fun z => ∏ ρ ∈ diskZeros f t₀,
      (z - ρ) ^ analyticOrderNatAt f ρ) := by
    have hrw : (fun z => ∏ ρ ∈ diskZeros f t₀, (z - ρ) ^ analyticOrderNatAt f ρ)
        = ∏ ρ ∈ diskZeros f t₀, fun z => (z - ρ) ^ analyticOrderNatAt f ρ := by
      funext z; rw [Finset.prod_apply]
    rw [hrw]
    apply Differentiable.finsetProd
    intro u _
    exact (differentiable_id.sub_const u).pow _
  have hPs_ne : (∏ ρ ∈ diskZeros f t₀, (s - ρ) ^ analyticOrderNatAt f ρ) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro ρ hρ
    exact pow_ne_zero _ (hsρ ρ hρ)
  have hh_diffAt : DifferentiableAt ℂ h s := (hh_an s hsU).differentiableAt
  have hnb : f =ᶠ[𝓝 s]
      fun z => (∏ ρ ∈ diskZeros f t₀, (z - ρ) ^ analyticOrderNatAt f ρ) * h z := by
    filter_upwards [isOpen_ball.mem_nhds hs] with z hz
    exact hh_fac z (hball_sub hz)
  have hd1 : deriv f s
      = deriv (fun z => (∏ ρ ∈ diskZeros f t₀,
          (z - ρ) ^ analyticOrderNatAt f ρ) * h z) s := hnb.deriv_eq
  have hval : f s = (∏ ρ ∈ diskZeros f t₀,
      (s - ρ) ^ analyticOrderNatAt f ρ) * h s := hh_fac s hsU
  have hld : logDeriv (fun z => (∏ ρ ∈ diskZeros f t₀,
      (z - ρ) ^ analyticOrderNatAt f ρ) * h z) s
      = logDeriv (fun z => ∏ ρ ∈ diskZeros f t₀,
          (z - ρ) ^ analyticOrderNatAt f ρ) s + logDeriv h s :=
    logDeriv_mul s hPs_ne hhs (hPdiff s) hh_diffAt
  have hPld : logDeriv (fun z => ∏ ρ ∈ diskZeros f t₀,
      (z - ρ) ^ analyticOrderNatAt f ρ) s
      = ∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℂ) / (s - ρ) := by
    have h1 : logDeriv (fun z => ∏ ρ ∈ diskZeros f t₀,
        (z - ρ) ^ analyticOrderNatAt f ρ) s
        = ∑ ρ ∈ diskZeros f t₀,
          logDeriv (fun z => (z - ρ) ^ analyticOrderNatAt f ρ) s :=
      logDeriv_prod
        (f := fun ρ => fun z => (z - ρ) ^ analyticOrderNatAt f ρ)
        (fun ρ hρ => pow_ne_zero _ (hsρ ρ hρ))
        (fun ρ _ => ((differentiable_id.sub_const ρ).pow _).differentiableAt)
    rw [h1]
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    have h2 : logDeriv (fun z => (z - ρ) ^ analyticOrderNatAt f ρ) s
        = (analyticOrderNatAt f ρ : ℂ) * logDeriv (fun z => z - ρ) s :=
      logDeriv_fun_pow ((differentiable_id.sub_const ρ).differentiableAt) _
    have h3 : logDeriv (fun z => z - ρ) s = 1 / (s - ρ) := by
      rw [logDeriv_apply, deriv_sub_const, deriv_id'']
    rw [h2, h3]
    ring
  have hLD : deriv f s / f s
      = logDeriv (fun z => (∏ ρ ∈ diskZeros f t₀,
          (z - ρ) ^ analyticOrderNatAt f ρ) * h z) s := by
    rw [logDeriv_apply, ← hd1, ← hval]
  rw [hLD, hld, hPld, logDeriv_apply]

set_option maxHeartbeats 1000000 in
/-- **Generic Landau expansion** at scale `X = A(|t₀|+2)`:
`‖f′/f − ∑ m_ρ/(s−ρ)‖ ≤ 520000·log X` on the closed `3/2`-disk. -/
theorem norm_logDeriv_sub_sum_diskZeros_le {f : ℂ → ℂ} {A : ℝ}
    (hf : DiskData f A) (t₀ : ℝ) {s : ℂ}
    (hs : s ∈ closedBall ((2:ℂ) + t₀*I) (3/2:ℝ)) (hfs : f s ≠ 0) :
    ‖deriv f s / f s
      - ∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
      ≤ 520000 * Real.log (A * (|t₀| + 2)) := by
  obtain ⟨h, hh_an, hh_fac, hh_ne⟩ := exists_diskData_factorization hf t₀
  set c : ℂ := (2:ℂ) + t₀ * I with hcdef
  set X : ℝ := A * (|t₀| + 2) with hXdef
  have hX2 : (2:ℝ) ≤ X := hf.scale_two_le t₀
  have hX0 : (0:ℝ) < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  set n : ℕ := ∑ ρ ∈ diskZeros f t₀, analyticOrderNatAt f ρ with hndef
  have hn : (n : ℝ) ≤ 112 * Real.log X := by
    have h0 := sum_ord_le_of_diskData hf t₀
      (F := diskZeros f t₀) (fun ρ hρ => ((mem_diskZeros hf).mp hρ).1)
    rw [hndef]
    push_cast
    exact h0
  have hs13 : s ∈ ball c (13/8 : ℝ) := by
    rw [mem_closedBall] at hs
    rw [mem_ball]
    linarith
  have hs13c : s ∈ closedBall c (13/8 : ℝ) := ball_subset_closedBall hs13
  have hball13_sub : ball c (13/8 : ℝ) ⊆ closedBall c (7/4 : ℝ) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  -- ‖h‖ on the 7/4-sphere
  have hsphere : ∀ z ∈ sphere c (7/4 : ℝ), ‖h z‖ ≤ 15 * X * 8^n := by
    intro z hz
    have hzU : z ∈ closedBall c (7/4 : ℝ) := sphere_subset_closedBall hz
    have hLz : ‖f z‖ ≤ 15 * X := hf.bd t₀ z hzU
    have hPz : ((1:ℝ)/8)^n ≤ ‖∏ ρ ∈ diskZeros f t₀,
        (z - ρ) ^ analyticOrderNatAt f ρ‖ := by
      rw [norm_prod, hndef, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun ρ _ => by positivity) (fun ρ hρ => ?_)
      rw [norm_pow]
      refine pow_le_pow_left₀ (by norm_num) ?_ _
      have hρc : dist ρ c ≤ 13/8 :=
        mem_closedBall.mp ((mem_diskZeros hf).mp hρ).1
      have hzc : dist z c = 7/4 := mem_sphere.mp hz
      have htri := dist_triangle z ρ c
      rw [← dist_eq_norm]
      linarith
    have h8n : (0:ℝ) < (1/8:ℝ)^n := by positivity
    have h1 : (1/8:ℝ)^n * ‖h z‖ ≤ 15 * X := by
      calc (1/8:ℝ)^n * ‖h z‖
          ≤ ‖∏ ρ ∈ diskZeros f t₀, (z - ρ) ^ analyticOrderNatAt f ρ‖ * ‖h z‖ :=
            mul_le_mul_of_nonneg_right hPz (norm_nonneg _)
        _ = ‖f z‖ := by rw [hh_fac z hzU, norm_mul]
        _ ≤ 15 * X := hLz
    have h2 : ‖h z‖ ≤ 15 * X / (1/8:ℝ)^n := (le_div_iff₀' h8n).mpr h1
    calc ‖h z‖ ≤ 15 * X / (1/8:ℝ)^n := h2
      _ = 15 * X * 8^n := by
          rw [one_div, inv_pow, div_eq_mul_inv, inv_inv]
  -- maximum principle
  have hball_bound : ∀ z ∈ closedBall c (7/4 : ℝ), ‖h z‖ ≤ 15 * X * 8^n := by
    intro z hz
    have hd : DiffContOnCl ℂ h (ball c (7/4 : ℝ)) := by
      refine ⟨fun w hw => (hh_an w
        (ball_subset_closedBall hw)).differentiableAt.differentiableWithinAt, ?_⟩
      rw [closure_ball c (by norm_num : (7/4:ℝ) ≠ 0)]
      exact fun w hw => (hh_an w hw).continuousAt.continuousWithinAt
    have hfr : ∀ w ∈ frontier (ball c (7/4 : ℝ)), ‖h w‖ ≤ 15 * X * 8^n := by
      rw [frontier_ball c (by norm_num : (7/4:ℝ) ≠ 0)]
      exact hsphere
    have hcl : z ∈ closure (ball c (7/4 : ℝ)) := by
      rw [closure_ball c (by norm_num : (7/4:ℝ) ≠ 0)]
      exact hz
    exact Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd hfr hcl
  -- lower bound at the center
  have hcU : c ∈ closedBall c (7/4 : ℝ) := mem_closedBall_self (by norm_num)
  have hc13 : c ∈ closedBall c (13/8 : ℝ) := mem_closedBall_self (by norm_num)
  have hLc : 1/6 ≤ ‖f c‖ := hf.low t₀
  have hPc : ‖∏ ρ ∈ diskZeros f t₀,
      (c - ρ) ^ analyticOrderNatAt f ρ‖ ≤ 2^n := by
    rw [norm_prod, hndef, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun ρ _ => by positivity) (fun ρ hρ => ?_)
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    have hρc : dist ρ c ≤ 13/8 :=
      mem_closedBall.mp ((mem_diskZeros hf).mp hρ).1
    rw [← dist_eq_norm, dist_comm]
    linarith
  have hhc : (1/6:ℝ) * (1/2)^n ≤ ‖h c‖ := by
    have heq : ‖f c‖ = ‖∏ ρ ∈ diskZeros f t₀,
        (c - ρ) ^ analyticOrderNatAt f ρ‖ * ‖h c‖ := by
      rw [hh_fac c hcU, norm_mul]
    have h2n : (0:ℝ) < (2:ℝ)^n := by positivity
    have h1 : 1/6 ≤ 2^n * ‖h c‖ := by
      have h2 : ‖∏ ρ ∈ diskZeros f t₀,
          (c - ρ) ^ analyticOrderNatAt f ρ‖ * ‖h c‖ ≤ 2^n * ‖h c‖ :=
        mul_le_mul_of_nonneg_right hPc (norm_nonneg _)
      linarith [heq ▸ hLc]
    have hhalf : ((1/2:ℝ))^n * 2^n = 1 := by
      rw [← mul_pow]; norm_num
    have h3 := mul_le_mul_of_nonneg_left h1
      (le_of_lt (pow_pos (by norm_num : (0:ℝ) < 1/2) n))
    nlinarith [h3, hhalf]
  -- the `Re log` bound
  have hM0 : (0:ℝ) < 325 * Real.log X := by linarith
  have hre : ∀ z ∈ ball c (13/8 : ℝ),
      Real.log ‖h z‖ - Real.log ‖h c‖ ≤ 325 * Real.log X := by
    intro z hz
    have hz74 : z ∈ closedBall c (7/4 : ℝ) := hball13_sub hz
    have hz13 : z ∈ closedBall c (13/8 : ℝ) := ball_subset_closedBall hz
    have hpos : 0 < ‖h z‖ := norm_pos_iff.mpr (hh_ne z hz13)
    have hposc : 0 < ‖h c‖ := norm_pos_iff.mpr (hh_ne c hc13)
    have h1 : Real.log ‖h z‖ ≤ Real.log (15 * X * 8^n) :=
      Real.log_le_log hpos (hball_bound z hz74)
    have h2 : Real.log ((1/6:ℝ) * (1/2)^n) ≤ Real.log ‖h c‖ :=
      Real.log_le_log (by positivity) hhc
    have h3 : Real.log (15 * X * 8^n)
        = Real.log 15 + Real.log X + n * Real.log 8 := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (ne_of_gt hX0), Real.log_pow]
    have h4 : Real.log ((1/6:ℝ) * (1/2)^n)
        = -Real.log 6 - n * Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
        one_div, Real.log_inv, one_div, Real.log_inv]
      ring
    have h45 : Real.log 15 + Real.log 6 = Real.log 90 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have h16 : Real.log 8 + Real.log 2 = Real.log 16 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have h6 : Real.log (90 * X) ≤ 8 * Real.log X := log_ninety_mul_le hX2
    have h7 : Real.log (90 * X) = Real.log 90 + Real.log X :=
      Real.log_mul (by norm_num) (ne_of_gt hX0)
    have h8 : Real.log 16 ≤ 2.78 := log_sixteen_le
    have h16nn : (0:ℝ) ≤ Real.log 16 := Real.log_nonneg (by norm_num)
    have h9 : (n:ℝ) * Real.log 16 ≤ 112 * Real.log X * 2.78 :=
      mul_le_mul hn h8 h16nn (by linarith)
    have h10 : (n:ℝ) * Real.log 8 + n * Real.log 2 = n * Real.log 16 := by
      rw [← h16]
      ring
    linarith
  -- Borel–Carathéodory + Schwarz
  have hbound := norm_logDeriv_le_of_log_norm_bound hM0
    (fun z hz => hh_an z (hball13_sub hz))
    (fun z hz => hh_ne z (ball_subset_closedBall hz)) hre hs
  have hhs : h s ≠ 0 := hh_ne s hs13c
  have hsplit := logDeriv_split hf t₀ hh_an hh_fac hs13 hfs hhs
  rw [hsplit]
  have hfinal : (∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℂ) / (s - ρ))
      + deriv h s / h s
      - ∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
      = deriv h s / h s := by ring
  rw [hfinal]
  calc ‖deriv h s / h s‖ ≤ 1600 * (325 * Real.log X) := hbound
    _ = 520000 * Real.log X := by ring

/-- Grid cover, closed-edge variant: allows zeros with `Re ρ = 1`
(the eta function has them). -/
lemma exists_grid_cover' {T t₀ : ℝ} (h1 : T ≤ t₀) (h2 : t₀ ≤ T + 1) {ρ : ℂ}
    (hre : 7/16 < ρ.re) (hre1 : ρ.re ≤ 1)
    (hρ : ρ ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ)) :
    ∃ j ∈ Finset.range 7,
      ρ ∈ closedBall ((2:ℂ) + ((T - 1 + (j:ℝ)/2 : ℝ) : ℂ) * I) (13/8 : ℝ) := by
  have hd : (ρ.re - 2)^2 + (ρ.im - t₀)^2 ≤ (13/8:ℝ)^2 := by
    have h3 : ‖ρ - ((2:ℂ) + t₀ * I)‖ ≤ 13/8 := by
      rw [← Complex.dist_eq]
      exact mem_closedBall.mp hρ
    have h4 := sq_add_sq_le_of_norm_le h3
    have hre' : (ρ - ((2:ℂ) + t₀ * I)).re = ρ.re - 2 := by simp
    have him' : (ρ - ((2:ℂ) + t₀ * I)).im = ρ.im - t₀ := by simp
    rw [hre', him'] at h4
    exact h4
  have hmem : ∀ γ' : ℝ, (ρ.re - 2)^2 + (ρ.im - γ')^2 ≤ (13/8:ℝ)^2 →
      ρ ∈ closedBall ((2:ℂ) + γ' * I) (13/8 : ℝ) := by
    intro γ' hγ'
    rw [mem_closedBall, Complex.dist_eq]
    apply norm_le_of_sq_le (by norm_num)
    have hre' : (ρ - ((2:ℂ) + γ' * I)).re = ρ.re - 2 := by simp
    have him' : (ρ - ((2:ℂ) + γ' * I)).im = ρ.im - γ' := by simp
    rw [hre', him']
    exact hγ'
  rcases le_or_gt ρ.im (T - 1) with hlow | hmid
  · refine ⟨0, Finset.mem_range.mpr (by norm_num), ?_⟩
    apply hmem
    have h5 : 0 ≤ (T - 1) - ρ.im := by linarith
    have h6 : (T - 1) - ρ.im ≤ t₀ - ρ.im := by linarith
    have h7 : ((T - 1) - ρ.im)^2 ≤ (t₀ - ρ.im)^2 := by nlinarith
    push_cast
    nlinarith [hd, h7]
  rcases le_or_gt (T + 2) ρ.im with hhigh | hin
  · refine ⟨6, Finset.mem_range.mpr (by norm_num), ?_⟩
    apply hmem
    have h5 : 0 ≤ ρ.im - (T + 2) := by linarith
    have h6 : ρ.im - (T + 2) ≤ ρ.im - t₀ := by linarith
    have h7 : (ρ.im - (T + 2))^2 ≤ (ρ.im - t₀)^2 := by nlinarith
    push_cast
    nlinarith [hd, h7]
  · set x : ℝ := 2 * (ρ.im - (T - 1)) with hxdef
    have hx0 : 0 ≤ x := by rw [hxdef]; linarith
    have hx6 : x < 6 := by rw [hxdef]; linarith
    have hround := abs_sub_round x
    have hrnn : 0 ≤ round x := by
      rw [round_eq]
      apply Int.le_floor.mpr
      push_cast
      linarith
    refine ⟨(round x).toNat, Finset.mem_range.mpr ?_, ?_⟩
    · have h7 := abs_le.mp hround
      have h8 : (round x : ℝ) < 7 := by linarith [h7.1]
      have h9 : round x < 7 := by exact_mod_cast h8
      omega
    · apply hmem
      have hcast : (((round x).toNat : ℕ) : ℝ) = (round x : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg hrnn
      rw [hcast]
      have h10 : ρ.im - (T - 1 + (round x : ℝ)/2) = (x - round x)/2 := by
        rw [hxdef]; ring
      have h9 : |ρ.im - (T - 1 + (round x : ℝ)/2)| ≤ 1/4 := by
        rw [h10, abs_div]
        have h2abs : |(2:ℝ)| = 2 := by norm_num
        rw [h2abs]
        linarith
      have h11 : (ρ.im - (T - 1 + (round x : ℝ)/2))^2 ≤ (1/4:ℝ)^2 := by
        have := abs_le.mp h9
        nlinarith
      have h12 : (ρ.re - 2)^2 ≤ (25/16:ℝ)^2 := by
        nlinarith [mul_pos (by linarith : (0:ℝ) < ρ.re - 7/16)
          (by linarith : (0:ℝ) < 57/16 - ρ.re)]
      nlinarith [h11, h12]

/-- Zeros of a `DiskData` function have real part at most `1`. -/
lemma re_le_one_of_zero {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) {ρ : ℂ}
    (hρ : f ρ = 0) : ρ.re ≤ 1 := by
  by_contra hgt
  push Not at hgt
  exact hf.nz ρ hgt hρ

/-- Cardinality bound for the disk-zero finset. -/
lemma card_diskZeros_le {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) (t₀ : ℝ) :
    ((diskZeros f t₀).card : ℝ) ≤ 112 * Real.log (A * (|t₀| + 2)) := by
  have h1 : ((diskZeros f t₀).card : ℝ)
      ≤ (∑ ρ ∈ diskZeros f t₀, analyticOrderNatAt f ρ : ℝ) := by
    rw [Finset.card_eq_sum_ones]
    push_cast
    exact Finset.sum_le_sum fun ρ hρ => by
      exact_mod_cast one_le_ord_of_mem_diskZeros hf hρ
  exact h1.trans (sum_ord_le_of_diskData hf t₀
    (fun ρ hρ => ((mem_diskZeros hf).mp hρ).1))

set_option maxHeartbeats 1000000 in
/-- **Generic good heights.**  For `T ≥ 2` there is `t₀ ∈ [T, T+1]` at distance
`≥ 1/(2000·log(A(T+4)))` from every member of `Γex` (assumed small), with
`f(σ+it₀) ≠ 0` and `‖f′/f(σ+it₀)‖ ≤ 10⁶·log²(A(T+4))` for all `σ ∈ [1/2, 3]`. -/
theorem exists_good_height {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) {T : ℝ}
    (hT : 2 ≤ T) (Γex : Finset ℝ)
    (hΓex : (Γex.card : ℝ) ≤ 16 * Real.log (A * (T + 4))) :
    ∃ t₀ : ℝ, T ≤ t₀ ∧ t₀ ≤ T + 1 ∧
      (∀ γ ∈ Γex, 1 / (2000 * Real.log (A * (T + 4))) ≤ |t₀ - γ|) ∧
      ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 3 →
        f ((σ:ℂ) + t₀ * I) ≠ 0 ∧
        ‖deriv f ((σ:ℂ) + t₀ * I) / f ((σ:ℂ) + t₀ * I)‖
          ≤ 1000000 * Real.log (A * (T + 4)) ^ 2 := by
  classical
  set W : Finset ℂ := (Finset.range 7).biUnion
    (fun j => diskZeros f (T - 1 + (j:ℝ)/2)) with hWdef
  set Γ : Finset ℝ := W.image Complex.im ∪ Γex with hΓdef
  have hA1 : (1:ℝ) ≤ A := hf.one_le
  have hY0 : (0:ℝ) < A * (T + 4) := by nlinarith
  set logY : ℝ := Real.log (A * (T + 4)) with hlogYdef
  have hlogY1 : 1 ≤ logY := by
    rw [hlogYdef, Real.le_log_iff_exp_le hY0]
    have hexp := Real.exp_one_lt_d9
    nlinarith
  have hlogY0 : (0:ℝ) < logY := by linarith
  -- census cardinality
  have hcardW : (W.card : ℝ) ≤ 784 * logY := by
    have h1 : W.card ≤ ∑ j ∈ Finset.range 7,
        (diskZeros f (T - 1 + (j:ℝ)/2)).card := Finset.card_biUnion_le
    have h2 : ∀ j ∈ Finset.range 7,
        ((diskZeros f (T - 1 + (j:ℝ)/2)).card : ℝ) ≤ 112 * logY := by
      intro j hj
      have hj6 : (j:ℝ) ≤ 6 := by
        exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      have h3 := card_diskZeros_le hf (T - 1 + (j:ℝ)/2)
      have habs : |T - 1 + (j:ℝ)/2| = T - 1 + (j:ℝ)/2 :=
        abs_of_nonneg (by linarith)
      have h4 : Real.log (A * (|T - 1 + (j:ℝ)/2| + 2)) ≤ logY := by
        rw [habs, hlogYdef]
        apply Real.log_le_log (by nlinarith)
        nlinarith
      linarith
    calc (W.card : ℝ)
        ≤ (∑ j ∈ Finset.range 7, (diskZeros f (T - 1 + (j:ℝ)/2)).card : ℕ) := by
          exact_mod_cast h1
      _ = ∑ j ∈ Finset.range 7,
            ((diskZeros f (T - 1 + (j:ℝ)/2)).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _j ∈ Finset.range 7, 112 * logY := Finset.sum_le_sum h2
      _ = 784 * logY := by
          rw [Finset.sum_const, Finset.card_range]
          ring
  have hcardΓ : (Γ.card : ℝ) ≤ 800 * logY := by
    have h1 : Γ.card ≤ (W.image Complex.im).card + Γex.card := by
      rw [hΓdef]
      exact Finset.card_union_le _ _
    have h2 : (W.image Complex.im).card ≤ W.card := Finset.card_image_le
    have h3 : ((W.image Complex.im).card : ℝ) + (Γex.card : ℝ) ≤ 800 * logY := by
      have h4 : ((W.image Complex.im).card : ℝ) ≤ 784 * logY :=
        le_trans (by exact_mod_cast h2) hcardW
      linarith
    calc (Γ.card : ℝ) ≤ ((W.image Complex.im).card + Γex.card : ℕ) := by
          exact_mod_cast h1
      _ = ((W.image Complex.im).card : ℝ) + (Γex.card : ℝ) := by push_cast; rfl
      _ ≤ 800 * logY := h3
  -- the good height
  obtain ⟨t₀, ht₀1, ht₀2, hgap⟩ := exists_gap_point Γ T
  set δ : ℝ := 1/(2*(Γ.card + 1) : ℝ) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδbig : 1 / (2000 * logY) ≤ δ := by
    rw [hδdef]
    apply one_div_le_one_div_of_le (by positivity)
    have : (Γ.card : ℝ) + 1 ≤ 800 * logY + 1 := by linarith
    nlinarith
  refine ⟨t₀, ht₀1, ht₀2, ?_, ?_⟩
  · intro γ hγ
    have hγΓ : γ ∈ Γ := by
      rw [hΓdef]
      exact Finset.mem_union_right _ hγ
    exact le_trans hδbig (hgap γ hγΓ)
  intro σ hσ1 hσ2
  set s : ℂ := (σ:ℂ) + (t₀:ℝ) * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hsim : s.im = t₀ := by simp [hsdef]
  have hs32 : s ∈ closedBall ((2:ℂ) + t₀ * I) (3/2 : ℝ) := by
    rw [mem_closedBall, Complex.dist_eq]
    have h1 : s - ((2:ℂ) + t₀ * I) = ((σ - 2 : ℝ) : ℂ) := by
      rw [hsdef]
      push_cast
      ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  -- any disk zero with `Re > 7/16` sits at an ordinate of the census
  have havoid : ∀ ρ ∈ diskZeros f t₀, 7/16 < ρ.re → δ ≤ |t₀ - ρ.im| := by
    intro ρ hρ hρre
    obtain ⟨hρball, hρzero⟩ := (mem_diskZeros hf).mp hρ
    have hρre1 : ρ.re ≤ 1 := re_le_one_of_zero hf hρzero
    obtain ⟨j, hjmem, hjball⟩ := exists_grid_cover' ht₀1 ht₀2 hρre hρre1 hρball
    have hρW : ρ ∈ W := by
      rw [hWdef]
      exact Finset.mem_biUnion.mpr
        ⟨j, hjmem, (mem_diskZeros hf).mpr ⟨hjball, hρzero⟩⟩
    apply hgap ρ.im
    rw [hΓdef]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hρW)
  -- nonvanishing on the segment
  have hfs : f s ≠ 0 := by
    intro h0
    rcases le_or_gt σ 1 with hle | hgt
    · have hs138 : s ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ) :=
        closedBall_subset_closedBall (by norm_num) hs32
      have hsK : s ∈ diskZeros f t₀ := (mem_diskZeros hf).mpr ⟨hs138, h0⟩
      have h716 : 7/16 < s.re := by rw [hsre]; linarith
      have h1 := havoid s hsK h716
      rw [hsim, sub_self, abs_zero] at h1
      linarith
    · exact hf.nz s (by rw [hsre]; exact hgt) h0
  -- Landau expansion at `s`
  have hmain := norm_logDeriv_sub_sum_diskZeros_le hf t₀ hs32 hfs
  have hXY : Real.log (A * (|t₀| + 2)) ≤ logY := by
    have habs : |t₀| = t₀ := abs_of_nonneg (by linarith)
    rw [habs, hlogYdef]
    apply Real.log_le_log (by nlinarith)
    nlinarith
  -- termwise bound on the partial-fraction sum
  have hterm : ∀ ρ ∈ diskZeros f t₀,
      ‖(analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
        ≤ (analyticOrderNatAt f ρ : ℝ) * (2016 * logY) := by
    intro ρ hρ
    have hlow : min (1/16 : ℝ) δ ≤ ‖s - ρ‖ := by
      rcases le_or_gt ρ.re (7/16) with hcase | hcase
      · have h2 : (s - ρ).re = σ - ρ.re := by
          rw [Complex.sub_re, hsre]
        have h1 : 1/16 ≤ |(s - ρ).re| := by
          rw [h2, abs_of_nonneg (by linarith)]
          linarith
        calc min (1/16:ℝ) δ ≤ 1/16 := min_le_left _ _
          _ ≤ |(s - ρ).re| := h1
          _ ≤ ‖s - ρ‖ := Complex.abs_re_le_norm _
      · have h1 := havoid ρ hρ hcase
        have h2 : (s - ρ).im = t₀ - ρ.im := by
          rw [Complex.sub_im, hsim]
        calc min (1/16:ℝ) δ ≤ δ := min_le_right _ _
          _ ≤ |t₀ - ρ.im| := h1
          _ = |(s - ρ).im| := by rw [h2]
          _ ≤ ‖s - ρ‖ := Complex.abs_im_le_norm _
    have hmin0 : (0:ℝ) < min (1/16:ℝ) δ := lt_min (by norm_num) hδ0
    have hmininv : 1/(min (1/16:ℝ) δ) ≤ 2016 * logY := by
      rcases le_total (1/16:ℝ) δ with hmd | hmd
      · rw [min_eq_left hmd]
        nlinarith
      · rw [min_eq_right hmd, hδdef, one_div_one_div]
        nlinarith [hcardΓ]
    have hinv : 1/‖s - ρ‖ ≤ 2016 * logY :=
      le_trans (one_div_le_one_div_of_le hmin0 hlow) hmininv
    rw [norm_div, Complex.norm_natCast, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
  -- sum bound
  have hsum : ‖∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
      ≤ 112 * logY * (2016 * logY) := by
    have hmass : (∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℝ))
        ≤ 112 * logY := by
      have h1 := sum_ord_le_of_diskData hf t₀
        (F := diskZeros f t₀) (fun ρ hρ => ((mem_diskZeros hf).mp hρ).1)
      have h2 : (∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℝ))
          = ((∑ ρ ∈ diskZeros f t₀, analyticOrderNatAt f ρ : ℕ) : ℝ) := by
        push_cast
        rfl
      rw [h2]
      calc ((∑ ρ ∈ diskZeros f t₀, analyticOrderNatAt f ρ : ℕ) : ℝ)
          ≤ 112 * Real.log (A * (|t₀| + 2)) := by exact_mod_cast h1
        _ ≤ 112 * logY := by linarith
    calc ‖∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ diskZeros f t₀,
          ‖(analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ diskZeros f t₀,
          (analyticOrderNatAt f ρ : ℝ) * (2016 * logY) := Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℝ)) * (2016 * logY) := by
          rw [← Finset.sum_mul]
      _ ≤ 112 * logY * (2016 * logY) := by
          apply mul_le_mul_of_nonneg_right hmass
          positivity
  refine ⟨hfs, ?_⟩
  calc ‖deriv f s / f s‖
      = ‖(deriv f s / f s
        - ∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℂ) / (s - ρ))
        + ∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ := by
        congr 1
        ring
    _ ≤ ‖deriv f s / f s
          - ∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
        + ‖∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ :=
        norm_add_le _ _
    _ ≤ 520000 * Real.log (A * (|t₀| + 2)) + 112 * logY * (2016 * logY) :=
        add_le_add hmain hsum
    _ ≤ 1000000 * logY ^ 2 := by nlinarith
    _ = 1000000 * Real.log (A * (T + 4)) ^ 2 := by rw [hlogYdef]

end GenericDisk

/-! ### Rectangle residue calculus for `y^s/(s(s−ρ))` -/

section RectResidue

/-- A point of the closed rectangle that is not strictly inside lies on the frame. -/
lemma mem_rectFrame_of_boundary {z w p : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hp : p ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]])
    (hnot : ¬ (z.re < p.re ∧ p.re < w.re ∧ z.im < p.im ∧ p.im < w.im)) :
    p ∈ rectFrame z w := by
  have hpmem := hp
  rw [Complex.mem_reProdIm, Set.uIcc_of_le hre, Set.uIcc_of_le him] at hpmem
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hpmem
  have hre_mem : p.re ∈ [[z.re, w.re]] := by
    rw [Set.uIcc_of_le hre]; exact ⟨h1, h2⟩
  have him_mem : p.im ∈ [[z.im, w.im]] := by
    rw [Set.uIcc_of_le him]; exact ⟨h3, h4⟩
  have key : (p.re = z.re ∨ p.re = w.re) ∨ (p.im = z.im ∨ p.im = w.im) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨ha, hb⟩, hc, hd⟩ := hcon
    exact hnot ⟨lt_of_le_of_ne h1 (Ne.symm ha), lt_of_le_of_ne h2 hb,
      lt_of_le_of_ne h3 (Ne.symm hc), lt_of_le_of_ne h4 hd⟩
  rcases key with hv | hh
  · have := mem_rectFrame_vert (z := z) (w := w) him_mem hv
    rwa [Complex.re_add_im] at this
  · have := mem_rectFrame_horiz (z := z) (w := w) hre_mem hh
    rwa [Complex.re_add_im] at this

/-- Interior pole: `∮ y^s/(s(s−p)) = 2πi·y^p/p` over a rectangle in the right
half-plane containing `p` strictly inside. -/
lemma rectInt_ys_pole {y : ℝ} (hy : 0 < y) {z w p : ℂ} (hz0 : 0 < z.re)
    (h1 : z.re < p.re) (h2 : p.re < w.re) (h3 : z.im < p.im) (h4 : p.im < w.im) :
    rectInt (fun s => (y:ℂ) ^ s / (s * (s - p))) z w
      = 2 * π * I * ((y:ℂ) ^ p / p) := by
  have hyC : (y:ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hy.ne'
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at h1
    simp at h1
    linarith
  have hframe_ne : ∀ s ∈ rectFrame z w, s ≠ 0 ∧ s ≠ p := by
    intro s hs
    have hsre : z.re ≤ s.re := by
      have := (rectFrame_subset z w hs)
      rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith), Set.uIcc_of_le (by linarith)] at this
      exact this.1.1
    constructor
    · intro h
      rw [h] at hsre
      simp at hsre
      linarith
    · intro h
      exact notMem_rectFrame h1 h2 h3 h4 (h ▸ hs)
  have hentire : Differentiable ℂ (fun s : ℂ => (y:ℂ) ^ s) := fun s =>
    differentiableAt_id.const_cpow (Or.inl hyC)
  -- the split on the frame
  have hsplit : ∀ s ∈ rectFrame z w,
      (y:ℂ) ^ s / (s * (s - p))
        = p⁻¹ * ((y:ℂ) ^ s / (s - p)) + (-p⁻¹) * ((y:ℂ) ^ s / s) := by
    intro s hs
    obtain ⟨hs0, hsp⟩ := hframe_ne s hs
    have hsp' : s - p ≠ 0 := sub_ne_zero.mpr hsp
    field_simp
    ring
  have hcont1 : ContinuousOn (fun s : ℂ => p⁻¹ * ((y:ℂ) ^ s / (s - p)))
      (rectFrame z w) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div (hentire.continuous.continuousOn)
      ((continuous_id.sub continuous_const).continuousOn)
    intro s hs
    exact sub_ne_zero.mpr (hframe_ne s hs).2
  have hcont2 : ContinuousOn (fun s : ℂ => (-p⁻¹) * ((y:ℂ) ^ s / s))
      (rectFrame z w) := by
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div (hentire.continuous.continuousOn)
      continuous_id.continuousOn
    intro s hs
    exact (hframe_ne s hs).1
  rw [rectInt_congr hsplit, rectInt_add hcont1 hcont2,
    rectInt_const_mul, rectInt_const_mul]
  -- first piece: Cauchy
  have hc1 : rectInt (fun s => (y:ℂ) ^ s / (s - p)) z w = 2 * π * I * (y:ℂ) ^ p :=
    rectInt_cauchy hentire h1 h2 h3 h4
  -- second piece: Goursat (0 outside the rectangle)
  have hc2 : rectInt (fun s => (y:ℂ) ^ s / s) z w = 0 := by
    apply rectInt_eq_zero (∅ : Set ℂ) Set.countable_empty
    · apply ContinuousOn.div (hentire.continuous.continuousOn)
        continuous_id.continuousOn
      intro s hs
      rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith : z.re ≤ w.re)] at hs
      show s ≠ 0
      intro h0
      have hsre : z.re ≤ s.re := hs.1.1
      rw [h0] at hsre
      simp at hsre
      linarith
    · intro x hx
      obtain ⟨hxm, -⟩ := hx
      rw [Complex.mem_reProdIm] at hxm
      have hxre : min z.re w.re < x.re := hxm.1.1
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0] at hxre
        simp only [Complex.zero_re] at hxre
        have h5 : min z.re w.re = z.re := min_eq_left (by linarith)
        rw [h5] at hxre
        linarith
      exact (hentire.differentiableAt).div differentiableAt_id hx0
  rw [hc1, hc2, mul_zero, add_zero]
  field_simp

/-- Exterior pole: the same boundary integral vanishes when `p` is outside
the closed rectangle. -/
lemma rectInt_ys_nopole {y : ℝ} (hy : 0 < y) {z w p : ℂ} (hz0 : 0 < z.re)
    (hzw : z.re ≤ w.re)
    (hp : p ∉ [[z.re, w.re]] ×ℂ [[z.im, w.im]]) :
    rectInt (fun s => (y:ℂ) ^ s / (s * (s - p))) z w = 0 := by
  have hyC : (y:ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hy.ne'
  have hentire : Differentiable ℂ (fun s : ℂ => (y:ℂ) ^ s) := fun s =>
    differentiableAt_id.const_cpow (Or.inl hyC)
  have hne : ∀ s ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], s ≠ 0 ∧ s ≠ p := by
    intro s hs
    constructor
    · intro h0
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hzw] at hs
      have : z.re ≤ s.re := hs.1.1
      rw [h0] at this
      simp at this
      linarith
    · intro hp'
      exact hp (hp' ▸ hs)
  apply rectInt_eq_zero (∅ : Set ℂ) Set.countable_empty
  · apply ContinuousOn.div (hentire.continuous.continuousOn)
      ((continuous_id.mul (continuous_id.sub continuous_const)).continuousOn)
    intro s hs
    exact mul_ne_zero (hne s hs).1 (sub_ne_zero.mpr (hne s hs).2)
  · intro x hx
    obtain ⟨hxm, -⟩ := hx
    rw [Complex.mem_reProdIm] at hxm
    have hxmem : x ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := by
      rw [Complex.mem_reProdIm]
      exact ⟨Set.Ioo_subset_Icc_self hxm.1, Set.Ioo_subset_Icc_self hxm.2⟩
    have h0 := (hne x hxmem).1
    have hp' := sub_ne_zero.mpr (hne x hxmem).2
    exact (hentire.differentiableAt).div
      (differentiableAt_id.mul (differentiableAt_id.sub (differentiableAt_const p)))
      (mul_ne_zero h0 hp')

end RectResidue

/-! ### The strip residue theorem -/

section Strip

set_option maxHeartbeats 1000000 in
/-- **Strip residue theorem.**  Over a height-`≤1` strip of the standard
rectangle avoiding zeros on its frame, the boundary integral of
`(f′/f)·y^s/s` collects `2πi·m_ρ·y^ρ/ρ` over the disk zeros strictly inside. -/
theorem rectInt_strip {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) {y : ℝ} (hy : 1 < y)
    {σ₁ cc t_lo t_hi : ℝ} (hσ : 9/16 ≤ σ₁) (hσc : σ₁ < cc) (hcc : cc ≤ 5/4)
    (hlo : t_lo < t_hi) (hgap : t_hi - t_lo ≤ 1)
    (hframe : ∀ s ∈ rectFrame ((σ₁:ℂ) + t_lo*I) ((cc:ℂ) + t_hi*I), f s ≠ 0) :
    rectInt (fun s => (deriv f s / f s) * ((y:ℂ)^s / s))
        ((σ₁:ℂ) + t_lo*I) ((cc:ℂ) + t_hi*I)
      = (2*π*I) * ∑ ρ ∈ (diskZeros f ((t_lo+t_hi)/2)).filter
            (fun ρ => σ₁ < ρ.re ∧ ρ.re < cc ∧ t_lo < ρ.im ∧ ρ.im < t_hi),
          (analyticOrderNatAt f ρ : ℂ) * ((y:ℂ)^ρ / ρ) := by
  classical
  have hy0 : (0:ℝ) < y := by linarith
  set τc : ℝ := (t_lo + t_hi)/2 with hτcdef
  set c₀ : ℂ := (2:ℂ) + τc * I with hc₀def
  set z : ℂ := (σ₁:ℂ) + t_lo*I with hzdef
  set w : ℂ := (cc:ℂ) + t_hi*I with hwdef
  have hzre : z.re = σ₁ := re_coord σ₁ t_lo
  have hzim : z.im = t_lo := im_coord σ₁ t_lo
  have hwre : w.re = cc := re_coord cc t_hi
  have hwim : w.im = t_hi := im_coord cc t_hi
  have hrele : z.re ≤ w.re := by rw [hzre, hwre]; linarith
  have himle : z.im ≤ w.im := by rw [hzim, hwim]; linarith
  -- geometry: closed rectangle inside `ball c₀ (13/8)`
  have hgeom : ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ cc → t_lo ≤ s.im → s.im ≤ t_hi →
      s ∈ ball c₀ (13/8 : ℝ) := by
    intro s h1 h2 h3 h4
    rw [mem_ball, Complex.dist_eq]
    have hre' : (s - c₀).re = s.re - 2 := by
      rw [hc₀def]; simp
    have him' : (s - c₀).im = s.im - τc := by
      rw [hc₀def]; simp
    have hsq : (s - c₀).re^2 + (s - c₀).im^2 ≤ (593/256 : ℝ) := by
      rw [hre', him']
      have hb1 : (s.re - 2)^2 ≤ (23/16)^2 := by nlinarith
      have hb2 : (s.im - τc)^2 ≤ (1/2)^2 := by
        rw [hτcdef]
        have hu1 : s.im - (t_lo+t_hi)/2 ≤ (t_hi - t_lo)/2 := by linarith
        have hu2 : -((t_hi - t_lo)/2) ≤ s.im - (t_lo+t_hi)/2 := by linarith
        have hd0 : (0:ℝ) ≤ (t_hi - t_lo)/2 := by linarith
        have hd1 : (t_hi - t_lo)/2 ≤ 1/2 := by linarith
        nlinarith [hu1, hu2, hd0, hd1]
      nlinarith
    have hnorm := norm_le_of_sq_le (a := Real.sqrt (593/256))
      (Real.sqrt_nonneg _)
      (by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 593/256)]; exact hsq)
    apply lt_of_le_of_lt hnorm
    rw [show (13/8 : ℝ) = Real.sqrt ((13/8)^2) from
      (Real.sqrt_sq (by norm_num)).symm]
    apply Real.sqrt_lt_sqrt (by norm_num)
    norm_num
  have hrect_ball : ∀ s ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]], s ∈ ball c₀ (13/8:ℝ) := by
    intro s hs
    rw [Complex.mem_reProdIm, Set.uIcc_of_le hrele, Set.uIcc_of_le himle] at hs
    exact hgeom s (hzre ▸ hs.1.1) (hwre ▸ hs.1.2) (hzim ▸ hs.2.1) (hwim ▸ hs.2.2)
  have hball74 : ball c₀ (13/8:ℝ) ⊆ closedBall c₀ (7/4:ℝ) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  have hframe_rect : rectFrame z w ⊆ [[z.re, w.re]] ×ℂ [[z.im, w.im]] :=
    rectFrame_subset z w
  -- the factorization
  obtain ⟨h, hh_an, hh_fac, hh_ne⟩ := exists_diskData_factorization hf τc
  set K : Finset ℂ := diskZeros f τc with hKdef
  set m : ℂ → ℕ := fun ρ => analyticOrderNatAt f ρ with hmdef
  -- zeros in `K` are off the frame
  have hKframe : ∀ ρ ∈ K, ρ ∉ rectFrame z w := by
    intro ρ hρ hmem
    exact hframe ρ hmem ((mem_diskZeros hf).mp hρ).2
  -- nonvanishing of `s`, `s−ρ` on the frame
  have hfr_ne : ∀ s ∈ rectFrame z w, s ≠ 0 ∧ ∀ ρ ∈ K, s - ρ ≠ 0 := by
    intro s hs
    have hsrect := hframe_rect hs
    rw [Complex.mem_reProdIm, Set.uIcc_of_le hrele, Set.uIcc_of_le himle] at hsrect
    constructor
    · intro h0
      have : σ₁ ≤ s.re := hzre ▸ hsrect.1.1
      rw [h0] at this
      simp at this
      linarith
    · intro ρ hρ
      rw [sub_ne_zero]
      intro hsρ
      exact hframe s hs (hsρ ▸ ((mem_diskZeros hf).mp hρ).2)
  -- the frame identity
  have hsplit : ∀ s ∈ rectFrame z w,
      (deriv f s / f s) * ((y:ℂ)^s / s)
        = (∑ ρ ∈ K, (m ρ : ℂ) * ((y:ℂ)^s / (s * (s - ρ))))
          + (deriv h s / h s) * ((y:ℂ)^s / s) := by
    intro s hs
    have hs13 : s ∈ ball c₀ (13/8:ℝ) := hrect_ball s (hframe_rect hs)
    have hfs : f s ≠ 0 := hframe s hs
    have hhs : h s ≠ 0 := hh_ne s (ball_subset_closedBall hs13)
    have hld := logDeriv_split hf τc hh_an hh_fac hs13 hfs hhs
    rw [hld, add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro ρ hρ
    have hs0 := (hfr_ne s hs).1
    have hsρ := (hfr_ne s hs).2 ρ hρ
    field_simp
    ring
  -- continuity of the pieces on the frame
  have hyC : (y:ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hy0.ne'
  have hentire : Differentiable ℂ (fun s : ℂ => (y:ℂ) ^ s) := fun s =>
    differentiableAt_id.const_cpow (Or.inl hyC)
  have hcontK : ∀ ρ ∈ K, ContinuousOn
      (fun s => (m ρ : ℂ) * ((y:ℂ)^s / (s * (s - ρ)))) (rectFrame z w) := by
    intro ρ hρ
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.div (hentire.continuous.continuousOn)
      ((continuous_id.mul (continuous_id.sub continuous_const)).continuousOn)
    intro s hs
    exact mul_ne_zero (hfr_ne s hs).1 ((hfr_ne s hs).2 ρ hρ)
  have hcontsum : ContinuousOn
      (fun s => ∑ ρ ∈ K, (m ρ : ℂ) * ((y:ℂ)^s / (s * (s - ρ)))) (rectFrame z w) := by
    apply continuousOn_finsetSum
    intro ρ hρ
    exact hcontK ρ hρ
  have hcontG : ContinuousOn (fun s => (deriv h s / h s) * ((y:ℂ)^s / s))
      (rectFrame z w) := by
    apply ContinuousOn.mul
    · apply ContinuousOn.div
      · intro s hs
        have hs13 := hrect_ball s (hframe_rect hs)
        exact ((hh_an s (hball74 hs13)).deriv.continuousAt).continuousWithinAt
      · intro s hs
        have hs13 := hrect_ball s (hframe_rect hs)
        exact ((hh_an s (hball74 hs13)).continuousAt).continuousWithinAt
      · intro s hs
        exact hh_ne s (ball_subset_closedBall (hrect_ball s (hframe_rect hs)))
    · apply ContinuousOn.div (hentire.continuous.continuousOn)
        continuousOn_id
      intro s hs
      exact (hfr_ne s hs).1
  -- assemble the boundary integral
  rw [rectInt_congr hsplit, rectInt_add hcontsum hcontG]
  -- the analytic part vanishes
  have hG0 : rectInt (fun s => (deriv h s / h s) * ((y:ℂ)^s / s)) z w = 0 := by
    apply rectInt_eq_zero (∅ : Set ℂ) Set.countable_empty
    · intro s hs
      have hs13 := hrect_ball s hs
      have hs0 : s ≠ 0 := by
        rw [Complex.mem_reProdIm, Set.uIcc_of_le hrele, Set.uIcc_of_le himle] at hs
        intro h0
        have : σ₁ ≤ s.re := hzre ▸ hs.1.1
        rw [h0] at this
        simp at this
        linarith
      apply ContinuousWithinAt.mul
      · apply ContinuousWithinAt.div
        · exact ((hh_an s (hball74 hs13)).deriv.continuousAt).continuousWithinAt
        · exact ((hh_an s (hball74 hs13)).continuousAt).continuousWithinAt
        · exact hh_ne s (ball_subset_closedBall hs13)
      · apply ContinuousWithinAt.div
          (hentire.continuous.continuousAt).continuousWithinAt
          continuousAt_id.continuousWithinAt hs0
    · intro x hx
      obtain ⟨hxm, -⟩ := hx
      rw [Complex.mem_reProdIm] at hxm
      have hxrect : x ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := by
        rw [Complex.mem_reProdIm]
        exact ⟨Set.Ioo_subset_Icc_self hxm.1, Set.Ioo_subset_Icc_self hxm.2⟩
      have hx13 := hrect_ball x hxrect
      have hx0 : x ≠ 0 := by
        rw [Complex.mem_reProdIm, Set.uIcc_of_le hrele, Set.uIcc_of_le himle]
          at hxrect
        intro h0
        have : σ₁ ≤ x.re := hzre ▸ hxrect.1.1
        rw [h0] at this
        simp at this
        linarith
      apply DifferentiableAt.mul
      · exact ((hh_an x (hball74 hx13)).deriv.differentiableAt).div
          (hh_an x (hball74 hx13)).differentiableAt
          (hh_ne x (ball_subset_closedBall hx13))
      · exact (hentire.differentiableAt).div differentiableAt_id hx0
  rw [hG0, add_zero]
  -- residues term by term
  have hres : ∀ ρ ∈ K, rectInt (fun s => (m ρ : ℂ) * ((y:ℂ)^s / (s * (s - ρ)))) z w
      = if σ₁ < ρ.re ∧ ρ.re < cc ∧ t_lo < ρ.im ∧ ρ.im < t_hi
        then (2*π*I) * ((m ρ : ℂ) * ((y:ℂ)^ρ / ρ)) else 0 := by
    intro ρ hρ
    rw [rectInt_const_mul]
    by_cases hin : σ₁ < ρ.re ∧ ρ.re < cc ∧ t_lo < ρ.im ∧ ρ.im < t_hi
    · rw [if_pos hin]
      obtain ⟨hi1, hi2, hi3, hi4⟩ := hin
      have hp := rectInt_ys_pole hy0 (z := z) (w := w) (p := ρ)
        (by rw [hzre]; linarith) (by rw [hzre]; exact hi1) (by rw [hwre]; exact hi2)
        (by rw [hzim]; exact hi3) (by rw [hwim]; exact hi4)
      rw [hp]
      ring
    · rw [if_neg hin]
      have hout : ρ ∉ [[z.re, w.re]] ×ℂ [[z.im, w.im]] := by
        intro hmem
        apply hKframe ρ hρ
        apply mem_rectFrame_of_boundary hrele himle hmem
        rw [hzre, hwre, hzim, hwim]
        exact hin
      rw [rectInt_ys_nopole hy0 (by rw [hzre]; linarith) hrele hout]
      ring
  -- sum the residues
  have hsum : rectInt (fun s => ∑ ρ ∈ K, (m ρ : ℂ) * ((y:ℂ)^s / (s * (s - ρ)))) z w
      = ∑ ρ ∈ K, rectInt (fun s => (m ρ : ℂ) * ((y:ℂ)^s / (s * (s - ρ)))) z w :=
    rectInt_sum K hcontK
  rw [hsum]
  rw [Finset.sum_congr rfl hres]
  rw [Finset.sum_ite, Finset.sum_const, smul_zero, add_zero]
  rw [Finset.mul_sum]

end Strip

/-! ### The chain: stacking strips up the rectangle -/

section Chain

/-- Vertical split of the rectangle boundary integral at an intermediate
height `μ`. -/
lemma rectInt_vsplit {F : ℂ → ℂ} {z w : ℂ} {μ : ℝ} (hμ1 : z.im ≤ μ)
    (hμ2 : μ ≤ w.im)
    (hintL : IntervalIntegrable (fun t : ℝ => F ((z.re:ℂ) + t*I))
      MeasureTheory.volume z.im w.im)
    (hintR : IntervalIntegrable (fun t : ℝ => F ((w.re:ℂ) + t*I))
      MeasureTheory.volume z.im w.im) :
    rectInt F z w
      = rectInt F z ((w.re:ℂ) + μ*I) + rectInt F ((z.re:ℂ) + μ*I) w := by
  have hsub1 : Set.uIcc z.im μ ⊆ Set.uIcc z.im w.im := by
    apply Set.uIcc_subset_uIcc left_mem_uIcc
    rw [Set.mem_uIcc]
    left
    exact ⟨hμ1, hμ2⟩
  have hsub2 : Set.uIcc μ w.im ⊆ Set.uIcc z.im w.im := by
    apply Set.uIcc_subset_uIcc _ right_mem_uIcc
    rw [Set.mem_uIcc]
    left
    exact ⟨hμ1, hμ2⟩
  have haddR : (∫ t in z.im..μ, F ((w.re:ℂ)+t*I))
      + (∫ t in μ..w.im, F ((w.re:ℂ)+t*I))
      = ∫ t in z.im..w.im, F ((w.re:ℂ)+t*I) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hintR.mono_set hsub1) (hintR.mono_set hsub2)
  have haddL : (∫ t in z.im..μ, F ((z.re:ℂ)+t*I))
      + (∫ t in μ..w.im, F ((z.re:ℂ)+t*I))
      = ∫ t in z.im..w.im, F ((z.re:ℂ)+t*I) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hintL.mono_set hsub1) (hintL.mono_set hsub2)
  unfold rectInt
  simp only [re_coord, im_coord]
  rw [← haddR, ← haddL]
  ring

/-- Continuity of the strip integrand along a vertical segment on which `f`
does not vanish. -/
lemma contOn_vert_stripInt {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) {y : ℝ}
    (hy : 0 < y) {x : ℝ} (hx1 : 1/4 ≤ x) (hx2 : x ≤ 15/4) {a b : ℝ}
    (hnz : ∀ t ∈ Set.uIcc a b, f ((x:ℂ) + t*I) ≠ 0) :
    ContinuousOn (fun t : ℝ =>
      (deriv f ((x:ℂ)+t*I) / f ((x:ℂ)+t*I))
        * ((y:ℂ)^((x:ℂ)+t*I) / ((x:ℂ)+t*I))) (Set.uIcc a b) := by
  have hyC : (y:ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hy.ne'
  have hentire : Differentiable ℂ (fun s : ℂ => (y:ℂ) ^ s) := fun s =>
    differentiableAt_id.const_cpow (Or.inl hyC)
  have hbase : Continuous (fun t : ℝ => (x:ℂ) + t*I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hmem : ∀ t : ℝ, ((x:ℂ) + t*I) ∈ closedBall ((2:ℂ) + t*I) (7/4 : ℝ) := by
    intro t
    rw [mem_closedBall, Complex.dist_eq]
    have h1 : ((x:ℂ) + t*I) - ((2:ℂ) + t*I) = ((x - 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  apply ContinuousOn.mul
  · apply ContinuousOn.div
    · intro t ht
      have h1 : ContinuousAt (deriv f) ((fun u : ℝ => (x:ℂ)+u*I) t) :=
        (hf.diff t ((x:ℂ)+t*I) (hmem t)).deriv.continuousAt
      have h3 : ContinuousAt ((deriv f) ∘ (fun u : ℝ => (x:ℂ)+u*I)) t :=
        ContinuousAt.comp h1 hbase.continuousAt
      exact h3.continuousWithinAt
    · intro t ht
      have h1 : ContinuousAt f ((fun u : ℝ => (x:ℂ)+u*I) t) :=
        (hf.diff t ((x:ℂ)+t*I) (hmem t)).continuousAt
      have h3 : ContinuousAt (f ∘ (fun u : ℝ => (x:ℂ)+u*I)) t :=
        ContinuousAt.comp h1 hbase.continuousAt
      exact h3.continuousWithinAt
    · exact hnz
  · apply ContinuousOn.div
    · exact (hentire.continuous.comp hbase).continuousOn
    · exact hbase.continuousOn
    · intro t _
      exact coord_ne_zero_of_re (by linarith)

set_option maxHeartbeats 2000000 in
/-- **The chained residue theorem** over a stack of strips. -/
theorem rectInt_chain {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) {y : ℝ} (hy : 1 < y)
    {σ₁ cc : ℝ} (hσ : 9/16 ≤ σ₁) (hσc : σ₁ < cc) (hcc1 : 1 < cc) (hcc : cc ≤ 5/4)
    (τ : ℕ → ℝ) (m : ℕ)
    (hmono : ∀ j < m, τ j < τ (j+1))
    (hgap : ∀ j < m, τ (j+1) - τ j ≤ 1)
    (hlines : ∀ j ≤ m, ∀ σ ∈ Icc σ₁ cc, f ((σ:ℂ) + (τ j)*I) ≠ 0)
    (hleft : ∀ t ∈ Icc (τ 0) (τ m), f ((σ₁:ℂ) + t*I) ≠ 0) :
    rectInt (fun s => (deriv f s / f s) * ((y:ℂ)^s / s))
        ((σ₁:ℂ) + (τ 0)*I) ((cc:ℂ) + (τ m)*I)
      = (2*π*I) * ∑ k ∈ Finset.range m,
          ∑ ρ ∈ (diskZeros f ((τ k + τ (k+1))/2)).filter
            (fun ρ => σ₁ < ρ.re ∧ ρ.re < cc ∧ τ k < ρ.im ∧ ρ.im < τ (k+1)),
          (analyticOrderNatAt f ρ : ℂ) * ((y:ℂ)^ρ / ρ) := by
  induction m with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, mul_zero]
      unfold rectInt
      simp only [re_coord, im_coord, intervalIntegral.integral_same]
      ring
  | succ m ih =>
      -- monotonicity facts
      have hmono' : ∀ j < m, τ j < τ (j+1) := fun j hj => hmono j (by omega)
      have hgap' : ∀ j < m, τ (j+1) - τ j ≤ 1 := fun j hj => hgap j (by omega)
      have hlines' : ∀ j ≤ m, ∀ σ ∈ Icc σ₁ cc, f ((σ:ℂ) + (τ j)*I) ≠ 0 :=
        fun j hj => hlines j (by omega)
      have hchain : ∀ j ≤ m + 1, τ 0 ≤ τ j := by
        intro j hj
        induction j with
        | zero => exact le_refl _
        | succ i ihi =>
            have h1 : τ i < τ (i+1) := hmono i (by omega)
            have h2 := ihi (by omega)
            linarith
      have h0m : τ 0 ≤ τ m := hchain m (by omega)
      have hmm1 : τ m < τ (m+1) := hmono m (by omega)
      have h0m1 : τ 0 ≤ τ (m+1) := by linarith
      have hleft' : ∀ t ∈ Icc (τ 0) (τ m), f ((σ₁:ℂ) + t*I) ≠ 0 := by
        intro t ht
        exact hleft t ⟨ht.1, by linarith [ht.2]⟩
      -- integrability of the two vertical edges over the full range
      have hnzL : ∀ t ∈ Set.uIcc (τ 0) (τ (m+1)), f ((σ₁:ℂ) + t*I) ≠ 0 := by
        intro t ht
        rw [Set.uIcc_of_le h0m1] at ht
        exact hleft t ht
      have hnzR : ∀ t ∈ Set.uIcc (τ 0) (τ (m+1)), f ((cc:ℂ) + t*I) ≠ 0 := by
        intro t _
        apply hf.nz
        rw [re_coord]
        exact hcc1
      have hintL : IntervalIntegrable (fun t : ℝ =>
          (deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
            * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I)))
          MeasureTheory.volume (τ 0) (τ (m+1)) :=
        (contOn_vert_stripInt hf (by linarith) (by linarith) (by linarith)
          hnzL).intervalIntegrable
      have hintR : IntervalIntegrable (fun t : ℝ =>
          (deriv f ((cc:ℂ)+t*I) / f ((cc:ℂ)+t*I))
            * ((y:ℂ)^((cc:ℂ)+t*I) / ((cc:ℂ)+t*I)))
          MeasureTheory.volume (τ 0) (τ (m+1)) :=
        (contOn_vert_stripInt hf (by linarith) (by linarith) (by linarith)
          hnzR).intervalIntegrable
      -- split at τ m
      have hvs := rectInt_vsplit (F := fun s => (deriv f s / f s) * ((y:ℂ)^s / s))
        (z := (σ₁:ℂ) + (τ 0)*I) (w := (cc:ℂ) + (τ (m+1))*I) (μ := τ m)
        (by rw [im_coord]; exact h0m) (by rw [im_coord]; linarith)
        (by rw [re_coord, im_coord, im_coord]; exact hintL)
        (by rw [re_coord, im_coord, im_coord]; exact hintR)
      simp only [re_coord] at hvs
      rw [hvs]
      -- the lower part by induction, the top strip directly
      have hstrip := rectInt_strip hf hy hσ hσc hcc (t_lo := τ m)
        (t_hi := τ (m+1)) hmm1 (hgap m (by omega)) ?_
      · rw [ih hmono' hgap' hlines' hleft', hstrip, Finset.sum_range_succ]
        ring
      -- frame nonvanishing for the top strip
      · intro s hs
        simp only [rectFrame, Set.mem_ofPred_eq] at hs
        rcases hs with ⟨hsre, hsim | hsim⟩ | ⟨hsim, hsre | hsre⟩
        · -- bottom edge at height τ m
          rw [im_coord] at hsim
          rw [re_coord, re_coord] at hsre
          rw [Set.uIcc_of_le (by linarith)] at hsre
          have := hlines m (by omega) s.re hsre
          have hs_eq : ((s.re:ℂ) + (τ m)*I) = s := by
            rw [← hsim]
            exact Complex.re_add_im s
          rwa [hs_eq] at this
        · -- top edge at height τ (m+1)
          rw [im_coord] at hsim
          rw [re_coord, re_coord] at hsre
          rw [Set.uIcc_of_le (by linarith)] at hsre
          have := hlines (m+1) (le_refl _) s.re hsre
          have hs_eq : ((s.re:ℂ) + (τ (m+1))*I) = s := by
            rw [← hsim]
            exact Complex.re_add_im s
          rwa [hs_eq] at this
        · -- left edge
          rw [re_coord] at hsre
          rw [im_coord, im_coord] at hsim
          rw [Set.uIcc_of_le (by linarith)] at hsim
          have := hleft s.im ⟨by linarith [hsim.1], hsim.2⟩
          have hs_eq : ((σ₁:ℂ) + (s.im)*I) = s := by
            rw [← hsre]
            exact Complex.re_add_im s
          rwa [hs_eq] at this
        · -- right edge
          apply hf.nz
          rw [hsre, re_coord]
          exact hcc1

end Chain

/-! ### The box zero container and the chain-sum fusion -/

section BoxZeros

/-- Strip membership implies membership in the covering `13/8`-disk
(closed version). -/
lemma mem_closedBall_of_strip {σ₁ cc t_lo t_hi : ℝ} (hσ : 9/16 ≤ σ₁)
    (hcc : cc ≤ 5/4) (hgap : t_hi - t_lo ≤ 1) {ρ : ℂ}
    (h1 : σ₁ ≤ ρ.re) (h2 : ρ.re ≤ cc) (h3 : t_lo ≤ ρ.im) (h4 : ρ.im ≤ t_hi) :
    ρ ∈ closedBall ((2:ℂ) + (((t_lo + t_hi)/2 : ℝ)) * I) (13/8 : ℝ) := by
  rw [mem_closedBall, Complex.dist_eq]
  apply norm_le_of_sq_le (by norm_num)
  have hre' : (ρ - ((2:ℂ) + (((t_lo + t_hi)/2 : ℝ)) * I)).re = ρ.re - 2 := by simp
  have him' : (ρ - ((2:ℂ) + (((t_lo + t_hi)/2 : ℝ)) * I)).im
      = ρ.im - (t_lo + t_hi)/2 := by simp
  rw [hre', him']
  have hb1 : (ρ.re - 2)^2 ≤ (23/16)^2 := by nlinarith
  have hb2 : (ρ.im - (t_lo + t_hi)/2)^2 ≤ (1/2)^2 := by
    have hu1 : ρ.im - (t_lo+t_hi)/2 ≤ (t_hi - t_lo)/2 := by linarith
    have hu2 : -((t_hi - t_lo)/2) ≤ ρ.im - (t_lo+t_hi)/2 := by linarith
    have hd0 : (0:ℝ) ≤ (t_hi - t_lo)/2 := by linarith
    have hd1 : (t_hi - t_lo)/2 ≤ 1/2 := by linarith
    nlinarith [hu1, hu2, hd0, hd1]
  nlinarith

open scoped Classical in
/-- The distinct zeros of `f` in the closed box `[1/2, 3/2] × [−U, U]`. -/
noncomputable def boxZeros (f : ℂ → ℂ) (U : ℝ) : Finset ℂ :=
  if h : {s ∈ Set.Icc (1/2 : ℝ) (3/2) ×ℂ Set.Icc (-U) U | f s = 0}.Finite
  then h.toFinset else ∅

lemma finite_boxZeroSet {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) (U : ℝ) :
    {s ∈ Set.Icc (1/2 : ℝ) (3/2) ×ℂ Set.Icc (-U) U | f s = 0}.Finite := by
  have hconv : Convex ℝ (Set.Icc (1/4 : ℝ) (15/4) ×ℂ Set.Icc (-(|U|+1)) (|U|+1)) := by
    have h1 : Convex ℝ (Complex.re ⁻¹' Set.Icc (1/4 : ℝ) (15/4)) :=
      (convex_Icc _ _).linear_preimage Complex.reLm
    have h2 : Convex ℝ (Complex.im ⁻¹' Set.Icc (-(|U|+1)) (|U|+1)) :=
      (convex_Icc _ _).linear_preimage Complex.imLm
    exact h1.inter h2
  apply finite_zeros_inter_compact'
    (U := Set.Icc (1/4 : ℝ) (15/4) ×ℂ Set.Icc (-(|U|+1)) (|U|+1))
    hconv.isPreconnected
  · intro z hz
    rw [Complex.mem_reProdIm] at hz
    apply hf.diff z.im
    rw [mem_closedBall, Complex.dist_eq]
    have h1 : z - ((2:ℂ) + z.im * I) = ((z.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_le]
    have := hz.1.1
    have := hz.1.2
    constructor <;> linarith
  · show (2:ℂ) ∈ _
    rw [Complex.mem_reProdIm]
    constructor
    · simp
      norm_num
    · simp
      have h0 : (0:ℝ) ≤ |U| := abs_nonneg U
      constructor <;> linarith
  · have h1 := hf.center_ne_zero 0
    have h2 : ((2:ℂ) + (0:ℝ) * I) = 2 := by
      push_cast
      ring
    rwa [h2] at h1
  · exact (isCompact_Icc.reProdIm isCompact_Icc)
  · intro s hs
    rw [Complex.mem_reProdIm] at hs ⊢
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hs
    have hU1 : -(|U|+1) ≤ -U := by
      have := le_abs_self U
      linarith
    have hU2 : U ≤ |U|+1 := by
      have := le_abs_self U
      linarith
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

lemma mem_boxZeros {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) {U : ℝ} {ρ : ℂ} :
    ρ ∈ boxZeros f U ↔
      (1/2 ≤ ρ.re ∧ ρ.re ≤ 3/2) ∧ (-U ≤ ρ.im ∧ ρ.im ≤ U) ∧ f ρ = 0 := by
  rw [boxZeros, dif_pos (finite_boxZeroSet hf U), Set.Finite.mem_toFinset]
  show ρ ∈ Set.Icc (1/2 : ℝ) (3/2) ×ℂ Set.Icc (-U) U ∧ f ρ = 0 ↔ _
  rw [Complex.mem_reProdIm]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

set_option maxHeartbeats 1000000 in
/-- **Fusion**: the chained strip sums equal a single sum over the box zeros
strictly inside the big rectangle. -/
theorem chain_sum_eq_box {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A)
    (g : ℂ → ℂ) {σ₁ cc U : ℝ} (hσ : 9/16 ≤ σ₁) (_hσc : σ₁ < cc) (hcc : cc ≤ 5/4)
    (τ : ℕ → ℝ) (m : ℕ)
    (hmono : ∀ j < m, τ j < τ (j+1))
    (hgap : ∀ j < m, τ (j+1) - τ j ≤ 1)
    (hU0 : -U ≤ τ 0) (hUm : τ m ≤ U)
    (hcuts : ∀ j ≤ m, ∀ ρ ∈ boxZeros f U, ρ.im ≠ τ j) :
    ∑ k ∈ Finset.range m,
        ∑ ρ ∈ (diskZeros f ((τ k + τ (k+1))/2)).filter
          (fun ρ => σ₁ < ρ.re ∧ ρ.re < cc ∧ τ k < ρ.im ∧ ρ.im < τ (k+1)), g ρ
      = ∑ ρ ∈ (boxZeros f U).filter
          (fun ρ => σ₁ < ρ.re ∧ ρ.re < cc ∧ τ 0 < ρ.im ∧ ρ.im < τ m), g ρ := by
  classical
  induction m with
  | zero =>
      rw [Finset.range_zero, Finset.sum_empty]
      symm
      rw [Finset.filter_false_of_mem, Finset.sum_empty]
      intro ρ _
      push Not
      intro _ _ h3
      linarith
  | succ m ih =>
      have hmono' : ∀ j < m, τ j < τ (j+1) := fun j hj => hmono j (by omega)
      have hgap' : ∀ j < m, τ (j+1) - τ j ≤ 1 := fun j hj => hgap j (by omega)
      have hmm1 : τ m < τ (m+1) := hmono m (by omega)
      have hUm' : τ m ≤ U := by linarith
      have hcuts' : ∀ j ≤ m, ∀ ρ ∈ boxZeros f U, ρ.im ≠ τ j :=
        fun j hj => hcuts j (by omega)
      have hchain : ∀ j ≤ m + 1, τ 0 ≤ τ j := by
        intro j hj
        induction j with
        | zero => exact le_refl _
        | succ i ihi =>
            have h1 : τ i < τ (i+1) := hmono i (by omega)
            have h2 := ihi (by omega)
            linarith
      have h0m : τ 0 ≤ τ m := hchain m (by omega)
      rw [Finset.sum_range_succ, ih hmono' hgap' hUm' hcuts']
      have hsplit := Finset.sum_filter_add_sum_filter_not
        ((boxZeros f U).filter
          (fun ρ => σ₁ < ρ.re ∧ ρ.re < cc ∧ τ 0 < ρ.im ∧ ρ.im < τ (m+1)))
        (fun ρ => ρ.im < τ m) g
      rw [← hsplit]
      congr 1
      · -- lower part
        have hset : ((boxZeros f U).filter
            (fun ρ => σ₁ < ρ.re ∧ ρ.re < cc ∧ τ 0 < ρ.im ∧ ρ.im < τ (m+1))).filter
              (fun ρ => ρ.im < τ m)
            = (boxZeros f U).filter
              (fun ρ => σ₁ < ρ.re ∧ ρ.re < cc ∧ τ 0 < ρ.im ∧ ρ.im < τ m) := by
          ext ρ
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨⟨hbox, h1, h2, h3, _⟩, h5⟩
            exact ⟨hbox, h1, h2, h3, h5⟩
          · rintro ⟨hbox, h1, h2, h3, h4⟩
            exact ⟨⟨hbox, h1, h2, h3, by linarith⟩, h4⟩
        rw [hset]
      · -- the top strip
        have hset : ((boxZeros f U).filter
            (fun ρ => σ₁ < ρ.re ∧ ρ.re < cc ∧ τ 0 < ρ.im ∧ ρ.im < τ (m+1))).filter
              (fun ρ => ¬ ρ.im < τ m)
            = (diskZeros f ((τ m + τ (m+1))/2)).filter
              (fun ρ => σ₁ < ρ.re ∧ ρ.re < cc ∧ τ m < ρ.im ∧ ρ.im < τ (m+1)) := by
          ext ρ
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨⟨hbox, h1, h2, h3, h4⟩, h5⟩
            push Not at h5
            have hzero : f ρ = 0 := ((mem_boxZeros hf).mp hbox).2.2
            have hne : ρ.im ≠ τ m := hcuts m (by omega) ρ hbox
            have h6 : τ m < ρ.im := lt_of_le_of_ne h5 (Ne.symm hne)
            refine ⟨(mem_diskZeros hf).mpr ⟨?_, hzero⟩, h1, h2, h6, h4⟩
            exact mem_closedBall_of_strip hσ hcc (hgap m (by omega))
              (le_of_lt h1) (le_of_lt h2) (le_of_lt h6) (le_of_lt h4)
          · rintro ⟨hdisk, h1, h2, h3, h4⟩
            have hzero : f ρ = 0 := ((mem_diskZeros hf).mp hdisk).2
            have hbox : ρ ∈ boxZeros f U := by
              rw [mem_boxZeros hf]
              refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, hzero⟩
            exact ⟨⟨hbox, h1, h2, by linarith, h4⟩, by push Not; linarith⟩
        rw [hset]

end BoxZeros

/-! ### The weight lemma: `∑ m_ρ/(1+|Im ρ|) ≤ 900·log²` -/

section WeightLemma

set_option maxHeartbeats 1000000 in
/-- Weighted zero-count over any finset of zeros in `[1/2,3/2] × [−U,U]`. -/
theorem weight_sum_le {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) {U : ℝ}
    (hU : 2 ≤ U) {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, 1/2 ≤ ρ.re ∧ ρ.re ≤ 3/2 ∧ |ρ.im| ≤ U) :
    ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|)
      ≤ 900 * Real.log (A * (U + 2)) ^ 2 := by
  classical
  have hA1 := hf.one_le
  set LA : ℝ := Real.log (A * (U + 2)) with hLAdef
  have hLA1 : 1 ≤ LA := by
    rw [hLAdef, Real.le_log_iff_exp_le (by nlinarith)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hLA0 : (0:ℝ) < LA := by linarith
  set K : ℕ := ⌊U⌋₊ + 1 with hKdef
  have hmaps : ∀ ρ ∈ Z, ⌊|ρ.im|⌋₊ ∈ Finset.range K := by
    intro ρ hρ
    rw [Finset.mem_range, hKdef]
    have h1 : |ρ.im| ≤ U := (hZ ρ hρ).2.2
    have h2 : ⌊|ρ.im|⌋₊ ≤ ⌊U⌋₊ := Nat.floor_le_floor h1
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  -- per-fiber estimate
  have hfiber : ∀ k ∈ Finset.range K,
      ∑ ρ ∈ Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k),
        (analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|)
      ≤ (1/((k:ℝ)+1)) * (448 * LA) := by
    intro k hk
    have hkU : (k : ℝ) ≤ U := by
      rw [Finset.mem_range, hKdef] at hk
      have : k ≤ ⌊U⌋₊ := by omega
      calc (k:ℝ) ≤ (⌊U⌋₊ : ℝ) := by exact_mod_cast this
        _ ≤ U := Nat.floor_le (by linarith)
    -- weight bound per element
    have hwt : ∀ ρ ∈ Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k),
        (analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|)
          ≤ (analyticOrderNatAt f ρ : ℝ) * (1/((k:ℝ)+1)) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have h1 : (k : ℝ) ≤ |ρ.im| := by
        rw [← hρ.2]
        exact Nat.floor_le (abs_nonneg _)
      rw [div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply one_div_le_one_div_of_le (by positivity)
      linarith
    -- mass bound for the fiber, split by sign
    have hmass : ∑ ρ ∈ Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k),
        (analyticOrderNatAt f ρ : ℝ) ≤ 448 * LA := by
      have hsplit := Finset.sum_filter_add_sum_filter_not
        (Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k)) (fun ρ => 0 ≤ ρ.im)
        (fun ρ => (analyticOrderNatAt f ρ : ℝ))
      have hbnds : ∀ ρ ∈ Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k),
          (ρ.re - 2)^2 ≤ (3/2)^2 ∧ (k : ℝ) ≤ |ρ.im| ∧ |ρ.im| < (k:ℝ) + 1 := by
        intro ρ hρ
        rw [Finset.mem_filter] at hρ
        have hbox := hZ ρ hρ.1
        refine ⟨by nlinarith [hbox.1, hbox.2.1], ?_, ?_⟩
        · rw [← hρ.2]
          exact Nat.floor_le (abs_nonneg _)
        · rw [← hρ.2]
          exact Nat.lt_floor_add_one _
      have hgeoP : ∀ ρ ∈ Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k), 0 ≤ ρ.im →
          ρ ∈ closedBall ((2:ℂ) + (((k:ℝ)+1/2 : ℝ) : ℂ) * I) (13/8 : ℝ) := by
        intro ρ hρ hpos
        obtain ⟨hb1, hklo, hkhi⟩ := hbnds ρ hρ
        rw [abs_of_nonneg hpos] at hklo hkhi
        rw [mem_closedBall, Complex.dist_eq]
        apply norm_le_of_sq_le (by norm_num)
        have hre' : (ρ - ((2:ℂ) + (((k:ℝ)+1/2 : ℝ) : ℂ) * I)).re = ρ.re - 2 := by simp
        have him' : (ρ - ((2:ℂ) + (((k:ℝ)+1/2 : ℝ) : ℂ) * I)).im
            = ρ.im - ((k:ℝ)+1/2) := by simp
        rw [hre', him']
        nlinarith
      have hgeoN : ∀ ρ ∈ Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k), ρ.im < 0 →
          ρ ∈ closedBall ((2:ℂ) + ((-((k:ℝ)+1/2) : ℝ) : ℂ) * I) (13/8 : ℝ) := by
        intro ρ hρ hneg
        obtain ⟨hb1, hklo, hkhi⟩ := hbnds ρ hρ
        rw [abs_of_neg hneg] at hklo hkhi
        rw [mem_closedBall, Complex.dist_eq]
        apply norm_le_of_sq_le (by norm_num)
        have hre' : (ρ - ((2:ℂ) + ((-((k:ℝ)+1/2) : ℝ) : ℂ) * I)).re = ρ.re - 2 := by simp
        have him' : (ρ - ((2:ℂ) + ((-((k:ℝ)+1/2) : ℝ) : ℂ) * I)).im
            = ρ.im + ((k:ℝ)+1/2) := by
          simp
          ring
        rw [hre', him']
        nlinarith
      have hlogk : Real.log (A * (((k:ℝ)+1/2) + 2)) ≤ 2 * LA := by
        have h2 : ((k:ℝ)+1/2)+2 ≤ (U+2)^2 := by nlinarith
        have h1 : A * (((k:ℝ)+1/2)+2) ≤ (A*(U+2))^2 := by
          calc A * (((k:ℝ)+1/2)+2) ≤ A * (U+2)^2 :=
              mul_le_mul_of_nonneg_left h2 (by linarith)
            _ ≤ A^2 * (U+2)^2 := by
                have hAA : A ≤ A^2 := by nlinarith
                have hsq : (0:ℝ) ≤ (U+2)^2 := sq_nonneg _
                nlinarith
            _ = (A*(U+2))^2 := by ring
        calc Real.log (A * (((k:ℝ)+1/2)+2))
            ≤ Real.log ((A*(U+2))^2) := Real.log_le_log (by positivity) h1
          _ = 2 * LA := by
              rw [Real.log_pow, hLAdef]
              push_cast
              ring
      have hpos_mass : ∑ ρ ∈ (Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k)).filter
          (fun ρ => 0 ≤ ρ.im), (analyticOrderNatAt f ρ : ℝ) ≤ 224 * LA := by
        have h1 := sum_ord_le_of_diskData hf ((k:ℝ)+1/2)
          (F := (Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k)).filter (fun ρ => 0 ≤ ρ.im))
          (fun ρ hρ => by
            rw [Finset.mem_filter] at hρ
            exact hgeoP ρ hρ.1 hρ.2)
        have h4 : |(k:ℝ)+1/2| = (k:ℝ)+1/2 := abs_of_nonneg (by positivity)
        rw [h4] at h1
        linarith [hlogk]
      have hneg_mass : ∑ ρ ∈ (Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k)).filter
          (fun ρ => ¬ 0 ≤ ρ.im), (analyticOrderNatAt f ρ : ℝ) ≤ 224 * LA := by
        have h1 := sum_ord_le_of_diskData hf (-((k:ℝ)+1/2))
          (F := (Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k)).filter (fun ρ => ¬ 0 ≤ ρ.im))
          (fun ρ hρ => by
            rw [Finset.mem_filter] at hρ
            exact hgeoN ρ hρ.1 (lt_of_not_ge hρ.2))
        have h4 : |(-((k:ℝ)+1/2))| = (k:ℝ)+1/2 := by
          rw [abs_neg]
          exact abs_of_nonneg (by positivity)
        rw [h4] at h1
        linarith [hlogk]
      linarith [hsplit, hpos_mass, hneg_mass]
    calc ∑ ρ ∈ Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k),
        (analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|)
        ≤ ∑ ρ ∈ Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k),
          (analyticOrderNatAt f ρ : ℝ) * (1/((k:ℝ)+1)) := Finset.sum_le_sum hwt
      _ = (∑ ρ ∈ Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k),
          (analyticOrderNatAt f ρ : ℝ)) * (1/((k:ℝ)+1)) := by
          rw [← Finset.sum_mul]
      _ ≤ (448 * LA) * (1/((k:ℝ)+1)) := by
          apply mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = (1/((k:ℝ)+1)) * (448 * LA) := by ring
  calc ∑ k ∈ Finset.range K, ∑ ρ ∈ Z.filter (fun ρ => ⌊|ρ.im|⌋₊ = k),
      (analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|)
      ≤ ∑ k ∈ Finset.range K, (1/((k:ℝ)+1)) * (448 * LA) :=
        Finset.sum_le_sum hfiber
    _ = (∑ k ∈ Finset.range K, (1:ℝ)/((k:ℝ)+1)) * (448 * LA) := by
        rw [← Finset.sum_mul]
    _ ≤ (1 + Real.log K) * (448 * LA) := by
        apply mul_le_mul_of_nonneg_right (harmonic_le K) (by positivity)
    _ ≤ 900 * LA ^ 2 := by
        have hlogK : Real.log K ≤ LA := by
          have h1 : (K : ℝ) ≤ A * (U + 2) := by
            rw [hKdef]
            push_cast
            have h2 : (⌊U⌋₊ : ℝ) ≤ U := Nat.floor_le (by linarith)
            nlinarith
          rcases Nat.eq_zero_or_pos K with h | h
          · rw [h]; simp; linarith
          · calc Real.log K ≤ Real.log (A * (U+2)) :=
                Real.log_le_log (by exact_mod_cast h) h1
              _ = LA := hLAdef.symm
        nlinarith
    _ = 900 * Real.log (A * (U + 2)) ^ 2 := by rw [hLAdef]

end WeightLemma

/-! ### The `σ₁` pigeonhole against the `|σ−β|^{−1/2}` majorant -/

section SigmaPigeonhole

/-- Interval integrability of a finite sum. -/
lemma intervalIntegrable_finsetSum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ}
    {a b : ℝ} (h : ∀ i ∈ s, IntervalIntegrable (F i) MeasureTheory.volume a b) :
    IntervalIntegrable (fun x => ∑ i ∈ s, F i x) MeasureTheory.volume a b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      have h1 : (fun x => ∑ j ∈ insert i s, F j x)
          = fun x => F i x + ∑ j ∈ s, F j x := by
        funext x
        rw [Finset.sum_insert hi]
      rw [h1]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- Disk zeros have real part in `[3/8, 29/8]`. -/
lemma re_bounds_of_mem_diskZeros {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A)
    {t₀ : ℝ} {ρ : ℂ} (hρ : ρ ∈ diskZeros f t₀) :
    3/8 ≤ ρ.re ∧ ρ.re ≤ 29/8 ∧ |ρ.im - t₀| ≤ 13/8 := by
  have h1 := ((mem_diskZeros hf).mp hρ).1
  rw [mem_closedBall, Complex.dist_eq] at h1
  have h2 : |(ρ - ((2:ℂ) + t₀ * I)).re| ≤ 13/8 :=
    le_trans (Complex.abs_re_le_norm _) h1
  have h3 : |(ρ - ((2:ℂ) + t₀ * I)).im| ≤ 13/8 :=
    le_trans (Complex.abs_im_le_norm _) h1
  have hre' : (ρ - ((2:ℂ) + t₀ * I)).re = ρ.re - 2 := by simp
  have him' : (ρ - ((2:ℂ) + t₀ * I)).im = ρ.im - t₀ := by simp
  rw [hre'] at h2
  rw [him'] at h3
  rw [abs_le] at h2
  exact ⟨by linarith [h2.1], by linarith [h2.2], h3⟩

/-- `(49/16)^(1/2) = 7/4`. -/
lemma rpow_fortynine_half : ((49:ℝ)/16) ^ ((1:ℝ)/2) = 7/4 := by
  rw [show ((49:ℝ)/16) = (7/4)^2 by norm_num]
  rw [← Real.rpow_natCast ((7:ℝ)/4) 2, ← Real.rpow_mul (by norm_num)]
  norm_num

set_option maxHeartbeats 1000000 in
/-- **The `σ₁` pigeonhole.**  There is `σ₁ ∈ [9/16, 5/8]`, off any given finite
bad set, at which the `|σ−β|^{−1/2}`-weighted zero functional of the left-edge
disks is `≤ 200000·log²(A(T+4))`. -/
theorem exists_good_sigma {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A)
    {T a : ℝ} {M : ℕ} (hT : 2 ≤ T) (ha : -(T+1) ≤ a) (ha0 : a ≤ 0)
    (hM1 : 0 ≤ a + M/2) (hM2 : a + M/2 ≤ T + 2) (B : Finset ℝ) :
    ∃ σ₁ : ℝ, 9/16 ≤ σ₁ ∧ σ₁ ≤ 5/8 ∧ σ₁ ∉ B ∧
      (∑ k ∈ Finset.range M, ∑ ρ ∈ diskZeros f (a + k/2 + 1/4),
        (analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|) * |σ₁ - ρ.re| ^ (-(1:ℝ)/2))
      ≤ 200000 * Real.log (A*(T+4))^2 := by
  classical
  have hA1 := hf.one_le
  set LT : ℝ := Real.log (A*(T+4)) with hLTdef
  have hLT1 : 1 ≤ LT := by
    rw [hLTdef, Real.le_log_iff_exp_le (by nlinarith)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hLT0 : (0:ℝ) < LT := by linarith
  set H : ℝ → ℝ := fun σ => ∑ k ∈ Finset.range M, ∑ ρ ∈ diskZeros f (a + k/2 + 1/4),
      (analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|) * |σ - ρ.re| ^ (-(1:ℝ)/2)
    with hHdef
  -- integrability of H
  have hHint : IntervalIntegrable H MeasureTheory.volume (9/16) (5/8) := by
    rw [hHdef]
    apply intervalIntegrable_finsetSum
    intro k _
    apply intervalIntegrable_finsetSum
    intro ρ _
    exact (intervalIntegrable_abs_sub_rpow ρ.re (9/16) (5/8)).const_mul
      ((analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|))
  -- midpoint bounds
  have hmid : ∀ k ∈ Finset.range M, |a + k/2 + 1/4| ≤ T + 2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    have h1 : (k : ℝ) + 1 ≤ M := by exact_mod_cast hk
    rw [abs_le]
    constructor
    · have : (0:ℝ) ≤ (k:ℝ)/2 := by positivity
      linarith
    · have h2 : a + (k:ℝ)/2 + 1/4 ≤ a + ((M:ℝ) - 1)/2 + 1/4 := by linarith
      linarith
  -- the per-`(k,ρ)` weight
  have hW : ∀ k ∈ Finset.range M,
      ∑ ρ ∈ diskZeros f (a + k/2 + 1/4),
        (analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|)
      ≤ (336 * LT) * (1 / (1 + |a + k/2 + 1/4|)) := by
    intro k hk
    set t₀ : ℝ := a + k/2 + 1/4 with ht₀def
    have hwt : ∀ ρ ∈ diskZeros f t₀,
        (analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|)
          ≤ (analyticOrderNatAt f ρ : ℝ) * (3 / (1 + |t₀|)) := by
      intro ρ hρ
      have h1 := (re_bounds_of_mem_diskZeros hf hρ).2.2
      have h2 : |t₀| ≤ |ρ.im| + 13/8 := by
        calc |t₀| = |ρ.im - (ρ.im - t₀)| := by ring_nf
          _ ≤ |ρ.im| + |ρ.im - t₀| := abs_sub _ _
          _ ≤ |ρ.im| + 13/8 := by linarith
      have h3 : 1 + |t₀| ≤ 3 * (1 + |ρ.im|) := by
        have := abs_nonneg ρ.im
        linarith
      rw [div_eq_mul_one_div]
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    have hmass : (∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℝ))
        ≤ 112 * LT := by
      have h1 := sum_ord_le_of_diskData hf t₀
        (F := diskZeros f t₀) (fun ρ hρ => ((mem_diskZeros hf).mp hρ).1)
      have h2 : Real.log (A * (|t₀| + 2)) ≤ LT := by
        rw [hLTdef]
        apply Real.log_le_log (by positivity)
        have := hmid k hk
        rw [← ht₀def] at this
        nlinarith
      linarith
    calc ∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|)
        ≤ ∑ ρ ∈ diskZeros f t₀,
          (analyticOrderNatAt f ρ : ℝ) * (3 / (1 + |t₀|)) := Finset.sum_le_sum hwt
      _ = (∑ ρ ∈ diskZeros f t₀, (analyticOrderNatAt f ρ : ℝ)) * (3 / (1 + |t₀|)) := by
          rw [← Finset.sum_mul]
      _ ≤ (112 * LT) * (3 / (1 + |t₀|)) := by
          apply mul_le_mul_of_nonneg_right hmass (by positivity)
      _ = (336 * LT) * (1 / (1 + |t₀|)) := by
          field_simp
          norm_num
  -- the harmonic sum of the midpoints
  have hharm : ∑ k ∈ Finset.range M, (1:ℝ) / (1 + |a + k/2 + 1/4|) ≤ 5 * LT := by
    have hptw : ∀ k ∈ Finset.range M, (1:ℝ) / (1 + |a + k/2 + 1/4|)
        ≤ (5/2) * ∫ t in (a + k/2)..(a + (k+1)/2), 1 / (1 + |t|) := by
      intro k _
      have hlow : ∀ t ∈ Set.Icc (a + (k:ℝ)/2) (a + ((k:ℝ)+1)/2),
          (4/5) * (1 / (1 + |a + k/2 + 1/4|)) ≤ 1 / (1 + |t|) := by
        intro t ht
        have h1 : |t - (a + (k:ℝ)/2 + 1/4)| ≤ 1/4 := by
          rw [abs_le]
          exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
        have h2 : |t| ≤ |a + (k:ℝ)/2 + 1/4| + 1/4 := by
          have h2a := abs_sub_abs_le_abs_sub t (a + (k:ℝ)/2 + 1/4)
          linarith
        have h3 : 1 + |t| ≤ (5/4) * (1 + |a + (k:ℝ)/2 + 1/4|) := by
          have := abs_nonneg (a + (k:ℝ)/2 + 1/4)
          linarith
        have h4 : (0:ℝ) < 1 + |t| := by positivity
        have h5 : (0:ℝ) < 1 + |a + (k:ℝ)/2 + 1/4| := by positivity
        rw [mul_one_div, div_le_div_iff₀ h5 h4]
        linarith
      have hint2 : IntervalIntegrable (fun t : ℝ => 1 / (1 + |t|))
          MeasureTheory.volume (a + k/2) (a + (k+1)/2) :=
        continuous_one_div_one_add_abs.intervalIntegrable _ _
      have hle : a + (k:ℝ)/2 ≤ a + ((k:ℝ)+1)/2 := by linarith
      have h4 : ((4:ℝ)/5) * (1 / (1 + |a + k/2 + 1/4|)) * (1/2)
          ≤ ∫ t in (a + k/2)..(a + (k+1)/2), 1 / (1 + |t|) := by
        have h5 : (∫ _t in (a + (k:ℝ)/2)..(a + ((k:ℝ)+1)/2),
            ((4:ℝ)/5) * (1 / (1 + |a + k/2 + 1/4|)))
            ≤ ∫ t in (a + (k:ℝ)/2)..(a + ((k:ℝ)+1)/2), 1 / (1 + |t|) := by
          apply intervalIntegral.integral_mono_on hle
            intervalIntegrable_const hint2
          intro t ht
          exact hlow t ht
        rw [intervalIntegral.integral_const] at h5
        have h6 : (a + ((k:ℝ)+1)/2) - (a + (k:ℝ)/2) = 1/2 := by ring
        rw [h6] at h5
        rw [smul_eq_mul] at h5
        linarith
      have h7 : (0:ℝ) < 1 + |a + (k:ℝ)/2 + 1/4| := by positivity
      calc (1:ℝ) / (1 + |a + k/2 + 1/4|)
          = (5/2) * (((4:ℝ)/5) * (1 / (1 + |a + k/2 + 1/4|)) * (1/2)) := by
            field_simp
            norm_num
        _ ≤ (5/2) * ∫ t in (a + k/2)..(a + (k+1)/2), 1 / (1 + |t|) := by
            apply mul_le_mul_of_nonneg_left h4 (by norm_num)
    have hadj : ∑ k ∈ Finset.range M,
        (∫ t in (a + k/2)..(a + (k+1)/2), 1 / (1 + |t|))
        = ∫ t in a..(a + M/2), 1 / (1 + |t|) := by
      have := intervalIntegral.sum_integral_adjacent_intervals
        (μ := MeasureTheory.volume)
        (a := fun k : ℕ => a + k/2) (n := M)
        (f := fun t : ℝ => 1 / (1 + |t|))
        (fun k _ => continuous_one_div_one_add_abs.intervalIntegrable _ _)
      simp only [Nat.cast_zero, Nat.cast_succ] at this ⊢
      convert this using 2; ring
    have hbig : (∫ t in a..(a + M/2), 1 / (1 + |t|)) ≤ 2 * Real.log (1 + (T+2)) := by
      exact integral_one_div_one_add_abs_le ha0 hM1 (by linarith) hM2
    have hlog2 : Real.log (1 + (T+2)) ≤ LT := by
      rw [hLTdef]
      apply Real.log_le_log (by linarith)
      nlinarith
    calc ∑ k ∈ Finset.range M, (1:ℝ) / (1 + |a + k/2 + 1/4|)
        ≤ ∑ k ∈ Finset.range M,
          (5/2) * ∫ t in (a + k/2)..(a + (k+1)/2), 1 / (1 + |t|) :=
          Finset.sum_le_sum hptw
      _ = (5/2) * ∑ k ∈ Finset.range M,
          ∫ t in (a + k/2)..(a + (k+1)/2), 1 / (1 + |t|) := by
          rw [Finset.mul_sum]
      _ = (5/2) * ∫ t in a..(a + M/2), 1 / (1 + |t|) := by rw [hadj]
      _ ≤ (5/2) * (2 * Real.log (1 + (T+2))) := by
          apply mul_le_mul_of_nonneg_left hbig (by norm_num)
      _ ≤ 5 * LT := by linarith
  -- the average of H
  have havg : (∫ σ in (9/16 : ℝ)..(5/8), H σ)
      ≤ (200000 * LT^2) * (5/8 - 9/16) := by
    have hHsum : (∫ σ in (9/16 : ℝ)..(5/8), H σ)
        = ∑ k ∈ Finset.range M, ∑ ρ ∈ diskZeros f (a + k/2 + 1/4),
          ((analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|))
            * ∫ σ in (9/16 : ℝ)..(5/8), |σ - ρ.re| ^ (-(1:ℝ)/2) := by
      rw [hHdef]
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro k _
        rw [intervalIntegral.integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro ρ _
          rw [intervalIntegral.integral_const_mul]
        · intro ρ _
          exact (intervalIntegrable_abs_sub_rpow ρ.re _ _).const_mul _
      · intro k _
        apply intervalIntegrable_finsetSum
        intro ρ _
        exact (intervalIntegrable_abs_sub_rpow ρ.re _ _).const_mul _
    rw [hHsum]
    have hper : ∀ k ∈ Finset.range M, ∀ ρ ∈ diskZeros f (a + k/2 + 1/4),
        (∫ σ in (9/16 : ℝ)..(5/8), |σ - ρ.re| ^ (-(1:ℝ)/2)) ≤ 7 := by
      intro k _ ρ hρ
      obtain ⟨hre1, hre2, _⟩ := re_bounds_of_mem_diskZeros hf hρ
      have h1 := integral_abs_sub_rpow_le (β := ρ.re) (a := 9/16) (b := 5/8)
        (D := 49/16) (by norm_num) (by linarith) (by linarith) (by norm_num)
      rw [rpow_fortynine_half] at h1
      linarith
    calc ∑ k ∈ Finset.range M, ∑ ρ ∈ diskZeros f (a + k/2 + 1/4),
        ((analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|))
          * ∫ σ in (9/16 : ℝ)..(5/8), |σ - ρ.re| ^ (-(1:ℝ)/2)
        ≤ ∑ k ∈ Finset.range M, ∑ ρ ∈ diskZeros f (a + k/2 + 1/4),
          ((analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|)) * 7 := by
          apply Finset.sum_le_sum
          intro k hk
          apply Finset.sum_le_sum
          intro ρ hρ
          apply mul_le_mul_of_nonneg_left (hper k hk ρ hρ) (by positivity)
      _ = 7 * ∑ k ∈ Finset.range M, ∑ ρ ∈ diskZeros f (a + k/2 + 1/4),
          ((analyticOrderNatAt f ρ : ℝ) / (1 + |ρ.im|)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ρ _
          ring
      _ ≤ 7 * ∑ k ∈ Finset.range M, (336 * LT) * (1 / (1 + |a + k/2 + 1/4|)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Finset.sum_le_sum hW
      _ = 7 * (336 * LT) * ∑ k ∈ Finset.range M, (1 / (1 + |a + k/2 + 1/4|)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
      _ ≤ 7 * (336 * LT) * (5 * LT) := by
          apply mul_le_mul_of_nonneg_left hharm (by positivity)
      _ ≤ (200000 * LT^2) * (5/8 - 9/16) := by nlinarith
  obtain ⟨σ₁, hσmem, hσB, hσH⟩ := exists_le_avg_off_finset
    (by norm_num : (9/16 : ℝ) < 5/8) hHint havg B
  exact ⟨σ₁, hσmem.1, hσmem.2, hσB, hσH⟩

end SigmaPigeonhole

/-! ### The left edge -/

section LeftEdge

/-- The AM–GM window integral: `∫_{J} dt/‖σ₁+it−ρ‖ ≤ 6·|σ₁−Re ρ|^{−1/2}`. -/
lemma integral_inv_dist_le {σ₁ : ℝ} {ρ : ℂ} (hne : ρ.re ≠ σ₁) {t₀ : ℝ}
    (him : |ρ.im - t₀| ≤ 13/8) :
    ∫ t in (t₀ - 1/4)..(t₀ + 1/4), (1/‖((σ₁:ℂ) + t*I) - ρ‖)
      ≤ 6 * |σ₁ - ρ.re| ^ (-(1:ℝ)/2) := by
  have hd0 : (0:ℝ) < |σ₁ - ρ.re| := by
    rw [abs_pos, sub_ne_zero]
    exact fun h => hne h.symm
  -- a.e. pointwise bound
  have hptw : ∀ t : ℝ, t ≠ ρ.im →
      1/‖((σ₁:ℂ) + t*I) - ρ‖
        ≤ |σ₁ - ρ.re| ^ (-(1:ℝ)/2) * |t - ρ.im| ^ (-(1:ℝ)/2) := by
    intro t ht
    have ht0 : (0:ℝ) < |t - ρ.im| := by
      rw [abs_pos, sub_ne_zero]
      exact ht
    have hre' : (((σ₁:ℂ) + t*I) - ρ).re = σ₁ - ρ.re := by simp
    have him' : (((σ₁:ℂ) + t*I) - ρ).im = t - ρ.im := by simp
    have hsq : |σ₁ - ρ.re| * |t - ρ.im| ≤ ‖((σ₁:ℂ) + t*I) - ρ‖^2 := by
      have h1 : ‖((σ₁:ℂ) + t*I) - ρ‖^2
          = (σ₁ - ρ.re)^2 + (t - ρ.im)^2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre', him']
        ring
      rw [h1]
      nlinarith [abs_nonneg (σ₁ - ρ.re), abs_nonneg (t - ρ.im),
        sq_abs (σ₁ - ρ.re), sq_abs (t - ρ.im),
        sq_nonneg (|σ₁ - ρ.re| - |t - ρ.im|)]
    have hnorm0 : (0:ℝ) < ‖((σ₁:ℂ) + t*I) - ρ‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      intro h
      apply ht
      have h4 := congrArg Complex.im h
      simpa using h4
    have hsqrt : Real.sqrt (|σ₁ - ρ.re| * |t - ρ.im|) ≤ ‖((σ₁:ℂ) + t*I) - ρ‖ := by
      rw [show ‖((σ₁:ℂ) + t*I) - ρ‖ = Real.sqrt (‖((σ₁:ℂ) + t*I) - ρ‖^2) from
        (Real.sqrt_sq (norm_nonneg _)).symm]
      exact Real.sqrt_le_sqrt hsq
    have hsqrt0 : (0:ℝ) < Real.sqrt (|σ₁ - ρ.re| * |t - ρ.im|) :=
      Real.sqrt_pos.mpr (by positivity)
    have h2 : 1/‖((σ₁:ℂ) + t*I) - ρ‖ ≤ 1/Real.sqrt (|σ₁ - ρ.re| * |t - ρ.im|) :=
      one_div_le_one_div_of_le hsqrt0 hsqrt
    have h3 : 1/Real.sqrt (|σ₁ - ρ.re| * |t - ρ.im|)
        = |σ₁ - ρ.re| ^ (-(1:ℝ)/2) * |t - ρ.im| ^ (-(1:ℝ)/2) := by
      rw [Real.sqrt_eq_rpow, ← Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
      rw [one_div, ← Real.rpow_neg (by positivity)]
      norm_num
    rw [h3] at h2
    exact h2
  have hint1 : IntervalIntegrable (fun t : ℝ => 1/‖((σ₁:ℂ) + t*I) - ρ‖)
      MeasureTheory.volume (t₀ - 1/4) (t₀ + 1/4) := by
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const
    · exact ((continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const).norm
    · intro t
      rw [ne_eq, norm_eq_zero, sub_eq_zero]
      intro h
      apply hne
      have := congrArg Complex.re h
      simpa using this.symm
  have hint2 : IntervalIntegrable
      (fun t : ℝ => |σ₁ - ρ.re| ^ (-(1:ℝ)/2) * |t - ρ.im| ^ (-(1:ℝ)/2))
      MeasureTheory.volume (t₀ - 1/4) (t₀ + 1/4) :=
    (intervalIntegrable_abs_sub_rpow ρ.im _ _).const_mul _
  have hmono : (∫ t in (t₀ - 1/4)..(t₀ + 1/4), 1/‖((σ₁:ℂ) + t*I) - ρ‖)
      ≤ ∫ t in (t₀ - 1/4)..(t₀ + 1/4),
          |σ₁ - ρ.re| ^ (-(1:ℝ)/2) * |t - ρ.im| ^ (-(1:ℝ)/2) := by
    apply intervalIntegral.integral_mono_ae (by linarith) hint1 hint2
    have hnull : MeasureTheory.volume ({ρ.im} : Set ℝ) = 0 :=
      MeasureTheory.measure_singleton _
    rw [Filter.EventuallyLE, MeasureTheory.ae_iff]
    apply MeasureTheory.measure_mono_null _ hnull
    intro t ht
    simp only [Set.mem_ofPred_eq] at ht
    simp only [Set.mem_singleton_iff]
    by_contra htne
    exact ht (hptw t htne)
  calc (∫ t in (t₀ - 1/4)..(t₀ + 1/4), 1/‖((σ₁:ℂ) + t*I) - ρ‖)
      ≤ ∫ t in (t₀ - 1/4)..(t₀ + 1/4),
          |σ₁ - ρ.re| ^ (-(1:ℝ)/2) * |t - ρ.im| ^ (-(1:ℝ)/2) := hmono
    _ = |σ₁ - ρ.re| ^ (-(1:ℝ)/2)
          * ∫ t in (t₀ - 1/4)..(t₀ + 1/4), |t - ρ.im| ^ (-(1:ℝ)/2) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ |σ₁ - ρ.re| ^ (-(1:ℝ)/2) * (4 * (2:ℝ) ^ ((1:ℝ)/2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [abs_le] at him
        apply integral_abs_sub_rpow_le (by linarith)
        · linarith [him.1]
        · linarith [him.2]
        · norm_num
    _ ≤ 6 * |σ₁ - ρ.re| ^ (-(1:ℝ)/2) := by
        have h1 : ((2:ℝ)) ^ ((1:ℝ)/2) ≤ 3/2 := by
          rw [← Real.sqrt_eq_rpow]
          rw [show (3/2 : ℝ) = Real.sqrt ((3/2)^2) from
            (Real.sqrt_sq (by norm_num)).symm]
          apply Real.sqrt_le_sqrt
          norm_num
        have h2 : (0:ℝ) ≤ |σ₁ - ρ.re| ^ (-(1:ℝ)/2) := by positivity
        nlinarith

/-- Pointwise bound for the strip integrand on the left edge. -/
lemma stripInt_norm_le {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A)
    {y σ₁ t₀ t : ℝ} (hy : 0 < y) (hσ1 : 9/16 ≤ σ₁) (hσ2 : σ₁ ≤ 5/8)
    (ht : |t - t₀| ≤ 1/4) (hfs : f ((σ₁:ℂ) + t*I) ≠ 0) :
    ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖
      ≤ y^σ₁ * ((2080000 * Real.log (A*(|t₀|+2))) * (1/(1+|t|))
          + 12 * ∑ ρ ∈ diskZeros f t₀,
              (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
                * (1/‖((σ₁:ℂ)+t*I) - ρ‖)) := by
  have hX2 : (2:ℝ) ≤ A*(|t₀|+2) := hf.scale_two_le t₀
  have hlogX : (0:ℝ) < Real.log (A*(|t₀|+2)) := Real.log_pos (by linarith)
  have hs32 : ((σ₁:ℂ) + t*I) ∈ closedBall ((2:ℂ) + t₀*I) (3/2 : ℝ) := by
    rw [mem_closedBall, Complex.dist_eq]
    apply norm_le_of_sq_le (by norm_num)
    have hre' : (((σ₁:ℂ) + t*I) - ((2:ℂ) + t₀*I)).re = σ₁ - 2 := by simp
    have him' : (((σ₁:ℂ) + t*I) - ((2:ℂ) + t₀*I)).im = t - t₀ := by simp
    rw [hre', him']
    have h1 : (σ₁ - 2)^2 ≤ (23/16)^2 := by nlinarith
    have h2 : (t - t₀)^2 ≤ (1/4)^2 := by
      rw [abs_le] at ht
      nlinarith [ht.1, ht.2]
    nlinarith
  have hmain := norm_logDeriv_sub_sum_diskZeros_le hf t₀ hs32 hfs
  -- bound on the log-derivative
  have hsum_le : ‖∑ ρ ∈ diskZeros f t₀,
      (analyticOrderNatAt f ρ : ℂ) / (((σ₁:ℂ)+t*I) - ρ)‖
      ≤ ∑ ρ ∈ diskZeros f t₀,
        (analyticOrderNatAt f ρ : ℝ) * (1/‖((σ₁:ℂ)+t*I) - ρ‖) := by
    calc ‖∑ ρ ∈ diskZeros f t₀,
        (analyticOrderNatAt f ρ : ℂ) / (((σ₁:ℂ)+t*I) - ρ)‖
        ≤ ∑ ρ ∈ diskZeros f t₀,
          ‖(analyticOrderNatAt f ρ : ℂ) / (((σ₁:ℂ)+t*I) - ρ)‖ := norm_sum_le _ _
      _ = ∑ ρ ∈ diskZeros f t₀,
          (analyticOrderNatAt f ρ : ℝ) * (1/‖((σ₁:ℂ)+t*I) - ρ‖) := by
          apply Finset.sum_congr rfl
          intro ρ _
          rw [norm_div, Complex.norm_natCast, div_eq_mul_one_div]
  have hLL : ‖deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I)‖
      ≤ 520000 * Real.log (A*(|t₀|+2))
        + ∑ ρ ∈ diskZeros f t₀,
          (analyticOrderNatAt f ρ : ℝ) * (1/‖((σ₁:ℂ)+t*I) - ρ‖) := by
    calc ‖deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I)‖
        ≤ ‖deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I)
            - ∑ ρ ∈ diskZeros f t₀,
              (analyticOrderNatAt f ρ : ℂ) / (((σ₁:ℂ)+t*I) - ρ)‖
          + ‖∑ ρ ∈ diskZeros f t₀,
              (analyticOrderNatAt f ρ : ℂ) / (((σ₁:ℂ)+t*I) - ρ)‖ := by
          have := norm_sub_le (deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I)
            - ∑ ρ ∈ diskZeros f t₀,
              (analyticOrderNatAt f ρ : ℂ) / (((σ₁:ℂ)+t*I) - ρ))
            (- ∑ ρ ∈ diskZeros f t₀,
              (analyticOrderNatAt f ρ : ℂ) / (((σ₁:ℂ)+t*I) - ρ))
          simp only [sub_neg_eq_add, sub_add_cancel, norm_neg] at this
          exact this
      _ ≤ _ := add_le_add hmain hsum_le
  -- the `y^s/s` factor
  have hys : ‖(y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I)‖ ≤ y^σ₁ * (4/(1+|t|)) := by
    rw [norm_div, norm_cpow_coord hy]
    have h1 : σ₁ ≤ ‖(σ₁:ℂ)+t*I‖ := by
      have := norm_coord_ge_abs_re σ₁ t
      rwa [abs_of_pos (by linarith)] at this
    have h2 : |t| ≤ ‖(σ₁:ℂ)+t*I‖ := norm_coord_ge_abs_im σ₁ t
    have h3 : (9/32) * (1+|t|) ≤ ‖(σ₁:ℂ)+t*I‖ := by
      have := abs_nonneg t
      linarith
    have h4 : (0:ℝ) < ‖(σ₁:ℂ)+t*I‖ := by
      have := abs_nonneg t
      linarith
    have h5 : 1/‖(σ₁:ℂ)+t*I‖ ≤ 4/(1+|t|) := by
      rw [div_le_div_iff₀ h4 (by positivity : (0:ℝ) < 1+|t|)]
      linarith
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left h5 (Real.rpow_nonneg hy.le σ₁)
  -- per-`ρ` weight conversion
  have hwt : ∀ ρ ∈ diskZeros f t₀,
      (4/(1+|t|)) * ((analyticOrderNatAt f ρ : ℝ) * (1/‖((σ₁:ℂ)+t*I) - ρ‖))
        ≤ 12 * ((analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
            * (1/‖((σ₁:ℂ)+t*I) - ρ‖)) := by
    intro ρ hρ
    have h1 := (re_bounds_of_mem_diskZeros hf hρ).2.2
    have h2 : |ρ.im| ≤ |t| + 2 := by
      have h3 : |ρ.im - t| ≤ 2 := by
        calc |ρ.im - t| = |(ρ.im - t₀) - (t - t₀)| := by ring_nf
          _ ≤ |ρ.im - t₀| + |t - t₀| := abs_sub _ _
          _ ≤ 2 := by linarith
      have h4 := abs_sub_abs_le_abs_sub ρ.im t
      linarith
    have h5 : 1 + |ρ.im| ≤ 3 * (1 + |t|) := by
      have := abs_nonneg t
      linarith
    have h6 : (0:ℝ) ≤ 1/‖((σ₁:ℂ)+t*I) - ρ‖ := by positivity
    have h7 : (0:ℝ) ≤ (analyticOrderNatAt f ρ : ℝ) := Nat.cast_nonneg _
    have h8 : (4/(1+|t|)) ≤ 12/(1+|ρ.im|) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    calc (4/(1+|t|)) * ((analyticOrderNatAt f ρ : ℝ) * (1/‖((σ₁:ℂ)+t*I) - ρ‖))
        ≤ (12/(1+|ρ.im|)) * ((analyticOrderNatAt f ρ : ℝ)
            * (1/‖((σ₁:ℂ)+t*I) - ρ‖)) := by
          apply mul_le_mul_of_nonneg_right h8 (by positivity)
      _ = 12 * ((analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
            * (1/‖((σ₁:ℂ)+t*I) - ρ‖)) := by
          field_simp
  -- assemble
  rw [norm_mul]
  have hnn1 : (0:ℝ) ≤ ‖(y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I)‖ := norm_nonneg _
  have hnn2 : (0:ℝ) ≤ 520000 * Real.log (A*(|t₀|+2))
      + ∑ ρ ∈ diskZeros f t₀,
        (analyticOrderNatAt f ρ : ℝ) * (1/‖((σ₁:ℂ)+t*I) - ρ‖) := by
    apply add_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro ρ _
    positivity
  calc ‖deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I)‖
      * ‖(y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I)‖
      ≤ (520000 * Real.log (A*(|t₀|+2))
          + ∑ ρ ∈ diskZeros f t₀,
            (analyticOrderNatAt f ρ : ℝ) * (1/‖((σ₁:ℂ)+t*I) - ρ‖))
        * (y^σ₁ * (4/(1+|t|))) := by
        apply mul_le_mul hLL hys hnn1 hnn2
    _ = y^σ₁ * ((520000 * Real.log (A*(|t₀|+2))) * (4/(1+|t|))
          + (4/(1+|t|)) * ∑ ρ ∈ diskZeros f t₀, ((analyticOrderNatAt f ρ : ℝ)
              * (1/‖((σ₁:ℂ)+t*I) - ρ‖))) := by
        ring
    _ = y^σ₁ * ((520000 * Real.log (A*(|t₀|+2))) * (4/(1+|t|))
          + ∑ ρ ∈ diskZeros f t₀, (4/(1+|t|)) * ((analyticOrderNatAt f ρ : ℝ)
              * (1/‖((σ₁:ℂ)+t*I) - ρ‖))) := by
        rw [Finset.mul_sum]
    _ ≤ y^σ₁ * ((2080000 * Real.log (A*(|t₀|+2))) * (1/(1+|t|))
          + 12 * ∑ ρ ∈ diskZeros f t₀,
              (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
                * (1/‖((σ₁:ℂ)+t*I) - ρ‖)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy.le σ₁)
        rw [Finset.mul_sum]
        apply add_le_add
        · have h9 : (0:ℝ) < 1 + |t| := by positivity
          rw [div_eq_mul_one_div (4:ℝ), ← mul_assoc]
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          nlinarith
        · exact Finset.sum_le_sum hwt

set_option maxHeartbeats 1000000 in
/-- Per-interval left-edge bound over `[t₀−1/4, t₀+1/4]`. -/
lemma edge_interval_bound {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A)
    {y σ₁ t₀ : ℝ} (hy : 1 < y) (hσ1 : 9/16 ≤ σ₁) (hσ2 : σ₁ ≤ 5/8)
    (hσne : ∀ ρ ∈ diskZeros f t₀, ρ.re ≠ σ₁)
    (hnz : ∀ t ∈ Set.Icc (t₀ - 1/4) (t₀ + 1/4), f ((σ₁:ℂ) + t*I) ≠ 0) :
    (∫ t in (t₀ - 1/4)..(t₀ + 1/4),
        ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
          * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖)
      ≤ y^σ₁ * ((2080000 * Real.log (A*(|t₀|+2)))
            * (∫ t in (t₀ - 1/4)..(t₀ + 1/4), 1/(1+|t|))
          + 72 * ∑ ρ ∈ diskZeros f t₀,
              (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
                * |σ₁ - ρ.re| ^ (-(1:ℝ)/2)) := by
  have hy0 : (0:ℝ) < y := by linarith
  have hle : t₀ - 1/4 ≤ t₀ + 1/4 := by linarith
  -- continuity/integrability of `‖Φ‖`
  have hcontΦ : ContinuousOn (fun t : ℝ =>
      (deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))) (Set.uIcc (t₀-1/4) (t₀+1/4)) := by
    apply contOn_vert_stripInt hf hy0 (by linarith) (by linarith)
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    exact hnz t ht
  have hintΦ : IntervalIntegrable (fun t : ℝ =>
      ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖)
      MeasureTheory.volume (t₀-1/4) (t₀+1/4) :=
    hcontΦ.norm.intervalIntegrable
  -- continuity/integrability of the majorant
  have hcontdist : ∀ ρ ∈ diskZeros f t₀,
      Continuous (fun t : ℝ => 1/‖((σ₁:ℂ)+t*I) - ρ‖) := by
    intro ρ hρ
    apply Continuous.div continuous_const
    · exact ((continuous_const.add
        (Complex.continuous_ofReal.mul continuous_const)).sub
        continuous_const).norm
    · intro t
      rw [ne_eq, norm_eq_zero, sub_eq_zero]
      intro h
      apply hσne ρ hρ
      have := congrArg Complex.re h
      simpa using this.symm
  have hcontmaj : Continuous (fun t : ℝ =>
      y^σ₁ * ((2080000 * Real.log (A*(|t₀|+2))) * (1/(1+|t|))
        + 12 * ∑ ρ ∈ diskZeros f t₀,
            (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
              * (1/‖((σ₁:ℂ)+t*I) - ρ‖))) := by
    apply Continuous.mul continuous_const
    apply Continuous.add
    · exact continuous_const.mul continuous_one_div_one_add_abs
    · apply Continuous.mul continuous_const
      apply continuous_finsetSum
      intro ρ hρ
      exact continuous_const.mul (hcontdist ρ hρ)
  have hmono : (∫ t in (t₀-1/4)..(t₀+1/4),
      ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖)
      ≤ ∫ t in (t₀-1/4)..(t₀+1/4),
        y^σ₁ * ((2080000 * Real.log (A*(|t₀|+2))) * (1/(1+|t|))
          + 12 * ∑ ρ ∈ diskZeros f t₀,
              (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
                * (1/‖((σ₁:ℂ)+t*I) - ρ‖)) := by
    apply intervalIntegral.integral_mono_on hle hintΦ
      (hcontmaj.intervalIntegrable _ _)
    intro t ht
    apply stripInt_norm_le hf hy0 hσ1 hσ2
    · rw [abs_le]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · exact hnz t ht
  -- evaluate the majorant integral
  have heval : (∫ t in (t₀-1/4)..(t₀+1/4),
      y^σ₁ * ((2080000 * Real.log (A*(|t₀|+2))) * (1/(1+|t|))
        + 12 * ∑ ρ ∈ diskZeros f t₀,
            (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
              * (1/‖((σ₁:ℂ)+t*I) - ρ‖)))
      = y^σ₁ * ((2080000 * Real.log (A*(|t₀|+2)))
            * (∫ t in (t₀-1/4)..(t₀+1/4), 1/(1+|t|))
          + 12 * ∑ ρ ∈ diskZeros f t₀,
              (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
                * (∫ t in (t₀-1/4)..(t₀+1/4), 1/‖((σ₁:ℂ)+t*I) - ρ‖)) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    rw [intervalIntegral.integral_add]
    · congr 1
      · rw [intervalIntegral.integral_const_mul]
      · rw [intervalIntegral.integral_const_mul]
        congr 1
        rw [intervalIntegral.integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro ρ _
          rw [intervalIntegral.integral_const_mul]
        · intro ρ hρ
          exact (continuous_const.mul (hcontdist ρ hρ)).intervalIntegrable _ _
    · exact (continuous_const.mul continuous_one_div_one_add_abs).intervalIntegrable _ _
    · apply Continuous.intervalIntegrable
      apply Continuous.mul continuous_const
      apply continuous_finsetSum
      intro ρ hρ
      exact continuous_const.mul (hcontdist ρ hρ)
  -- per-ρ window integral
  have hper : ∀ ρ ∈ diskZeros f t₀,
      (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
        * (∫ t in (t₀-1/4)..(t₀+1/4), 1/‖((σ₁:ℂ)+t*I) - ρ‖)
      ≤ (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
        * (6 * |σ₁ - ρ.re| ^ (-(1:ℝ)/2)) := by
    intro ρ hρ
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact integral_inv_dist_le (hσne ρ hρ) (re_bounds_of_mem_diskZeros hf hρ).2.2
  calc (∫ t in (t₀-1/4)..(t₀+1/4),
      ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖)
      ≤ y^σ₁ * ((2080000 * Real.log (A*(|t₀|+2)))
            * (∫ t in (t₀-1/4)..(t₀+1/4), 1/(1+|t|))
          + 12 * ∑ ρ ∈ diskZeros f t₀,
              (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
                * (∫ t in (t₀-1/4)..(t₀+1/4), 1/‖((σ₁:ℂ)+t*I) - ρ‖)) := by
        rw [← heval]
        exact hmono
    _ ≤ y^σ₁ * ((2080000 * Real.log (A*(|t₀|+2)))
            * (∫ t in (t₀-1/4)..(t₀+1/4), 1/(1+|t|))
          + 72 * ∑ ρ ∈ diskZeros f t₀,
              (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
                * |σ₁ - ρ.re| ^ (-(1:ℝ)/2)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy0.le σ₁)
        have hstep : 12 * (∑ ρ ∈ diskZeros f t₀,
            (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
              * (∫ t in (t₀-1/4)..(t₀+1/4), 1/‖((σ₁:ℂ)+t*I) - ρ‖))
            ≤ 72 * ∑ ρ ∈ diskZeros f t₀,
              (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
                * |σ₁ - ρ.re| ^ (-(1:ℝ)/2) := by
          calc 12 * ∑ ρ ∈ diskZeros f t₀,
            (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
              * (∫ t in (t₀-1/4)..(t₀+1/4), 1/‖((σ₁:ℂ)+t*I) - ρ‖)
              ≤ 12 * ∑ ρ ∈ diskZeros f t₀,
                (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
                  * (6 * |σ₁ - ρ.re| ^ (-(1:ℝ)/2)) := by
                apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hper) (by norm_num)
            _ = 72 * ∑ ρ ∈ diskZeros f t₀,
                (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
                  * |σ₁ - ρ.re| ^ (-(1:ℝ)/2) := by
                rw [Finset.mul_sum, Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro ρ _
                ring
        linarith [hstep]

set_option maxHeartbeats 1000000 in
/-- **The left-edge bound.** -/
theorem left_edge_le {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A)
    {y T a σ₁ : ℝ} {M : ℕ} (hy : 1 < y) (hT : 2 ≤ T)
    (ha : -(T+1) ≤ a) (ha0 : a ≤ 0) (hM1 : 0 ≤ a + M/2) (hM2 : a + M/2 ≤ T+2)
    (hσ1 : 9/16 ≤ σ₁) (hσ2 : σ₁ ≤ 5/8)
    (hσne : ∀ k ∈ Finset.range M, ∀ ρ ∈ diskZeros f (a + k/2 + 1/4), ρ.re ≠ σ₁)
    (hnz : ∀ t ∈ Set.Icc a (a + M/2), f ((σ₁:ℂ) + t*I) ≠ 0)
    (hH : (∑ k ∈ Finset.range M, ∑ ρ ∈ diskZeros f (a + k/2 + 1/4),
        (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|) * |σ₁ - ρ.re| ^ (-(1:ℝ)/2))
      ≤ 200000 * Real.log (A*(T+4))^2)
    {b : ℝ} (hb1 : a ≤ b) (hb2 : b ≤ a + M/2) :
    ‖∫ t in a..b, (deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖
      ≤ 20000000 * y^σ₁ * Real.log (A*(T+4))^2 := by
  classical
  have hy0 : (0:ℝ) < y := by linarith
  have hA1 := hf.one_le
  set LT : ℝ := Real.log (A*(T+4)) with hLTdef
  have hLT1 : 1 ≤ LT := by
    rw [hLTdef, Real.le_log_iff_exp_le (by nlinarith)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hLT0 : (0:ℝ) < LT := by linarith
  -- continuity on the full segment
  have hcontΦ : ContinuousOn (fun t : ℝ =>
      (deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))) (Set.uIcc a (a + M/2)) := by
    apply contOn_vert_stripInt hf hy0 (by linarith) (by linarith)
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    exact hnz t ht
  have hint : ∀ u v : ℝ, u ∈ Set.Icc a (a + (M:ℝ)/2) → v ∈ Set.Icc a (a + (M:ℝ)/2) →
      IntervalIntegrable (fun t : ℝ =>
        (deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
          * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I)))
        MeasureTheory.volume u v := by
    intro u v hu hv
    apply (hcontΦ.mono _).intervalIntegrable
    apply Set.uIcc_subset_uIcc
    · rw [Set.uIcc_of_le (by linarith)]
      exact hu
    · rw [Set.uIcc_of_le (by linarith)]
      exact hv
  -- step 1: `‖∫_a^b‖ ≤ ∫_a^{a+M/2} ‖Φ‖`
  have hstep1 : ‖∫ t in a..b, (deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
      * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖
      ≤ ∫ t in a..(a + M/2), ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖ := by
    have h1 : ‖∫ t in a..b, (deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖
        ≤ ∫ t in a..b, ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
          * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖ :=
      intervalIntegral.norm_integral_le_integral_norm hb1
    have h2 : (∫ t in a..b, ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖)
        + (∫ t in b..(a + M/2), ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
          * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖)
        = ∫ t in a..(a + M/2), ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
          * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖ := by
      apply intervalIntegral.integral_add_adjacent_intervals
      · exact (hint a b ⟨le_refl _, by linarith⟩ ⟨hb1, hb2⟩).norm
      · exact (hint b (a + M/2) ⟨hb1, hb2⟩ ⟨by linarith, le_refl _⟩).norm
    have h3 : (0:ℝ) ≤ ∫ t in b..(a + M/2),
        ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
          * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖ := by
      apply intervalIntegral.integral_nonneg hb2
      intro t _
      exact norm_nonneg _
    linarith
  -- step 2: decompose into the half-intervals
  have hstep2 : (∫ t in a..(a + M/2), ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
      * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖)
      = ∑ k ∈ Finset.range M, ∫ t in (a + k/2)..(a + (k+1)/2),
        ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
          * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖ := by
    have := intervalIntegral.sum_integral_adjacent_intervals
      (μ := MeasureTheory.volume)
      (a := fun k : ℕ => a + k/2) (n := M)
      (f := fun t : ℝ => ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖)
      (fun k hk => by
        apply IntervalIntegrable.norm
        apply hint
        · rw [Set.mem_Icc]
          have h4 : (k:ℝ) ≤ M := by
            have h6 : k ≤ M := by omega
            exact_mod_cast h6
          have h5 : (0:ℝ) ≤ (k:ℝ)/2 := by positivity
          exact ⟨by linarith, by linarith⟩
        · rw [Set.mem_Icc]
          have h4 : (k:ℝ)+1 ≤ M := by
            have h6 : k + 1 ≤ M := by omega
            exact_mod_cast h6
          have h5 : (0:ℝ) ≤ ((k:ℝ)+1)/2 := by positivity
          push_cast
          exact ⟨by linarith, by linarith⟩)
    symm
    simp only [Nat.cast_zero, Nat.cast_succ] at this ⊢
    convert this using 2; ring
  -- step 3: per-interval bound
  have hstep3 : ∀ k ∈ Finset.range M,
      (∫ t in (a + k/2)..(a + (k+1)/2),
        ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
          * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖)
      ≤ y^σ₁ * ((2080000 * LT)
            * (∫ t in (a + k/2)..(a + (k+1)/2), 1/(1+|t|))
          + 72 * ∑ ρ ∈ diskZeros f (a + k/2 + 1/4),
              (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
                * |σ₁ - ρ.re| ^ (-(1:ℝ)/2)) := by
    intro k hk
    have hkM : (k:ℝ) + 1 ≤ M := by
      rw [Finset.mem_range] at hk
      exact_mod_cast hk
    have hend1 : a + (k:ℝ)/2 = (a + k/2 + 1/4) - 1/4 := by ring
    have hend2 : a + ((k:ℝ)+1)/2 = (a + k/2 + 1/4) + 1/4 := by ring
    have hbnd := edge_interval_bound hf hy hσ1 hσ2
      (hσne k hk) (t₀ := a + k/2 + 1/4) ?_
    · have hmid : |a + (k:ℝ)/2 + 1/4| ≤ T + 2 := by
        rw [abs_le]
        constructor
        · have : (0:ℝ) ≤ (k:ℝ)/2 := by positivity
          linarith
        · have h2 : a + (k:ℝ)/2 + 1/4 ≤ a + ((M:ℝ) - 1)/2 + 1/4 := by linarith
          linarith
      have hlogmid : Real.log (A * (|a + (k:ℝ)/2 + 1/4| + 2)) ≤ LT := by
        rw [hLTdef]
        apply Real.log_le_log (by positivity)
        nlinarith
      have hintpos : (0:ℝ) ≤ ∫ t in ((a + k/2 + 1/4) - 1/4)..((a + k/2 + 1/4) + 1/4),
          1/(1+|t|) := by
        apply intervalIntegral.integral_nonneg (by linarith)
        intro t _
        positivity
      calc (∫ t in (a + k/2)..(a + (k+1)/2),
          ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
            * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖)
          = ∫ t in ((a + k/2 + 1/4) - 1/4)..((a + k/2 + 1/4) + 1/4),
            ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
              * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖ := by
            rw [← hend1, ← hend2]
        _ ≤ y^σ₁ * ((2080000 * Real.log (A*(|a + k/2 + 1/4|+2)))
              * (∫ t in ((a + k/2 + 1/4) - 1/4)..((a + k/2 + 1/4) + 1/4), 1/(1+|t|))
            + 72 * ∑ ρ ∈ diskZeros f (a + k/2 + 1/4),
                (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
                  * |σ₁ - ρ.re| ^ (-(1:ℝ)/2)) := hbnd
        _ ≤ y^σ₁ * ((2080000 * LT)
              * (∫ t in (a + k/2)..(a + (k+1)/2), 1/(1+|t|))
            + 72 * ∑ ρ ∈ diskZeros f (a + k/2 + 1/4),
                (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
                  * |σ₁ - ρ.re| ^ (-(1:ℝ)/2)) := by
            apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy0.le σ₁)
            apply add_le_add
            · have heq : (∫ t in ((a + k/2 + 1/4) - 1/4)..((a + k/2 + 1/4) + 1/4),
                  1/(1+|t|)) = ∫ t in (a + k/2)..(a + (k+1)/2), 1/(1+|t|) := by
                rw [← hend1, ← hend2]
              rw [heq] at hintpos ⊢
              apply mul_le_mul_of_nonneg_right _ hintpos
              nlinarith
            · exact le_refl _
    · intro t ht
      apply hnz t
      rw [Set.mem_Icc]
      have h5 : (0:ℝ) ≤ (k:ℝ)/2 := by positivity
      exact ⟨by linarith [ht.1], by linarith [ht.2, hkM]⟩
  -- assemble
  have hharm2 : ∑ k ∈ Finset.range M,
      (∫ t in (a + k/2)..(a + (k+1)/2), 1/(1+|t|)) ≤ 2 * LT := by
    have hadj : ∑ k ∈ Finset.range M,
        (∫ t in (a + k/2)..(a + (k+1)/2), 1 / (1 + |t|))
        = ∫ t in a..(a + M/2), 1 / (1 + |t|) := by
      have := intervalIntegral.sum_integral_adjacent_intervals
        (μ := MeasureTheory.volume)
        (a := fun k : ℕ => a + k/2) (n := M)
        (f := fun t : ℝ => 1 / (1 + |t|))
        (fun k _ => continuous_one_div_one_add_abs.intervalIntegrable _ _)
      simp only [Nat.cast_zero, Nat.cast_succ] at this ⊢
      convert this using 2; ring
    rw [hadj]
    have hbig := integral_one_div_one_add_abs_le ha0 hM1 (by linarith) hM2
    have hlog2 : Real.log (1 + (T+2)) ≤ LT := by
      rw [hLTdef]
      apply Real.log_le_log (by linarith)
      nlinarith
    linarith
  calc ‖∫ t in a..b, (deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
      * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖
      ≤ ∫ t in a..(a + M/2), ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖ := hstep1
    _ = ∑ k ∈ Finset.range M, ∫ t in (a + k/2)..(a + (k+1)/2),
        ‖(deriv f ((σ₁:ℂ)+t*I) / f ((σ₁:ℂ)+t*I))
          * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖ := hstep2
    _ ≤ ∑ k ∈ Finset.range M,
        y^σ₁ * ((2080000 * LT)
            * (∫ t in (a + k/2)..(a + (k+1)/2), 1/(1+|t|))
          + 72 * ∑ ρ ∈ diskZeros f (a + k/2 + 1/4),
              (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
                * |σ₁ - ρ.re| ^ (-(1:ℝ)/2)) := Finset.sum_le_sum hstep3
    _ = y^σ₁ * ((2080000 * LT)
          * (∑ k ∈ Finset.range M, ∫ t in (a + k/2)..(a + (k+1)/2), 1/(1+|t|))
        + 72 * ∑ k ∈ Finset.range M, ∑ ρ ∈ diskZeros f (a + k/2 + 1/4),
            (analyticOrderNatAt f ρ : ℝ)/(1+|ρ.im|)
              * |σ₁ - ρ.re| ^ (-(1:ℝ)/2)) := by
        symm
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ y^σ₁ * ((2080000 * LT) * (2 * LT) + 72 * (200000 * LT^2)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy0.le σ₁)
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hharm2 (by positivity)
        · exact mul_le_mul_of_nonneg_left hH (by norm_num)
    _ ≤ 20000000 * y^σ₁ * LT^2 := by
        have h1 : (0:ℝ) ≤ y^σ₁ := Real.rpow_nonneg hy0.le σ₁
        nlinarith [hLT0]
    _ = 20000000 * y^σ₁ * Real.log (A*(T+4))^2 := by rw [hLTdef]

end LeftEdge

/-! ### Conjugation transfer, horizontal edges, right-edge extras -/

section Conjugation

/-- The conjugate-reflected function. -/
noncomputable def conjF (f : ℂ → ℂ) : ℂ → ℂ :=
  fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w))

lemma conjF_conjF (f : ℂ → ℂ) : conjF (conjF f) = f := by
  funext w
  simp [conjF]

lemma conj_center (t₀ : ℝ) :
    (starRingEnd ℂ) ((2:ℂ) + t₀ * I) = (2:ℂ) + (-t₀ : ℝ) * I := by
  apply Complex.ext <;> simp

lemma conj_coord (x t : ℝ) :
    (starRingEnd ℂ) ((x:ℂ) + t * I) = (x:ℂ) + (-t : ℝ) * I := by
  apply Complex.ext <;> simp

lemma conj_mem_ball {z c : ℂ} {r : ℝ} (h : z ∈ closedBall c r) :
    (starRingEnd ℂ) z ∈ closedBall ((starRingEnd ℂ) c) r := by
  rw [mem_closedBall, Complex.dist_eq] at h ⊢
  rw [← map_sub, Complex.norm_conj]
  exact h

/-- `DiskData` transfers through conjugate reflection. -/
lemma DiskData.conj {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) :
    DiskData (conjF f) A := by
  constructor
  · exact hf.one_le
  · intro t₀ z hz
    -- `f` is analytic at `conj z`, hence differentiable near it
    have hz' : (starRingEnd ℂ) z ∈ closedBall ((2:ℂ) + (-t₀ : ℝ) * I) (7/4 : ℝ) := by
      have := conj_mem_ball hz
      rwa [conj_center] at this
    have hfz : AnalyticAt ℂ f ((starRingEnd ℂ) z) := hf.diff (-t₀) _ hz'
    have hev : ∀ᶠ w in 𝓝 ((starRingEnd ℂ) z), DifferentiableAt ℂ f w := by
      filter_upwards [hfz.eventually_analyticAt] with w hw
      exact hw.differentiableAt
    obtain ⟨U, hUdiff, hUopen, hUmem⟩ := _root_.eventually_nhds_iff.mp hev
    have hVopen : IsOpen ((starRingEnd ℂ) ⁻¹' U) :=
      hUopen.preimage Complex.continuous_conj
    have hVz : z ∈ (starRingEnd ℂ) ⁻¹' U := by
      show (starRingEnd ℂ) z ∈ U
      exact hUmem
    apply DifferentiableOn.analyticAt (s := (starRingEnd ℂ) ⁻¹' U)
    · intro w hw
      have h1 : DifferentiableAt ℂ f ((starRingEnd ℂ) w) := hUdiff _ hw
      have h2 := h1.conj_conj
      rw [Complex.conj_conj] at h2
      exact h2.differentiableWithinAt
    · exact hVopen.mem_nhds hVz
  · intro t₀
    have h1 := hf.low (-t₀)
    rw [conjF]
    rw [show (starRingEnd ℂ) ((2:ℂ) + t₀ * I) = (2:ℂ) + (-t₀ : ℝ) * I from
      conj_center t₀]
    rwa [Complex.norm_conj]
  · intro t₀ z hz
    have hz' : (starRingEnd ℂ) z ∈ closedBall ((2:ℂ) + (-t₀ : ℝ) * I) (7/4 : ℝ) := by
      have := conj_mem_ball hz
      rwa [conj_center] at this
    have h1 := hf.bd (-t₀) _ hz'
    rw [conjF, Complex.norm_conj]
    rwa [abs_neg] at h1
  · intro s hs
    have h1 : 1 < ((starRingEnd ℂ) s).re := by
      rwa [Complex.conj_re]
    have h2 := hf.nz _ h1
    rw [conjF, ne_eq, map_eq_zero]
    exact h2

/-- Norm of the logarithmic derivative transfers through reflection. -/
lemma norm_logDeriv_conjF (f : ℂ → ℂ) (w : ℂ) :
    ‖deriv f w / f w‖
      = ‖deriv (conjF f) ((starRingEnd ℂ) w) / conjF f ((starRingEnd ℂ) w)‖ := by
  have h1 : deriv (conjF f) = fun z => (starRingEnd ℂ) (deriv f ((starRingEnd ℂ) z)) := by
    have := deriv_conj_conj (f := f)
    rw [show (starRingEnd ℂ) ∘ f ∘ (starRingEnd ℂ) = conjF f from rfl] at this
    rw [this]
    rfl
  rw [h1]
  simp only [conjF, Complex.conj_conj]
  rw [← map_div₀, Complex.norm_conj]

/-- Value of `f` below the axis in terms of the reflection. -/
lemma conjF_eval (f : ℂ → ℂ) (w : ℂ) :
    f w = (starRingEnd ℂ) (conjF f ((starRingEnd ℂ) w)) := by
  simp [conjF]

end Conjugation

section HorizEdge

/-- Continuity of the strip integrand along a horizontal segment. -/
lemma contOn_horiz_stripInt {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) {y : ℝ}
    (hy : 0 < y) {t₀ : ℝ} {a b : ℝ} (ha : 1/4 ≤ a) (hb : b ≤ 15/4)
    (_hab : a ≤ b) (ht₀ : t₀ ≠ 0)
    (hnz : ∀ x ∈ Set.Icc a b, f ((x:ℂ) + t₀*I) ≠ 0) :
    ContinuousOn (fun x : ℝ =>
      (deriv f ((x:ℂ)+t₀*I) / f ((x:ℂ)+t₀*I))
        * ((y:ℂ)^((x:ℂ)+t₀*I) / ((x:ℂ)+t₀*I))) (Set.Icc a b) := by
  have hyC : (y:ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hy.ne'
  have hentire : Differentiable ℂ (fun s : ℂ => (y:ℂ) ^ s) := fun s =>
    differentiableAt_id.const_cpow (Or.inl hyC)
  have hbase : Continuous (fun x : ℝ => (x:ℂ) + t₀*I) :=
    (Complex.continuous_ofReal).add continuous_const
  have hmem : ∀ x ∈ Set.Icc a b, ((x:ℂ) + t₀*I) ∈ closedBall ((2:ℂ) + t₀*I) (7/4:ℝ) := by
    intro x hx
    rw [mem_closedBall, Complex.dist_eq]
    have h1 : ((x:ℂ) + t₀*I) - ((2:ℂ) + t₀*I) = ((x - 2 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  apply ContinuousOn.mul
  · apply ContinuousOn.div
    · intro x hx
      have h1 : ContinuousAt (deriv f) ((fun u : ℝ => (u:ℂ)+t₀*I) x) :=
        (hf.diff t₀ ((x:ℂ)+t₀*I) (hmem x hx)).deriv.continuousAt
      have h3 : ContinuousAt ((deriv f) ∘ (fun u : ℝ => (u:ℂ)+t₀*I)) x :=
        ContinuousAt.comp h1 hbase.continuousAt
      exact h3.continuousWithinAt
    · intro x hx
      have h1 : ContinuousAt f ((fun u : ℝ => (u:ℂ)+t₀*I) x) :=
        (hf.diff t₀ ((x:ℂ)+t₀*I) (hmem x hx)).continuousAt
      have h3 : ContinuousAt (f ∘ (fun u : ℝ => (u:ℂ)+t₀*I)) x :=
        ContinuousAt.comp h1 hbase.continuousAt
      exact h3.continuousWithinAt
    · exact hnz
  · apply ContinuousOn.div
    · exact (hentire.continuous.comp hbase).continuousOn
    · exact hbase.continuousOn
    · intro x _
      exact coord_ne_zero_of_im ht₀

/-- **Horizontal edge bound.** -/
lemma horiz_edge_le {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) {y σ₁ c t₀ B : ℝ}
    (hy : 100 ≤ y) (hσ1 : 9/16 ≤ σ₁) (hσc : σ₁ ≤ c) (hc : c ≤ 5/4)
    (hcy : y ^ c ≤ 3 * y) (ht₀ : 2 ≤ |t₀|) (hB : 0 ≤ B)
    (hnz : ∀ x ∈ Set.Icc σ₁ c, f ((x:ℂ) + t₀*I) ≠ 0)
    (hbd : ∀ x ∈ Set.Icc σ₁ c,
      ‖deriv f ((x:ℂ) + t₀*I) / f ((x:ℂ) + t₀*I)‖ ≤ B) :
    ‖∫ x in σ₁..c, (deriv f ((x:ℂ)+t₀*I) / f ((x:ℂ)+t₀*I))
        * ((y:ℂ)^((x:ℂ)+t₀*I) / ((x:ℂ)+t₀*I))‖
      ≤ B * (3 * y) / (|t₀| * Real.log y) := by
  have hy0 : (0:ℝ) < y := by linarith
  have hlogy : 4 ≤ Real.log y := four_le_log hy
  have hlogy0 : (0:ℝ) < Real.log y := by linarith
  have ht₀0 : (0:ℝ) < |t₀| := by linarith
  have ht₀ne : t₀ ≠ 0 := by
    intro h
    rw [h] at ht₀
    simp at ht₀
    linarith
  -- pointwise bound
  have hptw : ∀ x ∈ Set.Icc σ₁ c,
      ‖(deriv f ((x:ℂ)+t₀*I) / f ((x:ℂ)+t₀*I))
        * ((y:ℂ)^((x:ℂ)+t₀*I) / ((x:ℂ)+t₀*I))‖ ≤ B * (y ^ x / |t₀|) := by
    intro x hx
    rw [norm_mul]
    have hys : ‖(y:ℂ)^((x:ℂ)+t₀*I) / ((x:ℂ)+t₀*I)‖ ≤ y ^ x / |t₀| := by
      rw [norm_div, norm_cpow_coord hy0]
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le x) ht₀0
        (norm_coord_ge_abs_im x t₀)
    exact mul_le_mul (hbd x hx) hys (norm_nonneg _) hB
  -- the majorant integral
  have hcontpow : Continuous (fun x : ℝ => y ^ x) := by
    have h : (fun x : ℝ => y ^ x) = fun x => Real.exp (Real.log y * x) := by
      funext x
      rw [Real.rpow_def_of_pos hy0, mul_comm]
    rw [h]
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hint2 : IntervalIntegrable (fun x : ℝ => B * (y ^ x / |t₀|))
      MeasureTheory.volume σ₁ c :=
    (continuous_const.mul (hcontpow.div_const _)).intervalIntegrable _ _
  have h1 : ‖∫ x in σ₁..c, (deriv f ((x:ℂ)+t₀*I) / f ((x:ℂ)+t₀*I))
      * ((y:ℂ)^((x:ℂ)+t₀*I) / ((x:ℂ)+t₀*I))‖
      ≤ ∫ x in σ₁..c, ‖(deriv f ((x:ℂ)+t₀*I) / f ((x:ℂ)+t₀*I))
        * ((y:ℂ)^((x:ℂ)+t₀*I) / ((x:ℂ)+t₀*I))‖ :=
    intervalIntegral.norm_integral_le_integral_norm hσc
  have h2 : (∫ x in σ₁..c, ‖(deriv f ((x:ℂ)+t₀*I) / f ((x:ℂ)+t₀*I))
      * ((y:ℂ)^((x:ℂ)+t₀*I) / ((x:ℂ)+t₀*I))‖)
      ≤ ∫ x in σ₁..c, B * (y ^ x / |t₀|) := by
    apply intervalIntegral.integral_mono_on hσc _ hint2 hptw
    have hcont := (contOn_horiz_stripInt hf hy0 (by linarith) (by linarith) hσc
      ht₀ne hnz).norm
    rw [← Set.uIcc_of_le hσc] at hcont
    exact hcont.intervalIntegrable
  have h3 : (∫ x in σ₁..c, B * (y ^ x / |t₀|))
      = (B / |t₀|) * ((y ^ c - y ^ σ₁) / Real.log y) := by
    rw [show (fun x : ℝ => B * (y ^ x / |t₀|))
      = fun x : ℝ => (B / |t₀|) * y ^ x from by funext x; ring]
    rw [intervalIntegral.integral_const_mul, integral_const_rpow hy0 hlogy0.ne']
  have h4 : y ^ c - y ^ σ₁ ≤ 3 * y := by
    have h6 : (0:ℝ) ≤ y ^ σ₁ := Real.rpow_nonneg hy0.le σ₁
    linarith
  calc ‖∫ x in σ₁..c, (deriv f ((x:ℂ)+t₀*I) / f ((x:ℂ)+t₀*I))
      * ((y:ℂ)^((x:ℂ)+t₀*I) / ((x:ℂ)+t₀*I))‖
      ≤ ∫ x in σ₁..c, B * (y ^ x / |t₀|) := le_trans h1 h2
    _ = (B / |t₀|) * ((y ^ c - y ^ σ₁) / Real.log y) := h3
    _ ≤ (B / |t₀|) * ((3 * y) / Real.log y) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact div_le_div_right_of_pos hlogy0 h4
    _ = B * (3 * y) / (|t₀| * Real.log y) := by
        field_simp

end HorizEdge

/-! ### The right edge on `Re s = c` and the two instantiations -/

section RightEdge

open scoped LSeries.notation ArithmeticFunction

variable {N : ℕ} [NeZero N]

/-- On `Re s = c > 1`: `‖L′/L‖ ≤ 6/(c−1)²`. -/
lemma norm_logDeriv_LFunction_le (χ : DirichletCharacter ℂ N) {c : ℝ}
    (hc1 : 1 < c) (hc2 : c ≤ 2) (t : ℝ) :
    ‖deriv (DirichletCharacter.LFunction χ) ((c:ℂ) + t*I)
      / DirichletCharacter.LFunction χ ((c:ℂ) + t*I)‖ ≤ 6 / (c-1)^2 := by
  have hsre : 1 < ((c:ℂ) + t*I).re := by rw [re_coord]; exact hc1
  have hL := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hsre
  have hLf := DirichletCharacter.LFunction_eq_LSeries χ hsre
  have hLd := DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hsre
  have hkey : deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
      / DirichletCharacter.LFunction χ ((c:ℂ)+t*I)
      = - LSeries (↗χ * ↗Λ) ((c:ℂ)+t*I) := by
    rw [hLf, hLd, hL]
    ring
  rw [hkey, norm_neg]
  have hterm : ∀ n : ℕ, ‖LSeries.term (↗χ * ↗Λ) ((c:ℂ)+t*I) n‖
      ≤ ArithmeticFunction.vonMangoldt n * (n:ℝ) ^ (-c) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn.ne']

      simp only [Pi.mul_apply]
      rw [norm_div, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Complex.norm_natCast_cpow_of_pos hn, re_coord]
      have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
      have h1 : ‖χ (n : ZMod N)‖ ≤ 1 := χ.norm_le_one _
      have h2 : (n:ℝ) ^ (-c) = ((n:ℝ) ^ c)⁻¹ := by
        rw [Real.rpow_neg hn0.le]
      rw [h2]
      have h3 : (0:ℝ) < (n:ℝ) ^ c := Real.rpow_pos_of_pos hn0 c
      rw [div_le_iff₀ h3, mul_assoc, inv_mul_cancel₀ h3.ne', mul_one]
      calc ‖χ (n : ZMod N)‖ * ArithmeticFunction.vonMangoldt n
          ≤ 1 * ArithmeticFunction.vonMangoldt n :=
            mul_le_mul_of_nonneg_right h1 ArithmeticFunction.vonMangoldt_nonneg
        _ = ArithmeticFunction.vonMangoldt n := one_mul _
  have hsumnorm : Summable (fun n : ℕ => ‖LSeries.term (↗χ * ↗Λ) ((c:ℂ)+t*I) n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm
      (summable_vonMangoldt_rpow hc1)
  calc ‖LSeries (↗χ * ↗Λ) ((c:ℂ)+t*I)‖
      ≤ ∑' n : ℕ, ‖LSeries.term (↗χ * ↗Λ) ((c:ℂ)+t*I) n‖ :=
        norm_tsum_le_tsum_norm hsumnorm
    _ ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt n * (n:ℝ) ^ (-c) :=
        Summable.tsum_le_tsum hterm hsumnorm (summable_vonMangoldt_rpow hc1)
    _ ≤ 6 / (c-1)^2 := tsum_vonMangoldt_rpow_le hc1 hc2

/-- Right-edge overshoot segments: length `≤ 1`, height `≥ T`. -/
lemma right_extra_le (χ : DirichletCharacter ℂ N) {y c T u v : ℝ}
    (hy : 100 ≤ y) (hc : c = 1 + 1/Real.log y) (hT : 2 ≤ T)
    (huv : u ≤ v) (hlen : v - u ≤ 1) (hfar : ∀ t ∈ Set.Icc u v, T ≤ |t|) :
    ‖∫ t in u..v, (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
        / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
      * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))‖
      ≤ 18 * (y * Real.log y ^ 2 / T) := by
  have hy0 : (0:ℝ) < y := by linarith
  have hlogy : 4 ≤ Real.log y := four_le_log hy
  have hlogy0 : (0:ℝ) < Real.log y := by linarith
  have hinvlog : 1 / Real.log y ≤ 1/4 :=
    one_div_le_one_div_of_le (by norm_num) hlogy
  have hinvlog0 : 0 < 1 / Real.log y := one_div_pos.mpr hlogy0
  have hc1 : 1 < c := by rw [hc]; linarith
  have hc2 : c ≤ 2 := by rw [hc]; linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hyc : y ^ c = Real.exp 1 * y := by rw [hc]; exact rpow_one_add_inv_log hy
  have hyc3 : y ^ c ≤ 3 * y := by
    rw [hyc]
    nlinarith [Real.exp_one_lt_d9]
  have hcsub : c - 1 = 1 / Real.log y := by rw [hc]; ring
  have he6 : 6 / (c - 1) ^ 2 = 6 * Real.log y ^ 2 := by
    rw [hcsub, one_div, inv_pow, div_inv_eq_mul]
  have hC : ∀ t ∈ Set.uIoc u v,
      ‖(deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
          / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))‖
      ≤ (6 * Real.log y ^ 2) * (3 * y / T) := by
    intro t ht
    have htmem : t ∈ Set.Icc u v := by
      rw [Set.uIoc_of_le huv] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩
    have hTt := hfar t htmem
    rw [norm_mul]
    have h1 : ‖deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
        / DirichletCharacter.LFunction χ ((c:ℂ)+t*I)‖ ≤ 6 * Real.log y ^ 2 := by
      have := norm_logDeriv_LFunction_le χ hc1 hc2 t
      rwa [he6] at this
    have h2 : ‖(y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)‖ ≤ 3 * y / T := by
      rw [norm_div, norm_cpow_coord hy0]
      have h3 : T ≤ ‖(c:ℂ)+t*I‖ := le_trans hTt (norm_coord_ge_abs_im c t)
      calc y ^ c / ‖(c:ℂ)+t*I‖ ≤ y ^ c / T := by
            apply div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le c) hT0 h3
        _ ≤ 3 * y / T := div_le_div_right_of_pos hT0 hyc3
    apply mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  calc ‖∫ t in u..v, (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
        / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
      * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))‖
      ≤ (6 * Real.log y ^ 2) * (3 * y / T) * |v - u| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hC
    _ ≤ (6 * Real.log y ^ 2) * (3 * y / T) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [abs_of_nonneg (by linarith)]
        exact hlen
    _ = 18 * (y * Real.log y ^ 2 / T) := by ring

end RightEdge

/-! ### The two instantiations of `DiskData` -/

section Instances

variable {N : ℕ} [NeZero N]

/-- `DiskData` for the L-function of a nontrivial character, `A = N`. -/
lemma diskData_LFunction (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DiskData (DirichletCharacter.LFunction χ) N := by
  constructor
  · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  · intro t₀ z _
    exact (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  · intro t₀
    have h13 := one_third_le_norm_LFunction_of_two_le_re χ
      (s := (2:ℂ) + t₀ * I) (by rw [re_center])
    linarith
  · intro t₀ z hz
    have h1 := norm_LFunction_le_of_one_quarter_le_re χ hχ (disk_re_ge hz)
    have h2 := disk_norm_le hz
    have hN1 : (1:ℝ) ≤ N := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    calc ‖DirichletCharacter.LFunction χ z‖ ≤ 5 * N * (2 + ‖z‖) := h1
      _ ≤ 5 * N * (2 + (|t₀| + 15/4)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ 15 * ((N:ℝ) * (|t₀| + 2)) := by
          nlinarith [abs_nonneg t₀, mul_nonneg (by positivity : (0:ℝ) ≤ (N:ℝ))
            (abs_nonneg t₀)]
  · intro s hs
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le

/-- Termwise bound for the Abel-summed eta series (copy of the ZeroCount
private lemma). -/
lemma norm_etaTerm_le' {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ‖etaTerm s k‖ ≤ ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [etaTerm, Nat.zero_mod, Nat.cast_zero, zero_mul, norm_zero]
    positivity
  · have h1 : ‖((k % 2 : ℕ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_natCast]
      exact_mod_cast Nat.lt_succ_iff.mp (Nat.mod_lt k (by norm_num))
    calc ‖etaTerm s k‖
        = ‖((k % 2 : ℕ) : ℂ)‖ * ‖((k : ℕ) : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s)‖ :=
          norm_mul _ _
      _ ≤ 1 * (‖s‖ * (k : ℝ) ^ (-s.re - 1)) :=
          mul_le_mul h1 (norm_cpow_sub_cpow_le hs hk) (norm_nonneg _) (by norm_num)
      _ = ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by ring

/-- Differentiability of the eta function on the right half-plane (copy of the
ZeroCount private lemma). -/
lemma differentiableOn_etaFun' :
    DifferentiableOn ℂ etaFun {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hσ : 0 < s₀.re := hs₀
  set r : ℝ := s₀.re / 2 with hr
  have hrpos : 0 < r := by positivity
  suffices h : DifferentiableOn ℂ etaFun (Metric.ball s₀ r) by
    exact (h.differentiableAt (Metric.ball_mem_nhds s₀ hrpos)).differentiableWithinAt
  have hre : ∀ w ∈ Metric.ball s₀ r, r ≤ w.re := by
    intro w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    have h1 : |(w - s₀).re| ≤ ‖w - s₀‖ := Complex.abs_re_le_norm _
    have h2 : |(w - s₀).re| < r := lt_of_le_of_lt h1 hw
    rw [Complex.sub_re, abs_lt] at h2
    linarith [h2.1]
  have hnorm : ∀ w ∈ Metric.ball s₀ r, ‖w‖ ≤ ‖s₀‖ + r := by
    intro w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    calc ‖w‖ = ‖s₀ + (w - s₀)‖ := by ring_nf
      _ ≤ ‖s₀‖ + ‖w - s₀‖ := norm_add_le _ _
      _ ≤ ‖s₀‖ + r := by linarith
  refine differentiableOn_tsum_of_summable_norm
    (u := fun k : ℕ => (‖s₀‖ + r) * (k : ℝ) ^ (-r - 1))
    ?_ ?_ Metric.isOpen_ball ?_
  · exact ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _)
  · intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h0 : (fun s : ℂ => etaTerm s 0) = fun _ => 0 := by
        funext w
        simp [etaTerm]
      rw [h0]
      exact differentiableOn_const 0
    · have hk0 : ((k : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.pos_iff_ne_zero.mp hk
      have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero k
      have hneg : Differentiable ℂ (fun s : ℂ => -s) := differentiable_id.neg
      have hd : Differentiable ℂ (fun s : ℂ => etaTerm s k) := by
        unfold etaTerm
        exact ((hneg.const_cpow (Or.inl hk0)).sub
          (hneg.const_cpow (Or.inl hk1))).const_mul _
      exact hd.differentiableOn
  · intro k w hw
    have hwre : 0 < w.re := lt_of_lt_of_le hrpos (hre w hw)
    calc ‖etaTerm w k‖ ≤ ‖w‖ * (k : ℝ) ^ (-w.re - 1) := norm_etaTerm_le' hwre k
      _ ≤ (‖s₀‖ + r) * (k : ℝ) ^ (-r - 1) := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · rw [Nat.cast_zero, Real.zero_rpow (ne_of_lt (by linarith) : -w.re - 1 ≠ 0),
              Real.zero_rpow (ne_of_lt (by linarith) : -r - 1 ≠ 0), mul_zero, mul_zero]
          · have hk1 : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
            have hrw : (k : ℝ) ^ (-w.re - 1) ≤ (k : ℝ) ^ (-r - 1) :=
              Real.rpow_le_rpow_of_exponent_le hk1 (by linarith [hre w hw])
            have h3 : (0:ℝ) ≤ (k : ℝ) ^ (-w.re - 1) := Real.rpow_nonneg (by positivity) _
            have h4 : (0:ℝ) ≤ ‖s₀‖ + r := by positivity
            exact mul_le_mul (hnorm w hw) hrw h3 h4

/-- `DiskData` for the Abel-summed eta function, `A = 1`. -/
lemma diskData_etaFun : DiskData etaFun 1 := by
  constructor
  · exact le_refl 1
  · intro t₀ z hz
    have hre := disk_re_ge hz
    have hopen : IsOpen {s : ℂ | 0 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    exact (differentiableOn_etaFun'.analyticOnNhd hopen).mono
      (fun w hw => by
        have := disk_re_ge hw
        show (0:ℝ) < w.re
        linarith) z hz
  · intro t₀
    -- from the eta–zeta factorization at `Re = 2`
    have hmem2 : ((2:ℂ) + t₀ * I) ∈ {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
      constructor
      · rw [re_center]
        norm_num
      · intro h1
        have h2 := congrArg Complex.re h1
        rw [re_center] at h2
        simp at h2
    rw [etaFun_eqOn hmem2, norm_mul]
    have hζ : 1/3 ≤ ‖riemannZeta ((2:ℂ) + t₀ * I)‖ := by
      have h13 := one_third_le_norm_LFunction_of_two_le_re (N := 1)
        (1 : DirichletCharacter ℂ 1) (s := (2:ℂ) + t₀ * I) (by rw [re_center])
      rwa [DirichletCharacter.LFunction_modOne_eq] at h13
    have hfac : 1/2 ≤ ‖1 - (2:ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀ * I))‖ := by
      have hnorm : ‖(2:ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀ * I))‖ = 1/2 := by
        have hb : (2:ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀ * I))
            = ((2:ℝ):ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀ * I)) := by norm_num
        have hre : ((1:ℂ) - ((2:ℂ) + t₀ * I)).re = -1 := by
          simp
          norm_num
        rw [hb, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2), hre,
          Real.rpow_neg_one]
        norm_num
      calc (1/2 : ℝ) = ‖(1:ℂ)‖ - 1/2 := by simp; norm_num
        _ = ‖(1:ℂ)‖ - ‖(2:ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀ * I))‖ := by rw [hnorm]
        _ ≤ ‖1 - (2:ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀ * I))‖ := norm_sub_norm_le _ _
    nlinarith [norm_nonneg (1 - (2:ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀ * I))),
      norm_nonneg (riemannZeta ((2:ℂ) + t₀ * I))]
  · intro t₀ z hz
    have h1 := norm_etaFun_le_of_one_quarter_le_re (disk_re_ge hz)
    have h2 := disk_norm_le hz
    simp only [one_mul]
    linarith [abs_nonneg t₀]
  · intro s hs
    -- `η = (1 − 2^{1−s})·ζ` and both factors are nonzero on `Re > 1`
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1] at hs
      simp at hs
    have hmem : s ∈ {s : ℂ | 0 < s.re ∧ s ≠ 1} := ⟨by linarith, hs1⟩
    have hη := etaFun_eqOn hmem
    rw [hη]
    apply mul_ne_zero
    · intro h0
      rw [sub_eq_zero] at h0
      have h1 : ‖(2:ℂ) ^ ((1:ℂ) - s)‖ < 1 := by
        have hb : (2:ℂ) ^ ((1:ℂ) - s) = ((2:ℝ):ℂ) ^ ((1:ℂ) - s) := by norm_num
        rw [hb, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2)]
        apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
        have : ((1:ℂ) - s).re = 1 - s.re := by simp
        rw [this]
        linarith
      rw [← h0] at h1
      simp at h1
    · exact riemannZeta_ne_zero_of_one_le_re hs.le

end Instances

/-! ### Assembly toolkit: cuts, edge extraction, sum differences -/

section Toolkit

/-- Choice of strictly monotone cut heights from `−t₁` to `t₂` with gaps `≤ 1`,
interior cuts avoiding a given finite set. -/
lemma exists_cuts (S : Finset ℝ) {t₁ t₂ : ℝ} (h4 : 4 ≤ t₁ + t₂) :
    ∃ (m : ℕ) (τ : ℕ → ℝ), 1 ≤ m ∧ τ 0 = -t₁ ∧ τ m = t₂ ∧
      (∀ j < m, τ j < τ (j+1)) ∧ (∀ j < m, τ (j+1) - τ j ≤ 1) ∧
      (∀ j, 0 < j → j < m → τ j ∉ S) ∧
      (∀ j ≤ m, -t₁ ≤ τ j ∧ τ j ≤ t₂) := by
  classical
  set m : ℕ := ⌈2 * (t₁ + t₂)⌉₊ with hmdef
  have hsum0 : (0:ℝ) < t₁ + t₂ := by linarith
  have hmceil : 2 * (t₁ + t₂) ≤ (m : ℝ) := Nat.le_ceil _
  have hmceil' : (m : ℝ) < 2 * (t₁ + t₂) + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  have hm8 : 8 ≤ m := by
    have h1 : (8:ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast h1
  have hm0 : (0:ℝ) < (m : ℝ) := by
    have : (8:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm8
    linarith
  set d : ℝ := (t₁ + t₂) / m with hddef
  have hmd : (m : ℝ) * d = t₁ + t₂ := by
    rw [hddef]
    field_simp
  have hd1 : d ≤ 1/2 := by
    rw [hddef, div_le_iff₀ hm0]
    linarith
  have hd2 : 1/4 ≤ d := by
    rw [hddef, le_div_iff₀ hm0]
    linarith
  -- interior cut choice, avoiding the finite bad set
  have hex : ∀ j : ℕ, ∃ ε : ℝ, (0 ≤ ε ∧ ε ≤ 1/8) ∧ (-t₁ + j*d + ε) ∉ (S : Set ℝ) := by
    intro j
    have hbadfin : {ε : ℝ | -t₁ + j*d + ε ∈ (S : Set ℝ)}.Finite := by
      have h1 : {ε : ℝ | -t₁ + j*d + ε ∈ (S : Set ℝ)}
          = (fun ε : ℝ => -t₁ + j*d + ε) ⁻¹' (S : Set ℝ) := rfl
      rw [h1]
      apply Set.Finite.preimage _ (S.finite_toSet)
      intro x _ z _ h
      simpa using h
    have hIccInf : (Set.Icc (0:ℝ) (1/8)).Infinite :=
      Set.Icc_infinite (by norm_num)
    obtain ⟨ε, hε⟩ := (hIccInf.sdiff hbadfin).nonempty
    exact ⟨ε, ⟨hε.1.1, hε.1.2⟩, hε.2⟩
  choose ε hεmem hεS using hex
  set τ : ℕ → ℝ := fun j => if j = 0 then -t₁ else if m ≤ j then t₂
    else -t₁ + j*d + ε j with hτdef
  have hv0 : τ 0 = -t₁ := by
    rw [hτdef]
    beta_reduce
    rw [if_pos rfl]
  have hvm : ∀ i : ℕ, m ≤ i → τ i = t₂ := by
    intro i hi
    rw [hτdef]
    beta_reduce
    rw [if_neg (by omega : ¬ i = 0), if_pos hi]
  have hvi : ∀ i : ℕ, 0 < i → i < m → τ i = -t₁ + i*d + ε i := by
    intro i h1 h2
    rw [hτdef]
    beta_reduce
    rw [if_neg (by omega : ¬ i = 0), if_neg (by omega : ¬ m ≤ i)]
  have hcast1 : ∀ i : ℕ, ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by
    intro i
    push_cast
    ring
  have hmd1 : (0:ℝ) ≤ (m:ℝ) - 1 := by
    have : (8:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm8
    linarith
  have hεb : ∀ i : ℕ, 0 ≤ ε i ∧ ε i ≤ 1/8 := hεmem
  have ht2v : t₂ = -t₁ + (m:ℝ)*d := by rw [hmd]; ring
  have hjm1cast : ∀ j : ℕ, j = m - 1 → (j : ℝ) = (m : ℝ) - 1 := by
    intro j hj
    rw [hj]
    push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
    ring
  refine ⟨m, τ, by omega, hv0, hvm m (le_refl m), ?_, ?_, ?_, ?_⟩
  · -- strict monotonicity
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hv0, hvi 1 (by omega) (by omega)]
      push_cast
      have := (hεb 1).1
      linarith
    · rcases Nat.lt_or_ge (j+1) m with h1 | h1
      · rw [hvi j hj0 (by omega), hvi (j+1) (by omega) h1, hcast1 j]
        have h2 := (hεb j).2
        have h3 := (hεb (j+1)).1
        linarith
      · have hjm : j + 1 = m := by omega
        rw [hvi j hj0 (by omega), hvm (j+1) (by omega), ht2v,
          hjm1cast j (by omega)]
        have h2 := (hεb j).2
        nlinarith
  · -- gaps at most 1
    intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hv0, hvi 1 (by omega) (by omega)]
      push_cast
      have := (hεb 1).2
      linarith
    · rcases Nat.lt_or_ge (j+1) m with h1 | h1
      · rw [hvi j hj0 (by omega), hvi (j+1) (by omega) h1, hcast1 j]
        have h2 := (hεb j).1
        have h3 := (hεb (j+1)).2
        linarith
      · have hjm : j + 1 = m := by omega
        rw [hvi j hj0 (by omega), hvm (j+1) (by omega), ht2v,
          hjm1cast j (by omega)]
        have h2 := (hεb j).1
        nlinarith
  · -- interior avoidance
    intro j hj0 hjm
    rw [hvi j hj0 hjm]
    exact fun h => hεS j h
  · -- range bounds
    intro j hjm
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hv0]
      constructor
      · linarith
      · linarith
    · rcases Nat.lt_or_ge j m with h1 | h1
      · rw [hvi j hj0 h1]
        have h2 := (hεb j).1
        have h3 := (hεb j).2
        have hjd : (0:ℝ) ≤ (j:ℝ)*d := by positivity
        constructor
        · linarith
        · have hjm1 : (j:ℝ) ≤ (m:ℝ) - 1 := by
            have h9 : j ≤ m - 1 := by omega
            have h4 : (j:ℝ) ≤ ((m - 1 : ℕ) : ℝ) := by exact_mod_cast h9
            have h5 : ((m - 1 : ℕ) : ℝ) = (m:ℝ) - 1 := by
              push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
              ring
            linarith
          have h6 : (j:ℝ)*d ≤ ((m:ℝ)-1)*d := by
            apply mul_le_mul_of_nonneg_right hjm1 (by linarith)
          nlinarith
      · rw [hvm j h1]
        constructor
        · linarith
        · linarith

/-- Unfolding the rectangle boundary integral into its four edges, in the
coordinates of the Route-Z rectangle. -/
lemma rectInt_edges (F : ℂ → ℂ) (σ₁ cc t₁ t₂ : ℝ) :
    rectInt F ((σ₁:ℂ) + (-t₁ : ℝ)*I) ((cc:ℂ) + t₂*I)
      = (∫ x in σ₁..cc, F ((x:ℂ) + (-t₁ : ℝ)*I))
        - (∫ x in σ₁..cc, F ((x:ℂ) + t₂*I))
        + I * (∫ t in (-t₁)..t₂, F ((cc:ℂ) + t*I))
        - I * (∫ t in (-t₁)..t₂, F ((σ₁:ℂ) + t*I)) := by
  unfold rectInt
  simp only [re_coord, im_coord, smul_eq_mul]

/-- Difference of finset sums via symmetric differences. -/
lemma sum_sub_sum_eq {α : Type*} [DecidableEq α] (s t : Finset α) (g : α → ℂ) :
    ∑ x ∈ s, g x - ∑ x ∈ t, g x
      = ∑ x ∈ s \ t, g x - ∑ x ∈ t \ s, g x := by
  have h1 : ∑ x ∈ s \ t, g x + ∑ x ∈ s ∩ t, g x = ∑ x ∈ s, g x := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter s t)]
    congr 1
    rw [Finset.sdiff_union_inter]
  have h2 : ∑ x ∈ t \ s, g x + ∑ x ∈ t ∩ s, g x = ∑ x ∈ t, g x := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter t s)]
    congr 1
    rw [Finset.sdiff_union_inter]
  have h3 : ∑ x ∈ s ∩ t, g x = ∑ x ∈ t ∩ s, g x := by
    rw [Finset.inter_comm]
  rw [← h1, ← h2, h3]
  ring

/-- Mass of zeros in the band `T < |Im| ≤ T+1`, `1/2 ≤ Re ≤ 3/2`: at most
`224·log(A(T+4))`. -/
lemma band_mass_le {f : ℂ → ℂ} {A : ℝ} (hf : DiskData f A) {T : ℝ} (hT : 2 ≤ T)
    {Z : Finset ℂ}
    (hZ : ∀ ρ ∈ Z, 1/2 ≤ ρ.re ∧ ρ.re ≤ 3/2 ∧ T < |ρ.im| ∧ |ρ.im| ≤ T + 1) :
    (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ 224 * Real.log (A * (T+4)) := by
  classical
  have hA1 := hf.one_le
  have hgeo : ∀ (sgn : ℝ), sgn = 1 ∨ sgn = -1 → ∀ ρ ∈ Z,
      (0 ≤ ρ.im ↔ sgn = 1) →
      ρ ∈ closedBall ((2:ℂ) + ((sgn * (T + 1/2) : ℝ)) * I) (13/8 : ℝ) := by
    intro sgn hsgn ρ hρ him
    obtain ⟨h1, h2, h3, h4⟩ := hZ ρ hρ
    rw [mem_closedBall, Complex.dist_eq]
    apply norm_le_of_sq_le (by norm_num)
    have hre' : (ρ - ((2:ℂ) + ((sgn * (T + 1/2) : ℝ)) * I)).re = ρ.re - 2 := by simp
    have him' : (ρ - ((2:ℂ) + ((sgn * (T + 1/2) : ℝ)) * I)).im
        = ρ.im - sgn * (T + 1/2) := by simp
    rw [hre', him']
    have hb1 : (ρ.re - 2)^2 ≤ (3/2)^2 := by nlinarith
    have hb2 : (ρ.im - sgn * (T + 1/2))^2 ≤ (1/2)^2 := by
      rcases hsgn with rfl | rfl
      · have h5 : 0 ≤ ρ.im := him.mpr rfl
        rw [abs_of_nonneg h5] at h3 h4
        have h6 : ρ.im - 1 * (T + 1/2) ≤ 1/2 := by linarith
        have h7 : -(1/2:ℝ) ≤ ρ.im - 1 * (T + 1/2) := by linarith
        nlinarith
      · have h5 : ¬ (0 ≤ ρ.im) := by
          intro h6
          have := him.mp h6
          norm_num at this
        push Not at h5
        rw [abs_of_neg h5] at h3 h4
        have h6 : ρ.im - (-1) * (T + 1/2) ≤ 1/2 := by linarith
        have h7 : -(1/2:ℝ) ≤ ρ.im - (-1) * (T + 1/2) := by linarith
        nlinarith
    nlinarith
  have hsplit := Finset.sum_filter_add_sum_filter_not Z (fun ρ => 0 ≤ ρ.im)
    (fun ρ => (analyticOrderNatAt f ρ : ℝ))
  have hlogT : Real.log (A * (|T + 1/2| + 2)) ≤ Real.log (A * (T+4)) := by
    apply Real.log_le_log (by positivity)
    have : |T + 1/2| = T + 1/2 := abs_of_nonneg (by linarith)
    rw [this]
    nlinarith
  have hlogT' : Real.log (A * (|(-(T + 1/2))| + 2)) ≤ Real.log (A * (T+4)) := by
    rw [abs_neg]
    exact hlogT
  have hpos : ∑ ρ ∈ Z.filter (fun ρ => 0 ≤ ρ.im),
      (analyticOrderNatAt f ρ : ℝ) ≤ 112 * Real.log (A * (T+4)) := by
    have h1 := sum_ord_le_of_diskData hf (T + 1/2)
      (F := Z.filter (fun ρ => 0 ≤ ρ.im)) (fun ρ hρ => by
        rw [Finset.mem_filter] at hρ
        have := hgeo 1 (Or.inl rfl) ρ hρ.1 (by
          constructor
          · intro _; rfl
          · intro _; exact hρ.2)
        simpa using this)
    linarith
  have hneg : ∑ ρ ∈ Z.filter (fun ρ => ¬ 0 ≤ ρ.im),
      (analyticOrderNatAt f ρ : ℝ) ≤ 112 * Real.log (A * (T+4)) := by
    have h1 := sum_ord_le_of_diskData hf (-(T + 1/2))
      (F := Z.filter (fun ρ => ¬ 0 ≤ ρ.im)) (fun ρ hρ => by
        rw [Finset.mem_filter] at hρ
        have h2 := hgeo (-1) (Or.inr rfl) ρ hρ.1 (by
          constructor
          · intro h3; exact absurd h3 hρ.2
          · intro h3; norm_num at h3)
        have h3 : ((-1 : ℝ) * (T + 1/2)) = -(T + 1/2) := by ring
        rwa [h3] at h2)
    linarith
  linarith

end Toolkit

/-! ### The contour assembly for nontrivial characters -/

section AssemblyNeOne

/-- Triangle inequality for the edge combination. -/
lemma norm_edge_combo {A B C D E G : ℂ} :
    ‖A - B + I*C + I*D - I*E + G‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ + ‖G‖ := by
  have hIC : ‖I*C‖ = ‖C‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hID : ‖I*D‖ = ‖D‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hIE : ‖I*E‖ = ‖E‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  calc ‖A - B + I*C + I*D - I*E + G‖
      ≤ ‖A - B + I*C + I*D - I*E‖ + ‖G‖ := norm_add_le _ _
    _ ≤ ‖A - B + I*C + I*D‖ + ‖I*E‖ + ‖G‖ := by
        linarith [norm_sub_le (A - B + I*C + I*D) (I*E)]
    _ ≤ ‖A - B + I*C‖ + ‖I*D‖ + ‖I*E‖ + ‖G‖ := by
        linarith [norm_add_le (A - B + I*C) (I*D)]
    _ ≤ ‖A - B‖ + ‖I*C‖ + ‖I*D‖ + ‖I*E‖ + ‖G‖ := by
        linarith [norm_add_le (A - B) (I*C)]
    _ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ + ‖E‖ + ‖G‖ := by
        rw [hIC, hID, hIE]
        linarith [norm_sub_le A B]

variable {N : ℕ} [NeZero N]

set_option maxHeartbeats 4000000 in
/-- **Contour phase, `χ ≠ 1`**: the Perron sum plus the contract zero sum is
controlled by the ledger error. -/
theorem contour_ne_one (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {y T : ℝ} (hy : 100 ≤ y) (hT : 2 ≤ T) :
    ‖perronSum χ y (1 + 1/Real.log y) T
      + ∑ ρ ∈ zeroFinset χ (1/2) T,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
            * ((y:ℂ)^ρ/ρ)‖
      ≤ 100000000 * (y * Real.log ((N:ℝ)*T*y)^2 / T
          + y^((5:ℝ)/8) * Real.log ((N:ℝ)*(T+2))^2) := by
  classical
  have hDD : DiskData (DirichletCharacter.LFunction χ) N := diskData_LFunction χ hχ
  have hN1 : (1:ℝ) ≤ N := hDD.one_le
  -- numerics
  have hy0 : (0:ℝ) < y := by linarith
  have hy1 : (1:ℝ) < y := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hlogy : 4 ≤ Real.log y := four_le_log hy
  have hlogy0 : (0:ℝ) < Real.log y := by linarith
  have hinvlog : 1 / Real.log y ≤ 1/4 :=
    one_div_le_one_div_of_le (by norm_num) hlogy
  have hinvlog0 : 0 < 1 / Real.log y := one_div_pos.mpr hlogy0
  set c : ℝ := 1 + 1/Real.log y with hcdef
  have hc1 : 1 < c := by rw [hcdef]; linarith
  have hc54 : c ≤ 5/4 := by rw [hcdef]; linarith
  have hyc : y ^ c = Real.exp 1 * y := by rw [hcdef]; exact rpow_one_add_inv_log hy
  have hyc3 : y ^ c ≤ 3 * y := by
    rw [hyc]
    nlinarith [Real.exp_one_lt_d9]
  set LNT : ℝ := Real.log ((N:ℝ)*(T+2)) with hLNTdef
  set LNT4 : ℝ := Real.log ((N:ℝ)*(T+4)) with hLNT4def
  set LNTy : ℝ := Real.log ((N:ℝ)*T*y) with hLNTydef
  have hLNT1 : 1 ≤ LNT := by
    rw [hLNTdef, Real.le_log_iff_exp_le (by nlinarith)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hLNT41 : 1 ≤ LNT4 := by
    rw [hLNT4def, Real.le_log_iff_exp_le (by nlinarith)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hLNT4le : LNT4 ≤ 2 * LNT := by
    rw [hLNT4def, hLNTdef]
    have h0 : (T+4:ℝ) ≤ (T+2)^2 := by nlinarith
    have h1 : (N:ℝ)*(T+4) ≤ (N:ℝ)*(T+2)^2 :=
      mul_le_mul_of_nonneg_left h0 (by linarith)
    have h2 : (N:ℝ)*(T+2)^2 ≤ ((N:ℝ)*(T+2))^2 := by
      have h3 : ((N:ℝ)*(T+2))^2 = (N:ℝ)^2*(T+2)^2 := by ring
      rw [h3]
      have h4 : (N:ℝ) ≤ (N:ℝ)^2 := by nlinarith
      nlinarith [sq_nonneg (T+2:ℝ)]
    calc Real.log ((N:ℝ)*(T+4)) ≤ Real.log (((N:ℝ)*(T+2))^2) :=
        Real.log_le_log (by nlinarith) (by linarith)
      _ = 2 * Real.log ((N:ℝ)*(T+2)) := by
          rw [Real.log_pow]
          push_cast
          ring
  have hTy4 : (T+4:ℝ) ≤ T*y := by nlinarith
  have hTy2 : (T+2:ℝ) ≤ T*y := by nlinarith
  have hLNT4y : LNT4 ≤ LNTy := by
    rw [hLNT4def, hLNTydef]
    apply Real.log_le_log (by nlinarith)
    have h1 : (N:ℝ)*(T+4) ≤ (N:ℝ)*(T*y) :=
      mul_le_mul_of_nonneg_left hTy4 (by linarith)
    nlinarith
  have hLNTle : LNT ≤ LNTy := by
    rw [hLNTdef, hLNTydef]
    apply Real.log_le_log (by nlinarith)
    have h1 : (N:ℝ)*(T+2) ≤ (N:ℝ)*(T*y) :=
      mul_le_mul_of_nonneg_left hTy2 (by linarith)
    nlinarith
  have hlogyle : Real.log y ≤ LNTy := by
    rw [hLNTydef]
    apply Real.log_le_log hy0
    have h1 : (1:ℝ) ≤ (N:ℝ)*T := by nlinarith
    nlinarith
  have hLNTy1 : 1 ≤ LNTy := by linarith
  -- Step A: good heights (top for L, bottom via reflection)
  have hcard0 : ((∅ : Finset ℝ).card : ℝ) ≤ 16 * Real.log ((N:ℝ)*(T+4)) := by
    simp only [Finset.card_empty, Nat.cast_zero]
    have : (0:ℝ) ≤ Real.log ((N:ℝ)*(T+4)) := Real.log_nonneg (by nlinarith)
    linarith
  obtain ⟨t₂, ht₂1, ht₂2, -, htop⟩ := exists_good_height hDD hT ∅ hcard0
  obtain ⟨t₁, ht₁1, ht₁2, -, hbot'⟩ := exists_good_height hDD.conj hT ∅ hcard0
  have hbot : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 3 →
      DirichletCharacter.LFunction χ ((σ:ℂ) + (-t₁ : ℝ)*I) ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) ((σ:ℂ) + (-t₁:ℝ)*I)
        / DirichletCharacter.LFunction χ ((σ:ℂ) + (-t₁:ℝ)*I)‖
        ≤ 1000000 * LNT4^2 := by
    intro σ h1 h2
    obtain ⟨hnz', hbd'⟩ := hbot' σ h1 h2
    constructor
    · intro h0
      apply hnz'
      show (starRingEnd ℂ) (DirichletCharacter.LFunction χ
        ((starRingEnd ℂ) ((σ:ℂ) + t₁*I))) = 0
      rw [conj_coord σ t₁, h0, map_zero]
    · have heq := norm_logDeriv_conjF (DirichletCharacter.LFunction χ)
        ((σ:ℂ) + (-t₁:ℝ)*I)
      rw [conj_coord σ (-t₁)] at heq
      simp only [neg_neg] at heq
      rw [heq]
      rw [hLNT4def]
      exact hbd'
  -- Step B: `σ₁`
  set Bset : Finset ℝ :=
    (boxZeros (DirichletCharacter.LFunction χ) (T+4)).image Complex.re with hBdef
  set a : ℝ := -t₁ with hadef
  set M : ℕ := ⌈2*(t₁+t₂)⌉₊ with hMdef
  have hMceil : 2*(t₁+t₂) ≤ (M:ℝ) := Nat.le_ceil _
  have hMceil' : (M:ℝ) < 2*(t₁+t₂) + 1 := Nat.ceil_lt_add_one (by nlinarith)
  have ha' : -(T+1) ≤ a := by rw [hadef]; linarith
  have ha0 : a ≤ 0 := by rw [hadef]; linarith
  have hM1 : 0 ≤ a + M/2 := by rw [hadef]; nlinarith
  have hM2 : a + M/2 ≤ T + 2 := by rw [hadef]; nlinarith
  have hM3 : t₂ ≤ a + M/2 := by rw [hadef]; nlinarith
  obtain ⟨σ₁, hσ1, hσ2, hσB, hσH⟩ := exists_good_sigma hDD hT ha' ha0 hM1 hM2 Bset
  have hσc : σ₁ < c := by linarith
  have hσre : ∀ ρ ∈ boxZeros (DirichletCharacter.LFunction χ) (T+4),
      ρ.re ≠ σ₁ := by
    intro ρ hρ h
    apply hσB
    rw [hBdef, ← h]
    exact Finset.mem_image_of_mem _ hρ
  -- Step C: cuts
  obtain ⟨m, τ, hm1, hτ0, hτm, hτmono, hτgap, hτavoid, hτrange⟩ :=
    exists_cuts ((boxZeros (DirichletCharacter.LFunction χ) (T+4)).image
      Complex.im) (by linarith : 4 ≤ t₁ + t₂)
  have hcutzeros : ∀ j ≤ m, ∀ ρ ∈ boxZeros (DirichletCharacter.LFunction χ) (T+4),
      ρ.im ≠ τ j := by
    intro j hj ρ hρ him
    obtain ⟨⟨hre1, hre2⟩, ⟨him1, him2⟩, hzero⟩ := (mem_boxZeros hDD).mp hρ
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hτ0] at him
      have h1 := (hbot ρ.re hre1 (by linarith)).1
      apply h1
      have h2 : ((ρ.re:ℂ) + (-t₁:ℝ)*I) = ρ := by
        rw [← him]
        exact Complex.re_add_im ρ
      rw [h2]
      exact hzero
    · rcases Nat.lt_or_ge j m with hjm | hjm
      · apply hτavoid j hj0 hjm
        rw [← him]
        exact Finset.mem_image_of_mem _ hρ
      · have hjm' : j = m := by omega
        rw [hjm', hτm] at him
        have h1 := (htop ρ.re hre1 (by linarith)).1
        apply h1
        have h2 : ((ρ.re:ℂ) + t₂*I) = ρ := by
          rw [← him]
          exact Complex.re_add_im ρ
        rw [h2]
        exact hzero
  have hboxmem : ∀ (σ t : ℝ), 1/2 ≤ σ → σ ≤ 3/2 → -(T+4) ≤ t → t ≤ T+4 →
      DirichletCharacter.LFunction χ ((σ:ℂ) + t*I) = 0 →
      ((σ:ℂ) + t*I) ∈ boxZeros (DirichletCharacter.LFunction χ) (T+4) := by
    intro σ t h1 h2 h3 h4 h5
    rw [mem_boxZeros hDD]
    rw [re_coord, im_coord]
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
  have hτbounds : ∀ j ≤ m, -(T+4) ≤ τ j ∧ τ j ≤ T+4 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hτrange j hj
    constructor <;> linarith
  have hlines : ∀ j ≤ m, ∀ σ ∈ Set.Icc σ₁ c,
      DirichletCharacter.LFunction χ ((σ:ℂ) + (τ j)*I) ≠ 0 := by
    intro j hj σ hσ h0
    obtain ⟨hb1, hb2⟩ := hτbounds j hj
    have hmem := hboxmem σ (τ j) (by linarith [hσ.1]) (by linarith [hσ.2])
      hb1 hb2 h0
    exact hcutzeros j hj _ hmem (im_coord σ (τ j))
  have hleftnz : ∀ t : ℝ, -(T+4) ≤ t → t ≤ T+4 →
      DirichletCharacter.LFunction χ ((σ₁:ℂ) + t*I) ≠ 0 := by
    intro t h1 h2 h0
    have hmem := hboxmem σ₁ t (by linarith) (by linarith) h1 h2 h0
    exact hσre _ hmem (re_coord σ₁ t)
  have hleft : ∀ t ∈ Set.Icc (τ 0) (τ m),
      DirichletCharacter.LFunction χ ((σ₁:ℂ) + t*I) ≠ 0 := by
    intro t ht
    rw [hτ0] at ht
    rw [hτm] at ht
    exact hleftnz t (by linarith [ht.1]) (by linarith [ht.2])
  -- Step D+E: chain and fusion
  have hchain := rectInt_chain hDD hy1 hσ1 hσc hc1 hc54 τ m hτmono hτgap
    hlines hleft
  have hfusion := chain_sum_eq_box hDD
    (fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
      * ((y:ℂ)^ρ/ρ))
    hσ1 hσc hc54 τ m hτmono hτgap
    (by rw [hτ0]; linarith) (by rw [hτm]; linarith) hcutzeros
  rw [hfusion] at hchain
  simp only [hτ0, hτm] at hchain
  -- named pieces
  set S : ℂ := perronSum χ y c T with hSdef
  set SR : ℂ := ∑ ρ ∈ (boxZeros (DirichletCharacter.LFunction χ) (T+4)).filter
      (fun ρ => σ₁ < ρ.re ∧ ρ.re < c ∧ -t₁ < ρ.im ∧ ρ.im < t₂),
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((y:ℂ)^ρ/ρ)
    with hSRdef
  set SC : ℂ := ∑ ρ ∈ zeroFinset χ (1/2) T,
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((y:ℂ)^ρ/ρ)
    with hSCdef
  rw [rectInt_edges] at hchain
  -- right-edge splitting
  have hRnz : ∀ t ∈ Set.uIcc (-(T+4)) (T+4),
      DirichletCharacter.LFunction χ ((c:ℂ)+t*I) ≠ 0 := fun t _ =>
    hDD.nz _ (by rw [re_coord]; exact hc1)
  have hRcont := contOn_vert_stripInt hDD hy0 (by linarith : 1/4 ≤ c)
    (by linarith : c ≤ 15/4) hRnz
  have hRint : ∀ u v : ℝ, -(T+4) ≤ u → u ≤ T+4 → -(T+4) ≤ v → v ≤ T+4 →
      IntervalIntegrable (fun t : ℝ =>
        (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
          / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      MeasureTheory.volume u v := by
    intro u v h1 h2 h3 h4
    apply (hRcont.mono _).intervalIntegrable
    apply Set.uIcc_subset_uIcc
    · rw [Set.uIcc_of_le (by linarith)]
      exact ⟨h1, h2⟩
    · rw [Set.uIcc_of_le (by linarith)]
      exact ⟨h3, h4⟩
  have hsplit1 : (∫ t in (-t₁)..(-T),
        (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
          / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      + (∫ t in (-T)..T,
        (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
          / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      = ∫ t in (-t₁)..T,
        (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
          / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hRint _ _ (by linarith) (by linarith) (by linarith) (by linarith))
      (hRint _ _ (by linarith) (by linarith) (by linarith) (by linarith))
  have hsplit2 : (∫ t in (-t₁)..T,
        (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
          / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      + (∫ t in T..t₂,
        (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
          / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      = ∫ t in (-t₁)..t₂,
        (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
          / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hRint _ _ (by linarith) (by linarith) (by linarith) (by linarith))
      (hRint _ _ (by linarith) (by linarith) (by linarith) (by linarith))
  -- the interchange on the symmetric window
  have hJ := integral_right_edge χ (c := c) hy hc1 hT0
  have hJmid : (∫ t in (-T)..T,
      (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
        / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
      * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      = -(((2 * π : ℝ) : ℂ) * S) := by
    rw [hSdef, ← hJ, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  -- master identity
  have hmaster : ((2 * π : ℝ) : ℂ) * I * (S + SC)
      = (∫ x in σ₁..c,
          (deriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (-t₁:ℝ)*I)
            / DirichletCharacter.LFunction χ ((x:ℂ) + (-t₁:ℝ)*I))
          * ((y:ℂ)^((x:ℂ) + (-t₁:ℝ)*I) / ((x:ℂ) + (-t₁:ℝ)*I)))
        - (∫ x in σ₁..c,
          (deriv (DirichletCharacter.LFunction χ) ((x:ℂ) + t₂*I)
            / DirichletCharacter.LFunction χ ((x:ℂ) + t₂*I))
          * ((y:ℂ)^((x:ℂ) + t₂*I) / ((x:ℂ) + t₂*I)))
        + I * (∫ t in (-t₁)..(-T),
          (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
            / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
          * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
        + I * (∫ t in T..t₂,
          (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
            / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
          * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
        - I * (∫ t in (-t₁)..t₂,
          (deriv (DirichletCharacter.LFunction χ) ((σ₁:ℂ)+t*I)
            / DirichletCharacter.LFunction χ ((σ₁:ℂ)+t*I))
          * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I)))
        + 2*(π:ℂ)*I * (SC - SR) := by
    have hofReal : ((2 * π : ℝ) : ℂ) = 2*(π:ℂ) := by push_cast; ring
    rw [hofReal]
    have hRv : (∫ t in (-t₁)..t₂,
        (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
          / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
        = (∫ t in (-t₁)..(-T),
          (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
            / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
          * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
          + -(2*(π:ℂ) * S)
          + (∫ t in T..t₂,
          (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
            / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
          * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))) := by
      rw [← hsplit2, ← hsplit1, hJmid, hofReal]
    rw [hRv] at hchain
    linear_combination -hchain
  -- edge bounds
  have habs₂ : |t₂| = t₂ := abs_of_pos (by linarith)
  have habs₁ : |(-t₁ : ℝ)| = t₁ := by rw [abs_neg]; exact abs_of_pos (by linarith)
  have hTop : ‖∫ x in σ₁..c,
      (deriv (DirichletCharacter.LFunction χ) ((x:ℂ) + t₂*I)
        / DirichletCharacter.LFunction χ ((x:ℂ) + t₂*I))
      * ((y:ℂ)^((x:ℂ) + t₂*I) / ((x:ℂ) + t₂*I))‖
      ≤ (1000000 * LNT4^2) * (3*y) / (T * Real.log y) := by
    have h1 := horiz_edge_le hDD (t₀ := t₂) (B := 1000000 * LNT4^2)
      hy hσ1 hσc.le hc54 hyc3 (by rw [habs₂]; linarith)
      (by positivity)
      (fun x hx => (htop x (by linarith [hx.1]) (by linarith [hx.2])).1)
      (fun x hx => by
        have h2 := (htop x (by linarith [hx.1]) (by linarith [hx.2])).2
        rwa [hLNT4def])
    calc _ ≤ (1000000 * LNT4^2) * (3*y) / (|t₂| * Real.log y) := h1
      _ ≤ (1000000 * LNT4^2) * (3*y) / (T * Real.log y) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          rw [habs₂]
          nlinarith
  have hBot : ‖∫ x in σ₁..c,
      (deriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (-t₁:ℝ)*I)
        / DirichletCharacter.LFunction χ ((x:ℂ) + (-t₁:ℝ)*I))
      * ((y:ℂ)^((x:ℂ) + (-t₁:ℝ)*I) / ((x:ℂ) + (-t₁:ℝ)*I))‖
      ≤ (1000000 * LNT4^2) * (3*y) / (T * Real.log y) := by
    have h1 := horiz_edge_le hDD (t₀ := (-t₁ : ℝ)) (B := 1000000 * LNT4^2)
      hy hσ1 hσc.le hc54 hyc3 (by rw [habs₁]; linarith)
      (by positivity)
      (fun x hx => (hbot x (by linarith [hx.1]) (by linarith [hx.2])).1)
      (fun x hx => (hbot x (by linarith [hx.1]) (by linarith [hx.2])).2)
    calc _ ≤ (1000000 * LNT4^2) * (3*y) / (|(-t₁:ℝ)| * Real.log y) := h1
      _ ≤ (1000000 * LNT4^2) * (3*y) / (T * Real.log y) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity)
          rw [habs₁]
          nlinarith
  have hEt : ‖∫ t in T..t₂,
      (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
        / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
      * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))‖
      ≤ 18 * (y * Real.log y ^ 2 / T) :=
    right_extra_le χ hy hcdef hT (by linarith) (by linarith)
      (fun t ht => by
        rw [abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t)]
        exact ht.1)
  have hEb : ‖∫ t in (-t₁)..(-T),
      (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
        / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
      * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))‖
      ≤ 18 * (y * Real.log y ^ 2 / T) :=
    right_extra_le χ hy hcdef hT (by linarith) (by linarith)
      (fun t ht => by
        rw [abs_of_nonpos (by linarith [ht.2] : t ≤ 0)]
        linarith [ht.2])
  -- left edge
  have hσne : ∀ k ∈ Finset.range M,
      ∀ ρ ∈ diskZeros (DirichletCharacter.LFunction χ) (a + k/2 + 1/4),
        ρ.re ≠ σ₁ := by
    intro k hk ρ hρ h
    obtain ⟨hre1, hre2, him⟩ := re_bounds_of_mem_diskZeros hDD hρ
    rcases le_or_gt (1/2 : ℝ) ρ.re with hc1' | hc1'
    · rcases le_or_gt ρ.re (3/2 : ℝ) with hc2' | hc2'
      · -- in the box
        have hkM : (k:ℝ) + 1 ≤ M := by
          rw [Finset.mem_range] at hk
          exact_mod_cast hk
        have htk : |a + (k:ℝ)/2 + 1/4| ≤ T + 2 := by
          rw [abs_le]
          constructor
          · have : (0:ℝ) ≤ (k:ℝ)/2 := by positivity
            linarith
          · nlinarith
        have himρ : -(T+4) ≤ ρ.im ∧ ρ.im ≤ T+4 := by
          rw [abs_le] at him htk
          constructor <;> linarith [him.1, him.2, htk.1, htk.2]
        have hmem : ρ ∈ boxZeros (DirichletCharacter.LFunction χ) (T+4) := by
          rw [mem_boxZeros hDD]
          exact ⟨⟨hc1', hc2'⟩, himρ, ((mem_diskZeros hDD).mp hρ).2⟩
        exact hσre ρ hmem h
      · rw [h] at hc2'
        linarith
    · rw [h] at hc1'
      linarith
  have hnzleft : ∀ t ∈ Set.Icc a (a + M/2),
      DirichletCharacter.LFunction χ ((σ₁:ℂ) + t*I) ≠ 0 := by
    intro t ht
    apply hleftnz t
    · rw [hadef] at ht
      linarith [ht.1]
    · linarith [ht.2]
  have hLv : ‖∫ t in a..t₂,
      (deriv (DirichletCharacter.LFunction χ) ((σ₁:ℂ)+t*I)
        / DirichletCharacter.LFunction χ ((σ₁:ℂ)+t*I))
      * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖
      ≤ 20000000 * y^σ₁ * LNT4^2 := by
    have h1 := left_edge_le hDD hy1 hT ha' ha0 hM1 hM2 hσ1 hσ2 hσne hnzleft
      hσH (b := t₂) (by rw [hadef]; linarith) hM3
    rw [hLNT4def]
    exact h1
  -- zone adjustments
  have hζim : ∀ ρ ∈ zeroFinset χ (1/2) T, -t₁ < ρ.im ∧ ρ.im < t₂ := by
    intro ρ hρ
    have hm := mem_zeroFinset.mp hρ
    obtain ⟨h1, h2, h3, h4, h5⟩ := hm
    rw [abs_le] at h3
    constructor
    · rcases lt_or_eq_of_le (by linarith [h3.1] : -t₁ ≤ ρ.im) with h | h
      · exact h
      · exfalso
        apply (hbot ρ.re h1 (by linarith)).1
        have h6 : ((ρ.re:ℂ) + (-t₁:ℝ)*I) = ρ := by
          rw [h]
          exact Complex.re_add_im ρ
        rw [h6]
        exact h5
    · rcases lt_or_eq_of_le (by linarith [h3.2] : ρ.im ≤ t₂) with h | h
      · exact h
      · exfalso
        apply (htop ρ.re h1 (by linarith)).1
        have h6 : ((ρ.re:ℂ) + t₂*I) = ρ := by
          rw [← h]
          exact Complex.re_add_im ρ
        rw [h6]
        exact h5
  have hadj : ‖SC - SR‖ ≤ 2700 * y^((5:ℝ)/8) * LNT^2 + 448 * (y * LNTy^2 / T) := by
    set Cf : Finset ℂ := zeroFinset χ (1/2) T with hCfdef
    set Rf : Finset ℂ := (boxZeros (DirichletCharacter.LFunction χ) (T+4)).filter
      (fun ρ => σ₁ < ρ.re ∧ ρ.re < c ∧ -t₁ < ρ.im ∧ ρ.im < t₂) with hRfdef
    set g : ℂ → ℂ := fun ρ =>
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((y:ℂ)^ρ/ρ)
      with hgdef
    have hSC' : SC = ∑ ρ ∈ Cf, g ρ := hSCdef
    have hSR' : SR = ∑ ρ ∈ Rf, g ρ := hSRdef
    rw [hSC', hSR', sum_sub_sum_eq]
    -- memberships
    have hmemRf : ∀ ρ : ℂ, ρ ∈ Rf ↔
        (ρ ∈ boxZeros (DirichletCharacter.LFunction χ) (T+4)
          ∧ (σ₁ < ρ.re ∧ ρ.re < c ∧ -t₁ < ρ.im ∧ ρ.im < t₂)) := by
      intro ρ
      rw [hRfdef, Finset.mem_filter]
    -- `Cf \ Rf`
    have hCR : ‖∑ ρ ∈ Cf \ Rf, g ρ‖ ≤ 2700 * y^((5:ℝ)/8) * LNT^2 := by
      have hclass : ∀ ρ ∈ Cf \ Rf, ρ.re ≤ σ₁ := by
        intro ρ hρ
        rw [Finset.mem_sdiff] at hρ
        obtain ⟨hC', hnR⟩ := hρ
        have hm := mem_zeroFinset.mp (hCfdef ▸ hC')
        obtain ⟨h1, h2, h3, h4, h5⟩ := hm
        obtain ⟨h6, h7⟩ := hζim ρ (hCfdef ▸ hC')
        by_contra hgt
        push Not at hgt
        apply hnR
        rw [hmemRf]
        refine ⟨?_, hgt, by linarith, h6, h7⟩
        rw [mem_boxZeros hDD]
        rw [abs_le] at h3
        exact ⟨⟨h1, by linarith⟩, ⟨by linarith [h3.1], by linarith [h3.2]⟩, h5⟩
      have hterm : ∀ ρ ∈ Cf \ Rf, ‖g ρ‖
          ≤ (3 * y^σ₁) * ((analyticOrderNatAt
              (DirichletCharacter.LFunction χ) ρ : ℝ) / (1+|ρ.im|)) := by
        intro ρ hρ
        have hre := hclass ρ hρ
        rw [Finset.mem_sdiff] at hρ
        have hm := mem_zeroFinset.mp (hCfdef ▸ hρ.1)
        obtain ⟨h1, h2, h3, h4, h5⟩ := hm
        rw [hgdef]
        show ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
          * ((y:ℂ)^ρ/ρ)‖ ≤ _
        rw [norm_mul, norm_div, Complex.norm_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos hy0]
        have hρhalf : (1/2:ℝ) ≤ ‖ρ‖ := by
          have h6 := Complex.abs_re_le_norm ρ
          have h7 : (1/2:ℝ) ≤ |ρ.re| := by
            rw [abs_of_nonneg (by linarith)]
            exact h1
          linarith
        have hρ0 : (0:ℝ) < ‖ρ‖ := by linarith
        have hyre : y ^ ρ.re ≤ y ^ σ₁ :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hre
        have hnorm3 : 1 + |ρ.im| ≤ 3 * ‖ρ‖ := by
          have ha2 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
          linarith
        have h8 : y ^ ρ.re * (1+|ρ.im|) ≤ y ^ σ₁ * (3 * ‖ρ‖) :=
          mul_le_mul hyre hnorm3 (by positivity) (Real.rpow_nonneg hy0.le σ₁)
        calc (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
            * (y ^ ρ.re / ‖ρ‖)
            ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
              * (3 * y ^ σ₁ / (1+|ρ.im|)) := by
              apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
              rw [div_le_div_iff₀ hρ0 (by positivity)]
              nlinarith
          _ = (3 * y^σ₁) * ((analyticOrderNatAt
              (DirichletCharacter.LFunction χ) ρ : ℝ) / (1+|ρ.im|)) := by
              field_simp
      have hweight := weight_sum_le hDD (U := T) hT (Z := Cf \ Rf)
        (by
          intro ρ hρ
          rw [Finset.mem_sdiff] at hρ
          have hm := mem_zeroFinset.mp (hCfdef ▸ hρ.1)
          exact ⟨hm.1, by linarith [hm.2.1], hm.2.2.1⟩)
      calc ‖∑ ρ ∈ Cf \ Rf, g ρ‖ ≤ ∑ ρ ∈ Cf \ Rf, ‖g ρ‖ := norm_sum_le _ _
        _ ≤ ∑ ρ ∈ Cf \ Rf, (3 * y^σ₁) * ((analyticOrderNatAt
            (DirichletCharacter.LFunction χ) ρ : ℝ) / (1+|ρ.im|)) :=
            Finset.sum_le_sum hterm
        _ = (3 * y^σ₁) * ∑ ρ ∈ Cf \ Rf, ((analyticOrderNatAt
            (DirichletCharacter.LFunction χ) ρ : ℝ) / (1+|ρ.im|)) := by
            rw [Finset.mul_sum]
        _ ≤ (3 * y^σ₁) * (900 * Real.log ((N:ℝ)*(T+2))^2) := by
            apply mul_le_mul_of_nonneg_left hweight
            have := Real.rpow_nonneg hy0.le σ₁
            positivity
        _ ≤ 2700 * y^((5:ℝ)/8) * LNT^2 := by
            rw [← hLNTdef]
            have h1 : y ^ σ₁ ≤ y ^ ((5:ℝ)/8) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) hσ2
            nlinarith [Real.rpow_nonneg hy0.le σ₁, sq_nonneg LNT,
              Real.rpow_nonneg hy0.le ((5:ℝ)/8)]
    -- `Rf \ Cf`
    have hRC : ‖∑ ρ ∈ Rf \ Cf, g ρ‖ ≤ 448 * (y * LNTy^2 / T) := by
      have hclass : ∀ ρ ∈ Rf \ Cf,
          (1/2 ≤ ρ.re ∧ ρ.re ≤ 3/2) ∧ (T < |ρ.im| ∧ |ρ.im| ≤ T + 1)
            ∧ ρ.re ≤ 1 := by
        intro ρ hρ
        rw [Finset.mem_sdiff] at hρ
        obtain ⟨hR', hnC⟩ := hρ
        rw [hmemRf] at hR'
        obtain ⟨hbox, hf1, hf2, hf3, hf4⟩ := hR'
        have hzero := ((mem_boxZeros hDD).mp hbox).2.2
        have hre1 : ρ.re ≤ 1 := re_le_one_of_zero hDD hzero
        have hρne1 : ρ ≠ 1 := by
          intro h
          rw [h] at hzero
          exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
            (by rw [Complex.one_re]) hzero
        have himT : T < |ρ.im| := by
          by_contra hle
          push Not at hle
          apply hnC
          rw [hCfdef, mem_zeroFinset]
          exact ⟨by linarith, hre1, hle, hρne1, hzero⟩
        have himT1 : |ρ.im| ≤ T + 1 := by
          rw [abs_le]
          exact ⟨by linarith, by linarith⟩
        exact ⟨⟨by linarith, by linarith⟩, ⟨himT, himT1⟩, hre1⟩
      have hterm : ∀ ρ ∈ Rf \ Cf, ‖g ρ‖
          ≤ (y/T) * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
        intro ρ hρ
        obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hclass ρ hρ
        rw [hgdef]
        show ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
          * ((y:ℂ)^ρ/ρ)‖ ≤ _
        rw [norm_mul, norm_div, Complex.norm_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos hy0]
        have hρT : T ≤ ‖ρ‖ := le_trans h3.le (Complex.abs_im_le_norm ρ)
        have hyre : y ^ ρ.re ≤ y := by
          calc y ^ ρ.re ≤ y ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) h5
            _ = y := Real.rpow_one y
        calc (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
            * (y ^ ρ.re / ‖ρ‖)
            ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
              * (y / T) := by
              apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
              apply div_le_div₀ (by linarith) hyre hT0 hρT
          _ = (y/T) * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
              ring
      have hmass := band_mass_le hDD hT (Z := Rf \ Cf)
        (fun ρ hρ => by
          obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩, -⟩ := hclass ρ hρ
          exact ⟨h1, h2, h3, h4⟩)
      calc ‖∑ ρ ∈ Rf \ Cf, g ρ‖ ≤ ∑ ρ ∈ Rf \ Cf, ‖g ρ‖ := norm_sum_le _ _
        _ ≤ ∑ ρ ∈ Rf \ Cf, (y/T) * (analyticOrderNatAt
            (DirichletCharacter.LFunction χ) ρ : ℝ) := Finset.sum_le_sum hterm
        _ = (y/T) * ∑ ρ ∈ Rf \ Cf, (analyticOrderNatAt
            (DirichletCharacter.LFunction χ) ρ : ℝ) := by
            rw [Finset.mul_sum]
        _ ≤ (y/T) * (224 * LNT4) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [hLNT4def]
            exact hmass
        _ ≤ 448 * (y * LNTy^2 / T) := by
            have h1 : LNT4 ≤ LNTy := hLNT4y
            have h2 : LNTy ≤ LNTy^2 := by nlinarith
            rw [div_mul_eq_mul_div,
              show 448 * (y * LNTy^2 / T) = (448 * (y * LNTy^2)) / T by ring]
            apply div_le_div_right_of_pos hT0
            nlinarith
    calc ‖(∑ ρ ∈ Cf \ Rf, g ρ) - ∑ ρ ∈ Rf \ Cf, g ρ‖
        ≤ ‖∑ ρ ∈ Cf \ Rf, g ρ‖ + ‖∑ ρ ∈ Rf \ Cf, g ρ‖ := norm_sub_le _ _
      _ ≤ 2700 * y^((5:ℝ)/8) * LNT^2 + 448 * (y * LNTy^2 / T) :=
          add_le_add hCR hRC
  -- final norm bound
  have hnormfac : ‖((2 * π : ℝ) : ℂ) * I * (S + SC)‖ = 2*π*‖S + SC‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
  have hπ3 : (3:ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hrhs : ‖((2 * π : ℝ) : ℂ) * I * (S + SC)‖
      ≤ ((1000000 * LNT4^2) * (3*y) / (T * Real.log y))
        + ((1000000 * LNT4^2) * (3*y) / (T * Real.log y))
        + (18 * (y * Real.log y ^ 2 / T))
        + (18 * (y * Real.log y ^ 2 / T))
        + 20000000 * y^σ₁ * LNT4^2
        + 2*π*(2700 * y^((5:ℝ)/8) * LNT^2 + 448 * (y * LNTy^2 / T)) := by
    rw [hmaster]
    have h2πI : ‖2*(π:ℂ)*I * (SC - SR)‖ = 2*π*‖SC - SR‖ := by
      rw [show 2*(π:ℂ)*I * (SC - SR) = I * ((2*(π:ℂ)) * (SC - SR)) by ring]
      rw [norm_mul, Complex.norm_I, one_mul, norm_mul]
      have hπnorm : ‖(2*(π:ℂ))‖ = 2*π := by
        rw [show (2*(π:ℂ)) = ((2*π : ℝ) : ℂ) by push_cast; ring]
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [hπnorm]
    have htri := norm_edge_combo
      (A := ∫ x in σ₁..c,
          (deriv (DirichletCharacter.LFunction χ) ((x:ℂ) + (-t₁:ℝ)*I)
            / DirichletCharacter.LFunction χ ((x:ℂ) + (-t₁:ℝ)*I))
          * ((y:ℂ)^((x:ℂ) + (-t₁:ℝ)*I) / ((x:ℂ) + (-t₁:ℝ)*I)))
      (B := ∫ x in σ₁..c,
          (deriv (DirichletCharacter.LFunction χ) ((x:ℂ) + t₂*I)
            / DirichletCharacter.LFunction χ ((x:ℂ) + t₂*I))
          * ((y:ℂ)^((x:ℂ) + t₂*I) / ((x:ℂ) + t₂*I)))
      (C := ∫ t in (-t₁)..(-T),
          (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
            / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
          * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      (D := ∫ t in T..t₂,
          (deriv (DirichletCharacter.LFunction χ) ((c:ℂ)+t*I)
            / DirichletCharacter.LFunction χ ((c:ℂ)+t*I))
          * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      (E := ∫ t in (-t₁)..t₂,
          (deriv (DirichletCharacter.LFunction χ) ((σ₁:ℂ)+t*I)
            / DirichletCharacter.LFunction χ ((σ₁:ℂ)+t*I))
          * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I)))
      (G := 2*(π:ℂ)*I * (SC - SR))
    have hG : ‖2*(π:ℂ)*I * (SC - SR)‖
        ≤ 2*π*(2700 * y^((5:ℝ)/8) * LNT^2 + 448 * (y * LNTy^2 / T)) := by
      rw [h2πI]
      exact mul_le_mul_of_nonneg_left hadj (by positivity)
    have hLv' := hLv
    rw [hadef] at hLv'
    calc _ ≤ _ := htri
      _ ≤ _ := by
        have := add_le_add (add_le_add (add_le_add (add_le_add
          (add_le_add hBot hTop) hEb) hEt) hLv') hG
        linarith [this]
  -- final numeric assembly
  rw [hnormfac] at hrhs
  set P1 : ℝ := y * LNTy^2 / T with hP1def
  set P2 : ℝ := y^((5:ℝ)/8) * LNT^2 with hP2def
  have hP1nn : 0 ≤ P1 := by rw [hP1def]; positivity
  have hP2nn : 0 ≤ P2 := by
    rw [hP2def]
    positivity
  have hLNT4sq : LNT4^2 ≤ 4 * LNT^2 := by nlinarith
  have hLNTysq : LNT4^2 ≤ LNTy^2 := by nlinarith
  have hb1 : (1000000 * LNT4^2) * (3*y) / (T * Real.log y) ≤ 750000 * P1 := by
    rw [hP1def]
    have h1 : (1000000 * LNT4^2) * (3*y) ≤ 3000000 * (y * LNTy^2) := by nlinarith
    have h2 : 4 * T ≤ T * Real.log y := by nlinarith
    calc (1000000 * LNT4^2) * (3*y) / (T * Real.log y)
        ≤ 3000000 * (y * LNTy^2) / (4 * T) := by
          apply div_le_div₀ (by positivity) h1 (by positivity) h2
      _ = 750000 * (y * LNTy^2 / T) := by ring
  have hb2 : 18 * (y * Real.log y ^ 2 / T) ≤ 18 * P1 := by
    rw [hP1def]
    have h1 : Real.log y ^ 2 ≤ LNTy^2 := by nlinarith
    have h2 : y * Real.log y ^ 2 / T ≤ y * LNTy^2 / T := by
      apply div_le_div_right_of_pos hT0
      nlinarith
    linarith
  have hb3 : 20000000 * y^σ₁ * LNT4^2 ≤ 80000000 * P2 := by
    rw [hP2def]
    have h1 : y ^ σ₁ ≤ y ^ ((5:ℝ)/8) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hσ2
    nlinarith [Real.rpow_nonneg hy0.le σ₁, Real.rpow_nonneg hy0.le ((5:ℝ)/8),
      sq_nonneg LNT, hLNT1]
  have hπ7 : 2*π ≤ 7 := by
    have := Real.pi_lt_d2
    linarith
  have hb4 : 2*π*(2700 * y^((5:ℝ)/8) * LNT^2 + 448 * (y * LNTy^2 / T))
      ≤ 18900 * P2 + 3136 * P1 := by
    rw [hP1def, hP2def]
    have h1 : (0:ℝ) ≤ 2700 * (y^((5:ℝ)/8) * LNT^2) + 448 * (y * LNTy^2 / T) := by
      positivity
    nlinarith [hπ3, hP1nn, hP2nn]
  have hfinal6 : 6 * ‖S + SC‖ ≤ 2*π*‖S + SC‖ := by
    have := norm_nonneg (S + SC)
    nlinarith
  have htotal : 2*π*‖S + SC‖ ≤ 1503172 * P1 + 98918900 * P2 := by
    calc 2*π*‖S + SC‖ ≤ _ := hrhs
      _ ≤ 1503172 * P1 + 98918900 * P2 := by linarith [hb1, hb2, hb3, hb4]
  show ‖S + SC‖ ≤ 100000000 * (P1 + P2)
  nlinarith [hP1nn, hP2nn]

set_option maxHeartbeats 1000000 in
/-- **The explicit formula for nontrivial characters.** -/
theorem explicit_formula_ne_one (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {y T : ℝ} (hy : 100 ≤ y) (hT : 2 ≤ T) :
    ‖psiChi χ y + ∑ ρ ∈ zeroFinset χ (1/2) T,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
          * ((y:ℂ)^ρ/ρ)‖
      ≤ 200000000 * (y * Real.log ((N:ℝ)*T*y)^2 / T
          + y^((5:ℝ)/8) * Real.log ((N:ℝ)*(T+2))^2
          + Real.log ((N:ℝ)*T*y)^2) := by
  have hN1 : (1:ℝ) ≤ N := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hy0 : (0:ℝ) < y := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have h1 := perronSum_sub_psiChi_le χ hy hT
  have h2 := contour_ne_one χ hχ hy hT
  have hkey : psiChi χ y + ∑ ρ ∈ zeroFinset χ (1/2) T,
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((y:ℂ)^ρ/ρ)
      = -(perronSum χ y (1 + 1/Real.log y) T - psiChi χ y)
        + (perronSum χ y (1 + 1/Real.log y) T
          + ∑ ρ ∈ zeroFinset χ (1/2) T,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
              * ((y:ℂ)^ρ/ρ)) := by
    ring
  have hlogle : Real.log (T*y) ≤ Real.log ((N:ℝ)*T*y) := by
    apply Real.log_le_log (by positivity)
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ (N:ℝ)-1) hT0.le)
      hy0.le]
  have hlog0 : (0:ℝ) ≤ Real.log (T*y) := Real.log_nonneg (by nlinarith)
  have hsq : Real.log (T*y)^2 ≤ Real.log ((N:ℝ)*T*y)^2 := by nlinarith
  calc ‖psiChi χ y + ∑ ρ ∈ zeroFinset χ (1/2) T,
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((y:ℂ)^ρ/ρ)‖
      ≤ ‖perronSum χ y (1 + 1/Real.log y) T - psiChi χ y‖
        + ‖perronSum χ y (1 + 1/Real.log y) T
          + ∑ ρ ∈ zeroFinset χ (1/2) T,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
              * ((y:ℂ)^ρ/ρ)‖ := by
        rw [hkey]
        calc ‖_ + _‖ ≤ ‖-(perronSum χ y (1 + 1/Real.log y) T - psiChi χ y)‖
              + ‖perronSum χ y (1 + 1/Real.log y) T
                + ∑ ρ ∈ zeroFinset χ (1/2) T,
                  (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
                    * ((y:ℂ)^ρ/ρ)‖ := norm_add_le _ _
          _ = _ := by rw [norm_neg]
    _ ≤ (200 * (y * Real.log (T*y)^2 / T) + 30 * Real.log (T*y)^2)
        + 100000000 * (y * Real.log ((N:ℝ)*T*y)^2 / T
          + y^((5:ℝ)/8) * Real.log ((N:ℝ)*(T+2))^2) := add_le_add h1 h2
    _ ≤ 200000000 * (y * Real.log ((N:ℝ)*T*y)^2 / T
          + y^((5:ℝ)/8) * Real.log ((N:ℝ)*(T+2))^2
          + Real.log ((N:ℝ)*T*y)^2) := by
        have hp1 : y * Real.log (T*y)^2 / T ≤ y * Real.log ((N:ℝ)*T*y)^2 / T := by
          apply div_le_div_right_of_pos hT0
          nlinarith
        have hp2 : (0:ℝ) ≤ y * Real.log ((N:ℝ)*T*y)^2 / T := by positivity
        have hp3 : (0:ℝ) ≤ y^((5:ℝ)/8) * Real.log ((N:ℝ)*(T+2))^2 := by positivity
        nlinarith [hp1, hp2, hp3, hsq]

end AssemblyNeOne

/-! ### The correction factor `g(s) = 1 − 2^{1−s}` for the ζ case -/

section GFun

/-- The elementary factor relating `ζ` to the Abel-summed eta function. -/
noncomputable def gFun : ℂ → ℂ := fun s => 1 - (2:ℂ) ^ ((1:ℂ) - s)

lemma differentiable_gFun : Differentiable ℂ gFun :=
  (differentiable_const 1).sub
    (((differentiable_const (1:ℂ)).sub differentiable_id).const_cpow
      (Or.inl (by norm_num : (2:ℂ) ≠ 0)))

lemma hasDerivAt_gFun (s : ℂ) :
    HasDerivAt gFun ((Real.log 2 : ℂ) * (2:ℂ) ^ ((1:ℂ) - s)) s := by
  have h1 : HasDerivAt (fun s : ℂ => (1:ℂ) - s) (-1) s := by
    simpa using ((hasDerivAt_id s).const_sub (1:ℂ))
  have h2 := HasDerivAt.const_cpow (c := (2:ℂ)) h1 (Or.inl (by norm_num))
  have h3 := h2.const_sub (1:ℂ)
  have h4 : -((2:ℂ) ^ ((1:ℂ) - s) * Complex.log 2 * (-1))
      = (Real.log 2 : ℂ) * (2:ℂ) ^ ((1:ℂ) - s) := by
    have h5 : Complex.log 2 = (Real.log 2 : ℂ) := by
      rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.ofReal_log (by norm_num)]
    rw [h5]
    ring
  rw [← h4]
  exact h3

lemma deriv_gFun (s : ℂ) :
    deriv gFun s = (Real.log 2 : ℂ) * (2:ℂ) ^ ((1:ℂ) - s) :=
  (hasDerivAt_gFun s).deriv

/-- Modulus of the power factor. -/
lemma norm_two_cpow (s : ℂ) : ‖(2:ℂ) ^ ((1:ℂ) - s)‖ = (2:ℝ) ^ (1 - s.re) := by
  rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num,
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
  have h1 : ((1:ℂ) - s).re = 1 - s.re := by simp
  rw [h1]

lemma norm_deriv_gFun_le {s : ℂ} (hre : 9/16 ≤ s.re) :
    ‖deriv gFun s‖ ≤ 1 := by
  rw [deriv_gFun, norm_mul, norm_two_cpow, Complex.norm_real,
    Real.norm_of_nonneg (Real.log_nonneg (by norm_num))]
  have h1 : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le
  have h2 : (2:ℝ) ^ (1 - s.re) ≤ (2:ℝ) ^ ((7:ℝ)/16) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h3 : (2:ℝ) ^ ((7:ℝ)/16) ≤ 1.36 := by
    have h4 : ((2:ℝ) ^ ((7:ℝ)/16))^(16:ℕ) = 2^(7:ℕ) := by
      rw [← Real.rpow_natCast ((2:ℝ) ^ ((7:ℝ)/16)) 16, ← Real.rpow_mul (by norm_num)]
      norm_num
    by_contra hlt
    push Not at hlt
    have h5 : ((1.36:ℝ))^(16:ℕ) ≤ ((2:ℝ) ^ ((7:ℝ)/16))^(16:ℕ) :=
      pow_le_pow_left₀ (by norm_num) hlt.le _
    rw [h4] at h5
    norm_num at h5
  have h6 : (0:ℝ) ≤ (2:ℝ) ^ (1 - s.re) := Real.rpow_nonneg (by norm_num) _
  have h7 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  nlinarith

/-- `2^{3/8} ≥ 5/4`, hence `‖g‖ ≥ 1/4` left of `Re = 5/8`. -/
lemma norm_gFun_ge_left {s : ℂ} (hre : s.re ≤ 5/8) : 1/4 ≤ ‖gFun s‖ := by
  have h1 : (5/4 : ℝ) ≤ (2:ℝ) ^ (1 - s.re) := by
    have h2 : (2:ℝ) ^ ((3:ℝ)/8) ≤ (2:ℝ) ^ (1 - s.re) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h3 : (5/4 : ℝ) ≤ (2:ℝ) ^ ((3:ℝ)/8) := by
      have h4 : ((2:ℝ) ^ ((3:ℝ)/8))^(8:ℕ) = 2^(3:ℕ) := by
        rw [← Real.rpow_natCast ((2:ℝ) ^ ((3:ℝ)/8)) 8, ← Real.rpow_mul (by norm_num)]
        norm_num
      by_contra hlt
      push Not at hlt
      have h5 : ((2:ℝ) ^ ((3:ℝ)/8))^(8:ℕ) ≤ (5/4)^(8:ℕ) := by
        apply pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) hlt.le
      rw [h4] at h5
      norm_num at h5
    linarith
  calc (1/4 : ℝ) ≤ (2:ℝ) ^ (1 - s.re) - 1 := by linarith
    _ ≤ ‖(2:ℂ) ^ ((1:ℂ) - s)‖ - ‖(1:ℂ)‖ := by
        rw [norm_two_cpow, norm_one]
    _ ≤ ‖(2:ℂ) ^ ((1:ℂ) - s) - 1‖ := norm_sub_norm_le _ _
    _ = ‖gFun s‖ := by
        rw [gFun, ← norm_neg]
        congr 1
        ring

/-- `g` does not vanish for `Re s > 1`. -/
lemma gFun_ne_zero_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : gFun s ≠ 0 := by
  intro h0
  rw [gFun, sub_eq_zero] at h0
  have h1 : ‖(2:ℂ) ^ ((1:ℂ) - s)‖ < 1 := by
    rw [norm_two_cpow]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  rw [← h0] at h1
  simp at h1

/-- `DiskData` for the correction factor. -/
lemma diskData_gFun : DiskData gFun 1 := by
  constructor
  · exact le_refl 1
  · intro t₀ z _
    exact (differentiable_gFun.analyticAt z)
  · intro t₀
    have h2 : ‖(2:ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀*I))‖ = 1/2 := by
      rw [norm_two_cpow, re_center]
      rw [show (1 - (2:ℝ) : ℝ) = -1 by norm_num, Real.rpow_neg_one]
      norm_num
    have h3 := norm_sub_norm_le (1:ℂ) ((2:ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀*I)))
    rw [norm_one, h2] at h3
    calc (1/6:ℝ) ≤ 1 - 1/2 := by norm_num
      _ ≤ ‖gFun ((2:ℂ) + t₀*I)‖ := h3
  · intro t₀ z hz
    have hre := disk_re_ge hz
    calc ‖gFun z‖ ≤ ‖(1:ℂ)‖ + ‖(2:ℂ) ^ ((1:ℂ) - z)‖ := norm_sub_le _ _
      _ ≤ 1 + (2:ℝ) ^ ((3:ℝ)/4) := by
          rw [norm_one, norm_two_cpow]
          have h1 : (2:ℝ) ^ (1 - z.re) ≤ (2:ℝ) ^ ((3:ℝ)/4) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          linarith
      _ ≤ 15 * (1 * (|t₀| + 2)) := by
          have h1 : (2:ℝ) ^ ((3:ℝ)/4) ≤ 2 := by
            calc (2:ℝ) ^ ((3:ℝ)/4) ≤ (2:ℝ) ^ (1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
          have h2 : (0:ℝ) ≤ |t₀| := abs_nonneg t₀
          linarith
  · intro s hs
    exact gFun_ne_zero_of_one_lt_re hs

/-- Zeros of `g` sit on `Re = 1` at ordinates `2πn/log 2`. -/
lemma gFun_zero_imp {s : ℂ} (h : gFun s = 0) :
    s.re = 1 ∧ ∃ n : ℤ, s.im = 2*π*n/Real.log 2 := by
  rw [gFun, sub_eq_zero] at h
  have hL2 : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.ofReal_log (by norm_num)]
  have h1 : (2:ℂ) ^ ((1:ℂ) - s) = Complex.exp (((1:ℂ) - s) * (Real.log 2 : ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num), hL2]
    ring_nf
  rw [h1] at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h.symm
  have hL2pos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL2ne : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hL2pos.ne'
  have hs : s = 1 - ((2*π*(n:ℝ)/Real.log 2 : ℝ) : ℂ) * I := by
    have h2 : ((1:ℂ) - s) * (Real.log 2 : ℂ) = (n:ℂ) * (2*(π:ℂ)*I) := by
      exact_mod_cast hn
    have h3 : s * (Real.log 2 : ℂ) = (Real.log 2 : ℂ) - (n:ℂ)*(2*(π:ℂ)*I) := by
      linear_combination -h2
    apply mul_right_cancel₀ hL2ne
    rw [h3]
    push_cast
    field_simp
  constructor
  · rw [hs]
    simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  · refine ⟨-n, ?_⟩
    rw [hs]
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    push_cast
    ring

end GFun

/-! ### Eta–zeta order bookkeeping -/

section EtaZeta

/-- The eta function does not vanish at `1`. -/
lemma etaFun_one_ne_zero : etaFun 1 ≠ 0 := by
  have hsum : Summable (etaTerm 1) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (norm_etaTerm_le' (by norm_num : (0:ℝ) < (1:ℂ).re))
    have h1 : Summable (fun k : ℕ => (k:ℝ) ^ (-(1:ℂ).re - 1)) := by
      apply Real.summable_nat_rpow.mpr
      norm_num [Complex.one_re]
    exact h1.mul_left _
  have hre : ∀ k : ℕ, 0 ≤ (etaTerm 1 k).re := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [etaTerm]
    · have hk0 : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
      have h1 : etaTerm 1 k = (((k % 2 : ℕ) : ℝ) * ((k:ℝ)⁻¹ - ((k:ℝ)+1)⁻¹) : ℝ) := by
        rw [etaTerm, Complex.cpow_neg_one, Complex.cpow_neg_one]
        push_cast
        ring
      rw [h1, Complex.ofReal_re]
      have h2 : ((k:ℝ)+1)⁻¹ ≤ (k:ℝ)⁻¹ := by
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le hk0 (by linarith)
      positivity
  have hone : (1/2 : ℝ) ≤ (etaTerm 1 1).re := by
    have h1 : etaTerm 1 1 = ((1/2 : ℝ) : ℂ) := by
      rw [etaTerm, Complex.cpow_neg_one, Complex.cpow_neg_one]
      norm_num
    rw [h1, Complex.ofReal_re]
  have hsumre : Summable (fun k : ℕ => (etaTerm 1 k).re) :=
    (Complex.reCLM.summable hsum)
  have h2 : (1/2 : ℝ) ≤ ∑' k : ℕ, (etaTerm 1 k).re := by
    calc (1/2 : ℝ) ≤ (etaTerm 1 1).re := hone
      _ ≤ ∑' k : ℕ, (etaTerm 1 k).re := hsumre.le_tsum 1 (fun j _ => hre j)
  have h3 : (etaFun 1).re = ∑' k : ℕ, (etaTerm 1 k).re := by
    rw [etaFun]
    exact (Complex.reCLM.map_tsum hsum)
  intro h0
  rw [h0] at h3
  simp at h3
  linarith [h2, h3.symm.le]

/-- Order decomposition of the eta function at points off `1`. -/
lemma analyticOrderAt_eta_decomp {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ ≠ 1) :
    analyticOrderAt etaFun ρ
      = analyticOrderAt gFun ρ + analyticOrderAt riemannZeta ρ := by
  have hopen : IsOpen {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
    have h1 : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : IsOpen {s : ℂ | s ≠ 1} := isOpen_compl_singleton
    exact h1.inter h2
  have hmem : ρ ∈ {s : ℂ | 0 < s.re ∧ s ≠ 1} := ⟨hρ, hρ1⟩
  have hev : etaFun =ᶠ[𝓝 ρ] fun s => gFun s * riemannZeta s := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact etaFun_eqOn hz
  have hfac : AnalyticAt ℂ gFun ρ := differentiable_gFun.analyticAt ρ
  have hζ : AnalyticAt ℂ riemannZeta ρ := by
    have hopen1 : IsOpen {s : ℂ | s ≠ 1} := isOpen_compl_singleton
    have hd : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun z hz =>
      (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact hd.analyticAt (hopen1.mem_nhds hρ1)
  rw [analyticOrderAt_congr hev]
  have hprod : (fun s : ℂ => gFun s * riemannZeta s) = gFun * riemannZeta := rfl
  rw [hprod]
  exact analyticOrderAt_mul hfac hζ

/-- Nat-valued order decomposition. -/
lemma analyticOrderNatAt_eta_decomp {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ ≠ 1) :
    analyticOrderNatAt etaFun ρ
      = analyticOrderNatAt gFun ρ + analyticOrderNatAt riemannZeta ρ := by
  have hd := analyticOrderAt_eta_decomp hρ hρ1
  have htop := analyticOrderAt_etaFun_ne_top hρ
  rw [hd] at htop
  have hg : analyticOrderAt gFun ρ ≠ ⊤ := by
    intro h
    rw [h, top_add] at htop
    exact htop rfl
  have hz : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro h
    rw [h, add_top] at htop
    exact htop rfl
  rw [analyticOrderNatAt, analyticOrderNatAt, analyticOrderNatAt, hd,
    ENat.toNat_add hg hz]

/-- `g` has a simple zero at `1`. -/
lemma ord_gFun_one : analyticOrderNatAt gFun 1 = 1 := by
  have h0 : gFun 1 = 0 := by
    rw [gFun]
    norm_num
  have h1 : deriv gFun 1 ≠ 0 := by
    rw [deriv_gFun]
    have h2 : (2:ℂ) ^ ((1:ℂ) - 1) = 1 := by
      norm_num
    rw [h2, mul_one]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact (Real.log_pos (by norm_num)).ne'
  have h3 := (differentiable_gFun.analyticAt 1).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    h0 h1
  rw [analyticOrderNatAt, h3]
  rfl

/-- ζ does not vanish at the nontrivial `g`-zeros. -/
lemma ord_zeta_at_gzero {ρ : ℂ} (hg : gFun ρ = 0) :
    analyticOrderNatAt riemannZeta ρ = 0 := by
  have h1 := (gFun_zero_imp hg).1
  have h2 : riemannZeta ρ ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [h1])
  rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr h2)]
  rfl

/-- `g` does not vanish at ζ-zeros. -/
lemma ord_gFun_at_zetazero {ρ : ℂ} (hz : riemannZeta ρ = 0) :
    analyticOrderNatAt gFun ρ = 0 := by
  have h1 : gFun ρ ≠ 0 := by
    intro h
    have h2 := (gFun_zero_imp h).1
    exact (riemannZeta_ne_zero_of_one_le_re (by rw [h2])) hz
  rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr h1)]
  rfl

/-- eta vanishes wherever `g·ζ` does (off `1`, in the right half-plane). -/
lemma etaFun_eq_mul {s : ℂ} (h1 : 0 < s.re) (h2 : s ≠ 1) :
    etaFun s = gFun s * riemannZeta s :=
  etaFun_eqOn ⟨h1, h2⟩

end EtaZeta

/-! ### Quantitative nonvanishing of `g` on horizontal lines -/

section SinBound

/-- `sin u ≥ u/2` on `[0, π/2]`. -/
lemma sin_ge_half {u : ℝ} (h0 : 0 ≤ u) (h2 : u ≤ π/2) : u/2 ≤ Real.sin u := by
  rcases eq_or_lt_of_le h0 with rfl | h0'
  · simp
  rcases le_or_gt u 1 with h1 | h1
  · have h3 := Real.sin_gt_sub_cube h0'
    have h4 : u^3 ≤ u := by nlinarith [sq_nonneg u, mul_nonneg h0 h0]
    linarith
  · have h3 : Real.sin u = Real.cos (π/2 - u) := (Real.cos_pi_div_two_sub u).symm
    have h4 : 1 - (π/2 - u)^2/2 ≤ Real.cos (π/2 - u) :=
      Real.one_sub_sq_div_two_le_cos
    have h5 : (0:ℝ) ≤ π/2 - u := by linarith
    have hπ : π < 3.15 := Real.pi_lt_d2
    have h6 : (π/2 - u)^2 ≤ (π/2 - 1)^2 := by nlinarith
    nlinarith

/-- Jordan-type bound: `|sin x| ≥ dist(x, πℤ)/2`. -/
lemma half_dist_le_abs_sin (x : ℝ) :
    |x - (round (x/π) : ℤ) * π| / 2 ≤ |Real.sin x| := by
  set k : ℤ := round (x/π) with hkdef
  set d : ℝ := x - k * π with hddef
  have hπ0 : (0:ℝ) < π := Real.pi_pos
  have hd2 : |d| ≤ π/2 := by
    have h1 := abs_sub_round (x/π)
    have h2 : |x/π - k| * π ≤ (1/2) * π := by
      apply mul_le_mul_of_nonneg_right _ hπ0.le
      rw [hkdef]
      exact h1
    have h4 : (x/π - (k:ℝ)) * π = d := by
      rw [hddef]
      field_simp
    have h3 : |x/π - (k:ℝ)| * π = |d| := by
      calc |x/π - (k:ℝ)| * π = |x/π - (k:ℝ)| * |π| := by rw [abs_of_pos hπ0]
        _ = |(x/π - (k:ℝ)) * π| := (abs_mul _ _).symm
        _ = |d| := by rw [h4]
    rw [h3] at h2
    linarith
  have hsx : Real.sin x = (-1:ℝ)^k * Real.sin d := by
    have h1 : x = d + k * π := by rw [hddef]; ring
    rw [h1, Real.sin_add_int_mul_pi]
  have habs : |Real.sin x| = |Real.sin d| := by
    rw [hsx, abs_mul]
    have h1 : |(-1:ℝ)^k| = 1 := by
      rw [abs_zpow]
      norm_num
    rw [h1, one_mul]
  rw [habs]
  have hsd : |d|/2 ≤ Real.sin |d| := sin_ge_half (abs_nonneg d) hd2
  have h2 : Real.sin |d| ≤ |Real.sin d| := by
    rcases abs_cases d with ⟨h3, _⟩ | ⟨h3, h4⟩
    · rw [h3]
      exact le_abs_self _
    · rw [h3, Real.sin_neg]
      exact neg_le_abs _
  linarith

/-- Lower bound for `g` on horizontal lines via the sine of the ordinate. -/
lemma norm_gFun_ge_sin {σ t : ℝ} (_h1 : 9/16 ≤ σ) (h2 : σ ≤ 5/4) :
    (4/5) * |Real.sin (t * Real.log 2)| ≤ ‖gFun ((σ:ℂ) + t*I)‖ := by
  have hL2 : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, Complex.ofReal_log (by norm_num)]
  -- imaginary part of the power
  have him : ((2:ℂ) ^ ((1:ℂ) - ((σ:ℂ) + t*I))).im
      = -((2:ℝ) ^ (1 - σ)) * Real.sin (t * Real.log 2) := by
    have h3 : (1:ℂ) - ((σ:ℂ) + t*I) = ((1 - σ : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [h3, Complex.cpow_add _ _ (by norm_num : (2:ℂ) ≠ 0)]
    have h4 : (2:ℂ) ^ (((1 - σ : ℝ)) : ℂ) = (((2:ℝ) ^ (1 - σ) : ℝ) : ℂ) := by
      rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ← Complex.ofReal_cpow (by norm_num)]
    have h5 : (2:ℂ) ^ (((-t : ℝ)) * I : ℂ) = Complex.exp (((-t * Real.log 2 : ℝ)) * I) := by
      rw [Complex.cpow_def_of_ne_zero (by norm_num), hL2]
      congr 1
      push_cast
      ring
    rw [h4, h5]
    rw [Complex.mul_im]
    have h6 : ((((2:ℝ) ^ (1 - σ) : ℝ)) : ℂ).re = (2:ℝ) ^ (1 - σ) := by simp
    have h7 : ((((2:ℝ) ^ (1 - σ) : ℝ)) : ℂ).im = 0 := by simp
    rw [h6, h7, Complex.exp_ofReal_mul_I_im]
    have h8 : (-t * Real.log 2) = -(t * Real.log 2) := by ring
    rw [h8, Real.sin_neg]
    ring
  -- power lower bound
  have hpow : (4/5 : ℝ) ≤ (2:ℝ) ^ (1 - σ) := by
    have h3 : (2:ℝ) ^ (-(1:ℝ)/4) ≤ (2:ℝ) ^ (1 - σ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h4 : (4/5 : ℝ) ≤ (2:ℝ) ^ (-(1:ℝ)/4) := by
      have h5 : ((2:ℝ) ^ (-(1:ℝ)/4))^(4:ℕ) = 2⁻¹ := by
        rw [← Real.rpow_natCast ((2:ℝ) ^ (-(1:ℝ)/4)) 4, ← Real.rpow_mul (by norm_num)]
        rw [show (-(1:ℝ)/4 * ((4:ℕ):ℝ)) = -1 by push_cast; ring]
        exact Real.rpow_neg_one 2
      by_contra hlt
      push Not at hlt
      have h6 : ((2:ℝ) ^ (-(1:ℝ)/4))^(4:ℕ) ≤ ((4:ℝ)/5)^(4:ℕ) :=
        pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) hlt.le _
      rw [h5] at h6
      norm_num at h6
    linarith
  -- assemble
  have hIm : |(gFun ((σ:ℂ) + t*I)).im| = (2:ℝ) ^ (1 - σ) * |Real.sin (t * Real.log 2)| := by
    have h3 : (gFun ((σ:ℂ) + t*I)).im = -((2:ℂ) ^ ((1:ℂ) - ((σ:ℂ) + t*I))).im := by
      rw [gFun]
      simp
    rw [h3, abs_neg, him, abs_mul, abs_neg,
      abs_of_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)]
  calc (4/5) * |Real.sin (t * Real.log 2)|
      ≤ (2:ℝ) ^ (1 - σ) * |Real.sin (t * Real.log 2)| := by
        apply mul_le_mul_of_nonneg_right hpow (abs_nonneg _)
    _ = |(gFun ((σ:ℂ) + t*I)).im| := hIm.symm
    _ ≤ ‖gFun ((σ:ℂ) + t*I)‖ := Complex.abs_im_le_norm _

/-- Quantitative sine bound at pigeonholed heights. -/
lemma abs_sin_log_two_ge {T t₀ δ₀ : ℝ} (_hT : 2 ≤ T) (ht₀1 : T ≤ t₀)
    (ht₀2 : t₀ ≤ T+1) (hδ₀ : 0 < δ₀)
    (hgap : ∀ j : ℤ, (j = round (T / (π / Real.log 2)) - 1 ∨
        j = round (T / (π / Real.log 2)) ∨ j = round (T / (π / Real.log 2)) + 1) →
      δ₀ ≤ |t₀ - j * (π / Real.log 2)|) :
    δ₀ / 4 ≤ |Real.sin (t₀ * Real.log 2)| := by
  have hL2a : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hL2b : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hπa : (3.14 : ℝ) < π := Real.pi_gt_d2
  have hπb : π < 3.15 := Real.pi_lt_d2
  set q : ℝ := π / Real.log 2 with hqdef
  have hq0 : (0:ℝ) < q := by
    rw [hqdef]
    positivity
  have hq44 : (4.4 : ℝ) ≤ q := by
    rw [hqdef, le_div_iff₀ (by linarith)]
    nlinarith
  have hq46 : q ≤ 4.6 := by
    rw [hqdef, div_le_iff₀ (by linarith)]
    nlinarith
  set x : ℝ := t₀ * Real.log 2 with hxdef
  have hxq : x / π = t₀ / q := by
    rw [hxdef, hqdef]
    field_simp
  set kstar : ℤ := round (x/π) with hkstardef
  have hkstar : kstar = round (t₀ / q) := by rw [hkstardef, hxq]
  set kone : ℤ := round (T / q) with hkonedef
  -- the nearest half-multiple is one of the pigeonholed three
  have h1 : |t₀/q - (kstar:ℝ)| ≤ 1/2 := by
    rw [hkstar]
    exact abs_sub_round _
  have h2' : |T/q - (kone:ℝ)| ≤ 1/2 := by
    rw [hkonedef]
    exact abs_sub_round _
  have h3 : |t₀/q - T/q| ≤ 1/4 := by
    have h4 : t₀/q - T/q = (t₀ - T)/q := by ring
    rw [h4, abs_div, abs_of_pos hq0, div_le_iff₀ hq0]
    rw [abs_of_nonneg (by linarith)]
    linarith
  have h5 : |(kstar : ℝ) - (kone : ℝ)| < 2 := by
    have hA : |(kstar:ℝ) - t₀/q| ≤ 1/2 := by
      rw [abs_sub_comm]
      exact h1
    have hkk : (kstar : ℝ) - (kone : ℝ)
        = ((kstar:ℝ) - t₀/q) + ((t₀/q - T/q) + (T/q - (kone:ℝ))) := by ring
    calc |(kstar : ℝ) - (kone : ℝ)|
        = |((kstar:ℝ) - t₀/q) + ((t₀/q - T/q) + (T/q - (kone:ℝ)))| := by rw [hkk]
      _ ≤ |(kstar:ℝ) - t₀/q| + |(t₀/q - T/q) + (T/q - (kone:ℝ))| := abs_add' _ _
      _ ≤ |(kstar:ℝ) - t₀/q| + (|t₀/q - T/q| + |T/q - (kone:ℝ)|) := by
          linarith [abs_add' (t₀/q - T/q) (T/q - (kone:ℝ))]
      _ < 2 := by
          rw [abs_sub_comm (T/q) ((kone:ℝ))] at h2'
          rw [abs_sub_comm ((kone:ℝ)) (T/q)] at h2'
          linarith [h1, h2', h3]
  clear_value kstar kone
  have hnear : kstar = kone - 1 ∨ kstar = kone ∨ kstar = kone + 1 := by
    have h7 : |((kstar - kone : ℤ) : ℝ)| < 2 := by
      push_cast
      exact h5
    have h8 : |kstar - kone| < 2 := by exact_mod_cast h7
    have h9 := abs_lt.mp h8
    omega
  have hgapk := hgap kstar hnear
  -- transfer to the sine
  have hdist : |x - kstar * π| = Real.log 2 * |t₀ - kstar * q| := by
    have h1 : x - kstar * π = Real.log 2 * (t₀ - kstar * q) := by
      rw [hxdef, hqdef]
      field_simp
    rw [h1, abs_mul, abs_of_pos (by linarith)]
  have h2 := half_dist_le_abs_sin x
  rw [← hkstardef] at h2
  rw [hdist] at h2
  have h3 : Real.log 2 * δ₀ ≤ Real.log 2 * |t₀ - kstar * q| := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact hgapk
  calc δ₀/4 ≤ Real.log 2 * δ₀ / 2 := by nlinarith
    _ ≤ Real.log 2 * |t₀ - kstar * q| / 2 := by linarith
    _ ≤ |Real.sin x| := h2

/-- Left-edge bound for the `g`-part. -/
lemma g_left_edge_le {y σ₁ : ℝ} (hy : 1 < y) (hσ1 : 9/16 ≤ σ₁) (hσ2 : σ₁ ≤ 5/8)
    {u v U : ℝ} (hu : u ≤ 0) (hv : 0 ≤ v) (hUu : -U ≤ u) (hUv : v ≤ U) :
    ‖∫ t in u..v, (deriv gFun ((σ₁:ℂ)+t*I) / gFun ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖
      ≤ 32 * y^σ₁ * Real.log (1 + U) := by
  have hy0 : (0:ℝ) < y := by linarith
  have huv : u ≤ v := by linarith
  have hgnz : ∀ t : ℝ, gFun ((σ₁:ℂ)+t*I) ≠ 0 := by
    intro t
    have h1 := norm_gFun_ge_left (s := (σ₁:ℂ)+t*I) (by rw [re_coord]; linarith)
    intro h0
    rw [h0, norm_zero] at h1
    linarith
  -- pointwise bound
  have hptw : ∀ t ∈ Set.Icc u v,
      ‖(deriv gFun ((σ₁:ℂ)+t*I) / gFun ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖
      ≤ 16 * y^σ₁ * (1/(1+|t|)) := by
    intro t _
    rw [norm_mul, norm_div, norm_div, norm_cpow_coord hy0]
    have h1 : ‖deriv gFun ((σ₁:ℂ)+t*I)‖ ≤ 1 :=
      norm_deriv_gFun_le (by rw [re_coord]; linarith)
    have h2 : (1/4 : ℝ) ≤ ‖gFun ((σ₁:ℂ)+t*I)‖ :=
      norm_gFun_ge_left (by rw [re_coord]; linarith)
    have h3 : ‖deriv gFun ((σ₁:ℂ)+t*I)‖ / ‖gFun ((σ₁:ℂ)+t*I)‖ ≤ 4 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have h4 : (9/32) * (1+|t|) ≤ ‖(σ₁:ℂ)+t*I‖ := by
      have h5 : σ₁ ≤ ‖(σ₁:ℂ)+t*I‖ := by
        have := norm_coord_ge_abs_re σ₁ t
        rwa [abs_of_pos (by linarith)] at this
      have h6 : |t| ≤ ‖(σ₁:ℂ)+t*I‖ := norm_coord_ge_abs_im σ₁ t
      have := abs_nonneg t
      linarith
    have h7 : y ^ σ₁ / ‖(σ₁:ℂ)+t*I‖ ≤ y^σ₁ * (4/(1+|t|)) := by
      have h8 : (0:ℝ) < ‖(σ₁:ℂ)+t*I‖ := by
        have := abs_nonneg t
        linarith
      rw [div_le_iff₀ h8]
      have h9 : y^σ₁ * (4/(1+|t|)) * ((9/32) * (1+|t|)) ≤ y^σ₁ * (4/(1+|t|)) * ‖(σ₁:ℂ)+t*I‖ := by
        apply mul_le_mul_of_nonneg_left h4
        have h11 : (0:ℝ) ≤ y^σ₁ := Real.rpow_nonneg hy0.le σ₁
        positivity
      have htne : (0:ℝ) < 1+|t| := by positivity
      have h10 : y^σ₁ * (4/(1+|t|)) * ((9/32) * (1+|t|)) = y^σ₁ * (9/8) := by
        field_simp
        ring
      have h11 : (0:ℝ) ≤ y^σ₁ := Real.rpow_nonneg hy0.le σ₁
      linarith [h9, h10.symm.le, h10.le]
    calc ‖deriv gFun ((σ₁:ℂ)+t*I)‖ / ‖gFun ((σ₁:ℂ)+t*I)‖
        * (y ^ σ₁ / ‖(σ₁:ℂ)+t*I‖)
        ≤ 4 * (y^σ₁ * (4/(1+|t|))) := by
          apply mul_le_mul h3 h7 (by positivity) (by norm_num)
      _ = 16 * y^σ₁ * (1/(1+|t|)) := by ring
  -- integrate
  have hcont : ContinuousOn (fun t : ℝ =>
      (deriv gFun ((σ₁:ℂ)+t*I) / gFun ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))) (Set.uIcc u v) := by
    apply contOn_vert_stripInt diskData_gFun hy0 (by linarith) (by linarith)
    intro t _
    exact hgnz t
  calc ‖∫ t in u..v, (deriv gFun ((σ₁:ℂ)+t*I) / gFun ((σ₁:ℂ)+t*I))
      * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖
      ≤ ∫ t in u..v, ‖(deriv gFun ((σ₁:ℂ)+t*I) / gFun ((σ₁:ℂ)+t*I))
        * ((y:ℂ)^((σ₁:ℂ)+t*I) / ((σ₁:ℂ)+t*I))‖ :=
        intervalIntegral.norm_integral_le_integral_norm huv
    _ ≤ ∫ t in u..v, 16 * y^σ₁ * (1/(1+|t|)) := by
        apply intervalIntegral.integral_mono_on huv hcont.norm.intervalIntegrable
          ((continuous_const.mul continuous_one_div_one_add_abs).intervalIntegrable _ _)
          hptw
    _ = 16 * y^σ₁ * ∫ t in u..v, (1/(1+|t|)) := by
        rw [intervalIntegral.integral_const_mul]
    _ ≤ 16 * y^σ₁ * (2 * Real.log (1 + U)) := by
        apply mul_le_mul_of_nonneg_left
          (integral_one_div_one_add_abs_le hu hv hUu hUv)
        positivity
    _ = 32 * y^σ₁ * Real.log (1 + U) := by ring

/-- Right-edge overshoot bound for the `g`-part. -/
lemma g_right_extra_le {y c T u v : ℝ} (hy : 100 ≤ y)
    (hc : c = 1 + 1/Real.log y) (hT : 2 ≤ T)
    (huv : u ≤ v) (hlen : v - u ≤ 1) (hfar : ∀ t ∈ Set.Icc u v, T ≤ |t|) :
    ‖∫ t in u..v, (deriv gFun ((c:ℂ)+t*I) / gFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))‖
      ≤ 9 * (y * Real.log y / T) := by
  have hy0 : (0:ℝ) < y := by linarith
  have hlogy : 4 ≤ Real.log y := four_le_log hy
  have hlogy0 : (0:ℝ) < Real.log y := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hc1 : 1 < c := by
    rw [hc]
    have := one_div_pos.mpr hlogy0
    linarith
  have hyc3 : y ^ c ≤ 3 * y := by
    rw [hc, rpow_one_add_inv_log hy]
    nlinarith [Real.exp_one_lt_d9]
  -- lower bound for `g` on the line
  have hgge : ∀ t : ℝ, Real.log 2/(2*Real.log y) ≤ ‖gFun ((c:ℂ)+t*I)‖ := by
    intro t
    have h1 : ‖(2:ℂ) ^ ((1:ℂ) - ((c:ℂ)+t*I))‖ = (2:ℝ) ^ (1-c) := by
      rw [norm_two_cpow, re_coord]
    have hL2a : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h2 : (2:ℝ) ^ (1-c) = Real.exp (-(Real.log 2/Real.log y)) := by
      rw [Real.rpow_def_of_pos (by norm_num), hc]
      congr 1
      ring
    have h3 : Real.exp (-(Real.log 2/Real.log y)) ≤ 1/(1 + Real.log 2/Real.log y) := by
      rw [Real.exp_neg, inv_eq_one_div]
      apply one_div_le_one_div_of_le (by positivity)
      have h3a := Real.add_one_le_exp (Real.log 2/Real.log y)
      linarith
    have h4 : (2:ℝ) ^ (1-c) ≤ 1 - Real.log 2/(2*Real.log y) := by
      rw [h2]
      have h5 : Real.log 2/Real.log y ≤ 1 := by
        rw [div_le_one hlogy0]
        linarith [Real.log_two_lt_d9]
      have h6 : (0:ℝ) < Real.log 2/Real.log y := by
        positivity
      calc Real.exp (-(Real.log 2/Real.log y))
          ≤ 1/(1 + Real.log 2/Real.log y) := h3
        _ ≤ 1 - Real.log 2/(2*Real.log y) := by
            rw [div_le_iff₀ (by positivity)]
            have h7 : Real.log 2/(2*Real.log y) = (Real.log 2/Real.log y)/2 := by
              ring
            rw [h7]
            nlinarith
    calc Real.log 2/(2*Real.log y) ≤ 1 - (2:ℝ)^(1-c) := by linarith
      _ ≤ ‖(1:ℂ)‖ - ‖(2:ℂ) ^ ((1:ℂ) - ((c:ℂ)+t*I))‖ := by
          rw [norm_one, h1]
      _ ≤ ‖gFun ((c:ℂ)+t*I)‖ := norm_sub_norm_le _ _
  have hbnd : ∀ t ∈ Set.uIoc u v,
      ‖(deriv gFun ((c:ℂ)+t*I) / gFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))‖
      ≤ (3 * Real.log y) * (3*y/T) := by
    intro t ht
    have htmem : t ∈ Set.Icc u v := by
      rw [Set.uIoc_of_le huv] at ht
      exact ⟨le_of_lt ht.1, ht.2⟩
    rw [norm_mul, norm_div, norm_div, norm_cpow_coord hy0]
    have h1 : ‖deriv gFun ((c:ℂ)+t*I)‖ ≤ 1 :=
      norm_deriv_gFun_le (by rw [re_coord]; linarith)
    have h2 := hgge t
    have hL2a : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    have h3 : ‖deriv gFun ((c:ℂ)+t*I)‖ / ‖gFun ((c:ℂ)+t*I)‖ ≤ 3 * Real.log y := by
      have h4 : (0:ℝ) < Real.log 2/(2*Real.log y) := by positivity
      rw [div_le_iff₀ (by linarith)]
      calc ‖deriv gFun ((c:ℂ)+t*I)‖ ≤ 1 := h1
        _ ≤ 3 * Real.log y * (Real.log 2/(2*Real.log y)) := by
            rw [show 3 * Real.log y * (Real.log 2/(2*Real.log y))
              = (3/2) * Real.log 2 from by field_simp]
            linarith
        _ ≤ 3 * Real.log y * ‖gFun ((c:ℂ)+t*I)‖ := by
            apply mul_le_mul_of_nonneg_left h2 (by nlinarith)
    have h5 : y ^ c / ‖(c:ℂ)+t*I‖ ≤ 3*y/T := by
      have h6 : T ≤ ‖(c:ℂ)+t*I‖ := le_trans (hfar t htmem) (norm_coord_ge_abs_im c t)
      calc y ^ c / ‖(c:ℂ)+t*I‖
          ≤ y ^ c / T :=
            div_le_div_of_nonneg_left (Real.rpow_nonneg hy0.le c) hT0 h6
        _ ≤ 3*y/T := div_le_div_right_of_pos hT0 hyc3
    exact mul_le_mul h3 h5
      (div_nonneg (Real.rpow_nonneg hy0.le c) (norm_nonneg _))
      (by nlinarith : (0:ℝ) ≤ 3 * Real.log y)
  calc ‖∫ t in u..v, (deriv gFun ((c:ℂ)+t*I) / gFun ((c:ℂ)+t*I))
      * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))‖
      ≤ (3 * Real.log y) * (3*y/T) * |v - u| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    _ ≤ (3 * Real.log y) * (3*y/T) * 1 := by
        apply mul_le_mul_of_nonneg_left _ ?_
        · rw [abs_of_nonneg (by linarith)]
          exact hlen
        · have h12 : (0:ℝ) ≤ 3*y/T := by positivity
          nlinarith
    _ = 9 * (y * Real.log y / T) := by ring

end SinBound

/-! ### The contour assembly for ζ (the trivial character mod 1) -/

section AssemblyZeta

/-- On `Re s > 1` the eta log-derivative splits as `g′/g + ζ′/ζ`. -/
lemma logDeriv_eta_split {s : ℂ} (hs : 1 < s.re) :
    deriv etaFun s / etaFun s
      = deriv gFun s / gFun s + deriv riemannZeta s / riemannZeta s := by
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    linarith
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs.le
  have hg : gFun s ≠ 0 := gFun_ne_zero_of_one_lt_re hs
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z ≠ 1} := by
    have h1 : IsOpen {z : ℂ | 0 < z.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have h2 : IsOpen {z : ℂ | z ≠ 1} := isOpen_compl_singleton
    exact h1.inter h2
  have hev : etaFun =ᶠ[𝓝 s] fun z => gFun z * riemannZeta z := by
    filter_upwards [hopen.mem_nhds (⟨hs0, hs1⟩ : s ∈ {z : ℂ | 0 < z.re ∧ z ≠ 1})]
      with z hz'
    exact etaFun_eqOn hz'
  have hzd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hgd : DifferentiableAt ℂ gFun s := differentiable_gFun s
  have hderiv : deriv etaFun s
      = deriv gFun s * riemannZeta s + gFun s * deriv riemannZeta s := by
    have h2 := hgd.hasDerivAt.mul hzd.hasDerivAt
    exact (h2.congr_of_eventuallyEq hev).deriv
  have heta : etaFun s = gFun s * riemannZeta s := etaFun_eq_mul hs0 hs1
  rw [hderiv, heta]
  rw [div_add_div _ _ hg hz]

set_option maxHeartbeats 1000000 in
/-- The closing numeric assembly for the ζ contour: turning the six edge bounds
into the ledger error at `A = 1`. -/
lemma zeta_final_numeric {y T LNT LNT4 LNTy σ₁ X : ℝ}
    (hy : 100 ≤ y) (hT : 2 ≤ T) (hlogy : 4 ≤ Real.log y)
    (hLNT1 : 1 ≤ LNT) (hLNT41 : 1 ≤ LNT4) (hLNTy1 : 1 ≤ LNTy)
    (hLNT4le : LNT4 ≤ 2 * LNT) (hLNT4y : LNT4 ≤ LNTy)
    (hlogyle : Real.log y ≤ LNTy) (hσ2 : σ₁ ≤ 5/8) (hX : 0 ≤ X)
    (hbound : 2*π*X
        ≤ ((1000000 * LNT4^2) * (3*y) / (T * Real.log y)
            + (10000 * LNT4) * (3*y) / (T * Real.log y))
          + ((1000000 * LNT4^2) * (3*y) / (T * Real.log y)
            + (10000 * LNT4) * (3*y) / (T * Real.log y))
          + (18 * (y * Real.log y ^ 2 / T))
          + (18 * (y * Real.log y ^ 2 / T))
          + (20000000 * y^σ₁ * LNT4^2 + 32 * y^σ₁ * LNT)
          + 2*π*(2700 * y^((5:ℝ)/8) * LNT^2 + 448 * (y * LNTy^2 / T))) :
    X ≤ 1000000000 * (y * LNTy^2 / T + y^((5:ℝ)/8) * LNT^2) := by
  have hy0 : (0:ℝ) < y := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hlogy0 : (0:ℝ) < Real.log y := by linarith
  have hπ3 : (3:ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hπ7 : 2*π ≤ 7 := by
    have := Real.pi_lt_d2
    linarith
  have hyσ : (0:ℝ) ≤ y^σ₁ := Real.rpow_nonneg hy0.le σ₁
  have hy58 : (0:ℝ) ≤ y^((5:ℝ)/8) := Real.rpow_nonneg hy0.le _
  have hrp : y ^ σ₁ ≤ y ^ ((5:ℝ)/8) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) hσ2
  set P1 : ℝ := y * LNTy^2 / T with hP1def
  set P2 : ℝ := y^((5:ℝ)/8) * LNT^2 with hP2def
  have hP1nn : 0 ≤ P1 := by
    rw [hP1def]
    exact div_nonneg (mul_nonneg hy0.le (sq_nonneg LNTy)) hT0.le
  have hP2nn : 0 ≤ P2 := by
    rw [hP2def]
    exact mul_nonneg hy58 (sq_nonneg LNT)
  have hLNT4sq : LNT4^2 ≤ 4 * LNT^2 := by nlinarith
  have hLNTysq : LNT4^2 ≤ LNTy^2 := by nlinarith
  have hlogsq : Real.log y ^ 2 ≤ LNTy^2 := by nlinarith
  have hTlog : 4 * T ≤ T * Real.log y := by nlinarith
  have hb1 : (1000000 * LNT4^2) * (3*y) / (T * Real.log y) ≤ 750000 * P1 := by
    rw [hP1def]
    have h0 := mul_le_mul_of_nonneg_left hLNTysq hy0.le
    have h1 : (1000000 * LNT4^2) * (3*y) ≤ 3000000 * (y * LNTy^2) := by linarith
    calc (1000000 * LNT4^2) * (3*y) / (T * Real.log y)
        ≤ 3000000 * (y * LNTy^2) / (4 * T) := by
          refine div_le_div₀ ?_ h1 ?_ hTlog
          · nlinarith [sq_nonneg LNTy]
          · linarith
      _ = 750000 * (y * LNTy^2 / T) := by ring
  have hb1g : (10000 * LNT4) * (3*y) / (T * Real.log y) ≤ 7500 * P1 := by
    rw [hP1def]
    have hL1 : LNT4 ≤ LNTy^2 := by nlinarith
    have h0 := mul_le_mul_of_nonneg_left hL1 hy0.le
    have h1 : (10000 * LNT4) * (3*y) ≤ 30000 * (y * LNTy^2) := by linarith
    calc (10000 * LNT4) * (3*y) / (T * Real.log y)
        ≤ 30000 * (y * LNTy^2) / (4 * T) := by
          refine div_le_div₀ ?_ h1 ?_ hTlog
          · nlinarith
          · linarith
      _ = 7500 * (y * LNTy^2 / T) := by ring
  have hb2 : 18 * (y * Real.log y ^ 2 / T) ≤ 18 * P1 := by
    rw [hP1def]
    have h0 := mul_le_mul_of_nonneg_left hlogsq hy0.le
    have h2 : y * Real.log y ^ 2 / T ≤ y * LNTy^2 / T :=
      div_le_div_right_of_pos hT0 h0
    linarith
  have hb3 : 20000000 * y^σ₁ * LNT4^2 ≤ 80000000 * P2 := by
    rw [hP2def]
    have h3 : y^σ₁ * LNT4^2 ≤ y^((5:ℝ)/8) * LNT4^2 :=
      mul_le_mul_of_nonneg_right hrp (sq_nonneg LNT4)
    have h4 : y^((5:ℝ)/8) * LNT4^2 ≤ y^((5:ℝ)/8) * (4 * LNT^2) :=
      mul_le_mul_of_nonneg_left hLNT4sq hy58
    linarith
  have hb3g : 32 * y^σ₁ * LNT ≤ 32 * P2 := by
    rw [hP2def]
    have h2 : LNT ≤ LNT^2 := by nlinarith
    have h3 : y^σ₁ * LNT ≤ y^((5:ℝ)/8) * LNT :=
      mul_le_mul_of_nonneg_right hrp (by linarith)
    have h4 : y^((5:ℝ)/8) * LNT ≤ y^((5:ℝ)/8) * LNT^2 :=
      mul_le_mul_of_nonneg_left h2 hy58
    linarith
  have hb4 : 2*π*(2700 * y^((5:ℝ)/8) * LNT^2 + 448 * (y * LNTy^2 / T))
      ≤ 18900 * P2 + 3136 * P1 := by
    have h0 : 2700 * y^((5:ℝ)/8) * LNT^2 + 448 * (y * LNTy^2 / T)
        = 2700 * P2 + 448 * P1 := by
      rw [hP1def, hP2def]
      ring
    rw [h0]
    nlinarith [hπ7, hP1nn, hP2nn]
  have hfinal6 : 6 * X ≤ 2*π*X := by nlinarith [hπ3, hX]
  have htotal : 2*π*X ≤ 1518172 * P1 + 80018932 * P2 := by
    calc 2*π*X ≤ _ := hbound
      _ ≤ 1518172 * P1 + 80018932 * P2 := by
          linarith [hb1, hb1g, hb2, hb3, hb3g, hb4]
  show X ≤ 1000000000 * (P1 + P2)
  linarith [hP1nn, hP2nn, hfinal6, htotal]

set_option maxHeartbeats 4000000 in
/-- **Contour phase for ζ**: Perron sum plus contract zero sum minus the main
term `y` is controlled by the ledger error, at `A = 1`. -/
theorem contour_zeta {y T : ℝ} (hy : 100 ≤ y) (hT : 2 ≤ T) :
    ‖perronSum (1 : DirichletCharacter ℂ 1) y (1 + 1/Real.log y) T
      + (∑ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T,
          (analyticOrderNatAt riemannZeta ρ : ℂ) * ((y:ℂ)^ρ/ρ))
      - (y:ℂ)‖
      ≤ 1000000000 * (y * Real.log ((1:ℝ)*T*y)^2 / T
          + y^((5:ℝ)/8) * Real.log ((1:ℝ)*(T+2))^2) := by
  classical
  have hDD : DiskData etaFun 1 := diskData_etaFun
  have hDDg : DiskData gFun 1 := diskData_gFun
  have hLmod : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)
      = riemannZeta := DirichletCharacter.LFunction_modOne_eq
  -- numerics (A = 1)
  have hy0 : (0:ℝ) < y := by linarith
  have hy1 : (1:ℝ) < y := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  have hlogy : 4 ≤ Real.log y := four_le_log hy
  have hlogy0 : (0:ℝ) < Real.log y := by linarith
  have hinvlog : 1 / Real.log y ≤ 1/4 :=
    one_div_le_one_div_of_le (by norm_num) hlogy
  have hinvlog0 : 0 < 1 / Real.log y := one_div_pos.mpr hlogy0
  set c : ℝ := 1 + 1/Real.log y with hcdef
  have hc1 : 1 < c := by rw [hcdef]; linarith
  have hc54 : c ≤ 5/4 := by rw [hcdef]; linarith
  have hyc : y ^ c = Real.exp 1 * y := by rw [hcdef]; exact rpow_one_add_inv_log hy
  have hyc3 : y ^ c ≤ 3 * y := by
    rw [hyc]
    nlinarith [Real.exp_one_lt_d9]
  set LNT : ℝ := Real.log ((1:ℝ)*(T+2)) with hLNTdef
  set LNT4 : ℝ := Real.log ((1:ℝ)*(T+4)) with hLNT4def
  set LNTy : ℝ := Real.log ((1:ℝ)*T*y) with hLNTydef
  have hLNT1 : 1 ≤ LNT := by
    rw [hLNTdef, Real.le_log_iff_exp_le (by nlinarith)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hLNT41 : 1 ≤ LNT4 := by
    rw [hLNT4def, Real.le_log_iff_exp_le (by nlinarith)]
    have := Real.exp_one_lt_d9
    nlinarith
  have hLNT4le : LNT4 ≤ 2 * LNT := by
    rw [hLNT4def, hLNTdef]
    have h0 : (1:ℝ)*(T+4) ≤ ((1:ℝ)*(T+2))^2 := by nlinarith
    calc Real.log ((1:ℝ)*(T+4)) ≤ Real.log (((1:ℝ)*(T+2))^2) :=
        Real.log_le_log (by nlinarith) h0
      _ = 2 * Real.log ((1:ℝ)*(T+2)) := by
          rw [Real.log_pow]
          push_cast
          ring
  have hTy4 : (T+4:ℝ) ≤ T*y := by nlinarith
  have hTy2 : (T+2:ℝ) ≤ T*y := by nlinarith
  have hLNT4y : LNT4 ≤ LNTy := by
    rw [hLNT4def, hLNTydef]
    apply Real.log_le_log (by nlinarith)
    nlinarith
  have hLNTle : LNT ≤ LNTy := by
    rw [hLNTdef, hLNTydef]
    apply Real.log_le_log (by nlinarith)
    nlinarith
  have hlogyle : Real.log y ≤ LNTy := by
    rw [hLNTydef]
    apply Real.log_le_log hy0
    nlinarith
  have hLNTy1 : 1 ≤ LNTy := by linarith
  -- the pigeonholed g-ordinates
  set q : ℝ := π / Real.log 2 with hqdef
  set kone : ℤ := round (T / q) with hkonedef
  set Γex : Finset ℝ := {((kone - 1 : ℤ) : ℝ) * q, ((kone : ℤ) : ℝ) * q,
    ((kone + 1 : ℤ) : ℝ) * q} with hΓexdef
  have hΓexcard : ((Γex.card : ℝ)) ≤ 16 * Real.log ((1:ℝ)*(T+4)) := by
    have h1 : Γex.card ≤ 3 := by
      rw [hΓexdef]
      apply le_trans (Finset.card_insert_le _ _)
      have h2 := Finset.card_insert_le (((kone : ℤ) : ℝ) * q)
        ({((kone + 1 : ℤ) : ℝ) * q} : Finset ℝ)
      simp at h2 ⊢
      omega
    have h3 : (Γex.card : ℝ) ≤ 3 := by exact_mod_cast h1
    rw [← hLNT4def]
    linarith
  -- good heights for η (top) and its reflection (bottom)
  obtain ⟨t₂, ht₂1, ht₂2, ht₂gap, htop⟩ := exists_good_height hDD hT Γex hΓexcard
  obtain ⟨t₁, ht₁1, ht₁2, ht₁gap, hbot'⟩ :=
    exists_good_height hDD.conj hT Γex hΓexcard
  have hbot : ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 3 →
      etaFun ((σ:ℂ) + (-t₁ : ℝ)*I) ≠ 0 ∧
      ‖deriv etaFun ((σ:ℂ) + (-t₁:ℝ)*I) / etaFun ((σ:ℂ) + (-t₁:ℝ)*I)‖
        ≤ 1000000 * LNT4^2 := by
    intro σ h1 h2
    obtain ⟨hnz', hbd'⟩ := hbot' σ h1 h2
    constructor
    · intro h0
      apply hnz'
      show (starRingEnd ℂ) (etaFun ((starRingEnd ℂ) ((σ:ℂ) + t₁*I))) = 0
      rw [conj_coord σ t₁, h0, map_zero]
    · have heq := norm_logDeriv_conjF etaFun ((σ:ℂ) + (-t₁:ℝ)*I)
      rw [conj_coord σ (-t₁)] at heq
      simp only [neg_neg] at heq
      rw [heq, hLNT4def]
      exact hbd'
  -- sine lower bounds at the two heights
  set δ₀ : ℝ := 1 / (2000 * Real.log ((1:ℝ)*(T+4))) with hδ₀def
  have hδ₀0 : 0 < δ₀ := by
    rw [hδ₀def]
    have : (0:ℝ) < Real.log ((1:ℝ)*(T+4)) := by
      rw [← hLNT4def]
      linarith
    positivity
  have hδmem : ∀ j : ℤ, (j = kone - 1 ∨ j = kone ∨ j = kone + 1) →
      ((j : ℝ) * q) ∈ Γex := by
    intro j hj
    rw [hΓexdef]
    rcases hj with rfl | rfl | rfl
    · simp
    · simp
    · simp
  have hsin₂ : δ₀/4 ≤ |Real.sin (t₂ * Real.log 2)| := by
    apply abs_sin_log_two_ge hT ht₂1 ht₂2 hδ₀0
    intro j hj
    exact ht₂gap _ (hδmem j hj)
  have hsin₁ : δ₀/4 ≤ |Real.sin (t₁ * Real.log 2)| := by
    apply abs_sin_log_two_ge hT ht₁1 ht₁2 hδ₀0
    intro j hj
    exact ht₁gap _ (hδmem j hj)
  -- `g` lower bounds on the two horizontal lines
  have hg₂ : ∀ σ : ℝ, 9/16 ≤ σ → σ ≤ 5/4 →
      δ₀/5 ≤ ‖gFun ((σ:ℂ) + t₂*I)‖ := by
    intro σ h1 h2
    calc δ₀/5 = (4/5) * (δ₀/4) := by ring
      _ ≤ (4/5) * |Real.sin (t₂ * Real.log 2)| := by
          apply mul_le_mul_of_nonneg_left hsin₂ (by norm_num)
      _ ≤ ‖gFun ((σ:ℂ) + t₂*I)‖ := norm_gFun_ge_sin h1 h2
  have hg₁ : ∀ σ : ℝ, 9/16 ≤ σ → σ ≤ 5/4 →
      δ₀/5 ≤ ‖gFun ((σ:ℂ) + (-t₁:ℝ)*I)‖ := by
    intro σ h1 h2
    have h3 : |Real.sin ((-t₁) * Real.log 2)| = |Real.sin (t₁ * Real.log 2)| := by
      rw [show (-t₁) * Real.log 2 = -(t₁ * Real.log 2) by ring,
        Real.sin_neg, abs_neg]
    calc δ₀/5 = (4/5) * (δ₀/4) := by ring
      _ ≤ (4/5) * |Real.sin ((-t₁) * Real.log 2)| := by
          rw [h3]
          apply mul_le_mul_of_nonneg_left hsin₁ (by norm_num)
      _ ≤ ‖gFun ((σ:ℂ) + (-t₁:ℝ)*I)‖ := norm_gFun_ge_sin h1 h2
  -- Step B: `σ₁` (pigeonholed against the η-zeros only; `g`-zeros sit on `Re = 1`)
  set Bset : Finset ℝ := (boxZeros etaFun (T+4)).image Complex.re with hBdef
  set M : ℕ := ⌈2*(t₁+t₂)⌉₊ with hMdef
  have hMceil : 2*(t₁+t₂) ≤ (M:ℝ) := Nat.le_ceil _
  have hMceil' : (M:ℝ) < 2*(t₁+t₂) + 1 := Nat.ceil_lt_add_one (by nlinarith)
  have ha' : -(T+1) ≤ -t₁ := by linarith
  have ha0 : -t₁ ≤ (0:ℝ) := by linarith
  have hM1 : (0:ℝ) ≤ -t₁ + (M:ℝ)/2 := by nlinarith
  have hM2 : -t₁ + (M:ℝ)/2 ≤ T + 2 := by nlinarith
  have hM3 : t₂ ≤ -t₁ + (M:ℝ)/2 := by nlinarith
  obtain ⟨σ₁, hσ1, hσ2, hσB, hσH⟩ :=
    exists_good_sigma hDD (a := -t₁) (M := M) hT ha' ha0 hM1 hM2 Bset
  have hσc : σ₁ < c := by linarith
  have hσre : ∀ ρ ∈ boxZeros etaFun (T+4), ρ.re ≠ σ₁ := by
    intro ρ hρ h
    apply hσB
    rw [hBdef, ← h]
    exact Finset.mem_image_of_mem _ hρ
  have hgnzline : ∀ x t : ℝ, x ≤ 5/8 → gFun ((x:ℂ) + t*I) ≠ 0 := by
    intro x t hx h0
    have h1 := norm_gFun_ge_left (s := (x:ℂ) + t*I) (by rw [re_coord]; exact hx)
    rw [h0, norm_zero] at h1
    linarith
  -- Step C: cuts, avoiding both zero sets
  obtain ⟨m, τ, hm1, hτ0, hτm, hτmono, hτgap, hτavoid, hτrange⟩ :=
    exists_cuts (((boxZeros etaFun (T+4)).image Complex.im)
      ∪ ((boxZeros gFun (T+4)).image Complex.im)) (by linarith : 4 ≤ t₁ + t₂)
  have hτbounds : ∀ j ≤ m, -(T+4) ≤ τ j ∧ τ j ≤ T+4 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hτrange j hj
    constructor <;> linarith
  have hcutzeros : ∀ j ≤ m, ∀ ρ ∈ boxZeros etaFun (T+4), ρ.im ≠ τ j := by
    intro j hj ρ hρ him
    obtain ⟨⟨hre1, hre2⟩, ⟨him1, him2⟩, hzero⟩ := (mem_boxZeros hDD).mp hρ
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hτ0] at him
      have h1 := (hbot ρ.re hre1 (by linarith)).1
      apply h1
      have h2 : ((ρ.re:ℂ) + (-t₁:ℝ)*I) = ρ := by
        rw [← him]
        exact Complex.re_add_im ρ
      rw [h2]
      exact hzero
    · rcases Nat.lt_or_ge j m with hjm | hjm
      · apply hτavoid j hj0 hjm
        rw [Finset.mem_union]
        left
        rw [← him]
        exact Finset.mem_image_of_mem _ hρ
      · have hjm' : j = m := by omega
        rw [hjm', hτm] at him
        have h1 := (htop ρ.re hre1 (by linarith)).1
        apply h1
        have h2 : ((ρ.re:ℂ) + t₂*I) = ρ := by
          rw [← him]
          exact Complex.re_add_im ρ
        rw [h2]
        exact hzero
  have hcutzerosg : ∀ j ≤ m, ∀ ρ ∈ boxZeros gFun (T+4), ρ.im ≠ τ j := by
    intro j hj ρ hρ him
    obtain ⟨⟨hre1, hre2⟩, ⟨him1, him2⟩, hzero⟩ := (mem_boxZeros hDDg).mp hρ
    have hre : ρ.re = 1 := (gFun_zero_imp hzero).1
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [hτ0] at him
      have h1 := hg₁ 1 (by norm_num) (by norm_num)
      have h2 : ((1:ℝ):ℂ) + (-t₁:ℝ)*I = ρ := by
        rw [← hre, ← him]
        exact Complex.re_add_im ρ
      rw [h2, hzero, norm_zero] at h1
      linarith
    · rcases Nat.lt_or_ge j m with hjm | hjm
      · apply hτavoid j hj0 hjm
        rw [Finset.mem_union]
        right
        rw [← him]
        exact Finset.mem_image_of_mem _ hρ
      · have hjm' : j = m := by omega
        rw [hjm', hτm] at him
        have h1 := hg₂ 1 (by norm_num) (by norm_num)
        have h2 : ((1:ℝ):ℂ) + (t₂:ℝ)*I = ρ := by
          rw [← hre, ← him]
          exact Complex.re_add_im ρ
        rw [h2, hzero, norm_zero] at h1
        linarith
  have hboxmem : ∀ (σ t : ℝ), 1/2 ≤ σ → σ ≤ 3/2 → -(T+4) ≤ t → t ≤ T+4 →
      etaFun ((σ:ℂ) + t*I) = 0 → ((σ:ℂ) + t*I) ∈ boxZeros etaFun (T+4) := by
    intro σ t h1 h2 h3 h4 h5
    rw [mem_boxZeros hDD, re_coord, im_coord]
    exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
  have hlines : ∀ j ≤ m, ∀ σ ∈ Set.Icc σ₁ c, etaFun ((σ:ℂ) + (τ j)*I) ≠ 0 := by
    intro j hj σ hσ h0
    obtain ⟨hb1, hb2⟩ := hτbounds j hj
    have hmem := hboxmem σ (τ j) (by linarith [hσ.1]) (by linarith [hσ.2]) hb1 hb2 h0
    exact hcutzeros j hj _ hmem (im_coord σ (τ j))
  have hlinesg : ∀ j ≤ m, ∀ σ ∈ Set.Icc σ₁ c, gFun ((σ:ℂ) + (τ j)*I) ≠ 0 := by
    intro j hj σ hσ h0
    obtain ⟨hb1, hb2⟩ := hτbounds j hj
    have hre : σ = 1 := by
      have h := (gFun_zero_imp h0).1
      rwa [re_coord] at h
    have hmem : ((σ:ℂ) + (τ j)*I) ∈ boxZeros gFun (T+4) := by
      rw [mem_boxZeros hDDg, re_coord, im_coord]
      exact ⟨⟨by linarith, by linarith⟩, ⟨hb1, hb2⟩, h0⟩
    exact hcutzerosg j hj _ hmem (im_coord σ (τ j))
  have hleftnz : ∀ t : ℝ, -(T+4) ≤ t → t ≤ T+4 → etaFun ((σ₁:ℂ) + t*I) ≠ 0 := by
    intro t h1 h2 h0
    have hmem := hboxmem σ₁ t (by linarith) (by linarith) h1 h2 h0
    exact hσre _ hmem (re_coord σ₁ t)
  have hleft : ∀ t ∈ Set.Icc (τ 0) (τ m), etaFun ((σ₁:ℂ) + t*I) ≠ 0 := by
    intro t ht
    rw [hτ0] at ht
    rw [hτm] at ht
    exact hleftnz t (by linarith [ht.1]) (by linarith [ht.2])
  have hleftg : ∀ t ∈ Set.Icc (τ 0) (τ m), gFun ((σ₁:ℂ) + t*I) ≠ 0 :=
    fun t _ => hgnzline σ₁ t (by linarith)
  -- Step D: the two chains
  have hchain := rectInt_chain hDD hy1 hσ1 hσc hc1 hc54 τ m hτmono hτgap hlines hleft
  have hfusion := chain_sum_eq_box hDD
    (fun ρ => (analyticOrderNatAt etaFun ρ : ℂ) * ((y:ℂ)^ρ/ρ))
    hσ1 hσc hc54 τ m hτmono hτgap
    (by rw [hτ0]; linarith) (by rw [hτm]; linarith) hcutzeros
  rw [hfusion] at hchain
  simp only [hτ0, hτm] at hchain
  have hchaing := rectInt_chain hDDg hy1 hσ1 hσc hc1 hc54 τ m hτmono hτgap
    hlinesg hleftg
  have hfusiong := chain_sum_eq_box hDDg
    (fun ρ => (analyticOrderNatAt gFun ρ : ℂ) * ((y:ℂ)^ρ/ρ))
    hσ1 hσc hc54 τ m hτmono hτgap
    (by rw [hτ0]; linarith) (by rw [hτm]; linarith) hcutzerosg
  rw [hfusiong] at hchaing
  simp only [hτ0, hτm] at hchaing
  rw [rectInt_edges] at hchain hchaing
  -- named pieces
  set Sp : ℂ := perronSum (1 : DirichletCharacter ℂ 1) y c T with hSpdef
  set SC : ℂ := ∑ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T,
      (analyticOrderNatAt riemannZeta ρ : ℂ) * ((y:ℂ)^ρ/ρ) with hSCdef
  set Ze : Finset ℂ := (boxZeros etaFun (T+4)).filter
      (fun ρ => σ₁ < ρ.re ∧ ρ.re < c ∧ -t₁ < ρ.im ∧ ρ.im < t₂) with hZedef
  set Zg : Finset ℂ := (boxZeros gFun (T+4)).filter
      (fun ρ => σ₁ < ρ.re ∧ ρ.re < c ∧ -t₁ < ρ.im ∧ ρ.im < t₂) with hZgdef
  set IAe : ℂ := ∫ x in σ₁..c,
      (deriv etaFun ((x:ℂ) + (-t₁:ℝ)*I) / etaFun ((x:ℂ) + (-t₁:ℝ)*I))
      * ((y:ℂ)^((x:ℂ) + (-t₁:ℝ)*I) / ((x:ℂ) + (-t₁:ℝ)*I)) with hIAedef
  set IBe : ℂ := ∫ x in σ₁..c,
      (deriv etaFun ((x:ℂ) + t₂*I) / etaFun ((x:ℂ) + t₂*I))
      * ((y:ℂ)^((x:ℂ) + t₂*I) / ((x:ℂ) + t₂*I)) with hIBedef
  set IRe : ℂ := ∫ t in (-t₁)..t₂,
      (deriv etaFun ((c:ℂ) + t*I) / etaFun ((c:ℂ) + t*I))
      * ((y:ℂ)^((c:ℂ) + t*I) / ((c:ℂ) + t*I)) with hIRedef
  set ILe : ℂ := ∫ t in (-t₁)..t₂,
      (deriv etaFun ((σ₁:ℂ) + t*I) / etaFun ((σ₁:ℂ) + t*I))
      * ((y:ℂ)^((σ₁:ℂ) + t*I) / ((σ₁:ℂ) + t*I)) with hILedef
  set IAg : ℂ := ∫ x in σ₁..c,
      (deriv gFun ((x:ℂ) + (-t₁:ℝ)*I) / gFun ((x:ℂ) + (-t₁:ℝ)*I))
      * ((y:ℂ)^((x:ℂ) + (-t₁:ℝ)*I) / ((x:ℂ) + (-t₁:ℝ)*I)) with hIAgdef
  set IBg : ℂ := ∫ x in σ₁..c,
      (deriv gFun ((x:ℂ) + t₂*I) / gFun ((x:ℂ) + t₂*I))
      * ((y:ℂ)^((x:ℂ) + t₂*I) / ((x:ℂ) + t₂*I)) with hIBgdef
  set IRg : ℂ := ∫ t in (-t₁)..t₂,
      (deriv gFun ((c:ℂ) + t*I) / gFun ((c:ℂ) + t*I))
      * ((y:ℂ)^((c:ℂ) + t*I) / ((c:ℂ) + t*I)) with hIRgdef
  set ILg : ℂ := ∫ t in (-t₁)..t₂,
      (deriv gFun ((σ₁:ℂ) + t*I) / gFun ((σ₁:ℂ) + t*I))
      * ((y:ℂ)^((σ₁:ℂ) + t*I) / ((σ₁:ℂ) + t*I)) with hILgdef
  set ICz : ℂ := ∫ t in (-t₁)..(-T),
      (deriv riemannZeta ((c:ℂ) + t*I) / riemannZeta ((c:ℂ) + t*I))
      * ((y:ℂ)^((c:ℂ) + t*I) / ((c:ℂ) + t*I)) with hICzdef
  set IDz : ℂ := ∫ t in T..t₂,
      (deriv riemannZeta ((c:ℂ) + t*I) / riemannZeta ((c:ℂ) + t*I))
      * ((y:ℂ)^((c:ℂ) + t*I) / ((c:ℂ) + t*I)) with hIDzdef
  set SR : ℂ := ∑ ρ ∈ Ze, (analyticOrderNatAt riemannZeta ρ : ℂ) * ((y:ℂ)^ρ/ρ)
    with hSRdef
  -- residue bookkeeping: the `g`-zero at `s = 1` is the main term
  have hZe_ne1 : ∀ ρ ∈ Ze, ρ ≠ 1 := by
    intro ρ hρ h1
    rw [hZedef, Finset.mem_filter] at hρ
    have hz := ((mem_boxZeros hDD).mp hρ.1).2.2
    rw [h1] at hz
    exact etaFun_one_ne_zero hz
  have hZe_re0 : ∀ ρ ∈ Ze, 0 < ρ.re := by
    intro ρ hρ
    rw [hZedef, Finset.mem_filter] at hρ
    linarith [hρ.2.1]
  have hone_mem : (1:ℂ) ∈ Zg := by
    rw [hZgdef, Finset.mem_filter]
    constructor
    · rw [mem_boxZeros hDDg, Complex.one_re, Complex.one_im]
      refine ⟨⟨by norm_num, by norm_num⟩, ⟨by linarith, by linarith⟩, ?_⟩
      rw [gFun]
      norm_num
    · rw [Complex.one_re, Complex.one_im]
      exact ⟨by linarith, hc1, by linarith, by linarith⟩
  have hZgsub : Zg.erase 1 ⊆ Ze := by
    intro ρ hρ
    rw [Finset.mem_erase] at hρ
    obtain ⟨hne, hmem⟩ := hρ
    rw [hZgdef, Finset.mem_filter] at hmem
    obtain ⟨hbox, hf1, hf2, hf3, hf4⟩ := hmem
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩, hzero⟩ := (mem_boxZeros hDDg).mp hbox
    have hre1 : ρ.re = 1 := (gFun_zero_imp hzero).1
    have hηzero : etaFun ρ = 0 := by
      rw [etaFun_eq_mul (by rw [hre1]; norm_num) hne, hzero, zero_mul]
    rw [hZedef, Finset.mem_filter]
    exact ⟨(mem_boxZeros hDD).mpr ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩, hηzero⟩, hf1, hf2, hf3, hf4⟩
  have hordg_off : ∀ ρ ∈ Ze, ρ ∉ Zg.erase 1 →
      (analyticOrderNatAt gFun ρ : ℂ) * ((y:ℂ)^ρ/ρ) = 0 := by
    intro ρ hρ hnot
    have hne := hZe_ne1 ρ hρ
    have hg0 : analyticOrderNatAt gFun ρ = 0 := by
      by_contra hcon
      apply hnot
      rw [Finset.mem_erase]
      refine ⟨hne, ?_⟩
      have hgz : gFun ρ = 0 := by
        by_contra hgne
        apply hcon
        rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hgne)]
        rfl
      rw [hZedef, Finset.mem_filter] at hρ
      obtain ⟨hbox, hf⟩ := hρ
      obtain ⟨hre, him, -⟩ := (mem_boxZeros hDD).mp hbox
      rw [hZgdef, Finset.mem_filter]
      exact ⟨(mem_boxZeros hDDg).mpr ⟨hre, him, hgz⟩, hf⟩
    rw [hg0]
    norm_num
  have hgsum : ∑ ρ ∈ Zg.erase 1, (analyticOrderNatAt gFun ρ : ℂ) * ((y:ℂ)^ρ/ρ)
      = ∑ ρ ∈ Ze, (analyticOrderNatAt gFun ρ : ℂ) * ((y:ℂ)^ρ/ρ) :=
    Finset.sum_subset hZgsub hordg_off
  have hgtot : ∑ ρ ∈ Zg, (analyticOrderNatAt gFun ρ : ℂ) * ((y:ℂ)^ρ/ρ)
      = (y:ℂ) + ∑ ρ ∈ Ze, (analyticOrderNatAt gFun ρ : ℂ) * ((y:ℂ)^ρ/ρ) := by
    rw [← hgsum, ← Finset.add_sum_erase _ _ hone_mem, ord_gFun_one]
    norm_num
  have hdecomp : ∀ ρ ∈ Ze,
      (analyticOrderNatAt etaFun ρ : ℂ) * ((y:ℂ)^ρ/ρ)
        = (analyticOrderNatAt gFun ρ : ℂ) * ((y:ℂ)^ρ/ρ)
          + (analyticOrderNatAt riemannZeta ρ : ℂ) * ((y:ℂ)^ρ/ρ) := by
    intro ρ hρ
    rw [analyticOrderNatAt_eta_decomp (hZe_re0 ρ hρ) (hZe_ne1 ρ hρ)]
    push_cast
    ring
  have hres : (∑ ρ ∈ Ze, (analyticOrderNatAt etaFun ρ : ℂ) * ((y:ℂ)^ρ/ρ))
      - (∑ ρ ∈ Zg, (analyticOrderNatAt gFun ρ : ℂ) * ((y:ℂ)^ρ/ρ))
      = SR - (y:ℂ) := by
    rw [hSRdef, Finset.sum_congr rfl hdecomp, Finset.sum_add_distrib, hgtot]
    ring
  -- right-edge integrability for `η` and `g`
  have hRnze : ∀ t ∈ Set.uIcc (-(T+4)) (T+4), etaFun ((c:ℂ)+t*I) ≠ 0 := fun t _ =>
    hDD.nz _ (by rw [re_coord]; exact hc1)
  have hRnzg : ∀ t ∈ Set.uIcc (-(T+4)) (T+4), gFun ((c:ℂ)+t*I) ≠ 0 := fun t _ =>
    hDDg.nz _ (by rw [re_coord]; exact hc1)
  have hIntEe : ∀ u v : ℝ, -(T+4) ≤ u → u ≤ T+4 → -(T+4) ≤ v → v ≤ T+4 →
      IntervalIntegrable (fun t : ℝ =>
        (deriv etaFun ((c:ℂ)+t*I) / etaFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))) MeasureTheory.volume u v := by
    intro u v h1 h2 h3 h4
    apply ((contOn_vert_stripInt hDD hy0 (by linarith : (1:ℝ)/4 ≤ c)
      (by linarith : c ≤ 15/4) hRnze).mono _).intervalIntegrable
    apply Set.uIcc_subset_uIcc
    · rw [Set.uIcc_of_le (by linarith)]
      exact ⟨h1, h2⟩
    · rw [Set.uIcc_of_le (by linarith)]
      exact ⟨h3, h4⟩
  have hIntEg : ∀ u v : ℝ, -(T+4) ≤ u → u ≤ T+4 → -(T+4) ≤ v → v ≤ T+4 →
      IntervalIntegrable (fun t : ℝ =>
        (deriv gFun ((c:ℂ)+t*I) / gFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))) MeasureTheory.volume u v := by
    intro u v h1 h2 h3 h4
    apply ((contOn_vert_stripInt hDDg hy0 (by linarith : (1:ℝ)/4 ≤ c)
      (by linarith : c ≤ 15/4) hRnzg).mono _).intervalIntegrable
    apply Set.uIcc_subset_uIcc
    · rw [Set.uIcc_of_le (by linarith)]
      exact ⟨h1, h2⟩
    · rw [Set.uIcc_of_le (by linarith)]
      exact ⟨h3, h4⟩
  -- on `Re s = c` the difference of the `η` and `g` integrands is the `ζ` integrand
  have hdiffz : ∀ u v : ℝ, -(T+4) ≤ u → u ≤ T+4 → -(T+4) ≤ v → v ≤ T+4 →
      (∫ t in u..v, (deriv etaFun ((c:ℂ)+t*I) / etaFun ((c:ℂ)+t*I))
          * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
        - (∫ t in u..v, (deriv gFun ((c:ℂ)+t*I) / gFun ((c:ℂ)+t*I))
          * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      = ∫ t in u..v, (deriv riemannZeta ((c:ℂ)+t*I) / riemannZeta ((c:ℂ)+t*I))
          * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)) := by
    intro u v h1 h2 h3 h4
    rw [← intervalIntegral.integral_sub (hIntEe u v h1 h2 h3 h4)
      (hIntEg u v h1 h2 h3 h4)]
    apply intervalIntegral.integral_congr
    intro t _
    show (deriv etaFun ((c:ℂ)+t*I) / etaFun ((c:ℂ)+t*I))
          * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))
        - (deriv gFun ((c:ℂ)+t*I) / gFun ((c:ℂ)+t*I))
          * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))
        = (deriv riemannZeta ((c:ℂ)+t*I) / riemannZeta ((c:ℂ)+t*I))
          * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I))
    rw [logDeriv_eta_split (s := (c:ℂ)+t*I) (by rw [re_coord]; exact hc1)]
    ring
  -- the interchange on the symmetric window
  have hJ := integral_right_edge (1 : DirichletCharacter ℂ 1) (c := c) hy hc1 hT0
  rw [hLmod] at hJ
  have hJmid : (∫ t in (-T)..T,
      (deriv riemannZeta ((c:ℂ)+t*I) / riemannZeta ((c:ℂ)+t*I))
      * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      = -(((2 * π : ℝ) : ℂ) * Sp) := by
    rw [hSpdef, ← hJ, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  -- split the full right edge
  have hsp1e : (∫ t in (-t₁)..(-T),
        (deriv etaFun ((c:ℂ)+t*I) / etaFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      + (∫ t in (-T)..T,
        (deriv etaFun ((c:ℂ)+t*I) / etaFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      = ∫ t in (-t₁)..T,
        (deriv etaFun ((c:ℂ)+t*I) / etaFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hIntEe _ _ (by linarith) (by linarith) (by linarith) (by linarith))
      (hIntEe _ _ (by linarith) (by linarith) (by linarith) (by linarith))
  have hsp2e : (∫ t in (-t₁)..T,
        (deriv etaFun ((c:ℂ)+t*I) / etaFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      + (∫ t in T..t₂,
        (deriv etaFun ((c:ℂ)+t*I) / etaFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      = ∫ t in (-t₁)..t₂,
        (deriv etaFun ((c:ℂ)+t*I) / etaFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hIntEe _ _ (by linarith) (by linarith) (by linarith) (by linarith))
      (hIntEe _ _ (by linarith) (by linarith) (by linarith) (by linarith))
  have hsp1g : (∫ t in (-t₁)..(-T),
        (deriv gFun ((c:ℂ)+t*I) / gFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      + (∫ t in (-T)..T,
        (deriv gFun ((c:ℂ)+t*I) / gFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      = ∫ t in (-t₁)..T,
        (deriv gFun ((c:ℂ)+t*I) / gFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hIntEg _ _ (by linarith) (by linarith) (by linarith) (by linarith))
      (hIntEg _ _ (by linarith) (by linarith) (by linarith) (by linarith))
  have hsp2g : (∫ t in (-t₁)..T,
        (deriv gFun ((c:ℂ)+t*I) / gFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      + (∫ t in T..t₂,
        (deriv gFun ((c:ℂ)+t*I) / gFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)))
      = ∫ t in (-t₁)..t₂,
        (deriv gFun ((c:ℂ)+t*I) / gFun ((c:ℂ)+t*I))
        * ((y:ℂ)^((c:ℂ)+t*I) / ((c:ℂ)+t*I)) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hIntEg _ _ (by linarith) (by linarith) (by linarith) (by linarith))
      (hIntEg _ _ (by linarith) (by linarith) (by linarith) (by linarith))
  have hofReal : ((2 * π : ℝ) : ℂ) = 2*(π:ℂ) := by push_cast; ring
  have hRv : IRe - IRg = ICz + -(2*(π:ℂ)*Sp) + IDz := by
    have e1 := hdiffz (-t₁) (-T) (by linarith) (by linarith) (by linarith) (by linarith)
    have e2 := hdiffz (-T) T (by linarith) (by linarith) (by linarith) (by linarith)
    have e3 := hdiffz T t₂ (by linarith) (by linarith) (by linarith) (by linarith)
    rw [hJmid, hofReal] at e2
    rw [hIRedef, hIRgdef, hICzdef, hIDzdef, ← hsp2e, ← hsp1e, ← hsp2g, ← hsp1g]
    linear_combination e1 + e2 + e3
  -- master identity
  have hmaster : ((2 * π : ℝ) : ℂ) * I * (Sp + SC - (y:ℂ))
      = (IAe - IAg) - (IBe - IBg) + I * ICz + I * IDz - I * (ILe - ILg)
        + 2*(π:ℂ)*I * (SC - SR) := by
    rw [hofReal]
    linear_combination (-1 : ℂ) * hchain + hchaing + I * hRv - (2*(π:ℂ)*I) * hres
  clear hchain hchaing hfusion hfusiong hres hdecomp hgtot hgsum hordg_off
    hZgsub hone_mem hZe_re0 hRnze hRnzg hIntEe hIntEg hdiffz hJ hJmid
    hsp1e hsp2e hsp1g hsp2g hRv
  -- edge bounds
  have habs₂ : |t₂| = t₂ := abs_of_pos (by linarith)
  have habs₁ : |(-t₁ : ℝ)| = t₁ := by rw [abs_neg]; exact abs_of_pos (by linarith)
  have hLNT40 : (0:ℝ) < LNT4 := by linarith
  have hδ₀eq : δ₀ * (2000 * LNT4) = 1 := by
    have hne : LNT4 ≠ 0 := ne_of_gt hLNT40
    rw [hδ₀def, ← hLNT4def]
    field_simp
  have hprod : (10000 * LNT4) * (δ₀/5) = 1 := by linear_combination hδ₀eq
  have hgbdgen : ∀ t₀ : ℝ,
      (∀ σ : ℝ, 9/16 ≤ σ → σ ≤ 5/4 → δ₀/5 ≤ ‖gFun ((σ:ℂ) + t₀*I)‖) →
      ∀ x ∈ Set.Icc σ₁ c,
        ‖deriv gFun ((x:ℂ) + t₀*I) / gFun ((x:ℂ) + t₀*I)‖ ≤ 10000 * LNT4 := by
    intro t₀ hlow x hx
    have hx1 : 9/16 ≤ x := by linarith [hx.1]
    have hx2 : x ≤ 5/4 := by linarith [hx.2]
    have hnum : ‖deriv gFun ((x:ℂ) + t₀*I)‖ ≤ 1 :=
      norm_deriv_gFun_le (by rw [re_coord]; exact hx1)
    have hden := hlow x hx1 hx2
    have hδ5 : (0:ℝ) < δ₀/5 := by linarith
    rw [norm_div, div_le_iff₀ (by linarith)]
    linarith [hnum, hprod,
      mul_le_mul_of_nonneg_left hden (by linarith : (0:ℝ) ≤ 10000 * LNT4)]
  have hTopE : ‖IBe‖ ≤ (1000000 * LNT4^2) * (3*y) / (T * Real.log y) := by
    rw [hIBedef]
    have h1 := horiz_edge_le hDD (t₀ := t₂) (B := 1000000 * LNT4^2)
      hy hσ1 hσc.le hc54 hyc3 (by rw [habs₂]; linarith)
      (mul_nonneg (by norm_num) (sq_nonneg LNT4))
      (fun x hx => (htop x (by linarith [hx.1]) (by linarith [hx.2])).1)
      (fun x hx => by
        have h2 := (htop x (by linarith [hx.1]) (by linarith [hx.2])).2
        rwa [hLNT4def])
    calc _ ≤ (1000000 * LNT4^2) * (3*y) / (|t₂| * Real.log y) := h1
      _ ≤ (1000000 * LNT4^2) * (3*y) / (T * Real.log y) := by
          apply div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg LNT4)) (by linarith))
            (mul_pos hT0 hlogy0)
          rw [habs₂]
          nlinarith
  have hBotE : ‖IAe‖ ≤ (1000000 * LNT4^2) * (3*y) / (T * Real.log y) := by
    rw [hIAedef]
    have h1 := horiz_edge_le hDD (t₀ := (-t₁ : ℝ)) (B := 1000000 * LNT4^2)
      hy hσ1 hσc.le hc54 hyc3 (by rw [habs₁]; linarith)
      (mul_nonneg (by norm_num) (sq_nonneg LNT4))
      (fun x hx => (hbot x (by linarith [hx.1]) (by linarith [hx.2])).1)
      (fun x hx => (hbot x (by linarith [hx.1]) (by linarith [hx.2])).2)
    calc _ ≤ (1000000 * LNT4^2) * (3*y) / (|(-t₁:ℝ)| * Real.log y) := h1
      _ ≤ (1000000 * LNT4^2) * (3*y) / (T * Real.log y) := by
          apply div_le_div_of_nonneg_left
            (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg LNT4)) (by linarith))
            (mul_pos hT0 hlogy0)
          rw [habs₁]
          nlinarith
  have hTopG : ‖IBg‖ ≤ (10000 * LNT4) * (3*y) / (T * Real.log y) := by
    rw [hIBgdef]
    have hnz : ∀ x ∈ Set.Icc σ₁ c, gFun ((x:ℂ) + t₂*I) ≠ 0 := by
      intro x hx h0
      have h3 := hg₂ x (by linarith [hx.1]) (by linarith [hx.2])
      rw [h0, norm_zero] at h3
      linarith
    have h1 := horiz_edge_le hDDg (t₀ := t₂) (B := 10000 * LNT4)
      hy hσ1 hσc.le hc54 hyc3 (by rw [habs₂]; linarith) (by linarith)
      hnz (hgbdgen t₂ hg₂)
    calc _ ≤ (10000 * LNT4) * (3*y) / (|t₂| * Real.log y) := h1
      _ ≤ (10000 * LNT4) * (3*y) / (T * Real.log y) := by
          apply div_le_div_of_nonneg_left
            (mul_nonneg (by linarith) (by linarith)) (mul_pos hT0 hlogy0)
          rw [habs₂]
          nlinarith
  have hBotG : ‖IAg‖ ≤ (10000 * LNT4) * (3*y) / (T * Real.log y) := by
    rw [hIAgdef]
    have hnz : ∀ x ∈ Set.Icc σ₁ c, gFun ((x:ℂ) + (-t₁:ℝ)*I) ≠ 0 := by
      intro x hx h0
      have h3 := hg₁ x (by linarith [hx.1]) (by linarith [hx.2])
      rw [h0, norm_zero] at h3
      linarith
    have h1 := horiz_edge_le hDDg (t₀ := (-t₁ : ℝ)) (B := 10000 * LNT4)
      hy hσ1 hσc.le hc54 hyc3 (by rw [habs₁]; linarith) (by linarith)
      hnz (hgbdgen (-t₁ : ℝ) hg₁)
    calc _ ≤ (10000 * LNT4) * (3*y) / (|(-t₁:ℝ)| * Real.log y) := h1
      _ ≤ (10000 * LNT4) * (3*y) / (T * Real.log y) := by
          apply div_le_div_of_nonneg_left
            (mul_nonneg (by linarith) (by linarith)) (mul_pos hT0 hlogy0)
          rw [habs₁]
          nlinarith
  have hEb : ‖ICz‖ ≤ 18 * (y * Real.log y ^ 2 / T) := by
    rw [hICzdef]
    have h := right_extra_le (1 : DirichletCharacter ℂ 1) (y := y) (c := c) (T := T)
      (u := -t₁) (v := -T) hy hcdef hT (by linarith) (by linarith)
      (fun t ht => by
        rw [abs_of_nonpos (by linarith [ht.2] : t ≤ 0)]
        linarith [ht.2])
    rwa [hLmod] at h
  have hEt : ‖IDz‖ ≤ 18 * (y * Real.log y ^ 2 / T) := by
    rw [hIDzdef]
    have h := right_extra_le (1 : DirichletCharacter ℂ 1) (y := y) (c := c) (T := T)
      (u := T) (v := t₂) hy hcdef hT (by linarith) (by linarith)
      (fun t ht => by
        rw [abs_of_nonneg (by linarith [ht.1] : (0:ℝ) ≤ t)]
        exact ht.1)
    rwa [hLmod] at h
  -- left edges
  have hσne : ∀ k ∈ Finset.range M,
      ∀ ρ ∈ diskZeros etaFun (-t₁ + (k:ℝ)/2 + 1/4), ρ.re ≠ σ₁ := by
    intro k hk ρ hρ h
    obtain ⟨hre1, hre2, him⟩ := re_bounds_of_mem_diskZeros hDD hρ
    rcases le_or_gt (1/2 : ℝ) ρ.re with hc1' | hc1'
    · rcases le_or_gt ρ.re (3/2 : ℝ) with hc2' | hc2'
      · have hkM : (k:ℝ) + 1 ≤ M := by
          rw [Finset.mem_range] at hk
          exact_mod_cast hk
        have htk : |(-t₁) + (k:ℝ)/2 + 1/4| ≤ T + 2 := by
          rw [abs_le]
          constructor
          · have hk3 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
            have hk2 : (0:ℝ) ≤ (k:ℝ)/2 := by linarith
            linarith
          · nlinarith
        have himρ : -(T+4) ≤ ρ.im ∧ ρ.im ≤ T+4 := by
          rw [abs_le] at him htk
          constructor <;> linarith [him.1, him.2, htk.1, htk.2]
        have hmem : ρ ∈ boxZeros etaFun (T+4) := by
          rw [mem_boxZeros hDD]
          exact ⟨⟨hc1', hc2'⟩, himρ, ((mem_diskZeros hDD).mp hρ).2⟩
        exact hσre ρ hmem h
      · rw [h] at hc2'
        linarith
    · rw [h] at hc1'
      linarith
  have hnzleft : ∀ t ∈ Set.Icc (-t₁) (-t₁ + (M:ℝ)/2),
      etaFun ((σ₁:ℂ) + t*I) ≠ 0 := by
    intro t ht
    apply hleftnz t
    · linarith [ht.1]
    · linarith [ht.2]
  have hLE : ‖ILe‖ ≤ 20000000 * y^σ₁ * LNT4^2 := by
    rw [hILedef, hLNT4def]
    exact left_edge_le hDD hy1 hT ha' ha0 hM1 hM2 hσ1 hσ2 hσne hnzleft hσH
      (b := t₂) (by linarith) hM3
  have hLG : ‖ILg‖ ≤ 32 * y^σ₁ * LNT := by
    rw [hILgdef]
    have h1 := g_left_edge_le (y := y) (σ₁ := σ₁) hy1 hσ1 hσ2 (u := -t₁) (v := t₂)
      (U := T+1) (by linarith) (by linarith) (by linarith) (by linarith)
    have h2 : (1:ℝ) + (T+1) = (1:ℝ)*(T+2) := by ring
    rw [h2, ← hLNTdef] at h1
    exact h1
  -- shed the heavy definitional baggage
  clear hIAedef hIBedef hIRedef hILedef hIAgdef hIBgdef hIRgdef hILgdef
    hICzdef hIDzdef
  clear_value IAe IBe IRe ILe IAg IBg IRg ILg ICz IDz
  clear hσne hnzleft hgbdgen hprod hδ₀eq hleftnz hσre hσH
  -- zone adjustment
  have hζim : ∀ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T,
      -t₁ < ρ.im ∧ ρ.im < t₂ := by
    intro ρ hρ
    obtain ⟨h1, h2, h3, h4, h5⟩ := mem_zeroFinset.mp hρ
    rw [hLmod] at h5
    have hη : etaFun ρ = 0 := by
      rw [etaFun_eq_mul (by linarith : (0:ℝ) < ρ.re) h4, h5, mul_zero]
    rw [abs_le] at h3
    constructor
    · rcases lt_or_eq_of_le (by linarith [h3.1] : -t₁ ≤ ρ.im) with h | h
      · exact h
      · exfalso
        apply (hbot ρ.re h1 (by linarith)).1
        have h6 : ((ρ.re:ℂ) + (-t₁:ℝ)*I) = ρ := by
          rw [h]
          exact Complex.re_add_im ρ
        rw [h6]
        exact hη
    · rcases lt_or_eq_of_le (by linarith [h3.2] : ρ.im ≤ t₂) with h | h
      · exact h
      · exfalso
        apply (htop ρ.re h1 (by linarith)).1
        have h6 : ((ρ.re:ℂ) + t₂*I) = ρ := by
          rw [← h]
          exact Complex.re_add_im ρ
        rw [h6]
        exact hη
  have hadj : ‖SC - SR‖ ≤ 2700 * y^((5:ℝ)/8) * LNT^2 + 448 * (y * LNTy^2 / T) := by
    set Cf : Finset ℂ := zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T with hCfdef
    set gz : ℂ → ℂ := fun ρ =>
      (analyticOrderNatAt riemannZeta ρ : ℂ) * ((y:ℂ)^ρ/ρ) with hgzdef
    have hSC' : SC = ∑ ρ ∈ Cf, gz ρ := hSCdef
    have hSR' : SR = ∑ ρ ∈ Ze, gz ρ := hSRdef
    rw [hSC', hSR', sum_sub_sum_eq]
    -- `Cf \ Ze`: zeros left of `σ₁`
    have hCR : ‖∑ ρ ∈ Cf \ Ze, gz ρ‖ ≤ 2700 * y^((5:ℝ)/8) * LNT^2 := by
      have hclass : ∀ ρ ∈ Cf \ Ze, ρ.re ≤ σ₁ := by
        intro ρ hρ
        rw [Finset.mem_sdiff] at hρ
        obtain ⟨hC', hnR⟩ := hρ
        obtain ⟨h1, h2, h3, h4, h5⟩ := mem_zeroFinset.mp (hCfdef ▸ hC')
        rw [hLmod] at h5
        obtain ⟨h6, h7⟩ := hζim ρ (hCfdef ▸ hC')
        by_contra hgt
        push Not at hgt
        apply hnR
        rw [hZedef, Finset.mem_filter]
        refine ⟨?_, hgt, by linarith, h6, h7⟩
        rw [mem_boxZeros hDD]
        rw [abs_le] at h3
        refine ⟨⟨h1, by linarith⟩, ⟨by linarith [h3.1], by linarith [h3.2]⟩, ?_⟩
        rw [etaFun_eq_mul (by linarith : (0:ℝ) < ρ.re) h4, h5, mul_zero]
      have hterm : ∀ ρ ∈ Cf \ Ze, ‖gz ρ‖
          ≤ (3 * y^σ₁) * ((analyticOrderNatAt etaFun ρ : ℝ) / (1+|ρ.im|)) := by
        intro ρ hρ
        have hre := hclass ρ hρ
        rw [Finset.mem_sdiff] at hρ
        obtain ⟨h1, h2, h3, h4, h5⟩ := mem_zeroFinset.mp (hCfdef ▸ hρ.1)
        have hordle : (analyticOrderNatAt riemannZeta ρ : ℝ)
            ≤ (analyticOrderNatAt etaFun ρ : ℝ) := by
          exact_mod_cast analyticOrderNatAt_zeta_le_etaFun
            (by linarith : (0:ℝ) < ρ.re) h4
        rw [hgzdef]
        show ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ((y:ℂ)^ρ/ρ)‖ ≤ _
        rw [norm_mul, norm_div, Complex.norm_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos hy0]
        have hρhalf : (1/2:ℝ) ≤ ‖ρ‖ := by
          have h6 := Complex.abs_re_le_norm ρ
          have h7 : (1/2:ℝ) ≤ |ρ.re| := by
            rw [abs_of_nonneg (by linarith)]
            exact h1
          linarith
        have hρ0 : (0:ℝ) < ‖ρ‖ := by linarith
        have hpos : (0:ℝ) < 1 + |ρ.im| := by
          have habsim := abs_nonneg ρ.im
          linarith
        have hyre : y ^ ρ.re ≤ y ^ σ₁ :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hre
        have hnorm3 : 1 + |ρ.im| ≤ 3 * ‖ρ‖ := by
          have ha2 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
          linarith
        have hyσ : (0:ℝ) ≤ y^σ₁ := Real.rpow_nonneg hy0.le σ₁
        have hordnn : (0:ℝ) ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) :=
          Nat.cast_nonneg _
        calc (analyticOrderNatAt riemannZeta ρ : ℝ) * (y ^ ρ.re / ‖ρ‖)
            ≤ (analyticOrderNatAt riemannZeta ρ : ℝ)
              * (3 * y ^ σ₁ / (1+|ρ.im|)) := by
              apply mul_le_mul_of_nonneg_left _ hordnn
              rw [div_le_div_iff₀ hρ0 hpos]
              nlinarith
          _ = ((analyticOrderNatAt riemannZeta ρ : ℝ) * (3 * y ^ σ₁))
              / (1+|ρ.im|) := by ring
          _ ≤ ((3 * y^σ₁) * (analyticOrderNatAt etaFun ρ : ℝ)) / (1+|ρ.im|) := by
              apply div_le_div_right_of_pos hpos
              nlinarith
          _ = (3 * y^σ₁) * ((analyticOrderNatAt etaFun ρ : ℝ) / (1+|ρ.im|)) := by
              ring
      have hweight := weight_sum_le hDD (U := T) hT (Z := Cf \ Ze)
        (by
          intro ρ hρ
          rw [Finset.mem_sdiff] at hρ
          have hm := mem_zeroFinset.mp (hCfdef ▸ hρ.1)
          exact ⟨hm.1, by linarith [hm.2.1], hm.2.2.1⟩)
      calc ‖∑ ρ ∈ Cf \ Ze, gz ρ‖ ≤ ∑ ρ ∈ Cf \ Ze, ‖gz ρ‖ := norm_sum_le _ _
        _ ≤ ∑ ρ ∈ Cf \ Ze, (3 * y^σ₁) * ((analyticOrderNatAt etaFun ρ : ℝ)
            / (1+|ρ.im|)) := Finset.sum_le_sum hterm
        _ = (3 * y^σ₁) * ∑ ρ ∈ Cf \ Ze, ((analyticOrderNatAt etaFun ρ : ℝ)
            / (1+|ρ.im|)) := by rw [Finset.mul_sum]
        _ ≤ (3 * y^σ₁) * (900 * Real.log ((1:ℝ) * (T + 2))^2) := by
            refine mul_le_mul_of_nonneg_left hweight ?_
            have h9 := Real.rpow_nonneg hy0.le σ₁
            linarith
        _ ≤ 2700 * y^((5:ℝ)/8) * LNT^2 := by
            rw [← hLNTdef]
            have h1 : y ^ σ₁ ≤ y ^ ((5:ℝ)/8) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) hσ2
            nlinarith [Real.rpow_nonneg hy0.le σ₁, sq_nonneg LNT,
              Real.rpow_nonneg hy0.le ((5:ℝ)/8)]
    -- `Ze \ Cf`: the band `T < |Im| ≤ T+1` (spurious `g`-zeros carry no `ζ` order)
    have hRC : ‖∑ ρ ∈ Ze \ Cf, gz ρ‖ ≤ 448 * (y * LNTy^2 / T) := by
      set Zb : Finset ℂ := (Ze \ Cf).filter (fun ρ => riemannZeta ρ = 0) with hZbdef
      have hsub : Zb ⊆ Ze \ Cf := Finset.filter_subset _ _
      have hvanish : ∀ ρ ∈ Ze \ Cf, ρ ∉ Zb → gz ρ = 0 := by
        intro ρ hρ hnot
        have hz : riemannZeta ρ ≠ 0 := by
          intro h0
          exact hnot (by rw [hZbdef, Finset.mem_filter]; exact ⟨hρ, h0⟩)
        have hord0 : analyticOrderNatAt riemannZeta ρ = 0 := by
          rw [analyticOrderNatAt, analyticOrderAt_eq_zero.mpr (Or.inr hz)]
          rfl
        rw [hgzdef]
        show (analyticOrderNatAt riemannZeta ρ : ℂ) * ((y:ℂ)^ρ/ρ) = 0
        rw [hord0]
        norm_num
      rw [← Finset.sum_subset hsub hvanish]
      have hclass : ∀ ρ ∈ Zb, ((1/2 ≤ ρ.re ∧ ρ.re ≤ 3/2)
          ∧ (T < |ρ.im| ∧ |ρ.im| ≤ T + 1)) ∧ ρ.re ≤ 1 ∧ ρ ≠ 1 := by
        intro ρ hρ
        have hρ' := hρ
        rw [hZbdef, Finset.mem_filter, Finset.mem_sdiff] at hρ'
        obtain ⟨⟨hE, hnC⟩, hzz⟩ := hρ'
        have hne1 := hZe_ne1 ρ hE
        have hE' := hE
        rw [hZedef, Finset.mem_filter] at hE'
        obtain ⟨hbox, hf1, hf2, hf3, hf4⟩ := hE'
        obtain ⟨⟨hr1, hr2⟩, -, hηz⟩ := (mem_boxZeros hDD).mp hbox
        have hre1 : ρ.re ≤ 1 := re_le_one_of_zero hDD hηz
        have himT : T < |ρ.im| := by
          by_contra hle
          push Not at hle
          apply hnC
          rw [hCfdef, mem_zeroFinset, hLmod]
          exact ⟨by linarith, hre1, hle, hne1, hzz⟩
        have himT1 : |ρ.im| ≤ T + 1 := by
          rw [abs_le]
          exact ⟨by linarith, by linarith⟩
        exact ⟨⟨⟨hr1, hr2⟩, himT, himT1⟩, hre1, hne1⟩
      have hterm : ∀ ρ ∈ Zb, ‖gz ρ‖
          ≤ (y/T) * (analyticOrderNatAt etaFun ρ : ℝ) := by
        intro ρ hρ
        obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩ := hclass ρ hρ
        have hordle : (analyticOrderNatAt riemannZeta ρ : ℝ)
            ≤ (analyticOrderNatAt etaFun ρ : ℝ) := by
          exact_mod_cast analyticOrderNatAt_zeta_le_etaFun
            (by linarith : (0:ℝ) < ρ.re) h6
        rw [hgzdef]
        show ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * ((y:ℂ)^ρ/ρ)‖ ≤ _
        rw [norm_mul, norm_div, Complex.norm_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos hy0]
        have hρT : T ≤ ‖ρ‖ := le_trans h3.le (Complex.abs_im_le_norm ρ)
        have hyre : y ^ ρ.re ≤ y := by
          calc y ^ ρ.re ≤ y ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by linarith) h5
            _ = y := Real.rpow_one y
        have hordnn : (0:ℝ) ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) :=
          Nat.cast_nonneg _
        have hyT : (0:ℝ) < y / T := div_pos hy0 hT0
        calc (analyticOrderNatAt riemannZeta ρ : ℝ) * (y ^ ρ.re / ‖ρ‖)
            ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) * (y / T) := by
              apply mul_le_mul_of_nonneg_left _ hordnn
              exact div_le_div₀ (by linarith) hyre hT0 hρT
          _ ≤ (y/T) * (analyticOrderNatAt etaFun ρ : ℝ) := by
              nlinarith [hordle, hyT]
      have hmass := band_mass_le hDD hT (Z := Zb)
        (fun ρ hρ => by
          obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, -, -⟩ := hclass ρ hρ
          exact ⟨h1, h2, h3, h4⟩)
      calc ‖∑ ρ ∈ Zb, gz ρ‖ ≤ ∑ ρ ∈ Zb, ‖gz ρ‖ := norm_sum_le _ _
        _ ≤ ∑ ρ ∈ Zb, (y/T) * (analyticOrderNatAt etaFun ρ : ℝ) :=
            Finset.sum_le_sum hterm
        _ = (y/T) * ∑ ρ ∈ Zb, (analyticOrderNatAt etaFun ρ : ℝ) := by
            rw [Finset.mul_sum]
        _ ≤ (y/T) * (224 * LNT4) := by
            apply mul_le_mul_of_nonneg_left _ (div_pos hy0 hT0).le
            rw [hLNT4def]
            exact hmass
        _ ≤ 448 * (y * LNTy^2 / T) := by
            have h1 : LNT4 ≤ LNTy := hLNT4y
            have h2 : LNTy ≤ LNTy^2 := by nlinarith
            rw [div_mul_eq_mul_div,
              show 448 * (y * LNTy^2 / T) = (448 * (y * LNTy^2)) / T by ring]
            apply div_le_div_right_of_pos hT0
            nlinarith
    calc ‖(∑ ρ ∈ Cf \ Ze, gz ρ) - ∑ ρ ∈ Ze \ Cf, gz ρ‖
        ≤ ‖∑ ρ ∈ Cf \ Ze, gz ρ‖ + ‖∑ ρ ∈ Ze \ Cf, gz ρ‖ := norm_sub_le _ _
      _ ≤ 2700 * y^((5:ℝ)/8) * LNT^2 + 448 * (y * LNTy^2 / T) :=
          add_le_add hCR hRC
  -- final norm bound
  have hπ3 : (3:ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hπnn : (0:ℝ) ≤ 2*π := by linarith
  have hnormfac : ‖((2 * π : ℝ) : ℂ) * I * (Sp + SC - (y:ℂ))‖
      = 2*π*‖Sp + SC - (y:ℂ)‖ := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hπnn]
  have hrhs : ‖((2 * π : ℝ) : ℂ) * I * (Sp + SC - (y:ℂ))‖
      ≤ ((1000000 * LNT4^2) * (3*y) / (T * Real.log y)
          + (10000 * LNT4) * (3*y) / (T * Real.log y))
        + ((1000000 * LNT4^2) * (3*y) / (T * Real.log y)
          + (10000 * LNT4) * (3*y) / (T * Real.log y))
        + (18 * (y * Real.log y ^ 2 / T))
        + (18 * (y * Real.log y ^ 2 / T))
        + (20000000 * y^σ₁ * LNT4^2 + 32 * y^σ₁ * LNT)
        + 2*π*(2700 * y^((5:ℝ)/8) * LNT^2 + 448 * (y * LNTy^2 / T)) := by
    rw [hmaster]
    have h2πI : ‖2*(π:ℂ)*I * (SC - SR)‖ = 2*π*‖SC - SR‖ := by
      rw [show 2*(π:ℂ)*I * (SC - SR) = I * ((2*(π:ℂ)) * (SC - SR)) by ring]
      rw [norm_mul, Complex.norm_I, one_mul, norm_mul]
      have hπnorm : ‖(2*(π:ℂ))‖ = 2*π := by
        rw [show (2*(π:ℂ)) = ((2*π : ℝ) : ℂ) by push_cast; ring]
        rw [Complex.norm_real, Real.norm_of_nonneg hπnn]
      rw [hπnorm]
    have htri := norm_edge_combo (A := IAe - IAg) (B := IBe - IBg)
      (C := ICz) (D := IDz) (E := ILe - ILg) (G := 2*(π:ℂ)*I * (SC - SR))
    have hAb : ‖IAe - IAg‖ ≤ (1000000 * LNT4^2) * (3*y) / (T * Real.log y)
        + (10000 * LNT4) * (3*y) / (T * Real.log y) :=
      le_trans (norm_sub_le _ _) (add_le_add hBotE hBotG)
    have hBb : ‖IBe - IBg‖ ≤ (1000000 * LNT4^2) * (3*y) / (T * Real.log y)
        + (10000 * LNT4) * (3*y) / (T * Real.log y) :=
      le_trans (norm_sub_le _ _) (add_le_add hTopE hTopG)
    have hEb' : ‖ILe - ILg‖ ≤ 20000000 * y^σ₁ * LNT4^2 + 32 * y^σ₁ * LNT :=
      le_trans (norm_sub_le _ _) (add_le_add hLE hLG)
    have hGb : ‖2*(π:ℂ)*I * (SC - SR)‖
        ≤ 2*π*(2700 * y^((5:ℝ)/8) * LNT^2 + 448 * (y * LNTy^2 / T)) := by
      rw [h2πI]
      exact mul_le_mul_of_nonneg_left hadj hπnn
    calc _ ≤ _ := htri
      _ ≤ _ := by
        have hsum := add_le_add (add_le_add (add_le_add (add_le_add
          (add_le_add hAb hBb) hEb) hEt) hEb') hGb
        linarith [hsum]
  rw [hnormfac] at hrhs
  exact zeta_final_numeric hy hT hlogy hLNT1 hLNT41 hLNTy1 hLNT4le hLNT4y
    hlogyle hσ2 (norm_nonneg _) hrhs

end AssemblyZeta

/-! ### The combined explicit formula -/

section Combined

open scoped Classical

set_option maxHeartbeats 1000000 in
/-- **The truncated explicit formula** at the frozen ledger contract
(`routez/Z0a-ledger.md` §2/§7), with `C₅ = 10^12`.  Covers every character
with `χ ≠ 1` and the Riemann zeta case `N = 1`. -/
theorem explicit_formula {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1 ∨ N = 1) {y T : ℝ} (hy : 100 ≤ y) (hT : 2 ≤ T)
    (hyN : (N : ℝ) ≤ y) :
    ‖psiChi χ y - (if χ = 1 then (y : ℂ) else 0)
        + ∑ ρ ∈ zeroFinset χ (1/2) T,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
              * ((y:ℂ)^ρ/ρ)‖
      ≤ 10 ^ 12 * (y * Real.log ((N:ℝ)*T*y)^2 / T
          + y^((5:ℝ)/8) * Real.log ((N:ℝ)*(T+2))^2
          + Real.log ((N:ℝ)*T*y)^2) := by
  have hy0 : (0:ℝ) < y := by linarith
  have hT0 : (0:ℝ) < T := by linarith
  rcases hχ with hne | hN
  · -- nontrivial character: the `if` is vacuous
    have hif : (if χ = 1 then (y : ℂ) else 0) = 0 := if_neg hne
    rw [hif, sub_zero]
    have hN1 : (1:ℝ) ≤ N := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    have hp1 : (0:ℝ) ≤ y * Real.log ((N:ℝ)*T*y)^2 / T := by positivity
    have hp2 : (0:ℝ) ≤ y^((5:ℝ)/8) * Real.log ((N:ℝ)*(T+2))^2 := by positivity
    have hp3 : (0:ℝ) ≤ Real.log ((N:ℝ)*T*y)^2 := sq_nonneg _
    refine le_trans (explicit_formula_ne_one χ hne hy hT) ?_
    have hpow : (10:ℝ)^12 = 1000000000000 := by norm_num
    rw [hpow]
    linarith [hp1, hp2, hp3]
  · -- the Riemann zeta case
    subst hN
    have hχ1 : χ = 1 := DirichletCharacter.level_one χ
    subst hχ1
    have hif : (if (1 : DirichletCharacter ℂ 1) = 1 then (y : ℂ) else 0) = (y:ℂ) :=
      if_pos rfl
    rw [hif, Nat.cast_one, DirichletCharacter.LFunction_modOne_eq]
    have h1 := perronSum_sub_psiChi_le (1 : DirichletCharacter ℂ 1) hy hT
    have h2 := contour_zeta hy hT
    simp only [one_mul] at h2 ⊢
    have hkey : psiChi (1 : DirichletCharacter ℂ 1) y - (y:ℂ)
        + ∑ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T,
            (analyticOrderNatAt riemannZeta ρ : ℂ) * ((y:ℂ)^ρ/ρ)
        = -(perronSum (1 : DirichletCharacter ℂ 1) y (1 + 1/Real.log y) T
              - psiChi (1 : DirichletCharacter ℂ 1) y)
          + (perronSum (1 : DirichletCharacter ℂ 1) y (1 + 1/Real.log y) T
            + (∑ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T,
                (analyticOrderNatAt riemannZeta ρ : ℂ) * ((y:ℂ)^ρ/ρ))
            - (y:ℂ)) := by
      ring
    have hp1 : (0:ℝ) ≤ y * Real.log (T*y)^2 / T := by positivity
    have hp2 : (0:ℝ) ≤ y^((5:ℝ)/8) * Real.log (T+2)^2 := by positivity
    have hp3 : (0:ℝ) ≤ Real.log (T*y)^2 := sq_nonneg _
    calc ‖psiChi (1 : DirichletCharacter ℂ 1) y - (y:ℂ)
          + ∑ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T,
              (analyticOrderNatAt riemannZeta ρ : ℂ) * ((y:ℂ)^ρ/ρ)‖
        ≤ ‖perronSum (1 : DirichletCharacter ℂ 1) y (1 + 1/Real.log y) T
              - psiChi (1 : DirichletCharacter ℂ 1) y‖
          + ‖perronSum (1 : DirichletCharacter ℂ 1) y (1 + 1/Real.log y) T
            + (∑ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T,
                (analyticOrderNatAt riemannZeta ρ : ℂ) * ((y:ℂ)^ρ/ρ))
            - (y:ℂ)‖ := by
          rw [hkey]
          calc ‖_ + _‖
              ≤ ‖-(perronSum (1 : DirichletCharacter ℂ 1) y (1 + 1/Real.log y) T
                    - psiChi (1 : DirichletCharacter ℂ 1) y)‖
                + ‖perronSum (1 : DirichletCharacter ℂ 1) y (1 + 1/Real.log y) T
                  + (∑ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T,
                      (analyticOrderNatAt riemannZeta ρ : ℂ) * ((y:ℂ)^ρ/ρ))
                  - (y:ℂ)‖ := norm_add_le _ _
            _ = _ := by rw [norm_neg]
      _ ≤ (200 * (y * Real.log (T*y)^2 / T) + 30 * Real.log (T*y)^2)
          + 1000000000 * (y * Real.log (T*y)^2 / T
              + y^((5:ℝ)/8) * Real.log (T+2)^2) := add_le_add h1 h2
      _ ≤ 10 ^ 12 * (y * Real.log (T*y)^2 / T
            + y^((5:ℝ)/8) * Real.log (T+2)^2
            + Real.log (T*y)^2) := by
          have hpow : (10:ℝ)^12 = 1000000000000 := by norm_num
          rw [hpow]
          linarith [hp1, hp2, hp3]

end Combined

end EF

end Carmichael
