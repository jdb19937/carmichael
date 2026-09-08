/-
Route Z, sortie L1 (tail): the logged zero detector — truncation, dyadic blocks, Taylor
split, the LV1-shaped detector lemma, and the class-II mean square
(routez/Z6-logged.md §2 Lemmas 2.3–2.8, §3.3 Lemmas 3.6–3.8, §6.1 items L1.c–L1.f;
routez/Z6-logged-audit.md F1, F3, F7).  Imports the compiled `LoggedParams`
(`Ypar`, `Nmax`, `Jpar`, `EctrHalf`, `coeffJK`, `blockRange`), `DetectionShiftHalf`
(L1.a, L1.b, the `R = 1` collapse) and `LargeValues` (the discrete mean value).

No `sorry`, no `axiom`, no `native_decide` in this file.

STATEMENTS (namespace `Carmichael.LoggedDetector`):

 * L1.c  `norm_Fdet_sub_truncation_le χ hD hL hβ hβ1`
     (`1 < D`, `40 ≤ log D`, `39/50 ≤ Re ρ ≤ 1`):
     `‖Fdet χ D (2D) 1 (Ypar D) ρ − ∑_{n ∈ Icc 1 (Nmax D)} [D < n]·a(n)e^{−n/Y}χ(n)n^{−ρ}‖ ≤ 1/8`.
 * L1.e  `detector_large_value χ hD hL hσ hσ1 hβ hβ1 hρ1 hLρ`
     (`1 < D`, `40 ≤ log D`, `39/50 ≤ σ ≤ 1`, `σ ≤ Re ρ ≤ 1`, `χ = 1 → log D ≤ |Im ρ|`,
     `L(ρ,χ) = 0`):
     `1/4 ≤ ‖EctrHalf χ D (Ypar D) ρ‖ ∨ ∃ j < Jpar D, ∃ k ≤ Jpar D,
        1/(8·J·(J+1)) ≤ ‖∑_{n ∈ blockRange D j} coeffJK D σ j k n · χ(n) · exp((−log n·Im ρ) i)‖`
     (audit F1 range `blockRange D j = Icc 1 ⌈2^{j+1}D⌉₊`, audit F3 casts).
 * L1.f  `sum_sq_EctrHalf_le d hD ht hL hσ hσ1 s chi ρ hρ hsep`
     (`D = d(t+2)`, `2 ≤ t`, `40 ≤ log D`, `39/50 ≤ σ ≤ 1`, family `s` with
     `σ ≤ Re ρ_r ≤ 1`, `|Im ρ_r| ≤ t`, `1`-spaced per character):
     `∑_{r ∈ s} ‖EctrHalf (chi r) D (Ypar D) (ρ r)‖² ≤ 10²²·C_τ²·C_Γ²·log⁵D·D^{(151/50)(1−σ)}`.
     The points need not be zeros.

DELIVERED (in order):

§0  Parameter facts (`Ypar_pos`, `one_le_Ypar`, `le_Ypar`, `four_le_Ypar`, `log_le_Jpar`,
    `Jpar_le`, `one_le_Jpar`, `Jpar_le_two_mul`, `le_Nmax`, `Nmax_le`) and the numeric
    clauses at `𝓛 ≥ 40` as standalone real lemmas (no `rpow` inside `norm_num`/`nlinarith`):
    `numeric_tail` (`128 ≤ e^{0.98x}`), `numeric_blocks` (`9x ≤ e^{0.1831x}`),
    `numeric_taylor` (`64x² ≤ e^{0.961x}`); L1.b's `pole_threshold_numeric` is consumed
    from `DetectionShiftHalf`.
§1  Elementary: `abs_bvA_le_card_divisors` (`|a(n)| ≤ τ(n)`), `sum_card_divisors_eq`
    (`∑_{n≤x} τ(n) = ∑_{d≤x} ⌊x/d⌋`), `sum_card_divisors_le` (`≤ x(1 + log x)`, via
    `harmonic_le_one_add_log`), `sum_card_divisors_sq_le` (`∑_{n≤x} τ(n)² ≤ x(1 + log x)³`,
    the common-divisor double sum `∑_{a,b} ⌊x/lcm(a,b)⌋ ≤ x·∑_g g·(H/g)²`; for L2's
    coefficient mass, not consumed here), `natCast_cpow_neg_eq`
    (`n^{−ρ} = n^{−Re ρ}·exp((−log n·Im ρ) i)`).
§2  Lemma 2.3 `norm_LFunction_half_le` (I1 at `Re s = 1/2` + I9(d):
    `‖L(ρ + c + iu, χ)‖ ≤ 6·10⁵·C_τ·D^{201/800}·log D·(1+|u|)²` for `Re ρ + c = 1/2`,
    `N(|Im ρ|+2) ≤ D`, `2 ≤ log D`; constant `6·10⁵` in place of the blueprint's `10⁶`);
    `taylor_remainder_le` (`Real.exp_bound`: `|e^x − ∑_{k≤J} x^k/k!| ≤ (1/5)^{J+1}` for
    `|x| ≤ 1/6`, `J ≥ 3`).
§3  L1.c: `truncTerm`, `Fdet_eq_tsum_truncTerm`, `summable_truncTerm`, `norm_truncTerm_le`
    (`≤ n e^{−n/Y}`), `half_le_one_sub_exp_neg`, `tail_numeric` (`16Y²e^{−4 log D} ≤ 1/8`),
    `norm_Fdet_sub_truncation_le` (tail beyond `Nmax`: `Summable.sum_add_tsum_nat_add`,
    majorant `m·q^m·D^{−4}` with `q = e^{−1/(2Y)}`, `tsum_coe_mul_geometric_of_norm_lt_one`,
    `1/(1−q)² ≤ 16Y²`).
§4  Lemma 2.5: `Nmax_le_two_pow_Jpar_mul` (`Nmax D ≤ 2^{Jpar D}·D`), `exists_block`,
    `block_unique`; `blockSum` (`S_j`), `taylorSum` (`T_{j,k}` over `Icc 1 (Nmax D)`),
    `taylorRem`, `remTerm`, `remSum` (`R_j`); `sum_truncTerm_eq_sum_blockSum`
    (`S = ∑_{j<J} S_j`); Lemma 2.7: `rpow_neg_eq_taylor` (the real identity
    `n^{−β} = N^{−δ} n^{−σ}(∑_{k≤J} δ^k(−log(n/N))^k/k! + r_n)`), `blockSum_eq_taylor`
    (`S_j = N_j^{−δ}(∑_k (δ^k/k!) T_{j,k} + R_j)`), `norm_blockSum_le`
    (`‖S_j‖ ≤ ∑_k ‖T_{j,k}‖ + ‖R_j‖`), `abs_taylorRem_le` (`|r_n| ≤ (1/5)^{J+1}`),
    `norm_remTerm_le`, `rem_numeric`, `norm_remSum_le` (`‖R_j‖ ≤ 1/(8J)`).
§5  Pigeonholes `exists_block_large` (`‖S‖ ≥ 1/4 → ∃ j, ‖S_j‖ ≥ 1/(4J)`),
    `exists_taylor_index_large` (`‖S_j‖ ≥ 1/(4J) → ∃ k ≤ J, ‖T_{j,k}‖ ≥ 1/(8J(J+1))`),
    `taylorSum_eq_blockRange` (audit F1: both ranges contain the support of `coeffJK`),
    L1.e `detector_large_value` (`detection_identity_half` + `norm_Epole_le_of_height`
    + L1.c + `e^{−1/Y} ≥ 3/4`: `‖E_ctr‖ < 1/4 ⇒ ‖F‖ ≥ 3/8 ⇒ ‖S‖ ≥ 1/4`).
§6  L1.f (audit F7 route, no `(1+|u|)⁴` moment): `integrable_exp_neg_abs_mul`,
    `integral_exp_neg_abs_mul` (`∫ e^{−a|u|} = 2/a`), `weight_sq_le`
    (`(1+x)²e^{−x} ≤ 8e^{−x/2}`), `weight_lin_le` (`(3+x)e^{−x/2} ≤ 4e^{−x/4}`),
    `continuous_Mr_line`, `norm_Mr_one_le_card` (`‖M‖ ≤ ⌊z₂⌋₊`), `sq_integral_weight_le`
    (elementary Cauchy–Schwarz `(∫ w f)² ≤ 4∫ w f²`, `w = e^{−|u|/2}`), `Kcls`
    (`K = 8·201·C_Γ·6·10⁵·C_τ·D^{201/800}·log D·Y^{1/2−σ}`), `norm_ectrInt_half_le`
    (Lemma 3.6 pointwise), `integrable_weight_norm_Mr_pow`, `sq_norm_EctrHalf_le`
    (`‖E_ctr‖² ≤ (K/2π)²·4∫ w‖M‖²`), `mollifier_mass_le` (`G_M ≤ 2 log³D`),
    `classII_exponent` (`D^{201/400}·D·Y^{1−2σ} ≤ D^{(151/50)(1−σ)}`), `sum_sq_norm_Mr_le`
    (Lemma 3.7 at fixed `u`: `mean_value_chars_discrete_family` with `T = t + |u|`, point
    sets `{Im ρ_r + u}` per character, coefficients `λ_δ δ^{−1/2}`), `sum_sq_EctrHalf_le`.

CONSTANTS.  L1.f: `∑ ≤ (K/2π)²·4·12800·D·log³D` with `K² = 964800000²·C_Γ²C_τ²·D^{201/400}
·log²D·Y^{1−2σ}`, `(2π)² ≥ 36`, i.e. `964800000²·51200/36 ≈ 1.32·10²¹ ≤ 10²²` (frozen
constant met with margin `7.5`).  Numeric clauses: tail `16D^{−49/50} ≤ 1/8`, blocks
`9𝓛 ≤ D^{log 2 − 51/100}`, Taylor `64𝓛² ≤ D^{961/1000}` (from `‖R_j‖ ≤ 4𝓛D^{17/40}/5^{J+1}`,
`5^{J+1} ≥ D^{log 4}`), all discharged at `𝓛 = 40` and monotone.

DELTAS VS. THE BLUEPRINT / AUDIT (all reported):
 * L1.c and L1.e carry the extra hypothesis `hD : 1 < D`: `40 ≤ Real.log D` alone does not
   exclude `D < 0` (`Real.log_neg_eq_log`), and with `D < 0` the parameters `Ypar D`
   (`rpow` of a negative base) are meaningless.  L2 always has `D = d(t+2) ≥ 4`.
 * L1.c's hypotheses are `39/50 ≤ Re ρ ≤ 1` (the audit's `0 ≤ Re ρ` suffices for the proof;
   the stronger form matches L1.e's call site).  `Re ρ ≤ 1` is unused.
 * Lemma 2.3 is stated on the line `Re ρ + c = 1/2` with constant `6·10⁵` (the blueprint
   says `10⁶`); the Taylor remainder is `(1/5)^{J+1}` (blueprint `(0.2)^{J+1}`, same).
 * The Taylor components `T_{j,k}` are defined over `Icc 1 (Nmax D)` (`taylorSum`) and
   converted to the frozen `blockRange D j` range in `taylorSum_eq_blockRange`.
 * L1.f uses the audit's F7 weighting (`e^{−|u|/2}`, Cauchy–Schwarz in the elementary
   parametric AM–GM form, no `MemLp`/Hölder), so no `integral_Gamma_pow4_le` is delivered.
 * `sum_card_divisors_sq_le` has the blueprint's bound `x(1 + log x)³` exactly.

MATHLIB / PIN NOTES: `add_le_add_right h a : a + b ≤ a + c` (left-addition in this pin;
use `add_le_add h le_rfl`); `continuous_finset_sum` is deprecated for `continuous_finsetSum`;
`Set.mem_setOf_eq` for `Set.mem_ofPred_eq`; `GammaStrip.line_ptwise`,
`integrable_exp_neg_abs_half` are `private` (re-proved here); `λ` is a reserved token;
`rw [div_eq_mul_inv]` hits the exponent `961/1000` first (use `ring`); `rw [hpow]` rewrites
every occurrence (split the product first); `mean_value_chars_discrete_family` lives in
`Carmichael.LargeValues`, which is not in `DetectionShiftHalf`'s import closure.
-/
import Carmichael.DetectionShiftHalf
import Carmichael.LargeValues

set_option autoImplicit false

namespace Carmichael

open Complex MeasureTheory
open scoped Real

namespace LoggedDetector

open Detector DetectionShift

/-! ## §0.  Parameter facts and the numeric clauses at `𝓛 ≥ 40` -/

lemma Ypar_pos {D : ℝ} (hD : 0 < D) : 0 < Ypar D := Real.rpow_pos_of_pos hD _

lemma one_le_Ypar {D : ℝ} (hD : 1 ≤ D) : 1 ≤ Ypar D := Real.one_le_rpow hD (by norm_num)

lemma le_Ypar {D : ℝ} (hD : 1 ≤ D) : D ≤ Ypar D := by
  rw [Ypar]
  calc D = D ^ (1 : ℝ) := (Real.rpow_one D).symm
    _ ≤ D ^ (151/100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD (by norm_num)

/-- `40 ≤ log D` with `0 < D` gives `e^{40} ≤ D`. -/
lemma exp_forty_le {D : ℝ} (hD : 0 < D) (hL : 40 ≤ Real.log D) : Real.exp 40 ≤ D := by
  calc Real.exp 40 ≤ Real.exp (Real.log D) := Real.exp_le_exp.mpr hL
    _ = D := Real.exp_log hD

lemma four_le_of_log {D : ℝ} (hD : 0 < D) (hL : 40 ≤ Real.log D) : 4 ≤ D := by
  have h1 := exp_forty_le hD hL
  have h2 : Real.exp 2 ≤ Real.exp 40 := Real.exp_le_exp.mpr (by norm_num)
  have h3 := Real.quadratic_le_exp_of_nonneg (x := 2) (by norm_num)
  linarith

lemma four_le_Ypar {D : ℝ} (hD : 0 < D) (hL : 40 ≤ Real.log D) : 4 ≤ Ypar D :=
  (four_le_of_log hD hL).trans (le_Ypar (by linarith [four_le_of_log hD hL]))

lemma log_le_Jpar (D : ℝ) : Real.log D ≤ Jpar D := Nat.le_ceil _

lemma Jpar_le {D : ℝ} (hL : 0 ≤ Real.log D) : (Jpar D : ℝ) ≤ Real.log D + 1 :=
  (Nat.ceil_lt_add_one hL).le

lemma one_le_Jpar {D : ℝ} (hL : 1 ≤ Real.log D) : 1 ≤ Jpar D := by
  have := log_le_Jpar D
  exact_mod_cast (show (1 : ℝ) ≤ Jpar D by linarith)

lemma Jpar_le_two_mul {D : ℝ} (hL : 1 ≤ Real.log D) : (Jpar D : ℝ) ≤ 2 * Real.log D := by
  have := Jpar_le (by linarith : 0 ≤ Real.log D)
  linarith

lemma le_Nmax {D : ℝ} : 8 * Ypar D * Real.log D ≤ Nmax D := Nat.le_ceil _

lemma Nmax_le {D : ℝ} (hD : 0 < D) (hL : 0 ≤ Real.log D) :
    (Nmax D : ℝ) ≤ 8 * Ypar D * Real.log D + 1 :=
  (Nat.ceil_lt_add_one (by have := Ypar_pos hD; positivity)).le

/-- Numeric clause (ii), tail: `128 ≤ e^{0.98 x}` for `x ≥ 40`. -/
lemma numeric_tail {x : ℝ} (hx : 40 ≤ x) : (128 : ℝ) ≤ Real.exp ((98/100 : ℝ) * x) := by
  have h1 : Real.exp 5 ≤ Real.exp ((98/100 : ℝ) * x) := Real.exp_le_exp.mpr (by linarith)
  have h2 : (2.7 : ℝ) ^ 5 ≤ Real.exp 5 := by
    have := Real.exp_one_gt_d9
    calc (2.7 : ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
      _ = Real.exp 5 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : (128 : ℝ) ≤ 2.7 ^ 5 := by norm_num
  linarith

/-- Numeric clause (iii), block coverage: `9 x ≤ e^{0.1831 x}` for `x ≥ 40`. -/
lemma numeric_blocks {x : ℝ} (hx : 40 ≤ x) : 9 * x ≤ Real.exp ((1831/10000 : ℝ) * x) := by
  have h1 : Real.exp ((1831/10000 : ℝ) * x)
      = Real.exp 7 * Real.exp ((1831/10000 : ℝ) * x - 7) := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : (2.7 : ℝ) ^ 7 ≤ Real.exp 7 := by
    have := Real.exp_one_gt_d9
    calc (2.7 : ℝ) ^ 7 ≤ (Real.exp 1) ^ 7 := pow_le_pow_left₀ (by norm_num) (by linarith) 7
      _ = Real.exp 7 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : ((1831/10000 : ℝ) * x - 7) + 1 ≤ Real.exp ((1831/10000 : ℝ) * x - 7) :=
    Real.add_one_le_exp _
  have h4 : (0 : ℝ) ≤ (1831/10000 : ℝ) * x - 7 + 1 := by linarith
  rw [h1]
  calc 9 * x ≤ (2.7 : ℝ) ^ 7 * ((1831/10000 : ℝ) * x - 7 + 1) := by norm_num; nlinarith
    _ ≤ Real.exp 7 * Real.exp ((1831/10000 : ℝ) * x - 7) :=
        mul_le_mul h2 h3 h4 (Real.exp_pos _).le

/-- Numeric clause (iv), Taylor remainder: `64 x² ≤ e^{0.961 x}` for `x ≥ 40`. -/
lemma numeric_taylor {x : ℝ} (hx : 40 ≤ x) : 64 * x ^ 2 ≤ Real.exp ((961/1000 : ℝ) * x) := by
  have h := Real.pow_div_factorial_le_exp (x := (961/1000 : ℝ) * x) (by linarith) 6
  have hx4 : (40 : ℝ) ^ 4 ≤ x ^ 4 := pow_le_pow_left₀ (by norm_num) hx 4
  have hx6 : (40 : ℝ) ^ 4 * x ^ 2 ≤ x ^ 6 := by
    have := mul_le_mul_of_nonneg_right hx4 (sq_nonneg x)
    calc (40 : ℝ) ^ 4 * x ^ 2 ≤ x ^ 4 * x ^ 2 := this
      _ = x ^ 6 := by ring
  have h6 : ((961/1000 : ℝ) * x) ^ 6 / (Nat.factorial 6 : ℝ)
      = (961/1000 : ℝ) ^ 6 / 720 * x ^ 6 := by
    rw [show (Nat.factorial 6 : ℝ) = 720 by norm_num [Nat.factorial]]; ring
  rw [h6] at h
  have hx2 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  nlinarith

/-! ## §1.  Elementary lemmas: `|a(n)| ≤ τ(n)`, `∑ τ(n) ≤ x(1 + log x)`, `n^{−ρ}` -/

/-- `|a(n)| ≤ τ(n)` (from `|λ_δ| ≤ 1`). -/
lemma abs_bvA_le_card_divisors {z1 z2 : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2) (n : ℕ) :
    |bvA z1 z2 n| ≤ (n.divisors.card : ℝ) := by
  calc |bvA z1 z2 n| ≤ ∑ δ ∈ n.divisors, |bvLam z1 z2 δ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _δ ∈ n.divisors, (1 : ℝ) :=
        Finset.sum_le_sum fun δ _ => abs_bvLam_le_one hz1 hz12 δ
    _ = (n.divisors.card : ℝ) := by simp

/-- `∑_{n ≤ x} τ(n) = ∑_{d ≤ x} ⌊x/d⌋`. -/
lemma sum_card_divisors_eq (x : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, n.divisors.card = ∑ d ∈ Finset.Icc 1 x, x / d := by
  have h1 : ∀ n ∈ Finset.Icc 1 x,
      n.divisors.card = ((Finset.Icc 1 x).filter (fun d => d ∣ n)).card := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    congr 1
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, hn0⟩
      refine ⟨⟨Nat.pos_of_ne_zero ?_, (Nat.le_of_dvd (by omega) hd).trans hn.2⟩, hd⟩
      rintro rfl
      exact hn0 (Nat.eq_zero_of_zero_dvd hd)
    · rintro ⟨-, hd⟩
      exact ⟨hd, by omega⟩
  rw [Finset.sum_congr rfl h1]
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones, ← Nat.Ioc_filter_dvd_card_eq_div x d]
  congr 1

/-- `∑_{n ≤ x} τ(n) ≤ x (1 + log x)`. -/
lemma sum_card_divisors_le (x : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, (n.divisors.card : ℝ) ≤ x * (1 + Real.log x) := by
  have h := sum_card_divisors_eq x
  have h' : (∑ n ∈ Finset.Icc 1 x, (n.divisors.card : ℝ))
      = ∑ d ∈ Finset.Icc 1 x, ((x / d : ℕ) : ℝ) := by exact_mod_cast h
  rw [h']
  calc ∑ d ∈ Finset.Icc 1 x, ((x / d : ℕ) : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 x, (x : ℝ) / d := Finset.sum_le_sum fun d _ => Nat.cast_div_le
    _ = x * ∑ d ∈ Finset.Icc 1 x, ((d : ℝ))⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [div_eq_mul_inv]
    _ = x * ((harmonic x : ℚ) : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        rfl
    _ ≤ x * (1 + Real.log x) :=
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log x) (Nat.cast_nonneg x)

/-- `∑_{n ≤ x} τ(n)² ≤ x (1 + log x)³` (common-divisor double sum). -/
lemma sum_card_divisors_sq_le (x : ℕ) :
    ∑ n ∈ Finset.Icc 1 x, (n.divisors.card : ℝ) ^ 2 ≤ x * (1 + Real.log x) ^ 3 := by
  classical
  set I := Finset.Icc 1 x with hI
  set H : ℝ := ∑ d ∈ I, ((d : ℝ))⁻¹ with hH
  have hHle : H ≤ 1 + Real.log x := by
    have := harmonic_le_one_add_log x
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    exact this
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun d _ => by positivity
  -- Step 1: `τ(n) = ∑_{a ≤ x} [a ∣ n]`
  have hdiv : ∀ n ∈ I, (n.divisors.card : ℝ) = ∑ a ∈ I, if a ∣ n then (1 : ℝ) else 0 := by
    intro n hn
    rw [hI, Finset.mem_Icc] at hn
    have hset : n.divisors = I.filter (fun a => a ∣ n) := by
      ext a
      simp only [Nat.mem_divisors, Finset.mem_filter, hI, Finset.mem_Icc]
      constructor
      · rintro ⟨hd, hn0⟩
        refine ⟨⟨Nat.pos_of_ne_zero ?_, (Nat.le_of_dvd (by omega) hd).trans hn.2⟩, hd⟩
        rintro rfl
        exact hn0 (Nat.eq_zero_of_zero_dvd hd)
      · rintro ⟨-, hd⟩
        exact ⟨hd, by omega⟩
    rw [hset, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hite : ∀ a b n : ℕ, (if a ∣ n then (1 : ℝ) else 0) * (if b ∣ n then (1 : ℝ) else 0)
      = if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0 := by
    intro a b n
    by_cases h1 : a ∣ n <;> by_cases h2 : b ∣ n <;> simp [h1, h2]
  have hstep1 : ∑ n ∈ I, (n.divisors.card : ℝ) ^ 2
      = ∑ a ∈ I, ∑ b ∈ I, ∑ n ∈ I, (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) := by
    calc ∑ n ∈ I, (n.divisors.card : ℝ) ^ 2
        = ∑ n ∈ I, ∑ a ∈ I, ∑ b ∈ I, (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [hdiv n hn, sq, Finset.sum_mul_sum]
          simp_rw [hite]
      _ = ∑ a ∈ I, ∑ n ∈ I, ∑ b ∈ I, (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) := Finset.sum_comm
      _ = ∑ a ∈ I, ∑ b ∈ I, ∑ n ∈ I, (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
  -- Step 2: the inner count is `⌊x / lcm(a,b)⌋`
  have hcount : ∀ a b : ℕ, ∑ n ∈ I, (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0)
      = ((x / Nat.lcm a b : ℕ) : ℝ) := by
    intro a b
    have hc : (I.filter (fun n => a ∣ n ∧ b ∣ n)).card = x / Nat.lcm a b := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div]
      congr 1
      ext n
      simp only [Finset.mem_filter, hI, Finset.mem_Icc, Finset.mem_Ioc, Nat.lcm_dvd_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨by omega, h2⟩, h3⟩
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hc]
  -- Step 3: `⌊x/lcm⌋ ≤ x·gcd/(ab)`
  have hlcm : ∀ a ∈ I, ∀ b ∈ I,
      ((x / Nat.lcm a b : ℕ) : ℝ) ≤ x * ((Nat.gcd a b : ℝ) / (a * b)) := by
    intro a ha b hb
    rw [hI, Finset.mem_Icc] at ha hb
    have haR : (0 : ℝ) < a := by exact_mod_cast ha.1
    have hbR : (0 : ℝ) < b := by exact_mod_cast hb.1
    have hlpos : (0 : ℝ) < Nat.lcm a b := by exact_mod_cast Nat.lcm_pos ha.1 hb.1
    have hR : (Nat.gcd a b : ℝ) * (Nat.lcm a b : ℝ) = a * b := by
      exact_mod_cast Nat.gcd_mul_lcm a b
    have hR' : (Nat.gcd a b : ℝ) / (a * b) = 1 / Nat.lcm a b := by
      rw [div_eq_div_iff (by positivity) hlpos.ne', one_mul]
      exact hR
    calc ((x / Nat.lcm a b : ℕ) : ℝ) ≤ (x : ℝ) / Nat.lcm a b := Nat.cast_div_le
      _ = x * ((Nat.gcd a b : ℝ) / (a * b)) := by rw [hR']; ring
  -- Step 4: `gcd(a,b)/(ab) ≤ ∑_{g ∣ a, g ∣ b} g/(ab)`
  have hgcd : ∀ a ∈ I, ∀ b ∈ I, (Nat.gcd a b : ℝ) / (a * b)
      ≤ ∑ g ∈ I.filter (fun g => g ∣ a ∧ g ∣ b), (g : ℝ) / (a * b) := by
    intro a ha b hb
    rw [hI, Finset.mem_Icc] at ha hb
    refine Finset.single_le_sum (f := fun g : ℕ => (g : ℝ) / (a * b))
      (fun g _ => by positivity) ?_
    rw [Finset.mem_filter, hI, Finset.mem_Icc]
    exact ⟨⟨Nat.gcd_pos_of_pos_left b ha.1,
      (Nat.le_of_dvd ha.1 (Nat.gcd_dvd_left a b)).trans ha.2⟩,
      Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩
  -- Step 5: swap to the `g`-sum
  have hpt : ∀ g a b : ℕ, (if g ∣ a ∧ g ∣ b then (g : ℝ) / (a * b) else 0)
      = (g : ℝ) * ((if g ∣ a then ((a : ℝ))⁻¹ else 0) * (if g ∣ b then ((b : ℝ))⁻¹ else 0)) := by
    intro g a b
    by_cases h1 : g ∣ a <;> by_cases h2 : g ∣ b <;> simp [h1, h2]
    rw [div_eq_mul_inv, mul_inv]
  have hswap : ∑ a ∈ I, ∑ b ∈ I, ∑ g ∈ I.filter (fun g => g ∣ a ∧ g ∣ b), (g : ℝ) / (a * b)
      = ∑ g ∈ I, (g : ℝ) * ((∑ a ∈ I.filter (fun a => g ∣ a), ((a : ℝ))⁻¹)
          * (∑ b ∈ I.filter (fun b => g ∣ b), ((b : ℝ))⁻¹)) := by
    simp_rw [Finset.sum_filter]
    calc ∑ a ∈ I, ∑ b ∈ I, ∑ g ∈ I, (if g ∣ a ∧ g ∣ b then (g : ℝ) / (a * b) else 0)
        = ∑ a ∈ I, ∑ g ∈ I, ∑ b ∈ I, (if g ∣ a ∧ g ∣ b then (g : ℝ) / (a * b) else 0) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ g ∈ I, ∑ a ∈ I, ∑ b ∈ I, (if g ∣ a ∧ g ∣ b then (g : ℝ) / (a * b) else 0) :=
          Finset.sum_comm
      _ = ∑ g ∈ I, (g : ℝ) * ((∑ a ∈ I, if g ∣ a then ((a : ℝ))⁻¹ else 0)
          * (∑ b ∈ I, if g ∣ b then ((b : ℝ))⁻¹ else 0)) := by
          refine Finset.sum_congr rfl fun g _ => ?_
          rw [Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => hpt g a b
  -- Step 6: `∑_{a ≤ x, g ∣ a} 1/a ≤ H/g`
  have hmult : ∀ g ∈ I, ∑ a ∈ I.filter (fun a => g ∣ a), ((a : ℝ))⁻¹ ≤ ((g : ℝ))⁻¹ * H := by
    intro g hg
    rw [hI, Finset.mem_Icc] at hg
    have himg : I.filter (fun a => g ∣ a) = (Finset.Icc 1 (x / g)).image (fun a' => g * a') := by
      ext a
      simp only [Finset.mem_filter, hI, Finset.mem_Icc, Finset.mem_image]
      constructor
      · rintro ⟨⟨h1, h2⟩, hd⟩
        refine ⟨a / g, ⟨?_, Nat.div_le_div_right h2⟩, Nat.mul_div_cancel' hd⟩
        exact Nat.div_pos (Nat.le_of_dvd (by omega) hd) (by omega)
      · rintro ⟨a', ⟨h1, h2⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, dvd_mul_right g a'⟩
        · calc 1 ≤ g := hg.1
            _ ≤ g * a' := Nat.le_mul_of_pos_right g h1
        · calc g * a' ≤ g * (x / g) := Nat.mul_le_mul_left g h2
            _ ≤ x := Nat.mul_div_le x g
    rw [himg, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by omega) h)]
    have hinv : ∀ a' : ℕ, (((g * a' : ℕ) : ℝ))⁻¹ = ((g : ℝ))⁻¹ * ((a' : ℝ))⁻¹ := by
      intro a'; push_cast; rw [mul_inv]
    simp_rw [hinv]
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right (Nat.div_le_self x g)) (fun a _ _ => by positivity)
  -- Step 7: assemble
  calc ∑ n ∈ I, (n.divisors.card : ℝ) ^ 2
      = ∑ a ∈ I, ∑ b ∈ I, ∑ n ∈ I, (if a ∣ n ∧ b ∣ n then (1 : ℝ) else 0) := hstep1
    _ = ∑ a ∈ I, ∑ b ∈ I, ((x / Nat.lcm a b : ℕ) : ℝ) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hcount a b
    _ ≤ ∑ a ∈ I, ∑ b ∈ I, (x : ℝ) * ((Nat.gcd a b : ℝ) / (a * b)) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hlcm a ha b hb
    _ ≤ ∑ a ∈ I, ∑ b ∈ I, (x : ℝ)
        * ∑ g ∈ I.filter (fun g => g ∣ a ∧ g ∣ b), (g : ℝ) / (a * b) :=
        Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb =>
          mul_le_mul_of_nonneg_left (hgcd a ha b hb) (Nat.cast_nonneg x)
    _ = (x : ℝ) * ∑ a ∈ I, ∑ b ∈ I,
        ∑ g ∈ I.filter (fun g => g ∣ a ∧ g ∣ b), (g : ℝ) / (a * b) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
    _ = (x : ℝ) * ∑ g ∈ I, (g : ℝ) * ((∑ a ∈ I.filter (fun a => g ∣ a), ((a : ℝ))⁻¹)
          * (∑ b ∈ I.filter (fun b => g ∣ b), ((b : ℝ))⁻¹)) := by rw [hswap]
    _ ≤ (x : ℝ) * ∑ g ∈ I, (g : ℝ) * ((((g : ℝ))⁻¹ * H) * (((g : ℝ))⁻¹ * H)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun g hg => ?_) (Nat.cast_nonneg x)
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg g)
        have h0 : 0 ≤ ∑ b ∈ I.filter (fun b => g ∣ b), ((b : ℝ))⁻¹ :=
          Finset.sum_nonneg fun b _ => by positivity
        exact mul_le_mul (hmult g hg) (hmult g hg) h0 (by positivity)
    _ = (x : ℝ) * (H ^ 2 * H) := by
        congr 1
        have hHs : H ^ 2 * H = ∑ g ∈ I, H ^ 2 * ((g : ℝ))⁻¹ := by
          rw [← Finset.mul_sum, ← hH]
        rw [hHs]
        refine Finset.sum_congr rfl fun g hg => ?_
        rw [hI, Finset.mem_Icc] at hg
        have hg0 : (g : ℝ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
        field_simp
    _ = (x : ℝ) * H ^ 3 := by ring
    _ ≤ x * (1 + Real.log x) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH0 hHle 3) (Nat.cast_nonneg x)

/-- `(n:ℂ)^{−ρ} = n^{−Re ρ} · exp((−log n · Im ρ) i)`. -/
lemma natCast_cpow_neg_eq {n : ℕ} (hn : 0 < n) (ρ : ℂ) :
    (n : ℂ) ^ (-ρ) = (((n : ℝ) ^ (-ρ.re) : ℝ) : ℂ)
      * Complex.exp ((-Real.log n * ρ.im : ℝ) * Complex.I) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Complex.cpow_def_of_ne_zero hn0, Real.rpow_def_of_pos hnR, Complex.ofReal_exp,
    ← Complex.exp_add]
  congr 1
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg n)]
  rw [hlog]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im]
    ring

/-! ## §2.  Lemma 2.3: convexity on the half-line, and the Taylor remainder -/

/-- **Lemma 2.3** (I1 at `Re s = 1/2` with I9(d)): on `Re (ρ + w) = 1/2`, `w = c + iu`,
`‖L(ρ+w,χ)‖ ≤ 6·10⁵·C_τ·D^{201/800}·log D·(1+|u|)²` where `N(|Im ρ|+2) ≤ D`. -/
lemma norm_LFunction_half_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {D : ℝ} (hD1 : 1 < D) (hLD : 2 ≤ Real.log D)
    {ρ : ℂ} {c : ℝ} (hc : ρ.re + c = 1/2)
    (hDN : (N : ℝ) * (|ρ.im| + 2) ≤ D) (u : ℝ) :
    ‖DirichletCharacter.LFunction χ (ρ + ((c : ℂ) + (u : ℂ) * Complex.I))‖
      ≤ 600000 * Ctau * D ^ (201/800 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  set s : ℂ := ρ + ((c : ℂ) + (u : ℂ) * Complex.I) with hs
  have hsre : s.re = 1/2 := by
    simp only [hs, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im]
    linarith [hc]
  have hsim : s.im = ρ.im + u := by
    simp only [hs, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re]
    ring
  have hs1 : s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre] at this
    norm_num at this
  have hconv := norm_LFunction_le_convexity_all χ (s := s) (Or.inr hs1)
    (by rw [hsre]; norm_num) (by rw [hsre]; norm_num)
  rw [hsre] at hconv
  have hmax : max ((1 - (1:ℝ)/2)/2) 0 = 1/4 := by
    rw [max_eq_left (by norm_num)]; norm_num
  rw [hmax] at hconv
  refine hconv.trans ?_
  have hu0 : (0 : ℝ) ≤ |u| := abs_nonneg u
  have hu1 : (1 : ℝ) ≤ 1 + |u| := by linarith
  have habs : |s.im| ≤ |ρ.im| + |u| := by rw [hsim]; exact abs_add_le _ _
  have hρ0 : (0 : ℝ) ≤ |ρ.im| := abs_nonneg _
  -- the pole term
  have hpole : 1 / ‖s - 1‖ ≤ 2 := by
    have h1 : (1/2 : ℝ) ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1)
      rw [Complex.sub_re, hsre, Complex.one_re] at this
      rw [abs_of_neg (by norm_num)] at this
      linarith
    rw [div_le_iff₀ (by linarith)]
    linarith
  -- the base bound
  have hbase : (N : ℝ) * (|s.im| + 2) ≤ D * (1 + |u|) := by
    have h1 : (N : ℝ) * (|s.im| + 2) ≤ (N : ℝ) * ((|ρ.im| + 2) * (1 + |u|)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      nlinarith
    calc (N : ℝ) * (|s.im| + 2) ≤ (N : ℝ) * ((|ρ.im| + 2) * (1 + |u|)) := h1
      _ = ((N : ℝ) * (|ρ.im| + 2)) * (1 + |u|) := by ring
      _ ≤ D * (1 + |u|) := by nlinarith
  have hbase0 : (0 : ℝ) ≤ (N : ℝ) * (|s.im| + 2) := by positivity
  have hpow : ((N : ℝ) * (|s.im| + 2)) ^ (1/4 : ℝ) ≤ D ^ (1/4 : ℝ) * (1 + |u|) := by
    calc ((N : ℝ) * (|s.im| + 2)) ^ (1/4 : ℝ) ≤ (D * (1 + |u|)) ^ (1/4 : ℝ) :=
          Real.rpow_le_rpow hbase0 hbase (by norm_num)
      _ = D ^ (1/4 : ℝ) * (1 + |u|) ^ (1/4 : ℝ) :=
          Real.mul_rpow hD0.le (by linarith)
      _ ≤ D ^ (1/4 : ℝ) * (1 + |u|) ^ (1 : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hD0.le _)
          exact Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
      _ = D ^ (1/4 : ℝ) * (1 + |u|) := by rw [Real.rpow_one]
  -- the log bound
  have hND : (N : ℝ) ≤ D := by nlinarith
  have hlogbase : (N : ℝ) * (|s.im| + 3) ≤ 2 * D * (1 + |u|) := by
    have h1 : (N : ℝ) * (|s.im| + 3) = (N : ℝ) * (|s.im| + 2) + (N : ℝ) := by ring
    have h2 : (N : ℝ) ≤ D * (1 + |u|) := by nlinarith
    rw [h1]
    linarith [hbase]
  have hlog : Real.log ((N : ℝ) * (|s.im| + 3)) ≤ 2 * Real.log D * (1 + |u|) := by
    have hpos : (0 : ℝ) < (N : ℝ) * (|s.im| + 3) := by positivity
    have h1 : Real.log ((N : ℝ) * (|s.im| + 3)) ≤ Real.log (2 * D * (1 + |u|)) :=
      Real.log_le_log hpos hlogbase
    have h2 : Real.log (2 * D * (1 + |u|))
        = Real.log 2 + Real.log D + Real.log (1 + |u|) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (by positivity)]
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (x := (2:ℝ)) (by norm_num)
      linarith
    have h4 : Real.log (1 + |u|) ≤ |u| := by
      have := Real.log_le_sub_one_of_pos (x := 1 + |u|) (by linarith)
      linarith
    have h5 : (1 : ℝ) ≤ Real.log D := by linarith
    nlinarith
  have hL0 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|s.im| + 3)) := by
    refine Real.log_nonneg ?_
    nlinarith
  have hAnn : (0 : ℝ) ≤ D ^ (1/4 : ℝ) := Real.rpow_nonneg hD0.le _
  have hA1 : (1 : ℝ) ≤ D ^ (1/4 : ℝ) := by
    calc (1 : ℝ) = D ^ (0 : ℝ) := (Real.rpow_zero D).symm
      _ ≤ D ^ (1/4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by norm_num)
  have hlognn : (0 : ℝ) ≤ Real.log D := by linarith
  have hsq1 : (1 : ℝ) ≤ (1 + |u|) ^ 2 := by nlinarith
  -- the main product
  have hmain : ((N : ℝ) * (|s.im| + 2)) ^ (1/4 : ℝ) * Real.log ((N : ℝ) * (|s.im| + 3))
      ≤ 2 * D ^ (1/4 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by
    calc ((N : ℝ) * (|s.im| + 2)) ^ (1/4 : ℝ) * Real.log ((N : ℝ) * (|s.im| + 3))
        ≤ (D ^ (1/4 : ℝ) * (1 + |u|)) * (2 * Real.log D * (1 + |u|)) :=
          mul_le_mul hpow hlog hL0 (by positivity)
      _ = 2 * D ^ (1/4 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by ring
  have hinner : ((N : ℝ) * (|s.im| + 2)) ^ (1/4 : ℝ) * Real.log ((N : ℝ) * (|s.im| + 3))
      + 1 / ‖s - 1‖ ≤ 3 * D ^ (1/4 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by
    have h2 : (2 : ℝ) ≤ D ^ (1/4 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by
      calc (2 : ℝ) = 1 * 2 * 1 := by norm_num
        _ ≤ D ^ (1/4 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by gcongr
    linarith
  have hω : (2 : ℝ) ^ N.primeFactors.card ≤ Ctau * D ^ (1/800 : ℝ) :=
    two_pow_card_primeFactors_le_Ctau_mul hND
  have hin0 : (0 : ℝ) ≤ ((N : ℝ) * (|s.im| + 2)) ^ (1/4 : ℝ)
      * Real.log ((N : ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖ := by positivity
  have hexp : D ^ (1/800 : ℝ) * D ^ (1/4 : ℝ) = D ^ (201/800 : ℝ) := by
    rw [← Real.rpow_add hD0]; norm_num
  calc 200000 * (2 : ℝ) ^ N.primeFactors.card
        * (((N : ℝ) * (|s.im| + 2)) ^ (1/4 : ℝ) * Real.log ((N : ℝ) * (|s.im| + 3))
          + 1 / ‖s - 1‖)
      ≤ 200000 * (Ctau * D ^ (1/800 : ℝ))
        * (3 * D ^ (1/4 : ℝ) * Real.log D * (1 + |u|) ^ 2) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hω (by norm_num)) hinner hin0 ?_
        have := Ctau_pos
        positivity
    _ = 600000 * Ctau * (D ^ (1/800 : ℝ) * D ^ (1/4 : ℝ)) * Real.log D * (1 + |u|) ^ 2 := by
        ring
    _ = 600000 * Ctau * D ^ (201/800 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by rw [hexp]

/-- **Lemma 2.7, remainder** (via `Real.exp_bound`): for `|x| ≤ 1/6` and `J ≥ 3`,
`|e^x − ∑_{k ≤ J} x^k/k!| ≤ (1/5)^{J+1}`. -/
lemma taylor_remainder_le {x : ℝ} (hx : |x| ≤ 1/6) {J : ℕ} (hJ : 3 ≤ J) :
    |Real.exp x - ∑ k ∈ Finset.range (J + 1), x ^ k / (Nat.factorial k : ℝ)|
      ≤ (1/5 : ℝ) ^ (J + 1) := by
  have h := Real.exp_bound (x := x) (by linarith [abs_nonneg x]) (n := J + 1) (by omega)
  refine h.trans ?_
  have hfac : (1 : ℝ) ≤ (Nat.factorial (J + 1) : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hJ1 : (1 : ℝ) ≤ ((J + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos J
  have hfrac : (((J + 1).succ : ℕ) : ℝ) / ((Nat.factorial (J + 1) : ℝ) * ((J + 1 : ℕ) : ℝ))
      ≤ 2 := by
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hpow : |x| ^ (J + 1) ≤ (1/6 : ℝ) ^ (J + 1) :=
    pow_le_pow_left₀ (abs_nonneg x) hx _
  have h2 : (2 : ℝ) * (1/6 : ℝ) ^ (J + 1) ≤ (1/5 : ℝ) ^ (J + 1) := by
    have h65 : (2 : ℝ) ≤ (6/5 : ℝ) ^ (J + 1) := by
      calc (2 : ℝ) ≤ (6/5 : ℝ) ^ 4 := by norm_num
        _ ≤ (6/5 : ℝ) ^ (J + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h56 : (1/5 : ℝ) ^ (J + 1) = (6/5 : ℝ) ^ (J + 1) * (1/6 : ℝ) ^ (J + 1) := by
      rw [← mul_pow]; norm_num
    rw [h56]
    exact mul_le_mul_of_nonneg_right h65 (by positivity)
  calc |x| ^ (J + 1) * ((((J + 1).succ : ℕ) : ℝ)
        / ((Nat.factorial (J + 1) : ℝ) * ((J + 1 : ℕ) : ℝ)))
      ≤ (1/6 : ℝ) ^ (J + 1) * 2 := mul_le_mul hpow hfrac (by positivity) (by positivity)
    _ = 2 * (1/6 : ℝ) ^ (J + 1) := by ring
    _ ≤ (1/5 : ℝ) ^ (J + 1) := h2

/-! ## §3.  L1.c: truncation of the detector series (Lemma 2.4) -/

/-- The summand of the truncated detector sum at `R = 1`. -/
noncomputable def truncTerm {N : ℕ} (χ : DirichletCharacter ℂ N) (D : ℝ) (ρ : ℂ) (n : ℕ) : ℂ :=
  if D < (n : ℝ) then
    ((bvA D (2 * D) n * Real.exp (-(n : ℝ) / Ypar D) : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-ρ)
  else 0

/-- The `R = 1` detector summand is `truncTerm` (`Pfun N 1 n = 1`). -/
lemma fdetTerm_one_eq {N : ℕ} (χ : DirichletCharacter ℂ N) (D : ℝ) (ρ : ℂ) (n : ℕ) :
    (if D < (n : ℝ) then
      ((bvA D (2 * D) n * Pfun N 1 n * Real.exp (-(n : ℝ) / Ypar D) : ℝ) : ℂ) * χ n
        * (n : ℂ) ^ (-ρ) else 0) = truncTerm χ D ρ n := by
  rw [truncTerm, Pfun_one_eq_one, mul_one]

lemma Fdet_eq_tsum_truncTerm {N : ℕ} (χ : DirichletCharacter ℂ N) (D : ℝ) (ρ : ℂ) :
    Fdet χ D (2 * D) 1 (Ypar D) ρ = ∑' n : ℕ, truncTerm χ D ρ n := by
  rw [Fdet]
  exact tsum_congr fun n => fdetTerm_one_eq χ D ρ n

lemma summable_truncTerm {N : ℕ} (χ : DirichletCharacter ℂ N) {D : ℝ} (hD : 0 < D)
    {ρ : ℂ} (hρ : 0 ≤ ρ.re) : Summable (fun n : ℕ => truncTerm χ D ρ n) := by
  have h := summable_fdetTerm χ (z1 := D) (z2 := 2 * D) (R := 1) (X := Ypar D) hD
    (by linarith) (Ypar_pos hD) hρ
  exact h.congr fun n => fdetTerm_one_eq χ D ρ n

/-- Trivial bound on a detector summand: `‖g(n)‖ ≤ n·e^{−n/Y}`. -/
lemma norm_truncTerm_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {D : ℝ} (hD : 0 < D)
    {ρ : ℂ} (hρ : 0 ≤ ρ.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖truncTerm χ D ρ n‖ ≤ (n : ℝ) * Real.exp (-(n : ℝ) / Ypar D) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [truncTerm]
  split_ifs with h
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have h1 : |bvA D (2 * D) n| ≤ (n : ℝ) := abs_bvA_le hD (by linarith) n
    have h2 : ‖χ ((n : ℕ) : ZMod N)‖ ≤ 1 := χ.norm_le_one _
    have h3 : ‖((n : ℕ) : ℂ) ^ (-ρ)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by simp [hρ])
    have hb0 : (0 : ℝ) ≤ (n : ℝ) * Real.exp (-(n : ℝ) / Ypar D) := by positivity
    calc |bvA D (2 * D) n| * Real.exp (-(n : ℝ) / Ypar D) * ‖χ ((n : ℕ) : ZMod N)‖
          * ‖((n : ℕ) : ℂ) ^ (-ρ)‖
        ≤ ((n : ℝ) * Real.exp (-(n : ℝ) / Ypar D)) * 1 * 1 := by
          refine mul_le_mul (mul_le_mul ?_ h2 (norm_nonneg _) hb0) h3 (norm_nonneg _)
            (by positivity)
          exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = (n : ℝ) * Real.exp (-(n : ℝ) / Ypar D) := by ring
  · rw [norm_zero]; positivity

/-- `1 − e^{−x} ≥ x/2` for `0 ≤ x ≤ 1`. -/
lemma half_le_one_sub_exp_neg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have h2 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  have hpos : 0 < Real.exp x := Real.exp_pos x
  have h3 : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [h2, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by linarith) (by linarith)
  have h4 : 1 / (1 + x) ≤ 1 - x / 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- Tail numeric: `16·Y²·e^{−4 log D} ≤ 1/8` at `𝓛 ≥ 40`. -/
lemma tail_numeric {D : ℝ} (hD : 1 < D) (hL : 40 ≤ Real.log D) :
    16 * Ypar D ^ 2 * Real.exp (-4 * Real.log D) ≤ 1/8 := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hY2 : Ypar D ^ 2 = D ^ (302/100 : ℝ) := by
    rw [Ypar, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; norm_num
  have hE : Real.exp (-4 * Real.log D) = D ^ (-4 : ℝ) := by
    rw [Real.rpow_def_of_pos hD0]; congr 1; ring
  have h98 : (128 : ℝ) ≤ D ^ (98/100 : ℝ) := by
    rw [Real.rpow_def_of_pos hD0, mul_comm]
    exact numeric_tail hL
  have hprod : D ^ (302/100 : ℝ) * D ^ (-4 : ℝ) = (D ^ (98/100 : ℝ))⁻¹ := by
    rw [← Real.rpow_add hD0, ← Real.rpow_neg hD0.le]; norm_num
  rw [hY2, hE, mul_assoc, hprod]
  have hpos : (0 : ℝ) < D ^ (98/100 : ℝ) := Real.rpow_pos_of_pos hD0 _
  rw [← div_eq_mul_inv, div_le_iff₀ hpos]
  linarith

/-- **L1.c** (Lemma 2.4): the detector series is approximated within `1/8` by its
truncation at `Nmax D = ⌈8 Y log D⌉`. -/
theorem norm_Fdet_sub_truncation_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {D : ℝ} (hD : 1 < D) (hL : 40 ≤ Real.log D) {ρ : ℂ} (hβ : 39/50 ≤ ρ.re) (_hβ1 : ρ.re ≤ 1) :
    ‖Fdet χ D (2 * D) 1 (Ypar D) ρ
      - ∑ n ∈ Finset.Icc 1 (Nmax D), (if D < (n : ℝ) then
          ((bvA D (2 * D) n * Real.exp (-(n : ℝ) / Ypar D) : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-ρ)
        else 0)‖ ≤ 1/8 := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hρ0 : 0 ≤ ρ.re := by linarith
  have hY := Ypar_pos hD0
  have hY4 := four_le_Ypar hD0 hL
  have hL0 : (0 : ℝ) ≤ Real.log D := by linarith
  set M : ℕ := Nmax D with hM
  have hg := summable_truncTerm χ hD0 hρ0 (ρ := ρ)
  -- the finite sum is `∑_{n < M+1} g n` (the `n = 0` term vanishes)
  have hfin : (∑ n ∈ Finset.Icc 1 M, (if D < (n : ℝ) then
      ((bvA D (2 * D) n * Real.exp (-(n : ℝ) / Ypar D) : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-ρ)
        else 0)) = ∑ n ∈ Finset.range (M + 1), truncTerm χ D ρ n := by
    refine Finset.sum_subset ?_ ?_
    · intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]; omega
    · intro n hn hn'
      rw [Finset.mem_range] at hn
      rw [Finset.mem_Icc] at hn'
      have hn0 : n = 0 := by omega
      subst hn0
      simp only [Nat.cast_zero]
      rw [if_neg (by linarith)]
  rw [hfin, Fdet_eq_tsum_truncTerm, ← hg.sum_add_tsum_nat_add (M + 1), add_sub_cancel_left]
  -- the geometric majorant
  set q : ℝ := Real.exp (-1 / (2 * Ypar D)) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by
    rw [hq, Real.exp_lt_one_iff]
    have : (0 : ℝ) < 1 / (2 * Ypar D) := by positivity
    rw [neg_div]; linarith
  have hqn : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  set c : ℝ := Real.exp (-4 * Real.log D) with hc
  have hc0 : 0 < c := Real.exp_pos _
  have hmaj : Summable (fun m : ℕ => (m : ℝ) * q ^ m * c) := by
    have := (summable_pow_mul_geometric_of_norm_lt_one 1 hqn).mul_right c
    simpa using this
  -- pointwise bound for `m ≥ M + 1`
  have hM1 : 8 * Ypar D * Real.log D ≤ ((M + 1 : ℕ) : ℝ) := by
    have := le_Nmax (D := D)
    push_cast; linarith
  have hpt : ∀ i : ℕ, ‖truncTerm χ D ρ (i + (M + 1))‖
      ≤ ((i + (M + 1) : ℕ) : ℝ) * q ^ (i + (M + 1)) * c := by
    intro i
    set m : ℕ := i + (M + 1) with hm
    have hm1 : 1 ≤ m := by omega
    have hmR : ((M + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : M + 1 ≤ m)
    refine (norm_truncTerm_le χ hD0 hρ0 hm1).trans ?_
    have hsplit : Real.exp (-(m : ℝ) / Ypar D)
        = Real.exp (-(m : ℝ) / (2 * Ypar D)) * Real.exp (-(m : ℝ) / (2 * Ypar D)) := by
      rw [← Real.exp_add]; congr 1; field_simp; ring
    have hpow : Real.exp (-(m : ℝ) / (2 * Ypar D)) = q ^ m := by
      rw [hq, ← Real.exp_nat_mul]; congr 1; ring
    have hdecay : Real.exp (-(m : ℝ) / (2 * Ypar D)) ≤ c := by
      rw [hc]
      refine Real.exp_le_exp.mpr ?_
      have h4 : 4 * Real.log D ≤ (m : ℝ) / (2 * Ypar D) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have h5 : -(m : ℝ) / (2 * Ypar D) = -((m : ℝ) / (2 * Ypar D)) := by ring
      rw [h5]
      linarith
    have hre : (m : ℝ) * (Real.exp (-(m : ℝ) / (2 * Ypar D)) * Real.exp (-(m : ℝ) / (2 * Ypar D)))
        = ((m : ℝ) * q ^ m) * Real.exp (-(m : ℝ) / (2 * Ypar D)) := by
      rw [hpow]; ring
    rw [hsplit, hre]
    exact mul_le_mul_of_nonneg_left hdecay (by positivity)
  -- sum the majorant
  have hsumnorm : Summable (fun i : ℕ => ‖truncTerm χ D ρ (i + (M + 1))‖) :=
    summable_norm_iff.mpr ((summable_nat_add_iff (M + 1)).mpr hg)
  have htsum : ∑' i : ℕ, ‖truncTerm χ D ρ (i + (M + 1))‖ ≤ ∑' m : ℕ, (m : ℝ) * q ^ m * c := by
    refine Summable.tsum_le_tsum_of_inj (fun i => i + (M + 1)) (add_left_injective _)
      (fun m _ => by positivity) hpt hsumnorm hmaj
  have hgeo : ∑' m : ℕ, (m : ℝ) * q ^ m * c = q / (1 - q) ^ 2 * c := by
    rw [tsum_mul_right, tsum_coe_mul_geometric_of_norm_lt_one hqn]
  -- `1/(1−q)² ≤ 16 Y²`
  have h1q : 1 / (4 * Ypar D) ≤ 1 - q := by
    have hx0 : (0 : ℝ) ≤ 1 / (2 * Ypar D) := by positivity
    have hx1 : 1 / (2 * Ypar D) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have := half_le_one_sub_exp_neg hx0 hx1
    have heq : Real.exp (-(1 / (2 * Ypar D))) = q := by rw [hq, neg_div]
    rw [heq] at this
    calc 1 / (4 * Ypar D) = 1 / (2 * Ypar D) / 2 := by field_simp; ring
      _ ≤ 1 - q := this
  have hfrac : q / (1 - q) ^ 2 ≤ 16 * Ypar D ^ 2 := by
    have h1 : (1 / (4 * Ypar D)) ^ 2 ≤ (1 - q) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1q 2
    have h2 : (0 : ℝ) < (1 / (4 * Ypar D)) ^ 2 := by positivity
    calc q / (1 - q) ^ 2 ≤ 1 / (1 - q) ^ 2 :=
          div_le_div_of_nonneg_right hq1.le (by positivity)
      _ ≤ 1 / (1 / (4 * Ypar D)) ^ 2 := one_div_le_one_div_of_le h2 h1
      _ = 16 * Ypar D ^ 2 := by field_simp; ring
  calc ‖∑' i : ℕ, truncTerm χ D ρ (i + (M + 1))‖
      ≤ ∑' i : ℕ, ‖truncTerm χ D ρ (i + (M + 1))‖ := norm_tsum_le_tsum_norm hsumnorm
    _ ≤ q / (1 - q) ^ 2 * c := htsum.trans hgeo.le
    _ ≤ 16 * Ypar D ^ 2 * c := mul_le_mul_of_nonneg_right hfrac hc0.le
    _ ≤ 1/8 := tail_numeric hD hL

/-! ## §4.  Dyadic blocks and the Taylor split (Lemmas 2.5, 2.7) -/

/-- Numeric clause (iii): `Nmax D ≤ 2^{Jpar D}·D`, i.e. the blocks `j < Jpar D` cover
`(D, Nmax D]`. -/
lemma Nmax_le_two_pow_Jpar_mul {D : ℝ} (hD : 1 < D) (hL : 40 ≤ Real.log D) :
    (Nmax D : ℝ) ≤ 2 ^ Jpar D * D := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hL0 : (0 : ℝ) ≤ Real.log D := by linarith
  have hY := Ypar_pos hD0
  have hY1 := one_le_Ypar hD.le
  have h1 : (Nmax D : ℝ) ≤ 9 * Ypar D * Real.log D := by
    have := Nmax_le hD0 hL0
    have : 1 ≤ Ypar D * Real.log D := by nlinarith
    linarith
  have h2 : D ^ (Real.log 2) ≤ (2 : ℝ) ^ Jpar D := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hD0,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have := log_le_Jpar D
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith
  have h3 : 9 * Real.log D ≤ D ^ (Real.log 2 - 51/100) := by
    rw [Real.rpow_def_of_pos hD0]
    have hl2 := Real.log_two_gt_d9
    calc 9 * Real.log D ≤ Real.exp ((1831/10000 : ℝ) * Real.log D) := numeric_blocks hL
      _ ≤ Real.exp (Real.log D * (Real.log 2 - 51/100)) :=
          Real.exp_le_exp.mpr (by nlinarith)
  have h4 : D ^ (Real.log 2) * D = Ypar D * D ^ (Real.log 2 - 51/100) := by
    rw [Ypar, ← Real.rpow_add_one hD0.ne', ← Real.rpow_add hD0]
    congr 1; ring
  calc (Nmax D : ℝ) ≤ 9 * Ypar D * Real.log D := h1
    _ = Ypar D * (9 * Real.log D) := by ring
    _ ≤ Ypar D * D ^ (Real.log 2 - 51/100) := mul_le_mul_of_nonneg_left h3 hY.le
    _ = D ^ (Real.log 2) * D := h4.symm
    _ ≤ 2 ^ Jpar D * D := mul_le_mul_of_nonneg_right h2 hD0.le

/-- **Lemma 2.5** (existence): every `n` with `D < n ≤ 2^J D` lies in a block
`2^j D < n ≤ 2^{j+1} D` with `j < J`. -/
lemma exists_block {D : ℝ} (_hD : 0 < D) {n : ℕ} (hn : D < n) :
    ∀ J : ℕ, (n : ℝ) ≤ 2 ^ J * D →
      ∃ j < J, 2 ^ j * D < (n : ℝ) ∧ (n : ℝ) ≤ 2 ^ (j + 1) * D := by
  intro J
  induction J with
  | zero => intro h; simp at h; linarith
  | succ J ih =>
    intro h
    by_cases h' : (n : ℝ) ≤ 2 ^ J * D
    · obtain ⟨j, hj, hb⟩ := ih h'
      exact ⟨j, by omega, hb⟩
    · exact ⟨J, by omega, lt_of_not_ge h', h⟩

/-- Blocks are disjoint. -/
lemma block_unique {D : ℝ} (hD : 0 < D) {n : ℕ} {j j' : ℕ}
    (h : 2 ^ j * D < (n : ℝ) ∧ (n : ℝ) ≤ 2 ^ (j + 1) * D)
    (h' : 2 ^ j' * D < (n : ℝ) ∧ (n : ℝ) ≤ 2 ^ (j' + 1) * D) : j = j' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : (2 : ℝ) ^ (j + 1) ≤ 2 ^ j' := pow_le_pow_right₀ (by norm_num) (by omega)
    have : (2 : ℝ) ^ (j + 1) * D ≤ 2 ^ j' * D := mul_le_mul_of_nonneg_right this hD.le
    linarith [h.2, h'.1]
  · have : (2 : ℝ) ^ (j' + 1) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
    have : (2 : ℝ) ^ (j' + 1) * D ≤ 2 ^ j * D := mul_le_mul_of_nonneg_right this hD.le
    linarith [h'.2, h.1]

/-- The `j`-th dyadic block sum `S_j(ρ,χ)` of the truncated detector. -/
noncomputable def blockSum {N : ℕ} (χ : DirichletCharacter ℂ N) (D : ℝ) (ρ : ℂ) (j : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nmax D),
    if 2 ^ j * D < (n : ℝ) ∧ (n : ℝ) ≤ 2 ^ (j + 1) * D then
      ((bvA D (2 * D) n * Real.exp (-(n : ℝ) / Ypar D) : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-ρ)
    else 0

/-- The `(j,k)` Taylor component `T_{j,k}(γ,χ)`, summed over `Icc 1 (Nmax D)`. -/
noncomputable def taylorSum {N : ℕ} (χ : DirichletCharacter ℂ N) (D σ γ : ℝ) (j k : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nmax D),
    coeffJK D σ j k n * χ n * Complex.exp ((-Real.log n * γ : ℝ) * Complex.I)

/-- Taylor remainder of `e^{x}` at `x = δ·(−log(n/N))`, order `J`. -/
noncomputable def taylorRem (δ Nb : ℝ) (J : ℕ) (n : ℕ) : ℝ :=
  Real.exp (δ * (-(Real.log ((n : ℝ) / Nb))))
    - ∑ k ∈ Finset.range (J + 1), δ ^ k / (Nat.factorial k : ℝ) * (-(Real.log ((n : ℝ) / Nb))) ^ k

/-- The remainder summand of the Taylor split of block `j`. -/
noncomputable def remTerm {N : ℕ} (χ : DirichletCharacter ℂ N) (D σ : ℝ) (ρ : ℂ) (j : ℕ)
    (n : ℕ) : ℂ :=
  if 2 ^ j * D < (n : ℝ) ∧ (n : ℝ) ≤ 2 ^ (j + 1) * D then
    ((bvA D (2 * D) n * Real.exp (-(n : ℝ) / Ypar D) * (n : ℝ) ^ (-σ)
        * taylorRem (ρ.re - σ) (2 ^ j * D) (Jpar D) n : ℝ) : ℂ)
      * χ n * Complex.exp ((-Real.log n * ρ.im : ℝ) * Complex.I)
  else 0

/-- The remainder sum `R_j`. -/
noncomputable def remSum {N : ℕ} (χ : DirichletCharacter ℂ N) (D σ : ℝ) (ρ : ℂ) (j : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 (Nmax D), remTerm χ D σ ρ j n

/-- `S = ∑_{j < J} S_j` (Lemma 2.5). -/
lemma sum_truncTerm_eq_sum_blockSum {N : ℕ} (χ : DirichletCharacter ℂ N) {D : ℝ} (hD : 1 < D)
    (hL : 40 ≤ Real.log D) (ρ : ℂ) :
    ∑ n ∈ Finset.Icc 1 (Nmax D), truncTerm χ D ρ n
      = ∑ j ∈ Finset.range (Jpar D), blockSum χ D ρ j := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hcov := Nmax_le_two_pow_Jpar_mul hD hL
  unfold blockSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hnN : (n : ℝ) ≤ 2 ^ Jpar D * D := by
    calc (n : ℝ) ≤ (Nmax D : ℝ) := by exact_mod_cast hn.2
      _ ≤ 2 ^ Jpar D * D := hcov
  by_cases hDn : D < (n : ℝ)
  · obtain ⟨j0, hj0, hb⟩ := exists_block hD0 hDn (Jpar D) hnN
    rw [Finset.sum_eq_single j0]
    · rw [truncTerm, if_pos hDn, if_pos hb]
    · intro j _ hne
      rw [if_neg]
      intro hb'
      exact hne (block_unique hD0 hb' hb)
    · intro h
      exact absurd (Finset.mem_range.mpr hj0) h
  · rw [truncTerm, if_neg hDn]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    rintro ⟨h1, -⟩
    have : D ≤ 2 ^ j * D := le_mul_of_one_le_left hD0.le (one_le_pow₀ (by norm_num))
    linarith

lemma coeffJK_eq_zero_of_not_block {D σ : ℝ} {j k n : ℕ}
    (h : ¬ (2 ^ j * D < (n : ℝ) ∧ (n : ℝ) ≤ 2 ^ (j + 1) * D)) : coeffJK D σ j k n = 0 := by
  rw [coeffJK, if_neg]
  rintro ⟨h1, h2, -⟩
  exact h ⟨h1, h2⟩

/-- The real Taylor identity: `n^{−β} = N^{−δ}·n^{−σ}·(∑_{k≤J} δ^k(−log(n/N))^k/k! + r_n)`. -/
lemma rpow_neg_eq_taylor {Nb : ℝ} (hN : 0 < Nb) {n : ℕ} (hn : 0 < n) (σ δ : ℝ) (J : ℕ) :
    (n : ℝ) ^ (-(σ + δ)) = Nb ^ (-δ) * ((n : ℝ) ^ (-σ)
      * (∑ k ∈ Finset.range (J + 1), δ ^ k / (Nat.factorial k : ℝ)
          * (-(Real.log ((n : ℝ) / Nb))) ^ k + taylorRem δ Nb J n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hSr : (∑ k ∈ Finset.range (J + 1), δ ^ k / (Nat.factorial k : ℝ)
      * (-(Real.log ((n : ℝ) / Nb))) ^ k) + taylorRem δ Nb J n
      = Real.exp (δ * (-(Real.log ((n : ℝ) / Nb)))) := by
    rw [taylorRem]; ring
  rw [hSr, Real.rpow_def_of_pos hN, Real.rpow_def_of_pos hnR, Real.rpow_def_of_pos hnR,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Real.log_div hnR.ne' hN.ne']
  ring

/-- **Lemma 2.7** (Taylor split of a block):
`S_j = N_j^{−δ}·(∑_{k ≤ J} (δ^k/k!)·T_{j,k} + R_j)`, `δ = β − σ`. -/
lemma blockSum_eq_taylor {N : ℕ} (χ : DirichletCharacter ℂ N) {D : ℝ} (hD : 0 < D)
    (σ : ℝ) (ρ : ℂ) (j : ℕ) :
    blockSum χ D ρ j
      = (((2 ^ j * D) ^ (-(ρ.re - σ)) : ℝ) : ℂ)
        * (∑ k ∈ Finset.range (Jpar D + 1),
            (((ρ.re - σ) ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ) * taylorSum χ D σ ρ.im j k
          + remSum χ D σ ρ j) := by
  have hN0 : (0 : ℝ) < 2 ^ j * D := by positivity
  unfold blockSum taylorSum remSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn0 : 0 < n := hn.1
  by_cases hb : 2 ^ j * D < (n : ℝ) ∧ (n : ℝ) ≤ 2 ^ (j + 1) * D
  · rw [if_pos hb]
    have hcoef : ∀ k, coeffJK D σ j k n
        = ((bvA D (2 * D) n * Real.exp (-(n : ℝ) / Ypar D)
            * (-(Real.log ((n : ℝ) / (2 ^ j * D)))) ^ k * (n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
      intro k
      rw [coeffJK, if_pos ⟨hb.1, hb.2, hn.2⟩]
    simp_rw [hcoef]
    rw [remTerm, if_pos hb]
    obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ∑ k ∈ Finset.range (Jpar D + 1),
        (ρ.re - σ) ^ k / (Nat.factorial k : ℝ) * (-(Real.log ((n : ℝ) / (2 ^ j * D)))) ^ k :=
      ⟨_, rfl⟩
    have hsum : ∑ k ∈ Finset.range (Jpar D + 1),
        (((ρ.re - σ) ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ)
          * (((bvA D (2 * D) n * Real.exp (-(n : ℝ) / Ypar D)
              * (-(Real.log ((n : ℝ) / (2 ^ j * D)))) ^ k * (n : ℝ) ^ (-σ) : ℝ) : ℂ)
            * χ n * Complex.exp ((-Real.log n * ρ.im : ℝ) * Complex.I))
        = ((bvA D (2 * D) n * Real.exp (-(n : ℝ) / Ypar D) * (n : ℝ) ^ (-σ) * S : ℝ) : ℂ)
            * χ n * Complex.exp ((-Real.log n * ρ.im : ℝ) * Complex.I) := by
      rw [hS]
      push_cast
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [hsum]
    have hR := rpow_neg_eq_taylor hN0 hn0 σ (ρ.re - σ) (Jpar D)
    rw [← hS] at hR
    have hβ : -(σ + (ρ.re - σ)) = -ρ.re := by ring
    rw [hβ] at hR
    rw [natCast_cpow_neg_eq hn0, hR]
    push_cast
    ring
  · rw [if_neg hb]
    have hz : ∀ k ∈ Finset.range (Jpar D + 1),
        (((ρ.re - σ) ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ)
          * (coeffJK D σ j k n * χ n * Complex.exp ((-Real.log n * ρ.im : ℝ) * Complex.I)) = 0 := by
      intro k _
      rw [coeffJK_eq_zero_of_not_block hb]; ring
    rw [Finset.sum_eq_zero hz, remTerm, if_neg hb]
    ring

/-- `‖S_j‖ ≤ ∑_{k ≤ J} ‖T_{j,k}‖ + ‖R_j‖` (using `N_j^{−δ} ≤ 1`, `δ^k/k! ≤ 1`). -/
lemma norm_blockSum_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {D : ℝ} (hD : 1 ≤ D)
    {σ : ℝ} {ρ : ℂ} (hβ : σ ≤ ρ.re) (hβ1 : ρ.re ≤ 1) (hσ : 0 ≤ σ) (j : ℕ) :
    ‖blockSum χ D ρ j‖
      ≤ ∑ k ∈ Finset.range (Jpar D + 1), ‖taylorSum χ D σ ρ.im j k‖ + ‖remSum χ D σ ρ j‖ := by
  have hD0 : (0 : ℝ) < D := by linarith
  rw [blockSum_eq_taylor χ hD0 σ ρ j, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  have hN1 : (1 : ℝ) ≤ 2 ^ j * D := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hD
  have hpow1 : (2 ^ j * D) ^ (-(ρ.re - σ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hδ0 : 0 ≤ ρ.re - σ := by linarith
  have hδ1 : ρ.re - σ ≤ 1 := by linarith
  have hck : ∀ k : ℕ, (ρ.re - σ) ^ k / (Nat.factorial k : ℝ) ≤ 1 := by
    intro k
    have h1 : (ρ.re - σ) ^ k ≤ 1 := pow_le_one₀ hδ0 hδ1
    have h2 : (1 : ℝ) ≤ (Nat.factorial k : ℝ) := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_one (by linarith)]
    linarith
  calc (2 ^ j * D) ^ (-(ρ.re - σ))
        * ‖∑ k ∈ Finset.range (Jpar D + 1),
            (((ρ.re - σ) ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ) * taylorSum χ D σ ρ.im j k
          + remSum χ D σ ρ j‖
      ≤ 1 * (∑ k ∈ Finset.range (Jpar D + 1),
            ‖(((ρ.re - σ) ^ k / (Nat.factorial k : ℝ) : ℝ) : ℂ) * taylorSum χ D σ ρ.im j k‖
          + ‖remSum χ D σ ρ j‖) := by
        refine mul_le_mul hpow1 ((norm_add_le _ _).trans ?_) (norm_nonneg _) zero_le_one
        exact add_le_add (norm_sum_le _ _) le_rfl
    _ ≤ ∑ k ∈ Finset.range (Jpar D + 1), ‖taylorSum χ D σ ρ.im j k‖ + ‖remSum χ D σ ρ j‖ := by
        rw [one_mul]
        refine add_le_add (Finset.sum_le_sum fun k _ => ?_) le_rfl
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
        exact mul_le_of_le_one_left (norm_nonneg _) (hck k)

/-- The Taylor remainder on a block: `|r_n| ≤ (1/5)^{J+1}` for `0 ≤ δ ≤ 11/50`, `N < n ≤ 2N`. -/
lemma abs_taylorRem_le {δ Nb : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 11/50) (hN : 0 < Nb) {n : ℕ}
    (hn1 : Nb < n) (hn2 : (n : ℝ) ≤ 2 * Nb) {J : ℕ} (hJ : 3 ≤ J) :
    |taylorRem δ Nb J n| ≤ (1/5 : ℝ) ^ (J + 1) := by
  have hq1 : 1 < (n : ℝ) / Nb := (one_lt_div hN).mpr hn1
  have hq2 : (n : ℝ) / Nb ≤ 2 := by rw [div_le_iff₀ hN]; linarith
  have hlog0 : 0 ≤ Real.log ((n : ℝ) / Nb) := Real.log_nonneg hq1.le
  have hlog2 : Real.log ((n : ℝ) / Nb) ≤ Real.log 2 := Real.log_le_log (by linarith) hq2
  have hl2 := Real.log_two_lt_d9
  set x : ℝ := δ * (-(Real.log ((n : ℝ) / Nb))) with hx
  have hxabs : |x| ≤ 1/6 := by
    rw [hx, abs_mul, abs_of_nonneg hδ0, abs_neg, abs_of_nonneg hlog0]
    nlinarith
  have hsum : ∑ k ∈ Finset.range (J + 1), δ ^ k / (Nat.factorial k : ℝ)
      * (-(Real.log ((n : ℝ) / Nb))) ^ k
      = ∑ k ∈ Finset.range (J + 1), x ^ k / (Nat.factorial k : ℝ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hx, mul_pow]; ring
  rw [taylorRem, hsum]
  exact taylor_remainder_le hxabs hJ

/-- Pointwise bound on the remainder summand. -/
lemma norm_remTerm_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {D : ℝ} (hD : 0 < D)
    {σ : ℝ} (hσ : 0 ≤ σ) {ρ : ℂ} (hβ : σ ≤ ρ.re) (hβ1 : ρ.re ≤ σ + 11/50)
    (hJ : 3 ≤ Jpar D) {j n : ℕ} (hn : 1 ≤ n) :
    ‖remTerm χ D σ ρ j n‖
      ≤ if n ≤ ⌊2 * (2 ^ j * D)⌋₊ then
          (1/5 : ℝ) ^ (Jpar D + 1) * (2 ^ j * D) ^ (-σ) * (n.divisors.card : ℝ)
        else 0 := by
  have hN0 : (0 : ℝ) < 2 ^ j * D := by positivity
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2N : (2 : ℝ) ^ (j + 1) * D = 2 * (2 ^ j * D) := by ring
  rw [remTerm]
  split_ifs with hb hfl hfl
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
      mul_one]
    have hχ : ‖χ ((n : ℕ) : ZMod N)‖ ≤ 1 := χ.norm_le_one _
    have hA : |bvA D (2 * D) n| ≤ (n.divisors.card : ℝ) :=
      abs_bvA_le_card_divisors hD (by linarith) n
    have hexp : Real.exp (-(n : ℝ) / Ypar D) ≤ 1 := by
      rw [Real.exp_le_one_iff, neg_div]
      have := Ypar_pos hD
      have : 0 ≤ (n : ℝ) / Ypar D := by positivity
      linarith
    have hpow : (n : ℝ) ^ (-σ) ≤ (2 ^ j * D) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hN0 hb.1.le (by linarith)
    have hrem : |taylorRem (ρ.re - σ) (2 ^ j * D) (Jpar D) n| ≤ (1/5 : ℝ) ^ (Jpar D + 1) :=
      abs_taylorRem_le (by linarith) (by linarith) hN0 hb.1 (h2N ▸ hb.2) hJ
    have h0 : (0 : ℝ) ≤ (2 ^ j * D) ^ (-σ) := Real.rpow_nonneg hN0.le _
    have h1 : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg hnR.le _
    calc |bvA D (2 * D) n * Real.exp (-(n : ℝ) / Ypar D) * (n : ℝ) ^ (-σ)
          * taylorRem (ρ.re - σ) (2 ^ j * D) (Jpar D) n| * ‖χ ((n : ℕ) : ZMod N)‖
        ≤ |bvA D (2 * D) n * Real.exp (-(n : ℝ) / Ypar D) * (n : ℝ) ^ (-σ)
          * taylorRem (ρ.re - σ) (2 ^ j * D) (Jpar D) n| * 1 :=
          mul_le_mul_of_nonneg_left hχ (abs_nonneg _)
      _ = |bvA D (2 * D) n| * Real.exp (-(n : ℝ) / Ypar D) * (n : ℝ) ^ (-σ)
          * |taylorRem (ρ.re - σ) (2 ^ j * D) (Jpar D) n| := by
          rw [mul_one, abs_mul, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg h1]
      _ ≤ (n.divisors.card : ℝ) * 1 * (2 ^ j * D) ^ (-σ) * (1/5 : ℝ) ^ (Jpar D + 1) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul hA hexp (Real.exp_pos _).le (by positivity))
            hpow h1 (by positivity)) hrem (abs_nonneg _) (by positivity)
      _ = (1/5 : ℝ) ^ (Jpar D + 1) * (2 ^ j * D) ^ (-σ) * (n.divisors.card : ℝ) := by ring
  · exfalso
    exact hfl (Nat.le_floor (h2N ▸ hb.2))
  · rw [norm_zero]
    have h0 : (0 : ℝ) ≤ (2 ^ j * D) ^ (-σ) := Real.rpow_nonneg hN0.le _
    positivity
  · rw [norm_zero]

/-- The remainder numeric clause: for `j < J`, `3/4 ≤ σ ≤ 1`, `𝓛 ≥ 40`,
`(1/5)^{J+1}·N_j^{−σ}·2N_j(1 + log 2N_j) ≤ 1/(8J)`. -/
lemma rem_numeric {D : ℝ} (hD : 1 < D) (hL : 40 ≤ Real.log D) {j : ℕ} (hj : j < Jpar D)
    {σ : ℝ} (hσ : 3/4 ≤ σ) (_hσ1 : σ ≤ 1) :
    (1/5 : ℝ) ^ (Jpar D + 1)
      * ((2 ^ j * D) ^ (-σ) * (2 * (2 ^ j * D) * (1 + Real.log (2 * (2 ^ j * D)))))
      ≤ 1 / (8 * (Jpar D : ℝ)) := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hL0 : (0 : ℝ) ≤ Real.log D := by linarith
  set Nb : ℝ := 2 ^ j * D with hNb
  have hN0 : 0 < Nb := by positivity
  have hN1 : 1 ≤ Nb := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hD.le
  have hJ1 : (1 : ℝ) ≤ Jpar D := by exact_mod_cast one_le_Jpar (by linarith)
  have hJ2 : (Jpar D : ℝ) ≤ 2 * Real.log D := Jpar_le_two_mul (by linarith)
  -- (a) `N ≤ D^{17/10}`
  have hjL : (j : ℝ) ≤ Real.log D := by
    have h1 : ((j : ℕ) : ℝ) + 1 ≤ (Jpar D : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hj
    have h2 := Jpar_le hL0
    linarith
  have h2j : (2 : ℝ) ^ j ≤ D ^ (7/10 : ℝ) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos hD0]
    apply Real.exp_le_exp.mpr
    have := Real.log_two_lt_d9
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    nlinarith
  have hNle : Nb ≤ D ^ (17/10 : ℝ) := by
    calc Nb = 2 ^ j * D := rfl
      _ ≤ D ^ (7/10 : ℝ) * D := mul_le_mul_of_nonneg_right h2j hD0.le
      _ = D ^ (17/10 : ℝ) := by rw [← Real.rpow_add_one hD0.ne']; norm_num
  -- (b) `N^{−σ}·N = N^{1−σ} ≤ D^{17/40}`
  have hb : Nb ^ (-σ) * Nb = Nb ^ (1 - σ) := by
    rw [← Real.rpow_add_one hN0.ne']; congr 1; ring
  have hb2 : Nb ^ (1 - σ) ≤ D ^ (17/40 : ℝ) := by
    calc Nb ^ (1 - σ) ≤ Nb ^ (1/4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ ≤ (D ^ (17/10 : ℝ)) ^ (1/4 : ℝ) := Real.rpow_le_rpow hN0.le hNle (by norm_num)
      _ = D ^ (17/40 : ℝ) := by rw [← Real.rpow_mul hD0.le]; norm_num
  -- (c) `1 + log(2N) ≤ 2 log D`
  have hc : 1 + Real.log (2 * Nb) ≤ 2 * Real.log D := by
    rw [Real.log_mul two_ne_zero hN0.ne']
    have hlogN : Real.log Nb ≤ (17/10 : ℝ) * Real.log D := by
      calc Real.log Nb ≤ Real.log (D ^ (17/10 : ℝ)) := Real.log_le_log hN0 hNle
        _ = (17/10 : ℝ) * Real.log D := Real.log_rpow hD0 _
    have := Real.log_two_lt_d9
    linarith
  have hc0 : 0 ≤ 1 + Real.log (2 * Nb) := by
    have : 0 ≤ Real.log (2 * Nb) := Real.log_nonneg (by linarith)
    linarith
  -- (d) `(1/5)^{J+1} ≤ D^{−1386/1000}`
  have hd : (1/5 : ℝ) ^ (Jpar D + 1) ≤ D ^ (-(1386/1000 : ℝ)) := by
    have hlog4 : (1386/1000 : ℝ) ≤ Real.log 4 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_gt_d9
      linarith
    have h5 : D ^ (1386/1000 : ℝ) ≤ (5 : ℝ) ^ (Jpar D + 1) := by
      calc D ^ (1386/1000 : ℝ) ≤ D ^ (Real.log 4) :=
            Real.rpow_le_rpow_of_exponent_le hD.le hlog4
        _ = (4 : ℝ) ^ (Real.log D) := by
            rw [Real.rpow_def_of_pos hD0, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4),
              mul_comm]
        _ ≤ (4 : ℝ) ^ (((Jpar D + 1 : ℕ) : ℝ)) := by
            refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
            have := log_le_Jpar D
            push_cast; linarith
        _ = (4 : ℝ) ^ (Jpar D + 1) := Real.rpow_natCast _ _
        _ ≤ (5 : ℝ) ^ (Jpar D + 1) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    rw [Real.rpow_neg hD0.le, one_div_pow, one_div]
    exact inv_anti₀ (Real.rpow_pos_of_pos hD0 _) h5
  -- (e) combine
  have hfac2 : 2 * (Nb ^ (-σ) * Nb) * (1 + Real.log (2 * Nb))
      ≤ 2 * D ^ (17/40 : ℝ) * (2 * Real.log D) := by
    rw [hb]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hb2 (by norm_num)) hc hc0 (by positivity)
  have hfac2' : 0 ≤ 2 * (Nb ^ (-σ) * Nb) * (1 + Real.log (2 * Nb)) := by
    have : 0 ≤ Nb ^ (-σ) := Real.rpow_nonneg hN0.le _
    positivity
  have hP : (64 : ℝ) * Real.log D ^ 2 ≤ D ^ (961/1000 : ℝ) := by
    rw [Real.rpow_def_of_pos hD0,
      show Real.log D * (961/1000 : ℝ) = (961/1000 : ℝ) * Real.log D by ring]
    exact numeric_taylor hL
  have hP0 : (0 : ℝ) < D ^ (961/1000 : ℝ) := Real.rpow_pos_of_pos hD0 _
  calc (1/5 : ℝ) ^ (Jpar D + 1) * (Nb ^ (-σ) * (2 * Nb * (1 + Real.log (2 * Nb))))
      = (1/5 : ℝ) ^ (Jpar D + 1) * (2 * (Nb ^ (-σ) * Nb) * (1 + Real.log (2 * Nb))) := by ring
    _ ≤ D ^ (-(1386/1000 : ℝ)) * (2 * D ^ (17/40 : ℝ) * (2 * Real.log D)) :=
        mul_le_mul hd hfac2 hfac2' (Real.rpow_nonneg hD0.le _)
    _ = 4 * Real.log D * (D ^ (-(1386/1000 : ℝ)) * D ^ (17/40 : ℝ)) := by ring
    _ = 4 * Real.log D * D ^ (-(961/1000 : ℝ)) := by rw [← Real.rpow_add hD0]; norm_num
    _ = 4 * Real.log D / D ^ (961/1000 : ℝ) := by rw [Real.rpow_neg hD0.le]; ring
    _ ≤ 1 / (8 * (Jpar D : ℝ)) := by
        rw [div_le_div_iff₀ hP0 (by positivity)]
        nlinarith

/-- `‖R_j‖ ≤ 1/(8J)` for every block `j < J`. -/
lemma norm_remSum_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {D : ℝ} (hD : 1 < D)
    (hL : 40 ≤ Real.log D) {σ : ℝ} (hσ : 39/50 ≤ σ) (hσ1 : σ ≤ 1) {ρ : ℂ} (hβ : σ ≤ ρ.re)
    (hβ1 : ρ.re ≤ 1) {j : ℕ} (hj : j < Jpar D) :
    ‖remSum χ D σ ρ j‖ ≤ 1 / (8 * (Jpar D : ℝ)) := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hJ3 : 3 ≤ Jpar D := by
    have := log_le_Jpar D
    exact_mod_cast (show (3 : ℝ) ≤ Jpar D by linarith)
  set Nb : ℝ := 2 ^ j * D with hNb
  have hN0 : 0 < Nb := by positivity
  have hN1 : 1 ≤ Nb := one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hD.le
  set M2 : ℕ := ⌊2 * Nb⌋₊ with hM2
  set c : ℝ := (1/5 : ℝ) ^ (Jpar D + 1) * Nb ^ (-σ) with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ Nb ^ (-σ) := Real.rpow_nonneg hN0.le _
    positivity
  have hpt : ∀ n ∈ Finset.Icc 1 (Nmax D), ‖remTerm χ D σ ρ j n‖
      ≤ if n ≤ M2 then c * (n.divisors.card : ℝ) else 0 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact norm_remTerm_le χ hD0 (by linarith) hβ (by linarith) hJ3 hn.1
  have hM2le : (M2 : ℝ) ≤ 2 * Nb := Nat.floor_le (by positivity)
  have hM2pos : 1 ≤ M2 := Nat.le_floor (by push_cast; linarith)
  have hM2R : (1 : ℝ) ≤ M2 := by exact_mod_cast hM2pos
  calc ‖remSum χ D σ ρ j‖ ≤ ∑ n ∈ Finset.Icc 1 (Nmax D), ‖remTerm χ D σ ρ j n‖ :=
        norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 (Nmax D), (if n ≤ M2 then c * (n.divisors.card : ℝ) else 0) :=
        Finset.sum_le_sum hpt
    _ = ∑ n ∈ (Finset.Icc 1 (Nmax D)).filter (fun n => n ≤ M2), c * (n.divisors.card : ℝ) :=
        (Finset.sum_filter _ _).symm
    _ ≤ ∑ n ∈ Finset.Icc 1 M2, c * (n.divisors.card : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => by positivity
        intro n hn
        rw [Finset.mem_filter, Finset.mem_Icc] at hn
        rw [Finset.mem_Icc]
        exact ⟨hn.1.1, hn.2⟩
    _ = c * ∑ n ∈ Finset.Icc 1 M2, (n.divisors.card : ℝ) := by rw [Finset.mul_sum]
    _ ≤ c * (M2 * (1 + Real.log M2)) :=
        mul_le_mul_of_nonneg_left (sum_card_divisors_le M2) hc0
    _ ≤ c * (2 * Nb * (1 + Real.log (2 * Nb))) := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        have hlog : Real.log M2 ≤ Real.log (2 * Nb) := Real.log_le_log (by linarith) hM2le
        have hlog0 : 0 ≤ Real.log M2 := Real.log_nonneg hM2R
        nlinarith
    _ = (1/5 : ℝ) ^ (Jpar D + 1)
        * (Nb ^ (-σ) * (2 * Nb * (1 + Real.log (2 * Nb)))) := by rw [hc]; ring
    _ ≤ 1 / (8 * (Jpar D : ℝ)) := rem_numeric hD hL hj (by linarith) hσ1

/-! ## §5.  The pigeonholes and L1.e -/

/-- Block pigeonhole: `‖S‖ ≥ 1/4` forces some `‖S_j‖ ≥ 1/(4J)`. -/
lemma exists_block_large {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {D : ℝ} (hD : 1 < D)
    (hL : 40 ≤ Real.log D) (ρ : ℂ)
    (h : 1/4 ≤ ‖∑ n ∈ Finset.Icc 1 (Nmax D), truncTerm χ D ρ n‖) :
    ∃ j < Jpar D, 1 / (4 * (Jpar D : ℝ)) ≤ ‖blockSum χ D ρ j‖ := by
  rw [sum_truncTerm_eq_sum_blockSum χ hD hL ρ] at h
  have hJ1 : 1 ≤ Jpar D := one_le_Jpar (by linarith)
  have hJR : (0 : ℝ) < Jpar D := by exact_mod_cast hJ1
  have hsum : ∑ _j ∈ Finset.range (Jpar D), 1 / (4 * (Jpar D : ℝ))
      ≤ ∑ j ∈ Finset.range (Jpar D), ‖blockSum χ D ρ j‖ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc (Jpar D : ℝ) * (1 / (4 * (Jpar D : ℝ))) = 1/4 := by field_simp
      _ ≤ ‖∑ j ∈ Finset.range (Jpar D), blockSum χ D ρ j‖ := h
      _ ≤ ∑ j ∈ Finset.range (Jpar D), ‖blockSum χ D ρ j‖ := norm_sum_le _ _
  obtain ⟨j, hj, hle⟩ :=
    Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr (by omega)) hsum
  exact ⟨j, Finset.mem_range.mp hj, hle⟩

/-- Taylor pigeonhole: `‖S_j‖ ≥ 1/(4J)` forces some `‖T_{j,k}‖ ≥ 1/(8J(J+1))`. -/
lemma exists_taylor_index_large {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {D : ℝ}
    (hD : 1 < D) (hL : 40 ≤ Real.log D) {σ : ℝ} (hσ : 39/50 ≤ σ) (hσ1 : σ ≤ 1) {ρ : ℂ}
    (hβ : σ ≤ ρ.re) (hβ1 : ρ.re ≤ 1) {j : ℕ} (hj : j < Jpar D)
    (h : 1 / (4 * (Jpar D : ℝ)) ≤ ‖blockSum χ D ρ j‖) :
    ∃ k ≤ Jpar D, 1 / (8 * (Jpar D : ℝ) * ((Jpar D : ℝ) + 1)) ≤ ‖taylorSum χ D σ ρ.im j k‖ := by
  have hJ1 : 1 ≤ Jpar D := one_le_Jpar (by linarith)
  have hJR : (0 : ℝ) < Jpar D := by exact_mod_cast hJ1
  have h1 := norm_blockSum_le χ hD.le hβ hβ1 (by linarith) j
  have h2 := norm_remSum_le χ hD hL hσ hσ1 hβ hβ1 hj
  have h3 : 1 / (4 * (Jpar D : ℝ)) = 2 * (1 / (8 * (Jpar D : ℝ))) := by field_simp; ring
  have hsum : ∑ _k ∈ Finset.range (Jpar D + 1), 1 / (8 * (Jpar D : ℝ) * ((Jpar D : ℝ) + 1))
      ≤ ∑ k ∈ Finset.range (Jpar D + 1), ‖taylorSum χ D σ ρ.im j k‖ := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    calc ((Jpar D : ℝ) + 1) * (1 / (8 * (Jpar D : ℝ) * ((Jpar D : ℝ) + 1)))
        = 1 / (8 * (Jpar D : ℝ)) := by field_simp
      _ ≤ ∑ k ∈ Finset.range (Jpar D + 1), ‖taylorSum χ D σ ρ.im j k‖ := by linarith
  obtain ⟨k, hk, hle⟩ :=
    Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero _)) hsum
  exact ⟨k, Nat.lt_succ_iff.mp (Finset.mem_range.mp hk), hle⟩

lemma coeffJK_eq_zero_of_not_mem_Icc_Nmax {D σ : ℝ} (hD : 0 < D) {j k n : ℕ}
    (h : n ∉ Finset.Icc 1 (Nmax D)) : coeffJK D σ j k n = 0 := by
  rw [Finset.mem_Icc] at h
  rw [coeffJK, if_neg]
  rintro ⟨h1, -, h3⟩
  have hn : 0 < n := by
    by_contra h0
    push Not at h0
    have : n = 0 := by omega
    subst this
    have : (0 : ℝ) < 2 ^ j * D := by positivity
    simp at h1
    linarith
  exact h ⟨hn, h3⟩

lemma coeffJK_eq_zero_of_not_mem_blockRange {D σ : ℝ} (hD : 0 < D) {j k n : ℕ}
    (h : n ∉ blockRange D j) : coeffJK D σ j k n = 0 := by
  rw [blockRange, Finset.mem_Icc] at h
  rw [coeffJK, if_neg]
  rintro ⟨h1, h2, -⟩
  have hn : 0 < n := by
    by_contra h0
    push Not at h0
    have : n = 0 := by omega
    subst this
    have : (0 : ℝ) < 2 ^ j * D := by positivity
    simp at h1
    linarith
  have hn2 : n ≤ ⌈2 ^ (j + 1) * D⌉₊ := by
    by_contra hlt
    push Not at hlt
    have h1 : ((⌈2 ^ (j + 1) * D⌉₊ : ℕ) : ℝ) < n := by exact_mod_cast hlt
    have h2' := Nat.le_ceil (2 ^ (j + 1) * D)
    linarith
  exact h ⟨hn, hn2⟩

/-- The Taylor component over `Icc 1 (Nmax D)` equals the LV1-shaped sum over
`blockRange D j` (audit F1): both ranges contain the support of `coeffJK D σ j k`. -/
lemma taylorSum_eq_blockRange {N : ℕ} (χ : DirichletCharacter ℂ N) {D : ℝ} (hD : 0 < D)
    (σ γ : ℝ) (j k : ℕ) :
    taylorSum χ D σ γ j k
      = ∑ n ∈ blockRange D j,
          coeffJK D σ j k n * χ n * Complex.exp ((-Real.log n * γ : ℝ) * Complex.I) := by
  unfold taylorSum
  have h1 : ∑ n ∈ Finset.Icc 1 (Nmax D) ∩ blockRange D j,
      coeffJK D σ j k n * χ n * Complex.exp ((-Real.log n * γ : ℝ) * Complex.I)
      = ∑ n ∈ Finset.Icc 1 (Nmax D),
      coeffJK D σ j k n * χ n * Complex.exp ((-Real.log n * γ : ℝ) * Complex.I) := by
    refine Finset.sum_subset Finset.inter_subset_left fun n hn hn' => ?_
    have : n ∉ blockRange D j := fun h => hn' (Finset.mem_inter.mpr ⟨hn, h⟩)
    rw [coeffJK_eq_zero_of_not_mem_blockRange hD this]; ring
  have h2 : ∑ n ∈ Finset.Icc 1 (Nmax D) ∩ blockRange D j,
      coeffJK D σ j k n * χ n * Complex.exp ((-Real.log n * γ : ℝ) * Complex.I)
      = ∑ n ∈ blockRange D j,
      coeffJK D σ j k n * χ n * Complex.exp ((-Real.log n * γ : ℝ) * Complex.I) := by
    refine Finset.sum_subset Finset.inter_subset_right fun n hn hn' => ?_
    have : n ∉ Finset.Icc 1 (Nmax D) := fun h => hn' (Finset.mem_inter.mpr ⟨h, hn⟩)
    rw [coeffJK_eq_zero_of_not_mem_Icc_Nmax hD this]; ring
  rw [← h1, h2]

/-- **L1.e** (Proposition 2.8, the LV1-shaped detector lemma).  For a zero `ρ` of
`L(·,χ)` with `σ ≤ Re ρ ≤ 1` (and `|Im ρ| ≥ log D` if `χ = χ₀`): either the contour term
is large, `‖E_ctr‖ ≥ 1/4`, or some Taylor component `T_{j,k}` (`j < J`, `k ≤ J`) has
modulus `≥ 1/(8J(J+1))`.  DELTA vs. §6.1: the hypothesis `1 < D` is added (`40 ≤ log D`
alone does not exclude `D < 0`, cf. `Real.log_neg_eq_log`). -/
theorem detector_large_value {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {D σ : ℝ} (hD : 1 < D) (hL : 40 ≤ Real.log D) (hσ : 39/50 ≤ σ) (hσ1 : σ ≤ 1)
    {ρ : ℂ} (hβ : σ ≤ ρ.re) (hβ1 : ρ.re ≤ 1) (hρ1 : χ = 1 → Real.log D ≤ |ρ.im|)
    (hLρ : DirichletCharacter.LFunction χ ρ = 0) :
    1/4 ≤ ‖EctrHalf χ D (Ypar D) ρ‖ ∨
    ∃ j < Jpar D, ∃ k ≤ Jpar D,
      1 / (8 * (Jpar D : ℝ) * ((Jpar D : ℝ) + 1)) ≤
        ‖∑ n ∈ blockRange D j, coeffJK D σ j k n * χ n
            * Complex.exp ((-Real.log n * ρ.im : ℝ) * Complex.I)‖ := by
  have hD0 : (0 : ℝ) < D := by linarith
  by_cases hE : 1/4 ≤ ‖EctrHalf χ D (Ypar D) ρ‖
  · exact Or.inl hE
  right
  push Not at hE
  have hβ' : 39/50 ≤ ρ.re := hσ.trans hβ
  have hρ1' : χ = 1 → ρ ≠ 1 := by
    intro hχ hρ
    have := hρ1 hχ
    rw [hρ, Complex.one_im, abs_zero] at this
    linarith
  have hid := detection_identity_half χ hD hβ' hβ1 hρ1' hLρ
  have hpole : ‖Epole χ D (2 * D) 1 (Ypar D) ρ‖ ≤ 1/8 := by
    by_cases hχ : χ = 1
    · subst hχ
      exact norm_Epole_le_of_height N hL hσ hβ hβ1 (hρ1 rfl)
    · rw [Epole_one_eq, if_neg hχ, norm_zero]; norm_num
  have hexp : (3/4 : ℝ) ≤ Real.exp (-1 / Ypar D) := by
    have hY4 := four_le_Ypar hD0 hL
    have h1 := Real.add_one_le_exp (-1 / Ypar D)
    have h2 : -(1/4 : ℝ) ≤ -1 / Ypar D := by
      rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by linarith)]
      linarith
    linarith
  have htr : ‖Fdet χ D (2 * D) 1 (Ypar D) ρ - ∑ n ∈ Finset.Icc 1 (Nmax D), truncTerm χ D ρ n‖
      ≤ 1/8 := norm_Fdet_sub_truncation_le χ hD hL hβ' hβ1
  -- `‖F‖ ≥ 3/8`
  have hF : 3/8 ≤ ‖Fdet χ D (2 * D) 1 (Ypar D) ρ‖ := by
    have h3 : ((Real.exp (-1 / Ypar D) : ℝ) : ℂ)
        = EctrHalf χ D (Ypar D) ρ + Epole χ D (2 * D) 1 (Ypar D) ρ
          - Fdet χ D (2 * D) 1 (Ypar D) ρ := by rw [← hid]; ring
    have h2 : ‖((Real.exp (-1 / Ypar D) : ℝ) : ℂ)‖ = Real.exp (-1 / Ypar D) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have h4 := norm_sub_le (EctrHalf χ D (Ypar D) ρ + Epole χ D (2 * D) 1 (Ypar D) ρ)
      (Fdet χ D (2 * D) 1 (Ypar D) ρ)
    have h5 := norm_add_le (EctrHalf χ D (Ypar D) ρ) (Epole χ D (2 * D) 1 (Ypar D) ρ)
    rw [← h3, h2] at h4
    linarith
  -- `‖S‖ ≥ 1/4`
  have hS : 1/4 ≤ ‖∑ n ∈ Finset.Icc 1 (Nmax D), truncTerm χ D ρ n‖ := by
    have h := norm_sub_norm_le (Fdet χ D (2 * D) 1 (Ypar D) ρ)
      (∑ n ∈ Finset.Icc 1 (Nmax D), truncTerm χ D ρ n)
    linarith
  obtain ⟨j, hj, hjl⟩ := exists_block_large χ hD hL ρ hS
  obtain ⟨k, hk, hkl⟩ := exists_taylor_index_large χ hD hL hσ hσ1 hβ hβ1 hj hjl
  refine ⟨j, hj, k, hk, ?_⟩
  rw [← taylorSum_eq_blockRange χ hD0]
  exact hkl

/-! ## §6.  L1.f: the class-II mean square (Lemmas 3.6, 3.7, Corollary 3.8; audit F7) -/

/-- `u ↦ e^{−a|u|}` is integrable for `a > 0`. -/
lemma integrable_exp_neg_abs_mul {a : ℝ} (ha : 0 < a) :
    Integrable (fun u : ℝ => Real.exp (-a * |u|)) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0:ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic ha 0).congr_fun ?_ measurableSet_Iic
    intro x hx
    simp only [Set.mem_Iic] at hx
    show Real.exp (a * x) = Real.exp (-a * |x|)
    rw [abs_of_nonpos hx]; ring_nf
  · refine (integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0).congr_fun ?_ measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    show Real.exp (-a * x) = Real.exp (-a * |x|)
    rw [abs_of_pos hx]

/-- `∫ e^{−a|u|} du = 2/a` for `a > 0`. -/
lemma integral_exp_neg_abs_mul {a : ℝ} (ha : 0 < a) :
    ∫ u : ℝ, Real.exp (-a * |u|) = 2 / a := by
  have h := integral_comp_abs (f := fun t : ℝ => Real.exp (-a * t))
  rw [integral_exp_mul_Ioi (by linarith : -a < 0) 0] at h
  rw [h]
  field_simp
  ring_nf
  simp

/-- `(1+x)² e^{−x} ≤ 8 e^{−x/2}` for `x ≥ 0`. -/
lemma weight_sq_le {x : ℝ} (_hx : 0 ≤ x) :
    (1 + x) ^ 2 * Real.exp (-x) ≤ 8 * Real.exp (-(1/2) * x) := by
  have h1 : 1 + x / 2 + (x / 2) ^ 2 / 2 ≤ Real.exp (x / 2) :=
    Real.quadratic_le_exp_of_nonneg (by linarith)
  have h2 : Real.exp (-x) = Real.exp (-(1/2) * x) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-(x / 2)) * Real.exp (x / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-(1/2) * x) := Real.exp_pos _
  have hpos2 : 0 < Real.exp (-(x / 2)) := Real.exp_pos _
  rw [h2]
  have h4 : (1 + x) ^ 2 * Real.exp (-(x / 2)) ≤ 8 := by
    have h5 : (1 + x) ^ 2 ≤ 8 * Real.exp (x / 2) := by nlinarith
    calc (1 + x) ^ 2 * Real.exp (-(x / 2)) ≤ 8 * Real.exp (x / 2) * Real.exp (-(x / 2)) :=
          mul_le_mul_of_nonneg_right h5 hpos2.le
      _ = 8 := by rw [mul_assoc, mul_comm (Real.exp (x / 2)), h3, mul_one]
  calc (1 + x) ^ 2 * (Real.exp (-(1/2) * x) * Real.exp (-(x / 2)))
      = ((1 + x) ^ 2 * Real.exp (-(x / 2))) * Real.exp (-(1/2) * x) := by ring
    _ ≤ 8 * Real.exp (-(1/2) * x) := mul_le_mul_of_nonneg_right h4 hpos.le

/-- `(3 + x) e^{−x/2} ≤ 4 e^{−x/4}` for `x ≥ 0`. -/
lemma weight_lin_le {x : ℝ} (_hx : 0 ≤ x) :
    (3 + x) * Real.exp (-(1/2) * x) ≤ 4 * Real.exp (-(1/4) * x) := by
  have h1 : x / 4 + 1 ≤ Real.exp (x / 4) := Real.add_one_le_exp _
  have h2 : Real.exp (-(1/2) * x) = Real.exp (-(1/4) * x) * Real.exp (-(x / 4)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h3 : Real.exp (-(x / 4)) * Real.exp (x / 4) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-(1/4) * x) := Real.exp_pos _
  have hpos2 : 0 < Real.exp (-(x / 4)) := Real.exp_pos _
  have h4 : (3 + x) * Real.exp (-(x / 4)) ≤ 4 := by
    have h5 : 3 + x ≤ 4 * Real.exp (x / 4) := by nlinarith
    calc (3 + x) * Real.exp (-(x / 4)) ≤ 4 * Real.exp (x / 4) * Real.exp (-(x / 4)) :=
          mul_le_mul_of_nonneg_right h5 hpos2.le
      _ = 4 := by rw [mul_assoc, mul_comm (Real.exp (x / 4)), h3, mul_one]
  rw [h2]
  calc (3 + x) * (Real.exp (-(1/4) * x) * Real.exp (-(x / 4)))
      = ((3 + x) * Real.exp (-(x / 4))) * Real.exp (-(1/4) * x) := by ring
    _ ≤ 4 * Real.exp (-(1/4) * x) := mul_le_mul_of_nonneg_right h4 hpos.le

/-- The mollifier `M(ρ + c + iu, χ)` is continuous in `u`. -/
lemma continuous_Mr_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z1 z2 : ℝ) (ρ : ℂ)
    (c : ℝ) :
    Continuous (fun u : ℝ => Mr χ z1 z2 1 (ρ + ((c : ℂ) + (u : ℂ) * Complex.I))) := by
  simp only [Mr_one_eq]
  refine continuous_finsetSum _ fun δ hδ => ?_
  rw [Finset.mem_Icc] at hδ
  have hδ0 : (δ : ℂ) ≠ 0 := by exact_mod_cast (by omega : δ ≠ 0)
  have hinner : Continuous (fun u : ℝ => -(ρ + ((c : ℂ) + (u : ℂ) * Complex.I))) := by fun_prop
  exact (continuous_const.mul continuous_const).mul (hinner.const_cpow (Or.inl hδ0))

/-- Trivial bound: `‖M(s,χ)‖ ≤ ⌊z₂⌋₊` for `Re s ≥ 0`. -/
lemma norm_Mr_one_le_card {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {z1 z2 : ℝ}
    (hz1 : 0 < z1) (hz12 : z1 < z2) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖Mr χ z1 z2 1 s‖ ≤ (⌊z2⌋₊ : ℝ) := by
  rw [Mr_one_eq]
  calc ‖∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊, ((bvLam z1 z2 δ : ℝ) : ℂ) * χ δ * (δ : ℂ) ^ (-s)‖
      ≤ ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊, ‖((bvLam z1 z2 δ : ℝ) : ℂ) * χ δ * (δ : ℂ) ^ (-s)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _δ ∈ Finset.Icc 1 ⌊z2⌋₊, (1 : ℝ) := by
        refine Finset.sum_le_sum fun δ hδ => ?_
        rw [Finset.mem_Icc] at hδ
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_natCast_cpow_of_pos (by omega)]
        have h1 := abs_bvLam_le_one hz1 hz12 δ
        have h2 : ‖χ ((δ : ℕ) : ZMod N)‖ ≤ 1 := χ.norm_le_one _
        have h3 : (δ : ℝ) ^ (-s).re ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hδ.1) (by simp [hs])
        calc |bvLam z1 z2 δ| * ‖χ ((δ : ℕ) : ZMod N)‖ * (δ : ℝ) ^ (-s).re
            ≤ 1 * 1 * 1 := by
              refine mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3 ?_ (by norm_num)
              exact Real.rpow_nonneg (Nat.cast_nonneg δ) _
          _ = 1 := by ring
    _ = (⌊z2⌋₊ : ℝ) := by simp

/-- Cauchy–Schwarz against the weight `w = e^{−|u|/2}` (`∫ w = 4`), in the elementary
parametric form: `(∫ w f)² ≤ 4 ∫ w f²` for `f ≥ 0`. -/
lemma sq_integral_weight_le {f : ℝ → ℝ} (hf0 : ∀ u, 0 ≤ f u)
    (hf2 : Integrable (fun u => Real.exp (-(1/2) * |u|) * f u ^ 2)) :
    (∫ u, Real.exp (-(1/2) * |u|) * f u) ^ 2 ≤ 4 * ∫ u, Real.exp (-(1/2) * |u|) * f u ^ 2 := by
  have hw := integrable_exp_neg_abs_mul (a := 1/2) (by norm_num)
  have hwint : ∫ u : ℝ, Real.exp (-(1/2) * |u|) = 4 := by
    rw [integral_exp_neg_abs_mul (by norm_num)]; norm_num
  set I1 := ∫ u, Real.exp (-(1/2) * |u|) * f u with hI1
  set I2 := ∫ u, Real.exp (-(1/2) * |u|) * f u ^ 2 with hI2
  have hI1nn : 0 ≤ I1 :=
    integral_nonneg fun u => mul_nonneg (Real.exp_pos _).le (hf0 u)
  have hI2nn : 0 ≤ I2 :=
    integral_nonneg fun u => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  -- the parametric AM–GM bound `I1 ≤ 2/ε + (ε/2) I2`
  have key : ∀ ε : ℝ, 0 < ε → I1 ≤ 2 / ε + ε / 2 * I2 := by
    intro ε hε
    have hpt : ∀ u, Real.exp (-(1/2) * |u|) * f u
        ≤ (1 / (2 * ε)) * Real.exp (-(1/2) * |u|) + (ε / 2) * (Real.exp (-(1/2) * |u|) * f u ^ 2) := by
      intro u
      have hw0 : 0 ≤ Real.exp (-(1/2) * |u|) := (Real.exp_pos _).le
      have hsq : 0 ≤ (1 / ε - f u) ^ 2 := sq_nonneg _
      have hmul : f u ≤ 1 / (2 * ε) + (ε / 2) * f u ^ 2 := by
        have h1 : (1 / ε - f u) ^ 2 = 1 / ε ^ 2 - 2 * (f u) / ε + f u ^ 2 := by
          field_simp; ring
        rw [h1] at hsq
        have h2 : 0 ≤ ε * (1 / ε ^ 2 - 2 * f u / ε + f u ^ 2) := mul_nonneg hε.le hsq
        have h3 : ε * (1 / ε ^ 2 - 2 * f u / ε + f u ^ 2) = 1 / ε - 2 * f u + ε * f u ^ 2 := by
          field_simp
        rw [h3] at h2
        have h4 : 1 / (2 * ε) = (1 / ε) / 2 := by field_simp
        rw [h4]; linarith
      calc Real.exp (-(1/2) * |u|) * f u
          ≤ Real.exp (-(1/2) * |u|) * (1 / (2 * ε) + (ε / 2) * f u ^ 2) :=
            mul_le_mul_of_nonneg_left hmul hw0
        _ = (1 / (2 * ε)) * Real.exp (-(1/2) * |u|)
            + (ε / 2) * (Real.exp (-(1/2) * |u|) * f u ^ 2) := by ring
    have hint : ∫ u, ((1 / (2 * ε)) * Real.exp (-(1/2) * |u|)
        + (ε / 2) * (Real.exp (-(1/2) * |u|) * f u ^ 2)) = 2 / ε + ε / 2 * I2 := by
      rw [integral_add (hw.const_mul _) (hf2.const_mul _), integral_const_mul,
        integral_const_mul, hwint]
      ring
    calc I1 ≤ ∫ u, ((1 / (2 * ε)) * Real.exp (-(1/2) * |u|)
          + (ε / 2) * (Real.exp (-(1/2) * |u|) * f u ^ 2)) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun u =>
              mul_nonneg (Real.exp_pos _).le (hf0 u))
            ((hw.const_mul _).add (hf2.const_mul _)) (Filter.Eventually.of_forall hpt)
      _ = 2 / ε + ε / 2 * I2 := hint
  rcases eq_or_lt_of_le hI2nn with hI2z | hI2pos
  · -- `I2 = 0`: `I1 ≤ 2/ε` for all `ε`, so `I1 = 0`
    have hI1z : I1 ≤ 0 := by
      by_contra hcon
      push Not at hcon
      have := key (4 / I1) (by positivity)
      rw [← hI2z] at this
      have h1 : 2 / (4 / I1) = I1 / 2 := by field_simp; ring
      rw [h1] at this
      linarith
    have : I1 = 0 := le_antisymm hI1z hI1nn
    rw [this]; nlinarith
  · have hs : 0 < Real.sqrt I2 := Real.sqrt_pos.mpr hI2pos
    have hs2 : Real.sqrt I2 ^ 2 = I2 := Real.sq_sqrt hI2nn
    have := key (2 / Real.sqrt I2) (by positivity)
    have h1 : 2 / (2 / Real.sqrt I2) + 2 / Real.sqrt I2 / 2 * I2 = 2 * Real.sqrt I2 := by
      field_simp
      nlinarith
    rw [h1] at this
    calc I1 ^ 2 ≤ (2 * Real.sqrt I2) ^ 2 := pow_le_pow_left₀ hI1nn this 2
      _ = 4 * I2 := by rw [mul_pow, hs2]; norm_num

/-- The class-II constant `K = 8·201·C_Γ·6·10⁵·C_τ·D^{201/800}·log D·Y^{1/2−σ}` of Lemma 3.6. -/
noncomputable def Kcls (D σ : ℝ) : ℝ :=
  8 * (201 * GammaStrip.CGamma) * (600000 * Ctau * D ^ (201/800 : ℝ) * Real.log D)
    * Ypar D ^ (1/2 - σ)

lemma Kcls_nonneg {D σ : ℝ} (hD : 0 < D) (hL : 0 ≤ Real.log D) : 0 ≤ Kcls D σ := by
  have := GammaStrip.CGamma_pos
  have := Ctau_pos
  have h1 : 0 ≤ D ^ (201/800 : ℝ) := Real.rpow_nonneg hD.le _
  have h2 : 0 ≤ Ypar D ^ (1/2 - σ) := Real.rpow_nonneg (Ypar_pos hD).le _
  unfold Kcls
  positivity

/-- **Lemma 3.6, pointwise**: on the half-line, `w = (1/2 − β) + iu`,
`‖Γ(w)Y^w L(ρ+w,χ)M(ρ+w,χ)‖ ≤ K·e^{−|u|/2}·‖M(ρ+w,χ)‖`. -/
lemma norm_ectrInt_half_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {D : ℝ}
    (hD1 : 1 < D) (hLD : 2 ≤ Real.log D) {σ : ℝ} (hσ : 39/50 ≤ σ) {ρ : ℂ} (hβ : σ ≤ ρ.re)
    (hβ1 : ρ.re ≤ 1) (hDN : (N : ℝ) * (|ρ.im| + 2) ≤ D) (u : ℝ) :
    ‖ectrInt χ D (2 * D) (Ypar D) 1 ρ (1/2 - ρ.re) u‖
      ≤ Kcls D σ * Real.exp (-(1/2) * |u|)
        * ‖Mr χ D (2 * D) 1 (ρ + (((1/2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * Complex.I))‖ := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hY := Ypar_pos hD0
  have hCG := GammaStrip.CGamma_pos
  have hCt := Ctau_pos
  rw [ectrInt]
  set c : ℝ := 1/2 - ρ.re with hc
  set w : ℂ := (c : ℂ) + (u : ℂ) * Complex.I with hw
  have hwre : w.re = c := by simp [hw]
  have hwim : w.im = u := by simp [hw]
  have hcneg : c < 0 := by rw [hc]; linarith
  -- Γ
  have hΓ : ‖Complex.Gamma w‖ ≤ 201 * GammaStrip.CGamma * Real.exp (-|u|) := by
    have h3 : 1/100 ≤ ‖w‖ := by
      have := Complex.abs_re_le_norm w
      rw [hwre, abs_of_neg hcneg] at this
      rw [hc] at this
      linarith
    have h4 : 1/100 ≤ ‖w + 1‖ := by
      have := Complex.abs_re_le_norm (w + 1)
      rw [Complex.add_re, hwre, Complex.one_re, abs_of_pos (by rw [hc]; linarith)] at this
      rw [hc] at this
      linarith
    have h := GammaStrip.norm_Gamma_le_of_dist w (by rw [hwre, hc]; linarith)
      (by rw [hwre, hc]; linarith) h3 h4
    rwa [hwim] at h
  -- Y^w
  have hYw : ‖(Ypar D : ℂ) ^ w‖ ≤ Ypar D ^ (1/2 - σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY, hwre]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_Ypar hD1.le) (by rw [hc]; linarith)
  -- L
  have hLb := norm_LFunction_half_le χ hD1 hLD (c := c) (by rw [hc]; ring) hDN u
  have hwt := weight_sq_le (abs_nonneg u)
  have hA0 : 0 ≤ 600000 * Ctau * D ^ (201/800 : ℝ) * Real.log D := by
    have : 0 ≤ D ^ (201/800 : ℝ) := Real.rpow_nonneg hD0.le _
    have : 0 ≤ Real.log D := by linarith
    positivity
  have hY0 : 0 ≤ Ypar D ^ (1/2 - σ) := Real.rpow_nonneg hY.le _
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖Complex.Gamma w‖ * ‖(Ypar D : ℂ) ^ w‖ * ‖DirichletCharacter.LFunction χ (ρ + w)‖
        * ‖Mr χ D (2 * D) 1 (ρ + w)‖
      ≤ (201 * GammaStrip.CGamma * Real.exp (-|u|)) * Ypar D ^ (1/2 - σ)
        * (600000 * Ctau * D ^ (201/800 : ℝ) * Real.log D * (1 + |u|) ^ 2)
        * ‖Mr χ D (2 * D) 1 (ρ + w)‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        refine mul_le_mul (mul_le_mul hΓ hYw (norm_nonneg _) (by positivity)) hLb
          (norm_nonneg _) (by positivity)
    _ = (201 * GammaStrip.CGamma) * (600000 * Ctau * D ^ (201/800 : ℝ) * Real.log D)
        * Ypar D ^ (1/2 - σ) * ((1 + |u|) ^ 2 * Real.exp (-|u|))
        * ‖Mr χ D (2 * D) 1 (ρ + w)‖ := by ring
    _ ≤ (201 * GammaStrip.CGamma) * (600000 * Ctau * D ^ (201/800 : ℝ) * Real.log D)
        * Ypar D ^ (1/2 - σ) * (8 * Real.exp (-(1/2) * |u|))
        * ‖Mr χ D (2 * D) 1 (ρ + w)‖ := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwt ?_) (norm_nonneg _)
        positivity
    _ = Kcls D σ * Real.exp (-(1/2) * |u|) * ‖Mr χ D (2 * D) 1 (ρ + w)‖ := by
        rw [Kcls]; ring

/-- Integrability of `e^{−|u|/2}·‖M(ρ + c + iu)‖^k` for `Re ρ + c ≥ 0`. -/
lemma integrable_weight_norm_Mr_pow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {D : ℝ}
    (hD : 0 < D) {ρ : ℂ} {c : ℝ} (hc : 0 ≤ ρ.re + c) (k : ℕ) :
    Integrable (fun u : ℝ => Real.exp (-(1/2) * |u|)
      * ‖Mr χ D (2 * D) 1 (ρ + ((c : ℂ) + (u : ℂ) * Complex.I))‖ ^ k) := by
  have hw := integrable_exp_neg_abs_mul (a := 1/2) (by norm_num)
  have hcont : Continuous (fun u : ℝ => Real.exp (-(1/2) * |u|)
      * ‖Mr χ D (2 * D) 1 (ρ + ((c : ℂ) + (u : ℂ) * Complex.I))‖ ^ k) := by
    have h1 : Continuous (fun u : ℝ => Real.exp (-(1/2) * |u|)) := by fun_prop
    exact h1.mul ((continuous_Mr_line χ D (2 * D) ρ c).norm.pow k)
  refine Integrable.mono' (hw.const_mul ((⌊2 * D⌋₊ : ℝ) ^ k)) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ k
  refine norm_Mr_one_le_card χ hD (by linarith) ?_
  simp [hc]

/-- **Lemma 3.6**: `‖E_ctr(ρ,χ)‖² ≤ (K/2π)²·4·∫ e^{−|u|/2}‖M(1/2 + i(γ+u),χ)‖² du`. -/
lemma sq_norm_EctrHalf_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {D : ℝ}
    (hD1 : 1 < D) (hLD : 2 ≤ Real.log D) {σ : ℝ} (hσ : 39/50 ≤ σ) {ρ : ℂ} (hβ : σ ≤ ρ.re)
    (hβ1 : ρ.re ≤ 1) (hDN : (N : ℝ) * (|ρ.im| + 2) ≤ D) :
    ‖EctrHalf χ D (Ypar D) ρ‖ ^ 2
      ≤ (Kcls D σ / (2 * π)) ^ 2 * (4 * ∫ u : ℝ, Real.exp (-(1/2) * |u|)
          * ‖Mr χ D (2 * D) 1 (ρ + (((1/2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * Complex.I))‖ ^ 2) := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hK0 : 0 ≤ Kcls D σ := Kcls_nonneg hD0 (by linarith)
  have hc0 : 0 ≤ ρ.re + (1/2 - ρ.re) := by linarith
  have hint1 := integrable_weight_norm_Mr_pow χ hD0 (ρ := ρ) (c := 1/2 - ρ.re) hc0 1
  have hint2 := integrable_weight_norm_Mr_pow χ hD0 (ρ := ρ) (c := 1/2 - ρ.re) hc0 2
  simp only [pow_one] at hint1
  set m : ℝ → ℝ := fun u =>
    ‖Mr χ D (2 * D) 1 (ρ + (((1/2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * Complex.I))‖ with hm
  have h1 : ‖EctrHalf χ D (Ypar D) ρ‖
      ≤ Kcls D σ / (2 * π) * ∫ u : ℝ, Real.exp (-(1/2) * |u|) * m u := by
    rw [EctrHalf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h2 : ‖∫ u : ℝ, ectrInt χ D (2 * D) (Ypar D) 1 ρ (1/2 - ρ.re) u‖
        ≤ ∫ u : ℝ, Kcls D σ * (Real.exp (-(1/2) * |u|) * m u) := by
      refine (norm_integral_le_integral_norm _).trans ?_
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
        (hint1.const_mul _) (Filter.Eventually.of_forall fun u => ?_)
      have := norm_ectrInt_half_le χ hD1 hLD hσ hβ hβ1 hDN u
      rw [hm]
      linarith [this]
    rw [integral_const_mul] at h2
    calc 1 / (2 * π) * ‖∫ u : ℝ, ectrInt χ D (2 * D) (Ypar D) 1 ρ (1/2 - ρ.re) u‖
        ≤ 1 / (2 * π) * (Kcls D σ * ∫ u : ℝ, Real.exp (-(1/2) * |u|) * m u) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Kcls D σ / (2 * π) * ∫ u : ℝ, Real.exp (-(1/2) * |u|) * m u := by ring
  have h3 := sq_integral_weight_le (f := m) (fun u => norm_nonneg _) hint2
  have hI0 : 0 ≤ ∫ u : ℝ, Real.exp (-(1/2) * |u|) * m u :=
    integral_nonneg fun u => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)
  calc ‖EctrHalf χ D (Ypar D) ρ‖ ^ 2
      ≤ (Kcls D σ / (2 * π) * ∫ u : ℝ, Real.exp (-(1/2) * |u|) * m u) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (Kcls D σ / (2 * π)) ^ 2 * (∫ u : ℝ, Real.exp (-(1/2) * |u|) * m u) ^ 2 := by ring
    _ ≤ (Kcls D σ / (2 * π)) ^ 2 * (4 * ∫ u : ℝ, Real.exp (-(1/2) * |u|) * m u ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)

/-- `G_M = ∑_{δ ≤ M} (1 + log²δ)·|λ_δ|²/δ ≤ 2·log³ D` for `M = ⌊2D⌋₊`, `𝓛 ≥ 40`. -/
lemma mollifier_mass_le {D : ℝ} (hD : 1 < D) (hL : 40 ≤ Real.log D) :
    ∑ n ∈ Finset.Icc 1 ⌊2 * D⌋₊, (1 + Real.log n ^ 2)
        * ‖(((bvLam D (2 * D) n * (n : ℝ) ^ (-(1/2 : ℝ)) : ℝ)) : ℂ)‖ ^ 2
      ≤ 2 * Real.log D ^ 3 := by
  have hD0 : (0 : ℝ) < D := by linarith
  set M : ℕ := ⌊2 * D⌋₊ with hM
  have hMle : (M : ℝ) ≤ 2 * D := Nat.floor_le (by linarith)
  have hM1 : 1 ≤ M := Nat.le_floor (by push_cast; linarith)
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hlogM0 : 0 ≤ Real.log M := Real.log_nonneg hMR
  have hlogM : Real.log M ≤ Real.log D + 1 := by
    have h1 : Real.log M ≤ Real.log (2 * D) := Real.log_le_log (by linarith) hMle
    have h2 : Real.log (2 * D) = Real.log 2 + Real.log D := Real.log_mul two_ne_zero hD0.ne'
    have h3 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (x := (2:ℝ)) (by norm_num)
      linarith
    linarith
  have hpt : ∀ n ∈ Finset.Icc 1 M, (1 + Real.log n ^ 2)
      * ‖(((bvLam D (2 * D) n * (n : ℝ) ^ (-(1/2 : ℝ)) : ℝ)) : ℂ)‖ ^ 2
      ≤ (1 + Real.log M ^ 2) * ((n : ℝ))⁻¹ := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hn0 : (0 : ℝ) < n := by linarith
    have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hnR
    have hlogn : Real.log n ≤ Real.log M := Real.log_le_log hn0 (by exact_mod_cast hn.2)
    have h1 : Real.log n ^ 2 ≤ Real.log M ^ 2 := pow_le_pow_left₀ hlogn0 hlogn 2
    have hlam := abs_bvLam_le_one (z1 := D) (z2 := 2 * D) hD0 (by linarith) n
    have h2 : ‖(((bvLam D (2 * D) n * (n : ℝ) ^ (-(1/2 : ℝ)) : ℝ)) : ℂ)‖ ^ 2 ≤ ((n : ℝ))⁻¹ := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow]
      have h3 : ((n : ℝ) ^ (-(1/2 : ℝ))) ^ 2 = ((n : ℝ))⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        norm_num
        exact Real.rpow_neg_one _
      rw [h3]
      have h4 : bvLam D (2 * D) n ^ 2 ≤ 1 := by
        rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hlam
      exact mul_le_of_le_one_left (by positivity) h4
    exact mul_le_mul (by linarith) h2 (by positivity) (by positivity)
  calc ∑ n ∈ Finset.Icc 1 M, (1 + Real.log n ^ 2)
        * ‖(((bvLam D (2 * D) n * (n : ℝ) ^ (-(1/2 : ℝ)) : ℝ)) : ℂ)‖ ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 M, (1 + Real.log M ^ 2) * ((n : ℝ))⁻¹ := Finset.sum_le_sum hpt
    _ = (1 + Real.log M ^ 2) * ((harmonic M : ℚ) : ℝ) := by
        rw [← Finset.mul_sum, harmonic_eq_sum_Icc]
        push_cast
        rfl
    _ ≤ (1 + Real.log M ^ 2) * (1 + Real.log M) :=
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log M) (by positivity)
    _ ≤ (1 + (Real.log D + 1) ^ 2) * (1 + (Real.log D + 1)) := by
        have := pow_le_pow_left₀ hlogM0 hlogM 2
        exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    _ ≤ 2 * Real.log D ^ 3 := by
        have hL2 : 1600 ≤ Real.log D ^ 2 := by nlinarith
        have hL3 : 40 * Real.log D ^ 2 ≤ Real.log D ^ 3 := by
          have : Real.log D ^ 3 = Real.log D * Real.log D ^ 2 := by ring
          rw [this]; exact mul_le_mul_of_nonneg_right hL (by positivity)
        nlinarith

/-- The class-II exponent identity: `D^{201/400}·D·Y^{1−2σ} ≤ D^{(151/50)(1−σ)}`
(`3/2 + 1/400 + (151/100)(1−2σ) = (151/50)(1−σ) − 3/400`). -/
lemma classII_exponent {D : ℝ} (hD : 1 ≤ D) (σ : ℝ) :
    (D ^ (201/800 : ℝ)) ^ 2 * D * (Ypar D ^ (1/2 - σ)) ^ 2 ≤ D ^ ((151/50 : ℝ) * (1 - σ)) := by
  have hD0 : (0 : ℝ) < D := by linarith
  have h1 : (D ^ (201/800 : ℝ)) ^ 2 = D ^ (201/400 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; norm_num
  have h2 : (Ypar D ^ (1/2 - σ)) ^ 2 = D ^ ((151/100 : ℝ) * (1 - 2 * σ)) := by
    rw [Ypar, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le, ← Real.rpow_mul hD0.le]
    congr 1; push_cast; ring
  rw [h1, h2]
  have h3 : D ^ (201/400 : ℝ) * D * D ^ ((151/100 : ℝ) * (1 - 2 * σ))
      = D ^ ((201/400 : ℝ) + 1 + (151/100 : ℝ) * (1 - 2 * σ)) := by
    rw [Real.rpow_add hD0, Real.rpow_add_one hD0.ne']
  rw [h3]
  exact Real.rpow_le_rpow_of_exponent_le hD (by linarith)

/-- **Lemma 3.7 at a fixed `u`**: the discrete mean value of the mollifier over the shifted
`1`-spaced family `{γ_r + u}` (`mean_value_chars_discrete_family` with `T = t + |u|`):
`∑_r ‖M(1/2 + i(γ_r+u), χ_r)‖² ≤ 200·D·(3+|u|)·2 log³D`. -/
lemma sum_sq_norm_Mr_le {ι : Type*} (d : ℕ) [NeZero d] {D t : ℝ} (hD : D = d * (t + 2))
    (ht : 2 ≤ t) (hL : 40 ≤ Real.log D)
    (s : Finset ι) (chi : ι → DirichletCharacter ℂ d) (ρ : ι → ℂ)
    (hρ : ∀ r ∈ s, |(ρ r).im| ≤ t)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → chi r = chi r' → 1 ≤ |(ρ r).im - (ρ r').im|)
    (u : ℝ) :
    ∑ r ∈ s, ‖Mr (chi r) D (2 * D) 1
        (ρ r + (((1/2 - (ρ r).re : ℝ) : ℂ) + (u : ℂ) * Complex.I))‖ ^ 2
      ≤ 200 * D * (3 + |u|) * (2 * Real.log D ^ 3) := by
  classical
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hD1 : 1 < D := by rw [hD]; nlinarith
  have hD0 : (0 : ℝ) < D := by linarith
  have hdD : (d : ℝ) ≤ D := by rw [hD]; nlinarith
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℂ,
      a = fun n => (((bvLam D (2 * D) n * (n : ℝ) ^ (-(1/2 : ℝ)) : ℝ)) : ℂ) := ⟨_, rfl⟩
  have hT : 2 ≤ t + |u| := by linarith [abs_nonneg u]
  have hRT : ∀ χ : DirichletCharacter ℂ d,
      ∀ p ∈ (s.filter (fun r => chi r = χ)).image (fun r => (ρ r).im + u), |p| ≤ t + |u| := by
    intro χ p hp
    rw [Finset.mem_image] at hp
    obtain ⟨r, hr, rfl⟩ := hp
    rw [Finset.mem_filter] at hr
    calc |(ρ r).im + u| ≤ |(ρ r).im| + |u| := abs_add_le _ _
      _ ≤ t + |u| := by linarith [hρ r hr.1]
  have hsep' : ∀ χ : DirichletCharacter ℂ d,
      ∀ p ∈ (s.filter (fun r => chi r = χ)).image (fun r => (ρ r).im + u),
      ∀ p' ∈ (s.filter (fun r => chi r = χ)).image (fun r => (ρ r).im + u),
        p ≠ p' → 1 ≤ |p - p'| := by
    intro χ p hp p' hp' hne
    rw [Finset.mem_image] at hp hp'
    obtain ⟨r, hr, rfl⟩ := hp
    obtain ⟨r', hr', rfl⟩ := hp'
    rw [Finset.mem_filter] at hr hr'
    have hrr : r ≠ r' := by rintro rfl; exact hne rfl
    have := hsep r hr.1 r' hr'.1 hrr (hr.2.trans hr'.2.symm)
    calc (1 : ℝ) ≤ |(ρ r).im - (ρ r').im| := this
      _ = |(ρ r).im + u - ((ρ r').im + u)| := by congr 1; ring
  have hMV := LargeValues.mean_value_chars_discrete_family d hd (t + |u|) hT ⌊2 * D⌋₊ a
    (fun χ => (s.filter (fun r => chi r = χ)).image (fun r => (ρ r).im + u)) hRT hsep'
  -- identify the mollifier with the LV-shaped Dirichlet polynomial
  have hMr : ∀ r ∈ s, ‖Mr (chi r) D (2 * D) 1
      (ρ r + (((1/2 - (ρ r).re : ℝ) : ℂ) + (u : ℂ) * Complex.I))‖ ^ 2
      = ‖∑ n ∈ Finset.Icc 1 ⌊2 * D⌋₊, a n * (chi r) n
          * Complex.exp ((-Real.log n * ((ρ r).im + u) : ℝ) * Complex.I)‖ ^ 2 := by
    intro r _
    congr 2
    rw [Mr_one_eq]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    have hre : (ρ r + (((1/2 - (ρ r).re : ℝ) : ℂ) + (u : ℂ) * Complex.I)).re = 1/2 := by simp
    have him : (ρ r + (((1/2 - (ρ r).re : ℝ) : ℂ) + (u : ℂ) * Complex.I)).im
        = (ρ r).im + u := by simp
    rw [natCast_cpow_neg_eq hn.1, hre, him, ha]
    push_cast
    ring
  have hLHS : ∑ r ∈ s, ‖Mr (chi r) D (2 * D) 1
      (ρ r + (((1/2 - (ρ r).re : ℝ) : ℂ) + (u : ℂ) * Complex.I))‖ ^ 2
      = ∑ χ : DirichletCharacter ℂ d,
          ∑ p ∈ (s.filter (fun r => chi r = χ)).image (fun r => (ρ r).im + u),
            ‖∑ n ∈ Finset.Icc 1 ⌊2 * D⌋₊, a n * χ n
              * Complex.exp ((-Real.log n * p : ℝ) * Complex.I)‖ ^ 2 := by
    rw [← Finset.sum_fiberwise s chi]
    refine Finset.sum_congr rfl fun χ _ => ?_
    have hinj : Set.InjOn (fun r => (ρ r).im + u) ↑(s.filter (fun r => chi r = χ)) := by
      intro r hr r' hr' heq
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hr hr'
      by_contra hne
      have h1 := hsep r hr.1 r' hr'.1 hne (hr.2.trans hr'.2.symm)
      have h2 : (ρ r).im = (ρ r').im := by
        have : (ρ r).im + u = (ρ r').im + u := heq
        linarith
      rw [h2, sub_self, abs_zero] at h1
      linarith
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.mem_filter] at hr
    rw [hMr r hr.1, hr.2]
  have hcount : 200 * ((⌊2 * D⌋₊ : ℝ) + d * (t + |u| + 1)) ≤ 200 * D * (3 + |u|) := by
    have hMle : ((⌊2 * D⌋₊ : ℕ) : ℝ) ≤ 2 * D := Nat.floor_le (by linarith)
    have h1 : (d : ℝ) * (t + |u| + 1) ≤ D + D * |u| := by
      have h2 : (d : ℝ) * (t + |u| + 1) = d * (t + 2) + d * |u| - d := by ring
      rw [h2, ← hD]
      nlinarith [abs_nonneg u]
    nlinarith
  have hG : ∑ n ∈ Finset.Icc 1 ⌊2 * D⌋₊, (1 + Real.log n ^ 2) * ‖a n‖ ^ 2
      ≤ 2 * Real.log D ^ 3 := by
    rw [ha]
    exact mollifier_mass_le hD1 hL
  have hG0 : 0 ≤ ∑ n ∈ Finset.Icc 1 ⌊2 * D⌋₊, (1 + Real.log n ^ 2) * ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  rw [hLHS]
  calc _ ≤ 200 * ((⌊2 * D⌋₊ : ℝ) + d * (t + |u| + 1))
        * ∑ n ∈ Finset.Icc 1 ⌊2 * D⌋₊, (1 + Real.log n ^ 2) * ‖a n‖ ^ 2 := hMV
    _ ≤ 200 * D * (3 + |u|) * (2 * Real.log D ^ 3) :=
        mul_le_mul hcount hG hG0 (by positivity)

/-- **L1.f** (Lemmas 3.6, 3.7, Corollary 3.8): the class-II mean square over a `1`-spaced
family of points `ρ_r` (per character), `|Im ρ_r| ≤ t`, `σ ≤ Re ρ_r ≤ 1`:
`∑_r ‖E_ctr(ρ_r, χ_r)‖² ≤ 10²²·C_τ²·C_Γ²·log⁵D·D^{(151/50)(1−σ)}`, `D = d(t+2)`.
The points need not be zeros.  Route (audit F7): `e^{−|u|/2}` weighting, elementary
Cauchy–Schwarz, `mean_value_chars_discrete_family` at each `u` with `T = t + |u|`. -/
theorem sum_sq_EctrHalf_le {ι : Type*} (d : ℕ) [NeZero d] {D t σ : ℝ} (hD : D = d * (t + 2))
    (ht : 2 ≤ t) (hL : 40 ≤ Real.log D) (hσ : 39/50 ≤ σ) (_hσ1 : σ ≤ 1)
    (s : Finset ι) (chi : ι → DirichletCharacter ℂ d) (ρ : ι → ℂ)
    (hρ : ∀ r ∈ s, σ ≤ (ρ r).re ∧ (ρ r).re ≤ 1 ∧ |(ρ r).im| ≤ t)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → chi r = chi r' → 1 ≤ |(ρ r).im - (ρ r').im|) :
    ∑ r ∈ s, ‖EctrHalf (chi r) D (Ypar D) (ρ r)‖ ^ 2
      ≤ 10 ^ 22 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
          * Real.log D ^ 5 * D ^ ((151/50 : ℝ) * (1 - σ)) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hD1 : 1 < D := by rw [hD]; nlinarith
  have hD0 : (0 : ℝ) < D := by linarith
  have hL0 : (0 : ℝ) ≤ Real.log D := by linarith
  have hY := Ypar_pos hD0
  have hCG := GammaStrip.CGamma_pos
  have hCt := Ctau_pos
  -- per-index bound (Lemma 3.6)
  have hper : ∀ r ∈ s, ‖EctrHalf (chi r) D (Ypar D) (ρ r)‖ ^ 2
      ≤ (Kcls D σ / (2 * π)) ^ 2 * (4 * ∫ u : ℝ, Real.exp (-(1/2) * |u|)
          * ‖Mr (chi r) D (2 * D) 1
              (ρ r + (((1/2 - (ρ r).re : ℝ) : ℂ) + (u : ℂ) * Complex.I))‖ ^ 2) := by
    intro r hr
    obtain ⟨h1, h2, h3⟩ := hρ r hr
    refine sq_norm_EctrHalf_le (chi r) hD1 (by linarith) hσ h1 h2 ?_
    rw [hD]
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- the summed integral (Lemma 3.7)
  have hint : ∀ r ∈ s, Integrable (fun u : ℝ => Real.exp (-(1/2) * |u|)
      * ‖Mr (chi r) D (2 * D) 1
          (ρ r + (((1/2 - (ρ r).re : ℝ) : ℂ) + (u : ℂ) * Complex.I))‖ ^ 2) :=
    fun r _ => integrable_weight_norm_Mr_pow (chi r) hD0 (by linarith) 2
  have hsumint : ∑ r ∈ s, ∫ u : ℝ, Real.exp (-(1/2) * |u|)
      * ‖Mr (chi r) D (2 * D) 1
          (ρ r + (((1/2 - (ρ r).re : ℝ) : ℂ) + (u : ℂ) * Complex.I))‖ ^ 2
      ≤ 12800 * D * Real.log D ^ 3 := by
    rw [← integral_finsetSum s hint]
    have hw4 := integrable_exp_neg_abs_mul (a := 1/4) (by norm_num)
    have hI4 : ∫ u : ℝ, Real.exp (-(1/4) * |u|) = 8 := by
      rw [integral_exp_neg_abs_mul (by norm_num)]; norm_num
    calc ∫ u : ℝ, ∑ r ∈ s, Real.exp (-(1/2) * |u|)
          * ‖Mr (chi r) D (2 * D) 1
              (ρ r + (((1/2 - (ρ r).re : ℝ) : ℂ) + (u : ℂ) * Complex.I))‖ ^ 2
        ≤ ∫ u : ℝ, (1600 * D * Real.log D ^ 3) * Real.exp (-(1/4) * |u|) := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun u => Finset.sum_nonneg fun r _ => by positivity)
            (hw4.const_mul _) (Filter.Eventually.of_forall fun u => ?_)
          dsimp only
          rw [← Finset.mul_sum]
          have hmv := sum_sq_norm_Mr_le d hD ht hL s chi ρ (fun r hr => (hρ r hr).2.2) hsep u
          have hwl := weight_lin_le (abs_nonneg u)
          calc Real.exp (-(1/2) * |u|) * ∑ r ∈ s, ‖Mr (chi r) D (2 * D) 1
                (ρ r + (((1/2 - (ρ r).re : ℝ) : ℂ) + (u : ℂ) * Complex.I))‖ ^ 2
              ≤ Real.exp (-(1/2) * |u|) * (200 * D * (3 + |u|) * (2 * Real.log D ^ 3)) :=
                mul_le_mul_of_nonneg_left hmv (Real.exp_pos _).le
            _ = 400 * D * Real.log D ^ 3 * ((3 + |u|) * Real.exp (-(1/2) * |u|)) := by ring
            _ ≤ 400 * D * Real.log D ^ 3 * (4 * Real.exp (-(1/4) * |u|)) :=
                mul_le_mul_of_nonneg_left hwl (by positivity)
            _ = (1600 * D * Real.log D ^ 3) * Real.exp (-(1/4) * |u|) := by ring
      _ = (1600 * D * Real.log D ^ 3) * 8 := by rw [integral_const_mul, hI4]
      _ = 12800 * D * Real.log D ^ 3 := by ring
  -- the constant (Corollary 3.8)
  have hπ : (36 : ℝ) ≤ (2 * π) ^ 2 := by
    have := Real.pi_gt_three
    nlinarith
  have hP := classII_exponent hD1.le σ
  have hKsq : (Kcls D σ / (2 * π)) ^ 2 * (4 * (12800 * D * Real.log D ^ 3))
      ≤ 10 ^ 22 * Ctau ^ 2 * GammaStrip.CGamma ^ 2 * Real.log D ^ 5
          * D ^ ((151/50 : ℝ) * (1 - σ)) := by
    have hKdef : Kcls D σ = 964800000 * (GammaStrip.CGamma * Ctau * Real.log D)
        * (D ^ (201/800 : ℝ) * Ypar D ^ (1/2 - σ)) := by
      rw [Kcls]; ring
    rw [hKdef]
    have hB0 : 0 ≤ GammaStrip.CGamma ^ 2 * Ctau ^ 2 * Real.log D ^ 5 := by positivity
    have hDa : 0 ≤ D ^ (201/800 : ℝ) := Real.rpow_nonneg hD0.le _
    have hYb : 0 ≤ Ypar D ^ (1/2 - σ) := Real.rpow_nonneg hY.le _
    have hP0 : 0 ≤ (D ^ (201/800 : ℝ)) ^ 2 * D * (Ypar D ^ (1/2 - σ)) ^ 2 := by positivity
    have hq0 : 0 ≤ D ^ ((151/50 : ℝ) * (1 - σ)) := Real.rpow_nonneg hD0.le _
    have hπ0 : (0 : ℝ) < (2 * π) ^ 2 := by positivity
    calc (964800000 * (GammaStrip.CGamma * Ctau * Real.log D)
          * (D ^ (201/800 : ℝ) * Ypar D ^ (1/2 - σ)) / (2 * π)) ^ 2
          * (4 * (12800 * D * Real.log D ^ 3))
        = ((964800000 : ℝ) ^ 2 * 51200 / (2 * π) ^ 2)
          * (GammaStrip.CGamma ^ 2 * Ctau ^ 2 * Real.log D ^ 5)
          * ((D ^ (201/800 : ℝ)) ^ 2 * D * (Ypar D ^ (1/2 - σ)) ^ 2) := by
          rw [div_pow]; ring
      _ ≤ ((964800000 : ℝ) ^ 2 * 51200 / 36)
          * (GammaStrip.CGamma ^ 2 * Ctau ^ 2 * Real.log D ^ 5)
          * D ^ ((151/50 : ℝ) * (1 - σ)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right ?_ hB0) hP hP0 (by positivity)
          exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hπ
      _ ≤ 10 ^ 22 * Ctau ^ 2 * GammaStrip.CGamma ^ 2 * Real.log D ^ 5
          * D ^ ((151/50 : ℝ) * (1 - σ)) := by
          have hc : ((964800000 : ℝ) ^ 2 * 51200 / 36) ≤ 10 ^ 22 := by norm_num
          have := mul_le_mul_of_nonneg_right hc (mul_nonneg hB0 hq0)
          calc ((964800000 : ℝ) ^ 2 * 51200 / 36)
                * (GammaStrip.CGamma ^ 2 * Ctau ^ 2 * Real.log D ^ 5)
                * D ^ ((151/50 : ℝ) * (1 - σ))
              = ((964800000 : ℝ) ^ 2 * 51200 / 36)
                * ((GammaStrip.CGamma ^ 2 * Ctau ^ 2 * Real.log D ^ 5)
                  * D ^ ((151/50 : ℝ) * (1 - σ))) := by ring
            _ ≤ 10 ^ 22 * ((GammaStrip.CGamma ^ 2 * Ctau ^ 2 * Real.log D ^ 5)
                  * D ^ ((151/50 : ℝ) * (1 - σ))) := this
            _ = 10 ^ 22 * Ctau ^ 2 * GammaStrip.CGamma ^ 2 * Real.log D ^ 5
                * D ^ ((151/50 : ℝ) * (1 - σ)) := by ring
  have hK0 := Kcls_nonneg hD0 hL0 (σ := σ)
  calc ∑ r ∈ s, ‖EctrHalf (chi r) D (Ypar D) (ρ r)‖ ^ 2
      ≤ ∑ r ∈ s, (Kcls D σ / (2 * π)) ^ 2 * (4 * ∫ u : ℝ, Real.exp (-(1/2) * |u|)
          * ‖Mr (chi r) D (2 * D) 1
              (ρ r + (((1/2 - (ρ r).re : ℝ) : ℂ) + (u : ℂ) * Complex.I))‖ ^ 2) :=
        Finset.sum_le_sum hper
    _ = (Kcls D σ / (2 * π)) ^ 2 * (4 * ∑ r ∈ s, ∫ u : ℝ, Real.exp (-(1/2) * |u|)
          * ‖Mr (chi r) D (2 * D) 1
              (ρ r + (((1/2 - (ρ r).re : ℝ) : ℂ) + (u : ℂ) * Complex.I))‖ ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ (Kcls D σ / (2 * π)) ^ 2 * (4 * (12800 * D * Real.log D ^ 3)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumint (by norm_num)) ?_
        positivity
    _ ≤ _ := hKsq

end LoggedDetector
end Carmichael
