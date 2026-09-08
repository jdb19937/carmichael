/-
Route Z, sortie Z6d-A: the Gram function `B` of the log-free zero-density machine.
Blueprint: routez/Z0b-density.md §5 (Lemma 5.1, Halász duality with majorants) and §6
(Proposition 6.1 and Lemmas 6.2–6.4: structure and bounds of `B`), consumed by §8
(Lemma 8.2, Theorem 8.3) of the density theorem Z6d (§12.4).

No `sorry`, no `axiom`, no `native_decide` in this file.  `#print axioms` on every theorem
named below: [propext, Classical.choice, Quot.sound].

STATEMENTS (the interface; all parameters `Rpar D, M0par D, Xpar D, ellpar D, z1par D,
z2par D` are `Detector`'s frozen §1 table, `𝓛 = Real.log D`, `Q_R = Detector.QR N (Rpar D)`).

* Lemma 5.1, general form, `halasz_duality`:
    `(N) [NeZero N] {J} [Fintype J] (s : J → ℂ) (χ : J → DirichletCharacter ℂ N)
     (hs : ∀ j, 0 ≤ (s j).re) (c : ℕ → ℂ) (b : ℕ → ℝ) (hb0 : b 0 = 0) (hb : ∀ n, 0 ≤ b n)
     (hbc : ∀ n, c n ≠ 0 → 0 < b n) (hsum : Summable fun n => ‖c n‖^2 / b n) (hbs : Summable b) :
     (∑ j, ‖Fgen c (χ j) (s j)‖)^2
       ≤ (∑' n, ‖c n‖^2 / b n) * ∑ j, ∑ k, ‖Bgen b (χ j * (χ k)⁻¹) (s j + conj (s k))‖`
  with `Fgen c χ s = ∑' n, c n * χ n * n^{−s}`, `Bgen b χ s = ∑' n, (b n : ℂ) * χ n * n^{−s}`.
* Lemma 5.1, applied (`halasz_duality_detector`, and `halasz_duality_frozen` at the frozen
  parameters, hypotheses `1 < D`, `2 ≤ log D`, `0 ≤ σ`, `∀ j, σ ≤ (ρ j).re`):
    `(∑ j, ‖Fdet (χ j) z₁ z₂ R X (ρ j)‖)^2
       ≤ (∑' n, (cDet N z₁ z₂ R X σ n)^2 / bMaj N R M₀ X ℓ n)
         * ∑ j, ∑ k, ‖Bgram N R M₀ X ℓ (χ j * (χ k)⁻¹) ((ρ j − σ) + conj (ρ k − σ))‖`
  where `Bgram N R M₀ X ℓ χ 𝔰 = Bgen (bMaj N R M₀ X ℓ) χ 𝔰` is `B` with `Detector.bMaj`, and
  `Fdet`, `cDet` are Z6c's detector and coefficients (`Fgen cDet χ (ρ−σ) = Fdet χ ρ` is
  `Fgen_cDet_eq_Fdet`).  The summability of `∑ c_n²/b_n` (blueprint Lemma 8.1, Step 1:
  `W(n) ≥ e^{−n/X}/3` on `n > z₁`, `Wwin_ge_third`) is PROVED here, not assumed.
* Proposition 6.1, `Bgram_eq_main_add_rem` (general `R`, `0 ≤ log M₀ ≤ log X`, `0 < ℓ`) and
  `Bgram_eq_main_add_rem_frozen` (`1 < D`); for every `χ mod N` and `0 ≤ Re 𝔰 ≤ 1/50`:
    `Bgram N R M₀ X ℓ χ 𝔰
       = (if χ = 1 then (φ(N)/N : ℂ) * (PhiR N R : ℂ) * G1 M₀ X ℓ (−𝔰) else 0)
         + Brem N R M₀ X ℓ χ 𝔰`
  with `PhiR N R = ∑ r ∈ Rset N R, φ(r)/r²` (the form of `Detection.sum_totient_div_sq_le_P1`),
  `Brem N R M₀ X ℓ χ 𝔰 = (1/2π) ∫_ℝ gramInt χ 𝔰 (−99/100) u du`,
  `gramInt χ 𝔰 c u = Γ(w)·Kker(w)·Mh N R χ (1+𝔰+w)·L(1+𝔰+w,χ)` at `w = c + iu`,
  `Mh N R χ s = ∑'_{r,r'≤R} (rr')⁻¹ ∑_{δ ∣ rr'} h(δ;r,r') χ(δ) δ^{−s}` (blueprint `B_rem` with the
  finite `δ, r, r'` sums written inside the integral), `Kker M₀ X ℓ w = avgExp (log X) ℓ w −
  avgExp (log M₀) ℓ w` with `avgExp a ℓ w = (1/ℓ)∫_a^{a+ℓ} e^{wη} dη` (the blueprint's `𝒦`,
  in the averaged-window integral form; `avgExp_eq_of_ne` is the closed form
  `(1/ℓ)(e^{(a+ℓ)w} − e^{aw})/w`), and `G1 M₀ X ℓ w = Γ(w+1) · dslope (Kker M₀ X ℓ) 0 w`
  (`= Γ(w)𝒦(w)` off `w = 0`, `G1_eq_of_ne`; `G1 0 = 𝒦'(0) = log X − log M₀`, `G1_zero`,
  `= (3/5)𝓛` at the frozen parameters, `G1_zero_frozen`).
* Lemma 6.2, `G1_bounds_frozen` (`1 < D`, `1 ≤ log D`, `0 ≤ Re 𝔰 ≤ 1/50`), three product forms:
    `‖G1 (−𝔰)‖ ≤ C7 * exp(−|θ|/2) * log D`,
    `|θ| * ‖G1 (−𝔰)‖ ≤ C7 * exp(−|θ|/2)`,
    `θ^2 * ellpar D * ‖G1 (−𝔰)‖ ≤ 4 * C7 * exp(−|θ|/2)`   (`θ = 𝔰.im`),
  and the `min` form `norm_G1_le_min` for `θ ≠ 0`:
    `‖G1 (−𝔰)‖ ≤ C7 * exp(−|θ|/2) * min (log D) (min (1/|θ|) (4/(θ^2 * ellpar D)))`.
  Core version with abstract parameters: `G1_bounds`.
* Lemma 6.3, `norm_Brem_le` (`1 < D`, `2 ≤ log D`, `0 ≤ Re 𝔰 ≤ 1/50`, `N(|θ|+2) ≤ 2D`, all `χ`):
    `‖Brem N (Rpar D) (M0par D) (Xpar D) (ellpar D) χ 𝔰‖
       ≤ C11 * D^(20651/40000) * log D * (M0par D)^(−99/100)`
  and the corollary `norm_Brem_le'`: `≤ C11 * (log D)^3 * D^(−7/100)`.
* Lemma 6.4, `row_sum_le` (`1 < D`, `1 ≤ log D`; `ι`, `S : Finset ι`, `j : ι`, `𝔰 : ι → ℂ`,
  `hre : ∀ k ∈ S, 0 ≤ (𝔰 k).re ∧ (𝔰 k).re ≤ 1/50`,
  `hdiag : ∀ k ∈ S, k ≠ j → 1/log D ≤ |(𝔰 k).im|`,
  `hbin : ∀ m ≥ 1, (S.filter fun k => m/log D ≤ |(𝔰 k).im| ∧ |(𝔰 k).im| < (m+1)/log D).card ≤ 2`,
  `hMertens : MertensProd (Rpar D) ≤ CM * Real.log (Rpar D)`):
    `∑ k ∈ S, ‖(φ(N)/N : ℂ) * (PhiR N (Rpar D) : ℂ) * G1 (M0par D) (Xpar D) (ellpar D) (−𝔰 k)‖
       ≤ C9 CM * (QR N (Rpar D))^2 * (1/100) * (log D)^2`.
  The consumer passes `𝔰 k = s_j + conj s_k` (so `(𝔰 k).im = θ_{jk}`, `k = j` is the diagonal).

CONSTANTS DELIVERED.  `C7 = 1608·(1 + C_Γ)` (`C_Γ = GammaStrip.CGamma = 5184`);
`C11 = 6432·2·1.2·10⁶·C_Γ·C_τ³` (`C_τ = DetectionShift.Ctau = 2^(2^800)`, irreducible);
`C9 CM = CM·C7·(5 + 2·log 400)` (`log 400 = log(4/ε)`, `ε = 1/100`).

DELTAS VS. THE BLUEPRINT (routez/Z0b-density.md §5–§6), none silent.
1. Lemma 6.2's `min(𝓛, 1/|θ|, 4/(θ²ℓ))` is delivered in the three product forms above (in
   Lean `1/0 = 0`, so the `min` form is false at `θ = 0`); the `min` form is provided for
   `θ ≠ 0`.  `C7 = 1608(1 + C_Γ)` in place of `8(1 + C_Γ)e^{3/8}`: the delivered I8(b)
   carries `201·C_Γ`, and `e^{3/8} ≤ 2` is used.
2. Lemma 6.3's coefficient mass is bounded log-free by `Hmass ≤ C_τ²·R^{2+1/400}`
   (`∏_{p∣r}(p+1) ≤ 2^{ω(r)}r`, I9(d) `2^{ω(r)} ≤ C_τ r^{1/800}`, `#Rset ≤ R`) instead of
   `(R·C loglog R)² ≤ R²𝓛²` under a threshold; the delivered `D`-exponent is
   `20651/40000 = 99/200 + 1/800 + 801/40000 = 0.516275` (blueprint: `0.52125`, which used
   `1/2` for I1's `(1−ε₂)/2 = 0.495`), i.e. exact total exponent `−3109/40000 = −0.077725`
   against the blueprint's `−0.07275`.  Exponent spend from the coefficient mass: `+1/40000`;
   net gain `0.004975`.  No `D ≥ D₀` threshold beyond `2 ≤ log D`.  The `𝓛³` of the frozen
   statement is kept in the corollary `norm_Brem_le'` (`𝓛 ≤ 𝓛³`); the main form carries `𝓛¹`.
3. Lemma 6.3 needs the height hypothesis `N(|Im 𝔰|+2) ≤ 2D` (the blueprint's `|θ| ≤ 2t`,
   `D = d(t+2)`, gives it) and `2 ≤ log D` (for `log 3 ≤ 𝓛`); the I1 line constant is
   `1.2·10⁶·C_τ` (`norm_LFunction_left_line_le`).
4. Lemma 6.4 carries the Mertens input as the NAMED HYPOTHESIS `hMertens` on `CM`
   (blueprint §12.3 authorises this); `Φ_R ≤ P(1) ≤ Q_R·MertensProd R` is
   `Detection.P1_le_QR_mul_MertensProd`, `φ(N)/N ≤ Q_R` is `Detection.totient_div_le_QR`.
   The spacing hypotheses are exactly the blueprint's (a) and (b); `C9` is the blueprint's
   `C_M C_7 (5 + 2 log(4/ε))` (row sum `𝓛(1 + 2(1 + log 400) + 2·1)`).
5. Proposition 6.1 is proved for every `𝔰` with `0 ≤ Re 𝔰 ≤ 1/50` INCLUDING `𝔰 = 0`: `G1` is
   defined through `dslope` (so `Γ𝒦` is regular at `0` by construction) and the residue is
   read off the numerator `Hfull(w) = G1(w)·Mh(1+𝔰+w,χ₀)·L₁(1+𝔰+w)` (`L₁` = Mathlib's entire
   `LFunctionTrivChar₁`) via `rectInt_cauchy_on` at the pole `w = −𝔰`; no case split.
   The identity has no `D`-threshold (only `0 ≤ log M₀ ≤ log X`, `0 < ℓ`); the strip
   estimates use a crude `L`-bound (`norm_LFunction_crude`) for integrability only.
6. `Brem` places the finite `∑_{r,r'}∑_δ` inside the line integral (as `Mh`); the two forms
   are equal termwise, and only the norm bound of Lemma 6.3 is consumed downstream.
7. The Halász majorant lemma takes `b 0 = 0` (true for `bMaj`) and returns `Fgen`/`Bgen`;
   `c 0 = 0` is not needed.

DELIVERED, by section.
§0  `norm_exp_sub_one_le_of_re_nonpos` (`‖e^z − 1‖ ≤ ‖z‖` on `Re z ≤ 0`),
    `exp_neg_half_le_two_div`, `exp_three_eighths_le_two`.
§1  `avgExp`, `Kker`, `G1`; `avgExp_eq_of_ne`, `avgExp_zero`, `hasDerivAt_avgExp` (dominated
    differentiation under the interval integral), `differentiable_avgExp`, `deriv_avgExp_zero`,
    `differentiable_Kker`, `Kker_zero`, `deriv_Kker_zero`, `dslope_Kker_zero`,
    `dslope_Kker_of_ne`, `G1_zero`, `G1_eq_of_ne`, `differentiableAt_G1` (on `Re w > −1`);
    the kernel bounds (K1) `norm_Kker_le_two`, (K1′) `norm_Kker_le_of_re_nonpos`,
    (K2) `norm_Kker_le_div`, (K3) `norm_Kker_le_slope`, (K4) `norm_Kker_le_of_re_le_one`,
    `norm_dslope_Kker_le`; `C7`, `G1_bounds` (Lemma 6.2, abstract parameters).
§2  `tsum_mul_le_sqrt_mul_sqrt` (Cauchy–Schwarz for `tsum`), `Fgen`, `Bgen`,
    `conj_char_apply` (`conj χ(n) = χ⁻¹(n)`), `conj_natCast_cpow`, `char_cpow_mul_conj`,
    `halasz_duality` (Lemma 5.1).
§3  `hBV_eq_zero_of_not_dvd`, `sum_divisors_hBV_eq`, `Mh`, `Hmass`, `differentiable_Mh`,
    `norm_Mh_le`, `Hmass_le_sq`, `prod_primeFactors_add_one_le_two_pow_mul`, `Hmass_le`
    (`≤ C_τ² R^{801/400}`), `LFunction_eq_tsum`, `summable_char_cpow`,
    `tsum_multiples_char_cpow`, `Pfun_sq_term_eq`, `tsum_Pfun_sq_eq_Mh_mul_LFunction`
    (`∑_n P(n)²χ(n)n^{−s} = M_h(s,χ)L(s,χ)`, `Re s > 1`), `PhiR`, `principal_apply_of_dvd`,
    `Mh_one_principal` (`M_h(1,χ₀) = Φ_R`, exact orthogonality summed).
§4  `intervalIntegral_integral_swap` (Fubini on `[a,b] × ℝ`), `ofReal_div_exp_cpow_neg`,
    `avg_window_eq_integral`, `Wwin_eq_integral` (Mellin representation of `W(n)`).
§5  `Bgram`, `gramInt`, `Brem`, `Gfull`, `gramInt_eq_Gfull`, `Tanc`, `bMaj_term_eq_integral`,
    `norm_Tanc_le`, `continuous_Tanc`, `integrable_Tanc`, `tsum_Tanc`,
    `Bgram_eq_integral_anchor` (`B = (1/2π)∫_{(1)} Γ𝒦M_hL`).
§6  `norm_LFunction_crude`, `Kbig`, `differentiableAt_Gfull`, `norm_Gfull_le`,
    `integrable_gramInt_line`, `norm_integral_Gfull_horiz_le`, `tendsto_Gfull_horiz`,
    `dist_pole_line`, `gramInt_line_shift` (`χ ≠ χ₀`), `Hfull`, `differentiableAt_Hfull`,
    `Gfull_eq_Hfull_div`, `Hfull_at_pole`, `rectInt_Gfull_principal`,
    `gramInt_line_shift_principal` (`χ₀`), `Bgram_eq_main_add_rem` (Proposition 6.1).
§7  `log_M0par`, `log_Xpar`, `log_Rpar`, `ellpar_pos`, `G1_bounds_frozen`, `norm_G1_le_min`.
§8  `norm_LFunction_left_line_le` (I1 on `Re s ∈ [1/100, 3/100]`), `C11`,
    `norm_gramInt_left_le`, `norm_Brem_le`, `norm_Brem_le'` (Lemma 6.3).
§9  `sum_Ioc_inv_sq_le`, `binWeight`, `sum_binWeight_le`, `C9`, `norm_G1_le_binWeight`,
    `row_sum_le` (Lemma 6.4).
§10 `Fgen_cDet_eq_Fdet`, `Wwin_ge_third`, `cDet_sq_div_bMaj_le`, `halasz_duality_detector`,
    `frozen_window_hyps`, `halasz_duality_frozen`, `Bgram_eq_main_add_rem_frozen`,
    `G1_zero_frozen`.

CONTOUR DESIGN (Proposition 6.1).  Anchor line `Re w = 1` (the `n^{−2−x}` weight against
`P(n)² ≤ ⌊R⌋₊²` pays the Mellin/`tsum` interchange, `integral_tsum_of_summable_integral_norm`);
target line `Re w = −99/100` (distance `1/100` to the `Γ`-pole `−1`, `1 − 1/100` to `0`, and
`≥ 97/100` to the `L`-pole `w = −𝔰`, `Re(−𝔰) ∈ [−1/50, 0]`); horizontal edges at
`Im w = ±T`, `T ≥ |Im 𝔰| + 1`, killed by I8(b) against the polynomial `(1+T)²`.
-/
import Carmichael.DetectionShift
import Carmichael.GammaStrip
import Carmichael.LConvexityCorollaries
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

set_option autoImplicit false

namespace Carmichael
namespace GramFunction

open Complex MeasureTheory Detector DetectionShift
open scoped Real ComplexConjugate

/-! ## §0. Elementary helpers -/

/-- `‖e^z − 1‖ ≤ ‖z‖` on the closed left half-plane `Re z ≤ 0`. -/
lemma norm_exp_sub_one_le_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) :
    ‖Complex.exp z - 1‖ ≤ ‖z‖ := by
  rcases eq_or_ne z 0 with rfl | hz0
  · simp
  have hint : ∫ t in (0 : ℝ)..1, Complex.exp (z * t)
      = (Complex.exp (z * 1) - Complex.exp (z * 0)) / z := integral_exp_mul_complex hz0
  have hbd : ‖∫ t in (0 : ℝ)..1, Complex.exp (z * t)‖ ≤ 1 * |(1 : ℝ) - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun t ht => ?_
    rw [Set.uIoc_of_le zero_le_one] at ht
    rw [Complex.norm_exp]
    have hre : (z * (t : ℂ)).re = z.re * t := by simp
    rw [hre]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hz ht.1.le)
  rw [hint, mul_one, mul_zero, Complex.exp_zero, norm_div] at hbd
  rw [div_le_iff₀ (norm_pos_iff.mpr hz0)] at hbd
  simpa using hbd

/-- `e^{-u/2} ≤ 2/u` for `u > 0` (from `1 + u/2 ≤ e^{u/2}`). -/
lemma exp_neg_half_le_two_div {u : ℝ} (hu : 0 < u) : Real.exp (-u / 2) ≤ 2 / u := by
  have h := Real.add_one_le_exp (u / 2)
  have hpos := Real.exp_pos (u / 2)
  have hneg : Real.exp (-u / 2) = (Real.exp (u / 2))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [hneg, inv_eq_one_div, div_le_div_iff₀ hpos hu]
  nlinarith

/-- `e^{3/8} ≤ 2`. -/
lemma exp_three_eighths_le_two : Real.exp (3 / 8) ≤ 2 := by
  have h1 : Real.exp (3 / 8) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by norm_num)
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have h4 : Real.exp (1 / 2) ≤ 2 := by nlinarith [Real.exp_pos (1 / 2)]
  linarith

/-! ## §1. The averaged exponential, the combined kernel `𝒦`, and `G₁` -/

/-- `avg_{η ∈ [a, a+ℓ]} e^{ηw} = (1/ℓ)∫_a^{a+ℓ} e^{wη} dη` (the Mellin transform of one
averaged window `avg_η e^{−n/e^η}` divided by `Γ(w) n^{−w}`). -/
noncomputable def avgExp (a ell : ℝ) (w : ℂ) : ℂ :=
  ((1 / ell : ℝ) : ℂ) * ∫ η in a..(a + ell), Complex.exp (w * (η : ℂ))

/-- The combined kernel `𝒦(w) = avg_η N^w − avg_ξ M^w` (blueprint §6). -/
noncomputable def Kker (M0 X ell : ℝ) (w : ℂ) : ℂ :=
  avgExp (Real.log X) ell w - avgExp (Real.log M0) ell w

/-- `G₁(w) = Γ(w)·𝒦(w)`, written as `Γ(w+1)·(𝒦(w)/w)` with the removable singularity at
`w = 0` filled in by `dslope` (`G₁(0) = 𝒦'(0)`). -/
noncomputable def G1 (M0 X ell : ℝ) (w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * dslope (Kker M0 X ell) 0 w

lemma continuous_exp_mul_ofReal (w : ℂ) :
    Continuous fun η : ℝ => Complex.exp (w * (η : ℂ)) := by fun_prop

lemma intervalIntegrable_exp_mul_ofReal (w : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun η : ℝ => Complex.exp (w * (η : ℂ))) volume a b :=
  (continuous_exp_mul_ofReal w).intervalIntegrable a b

lemma norm_exp_mul_ofReal (w : ℂ) (η : ℝ) :
    ‖Complex.exp (w * (η : ℂ))‖ = Real.exp (w.re * η) := by
  rw [Complex.norm_exp]; simp

/-- Closed form off `w = 0`: `avgExp a ℓ w = (1/ℓ)·(e^{(a+ℓ)w} − e^{aw})/w`. -/
lemma avgExp_eq_of_ne {a ell : ℝ} {w : ℂ} (hw : w ≠ 0) :
    avgExp a ell w
      = ((1 / ell : ℝ) : ℂ) * ((Complex.exp (w * ((a + ell : ℝ) : ℂ))
          - Complex.exp (w * (a : ℂ))) / w) := by
  rw [avgExp, integral_exp_mul_complex hw]

lemma avgExp_zero (a : ℝ) {ell : ℝ} (hell : 0 < ell) : avgExp a ell 0 = 1 := by
  simp only [avgExp, zero_mul, Complex.exp_zero, intervalIntegral.integral_const,
    add_sub_cancel_left, Complex.real_smul, mul_one]
  rw [← Complex.ofReal_mul]
  have : (1 / ell) * ell = 1 := by field_simp
  rw [this, Complex.ofReal_one]

/-- `avgExp a ℓ` is entire (dominated differentiation under the interval integral). -/
lemma hasDerivAt_avgExp (a ell : ℝ) (w₀ : ℂ) :
    HasDerivAt (avgExp a ell)
      (((1 / ell : ℝ) : ℂ) * ∫ η in a..(a + ell), (η : ℂ) * Complex.exp (w₀ * (η : ℂ))) w₀ := by
  have hball : Metric.ball w₀ 1 ∈ nhds w₀ := Metric.ball_mem_nhds w₀ one_pos
  set bound : ℝ → ℝ := fun η => |η| * Real.exp (|η| * (‖w₀‖ + 1)) with hbound
  have hcont_bound : Continuous bound := by
    simp only [hbound]; fun_prop
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun w η => Complex.exp (w * (η : ℂ)))
    (F' := fun w η => (η : ℂ) * Complex.exp (w * (η : ℂ)))
    (x₀ := w₀) (a := a) (b := a + ell) (μ := volume) (bound := bound) hball
    (Filter.Eventually.of_forall fun w =>
      (continuous_exp_mul_ofReal w).aestronglyMeasurable)
    (intervalIntegrable_exp_mul_ofReal w₀ a (a + ell))
    (by
      have : Continuous fun η : ℝ => (η : ℂ) * Complex.exp (w₀ * (η : ℂ)) := by fun_prop
      exact this.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun η _ w hw => by
      rw [norm_mul, norm_exp_mul_ofReal, Complex.norm_real, Real.norm_eq_abs, hbound]
      simp only
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine Real.exp_le_exp.mpr ?_
      have h1 : w.re * η ≤ |w.re| * |η| := by
        rw [← abs_mul]; exact le_abs_self _
      have h2 : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
      have h3 : ‖w‖ ≤ ‖w₀‖ + 1 := by
        rw [Metric.mem_ball, dist_eq_norm] at hw
        calc ‖w‖ = ‖(w - w₀) + w₀‖ := by rw [sub_add_cancel]
          _ ≤ ‖w - w₀‖ + ‖w₀‖ := norm_add_le _ _
          _ ≤ ‖w₀‖ + 1 := by linarith
      calc w.re * η ≤ |w.re| * |η| := h1
        _ ≤ (‖w₀‖ + 1) * |η| := by
            refine mul_le_mul_of_nonneg_right (h2.trans h3) (abs_nonneg _)
        _ = |η| * (‖w₀‖ + 1) := by ring)
    (hcont_bound.intervalIntegrable _ _)
    (Filter.Eventually.of_forall fun η _ w _hw => by
      have h := (Complex.hasDerivAt_exp (w * (η : ℂ))).comp w
        ((hasDerivAt_id w).mul_const (η : ℂ))
      simp only [Function.comp_def, id, one_mul] at h
      exact h.congr_deriv (mul_comm _ _))
  exact key.2.const_mul (((1 / ell : ℝ) : ℂ))

lemma differentiable_avgExp (a ell : ℝ) : Differentiable ℂ (avgExp a ell) :=
  fun w => (hasDerivAt_avgExp a ell w).differentiableAt

lemma deriv_avgExp_zero (a : ℝ) {ell : ℝ} (hell : 0 < ell) :
    deriv (avgExp a ell) 0 = ((a + ell / 2 : ℝ) : ℂ) := by
  rw [(hasDerivAt_avgExp a ell 0).deriv]
  simp only [zero_mul, Complex.exp_zero, mul_one]
  rw [intervalIntegral.integral_ofReal, integral_id, ← Complex.ofReal_mul]
  congr 1
  field_simp
  ring

lemma hasDerivAt_avgExp_zero (a : ℝ) {ell : ℝ} (hell : 0 < ell) :
    HasDerivAt (avgExp a ell) ((a + ell / 2 : ℝ) : ℂ) 0 := by
  rw [← deriv_avgExp_zero a hell]
  exact (differentiable_avgExp a ell 0).hasDerivAt

lemma differentiable_Kker (M0 X ell : ℝ) : Differentiable ℂ (Kker M0 X ell) :=
  (differentiable_avgExp _ _).sub (differentiable_avgExp _ _)

lemma Kker_zero (M0 X : ℝ) {ell : ℝ} (hell : 0 < ell) : Kker M0 X ell 0 = 0 := by
  unfold Kker
  rw [avgExp_zero _ hell, avgExp_zero _ hell, sub_self]

lemma deriv_Kker_zero (M0 X : ℝ) {ell : ℝ} (hell : 0 < ell) :
    deriv (Kker M0 X ell) 0 = ((Real.log X - Real.log M0 : ℝ) : ℂ) := by
  show deriv (avgExp (Real.log X) ell - avgExp (Real.log M0) ell) 0 = _
  rw [((hasDerivAt_avgExp_zero (Real.log X) hell).sub
    (hasDerivAt_avgExp_zero (Real.log M0) hell)).deriv, ← Complex.ofReal_sub]
  congr 1; ring

lemma dslope_Kker_zero (M0 X : ℝ) {ell : ℝ} (hell : 0 < ell) :
    dslope (Kker M0 X ell) 0 0 = ((Real.log X - Real.log M0 : ℝ) : ℂ) := by
  rw [dslope_same, deriv_Kker_zero _ _ hell]

lemma dslope_Kker_of_ne (M0 X : ℝ) {ell : ℝ} (hell : 0 < ell) {w : ℂ} (hw : w ≠ 0) :
    dslope (Kker M0 X ell) 0 w = Kker M0 X ell w / w := by
  rw [dslope_of_ne _ hw, slope_def_field, Kker_zero _ _ hell, sub_zero, sub_zero]

/-- `G₁(0) = 𝒦'(0) = log X − log M₀` (`= (3/5)𝓛` at the frozen parameters). -/
lemma G1_zero (M0 X : ℝ) {ell : ℝ} (hell : 0 < ell) :
    G1 M0 X ell 0 = ((Real.log X - Real.log M0 : ℝ) : ℂ) := by
  rw [G1, zero_add, Complex.Gamma_one, one_mul, dslope_Kker_zero _ _ hell]

/-- Off `w = 0`, `G₁(w) = Γ(w)·𝒦(w)`. -/
lemma G1_eq_of_ne (M0 X : ℝ) {ell : ℝ} (hell : 0 < ell) {w : ℂ} (hw : w ≠ 0) :
    G1 M0 X ell w = Complex.Gamma w * Kker M0 X ell w := by
  rw [G1, Complex.Gamma_add_one w hw, dslope_Kker_of_ne _ _ hell hw]
  field_simp

/-- `G₁` is holomorphic on `Re w > −1`. -/
lemma differentiableAt_G1 (M0 X ell : ℝ) {w : ℂ} (hw : -1 < w.re) :
    DifferentiableAt ℂ (G1 M0 X ell) w := by
  have hne : ∀ n : ℕ, w + 1 ≠ -n := by
    intro n hcontra
    have := congrArg Complex.re hcontra
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)) w :=
    (Complex.differentiableAt_Gamma _ hne).comp w (differentiableAt_id.add_const 1)
  refine hΓ.mul ?_
  have hd : DifferentiableOn ℂ (dslope (Kker M0 X ell) 0) Set.univ :=
    (Complex.differentiableOn_dslope Filter.univ_mem).mpr
      (differentiable_Kker M0 X ell).differentiableOn
  exact (hd w (Set.mem_univ _)).differentiableAt Filter.univ_mem

lemma continuous_G1 (M0 X ell : ℝ) :
    ContinuousOn (G1 M0 X ell) {w : ℂ | -1 < w.re} := fun _ hw =>
  (differentiableAt_G1 M0 X ell hw).continuousAt.continuousWithinAt

/-! ### Bounds on `avgExp` and `𝒦` -/

/-- On `Re w ≤ 0` with `a ≥ 0`: `‖avgExp a ℓ w‖ ≤ e^{a·Re w}`. -/
lemma norm_avgExp_le_of_re_nonpos {a ell : ℝ} (_ha : 0 ≤ a) (hell : 0 < ell) {w : ℂ}
    (hw : w.re ≤ 0) : ‖avgExp a ell w‖ ≤ Real.exp (a * w.re) := by
  have hbd : ‖∫ η in a..(a + ell), Complex.exp (w * (η : ℂ))‖
      ≤ Real.exp (a * w.re) * |(a + ell) - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun η hη => ?_
    rw [Set.uIoc_of_le (by linarith)] at hη
    rw [norm_exp_mul_ofReal]
    exact Real.exp_le_exp.mpr (by nlinarith [hη.1])
  rw [avgExp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [add_sub_cancel_left, abs_of_pos hell] at hbd
  calc 1 / ell * ‖∫ η in a..(a + ell), Complex.exp (w * (η : ℂ))‖
      ≤ 1 / ell * (Real.exp (a * w.re) * ell) := by gcongr
    _ = Real.exp (a * w.re) := by field_simp

/-- On `Re w ≤ 1` with `a ≥ 0`: `‖avgExp a ℓ w‖ ≤ e^{a+ℓ}`. -/
lemma norm_avgExp_le_of_re_le_one {a ell : ℝ} (ha : 0 ≤ a) (hell : 0 < ell) {w : ℂ}
    (hw : w.re ≤ 1) : ‖avgExp a ell w‖ ≤ Real.exp (a + ell) := by
  have hbd : ‖∫ η in a..(a + ell), Complex.exp (w * (η : ℂ))‖
      ≤ Real.exp (a + ell) * |(a + ell) - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun η hη => ?_
    rw [Set.uIoc_of_le (by linarith)] at hη
    rw [norm_exp_mul_ofReal]
    refine Real.exp_le_exp.mpr ?_
    have hη0 : 0 ≤ η := by linarith [hη.1]
    nlinarith [hη.2]
  rw [avgExp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [add_sub_cancel_left, abs_of_pos hell] at hbd
  calc 1 / ell * ‖∫ η in a..(a + ell), Complex.exp (w * (η : ℂ))‖
      ≤ 1 / ell * (Real.exp (a + ell) * ell) := by gcongr
    _ = Real.exp (a + ell) := by field_simp

/-- Slope bound on `Re w ≤ 0`, `a ≥ 0`: `‖avgExp a ℓ w − 1‖ ≤ (a+ℓ)‖w‖`. -/
lemma norm_avgExp_sub_one_le {a ell : ℝ} (ha : 0 ≤ a) (hell : 0 < ell) {w : ℂ}
    (hw : w.re ≤ 0) : ‖avgExp a ell w - 1‖ ≤ (a + ell) * ‖w‖ := by
  have hone : (1 : ℂ) = ((1 / ell : ℝ) : ℂ) * ∫ η in a..(a + ell), (1 : ℂ) := by
    rw [intervalIntegral.integral_const, add_sub_cancel_left, Complex.real_smul, mul_one,
      ← Complex.ofReal_mul]
    have : (1 / ell) * ell = 1 := by field_simp
    rw [this, Complex.ofReal_one]
  rw [avgExp, hone, ← mul_sub, ← intervalIntegral.integral_sub
    (intervalIntegrable_exp_mul_ofReal w a (a + ell)) intervalIntegrable_const]
  have hbd : ‖∫ η in a..(a + ell), (Complex.exp (w * (η : ℂ)) - 1)‖
      ≤ ((a + ell) * ‖w‖) * |(a + ell) - a| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun η hη => ?_
    rw [Set.uIoc_of_le (by linarith)] at hη
    have hre : (w * (η : ℂ)).re ≤ 0 := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hw (by linarith [hη.1])
    calc ‖Complex.exp (w * (η : ℂ)) - 1‖ ≤ ‖w * (η : ℂ)‖ :=
          norm_exp_sub_one_le_of_re_nonpos hre
      _ = ‖w‖ * |η| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖w‖ * (a + ell) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [abs_of_nonneg (by linarith [hη.1])]
          exact hη.2
      _ = (a + ell) * ‖w‖ := by ring
  rw [add_sub_cancel_left, abs_of_pos hell] at hbd
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / ell * ‖∫ η in a..(a + ell), (Complex.exp (w * (η : ℂ)) - 1)‖
      ≤ 1 / ell * (((a + ell) * ‖w‖) * ell) := by gcongr
    _ = (a + ell) * ‖w‖ := by field_simp

/-- Decay bound on `Re w ≤ 0`, `w ≠ 0`, `a ≥ 0`: `‖avgExp a ℓ w‖ ≤ 2/(ℓ‖w‖)`. -/
lemma norm_avgExp_le_div {a ell : ℝ} (ha : 0 ≤ a) (hell : 0 < ell) {w : ℂ}
    (hw : w.re ≤ 0) (hw0 : w ≠ 0) : ‖avgExp a ell w‖ ≤ 2 / (ell * ‖w‖) := by
  rw [avgExp_eq_of_ne hw0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity), norm_div]
  have hw0' : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have h1 : ‖Complex.exp (w * ((a + ell : ℝ) : ℂ))‖ ≤ 1 := by
    rw [norm_exp_mul_ofReal]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hw (by linarith))
  have h2 : ‖Complex.exp (w * (a : ℂ))‖ ≤ 1 := by
    rw [norm_exp_mul_ofReal]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hw ha)
  have h3 : ‖Complex.exp (w * ((a + ell : ℝ) : ℂ)) - Complex.exp (w * (a : ℂ))‖ ≤ 2 := by
    calc _ ≤ ‖Complex.exp (w * ((a + ell : ℝ) : ℂ))‖ + ‖Complex.exp (w * (a : ℂ))‖ :=
          norm_sub_le _ _
      _ ≤ 2 := by linarith
  calc 1 / ell * (‖Complex.exp (w * ((a + ell : ℝ) : ℂ)) - Complex.exp (w * (a : ℂ))‖ / ‖w‖)
      ≤ 1 / ell * (2 / ‖w‖) := by gcongr
    _ = 2 / (ell * ‖w‖) := by field_simp

/-! ### Bounds on `𝒦` and on `G₁` (blueprint Lemma 6.2) -/

/-- (K1′) On `Re w ≤ 0`: `‖𝒦(w)‖ ≤ e^{log X·Re w} + e^{log M₀·Re w}`. -/
lemma norm_Kker_le_of_re_nonpos {M0 X ell : ℝ} (hM0 : 0 ≤ Real.log M0) (hX : 0 ≤ Real.log X)
    (hell : 0 < ell) {w : ℂ} (hw : w.re ≤ 0) :
    ‖Kker M0 X ell w‖ ≤ Real.exp (Real.log X * w.re) + Real.exp (Real.log M0 * w.re) :=
  (norm_sub_le _ _).trans (add_le_add (norm_avgExp_le_of_re_nonpos hX hell hw)
    (norm_avgExp_le_of_re_nonpos hM0 hell hw))

/-- (K1) On `Re w ≤ 0`: `‖𝒦(w)‖ ≤ 2`. -/
lemma norm_Kker_le_two {M0 X ell : ℝ} (hM0 : 0 ≤ Real.log M0) (hX : 0 ≤ Real.log X)
    (hell : 0 < ell) {w : ℂ} (hw : w.re ≤ 0) : ‖Kker M0 X ell w‖ ≤ 2 := by
  refine (norm_Kker_le_of_re_nonpos hM0 hX hell hw).trans ?_
  have h1 : Real.exp (Real.log X * w.re) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hX hw)
  have h2 : Real.exp (Real.log M0 * w.re) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hM0 hw)
  linarith

/-- (K4) On `Re w ≤ 1`: `‖𝒦(w)‖ ≤ e^{log X+ℓ} + e^{log M₀+ℓ}`. -/
lemma norm_Kker_le_of_re_le_one {M0 X ell : ℝ} (hM0 : 0 ≤ Real.log M0) (hX : 0 ≤ Real.log X)
    (hell : 0 < ell) {w : ℂ} (hw : w.re ≤ 1) :
    ‖Kker M0 X ell w‖ ≤ Real.exp (Real.log X + ell) + Real.exp (Real.log M0 + ell) :=
  (norm_sub_le _ _).trans (add_le_add (norm_avgExp_le_of_re_le_one hX hell hw)
    (norm_avgExp_le_of_re_le_one hM0 hell hw))

/-- (K3, slope) On `Re w ≤ 0`: `‖𝒦(w)‖ ≤ (log X + log M₀ + 2ℓ)·‖w‖`. -/
lemma norm_Kker_le_slope {M0 X ell : ℝ} (hM0 : 0 ≤ Real.log M0) (hX : 0 ≤ Real.log X)
    (hell : 0 < ell) {w : ℂ} (hw : w.re ≤ 0) :
    ‖Kker M0 X ell w‖ ≤ (Real.log X + Real.log M0 + 2 * ell) * ‖w‖ := by
  have h : Kker M0 X ell w = (avgExp (Real.log X) ell w - 1) - (avgExp (Real.log M0) ell w - 1) := by
    rw [Kker]; ring
  rw [h]
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_avgExp_sub_one_le hX hell hw
  have h2 := norm_avgExp_sub_one_le hM0 hell hw
  nlinarith [norm_nonneg w]

/-- (K2, decay) On `Re w ≤ 0`, `w ≠ 0`: `‖𝒦(w)‖ ≤ 4/(ℓ‖w‖)`. -/
lemma norm_Kker_le_div {M0 X ell : ℝ} (hM0 : 0 ≤ Real.log M0) (hX : 0 ≤ Real.log X)
    (hell : 0 < ell) {w : ℂ} (hw : w.re ≤ 0) (hw0 : w ≠ 0) :
    ‖Kker M0 X ell w‖ ≤ 4 / (ell * ‖w‖) := by
  refine (norm_sub_le _ _).trans ?_
  have h1 := norm_avgExp_le_div hX hell hw hw0
  have h2 := norm_avgExp_le_div hM0 hell hw hw0
  have : 4 / (ell * ‖w‖) = 2 / (ell * ‖w‖) + 2 / (ell * ‖w‖) := by ring
  linarith

/-- The slope bound for `dslope 𝒦 0`, valid on all of `Re w ≤ 0` including `w = 0`. -/
lemma norm_dslope_Kker_le {M0 X ell : ℝ} (hM0 : 0 ≤ Real.log M0) (hX : 0 ≤ Real.log X)
    (hell : 0 < ell) {w : ℂ} (hw : w.re ≤ 0) :
    ‖dslope (Kker M0 X ell) 0 w‖ ≤ Real.log X + Real.log M0 + 2 * ell := by
  rcases eq_or_ne w 0 with rfl | hw0
  · rw [dslope_Kker_zero _ _ hell, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  · rw [dslope_Kker_of_ne _ _ hell hw0, norm_div, div_le_iff₀ (norm_pos_iff.mpr hw0)]
    exact norm_Kker_le_slope hM0 hX hell hw

/-- The constant of blueprint Lemma 6.2: `C₇ = 1608·(1 + C_Γ)`. -/
def C7 : ℝ := 1608 * (1 + GammaStrip.CGamma)

lemma C7_def : C7 = 1608 * (1 + GammaStrip.CGamma) := rfl

lemma C7_pos : 0 < C7 := by rw [C7_def, GammaStrip.CGamma_def]; norm_num

/-- **Blueprint Lemma 6.2 (kernel bounds), core form.**  For `z = −𝔰` with
`−1/50 ≤ Re z ≤ 0`, writing `θ = Im z`, the three bounds
`‖G₁(z)‖ ≤ C₇ e^{−|θ|/2} L`, `|θ|·‖G₁(z)‖ ≤ C₇ e^{−|θ|/2}`, `θ²ℓ·‖G₁(z)‖ ≤ 4C₇ e^{−|θ|/2}`
hold whenever `0 ≤ log M₀ ≤ log X`, `ℓ > 0`, `L ≥ 1` and `log X + log M₀ + 2ℓ ≤ (5/2)L`.
(The three product forms replace the blueprint's `min(L, 1/|θ|, 4/(θ²ℓ))`, which in Lean
would read `0` at `θ = 0`.) -/
theorem G1_bounds {M0 X ell L : ℝ} (hM0 : 0 ≤ Real.log M0) (hMX : Real.log M0 ≤ Real.log X)
    (hell : 0 < ell) (hL : 1 ≤ L) (hsum : Real.log X + Real.log M0 + 2 * ell ≤ 5 / 2 * L)
    {z : ℂ} (hz0 : -(1 / 50) ≤ z.re) (hz1 : z.re ≤ 0) :
    ‖G1 M0 X ell z‖ ≤ C7 * Real.exp (-|z.im| / 2) * L
    ∧ |z.im| * ‖G1 M0 X ell z‖ ≤ C7 * Real.exp (-|z.im| / 2)
    ∧ z.im ^ 2 * ell * ‖G1 M0 X ell z‖ ≤ 4 * C7 * Real.exp (-|z.im| / 2) := by
  have hX : 0 ≤ Real.log X := hM0.trans hMX
  have hCΓ : 0 < GammaStrip.CGamma := GammaStrip.CGamma_pos
  have hC7 := C7_pos
  have hexp_pos : 0 < Real.exp (-|z.im| / 2) := Real.exp_pos _
  have hexp_le : Real.exp (-|z.im| / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := abs_nonneg z.im; linarith)
  have hθz : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hθ0 : 0 ≤ |z.im| := abs_nonneg _
  have hsq : z.im ^ 2 = |z.im| ^ 2 := (sq_abs _).symm
  rcases eq_or_ne z 0 with rfl | hz
  · -- `z = 0`
    rw [G1_zero _ _ hell]
    simp only [Complex.zero_im, abs_zero, neg_zero, zero_div, Real.exp_zero, mul_one,
      zero_mul, Complex.norm_real, Real.norm_eq_abs, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    have hC7L : 5 / 2 * L ≤ C7 * L :=
      mul_le_mul_of_nonneg_right (by rw [C7_def]; linarith) (by linarith)
    refine ⟨?_, by positivity, by positivity⟩
    rw [abs_le]
    constructor <;> nlinarith
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [G1_eq_of_ne _ _ hell hz, norm_mul]
  have hK1 := norm_Kker_le_two hM0 hX hell hz1
  have hK2 := norm_Kker_le_div hM0 hX hell hz1 hz
  have hK3 := norm_Kker_le_slope hM0 hX hell hz1
  have hK3' : ‖Kker M0 X ell z‖ ≤ 5 / 2 * L * ‖z‖ := by
    refine hK3.trans ?_
    exact mul_le_mul_of_nonneg_right hsum hzn.le
  have hKnn : 0 ≤ ‖Kker M0 X ell z‖ := norm_nonneg _
  rcases le_or_gt ‖z‖ (3 / 4) with hsmall | hbig
  · -- regime I: `‖z‖ ≤ 3/4`, I8(a)
    have hΓ : ‖Complex.Gamma z‖ ≤ ‖z‖⁻¹ + GammaStrip.CGamma := by
      have h := GammaStrip.norm_Gamma_sub_inv_le z hz hsmall (by linarith)
      calc ‖Complex.Gamma z‖ = ‖(Complex.Gamma z - z⁻¹) + z⁻¹‖ := by ring_nf
        _ ≤ ‖Complex.Gamma z - z⁻¹‖ + ‖z⁻¹‖ := norm_add_le _ _
        _ ≤ GammaStrip.CGamma + ‖z‖⁻¹ := by rw [norm_inv]; linarith
        _ = ‖z‖⁻¹ + GammaStrip.CGamma := by ring
    have hΓz : ‖Complex.Gamma z‖ * ‖z‖ ≤ 1 + GammaStrip.CGamma := by
      calc ‖Complex.Gamma z‖ * ‖z‖ ≤ (‖z‖⁻¹ + GammaStrip.CGamma) * ‖z‖ :=
            mul_le_mul_of_nonneg_right hΓ hzn.le
        _ = 1 + GammaStrip.CGamma * ‖z‖ := by field_simp
        _ ≤ 1 + GammaStrip.CGamma := by nlinarith
    -- `1 ≤ 2 e^{−|θ|/2}` in this regime
    have hcomp : 1 ≤ 2 * Real.exp (-|z.im| / 2) := by
      have h1 : Real.exp (-(3 / 8)) ≤ Real.exp (-|z.im| / 2) :=
        Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (-(3 / 8)) * Real.exp (3 / 8) = 1 := by
        rw [← Real.exp_add]; norm_num
      have h3 := exp_three_eighths_le_two
      nlinarith [Real.exp_pos (3 / 8), Real.exp_pos (-(3 / 8))]
    have hΓnn : 0 ≤ ‖Complex.Gamma z‖ := norm_nonneg _
    refine ⟨?_, ?_, ?_⟩
    · -- entry `L`
      calc ‖Complex.Gamma z‖ * ‖Kker M0 X ell z‖
          ≤ ‖Complex.Gamma z‖ * (5 / 2 * L * ‖z‖) := mul_le_mul_of_nonneg_left hK3' hΓnn
        _ = 5 / 2 * L * (‖Complex.Gamma z‖ * ‖z‖) := by ring
        _ ≤ 5 / 2 * L * (1 + GammaStrip.CGamma) := by gcongr
        _ = 5 / 2 * ((1 + GammaStrip.CGamma) * L) * 1 := by ring
        _ ≤ 5 / 2 * ((1 + GammaStrip.CGamma) * L) * (2 * Real.exp (-|z.im| / 2)) := by
            gcongr
        _ ≤ C7 * Real.exp (-|z.im| / 2) * L := by
            have hL0 : 0 ≤ L := by linarith
            rw [C7_def]; nlinarith [mul_nonneg (mul_nonneg hCΓ.le hL0) hexp_pos.le,
              mul_nonneg hL0 hexp_pos.le]
    · -- entry `1/|θ|`
      calc |z.im| * (‖Complex.Gamma z‖ * ‖Kker M0 X ell z‖)
          ≤ ‖z‖ * (‖Complex.Gamma z‖ * 2) := by gcongr
        _ = 2 * (‖Complex.Gamma z‖ * ‖z‖) := by ring
        _ ≤ 2 * (1 + GammaStrip.CGamma) := by gcongr
        _ = (1 + GammaStrip.CGamma) * 1 * 2 := by ring
        _ ≤ (1 + GammaStrip.CGamma) * (2 * Real.exp (-|z.im| / 2)) * 2 := by gcongr
        _ ≤ C7 * Real.exp (-|z.im| / 2) := by rw [C7_def]; nlinarith
    · -- entry `4/(θ²ℓ)`
      have hK2' : ‖Kker M0 X ell z‖ * (ell * ‖z‖) ≤ 4 := by
        rw [le_div_iff₀ (by positivity)] at hK2; exact hK2
      calc z.im ^ 2 * ell * (‖Complex.Gamma z‖ * ‖Kker M0 X ell z‖)
          = |z.im| ^ 2 * ell * (‖Complex.Gamma z‖ * ‖Kker M0 X ell z‖) := by rw [hsq]
        _ ≤ ‖z‖ ^ 2 * ell * (‖Complex.Gamma z‖ * ‖Kker M0 X ell z‖) := by gcongr
        _ = (‖Complex.Gamma z‖ * ‖z‖) * (‖Kker M0 X ell z‖ * (ell * ‖z‖)) := by ring
        _ ≤ (1 + GammaStrip.CGamma) * 4 := by gcongr
        _ = (1 + GammaStrip.CGamma) * 1 * 4 := by ring
        _ ≤ (1 + GammaStrip.CGamma) * (2 * Real.exp (-|z.im| / 2)) * 4 := by gcongr
        _ ≤ 4 * C7 * Real.exp (-|z.im| / 2) := by rw [C7_def]; nlinarith
  · -- regime II: `‖z‖ > 3/4`, I8(b)
    have hθ : 1 / 2 ≤ |z.im| := by
      have h1 : ‖z‖ ≤ |z.re| + |z.im| := by
        have := Complex.norm_le_abs_re_add_abs_im z
        exact this
      have h2 : |z.re| ≤ 1 / 50 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have hθpos : 0 < |z.im| := by linarith
    have hΓ : ‖Complex.Gamma z‖ ≤ 201 * GammaStrip.CGamma * Real.exp (-|z.im|) := by
      refine GammaStrip.norm_Gamma_le_of_dist z (by linarith) (by linarith) (by linarith) ?_
      have := Complex.abs_re_le_norm (z + 1)
      rw [Complex.add_re, Complex.one_re] at this
      have h2 : 49 / 50 ≤ |z.re + 1| := by rw [abs_of_nonneg (by linarith)]; linarith
      linarith
    have hsplit : Real.exp (-|z.im|) = Real.exp (-|z.im| / 2) * Real.exp (-|z.im| / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hspare : Real.exp (-|z.im| / 2) ≤ 2 / |z.im| := exp_neg_half_le_two_div hθpos
    have hspare' : Real.exp (-|z.im| / 2) * |z.im| ≤ 2 := by
      rw [le_div_iff₀ hθpos] at hspare; exact hspare
    have hΓnn : 0 ≤ ‖Complex.Gamma z‖ := norm_nonneg _
    have hΓ' : ‖Complex.Gamma z‖ ≤ 201 * GammaStrip.CGamma * Real.exp (-|z.im| / 2) := by
      refine hΓ.trans ?_
      rw [hsplit]
      have : 201 * GammaStrip.CGamma * (Real.exp (-|z.im| / 2) * Real.exp (-|z.im| / 2))
          ≤ 201 * GammaStrip.CGamma * (Real.exp (-|z.im| / 2) * 1) := by gcongr
      linarith
    refine ⟨?_, ?_, ?_⟩
    · -- entry `L`
      calc ‖Complex.Gamma z‖ * ‖Kker M0 X ell z‖
          ≤ (201 * GammaStrip.CGamma * Real.exp (-|z.im| / 2)) * 2 := by gcongr
        _ = 402 * GammaStrip.CGamma * Real.exp (-|z.im| / 2) * 1 := by ring
        _ ≤ C7 * Real.exp (-|z.im| / 2) * L := by
            have h1 : 402 * GammaStrip.CGamma ≤ C7 := by rw [C7_def]; linarith
            gcongr
    · -- entry `1/|θ|`
      calc |z.im| * (‖Complex.Gamma z‖ * ‖Kker M0 X ell z‖)
          ≤ |z.im| * ((201 * GammaStrip.CGamma * Real.exp (-|z.im|)) * 2) := by gcongr
        _ = 402 * GammaStrip.CGamma * (Real.exp (-|z.im| / 2) * |z.im|)
              * Real.exp (-|z.im| / 2) := by rw [hsplit]; ring
        _ ≤ 402 * GammaStrip.CGamma * 2 * Real.exp (-|z.im| / 2) := by gcongr
        _ ≤ C7 * Real.exp (-|z.im| / 2) := by
            have h1 : 402 * GammaStrip.CGamma * 2 ≤ C7 := by rw [C7_def]; linarith
            gcongr
    · -- entry `4/(θ²ℓ)`
      have hK2' : ‖Kker M0 X ell z‖ * (ell * ‖z‖) ≤ 4 := by
        rw [le_div_iff₀ (by positivity)] at hK2; exact hK2
      have hθz2 : |z.im| ^ 2 ≤ |z.im| * ‖z‖ := by nlinarith
      calc z.im ^ 2 * ell * (‖Complex.Gamma z‖ * ‖Kker M0 X ell z‖)
          = |z.im| ^ 2 * ell * (‖Complex.Gamma z‖ * ‖Kker M0 X ell z‖) := by rw [hsq]
        _ ≤ (|z.im| * ‖z‖) * ell * ((201 * GammaStrip.CGamma * Real.exp (-|z.im|))
              * ‖Kker M0 X ell z‖) := by gcongr
        _ = 201 * GammaStrip.CGamma * (Real.exp (-|z.im| / 2) * |z.im|)
              * (‖Kker M0 X ell z‖ * (ell * ‖z‖)) * Real.exp (-|z.im| / 2) := by
            rw [hsplit]; ring
        _ ≤ 201 * GammaStrip.CGamma * 2 * 4 * Real.exp (-|z.im| / 2) := by gcongr
        _ ≤ 4 * C7 * Real.exp (-|z.im| / 2) := by
            have h1 : 201 * GammaStrip.CGamma * 2 * 4 ≤ 4 * C7 := by rw [C7_def]; linarith
            gcongr



/-! ## §2. Halász duality with majorants (blueprint Lemma 5.1) -/

/-- Cauchy–Schwarz for `tsum`s of nonnegative reals. -/
lemma tsum_mul_le_sqrt_mul_sqrt {x y : ℕ → ℝ} (hx : ∀ n, 0 ≤ x n) (hy : ∀ n, 0 ≤ y n)
    (hx2 : Summable fun n => x n ^ 2) (hy2 : Summable fun n => y n ^ 2) :
    ∑' n, x n * y n ≤ Real.sqrt (∑' n, x n ^ 2) * Real.sqrt (∑' n, y n ^ 2) := by
  refine Real.tsum_le_of_sum_le (fun n => mul_nonneg (hx n) (hy n)) fun s => ?_
  have h := Finset.sum_mul_sq_le_sq_mul_sq s x y
  have hs1 : ∑ i ∈ s, x i ^ 2 ≤ ∑' n, x n ^ 2 := hx2.sum_le_tsum s (fun n _ => sq_nonneg _)
  have hs2 : ∑ i ∈ s, y i ^ 2 ≤ ∑' n, y n ^ 2 := hy2.sum_le_tsum s (fun n _ => sq_nonneg _)
  have hA : 0 ≤ ∑' n, x n ^ 2 := tsum_nonneg fun n => sq_nonneg _
  have hB : 0 ≤ ∑' n, y n ^ 2 := tsum_nonneg fun n => sq_nonneg _
  have hs1' : 0 ≤ ∑ i ∈ s, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [← Real.sqrt_mul hA]
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  calc (∑ i ∈ s, x i * y i) ^ 2 ≤ (∑ i ∈ s, x i ^ 2) * ∑ i ∈ s, y i ^ 2 := h
    _ ≤ (∑' n, x n ^ 2) * ∑' n, y n ^ 2 := mul_le_mul hs1 hs2 (by positivity) hA

/-- `F(s,χ) = ∑_n c_n χ(n) n^{−s}` for general coefficients `c`. -/
noncomputable def Fgen {N : ℕ} (c : ℕ → ℂ) (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' n : ℕ, c n * χ n * (n : ℂ) ^ (-s)

/-- `B(s,χ) = ∑_n b_n χ(n) n^{−s}` for a general real majorant `b`. -/
noncomputable def Bgen {N : ℕ} (b : ℕ → ℝ) (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' n : ℕ, ((b n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-s)

lemma norm_natCast_cpow_neg_le_one {n : ℕ} {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(n : ℂ) ^ (-s)‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases eq_or_ne s 0 with rfl | hs0
    · simp
    · rw [Nat.cast_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0), norm_zero]; exact zero_le_one
  · rw [Complex.norm_natCast_cpow_of_pos hn]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by simp [hs])

/-- `conj (χ(n)) = χ⁻¹(n)` for Dirichlet characters. -/
lemma conj_char_apply {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (n : ℕ) :
    conj (χ n) = χ⁻¹ n := by
  rw [← MulChar.star_apply' χ (n : ZMod N)]
  rfl

/-- `conj (n^{−s}) = n^{−conj s}` for `n : ℕ`. -/
lemma conj_natCast_cpow (n : ℕ) (s : ℂ) : conj ((n : ℂ) ^ (-s)) = (n : ℂ) ^ (-conj s) := by
  have h := Complex.cpow_conj (n : ℂ) (-s) (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
  rw [Complex.conj_natCast, map_neg] at h
  exact h.symm

/-- Termwise identity: `χ_j(n)·conj χ_k(n)·n^{−s_j}·conj(n^{−s_k}) = (χ_jχ_k⁻¹)(n)·n^{−(s_j+conj s_k)}`
for `n ≠ 0`. -/
lemma char_cpow_mul_conj {N : ℕ} [NeZero N] (χj χk : DirichletCharacter ℂ N) (sj sk : ℂ)
    {n : ℕ} (hn : n ≠ 0) :
    χj n * (n : ℂ) ^ (-sj) * conj (χk n * (n : ℂ) ^ (-sk))
      = (χj * χk⁻¹) n * (n : ℂ) ^ (-(sj + conj sk)) := by
  rw [map_mul, conj_char_apply, conj_natCast_cpow, MulChar.mul_apply, neg_add,
    Complex.cpow_add _ _ (by exact_mod_cast hn)]
  ring

/-- **Blueprint Lemma 5.1 (Halász duality with majorants), general form.**  For a finite
family `(s_j, χ_j)` with `Re s_j ≥ 0`, coefficients `c` and a majorant `b ≥ 0` with
`b_n > 0` wherever `c_n ≠ 0`, `∑|c_n|²/b_n < ∞`, `∑ b_n < ∞` (and `c_0 = b_0 = 0`):
`(∑_j |F(s_j,χ_j)|)² ≤ (∑_n |c_n|²/b_n) · ∑_{j,k} |B(s_j + conj s_k, χ_j χ_k⁻¹)|`. -/
theorem halasz_duality {N : ℕ} [NeZero N] {J : Type*} [Fintype J]
    (s : J → ℂ) (χ : J → DirichletCharacter ℂ N) (hs : ∀ j, 0 ≤ (s j).re)
    (c : ℕ → ℂ) (b : ℕ → ℝ) (hb0 : b 0 = 0)
    (hb : ∀ n, 0 ≤ b n) (hbc : ∀ n, c n ≠ 0 → 0 < b n)
    (hsum : Summable fun n => ‖c n‖ ^ 2 / b n) (hbs : Summable b) :
    (∑ j, ‖Fgen c (χ j) (s j)‖) ^ 2
      ≤ (∑' n, ‖c n‖ ^ 2 / b n)
        * ∑ j, ∑ k, ‖Bgen b (χ j * (χ k)⁻¹) (s j + conj (s k))‖ := by
  classical
  set a : ℕ → ℝ := fun n => ‖c n‖ ^ 2 / b n with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => div_nonneg (sq_nonneg _) (hb n)
  -- `‖c_n‖ = √a_n · √b_n`
  have hcn : ∀ n, ‖c n‖ = Real.sqrt (a n) * Real.sqrt (b n) := by
    intro n
    rcases eq_or_ne (c n) 0 with h0 | h0
    · simp only [ha, h0, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        zero_div, Real.sqrt_zero, zero_mul]
    · have hbn : 0 < b n := hbc n h0
      simp only [ha]
      rw [← Real.sqrt_mul (by positivity), div_mul_cancel₀ _ hbn.ne', Real.sqrt_sq (norm_nonneg _)]
  -- absolute summability of `c`
  have hcsum : Summable fun n => ‖c n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((hsum.add hbs).div_const 2)
    rw [hcn n]
    have h1 := Real.sq_sqrt (ha0 n)
    have h2 := Real.sq_sqrt (hb n)
    have h3 := Real.sqrt_nonneg (a n)
    have h4 := Real.sqrt_nonneg (b n)
    show Real.sqrt (a n) * Real.sqrt (b n) ≤ (a n + b n) / 2
    nlinarith [sq_nonneg (Real.sqrt (a n) - Real.sqrt (b n))]
  -- the detector values and the unimodular phases
  set F : J → ℂ := fun j => Fgen c (χ j) (s j) with hF
  set η : J → ℂ := fun j => if F j = 0 then 1 else F j / (‖F j‖ : ℂ) with hη
  have hη1 : ∀ j, ‖η j‖ = 1 := by
    intro j
    simp only [hη]
    split_ifs with h
    · simp
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr h)]
  have hηF : ∀ j, conj (η j) * F j = (‖F j‖ : ℂ) := by
    intro j
    simp only [hη]
    split_ifs with h
    · simp [h]
    · have hF0 : ‖F j‖ ≠ 0 := norm_ne_zero_iff.mpr h
      rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul',
        ← Complex.ofReal_pow, ← Complex.ofReal_div]
      congr 1
      field_simp
  -- termwise summability of the detector series
  have hterm : ∀ j, Summable fun n : ℕ => c n * χ j n * (n : ℂ) ^ (-(s j)) := by
    intro j
    refine Summable.of_norm_bounded hcsum fun n => ?_
    rw [norm_mul, norm_mul]
    calc ‖c n‖ * ‖χ j n‖ * ‖(n : ℂ) ^ (-(s j))‖ ≤ ‖c n‖ * 1 * 1 := by
          gcongr
          · exact (χ j).norm_le_one _
          · exact norm_natCast_cpow_neg_le_one (hs j)
      _ = ‖c n‖ := by ring
  -- `G(n) = ∑_j conj η_j χ_j(n) n^{−s_j}`
  set G : ℕ → ℂ := fun n => ∑ j, conj (η j) * (χ j n * (n : ℂ) ^ (-(s j))) with hG
  have hGle : ∀ n, ‖G n‖ ≤ Fintype.card J := by
    intro n
    simp only [hG]
    calc ‖∑ j, conj (η j) * (χ j n * (n : ℂ) ^ (-(s j)))‖
        ≤ ∑ j, ‖conj (η j) * (χ j n * (n : ℂ) ^ (-(s j)))‖ := norm_sum_le _ _
      _ ≤ ∑ _j : J, (1 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj, hη1]
          calc 1 * (‖χ j n‖ * ‖(n : ℂ) ^ (-(s j))‖) ≤ 1 * (1 * 1) := by
                gcongr
                · exact (χ j).norm_le_one _
                · exact norm_natCast_cpow_neg_le_one (hs j)
            _ = 1 := by ring
      _ = Fintype.card J := by simp
  -- Step 1: `∑_j ‖F_j‖ = ∑_n c_n G(n)`
  have hstep1 : ((∑ j, ‖F j‖ : ℝ) : ℂ) = ∑' n, c n * G n := by
    push_cast
    calc ∑ j, (‖F j‖ : ℂ) = ∑ j, conj (η j) * F j := by simp_rw [hηF]
      _ = ∑ j, ∑' n, conj (η j) * (c n * χ j n * (n : ℂ) ^ (-(s j))) := by
          simp_rw [hF, Fgen, tsum_mul_left]
      _ = ∑' n, ∑ j, conj (η j) * (c n * χ j n * (n : ℂ) ^ (-(s j))) := by
          rw [Summable.tsum_finsetSum]
          intro j _
          exact (hterm j).mul_left _
      _ = ∑' n, c n * G n := by
          refine tsum_congr fun n => ?_
          simp only [hG, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  -- Step 2: Cauchy–Schwarz
  have hcG : Summable fun n => ‖c n * G n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      (hcsum.mul_right (Fintype.card J : ℝ))
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hGle n) (norm_nonneg _)
  have hy2 : Summable fun n => (Real.sqrt (b n) * ‖G n‖) ^ 2 := by
    refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_)
      (hbs.mul_right ((Fintype.card J : ℝ) ^ 2))
    rw [mul_pow, Real.sq_sqrt (hb n)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hGle n) 2) (hb n)
  have hx2 : Summable fun n => (Real.sqrt (a n)) ^ 2 := by
    refine hsum.congr fun n => ?_
    rw [Real.sq_sqrt (ha0 n)]
  have hCS : ∑' n, ‖c n * G n‖
      ≤ Real.sqrt (∑' n, a n) * Real.sqrt (∑' n, b n * ‖G n‖ ^ 2) := by
    have h := tsum_mul_le_sqrt_mul_sqrt (x := fun n => Real.sqrt (a n))
      (y := fun n => Real.sqrt (b n) * ‖G n‖) (fun n => Real.sqrt_nonneg _)
      (fun n => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hx2 hy2
    have e1 : ∀ n, ‖c n * G n‖ = Real.sqrt (a n) * (Real.sqrt (b n) * ‖G n‖) := by
      intro n; rw [norm_mul, hcn n]; ring
    have e2 : ∀ n, (Real.sqrt (a n)) ^ 2 = a n := fun n => Real.sq_sqrt (ha0 n)
    have e3 : ∀ n, (Real.sqrt (b n) * ‖G n‖) ^ 2 = b n * ‖G n‖ ^ 2 := by
      intro n; rw [mul_pow, Real.sq_sqrt (hb n)]
    simp only [e1, e2, e3] at h ⊢
    exact h
  have hsqF : (∑ j, ‖F j‖) ^ 2 ≤ (∑' n, a n) * ∑' n, b n * ‖G n‖ ^ 2 := by
    have hA : 0 ≤ ∑' n, a n := tsum_nonneg ha0
    have hB : 0 ≤ ∑' n, b n * ‖G n‖ ^ 2 := tsum_nonneg fun n => mul_nonneg (hb n) (sq_nonneg _)
    have h1 : ∑ j, ‖F j‖ ≤ ∑' n, ‖c n * G n‖ := by
      have := norm_tsum_le_tsum_norm hcG
      rw [← hstep1, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Finset.sum_nonneg fun j _ => norm_nonneg _)] at this
      exact this
    have h2 : ∑ j, ‖F j‖ ≤ Real.sqrt ((∑' n, a n) * ∑' n, b n * ‖G n‖ ^ 2) := by
      rw [Real.sqrt_mul hA]; exact h1.trans hCS
    have h3 : 0 ≤ ∑ j, ‖F j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
    calc (∑ j, ‖F j‖) ^ 2 ≤ (Real.sqrt ((∑' n, a n) * ∑' n, b n * ‖G n‖ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ h3 h2 2
      _ = (∑' n, a n) * ∑' n, b n * ‖G n‖ ^ 2 := Real.sq_sqrt (mul_nonneg hA hB)
  -- Step 3: expand `∑_n b_n |G(n)|²` into Gram values
  have hBterm : ∀ j k, Summable fun n : ℕ =>
      ((b n : ℝ) : ℂ) * (χ j * (χ k)⁻¹) n * (n : ℂ) ^ (-(s j + conj (s k))) := by
    intro j k
    refine Summable.of_norm_bounded hbs fun n => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb n)]
    have hre : 0 ≤ (s j + conj (s k)).re := by
      rw [Complex.add_re, Complex.conj_re]; linarith [hs j, hs k]
    calc b n * ‖(χ j * (χ k)⁻¹) n‖ * ‖(n : ℂ) ^ (-(s j + conj (s k)))‖ ≤ b n * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left ((χ j * (χ k)⁻¹).norm_le_one _) (hb n))
            (norm_natCast_cpow_neg_le_one hre) (norm_nonneg _) (by linarith [hb n])
      _ = b n := by ring
  have hexpand : ∀ n, ((b n * ‖G n‖ ^ 2 : ℝ) : ℂ)
      = ∑ j, ∑ k, (conj (η j) * η k)
          * (((b n : ℝ) : ℂ) * (χ j * (χ k)⁻¹) n * (n : ℂ) ^ (-(s j + conj (s k)))) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hb0]
    have hGG : ((‖G n‖ ^ 2 : ℝ) : ℂ) = G n * conj (G n) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [Complex.ofReal_mul, hGG]
    simp only [hG]
    rw [map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Complex.conj_conj]
    have := char_cpow_mul_conj (χ j) (χ k) (s j) (s k) hn
    linear_combination ((b n : ℝ) : ℂ) * conj (η j) * η k * this
  have hstep3 : ∑' n, b n * ‖G n‖ ^ 2
      ≤ ∑ j, ∑ k, ‖Bgen b (χ j * (χ k)⁻¹) (s j + conj (s k))‖ := by
    have hsum2 : Summable fun n => b n * ‖G n‖ ^ 2 := by
      refine Summable.of_nonneg_of_le (fun n => mul_nonneg (hb n) (sq_nonneg _)) (fun n => ?_)
        (hbs.mul_right ((Fintype.card J : ℝ) ^ 2))
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hGle n) 2) (hb n)
    have hcast : ((∑' n, b n * ‖G n‖ ^ 2 : ℝ) : ℂ)
        = ∑ j, ∑ k, (conj (η j) * η k) * Bgen b (χ j * (χ k)⁻¹) (s j + conj (s k)) := by
      rw [Complex.ofReal_tsum]
      simp_rw [hexpand]
      rw [Summable.tsum_finsetSum fun j _ => ?_]
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [Summable.tsum_finsetSum fun k _ => (hBterm j k).mul_left _]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [tsum_mul_left, Bgen]
      · exact summable_sum fun k _ => (hBterm j k).mul_left _
    have hnn : 0 ≤ ∑' n, b n * ‖G n‖ ^ 2 := tsum_nonneg fun n => mul_nonneg (hb n) (sq_nonneg _)
    calc ∑' n, b n * ‖G n‖ ^ 2 = ‖((∑' n, b n * ‖G n‖ ^ 2 : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      _ = ‖∑ j, ∑ k, (conj (η j) * η k) * Bgen b (χ j * (χ k)⁻¹) (s j + conj (s k))‖ := by
          rw [hcast]
      _ ≤ ∑ j, ∑ k, ‖(conj (η j) * η k) * Bgen b (χ j * (χ k)⁻¹) (s j + conj (s k))‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
      _ = ∑ j, ∑ k, ‖Bgen b (χ j * (χ k)⁻¹) (s j + conj (s k))‖ := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj, hη1, hη1, one_mul, one_mul]
  -- assemble
  have hA : 0 ≤ ∑' n, a n := tsum_nonneg ha0
  calc (∑ j, ‖Fgen c (χ j) (s j)‖) ^ 2 = (∑ j, ‖F j‖) ^ 2 := rfl
    _ ≤ (∑' n, a n) * ∑' n, b n * ‖G n‖ ^ 2 := hsqF
    _ ≤ (∑' n, a n) * ∑ j, ∑ k, ‖Bgen b (χ j * (χ k)⁻¹) (s j + conj (s k))‖ :=
        mul_le_mul_of_nonneg_left hstep3 hA


/-! ## §3. The Dirichlet series of `P(n)²`: `∑_n P(n)²χ(n)n^{−s} = M_h(s,χ)·L(s,χ)` -/

/-- `h(δ;r,r') = 0` unless `δ ∣ r·r'` (blueprint: `h` is supported on `δ ∣ rad(rr')`). -/
lemma hBV_eq_zero_of_not_dvd {r r' δ : ℕ} (h : ¬ δ ∣ r * r') : hBV r r' δ = 0 := by
  unfold hBV
  split_ifs with hsf
  · by_contra hne
    apply h
    have hall : ∀ p ∈ δ.primeFactors, p ∣ r * r' := by
      intro p hp
      by_contra hpd
      apply hne
      refine Finset.prod_eq_zero hp ?_
      have hpr : ¬ p ∣ r := fun hh => hpd (dvd_mul_of_dvd_left hh _)
      have hpr' : ¬ p ∣ r' := fun hh => hpd (dvd_mul_of_dvd_right hh _)
      simp [hPrime, hpr, hpr']
    rw [← Nat.prod_primeFactors_of_squarefree hsf]
    exact Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) hall
  · rfl

/-- A divisor sum of `h(·;r,r')·g` over `n` is the sum over the divisors of `r·r'` that
divide `n`. -/
lemma sum_divisors_hBV_eq {r r' n : ℕ} (hn : n ≠ 0) (hrr : r * r' ≠ 0) (g : ℕ → ℂ) :
    ∑ δ ∈ n.divisors, (hBV r r' δ : ℂ) * g δ
      = ∑ δ ∈ (r * r').divisors, if δ ∣ n then (hBV r r' δ : ℂ) * g δ else 0 := by
  classical
  rw [← Finset.sum_filter]
  have hset : (r * r').divisors.filter (fun δ => δ ∣ n)
      = n.divisors.filter (fun δ => δ ∣ r * r') := by
    ext δ
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨h2, hn⟩, h1⟩
    · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨⟨h2, hrr⟩, h1⟩
  rw [hset]
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) fun δ hδ hδ' => ?_
  have : ¬ δ ∣ r * r' := by
    intro hd
    exact hδ' (Finset.mem_filter.mpr ⟨hδ, hd⟩)
  rw [hBV_eq_zero_of_not_dvd this, Complex.ofReal_zero, zero_mul]

/-- The finite Dirichlet polynomial
`M_h(s,χ) = ∑'_{r,r' ≤ R} (rr')⁻¹ ∑_{δ ∣ rr'} h(δ;r,r') χ(δ) δ^{−s}` (blueprint §6). -/
noncomputable def Mh (N : ℕ) (R : ℝ) (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑ r ∈ Rset N R, ∑ r' ∈ Rset N R, ((r : ℂ) * (r' : ℂ))⁻¹
    * ∑ δ ∈ (r * r').divisors, (hBV r r' δ : ℂ) * χ δ * (δ : ℂ) ^ (-s)

/-- The `h`-mass `∑'_{r,r'} (rr')⁻¹ ∑_δ |h(δ;r,r')|`. -/
noncomputable def Hmass (N : ℕ) (R : ℝ) : ℝ :=
  ∑ r ∈ Rset N R, ∑ r' ∈ Rset N R, ((r : ℝ) * (r' : ℝ))⁻¹
    * ∑ δ ∈ (r * r').divisors, |hBV r r' δ|

lemma Hmass_nonneg (N : ℕ) (R : ℝ) : 0 ≤ Hmass N R :=
  Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun r' _ =>
    mul_nonneg (by positivity) (Finset.sum_nonneg fun δ _ => abs_nonneg _)

lemma differentiable_Mh (N : ℕ) (R : ℝ) (χ : DirichletCharacter ℂ N) :
    Differentiable ℂ (Mh N R χ) := by
  unfold Mh
  refine Differentiable.fun_sum fun r _ => Differentiable.fun_sum fun r' _ => ?_
  refine Differentiable.const_mul (Differentiable.fun_sum fun δ hδ => ?_) _
  have hδ0 : (δ : ℂ) ≠ 0 := by
    have := Nat.pos_of_mem_divisors hδ
    exact_mod_cast this.ne'
  exact (differentiable_const _).mul (differentiable_neg.const_cpow (Or.inl hδ0))

/-- `‖M_h(s,χ)‖ ≤ Hmass` on `Re s ≥ 0`. -/
lemma norm_Mh_le (N : ℕ) (R : ℝ) (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖Mh N R χ s‖ ≤ Hmass N R := by
  unfold Mh Hmass
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r' _ => ?_)
  rw [norm_mul, norm_inv, ← Complex.ofReal_natCast, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun δ hδ => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hδ : 0 < δ := Nat.pos_of_mem_divisors hδ
  have h1 : ‖χ δ‖ ≤ 1 := χ.norm_le_one _
  have h2 : ‖(δ : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hδ]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hδ) (by simp [hs])
  calc |hBV r r' δ| * ‖χ δ‖ * ‖(δ : ℂ) ^ (-s)‖ ≤ |hBV r r' δ| * 1 * 1 := by
        gcongr
    _ = |hBV r r' δ| := by ring

/-- `Hmass ≤ (∑'_{r ≤ R} r⁻¹ ∏_{p∣r}(p+1))²` (blueprint Lemma 3.3(b), summed). -/
lemma Hmass_le_sq (N : ℕ) (R : ℝ) :
    Hmass N R ≤ (∑ r ∈ Rset N R, (r : ℝ)⁻¹ * ∏ p ∈ r.primeFactors, ((p : ℝ) + 1)) ^ 2 := by
  rw [sq, Finset.sum_mul_sum]
  unfold Hmass
  refine Finset.sum_le_sum fun r hr => Finset.sum_le_sum fun r' hr' => ?_
  have hsr : Squarefree r := (mem_Rset.mp hr).2.1
  have hsr' : Squarefree r' := (mem_Rset.mp hr').2.1
  have h := sum_abs_hBV_le hsr hsr'
  have h0 : 0 ≤ ((r : ℝ) * (r' : ℝ))⁻¹ := by positivity
  calc ((r : ℝ) * (r' : ℝ))⁻¹ * ∑ δ ∈ (r * r').divisors, |hBV r r' δ|
      ≤ ((r : ℝ) * (r' : ℝ))⁻¹ * ((∏ p ∈ r.primeFactors, ((p : ℝ) + 1))
          * ∏ p ∈ r'.primeFactors, ((p : ℝ) + 1)) := mul_le_mul_of_nonneg_left h h0
    _ = (r : ℝ)⁻¹ * (∏ p ∈ r.primeFactors, ((p : ℝ) + 1))
          * ((r' : ℝ)⁻¹ * ∏ p ∈ r'.primeFactors, ((p : ℝ) + 1)) := by
        rw [mul_inv]; ring

/-- `∏_{p∣r}(p+1) ≤ 2^{ω(r)}·r` for squarefree `r`. -/
lemma prod_primeFactors_add_one_le_two_pow_mul {r : ℕ} (hr : Squarefree r) :
    ∏ p ∈ r.primeFactors, ((p : ℝ) + 1) ≤ 2 ^ r.primeFactors.card * (r : ℝ) := by
  have h4 : ∏ p ∈ r.primeFactors, (p : ℝ) = (r : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hr]
  calc ∏ p ∈ r.primeFactors, ((p : ℝ) + 1)
      ≤ ∏ p ∈ r.primeFactors, (2 * (p : ℝ)) := by
        refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
        have : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
        linarith
    _ = 2 ^ r.primeFactors.card * (r : ℝ) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, h4]

/-- The coefficient mass, log-free: `Hmass ≤ C_τ²·R^{801/400}` for `R ≥ 1`
(`2^{ω(r)} ≤ C_τ r^{1/800}` and `#Rset ≤ R`). -/
theorem Hmass_le (N : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    Hmass N R ≤ Ctau ^ 2 * R ^ (801 / 400 : ℝ) := by
  have hR0 : 0 < R := by linarith
  have hsum : ∑ r ∈ Rset N R, (r : ℝ)⁻¹ * ∏ p ∈ r.primeFactors, ((p : ℝ) + 1)
      ≤ Ctau * R ^ (801 / 800 : ℝ) := by
    calc ∑ r ∈ Rset N R, (r : ℝ)⁻¹ * ∏ p ∈ r.primeFactors, ((p : ℝ) + 1)
        ≤ ∑ _r ∈ Rset N R, Ctau * R ^ (1 / 800 : ℝ) := by
          refine Finset.sum_le_sum fun r hr => ?_
          obtain ⟨⟨hr1, hrR⟩, hsf, -⟩ := mem_Rset.mp hr
          have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
          have hrR' : (r : ℝ) ≤ R := by
            calc (r : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast hrR
              _ ≤ R := Nat.floor_le hR0.le
          calc (r : ℝ)⁻¹ * ∏ p ∈ r.primeFactors, ((p : ℝ) + 1)
              ≤ (r : ℝ)⁻¹ * (2 ^ r.primeFactors.card * (r : ℝ)) :=
                mul_le_mul_of_nonneg_left (prod_primeFactors_add_one_le_two_pow_mul hsf)
                  (by positivity)
            _ = 2 ^ r.primeFactors.card := by field_simp
            _ ≤ (2 : ℝ) ^ (2 ^ 800 : ℕ) * (r : ℝ) ^ ((1 : ℝ) / 800) :=
                two_pow_card_primeFactors_le_rpow (by omega)
            _ = Ctau * (r : ℝ) ^ ((1 : ℝ) / 800) := by rw [Ctau_def]
            _ ≤ Ctau * R ^ (1 / 800 : ℝ) := by
                refine mul_le_mul_of_nonneg_left ?_ Ctau_pos.le
                exact Real.rpow_le_rpow hr0.le hrR' (by norm_num)
      _ = (Rset N R).card * (Ctau * R ^ (1 / 800 : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ R * (Ctau * R ^ (1 / 800 : ℝ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by have := Ctau_pos; positivity)
          calc ((Rset N R).card : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast card_Rset_le N R
            _ ≤ R := Nat.floor_le hR0.le
      _ = Ctau * R ^ (801 / 800 : ℝ) := by
          rw [show R ^ (801 / 800 : ℝ) = R ^ (1 : ℝ) * R ^ (1 / 800 : ℝ) from by
            rw [← Real.rpow_add hR0]; norm_num, Real.rpow_one]
          ring
  have h0 : 0 ≤ ∑ r ∈ Rset N R, (r : ℝ)⁻¹ * ∏ p ∈ r.primeFactors, ((p : ℝ) + 1) :=
    Finset.sum_nonneg fun r _ => mul_nonneg (by positivity)
      (Finset.prod_nonneg fun p _ => by positivity)
  calc Hmass N R ≤ (∑ r ∈ Rset N R, (r : ℝ)⁻¹ * ∏ p ∈ r.primeFactors, ((p : ℝ) + 1)) ^ 2 :=
        Hmass_le_sq N R
    _ ≤ (Ctau * R ^ (801 / 800 : ℝ)) ^ 2 := pow_le_pow_left₀ h0 hsum 2
    _ = Ctau ^ 2 * R ^ (801 / 400 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast (R ^ (801 / 800 : ℝ)) 2, ← Real.rpow_mul hR0.le]
        norm_num

/-! ### The identity `∑_n P(n)² χ(n) n^{−s} = M_h(s,χ) L(s,χ)` on `Re s > 1` -/

/-- `L(s,χ) = ∑_n χ(n) n^{−s}` on `Re s > 1`, in the `cpow` form. -/
lemma LFunction_eq_tsum {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    χ.LFunction s = ∑' n : ℕ, χ n * (n : ℂ) ^ (-s) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs, LSeries]
  refine tsum_congr fun n => ?_
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; norm_num at hs
  rw [LSeries.term_of_ne_zero' hs0, Complex.cpow_neg, div_eq_mul_inv]

lemma summable_char_cpow {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ => χ n * (n : ℂ) ^ (-s) := by
  have h := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; norm_num at hs
  refine h.congr fun n => ?_
  rw [LSeries.term_of_ne_zero' hs0, Complex.cpow_neg, div_eq_mul_inv]

/-- The sum over multiples of `δ`: `∑_{δ ∣ n} χ(n) n^{−s} = χ(δ) δ^{−s} ∑_m χ(m) m^{−s}`. -/
lemma tsum_multiples_char_cpow {N : ℕ} (χ : DirichletCharacter ℂ N) (s : ℂ)
    {δ : ℕ} (hδ : δ ≠ 0) :
    ∑' n : ℕ, (if δ ∣ n then χ n * (n : ℂ) ^ (-s) else 0)
      = χ δ * (δ : ℂ) ^ (-s) * ∑' m : ℕ, χ m * (m : ℂ) ^ (-s) := by
  rw [← tsum_mul_left]
  have hinj : Function.Injective (fun m : ℕ => δ * m) := mul_right_injective₀ hδ
  rw [← hinj.tsum_eq (f := fun n : ℕ => if δ ∣ n then χ n * (n : ℂ) ^ (-s) else 0)]
  · refine tsum_congr fun m => ?_
    simp only [dvd_mul_right, if_true, Nat.cast_mul, map_mul,
      Complex.natCast_mul_natCast_cpow]
    ring
  · intro n hn
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
    obtain ⟨k, hk⟩ := hn.1
    exact ⟨k, hk.symm⟩

lemma summable_ite_dvd {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) (δ : ℕ) :
    Summable fun n : ℕ => (if δ ∣ n then χ n * (n : ℂ) ^ (-s) else 0) := by
  refine Summable.of_norm_bounded (summable_char_cpow χ hs).norm fun n => ?_
  split_ifs
  · exact le_rfl
  · rw [norm_zero]; exact norm_nonneg _

/-- Termwise expansion of `P(n)²χ(n)n^{−s}` through blueprint Lemma 3.2. -/
lemma Pfun_sq_term_eq (N : ℕ) (R : ℝ) (χ : DirichletCharacter ℂ N) (s : ℂ) {n : ℕ}
    (hn : n ≠ 0) :
    ((Pfun N R n : ℝ) : ℂ) ^ 2 * χ n * (n : ℂ) ^ (-s)
      = ∑ r ∈ Rset N R, ∑ r' ∈ Rset N R, ((r : ℂ) * (r' : ℂ))⁻¹
          * ∑ δ ∈ (r * r').divisors,
              (if δ ∣ n then (hBV r r' δ : ℂ) * (χ n * (n : ℂ) ^ (-s)) else 0) := by
  have hP : ((Pfun N R n : ℝ) : ℂ) ^ 2
      = ∑ r ∈ Rset N R, ∑ r' ∈ Rset N R, ((r : ℂ) * (r' : ℂ))⁻¹
          * ∑ δ ∈ n.divisors, (hBV r r' δ : ℂ) := by
    rw [sq, Pfun, Complex.ofReal_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun r' hr' => ?_
    have hsr : Squarefree r := (mem_Rset.mp hr).2.1
    have hsr' : Squarefree r' := (mem_Rset.mp hr').2.1
    rw [← Complex.ofReal_mul]
    have : psi r n / r * (psi r' n / r') = (psi r n * psi r' n) / (r * r') := by
      rw [div_mul_div_comm]
    rw [this, psi_mul_psi_eq_sum_hBV hsr hsr' hn, Complex.ofReal_div, Complex.ofReal_sum,
      div_eq_inv_mul, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_natCast]
  rw [hP, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r' hr' => ?_
  have hr0 : r ≠ 0 := (mem_Rset.mp hr).2.1.ne_zero
  have hr0' : r' ≠ 0 := (mem_Rset.mp hr').2.1.ne_zero
  rw [mul_assoc, mul_assoc, Finset.sum_mul,
    sum_divisors_hBV_eq hn (mul_ne_zero hr0 hr0') (fun δ => χ n * (n : ℂ) ^ (-s))]

/-- **The Dirichlet-series identity** (blueprint §6, first display, Mellin-free form):
`∑_n P(n)² χ(n) n^{−s} = M_h(s,χ)·L(s,χ)` for `Re s > 1`. -/
theorem tsum_Pfun_sq_eq_Mh_mul_LFunction (N : ℕ) [NeZero N] (R : ℝ)
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    ∑' n : ℕ, ((Pfun N R n : ℝ) : ℂ) ^ 2 * χ n * (n : ℂ) ^ (-s)
      = Mh N R χ s * χ.LFunction s := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hs; norm_num at hs
  -- termwise expansion, valid for all `n` (both sides vanish at `n = 0`)
  have hterm : ∀ n : ℕ, ((Pfun N R n : ℝ) : ℂ) ^ 2 * χ n * (n : ℂ) ^ (-s)
      = ∑ r ∈ Rset N R, ∑ r' ∈ Rset N R, ((r : ℂ) * (r' : ℂ))⁻¹
          * ∑ δ ∈ (r * r').divisors,
              (hBV r r' δ : ℂ) * (if δ ∣ n then χ n * (n : ℂ) ^ (-s) else 0) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Complex.zero_cpow (neg_ne_zero.mpr hs0)]
    · rw [Pfun_sq_term_eq N R χ s hn]
      refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun δ _ => ?_
      split_ifs <;> simp
  simp_rw [hterm]
  have hsumδ : ∀ (r r' : ℕ), ∀ δ ∈ (r * r').divisors,
      Summable fun n : ℕ => (hBV r r' δ : ℂ) * (if δ ∣ n then χ n * (n : ℂ) ^ (-s) else 0) :=
    fun r r' δ _ => (summable_ite_dvd χ hs δ).mul_left _
  rw [Summable.tsum_finsetSum fun r _ => summable_sum fun r' _ =>
    (summable_sum (hsumδ r r')).mul_left _, Mh, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Summable.tsum_finsetSum fun r' _ => (summable_sum (hsumδ r r')).mul_left _,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun r' _ => ?_
  rw [tsum_mul_left, Summable.tsum_finsetSum (hsumδ r r'), mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun δ hδ => ?_
  have hδ0 : δ ≠ 0 := (Nat.pos_of_mem_divisors hδ).ne'
  rw [tsum_mul_left, tsum_multiples_char_cpow χ s hδ0, LFunction_eq_tsum χ hs]
  ring

/-! ### `M_h(1, χ₀) = Φ_R` by exact orthogonality (blueprint Lemma 3.3(a)) -/

/-- `Φ_R = ∑'_{r ≤ R} φ(r)/r²` (the form of `Detection.sum_totient_div_sq_le_P1`). -/
noncomputable def PhiR (N : ℕ) (R : ℝ) : ℝ :=
  ∑ r ∈ Rset N R, (r.totient : ℝ) / (r : ℝ) ^ 2

lemma PhiR_nonneg (N : ℕ) (R : ℝ) : 0 ≤ PhiR N R :=
  Finset.sum_nonneg fun r _ => by positivity

lemma PhiR_le_P1 (N : ℕ) (R : ℝ) : PhiR N R ≤ P1 N R := sum_totient_div_sq_le_P1 N R

/-- The principal character is `1` on every divisor of `r·r'` when `r, r'` are coprime to
the modulus. -/
lemma principal_apply_of_dvd {N : ℕ} {r r' δ : ℕ} (hr : r.Coprime N) (hr' : r'.Coprime N)
    (hδ : δ ∣ r * r') : (1 : DirichletCharacter ℂ N) δ = 1 := by
  have hcop : δ.Coprime N := Nat.Coprime.coprime_dvd_left hδ (Nat.Coprime.mul_left hr hr')
  exact MulChar.one_apply ((ZMod.isUnit_iff_coprime δ N).mpr hcop)

/-- **Exact orthogonality, summed**: `M_h(1, χ₀) = Φ_R`. -/
theorem Mh_one_principal (N : ℕ) (R : ℝ) :
    Mh N R (1 : DirichletCharacter ℂ N) 1 = ((PhiR N R : ℝ) : ℂ) := by
  classical
  unfold Mh PhiR
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨⟨hr1, -⟩, hsr, hrN⟩ := mem_Rset.mp hr
  have hinner : ∀ r' ∈ Rset N R,
      ∑ δ ∈ (r * r').divisors, (hBV r r' δ : ℂ) * (1 : DirichletCharacter ℂ N) δ
          * (δ : ℂ) ^ (-(1 : ℂ))
        = if r = r' then (r.totient : ℂ) else 0 := by
    intro r' hr'
    obtain ⟨-, hsr', hrN'⟩ := mem_Rset.mp hr'
    have h := sum_hBV_div_eq hsr hsr'
    have hc : ((∑ δ ∈ (r * r').divisors, hBV r r' δ / δ : ℝ) : ℂ)
        = ((if r = r' then (r.totient : ℝ) else 0 : ℝ) : ℂ) := by rw [h]
    rw [Complex.ofReal_sum] at hc
    have hc' : ∑ δ ∈ (r * r').divisors, (hBV r r' δ : ℂ) * (1 : DirichletCharacter ℂ N) δ
        * (δ : ℂ) ^ (-(1 : ℂ)) = ∑ δ ∈ (r * r').divisors, ((hBV r r' δ / δ : ℝ) : ℂ) := by
      refine Finset.sum_congr rfl fun δ hδ => ?_
      rw [principal_apply_of_dvd hrN hrN' (Nat.dvd_of_mem_divisors hδ), mul_one,
        Complex.cpow_neg_one, Complex.ofReal_div, div_eq_mul_inv, Complex.ofReal_natCast]
    rw [hc', hc]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun r' hr' => by rw [hinner r' hr']]
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq (Rset N R) r (fun r' => ((r : ℂ) * (r' : ℂ))⁻¹ * (r.totient : ℂ)),
    if_pos hr]
  push_cast
  have : (r : ℂ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  field_simp

/-! ## §4. Mellin representation of the averaged window `W(n)` -/

/-- Fubini on `[a,b] × ℝ` for a continuous integrand dominated by an integrable function of
the second variable. -/
lemma intervalIntegral_integral_swap {f : ℝ → ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : Continuous (Function.uncurry f)) {g : ℝ → ℝ} (hg : Integrable g)
    (hbound : ∀ η ∈ Set.Icc a b, ∀ u, ‖f η u‖ ≤ g u) :
    ∫ η in a..b, ∫ u, f η u = ∫ u, ∫ η in a..b, f η u := by
  rw [intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le hab]
  refine MeasureTheory.integral_integral_swap ?_
  have hprod : (volume.restrict (Set.Ioc a b)).prod (volume : Measure ℝ)
      = (volume.prod volume).restrict (Set.Ioc a b ×ˢ Set.univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hmeas : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict (Set.Ioc a b)).prod volume) := hf.aestronglyMeasurable
  refine Integrable.mono' (g := fun z : ℝ × ℝ => (1 : ℝ) * g z.2) ?_ hmeas ?_
  · have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Set.Ioc a b)) :=
      integrableOn_const (μ := (volume : Measure ℝ)) (s := Set.Ioc a b) (C := (1 : ℝ))
        measure_Ioc_lt_top.ne
    exact Integrable.mul_prod (μ := volume.restrict (Set.Ioc a b)) (ν := volume) h1 hg
  · rw [hprod, ae_restrict_iff' (measurableSet_Ioc.prod MeasurableSet.univ)]
    refine Filter.Eventually.of_forall fun z hz => ?_
    rw [one_mul]
    exact hbound z.1 (Set.Ioc_subset_Icc_self hz.1) z.2

/-- `((n/e^η : ℝ) : ℂ)^{−w} = n^{−w}·e^{wη}`. -/
lemma ofReal_div_exp_cpow_neg {n : ℕ} (hn : 0 < n) (η : ℝ) (w : ℂ) :
    (((n : ℝ) / Real.exp η : ℝ) : ℂ) ^ (-w) = (n : ℂ) ^ (-w) * Complex.exp (w * (η : ℂ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ofReal_div_cpow hn' (Real.exp_pos η), Complex.ofReal_exp,
    Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp; linarith [Real.pi_pos]) (by simp; linarith [Real.pi_pos]),
    Complex.ofReal_natCast]
  rw [show (η : ℂ) * -w = -(w * (η : ℂ)) from by ring, Complex.exp_neg, div_eq_mul_inv, inv_inv]

lemma continuous_Gamma_line_pos {c : ℝ} (hc : 0 < c) :
    Continuous fun u : ℝ => Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I) :=
  continuous_Gamma_line' hc

/-- **Mellin representation of one averaged window.**  For `n ≥ 1`, `1/100 ≤ c ≤ 3`:
`(1/ℓ)∫_a^{a+ℓ} e^{−n/e^η} dη = (1/2π)∫_u Γ(c+iu) n^{−(c+iu)} avgExp a ℓ (c+iu) du`. -/
theorem avg_window_eq_integral {c : ℝ} (hc1 : 1 / 100 ≤ c) (hc2 : c ≤ 3) {n : ℕ} (hn : 0 < n)
    (a : ℝ) {ell : ℝ} (hell : 0 < ell) :
    ((((1 / ell) * ∫ η in a..(a + ell), Real.exp (-(n : ℝ) / Real.exp η) : ℝ)) : ℂ)
      = ((1 / (2 * π) : ℝ) : ℂ) * ∫ u : ℝ,
          Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
            * (n : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))
            * avgExp a ell ((c : ℂ) + (u : ℂ) * Complex.I) := by
  have hc0 : 0 < c := by linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hπ : (0 : ℝ) < 2 * π := by positivity
  -- pointwise Mellin identity in `η`
  have hpt : ∀ η : ℝ, ((Real.exp (-(n : ℝ) / Real.exp η) : ℝ) : ℂ)
      = ((1 / (2 * π) : ℝ) : ℂ) * ∫ u : ℝ,
          Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
            * (n : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))
            * Complex.exp (((c : ℂ) + (u : ℂ) * Complex.I) * (η : ℂ)) := by
    intro η
    have hy : (0 : ℝ) < (n : ℝ) / Real.exp η := by positivity
    have h := integral_Gamma_cpow_line hc1 hc2 hy
    have hrw : ∀ u : ℝ, (((n : ℝ) / Real.exp η : ℝ) : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))
        * Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
        = Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
            * (n : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))
            * Complex.exp (((c : ℂ) + (u : ℂ) * Complex.I) * (η : ℂ)) := by
      intro u
      rw [ofReal_div_exp_cpow_neg hn]
      ring
    simp only [hrw] at h
    rw [h, ← mul_assoc, ← Complex.ofReal_mul, show (1 / (2 * π)) * (2 * π) = (1 : ℝ) from by
      field_simp, Complex.ofReal_one, one_mul, neg_div]
  -- integrability data for Fubini
  set F : ℝ → ℝ → ℂ := fun η u =>
    Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
      * (n : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))
      * Complex.exp (((c : ℂ) + (u : ℂ) * Complex.I) * (η : ℂ)) with hF
  have hcont : Continuous (Function.uncurry F) := by
    have h1 : Continuous fun z : ℝ × ℝ => Complex.Gamma ((c : ℂ) + (z.2 : ℂ) * Complex.I) :=
      (continuous_Gamma_line_pos hc0).comp continuous_snd
    have h2 : Continuous fun z : ℝ × ℝ => (n : ℂ) ^ (-((c : ℂ) + (z.2 : ℂ) * Complex.I)) := by
      refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
      exact_mod_cast hn.ne'
    have h3 : Continuous fun z : ℝ × ℝ =>
        Complex.exp (((c : ℂ) + (z.2 : ℂ) * Complex.I) * (z.1 : ℂ)) := by fun_prop
    exact (h1.mul h2).mul h3
  set g : ℝ → ℝ := fun u => ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖
    * Real.exp (c * (|a| + ell)) with hg
  have hgint : Integrable g := (integrable_Gamma_line hc1 hc2).norm.mul_const _
  have hbound : ∀ η ∈ Set.Icc a (a + ell), ∀ u, ‖F η u‖ ≤ g u := by
    intro η hη u
    simp only [hF, hg]
    rw [norm_mul, norm_mul, norm_exp_mul_ofReal, Complex.norm_natCast_cpow_of_pos hn]
    have hre : ((c : ℂ) + (u : ℂ) * Complex.I).re = c := by simp
    have hre' : (-((c : ℂ) + (u : ℂ) * Complex.I)).re = -c := by simp
    rw [hre, hre']
    have h1 : (n : ℝ) ^ (-c) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
    have h2 : Real.exp (c * η) ≤ Real.exp (c * (|a| + ell)) := by
      refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hc0.le)
      linarith [hη.2, le_abs_self a]
    have h0 : 0 ≤ ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ := norm_nonneg _
    calc ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * (n : ℝ) ^ (-c) * Real.exp (c * η)
        ≤ ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * 1 * Real.exp (c * (|a| + ell)) := by
          gcongr
      _ = _ := by ring
  -- assemble
  rw [Complex.ofReal_mul, ← intervalIntegral.integral_ofReal]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul]
  have hswap := intervalIntegral_integral_swap (f := F) (by linarith) hcont hgint hbound
  simp only [hF] at hswap
  rw [hswap]
  have hRHS : ∀ u : ℝ, Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
      * (n : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))
      * avgExp a ell ((c : ℂ) + (u : ℂ) * Complex.I)
      = ((1 / ell : ℝ) : ℂ) * ∫ η in a..(a + ell),
          Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
            * (n : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))
            * Complex.exp (((c : ℂ) + (u : ℂ) * Complex.I) * (η : ℂ)) := by
    intro u
    simp only [avgExp]
    rw [intervalIntegral.integral_const_mul]
    ring
  simp_rw [hRHS]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- **Mellin representation of `W(n)`** (blueprint §6, "Mellin representation" and the
combined kernel): for `n ≥ 1` and `1/100 ≤ c ≤ 3`,
`W(n) = (1/2π) ∫_u Γ(c+iu) n^{−(c+iu)} 𝒦(c+iu) du`. -/
theorem Wwin_eq_integral (M0 X : ℝ) {ell : ℝ} (hell : 0 < ell)
    {c : ℝ} (hc1 : 1 / 100 ≤ c) (hc2 : c ≤ 3) {n : ℕ} (hn : 0 < n) :
    ((Wwin M0 X ell n : ℝ) : ℂ)
      = ((1 / (2 * π) : ℝ) : ℂ) * ∫ u : ℝ,
          Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
            * (n : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))
            * Kker M0 X ell ((c : ℂ) + (u : ℂ) * Complex.I) := by
  have hc0 : 0 < c := by linarith
  rw [Wwin, Complex.ofReal_sub, avg_window_eq_integral hc1 hc2 hn (Real.log X) hell,
    avg_window_eq_integral hc1 hc2 hn (Real.log M0) hell, ← mul_sub]
  congr 1
  -- integrability of each piece
  have hint : ∀ a : ℝ, Integrable fun u : ℝ =>
      Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
        * (n : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))
        * avgExp a ell ((c : ℂ) + (u : ℂ) * Complex.I) := by
    intro a
    have hcont : Continuous fun u : ℝ =>
        Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
          * (n : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))
          * avgExp a ell ((c : ℂ) + (u : ℂ) * Complex.I) := by
      refine ((continuous_Gamma_line_pos hc0).mul ?_).mul ?_
      · refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
        exact_mod_cast hn.ne'
      · exact (differentiable_avgExp a ell).continuous.comp (by fun_prop)
    refine Integrable.mono' ((integrable_Gamma_line hc1 hc2).norm.mul_const
      (Real.exp (3 * (|a| + ell)))) hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => ?_)
    rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn]
    have hre' : (-((c : ℂ) + (u : ℂ) * Complex.I)).re = -c := by simp
    rw [hre']
    have h1 : (n : ℝ) ^ (-c) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)
    have h2 : ‖avgExp a ell ((c : ℂ) + (u : ℂ) * Complex.I)‖ ≤ Real.exp (3 * (|a| + ell)) := by
      have hbd : ‖∫ η in a..(a + ell), Complex.exp (((c : ℂ) + (u : ℂ) * Complex.I) * (η : ℂ))‖
          ≤ Real.exp (3 * (|a| + ell)) * |(a + ell) - a| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun η hη => ?_
        rw [Set.uIoc_of_le (by linarith)] at hη
        rw [norm_exp_mul_ofReal]
        have hre : ((c : ℂ) + (u : ℂ) * Complex.I).re = c := by simp
        rw [hre]
        refine Real.exp_le_exp.mpr ?_
        have hη1 : η ≤ |a| + ell := by linarith [hη.2, le_abs_self a]
        have hη2 : -(|a| + ell) ≤ η := by linarith [hη.1, neg_abs_le a]
        nlinarith [mul_le_mul_of_nonneg_left hη1 hc0.le, abs_nonneg a]
      rw [avgExp, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      rw [add_sub_cancel_left, abs_of_pos hell] at hbd
      calc 1 / ell * ‖∫ η in a..(a + ell),
              Complex.exp (((c : ℂ) + (u : ℂ) * Complex.I) * (η : ℂ))‖
          ≤ 1 / ell * (Real.exp (3 * (|a| + ell)) * ell) := by gcongr
        _ = Real.exp (3 * (|a| + ell)) := by field_simp
    have h0 : 0 ≤ ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ := norm_nonneg _
    calc ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * (n : ℝ) ^ (-c)
          * ‖avgExp a ell ((c : ℂ) + (u : ℂ) * Complex.I)‖
        ≤ ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * 1 * Real.exp (3 * (|a| + ell)) := by
          gcongr
      _ = _ := by ring
  rw [← integral_sub (hint _) (hint _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [Kker]
  ring

/-! ## §5. The Gram function `B`, the line integrand, `B_rem`, and the anchor line `Re w = 1` -/

/-- The Gram function `B(𝔰,χ) = ∑_n b_n χ(n) n^{−𝔰}` with the Halász majorant
`b_n = n⁻¹P(n)²W(n)` (`Detector.bMaj`). -/
noncomputable def Bgram (N : ℕ) (R M0 X ell : ℝ) (χ : DirichletCharacter ℂ N) (𝔰 : ℂ) : ℂ :=
  Bgen (bMaj N R M0 X ell) χ 𝔰

/-- The line integrand `Γ(w)·𝒦(w)·M_h(1+𝔰+w,χ)·L(1+𝔰+w,χ)` at `w = c + iu`. -/
noncomputable def gramInt (N : ℕ) [NeZero N] (R M0 X ell : ℝ) (χ : DirichletCharacter ℂ N)
    (𝔰 : ℂ) (c u : ℝ) : ℂ :=
  Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I) * Kker M0 X ell ((c : ℂ) + (u : ℂ) * Complex.I)
    * Mh N R χ (1 + 𝔰 + ((c : ℂ) + (u : ℂ) * Complex.I))
    * χ.LFunction (1 + 𝔰 + ((c : ℂ) + (u : ℂ) * Complex.I))

/-- The remainder `B_rem(𝔰,χ) = (1/2π)∫_{Re w = −1+ε₂} Γ(w)𝒦(w)M_h(1+𝔰+w,χ)L(1+𝔰+w,χ) du`
(blueprint Proposition 6.1, with the finite `δ, r, r'` sums inside the integral as `M_h`). -/
noncomputable def Brem (N : ℕ) [NeZero N] (R M0 X ell : ℝ) (χ : DirichletCharacter ℂ N)
    (𝔰 : ℂ) : ℂ :=
  ((1 / (2 * π) : ℝ) : ℂ) * ∫ u : ℝ, gramInt N R M0 X ell χ 𝔰 (-(99 / 100)) u

/-- The holomorphic form `Gfull(w) = G₁(w)·M_h(1+𝔰+w,χ)·L(1+𝔰+w,χ)` of the integrand. -/
noncomputable def Gfull (N : ℕ) [NeZero N] (R M0 X ell : ℝ) (χ : DirichletCharacter ℂ N)
    (𝔰 : ℂ) (w : ℂ) : ℂ :=
  G1 M0 X ell w * Mh N R χ (1 + 𝔰 + w) * χ.LFunction (1 + 𝔰 + w)

lemma gramInt_eq_Gfull (N : ℕ) [NeZero N] (R M0 X : ℝ) {ell : ℝ} (hell : 0 < ell)
    (χ : DirichletCharacter ℂ N) (𝔰 : ℂ) {c : ℝ} (hc : c ≠ 0) (u : ℝ) :
    gramInt N R M0 X ell χ 𝔰 c u = Gfull N R M0 X ell χ 𝔰 ((c : ℂ) + (u : ℂ) * Complex.I) := by
  have hw : (c : ℂ) + (u : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    exact hc this
  rw [gramInt, Gfull, G1_eq_of_ne _ _ hell hw]

lemma bMaj_zero (N : ℕ) (R M0 X ell : ℝ) : bMaj N R M0 X ell 0 = 0 := by
  simp [bMaj]

/-- The anchor-line term `T_n(u) = Γ(w)𝒦(w)·P(n)²χ(n)n^{−(1+𝔰+w)}`, `w = 1 + iu`. -/
noncomputable def Tanc (N : ℕ) (R M0 X ell : ℝ) (χ : DirichletCharacter ℂ N) (𝔰 : ℂ) (n : ℕ)
    (u : ℝ) : ℂ :=
  Complex.Gamma (1 + (u : ℂ) * Complex.I) * Kker M0 X ell (1 + (u : ℂ) * Complex.I)
    * (((Pfun N R n : ℝ) : ℂ) ^ 2 * χ n * (n : ℂ) ^ (-(1 + 𝔰 + (1 + (u : ℂ) * Complex.I))))

lemma Tanc_zero (N : ℕ) (R M0 X ell : ℝ) (χ : DirichletCharacter ℂ N) {𝔰 : ℂ} (hx : 0 ≤ 𝔰.re)
    (u : ℝ) : Tanc N R M0 X ell χ 𝔰 0 u = 0 := by
  have hne : -(1 + 𝔰 + (1 + (u : ℂ) * Complex.I)) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have h0 : ((0 : ℕ) : ℂ) ^ (-(1 + 𝔰 + (1 + (u : ℂ) * Complex.I))) = 0 := by
    simp only [Nat.cast_zero]
    exact Complex.zero_cpow hne
  rw [Tanc, h0]
  simp

/-- Termwise: `b_n χ(n) n^{−𝔰} = (1/2π)∫_u T_n(u) du`. -/
lemma bMaj_term_eq_integral (N : ℕ) (R M0 X : ℝ) {ell : ℝ} (hell : 0 < ell)
    (χ : DirichletCharacter ℂ N) {𝔰 : ℂ} (hx : 0 ≤ 𝔰.re) (n : ℕ) :
    ((bMaj N R M0 X ell n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-𝔰)
      = ((1 / (2 * π) : ℝ) : ℂ) * ∫ u : ℝ, Tanc N R M0 X ell χ 𝔰 n u := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [bMaj_zero, Tanc_zero N R M0 X ell χ hx]
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hW := Wwin_eq_integral M0 X hell (c := 1) (by norm_num) (by norm_num) hn
  simp only [Complex.ofReal_one] at hW
  rw [bMaj, Complex.ofReal_mul, Complex.ofReal_mul, hW, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_pow]
  have hpow : ∀ u : ℝ, (n : ℂ)⁻¹ * (n : ℂ) ^ (-𝔰) * (n : ℂ) ^ (-(1 + (u : ℂ) * Complex.I))
      = (n : ℂ) ^ (-(1 + 𝔰 + (1 + (u : ℂ) * Complex.I))) := by
    intro u
    rw [show -(1 + 𝔰 + (1 + (u : ℂ) * Complex.I))
        = (-1) + (-𝔰) + (-(1 + (u : ℂ) * Complex.I)) from by ring,
      Complex.cpow_add _ _ hnc, Complex.cpow_add _ _ hnc, Complex.cpow_neg_one]
  have hrw : ∀ u : ℝ, Tanc N R M0 X ell χ 𝔰 n u
      = ((n : ℂ)⁻¹ * ((Pfun N R n : ℝ) : ℂ) ^ 2 * χ n * (n : ℂ) ^ (-𝔰))
        * (Complex.Gamma (1 + (u : ℂ) * Complex.I) * (n : ℂ) ^ (-(1 + (u : ℂ) * Complex.I))
          * Kker M0 X ell (1 + (u : ℂ) * Complex.I)) := by
    intro u
    rw [Tanc, ← hpow u]
    ring
  simp_rw [hrw]
  rw [integral_const_mul]
  ring

lemma norm_Tanc_le (N : ℕ) (R M0 X : ℝ) {ell : ℝ} (hM0 : 0 ≤ Real.log M0)
    (hX : 0 ≤ Real.log X) (hell : 0 < ell) (χ : DirichletCharacter ℂ N) {𝔰 : ℂ} (hx : 0 ≤ 𝔰.re)
    (n : ℕ) (u : ℝ) :
    ‖Tanc N R M0 X ell χ 𝔰 n u‖
      ≤ ((Real.exp (Real.log X + ell) + Real.exp (Real.log M0 + ell)) * (⌊R⌋₊ : ℝ) ^ 2
          * ((n : ℝ) ^ 2)⁻¹) * ‖Complex.Gamma (1 + (u : ℂ) * Complex.I)‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Tanc_zero N R M0 X ell χ hx, norm_zero]; positivity
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Tanc, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_natCast_cpow_of_pos hn]
  have hre : (-(1 + 𝔰 + (1 + (u : ℂ) * Complex.I))).re = -(2 + 𝔰.re) := by simp; ring
  rw [hre]
  have hK : ‖Kker M0 X ell (1 + (u : ℂ) * Complex.I)‖
      ≤ Real.exp (Real.log X + ell) + Real.exp (Real.log M0 + ell) :=
    norm_Kker_le_of_re_le_one hM0 hX hell (by simp)
  have hP : |Pfun N R n| ^ 2 ≤ (⌊R⌋₊ : ℝ) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (abs_Pfun_le N R n) 2
  have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one _
  have hpow : (n : ℝ) ^ (-(2 + 𝔰.re)) ≤ ((n : ℝ) ^ 2)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by linarith)]
    refine Real.rpow_le_rpow_of_exponent_le hn' ?_
    push_cast; linarith
  have h0 : 0 ≤ ‖Complex.Gamma (1 + (u : ℂ) * Complex.I)‖ := norm_nonneg _
  calc ‖Complex.Gamma (1 + (u : ℂ) * Complex.I)‖ * ‖Kker M0 X ell (1 + (u : ℂ) * Complex.I)‖
        * (|Pfun N R n| ^ 2 * ‖χ n‖ * (n : ℝ) ^ (-(2 + 𝔰.re)))
      ≤ ‖Complex.Gamma (1 + (u : ℂ) * Complex.I)‖
        * (Real.exp (Real.log X + ell) + Real.exp (Real.log M0 + ell))
        * ((⌊R⌋₊ : ℝ) ^ 2 * 1 * ((n : ℝ) ^ 2)⁻¹) := by gcongr
    _ = _ := by ring

lemma continuous_Tanc (N : ℕ) (R M0 X ell : ℝ) (χ : DirichletCharacter ℂ N) {𝔰 : ℂ}
    (hx : 0 ≤ 𝔰.re) (n : ℕ) : Continuous fun u : ℝ => Tanc N R M0 X ell χ 𝔰 n u := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Tanc_zero N R M0 X ell χ hx]; exact continuous_const
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hΓ : Continuous fun u : ℝ => Complex.Gamma (1 + (u : ℂ) * Complex.I) := by
    have h1 : Continuous fun u : ℝ => Complex.Gamma (((1 : ℝ) : ℂ) + (u : ℂ) * Complex.I) :=
      continuous_Gamma_line_pos one_pos
    simpa using h1
  have hK : Continuous fun u : ℝ => Kker M0 X ell (1 + (u : ℂ) * Complex.I) :=
    (differentiable_Kker M0 X ell).continuous.comp (by fun_prop)
  have hc : Continuous fun u : ℝ => (n : ℂ) ^ (-(1 + 𝔰 + (1 + (u : ℂ) * Complex.I))) :=
    Continuous.const_cpow (by fun_prop) (Or.inl hnc)
  unfold Tanc
  exact (hΓ.mul hK).mul ((continuous_const.mul continuous_const).mul hc)

lemma integrable_Tanc (N : ℕ) (R M0 X : ℝ) {ell : ℝ} (hM0 : 0 ≤ Real.log M0)
    (hX : 0 ≤ Real.log X) (hell : 0 < ell) (χ : DirichletCharacter ℂ N) {𝔰 : ℂ} (hx : 0 ≤ 𝔰.re)
    (n : ℕ) : Integrable fun u : ℝ => Tanc N R M0 X ell χ 𝔰 n u := by
  have hΓ : Integrable fun u : ℝ => ‖Complex.Gamma (1 + (u : ℂ) * Complex.I)‖ := by
    have h1 : Integrable fun u : ℝ => Complex.Gamma (((1 : ℝ) : ℂ) + (u : ℂ) * Complex.I) :=
      integrable_Gamma_line (by norm_num) (by norm_num)
    simpa using h1.norm
  refine Integrable.mono' (hΓ.const_mul _) (continuous_Tanc N R M0 X ell χ hx n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => norm_Tanc_le N R M0 X hM0 hX hell χ hx n u)

/-- The summed anchor-line integrand is the line integrand `gramInt` at `c = 1`. -/
lemma tsum_Tanc (N : ℕ) [NeZero N] (R M0 X ell : ℝ) (χ : DirichletCharacter ℂ N) {𝔰 : ℂ}
    (hx : 0 ≤ 𝔰.re) (u : ℝ) :
    ∑' n : ℕ, Tanc N R M0 X ell χ 𝔰 n u = gramInt N R M0 X ell χ 𝔰 1 u := by
  unfold Tanc
  rw [tsum_mul_left]
  have hs : 1 < (1 + 𝔰 + (1 + (u : ℂ) * Complex.I)).re := by simp; linarith
  rw [tsum_Pfun_sq_eq_Mh_mul_LFunction N R χ hs, gramInt]
  simp only [Complex.ofReal_one]
  ring

/-- **The anchor-line identity**: `B(𝔰,χ) = (1/2π)∫_{Re w = 1} Γ(w)𝒦(w)M_h(1+𝔰+w,χ)L(1+𝔰+w,χ) du`
(blueprint §6, the Mellin representation of `B` before the contour shift). -/
theorem Bgram_eq_integral_anchor (N : ℕ) [NeZero N] (R M0 X : ℝ) {ell : ℝ}
    (hM0 : 0 ≤ Real.log M0) (hX : 0 ≤ Real.log X) (hell : 0 < ell)
    (χ : DirichletCharacter ℂ N) {𝔰 : ℂ} (hx : 0 ≤ 𝔰.re) :
    Bgram N R M0 X ell χ 𝔰 = ((1 / (2 * π) : ℝ) : ℂ) * ∫ u : ℝ, gramInt N R M0 X ell χ 𝔰 1 u := by
  rw [Bgram, Bgen]
  simp_rw [bMaj_term_eq_integral N R M0 X hell χ hx]
  rw [tsum_mul_left]
  congr 1
  have hΓ : Integrable fun u : ℝ => ‖Complex.Gamma (1 + (u : ℂ) * Complex.I)‖ := by
    have h1 : Integrable fun u : ℝ => Complex.Gamma (((1 : ℝ) : ℂ) + (u : ℂ) * Complex.I) :=
      integrable_Gamma_line (by norm_num) (by norm_num)
    simpa using h1.norm
  set CG : ℝ := ∫ u : ℝ, ‖Complex.Gamma (1 + (u : ℂ) * Complex.I)‖ with hCG
  set KB : ℝ := (Real.exp (Real.log X + ell) + Real.exp (Real.log M0 + ell)) * (⌊R⌋₊ : ℝ) ^ 2
    with hKB
  have hbnd : ∀ n : ℕ, ∫ u : ℝ, ‖Tanc N R M0 X ell χ 𝔰 n u‖ ≤ (KB * ((n : ℝ) ^ 2)⁻¹) * CG := by
    intro n
    calc ∫ u : ℝ, ‖Tanc N R M0 X ell χ 𝔰 n u‖
        ≤ ∫ u : ℝ, (KB * ((n : ℝ) ^ 2)⁻¹) * ‖Complex.Gamma (1 + (u : ℂ) * Complex.I)‖ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
            (hΓ.const_mul _)
            (Filter.Eventually.of_forall fun u => norm_Tanc_le N R M0 X hM0 hX hell χ hx n u)
      _ = (KB * ((n : ℝ) ^ 2)⁻¹) * CG := integral_const_mul _ _
  have hsummable : Summable fun n : ℕ => ∫ u : ℝ, ‖Tanc N R M0 X ell χ 𝔰 n u‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun u => norm_nonneg _) hbnd ?_
    have hb : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := Real.summable_nat_pow_inv.mpr one_lt_two
    exact (hb.mul_left KB).mul_right CG
  rw [integral_tsum_of_summable_integral_norm
    (fun n => integrable_Tanc N R M0 X hM0 hX hell χ hx n) hsummable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun u => tsum_Tanc N R M0 X ell χ hx u)

/-! ## §6. The contour shift `Re w = 1 → Re w = −1+ε₂` and Proposition 6.1 -/

/-- A crude polynomial bound on `L(s,χ)` for `Re s ≥ 1/100` at distance `≥ 97/100` from
`s = 1` (I1 for `Re s ≤ 2`, the trivial bound beyond), used only for integrability and the
horizontal edges, never for size. -/
lemma norm_LFunction_crude {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (h1 : 1 / 100 ≤ s.re) (hs1 : 97 / 100 ≤ ‖s - 1‖) :
    ‖χ.LFunction s‖ ≤ 600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|s.im| + 3)) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have ht0 : 0 ≤ |s.im| := abs_nonneg _
  have hbase : (1 : ℝ) ≤ (N : ℝ) * (|s.im| + 3) := by nlinarith
  have hbase2 : (0 : ℝ) ≤ (N : ℝ) * (|s.im| + 2) := by positivity
  have hB : Real.log ((N : ℝ) * (|s.im| + 3)) ≤ (N : ℝ) * (|s.im| + 3) := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < (N : ℝ) * (|s.im| + 3)); linarith
  have hlog0 : 0 ≤ Real.log ((N : ℝ) * (|s.im| + 3)) := Real.log_nonneg hbase
  have h2ω : (1 : ℝ) ≤ 2 ^ N.primeFactors.card := one_le_pow₀ (by norm_num)
  have hsq : 1 ≤ ((N : ℝ) * (|s.im| + 3)) ^ 2 := one_le_pow₀ hbase
  have hmono : ∀ e : ℝ, e ≤ 1 → ((N : ℝ) * (|s.im| + 2)) ^ e ≤ (N : ℝ) * (|s.im| + 3) := by
    intro e he
    calc ((N : ℝ) * (|s.im| + 2)) ^ e ≤ ((N : ℝ) * (|s.im| + 2)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith) he
      _ = (N : ℝ) * (|s.im| + 2) := Real.rpow_one _
      _ ≤ (N : ℝ) * (|s.im| + 3) := by nlinarith
  rcases le_or_gt s.re 2 with hle | hgt
  · have hs1' : s ≠ 1 := by
      intro h; rw [h, sub_self, norm_zero] at hs1; norm_num at hs1
    have h := norm_LFunction_le_convexity_all χ (Or.inr hs1') (by linarith) hle
    refine h.trans ?_
    have hA := hmono (max ((1 - s.re) / 2) 0) (max_le (by linarith) (by norm_num))
    have hC : 1 / ‖s - 1‖ ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    have hAB : ((N : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re) / 2) 0)
        * Real.log ((N : ℝ) * (|s.im| + 3)) ≤ ((N : ℝ) * (|s.im| + 3)) ^ 2 := by
      rw [sq]; exact mul_le_mul hA hB hlog0 (by linarith)
    calc 200000 * 2 ^ N.primeFactors.card
          * (((N : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re) / 2) 0)
              * Real.log ((N : ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖)
        ≤ 200000 * 2 ^ N.primeFactors.card * (((N : ℝ) * (|s.im| + 3)) ^ 2 + 2) := by
          gcongr
      _ ≤ 600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|s.im| + 3)) ^ 2 := by
          nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 2 ^ N.primeFactors.card) (by linarith : (0:ℝ) ≤ ((N : ℝ) * (|s.im| + 3)) ^ 2 - 1)]
  · have hs99 : 99 / 100 ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1)
      rw [Complex.sub_re, Complex.one_re, abs_of_pos (by linarith)] at this
      linarith
    have h := norm_LFunction_strip_le χ hs99 h1
    refine h.trans ?_
    have hA := hmono (1 / 2) (by norm_num)
    have hAB : ((N : ℝ) * (|s.im| + 2)) ^ (1 / 2 : ℝ) * Real.log ((N : ℝ) * (|s.im| + 3))
        ≤ ((N : ℝ) * (|s.im| + 3)) ^ 2 := by
      rw [sq]; exact mul_le_mul hA hB hlog0 (by linarith)
    gcongr

/-- The strip constant `K = (e^{log X+ℓ} + e^{log M₀+ℓ}) · Hmass · 6·10⁵·2^{ω(N)}·(N(|θ|+3))²`. -/
noncomputable def Kbig (N : ℕ) (R M0 X ell : ℝ) (𝔰 : ℂ) : ℝ :=
  (Real.exp (Real.log X + ell) + Real.exp (Real.log M0 + ell)) * Hmass N R
    * (600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|𝔰.im| + 3)) ^ 2)

lemma Kbig_nonneg (N : ℕ) (R M0 X ell : ℝ) (𝔰 : ℂ) : 0 ≤ Kbig N R M0 X ell 𝔰 := by
  unfold Kbig
  have := Hmass_nonneg N R
  positivity

/-- `Gfull` is holomorphic on `Re w > −1`, off the `L`-pole `1+𝔰+w = 1` when `χ = χ₀`. -/
lemma differentiableAt_Gfull (N : ℕ) [NeZero N] (R M0 X ell : ℝ) (χ : DirichletCharacter ℂ N)
    (𝔰 : ℂ) {w : ℂ} (hw : -1 < w.re) (hL : 1 + 𝔰 + w ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (Gfull N R M0 X ell χ 𝔰) w := by
  have hlin : DifferentiableAt ℂ (fun w : ℂ => 1 + 𝔰 + w) w := by fun_prop
  have hM : DifferentiableAt ℂ (fun w : ℂ => Mh N R χ (1 + 𝔰 + w)) w :=
    (differentiable_Mh N R χ (1 + 𝔰 + w)).comp w hlin
  have hL' : DifferentiableAt ℂ (fun w : ℂ => χ.LFunction (1 + 𝔰 + w)) w :=
    (DirichletCharacter.differentiableAt_LFunction χ (1 + 𝔰 + w) hL).comp w hlin
  exact ((differentiableAt_G1 M0 X ell hw).mul hM).mul hL'

/-- Pointwise bound on the strip `−99/100 ≤ Re w ≤ 1`, `w ≠ 0`, at distance `≥ 97/100` from
the `L`-pole: `‖Gfull(w)‖ ≤ ‖Γ(w)‖·K·(1+|Im w|)²`. -/
lemma norm_Gfull_le (N : ℕ) [NeZero N] (R M0 X : ℝ) {ell : ℝ} (hM0 : 0 ≤ Real.log M0)
    (hX : 0 ≤ Real.log X) (hell : 0 < ell) (χ : DirichletCharacter ℂ N) {𝔰 : ℂ} (hx : 0 ≤ 𝔰.re)
    {w : ℂ} (hw0 : w ≠ 0) (hw1 : -(99 / 100) ≤ w.re) (hw2 : w.re ≤ 1)
    (hdist : 97 / 100 ≤ ‖𝔰 + w‖) :
    ‖Gfull N R M0 X ell χ 𝔰 w‖ ≤ ‖Complex.Gamma w‖ * Kbig N R M0 X ell 𝔰 * (1 + |w.im|) ^ 2 := by
  rw [Gfull, G1_eq_of_ne _ _ hell hw0, norm_mul, norm_mul, norm_mul, Kbig]
  have hK := norm_Kker_le_of_re_le_one hM0 hX hell hw2
  have hsre : (1 + 𝔰 + w).re = 1 + 𝔰.re + w.re := by simp
  have hsim : (1 + 𝔰 + w).im = 𝔰.im + w.im := by simp
  have hM := norm_Mh_le N R χ (s := 1 + 𝔰 + w) (by rw [hsre]; linarith)
  have hL := norm_LFunction_crude χ (s := 1 + 𝔰 + w) (by rw [hsre]; linarith)
    (by rw [show 1 + 𝔰 + w - 1 = 𝔰 + w from by ring]; exact hdist)
  rw [hsim] at hL
  have hθv : |𝔰.im + w.im| + 3 ≤ (|𝔰.im| + 3) * (1 + |w.im|) := by
    have h1 := abs_add_le 𝔰.im w.im
    nlinarith [abs_nonneg 𝔰.im, abs_nonneg w.im]
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hL' : ‖χ.LFunction (1 + 𝔰 + w)‖
      ≤ 600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|𝔰.im| + 3)) ^ 2 * (1 + |w.im|) ^ 2 := by
    refine hL.trans ?_
    rw [mul_assoc (600000 * (2 : ℝ) ^ N.primeFactors.card), ← mul_pow]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ 2) (by positivity)
    calc (N : ℝ) * (|𝔰.im + w.im| + 3) ≤ (N : ℝ) * ((|𝔰.im| + 3) * (1 + |w.im|)) :=
          mul_le_mul_of_nonneg_left hθv hN0
      _ = (N : ℝ) * (|𝔰.im| + 3) * (1 + |w.im|) := by ring
  have hΓ0 : 0 ≤ ‖Complex.Gamma w‖ := norm_nonneg _
  have hHm := Hmass_nonneg N R
  calc ‖Complex.Gamma w‖ * ‖Kker M0 X ell w‖ * ‖Mh N R χ (1 + 𝔰 + w)‖
        * ‖χ.LFunction (1 + 𝔰 + w)‖
      ≤ ‖Complex.Gamma w‖ * (Real.exp (Real.log X + ell) + Real.exp (Real.log M0 + ell))
        * Hmass N R
        * (600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|𝔰.im| + 3)) ^ 2
          * (1 + |w.im|) ^ 2) := by gcongr
    _ = _ := by ring

/-- On a vertical line `Re w = c` in the strip, at distance `≥ 97/100` from the `L`-pole,
`gramInt` is integrable. -/
lemma integrable_gramInt_line (N : ℕ) [NeZero N] (R M0 X : ℝ) {ell : ℝ} (hM0 : 0 ≤ Real.log M0)
    (hX : 0 ≤ Real.log X) (hell : 0 < ell) (χ : DirichletCharacter ℂ N) {𝔰 : ℂ} (hx : 0 ≤ 𝔰.re)
    {c : ℝ} (hc1 : -(99 / 100) ≤ c) (hc2 : c ≤ 1) (hc3 : 1 / 100 ≤ |c|) (hc4 : 1 / 100 ≤ |c + 1|)
    (hdist : ∀ u : ℝ, 97 / 100 ≤ ‖𝔰 + ((c : ℂ) + (u : ℂ) * Complex.I)‖) :
    Integrable fun u : ℝ => gramInt N R M0 X ell χ 𝔰 c u := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc3; norm_num at hc3
  have hw0 : ∀ u : ℝ, (c : ℂ) + (u : ℂ) * Complex.I ≠ 0 := by
    intro u h
    have := congrArg Complex.re h
    simp at this
    exact hc0 this
  have hwre : ∀ u : ℝ, ((c : ℂ) + (u : ℂ) * Complex.I).re = c := by intro u; simp
  have hwim : ∀ u : ℝ, ((c : ℂ) + (u : ℂ) * Complex.I).im = u := by intro u; simp
  have hpole : ∀ u : ℝ, 1 + 𝔰 + ((c : ℂ) + (u : ℂ) * Complex.I) ≠ 1 := by
    intro u h
    have h' : 𝔰 + ((c : ℂ) + (u : ℂ) * Complex.I) = 0 := by linear_combination h
    have := hdist u
    rw [h', norm_zero] at this
    norm_num at this
  have hcont : Continuous fun u : ℝ => gramInt N R M0 X ell χ 𝔰 c u := by
    simp_rw [gramInt_eq_Gfull N R M0 X hell χ 𝔰 hc0]
    refine continuous_iff_continuousAt.mpr fun u => ?_
    have hline : Continuous fun u : ℝ => (c : ℂ) + (u : ℂ) * Complex.I := by fun_prop
    exact ContinuousAt.comp (f := fun u : ℝ => (c : ℂ) + (u : ℂ) * Complex.I)
      (differentiableAt_Gfull N R M0 X ell χ 𝔰 (by rw [hwre]; linarith)
        (Or.inl (hpole u))).continuousAt hline.continuousAt
  refine Integrable.mono' ((GammaStrip.integrable_norm_Gamma_line (by linarith) (by linarith)
    hc3 hc4).mul_const (Kbig N R M0 X ell 𝔰)) hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [gramInt_eq_Gfull N R M0 X hell χ 𝔰 hc0]
  have := norm_Gfull_le N R M0 X hM0 hX hell χ hx (hw0 u) (by rw [hwre]; exact hc1)
    (by rw [hwre]; exact hc2) (hdist u)
  rw [hwim] at this
  linarith

/-- Horizontal-edge bound at height `|v| = T ≥ |θ| + 1`. -/
lemma norm_integral_Gfull_horiz_le (N : ℕ) [NeZero N] (R M0 X : ℝ) {ell : ℝ}
    (hM0 : 0 ≤ Real.log M0) (hX : 0 ≤ Real.log X) (hell : 0 < ell)
    (χ : DirichletCharacter ℂ N) {𝔰 : ℂ} (hx : 0 ≤ 𝔰.re)
    {T : ℝ} (hT : |𝔰.im| + 1 ≤ T) {v : ℝ} (hv : v = T ∨ v = -T) :
    ‖∫ x in (-(99 / 100) : ℝ)..1, Gfull N R M0 X ell χ 𝔰 ((x : ℂ) + (v : ℂ) * Complex.I)‖
      ≤ ((201 * GammaStrip.CGamma * Kbig N R M0 X ell 𝔰) * ((1 + T) ^ 2 * Real.exp (-T)))
        * |(1 : ℝ) - (-(99 / 100))| := by
  have hT1 : 1 ≤ T := by linarith [abs_nonneg 𝔰.im]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx' => ?_
  rw [Set.uIoc_of_le (by norm_num)] at hx'
  have hxre : ((x : ℂ) + (v : ℂ) * Complex.I).re = x := by simp
  have hxim : ((x : ℂ) + (v : ℂ) * Complex.I).im = v := by simp
  have habsv : |v| = T := by
    rcases hv with rfl | rfl
    · exact abs_of_nonneg (by linarith)
    · rw [abs_neg]; exact abs_of_nonneg (by linarith)
  have hw0 : (x : ℂ) + (v : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [hxim] at this
    simp at this
    rw [this, abs_zero] at habsv
    linarith
  have hnorm1 : (1 : ℝ) ≤ ‖(x : ℂ) + (v : ℂ) * Complex.I‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) + (v : ℂ) * Complex.I)
    rw [hxim, habsv] at this
    linarith
  have hnorm2 : (1 : ℝ) ≤ ‖((x : ℂ) + (v : ℂ) * Complex.I) + 1‖ := by
    have := Complex.abs_im_le_norm (((x : ℂ) + (v : ℂ) * Complex.I) + 1)
    simp only [Complex.add_im, Complex.one_im, add_zero, hxim] at this
    rw [habsv] at this
    linarith
  have hdist : 97 / 100 ≤ ‖𝔰 + ((x : ℂ) + (v : ℂ) * Complex.I)‖ := by
    have hle := Complex.abs_im_le_norm (𝔰 + ((x : ℂ) + (v : ℂ) * Complex.I))
    simp only [Complex.add_im, hxim] at hle
    have h := abs_sub_abs_le_abs_sub v (-𝔰.im)
    rw [abs_neg, sub_neg_eq_add, habsv] at h
    have h3 : |𝔰.im + v| = |v + 𝔰.im| := by rw [add_comm]
    linarith
  have hΓ : ‖Complex.Gamma ((x : ℂ) + (v : ℂ) * Complex.I)‖
      ≤ 201 * GammaStrip.CGamma * Real.exp (-T) := by
    have := GammaStrip.norm_Gamma_le_of_dist ((x : ℂ) + (v : ℂ) * Complex.I)
      (by rw [hxre]; linarith [hx'.1]) (by rw [hxre]; linarith [hx'.2])
      (by linarith) (by linarith)
    rwa [hxim, habsv] at this
  have hbd := norm_Gfull_le N R M0 X hM0 hX hell χ hx hw0 (by rw [hxre]; exact hx'.1.le)
    (by rw [hxre]; exact hx'.2) hdist
  rw [hxim, habsv] at hbd
  refine hbd.trans ?_
  have hK := Kbig_nonneg N R M0 X ell 𝔰
  calc ‖Complex.Gamma ((x : ℂ) + (v : ℂ) * Complex.I)‖ * Kbig N R M0 X ell 𝔰 * (1 + T) ^ 2
      ≤ (201 * GammaStrip.CGamma * Real.exp (-T)) * Kbig N R M0 X ell 𝔰 * (1 + T) ^ 2 := by
        gcongr
    _ = _ := by ring

open Filter Topology in
/-- The horizontal edges vanish as `T → ∞`. -/
lemma tendsto_Gfull_horiz (N : ℕ) [NeZero N] (R M0 X : ℝ) {ell : ℝ}
    (hM0 : 0 ≤ Real.log M0) (hX : 0 ≤ Real.log X) (hell : 0 < ell)
    (χ : DirichletCharacter ℂ N) {𝔰 : ℂ} (hx : 0 ≤ 𝔰.re) :
    Tendsto (fun T : ℝ => ∫ x in (-(99 / 100) : ℝ)..1,
        Gfull N R M0 X ell χ 𝔰 ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0)
    ∧ Tendsto (fun T : ℝ => ∫ x in (-(99 / 100) : ℝ)..1,
        Gfull N R M0 X ell χ 𝔰 ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
  set KK : ℝ := 201 * GammaStrip.CGamma * Kbig N R M0 X ell 𝔰 with hKK
  have hlim0 : Tendsto (fun T : ℝ => (KK * ((1 + T) ^ 2 * Real.exp (-T)))
      * |(1 : ℝ) - (-(99 / 100))|) atTop (𝓝 0) := by
    have := (tendsto_one_add_sq_mul_exp_neg.const_mul KK).mul_const |(1 : ℝ) - (-(99 / 100))|
    simpa using this
  constructor
  · refine squeeze_zero_norm' ?_ hlim0
    filter_upwards [eventually_ge_atTop (|𝔰.im| + 1)] with T hT
    exact norm_integral_Gfull_horiz_le N R M0 X hM0 hX hell χ hx hT (Or.inl rfl)
  · refine squeeze_zero_norm' ?_ hlim0
    filter_upwards [eventually_ge_atTop (|𝔰.im| + 1)] with T hT
    exact norm_integral_Gfull_horiz_le N R M0 X hM0 hX hell χ hx hT (Or.inr rfl)

/-- Distance to the `L`-pole on the two vertical lines `Re w = 1` and `Re w = −99/100`. -/
lemma dist_pole_line {𝔰 : ℂ} (hx0 : 0 ≤ 𝔰.re) (hx1 : 𝔰.re ≤ 1 / 50) {c : ℝ}
    (hc : c = 1 ∨ c = -(99 / 100)) (u : ℝ) :
    97 / 100 ≤ ‖𝔰 + ((c : ℂ) + (u : ℂ) * Complex.I)‖ := by
  have h := Complex.abs_re_le_norm (𝔰 + ((c : ℂ) + (u : ℂ) * Complex.I))
  have hre : (𝔰 + ((c : ℂ) + (u : ℂ) * Complex.I)).re = 𝔰.re + c := by simp
  rw [hre] at h
  rcases hc with rfl | rfl
  · rw [abs_of_pos (by linarith)] at h; linarith
  · rw [abs_of_neg (by linarith)] at h; linarith

/-- **The contour shift, `χ ≠ χ₀`**: no pole in the strip. -/
theorem gramInt_line_shift (N : ℕ) [NeZero N] (R M0 X : ℝ) {ell : ℝ} (hM0 : 0 ≤ Real.log M0)
    (hX : 0 ≤ Real.log X) (hell : 0 < ell) {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {𝔰 : ℂ} (hx0 : 0 ≤ 𝔰.re) (hx1 : 𝔰.re ≤ 1 / 50) :
    ∫ u : ℝ, gramInt N R M0 X ell χ 𝔰 (-(99 / 100)) u
      = ∫ u : ℝ, gramInt N R M0 X ell χ 𝔰 1 u := by
  have hab : (-(99 / 100) : ℝ) ≤ 1 := by norm_num
  obtain ⟨htop, hbot⟩ := tendsto_Gfull_horiz N R M0 X hM0 hX hell χ hx0
  have hia := integrable_gramInt_line N R M0 X hM0 hX hell χ hx0 (c := -(99 / 100)) le_rfl hab
    (by rw [abs_of_neg (by norm_num)]; norm_num) (by rw [abs_of_pos (by norm_num)]; norm_num)
    (dist_pole_line hx0 hx1 (Or.inr rfl))
  have hib := integrable_gramInt_line N R M0 X hM0 hX hell χ hx0 (c := 1) hab le_rfl
    (by rw [abs_of_pos (by norm_num)]; norm_num) (by rw [abs_of_pos (by norm_num)]; norm_num)
    (dist_pole_line hx0 hx1 (Or.inl rfl))
  simp_rw [gramInt_eq_Gfull N R M0 X hell χ 𝔰 (by norm_num : (-(99 / 100) : ℝ) ≠ 0)] at hia ⊢
  simp_rw [gramInt_eq_Gfull N R M0 X hell χ 𝔰 (by norm_num : (1 : ℝ) ≠ 0)] at hib ⊢
  have h := shift_lines (f := Gfull N R M0 X ell χ 𝔰) hab ?_ hia hib htop hbot
  · simpa using h
  · intro w h1 _
    exact differentiableAt_Gfull N R M0 X ell χ 𝔰 (by linarith) (Or.inr hχ)

/-- The numerator `H(w) = G₁(w)·M_h(1+𝔰+w,χ₀)·L₁(1+𝔰+w)`, `L₁ = (s−1)L(s,χ₀)` entire. -/
noncomputable def Hfull (N : ℕ) [NeZero N] (R M0 X ell : ℝ) (𝔰 : ℂ) (w : ℂ) : ℂ :=
  G1 M0 X ell w * Mh N R (1 : DirichletCharacter ℂ N) (1 + 𝔰 + w)
    * DirichletCharacter.LFunctionTrivChar₁ N (1 + 𝔰 + w)

lemma differentiableAt_Hfull (N : ℕ) [NeZero N] (R M0 X ell : ℝ) (𝔰 : ℂ) {w : ℂ}
    (hw : -1 < w.re) : DifferentiableAt ℂ (Hfull N R M0 X ell 𝔰) w := by
  have hlin : DifferentiableAt ℂ (fun w : ℂ => 1 + 𝔰 + w) w := by fun_prop
  have hM : DifferentiableAt ℂ (fun w : ℂ => Mh N R (1 : DirichletCharacter ℂ N) (1 + 𝔰 + w)) w :=
    (differentiable_Mh N R _ (1 + 𝔰 + w)).comp w hlin
  have hL : DifferentiableAt ℂ (fun w : ℂ => DirichletCharacter.LFunctionTrivChar₁ N (1 + 𝔰 + w))
      w :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ N (1 + 𝔰 + w)).comp w hlin
  exact ((differentiableAt_G1 M0 X ell hw).mul hM).mul hL

lemma Gfull_eq_Hfull_div (N : ℕ) [NeZero N] (R M0 X ell : ℝ) (𝔰 : ℂ) {w : ℂ} (hw : w ≠ -𝔰) :
    Gfull N R M0 X ell (1 : DirichletCharacter ℂ N) 𝔰 w
      = Hfull N R M0 X ell 𝔰 w / (w - (-𝔰)) := by
  have hne : 1 + 𝔰 + w ≠ 1 := by
    intro h; apply hw; linear_combination h
  rw [Gfull, Hfull, LFunctionTrivChar₁_of_ne N hne, show 1 + 𝔰 + w - 1 = w - (-𝔰) from by ring]
  have : w - (-𝔰) ≠ 0 := sub_ne_zero.mpr hw
  field_simp

/-- `H(−𝔰) = G₁(−𝔰)·Φ_R·φ(N)/N` (exact orthogonality and `L₁(1) = φ(N)/N`). -/
lemma Hfull_at_pole (N : ℕ) [NeZero N] (R M0 X ell : ℝ) (𝔰 : ℂ) :
    Hfull N R M0 X ell 𝔰 (-𝔰)
      = G1 M0 X ell (-𝔰) * ((PhiR N R : ℝ) : ℂ) * ((N.totient : ℂ) / N) := by
  rw [Hfull, show 1 + 𝔰 + -𝔰 = 1 from by ring, Mh_one_principal, LFunctionTrivChar₁_one]

/-- **The rectangle identity for `χ₀`**: over `[−99/100, 1] × [−T, T]`, `T ≥ |θ| + 1`, the
boundary integral of `Gfull` is `2πi·H(−𝔰)`. -/
theorem rectInt_Gfull_principal (N : ℕ) [NeZero N] (R M0 X ell : ℝ) {𝔰 : ℂ} (hx0 : 0 ≤ 𝔰.re)
    (hx1 : 𝔰.re ≤ 1 / 50) {T : ℝ} (hT : |𝔰.im| + 1 ≤ T) :
    rectInt (Gfull N R M0 X ell (1 : DirichletCharacter ℂ N) 𝔰)
        (((-(99 / 100) : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        (((1 : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
      = 2 * π * Complex.I * Hfull N R M0 X ell 𝔰 (-𝔰) := by
  set z : ℂ := ((-(99 / 100) : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I with hz
  set w : ℂ := ((1 : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I with hw
  set p : ℂ := -𝔰 with hp
  have hzre : z.re = -(99 / 100) := by rw [hz]; simp
  have hzim : z.im = -T := by rw [hz]; simp
  have hwre : w.re = 1 := by rw [hw]; simp
  have hwim : w.im = T := by rw [hw]; simp
  have hpre : p.re = -𝔰.re := by rw [hp]; simp
  have hpim : p.im = -𝔰.im := by rw [hp]; simp
  have h1 : z.re < p.re := by rw [hzre, hpre]; linarith
  have h2 : p.re < w.re := by rw [hpre, hwre]; linarith
  have h3 : z.im < p.im := by rw [hzim, hpim]; linarith [le_abs_self 𝔰.im]
  have h4 : p.im < w.im := by rw [hpim, hwim]; linarith [neg_le_abs 𝔰.im]
  have hp0 : p ∉ rectFrame z w := notMem_rectFrame h1 h2 h3 h4
  have key : ∀ s ∈ rectFrame z w, Gfull N R M0 X ell (1 : DirichletCharacter ℂ N) 𝔰 s
      = Hfull N R M0 X ell 𝔰 s / (s - p) := by
    intro s hs
    have hsp : s ≠ p := fun h => hp0 (h ▸ hs)
    exact Gfull_eq_Hfull_div N R M0 X ell 𝔰 hsp
  rw [rectInt_congr key]
  have hdiff : ∀ x ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im,
      DifferentiableAt ℂ (Hfull N R M0 X ell 𝔰) x := by
    intro x hx
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (h1.le.trans h2.le)] at hx
    have hxre : z.re ≤ x.re := hx.1.1
    rw [hzre] at hxre
    exact differentiableAt_Hfull N R M0 X ell 𝔰 (by linarith)
  rw [rectInt_cauchy_on hdiff h1 h2 h3 h4]

open Filter Topology in
/-- **The contour shift, `χ = χ₀`**: the pole of `L(1+𝔰+w,χ₀)` at `w = −𝔰` (strictly inside
the strip, including the case `𝔰 = 0` where `G₁` is regular) contributes `2π·H(−𝔰)`. -/
theorem gramInt_line_shift_principal (N : ℕ) [NeZero N] (R M0 X : ℝ) {ell : ℝ}
    (hM0 : 0 ≤ Real.log M0) (hX : 0 ≤ Real.log X) (hell : 0 < ell)
    {𝔰 : ℂ} (hx0 : 0 ≤ 𝔰.re) (hx1 : 𝔰.re ≤ 1 / 50) :
    ∫ u : ℝ, gramInt N R M0 X ell (1 : DirichletCharacter ℂ N) 𝔰 1 u
      = (∫ u : ℝ, gramInt N R M0 X ell (1 : DirichletCharacter ℂ N) 𝔰 (-(99 / 100)) u)
        + 2 * (π : ℂ) * Hfull N R M0 X ell 𝔰 (-𝔰) := by
  have hab : (-(99 / 100) : ℝ) ≤ 1 := by norm_num
  obtain ⟨htop, hbot⟩ := tendsto_Gfull_horiz N R M0 X hM0 hX hell (1 : DirichletCharacter ℂ N) hx0
  have hia := integrable_gramInt_line N R M0 X hM0 hX hell (1 : DirichletCharacter ℂ N) hx0
    (c := -(99 / 100)) le_rfl hab
    (by rw [abs_of_neg (by norm_num)]; norm_num) (by rw [abs_of_pos (by norm_num)]; norm_num)
    (dist_pole_line hx0 hx1 (Or.inr rfl))
  have hib := integrable_gramInt_line N R M0 X hM0 hX hell (1 : DirichletCharacter ℂ N) hx0
    (c := 1) hab le_rfl
    (by rw [abs_of_pos (by norm_num)]; norm_num) (by rw [abs_of_pos (by norm_num)]; norm_num)
    (dist_pole_line hx0 hx1 (Or.inl rfl))
  simp_rw [gramInt_eq_Gfull N R M0 X hell (1 : DirichletCharacter ℂ N) 𝔰
    (by norm_num : (-(99 / 100) : ℝ) ≠ 0)] at hia ⊢
  simp_rw [gramInt_eq_Gfull N R M0 X hell (1 : DirichletCharacter ℂ N) 𝔰
    (by norm_num : (1 : ℝ) ≠ 0)] at hib ⊢
  set c₀ : ℂ := Hfull N R M0 X ell 𝔰 (-𝔰) with hc₀
  have hrect : ∀ T : ℝ, |𝔰.im| + 1 ≤ T →
      rectInt (Gfull N R M0 X ell (1 : DirichletCharacter ℂ N) 𝔰)
        (((-(99 / 100) : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        (((1 : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I) = 2 * π * Complex.I * c₀ :=
    fun T hT => rectInt_Gfull_principal N R M0 X ell hx0 hx1 hT
  have h := shift_lines_residue hrect hia hib htop hbot
  have hI : -Complex.I * (2 * π * Complex.I * c₀) = 2 * (π : ℂ) * c₀ := by
    linear_combination (-(2 * (π : ℂ) * c₀)) * Complex.I_mul_I
  rw [hI] at h
  simp only [Complex.ofReal_one] at h ⊢
  linear_combination h

open scoped Classical in
/-- **Blueprint Proposition 6.1 (structure of `B`).**  For `0 ≤ Re 𝔰 ≤ 1/50` and any
`χ mod N`, with `0 ≤ log M₀ ≤ log X`, `ℓ > 0`:
`B(𝔰,χ) = [χ = χ₀]·(φ(N)/N)·Φ_R·G₁(−𝔰) + B_rem(𝔰,χ)`.
The case `𝔰 = 0` is included: the residue at `w = 0` is `(φ(N)/N)Φ_R·G₁(0)` with
`G₁(0) = 𝒦'(0)` (`G1_zero`). -/
theorem Bgram_eq_main_add_rem (N : ℕ) [NeZero N] (R M0 X : ℝ) {ell : ℝ}
    (hM0 : 0 ≤ Real.log M0) (hX : 0 ≤ Real.log X) (hell : 0 < ell)
    (χ : DirichletCharacter ℂ N) {𝔰 : ℂ} (hx0 : 0 ≤ 𝔰.re) (hx1 : 𝔰.re ≤ 1 / 50) :
    Bgram N R M0 X ell χ 𝔰
      = (if χ = 1 then ((N.totient : ℂ) / N) * ((PhiR N R : ℝ) : ℂ) * G1 M0 X ell (-𝔰) else 0)
        + Brem N R M0 X ell χ 𝔰 := by
  rw [Bgram_eq_integral_anchor N R M0 X hM0 hX hell χ hx0, Brem]
  have hπ : ((1 / (2 * π) : ℝ) : ℂ) * (2 * (π : ℂ)) = 1 := by
    rw [show (2 * (π : ℂ)) = ((2 * π : ℝ) : ℂ) from by push_cast; ring, ← Complex.ofReal_mul]
    have : (1 / (2 * π)) * (2 * π) = (1 : ℝ) := by field_simp
    rw [this, Complex.ofReal_one]
  split_ifs with hχ
  · subst hχ
    rw [gramInt_line_shift_principal N R M0 X hM0 hX hell hx0 hx1, mul_add, Hfull_at_pole]
    linear_combination (G1 M0 X ell (-𝔰) * ((PhiR N R : ℝ) : ℂ) * ((N.totient : ℂ) / N)) * hπ
  · rw [gramInt_line_shift N R M0 X hM0 hX hell hχ hx0 hx1, zero_add]

/-! ## §7. Lemma 6.2 at the frozen parameters -/

lemma log_M0par {D : ℝ} (hD : 0 < D) : Real.log (M0par D) = 3 / 5 * Real.log D := by
  rw [M0par, Real.log_rpow hD]

lemma log_Xpar {D : ℝ} (hD : 0 < D) : Real.log (Xpar D) = 6 / 5 * Real.log D := by
  rw [Xpar, Real.log_rpow hD]

lemma log_Rpar {D : ℝ} (hD : 0 < D) : Real.log (Rpar D) = 1 / 100 * Real.log D := by
  rw [Rpar, Real.log_rpow hD]

lemma ellpar_pos {D : ℝ} (hD : 1 < D) : 0 < ellpar D := by
  rw [ellpar]; have := Real.log_pos hD; positivity

/-- **Blueprint Lemma 6.2 (kernel bounds)**, frozen parameters.  For `𝔰 = x + iθ` with
`0 ≤ x ≤ 1/50` and `𝓛 = log D ≥ 1`:
`‖G₁(−𝔰)‖ ≤ C₇e^{−|θ|/2}𝓛`, `|θ|·‖G₁(−𝔰)‖ ≤ C₇e^{−|θ|/2}`, `θ²ℓ·‖G₁(−𝔰)‖ ≤ 4C₇e^{−|θ|/2}`,
i.e. `‖G₁(−𝔰)‖ ≤ C₇ e^{−|θ|/2} min(𝓛, 1/|θ|, 4/(θ²ℓ))` in product form. -/
theorem G1_bounds_frozen {D : ℝ} (hD : 1 < D) (hL : 1 ≤ Real.log D) {𝔰 : ℂ} (hx0 : 0 ≤ 𝔰.re)
    (hx1 : 𝔰.re ≤ 1 / 50) :
    ‖G1 (M0par D) (Xpar D) (ellpar D) (-𝔰)‖ ≤ C7 * Real.exp (-|𝔰.im| / 2) * Real.log D
    ∧ |𝔰.im| * ‖G1 (M0par D) (Xpar D) (ellpar D) (-𝔰)‖ ≤ C7 * Real.exp (-|𝔰.im| / 2)
    ∧ 𝔰.im ^ 2 * ellpar D * ‖G1 (M0par D) (Xpar D) (ellpar D) (-𝔰)‖
        ≤ 4 * C7 * Real.exp (-|𝔰.im| / 2) := by
  have hD0 : 0 < D := by linarith
  have hM0 : 0 ≤ Real.log (M0par D) := by rw [log_M0par hD0]; linarith
  have hMX : Real.log (M0par D) ≤ Real.log (Xpar D) := by
    rw [log_M0par hD0, log_Xpar hD0]; linarith
  have hsum : Real.log (Xpar D) + Real.log (M0par D) + 2 * ellpar D ≤ 5 / 2 * Real.log D := by
    rw [log_M0par hD0, log_Xpar hD0, ellpar]; linarith
  have h := G1_bounds hM0 hMX (ellpar_pos hD) hL hsum (z := -𝔰)
    (by rw [Complex.neg_re]; linarith) (by rw [Complex.neg_re]; linarith)
  simpa only [Complex.neg_im, abs_neg, neg_sq] using h

/-- The `min` form of Lemma 6.2 for `θ ≠ 0`. -/
theorem norm_G1_le_min {D : ℝ} (hD : 1 < D) (hL : 1 ≤ Real.log D) {𝔰 : ℂ} (hx0 : 0 ≤ 𝔰.re)
    (hx1 : 𝔰.re ≤ 1 / 50) (hθ : 𝔰.im ≠ 0) :
    ‖G1 (M0par D) (Xpar D) (ellpar D) (-𝔰)‖
      ≤ C7 * Real.exp (-|𝔰.im| / 2)
        * min (Real.log D) (min (1 / |𝔰.im|) (4 / (𝔰.im ^ 2 * ellpar D))) := by
  obtain ⟨h1, h2, h3⟩ := G1_bounds_frozen hD hL hx0 hx1
  have hθ0 : 0 < |𝔰.im| := abs_pos.mpr hθ
  have hθ2 : 0 < 𝔰.im ^ 2 * ellpar D := by
    have := ellpar_pos hD; positivity
  have hE : 0 < C7 * Real.exp (-|𝔰.im| / 2) := by have := C7_pos; positivity
  rw [mul_min_of_nonneg _ _ hE.le, mul_min_of_nonneg _ _ hE.le]
  refine le_min h1 (le_min ?_ ?_)
  · rw [mul_one_div, le_div_iff₀ hθ0]; linarith
  · rw [mul_div_assoc', le_div_iff₀ hθ2]; linarith

/-! ## §8. Lemma 6.3: the remainder is power-small -/

/-- I1 on the shifted line `Re s ∈ [1/100, 3/100]` (blueprint Lemma 6.3, `u`-weight
bookkeeping as in Lemma 4.2): for `s` with `Im s = θ + u` and `N(|θ|+2) ≤ 2D`,
`‖L(s,χ)‖ ≤ 1.2·10⁶·C_τ·D^{397/800}·𝓛·(1+|u|)²`. -/
lemma norm_LFunction_left_line_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {D : ℝ} (hD1 : 1 < D) (hLD : 2 ≤ Real.log D) {θ : ℝ}
    (hθ : (N : ℝ) * (|θ| + 2) ≤ 2 * D) {s : ℂ} (hs1 : 1 / 100 ≤ s.re) (hs2 : s.re ≤ 3 / 100)
    {u : ℝ} (hsim : s.im = θ + u) :
    ‖χ.LFunction s‖ ≤ 1200000 * Ctau * D ^ (397 / 800 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hu0 : (0 : ℝ) ≤ |u| := abs_nonneg u
  have hu1 : (1 : ℝ) ≤ 1 + |u| := by linarith
  have hθ0 : (0 : ℝ) ≤ |θ| := abs_nonneg θ
  have hs1' : s ≠ 1 := by
    intro h; rw [h] at hs2; norm_num at hs2
  have hconv := norm_LFunction_le_convexity_all χ (Or.inr hs1') (by linarith) (by linarith)
  refine hconv.trans ?_
  have habs : |s.im| ≤ |θ| + |u| := by rw [hsim]; exact abs_add_le _ _
  -- the pole term
  have hpole : 1 / ‖s - 1‖ ≤ 2 := by
    have h1 : (97 / 100 : ℝ) ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1)
      rw [Complex.sub_re, Complex.one_re, abs_of_neg (by linarith)] at this
      linarith
    rw [div_le_iff₀ (by linarith)]
    linarith
  -- the base
  have hbase : (N : ℝ) * (|s.im| + 2) ≤ 2 * D * (1 + |u|) := by
    calc (N : ℝ) * (|s.im| + 2) ≤ (N : ℝ) * ((|θ| + 2) * (1 + |u|)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by linarith)
          nlinarith
      _ = ((N : ℝ) * (|θ| + 2)) * (1 + |u|) := by ring
      _ ≤ 2 * D * (1 + |u|) := by nlinarith
  have hbase0 : (0 : ℝ) ≤ (N : ℝ) * (|s.im| + 2) := by positivity
  have hbase1 : (1 : ℝ) ≤ (N : ℝ) * (|s.im| + 2) := by nlinarith [abs_nonneg s.im]
  have hmax : max ((1 - s.re) / 2) 0 ≤ 99 / 200 := max_le (by linarith) (by norm_num)
  have hpow : ((N : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re) / 2) 0)
      ≤ 2 * D ^ (99 / 200 : ℝ) * (1 + |u|) := by
    calc ((N : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re) / 2) 0)
        ≤ ((N : ℝ) * (|s.im| + 2)) ^ (99 / 200 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hbase1 hmax
      _ ≤ (2 * D * (1 + |u|)) ^ (99 / 200 : ℝ) := Real.rpow_le_rpow hbase0 hbase (by norm_num)
      _ = (2 : ℝ) ^ (99 / 200 : ℝ) * D ^ (99 / 200 : ℝ) * (1 + |u|) ^ (99 / 200 : ℝ) := by
          rw [Real.mul_rpow (by positivity) (by linarith), Real.mul_rpow (by norm_num) hD0.le]
      _ ≤ 2 * D ^ (99 / 200 : ℝ) * (1 + |u|) := by
          have h2 : (2 : ℝ) ^ (99 / 200 : ℝ) ≤ 2 := by
            calc (2 : ℝ) ^ (99 / 200 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
          have h3 : (1 + |u|) ^ (99 / 200 : ℝ) ≤ 1 + |u| := by
            calc (1 + |u|) ^ (99 / 200 : ℝ) ≤ (1 + |u|) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
              _ = 1 + |u| := Real.rpow_one _
          have hDn : (0 : ℝ) ≤ D ^ (99 / 200 : ℝ) := Real.rpow_nonneg hD0.le _
          exact mul_le_mul (mul_le_mul h2 le_rfl hDn (by norm_num)) h3 (by positivity)
            (by positivity)
  -- the log
  have hND : (N : ℝ) ≤ D := by nlinarith
  have hlogbase : (N : ℝ) * (|s.im| + 3) ≤ 3 * D * (1 + |u|) := by
    have h1 : (N : ℝ) * (|s.im| + 3) = (N : ℝ) * (|s.im| + 2) + (N : ℝ) := by ring
    have h2 : (N : ℝ) ≤ D * (1 + |u|) := by nlinarith
    rw [h1]; linarith
  have hlog : Real.log ((N : ℝ) * (|s.im| + 3)) ≤ 2 * Real.log D * (1 + |u|) := by
    have hpos : (0 : ℝ) < (N : ℝ) * (|s.im| + 3) := by positivity
    have h1 : Real.log ((N : ℝ) * (|s.im| + 3)) ≤ Real.log (3 * D * (1 + |u|)) :=
      Real.log_le_log hpos hlogbase
    have h2 : Real.log (3 * D * (1 + |u|))
        = Real.log 3 + Real.log D + Real.log (1 + |u|) := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity)]
    have h3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (x := (3 : ℝ)) (by norm_num); linarith
    have h4 : Real.log (1 + |u|) ≤ |u| := by
      have := Real.log_le_sub_one_of_pos (x := 1 + |u|) (by linarith); linarith
    nlinarith
  have hL0 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|s.im| + 3)) := Real.log_nonneg (by nlinarith)
  have hDn : (0 : ℝ) ≤ D ^ (99 / 200 : ℝ) := Real.rpow_nonneg hD0.le _
  have hD1' : (1 : ℝ) ≤ D ^ (99 / 200 : ℝ) := by
    calc (1 : ℝ) = D ^ (0 : ℝ) := (Real.rpow_zero D).symm
      _ ≤ D ^ (99 / 200 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by norm_num)
  have hsq1 : (1 : ℝ) ≤ (1 + |u|) ^ 2 := one_le_pow₀ hu1
  have hmain : ((N : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re) / 2) 0)
      * Real.log ((N : ℝ) * (|s.im| + 3))
      ≤ 4 * D ^ (99 / 200 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by
    calc ((N : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re) / 2) 0)
          * Real.log ((N : ℝ) * (|s.im| + 3))
        ≤ (2 * D ^ (99 / 200 : ℝ) * (1 + |u|)) * (2 * Real.log D * (1 + |u|)) :=
          mul_le_mul hpow hlog hL0 (by positivity)
      _ = 4 * D ^ (99 / 200 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by ring
  have hinner : ((N : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re) / 2) 0)
      * Real.log ((N : ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖
      ≤ 6 * D ^ (99 / 200 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by
    have h2 : (2 : ℝ) ≤ 2 * (D ^ (99 / 200 : ℝ) * Real.log D * (1 + |u|) ^ 2) := by
      have : (1 : ℝ) ≤ D ^ (99 / 200 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by
        calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
          _ ≤ D ^ (99 / 200 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by gcongr; linarith
      linarith
    linarith
  have hω : (2 : ℝ) ^ N.primeFactors.card ≤ Ctau * D ^ (1 / 800 : ℝ) :=
    two_pow_card_primeFactors_le_Ctau_mul hND
  have hin0 : (0 : ℝ) ≤ ((N : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re) / 2) 0)
      * Real.log ((N : ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖ := by positivity
  have hexp : D ^ (1 / 800 : ℝ) * D ^ (99 / 200 : ℝ) = D ^ (397 / 800 : ℝ) := by
    rw [← Real.rpow_add hD0]; norm_num
  calc 200000 * (2 : ℝ) ^ N.primeFactors.card
        * (((N : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re) / 2) 0)
            * Real.log ((N : ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖)
      ≤ 200000 * (Ctau * D ^ (1 / 800 : ℝ))
        * (6 * D ^ (99 / 200 : ℝ) * Real.log D * (1 + |u|) ^ 2) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hω (by norm_num)) hinner hin0 ?_
        have := Ctau_pos
        positivity
    _ = 1200000 * Ctau * (D ^ (1 / 800 : ℝ) * D ^ (99 / 200 : ℝ)) * Real.log D
          * (1 + |u|) ^ 2 := by ring
    _ = 1200000 * Ctau * D ^ (397 / 800 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by rw [hexp]

/-- The constant of blueprint Lemma 6.3:
`C₁₁ = 6432·2·1.2·10⁶·C_Γ·C_τ³` (I8(d) moment `6432·C_Γ`, kernel factor `2`, the I1
constant `1.2·10⁶·C_τ` on the shifted line, and `C_τ²` from the coefficient mass). -/
noncomputable def C11 : ℝ := 6432 * 2 * 1200000 * GammaStrip.CGamma * Ctau ^ 3

lemma C11_pos : 0 < C11 := by
  unfold C11; have := Ctau_pos; have := GammaStrip.CGamma_pos; positivity

/-- Pointwise bound for the `B_rem` integrand on `Re w = −99/100`. -/
lemma norm_gramInt_left_le (N : ℕ) [NeZero N] {D : ℝ} (hD1 : 1 < D) (hLD : 2 ≤ Real.log D)
    (χ : DirichletCharacter ℂ N) {𝔰 : ℂ} (hx0 : 0 ≤ 𝔰.re) (hx1 : 𝔰.re ≤ 1 / 50)
    (hθ : (N : ℝ) * (|𝔰.im| + 2) ≤ 2 * D) (u : ℝ) :
    ‖gramInt N (Rpar D) (M0par D) (Xpar D) (ellpar D) χ 𝔰 (-(99 / 100)) u‖
      ≤ (2 * (M0par D) ^ (-(99 / 100) : ℝ) * (Ctau ^ 2 * (Rpar D) ^ (801 / 400 : ℝ))
          * (1200000 * Ctau * D ^ (397 / 800 : ℝ) * Real.log D))
        * (‖Complex.Gamma (((-(99 / 100) : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ * (1 + |u|) ^ 2) := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hM0pos : 0 < M0par D := Real.rpow_pos_of_pos hD0 _
  have hM0 : 0 ≤ Real.log (M0par D) := by rw [log_M0par hD0]; linarith
  have hX : 0 ≤ Real.log (Xpar D) := by rw [log_Xpar hD0]; linarith
  have hMX : Real.log (M0par D) ≤ Real.log (Xpar D) := by
    rw [log_M0par hD0, log_Xpar hD0]; linarith
  have hell := ellpar_pos hD1
  have hR1 : 1 ≤ Rpar D := Real.one_le_rpow hD1.le (by norm_num)
  set w : ℂ := ((-(99 / 100) : ℝ) : ℂ) + (u : ℂ) * Complex.I with hw
  have hwre : w.re = -(99 / 100) := by rw [hw]; simp
  have hwim : w.im = u := by rw [hw]; simp
  have hsre : (1 + 𝔰 + w).re = 𝔰.re + 1 / 100 := by simp [hw]; ring
  have hsim : (1 + 𝔰 + w).im = 𝔰.im + u := by simp [hw]
  rw [gramInt, norm_mul, norm_mul, norm_mul]
  have hK : ‖Kker (M0par D) (Xpar D) (ellpar D) w‖ ≤ 2 * (M0par D) ^ (-(99 / 100) : ℝ) := by
    have h := norm_Kker_le_of_re_nonpos hM0 hX hell (w := w) (by rw [hwre]; norm_num)
    rw [hwre] at h
    have h1 : Real.exp (Real.log (Xpar D) * -(99 / 100))
        ≤ Real.exp (Real.log (M0par D) * -(99 / 100)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : Real.exp (Real.log (M0par D) * -(99 / 100)) = (M0par D) ^ (-(99 / 100) : ℝ) := by
      rw [Real.rpow_def_of_pos hM0pos]
    linarith
  have hM : ‖Mh N (Rpar D) χ (1 + 𝔰 + w)‖ ≤ Ctau ^ 2 * (Rpar D) ^ (801 / 400 : ℝ) :=
    (norm_Mh_le N (Rpar D) χ (by rw [hsre]; linarith)).trans (Hmass_le N hR1)
  have hL : ‖χ.LFunction (1 + 𝔰 + w)‖
      ≤ 1200000 * Ctau * D ^ (397 / 800 : ℝ) * Real.log D * (1 + |u|) ^ 2 :=
    norm_LFunction_left_line_le χ hD1 hLD hθ (by rw [hsre]; linarith) (by rw [hsre]; linarith) hsim
  have hΓ0 : 0 ≤ ‖Complex.Gamma w‖ := norm_nonneg _
  have hC : 0 < Ctau := Ctau_pos
  calc ‖Complex.Gamma w‖ * ‖Kker (M0par D) (Xpar D) (ellpar D) w‖ * ‖Mh N (Rpar D) χ (1 + 𝔰 + w)‖
        * ‖χ.LFunction (1 + 𝔰 + w)‖
      ≤ ‖Complex.Gamma w‖ * (2 * (M0par D) ^ (-(99 / 100) : ℝ))
        * (Ctau ^ 2 * (Rpar D) ^ (801 / 400 : ℝ))
        * (1200000 * Ctau * D ^ (397 / 800 : ℝ) * Real.log D * (1 + |u|) ^ 2) := by gcongr
    _ = _ := by ring

/-- **Blueprint Lemma 6.3 (the remainder is power-small).**  For `0 ≤ Re 𝔰 ≤ 1/50`,
`N(|Im 𝔰|+2) ≤ 2D`, `𝓛 = log D ≥ 2`, and every `χ mod N`:
`‖B_rem(𝔰,χ)‖ ≤ C₁₁·D^{20651/40000}·𝓛·M₀^{−99/100}`.
The `D`-exponent `20651/40000 = 99/200 + 1/800 + 801/40000` is I1's `(1−ε₂)/2`, the divisor
bound `ε/8`, and the log-free coefficient mass `R^{2+1/400}`. -/
theorem norm_Brem_le (N : ℕ) [NeZero N] {D : ℝ} (hD1 : 1 < D) (hLD : 2 ≤ Real.log D)
    (χ : DirichletCharacter ℂ N) {𝔰 : ℂ} (hx0 : 0 ≤ 𝔰.re) (hx1 : 𝔰.re ≤ 1 / 50)
    (hθ : (N : ℝ) * (|𝔰.im| + 2) ≤ 2 * D) :
    ‖Brem N (Rpar D) (M0par D) (Xpar D) (ellpar D) χ 𝔰‖
      ≤ C11 * D ^ (20651 / 40000 : ℝ) * Real.log D * (M0par D) ^ (-(99 / 100) : ℝ) := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hM0pos : 0 < M0par D := Real.rpow_pos_of_pos hD0 _
  have hC : 0 < Ctau := Ctau_pos
  have hCΓ : 0 < GammaStrip.CGamma := GammaStrip.CGamma_pos
  set KL : ℝ := 2 * (M0par D) ^ (-(99 / 100) : ℝ) * (Ctau ^ 2 * (Rpar D) ^ (801 / 400 : ℝ))
    * (1200000 * Ctau * D ^ (397 / 800 : ℝ) * Real.log D) with hKL
  have hKL0 : 0 ≤ KL := by
    rw [hKL]
    have h1 : 0 ≤ Real.log D := by linarith
    have h2 : 0 ≤ (M0par D) ^ (-(99 / 100) : ℝ) := Real.rpow_nonneg hM0pos.le _
    have h3 : 0 ≤ (Rpar D) ^ (801 / 400 : ℝ) := Real.rpow_nonneg (Real.rpow_pos_of_pos hD0 _).le _
    have h4 : 0 ≤ D ^ (397 / 800 : ℝ) := Real.rpow_nonneg hD0.le _
    positivity
  have hΓint := GammaStrip.integrable_norm_Gamma_line (x₀ := -(99 / 100)) (by norm_num)
    (by norm_num) (by rw [abs_of_neg (by norm_num)]; norm_num)
    (by rw [abs_of_pos (by norm_num)]; norm_num)
  have hint : ‖∫ u : ℝ, gramInt N (Rpar D) (M0par D) (Xpar D) (ellpar D) χ 𝔰 (-(99 / 100)) u‖
      ≤ ∫ u : ℝ, KL * (‖Complex.Gamma (((-(99 / 100) : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖
          * (1 + |u|) ^ 2) := by
    refine norm_integral_le_of_norm_le (hΓint.const_mul KL)
      (Filter.Eventually.of_forall fun u => ?_)
    exact norm_gramInt_left_le N hD1 hLD χ hx0 hx1 hθ u
  have hΓmom := GammaStrip.integral_norm_Gamma_line_le (x₀ := -(99 / 100)) (by norm_num)
    (by norm_num) (by rw [abs_of_neg (by norm_num)]; norm_num)
    (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [integral_const_mul] at hint
  have hπ : (1 / (2 * π)) ≤ (1 : ℝ) := by
    rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
  have hπ0 : (0 : ℝ) < 1 / (2 * π) := by positivity
  rw [Brem, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ0]
  have hRD : (Rpar D) ^ (801 / 400 : ℝ) = D ^ (801 / 40000 : ℝ) := by
    rw [Rpar, ← Real.rpow_mul hD0.le]; norm_num
  have hexp : D ^ (801 / 40000 : ℝ) * D ^ (397 / 800 : ℝ) = D ^ (20651 / 40000 : ℝ) := by
    rw [← Real.rpow_add hD0]; norm_num
  have hlog0 : 0 ≤ Real.log D := by linarith
  have hM0n : 0 ≤ (M0par D) ^ (-(99 / 100) : ℝ) := Real.rpow_nonneg hM0pos.le _
  calc 1 / (2 * π) * ‖∫ u : ℝ, gramInt N (Rpar D) (M0par D) (Xpar D) (ellpar D) χ 𝔰 (-(99 / 100)) u‖
      ≤ 1 * (KL * (6432 * GammaStrip.CGamma)) := by
        refine mul_le_mul hπ (hint.trans (mul_le_mul_of_nonneg_left hΓmom hKL0)) (norm_nonneg _)
          zero_le_one
    _ = C11 * (D ^ (801 / 40000 : ℝ) * D ^ (397 / 800 : ℝ)) * Real.log D
          * (M0par D) ^ (-(99 / 100) : ℝ) := by
        rw [hKL, hRD, C11]; ring
    _ = _ := by rw [hexp]

/-- **Lemma 6.3, corollary form**: `‖B_rem(𝔰,χ)‖ ≤ C₁₁·𝓛³·D^{−7/100}`
(the exact exponent is `20651/40000 − 594/1000 = −3109/40000 = −0.077725`). -/
theorem norm_Brem_le' (N : ℕ) [NeZero N] {D : ℝ} (hD1 : 1 < D) (hLD : 2 ≤ Real.log D)
    (χ : DirichletCharacter ℂ N) {𝔰 : ℂ} (hx0 : 0 ≤ 𝔰.re) (hx1 : 𝔰.re ≤ 1 / 50)
    (hθ : (N : ℝ) * (|𝔰.im| + 2) ≤ 2 * D) :
    ‖Brem N (Rpar D) (M0par D) (Xpar D) (ellpar D) χ 𝔰‖
      ≤ C11 * (Real.log D) ^ 3 * D ^ (-(7 / 100) : ℝ) := by
  have hD0 : (0 : ℝ) < D := by linarith
  refine (norm_Brem_le N hD1 hLD χ hx0 hx1 hθ).trans ?_
  have hM0 : (M0par D) ^ (-(99 / 100) : ℝ) = D ^ (-(594 / 1000) : ℝ) := by
    rw [M0par, ← Real.rpow_mul hD0.le]; norm_num
  have hexp : D ^ (20651 / 40000 : ℝ) * D ^ (-(594 / 1000) : ℝ) = D ^ (-(3109 / 40000) : ℝ) := by
    rw [← Real.rpow_add hD0]; norm_num
  have hle : D ^ (-(3109 / 40000) : ℝ) ≤ D ^ (-(7 / 100) : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hD1.le (by norm_num)
  have hlog1 : 1 ≤ Real.log D := by linarith
  have hlog3 : Real.log D ≤ (Real.log D) ^ 3 := by
    calc Real.log D = Real.log D * 1 * 1 := by ring
      _ ≤ Real.log D * Real.log D * Real.log D := by gcongr
      _ = (Real.log D) ^ 3 := by ring
  have hC := C11_pos
  calc C11 * D ^ (20651 / 40000 : ℝ) * Real.log D * (M0par D) ^ (-(99 / 100) : ℝ)
      = C11 * Real.log D * (D ^ (20651 / 40000 : ℝ) * D ^ (-(594 / 1000) : ℝ)) := by
        rw [hM0]; ring
    _ = C11 * Real.log D * D ^ (-(3109 / 40000) : ℝ) := by rw [hexp]
    _ ≤ C11 * (Real.log D) ^ 3 * D ^ (-(7 / 100) : ℝ) := by gcongr

/-! ## §9. Lemma 6.4: row sums of the main term -/

/-- Telescoping tail: `∑_{K < m ≤ M} m⁻² ≤ K⁻¹ − M⁻¹` for `1 ≤ K ≤ M`. -/
lemma sum_Ioc_inv_sq_le {K : ℕ} (hK : 1 ≤ K) : ∀ M : ℕ, K ≤ M →
    ∑ m ∈ Finset.Ioc K M, ((m : ℝ) ^ 2)⁻¹ ≤ (K : ℝ)⁻¹ - (M : ℝ)⁻¹ := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hKM ih =>
    rw [Finset.sum_Ioc_succ_top hKM]
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by omega) hKM)
    have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by linarith
    have h : (((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ ≤ (M : ℝ)⁻¹ - ((M + 1 : ℕ) : ℝ)⁻¹ := by
      push_cast
      have e : (M : ℝ)⁻¹ - ((M : ℝ) + 1)⁻¹ = ((M : ℝ) * ((M : ℝ) + 1))⁻¹ := by
        field_simp
        ring
      rw [e]
      exact inv_anti₀ (by positivity) (by nlinarith)
    linarith

/-- The bin weight `β(m)`: `1` at `m = 0`, `1/m` for `1 ≤ m ≤ 400`, `400/m²` beyond. -/
noncomputable def binWeight (m : ℕ) : ℝ :=
  if m = 0 then 1 else if m ≤ 400 then (m : ℝ)⁻¹ else 400 * ((m : ℝ) ^ 2)⁻¹

lemma binWeight_nonneg (m : ℕ) : 0 ≤ binWeight m := by
  unfold binWeight; split_ifs <;> positivity

/-- `∑_{1 ≤ m ≤ M} β(m) ≤ 2 + log 400` for every `M`. -/
lemma sum_binWeight_le (M : ℕ) : ∑ m ∈ Finset.Icc 1 M, binWeight m ≤ 2 + Real.log 400 := by
  have hsplit : ∀ M' : ℕ, 400 ≤ M' → ∑ m ∈ Finset.Icc 1 M', binWeight m
      = ∑ m ∈ Finset.Icc (1 : ℕ) 400, binWeight m + ∑ m ∈ Finset.Ioc (400 : ℕ) M', binWeight m := by
    intro M' hM'
    have h1 : ∀ K : ℕ, Finset.Icc (1 : ℕ) K = Finset.Ioc 0 K := by
      intro K; ext m; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [h1, h1, Finset.sum_Ioc_consecutive _ (by omega) hM']
  have hhead : ∑ m ∈ Finset.Icc (1 : ℕ) 400, binWeight m ≤ 1 + Real.log 400 := by
    calc ∑ m ∈ Finset.Icc (1 : ℕ) 400, binWeight m
        = ∑ m ∈ Finset.Icc (1 : ℕ) 400, ((m : ℝ))⁻¹ := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [Finset.mem_Icc] at hm
          unfold binWeight
          rw [if_neg (by omega), if_pos hm.2]
      _ ≤ 1 + Real.log ((400 : ℕ) : ℝ) := sum_Icc_inv_le 400
      _ = 1 + Real.log 400 := by norm_num
  have htail : ∀ M' : ℕ, 400 ≤ M' → ∑ m ∈ Finset.Ioc (400 : ℕ) M', binWeight m ≤ 1 := by
    intro M' hM'
    calc ∑ m ∈ Finset.Ioc (400 : ℕ) M', binWeight m
        = ∑ m ∈ Finset.Ioc (400 : ℕ) M', 400 * ((m : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [Finset.mem_Ioc] at hm
          unfold binWeight
          rw [if_neg (by omega), if_neg (by omega)]
      _ = 400 * ∑ m ∈ Finset.Ioc (400 : ℕ) M', ((m : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 400 * (((400 : ℕ) : ℝ)⁻¹ - (M' : ℝ)⁻¹) := by
          gcongr
          exact sum_Ioc_inv_sq_le (by norm_num) M' hM'
      _ ≤ 1 := by
          have : (0 : ℝ) ≤ (M' : ℝ)⁻¹ := by positivity
          push_cast
          linarith
  rcases le_or_gt 400 M with hM | hM
  · rw [hsplit M hM]
    linarith [htail M hM]
  · calc ∑ m ∈ Finset.Icc 1 M, binWeight m ≤ ∑ m ∈ Finset.Icc (1 : ℕ) 400, binWeight m := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun m _ _ => binWeight_nonneg m
          intro m hm
          simp only [Finset.mem_Icc] at hm ⊢
          omega
      _ ≤ 1 + Real.log 400 := hhead
      _ ≤ 2 + Real.log 400 := by linarith

/-- The row constant of blueprint Lemma 6.4, `C₉ = C_M·C₇·(5 + 2 log(4/ε))`, `ε = 1/100`. -/
noncomputable def C9 (CM : ℝ) : ℝ := CM * C7 * (5 + 2 * Real.log 400)

/-- Each `G₁`-value in a row is bounded through its bin: with `m = ⌊|θ|𝓛⌋₊`,
`‖G₁(−𝔰)‖ ≤ C₇·𝓛·β(m)`. -/
lemma norm_G1_le_binWeight {D : ℝ} (hD : 1 < D) (hL : 1 ≤ Real.log D) {𝔰 : ℂ}
    (hx0 : 0 ≤ 𝔰.re) (hx1 : 𝔰.re ≤ 1 / 50) :
    ‖G1 (M0par D) (Xpar D) (ellpar D) (-𝔰)‖
      ≤ C7 * Real.log D * binWeight ⌊|𝔰.im| * Real.log D⌋₊ := by
  obtain ⟨h1, h2, h3⟩ := G1_bounds_frozen hD hL hx0 hx1
  have hexp : Real.exp (-|𝔰.im| / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := abs_nonneg 𝔰.im; linarith)
  have hC7 := C7_pos
  have hG0 : 0 ≤ ‖G1 (M0par D) (Xpar D) (ellpar D) (-𝔰)‖ := norm_nonneg _
  have hL0 : 0 < Real.log D := by linarith
  set m := ⌊|𝔰.im| * Real.log D⌋₊ with hm
  unfold binWeight
  split_ifs with hm0 hm400
  · -- `m = 0`: the `𝓛`-entry
    calc ‖G1 (M0par D) (Xpar D) (ellpar D) (-𝔰)‖ ≤ C7 * Real.exp (-|𝔰.im| / 2) * Real.log D := h1
      _ ≤ C7 * 1 * Real.log D := by gcongr
      _ = C7 * Real.log D * 1 := by ring
  · -- `1 ≤ m ≤ 400`: the `1/|θ|` entry, `|θ| ≥ m/𝓛`
    have hmθ : (m : ℝ) ≤ |𝔰.im| * Real.log D := Nat.floor_le (by positivity)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm0
    have hθpos : 0 < |𝔰.im| := by
      rcases (abs_nonneg 𝔰.im).lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hmθ; linarith
    have hbd : |𝔰.im| * ‖G1 (M0par D) (Xpar D) (ellpar D) (-𝔰)‖ ≤ C7 := by
      calc |𝔰.im| * ‖G1 (M0par D) (Xpar D) (ellpar D) (-𝔰)‖ ≤ C7 * Real.exp (-|𝔰.im| / 2) := h2
        _ ≤ C7 * 1 := by gcongr
        _ = C7 := by ring
    rw [← le_div_iff₀' hθpos] at hbd
    refine hbd.trans ?_
    rw [div_le_iff₀ hθpos]
    have hq : 1 ≤ |𝔰.im| * Real.log D / (m : ℝ) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    calc C7 = C7 * 1 := by ring
      _ ≤ C7 * (|𝔰.im| * Real.log D / (m : ℝ)) := by gcongr
      _ = C7 * Real.log D * (m : ℝ)⁻¹ * |𝔰.im| := by field_simp
  · -- `m > 400`: the `4/(θ²ℓ)` entry
    have hmθ : (m : ℝ) ≤ |𝔰.im| * Real.log D := Nat.floor_le (by positivity)
    have hm1 : (400 : ℝ) < m := by exact_mod_cast (not_le.mp hm400)
    have hθpos : 0 < |𝔰.im| := by
      rcases (abs_nonneg 𝔰.im).lt_or_eq with h | h
      · exact h
      · rw [← h, zero_mul] at hmθ; linarith
    have hθ2 : 0 < 𝔰.im ^ 2 := by rw [← sq_abs]; positivity
    have hbd : 𝔰.im ^ 2 * ellpar D * ‖G1 (M0par D) (Xpar D) (ellpar D) (-𝔰)‖ ≤ 4 * C7 := by
      calc 𝔰.im ^ 2 * ellpar D * ‖G1 (M0par D) (Xpar D) (ellpar D) (-𝔰)‖
          ≤ 4 * C7 * Real.exp (-|𝔰.im| / 2) := h3
        _ ≤ 4 * C7 * 1 := by gcongr
        _ = 4 * C7 := by ring
    have hm2 : (m : ℝ) ^ 2 ≤ 𝔰.im ^ 2 * (Real.log D) ^ 2 := by
      rw [← sq_abs 𝔰.im, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hmθ 2
    have hm0' : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    have key : ‖G1 (M0par D) (Xpar D) (ellpar D) (-𝔰)‖ * (𝔰.im ^ 2 * Real.log D)
        ≤ 400 * C7 := by
      have e : 𝔰.im ^ 2 * ellpar D * ‖G1 (M0par D) (Xpar D) (ellpar D) (-𝔰)‖
          = (‖G1 (M0par D) (Xpar D) (ellpar D) (-𝔰)‖ * (𝔰.im ^ 2 * Real.log D)) / 100 := by
        rw [ellpar]; ring
      rw [e] at hbd
      linarith
    rw [← le_div_iff₀ (by positivity)] at key
    refine key.trans ?_
    rw [div_le_iff₀ (by positivity)]
    have hq : 1 ≤ 𝔰.im ^ 2 * (Real.log D) ^ 2 / (m : ℝ) ^ 2 := by
      rw [le_div_iff₀ hm0']; linarith
    calc 400 * C7 = 400 * C7 * 1 := by ring
      _ ≤ 400 * C7 * (𝔰.im ^ 2 * (Real.log D) ^ 2 / (m : ℝ) ^ 2) := by gcongr
      _ = C7 * Real.log D * (400 * ((m : ℝ) ^ 2)⁻¹) * (𝔰.im ^ 2 * Real.log D) := by
          field_simp

open scoped Classical in
/-- **Blueprint Lemma 6.4 (row sums).**  Let `S` be a finite index set of points
`𝔰_k = x_k + iθ_k` (`0 ≤ x_k ≤ 1/50`) with the spacing property of one parity system:
`|θ_k| ≥ Δ = 1/𝓛` for `k ≠ j`, and at most two `k` per bin `[mΔ, (m+1)Δ)`, `m ≥ 1`.  Then
`∑_{k∈S} ‖(φ(N)/N)·Φ_R·G₁(−𝔰_k)‖ ≤ C₉·Q_R²·ε·𝓛²`, `ε = 1/100`, where `C₉ = C_M C₇(5 + 2 log 400)`
and `C_M` is the Mertens constant carried as the hypothesis
`hMertens : ∏_{p ≤ R}(1−1/p)⁻¹ ≤ C_M·log R` (blueprint §12.3). -/
theorem row_sum_le (N : ℕ) [NeZero N] {D : ℝ} (hD : 1 < D) (hL : 1 ≤ Real.log D)
    {ι : Type*} (S : Finset ι) (j : ι) (𝔰 : ι → ℂ)
    (hre : ∀ k ∈ S, 0 ≤ (𝔰 k).re ∧ (𝔰 k).re ≤ 1 / 50)
    (hdiag : ∀ k ∈ S, k ≠ j → 1 / Real.log D ≤ |(𝔰 k).im|)
    (hbin : ∀ m : ℕ, 1 ≤ m →
      (S.filter fun k => (m : ℝ) / Real.log D ≤ |(𝔰 k).im|
        ∧ |(𝔰 k).im| < ((m : ℝ) + 1) / Real.log D).card ≤ 2)
    {CM : ℝ} (hMertens : MertensProd (Rpar D) ≤ CM * Real.log (Rpar D)) :
    ∑ k ∈ S, ‖((N.totient : ℂ) / N) * ((PhiR N (Rpar D) : ℝ) : ℂ)
        * G1 (M0par D) (Xpar D) (ellpar D) (-(𝔰 k))‖
      ≤ C9 CM * (QR N (Rpar D)) ^ 2 * (1 / 100) * (Real.log D) ^ 2 := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hL0 : 0 < Real.log D := by linarith
  have hC7 := C7_pos
  -- the bin of `k`
  set g : ι → ℕ := fun k => ⌊|(𝔰 k).im| * Real.log D⌋₊ with hg
  -- Step 1: termwise bound through the bin weight
  have hterm : ∀ k ∈ S, ‖G1 (M0par D) (Xpar D) (ellpar D) (-(𝔰 k))‖
      ≤ C7 * Real.log D * binWeight (g k) := fun k hk =>
    norm_G1_le_binWeight hD hL (hre k hk).1 (hre k hk).2
  -- Step 2: the bins
  have hfib : ∀ m : ℕ, (S.filter fun k => g k = m).card ≤ (if m = 0 then 1 else 2) := by
    intro m
    split_ifs with hm0
    · subst hm0
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      have hlt : ∀ k ∈ S, g k = 0 → k = j := by
        intro k hk hk0
        by_contra hkj
        have h1 := hdiag k hk hkj
        have h2 : |(𝔰 k).im| * Real.log D < 1 := by
          have := (Nat.floor_eq_zero.mp hk0)
          exact_mod_cast this
        rw [div_le_iff₀ hL0] at h1
        linarith
      rw [hlt a ha.1 ha.2, hlt b hb.1 hb.2]
    · refine le_trans (le_of_eq ?_) (hbin m (Nat.one_le_iff_ne_zero.mpr hm0))
      congr 1
      ext k
      simp only [Finset.mem_filter, hg]
      constructor
      · rintro ⟨hk, hfl⟩
        rw [Nat.floor_eq_iff (by positivity)] at hfl
        refine ⟨hk, ?_, ?_⟩
        · rw [div_le_iff₀ hL0]; exact hfl.1
        · rw [lt_div_iff₀ hL0]; exact hfl.2
      · rintro ⟨hk, h1, h2⟩
        refine ⟨hk, ?_⟩
        rw [Nat.floor_eq_iff (by positivity)]
        rw [div_le_iff₀ hL0] at h1
        rw [lt_div_iff₀ hL0] at h2
        exact ⟨h1, h2⟩
  -- Step 3: the row sum of bin weights
  have hrow : ∑ k ∈ S, binWeight (g k) ≤ 5 + 2 * Real.log 400 := by
    set t := S.image g with ht
    have hmaps : ∀ k ∈ S, g k ∈ t := fun k hk => Finset.mem_image_of_mem g hk
    rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun k => binWeight (g k))]
    have hin : ∀ m ∈ t, ∑ k ∈ S.filter (fun k => g k = m), binWeight (g k)
        = (S.filter fun k => g k = m).card * binWeight m := by
      intro m _
      rw [Finset.sum_congr rfl (fun k hk => by rw [(Finset.mem_filter.mp hk).2]),
        Finset.sum_const, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hin]
    set M := t.sup id with hM
    have htsub : t ⊆ Finset.range (M + 1) := by
      intro m hm
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Finset.le_sup (f := id) hm
    calc ∑ m ∈ t, ((S.filter fun k => g k = m).card : ℝ) * binWeight m
        ≤ ∑ m ∈ t, (if m = 0 then 1 else 2 : ℝ) * binWeight m := by
          refine Finset.sum_le_sum fun m _ => ?_
          refine mul_le_mul_of_nonneg_right ?_ (binWeight_nonneg m)
          have := hfib m
          split_ifs at this ⊢ <;> exact_mod_cast this
      _ ≤ ∑ m ∈ Finset.range (M + 1), (if m = 0 then 1 else 2 : ℝ) * binWeight m := by
          refine Finset.sum_le_sum_of_subset_of_nonneg htsub fun m _ _ => ?_
          split_ifs <;> linarith [binWeight_nonneg m]
      _ = 1 + 2 * ∑ m ∈ Finset.Icc 1 M, binWeight m := by
          rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.mul_sum]
          have h0 : (if (0 : ℕ) = 0 then (1 : ℝ) else 2) * binWeight 0 = 1 := by
            simp [binWeight]
          have hIco : Finset.Ico 1 (M + 1) = Finset.Icc 1 M := by
            ext m; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
          rw [h0, hIco]
          congr 1
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [Finset.mem_Icc] at hm
          rw [if_neg (by omega)]
      _ ≤ 1 + 2 * (2 + Real.log 400) := by
          have := sum_binWeight_le M; linarith
      _ = 5 + 2 * Real.log 400 := by ring
  -- Step 4: assemble
  have hφ : (N.totient : ℝ) / N ≤ QR N (Rpar D) := totient_div_le_QR N (NeZero.ne N) _
  have hΦ : PhiR N (Rpar D) ≤ QR N (Rpar D) * (CM * (1 / 100 * Real.log D)) := by
    calc PhiR N (Rpar D) ≤ P1 N (Rpar D) := PhiR_le_P1 N _
      _ ≤ QR N (Rpar D) * MertensProd (Rpar D) := P1_le_QR_mul_MertensProd N _
      _ ≤ QR N (Rpar D) * (CM * Real.log (Rpar D)) :=
          mul_le_mul_of_nonneg_left hMertens (QR_pos N _).le
      _ = QR N (Rpar D) * (CM * (1 / 100 * Real.log D)) := by rw [log_Rpar hD0]
  have hQ0 : 0 ≤ QR N (Rpar D) := (QR_pos N _).le
  have hφ0 : 0 ≤ (N.totient : ℝ) / N := by positivity
  have hΦ0 : 0 ≤ PhiR N (Rpar D) := PhiR_nonneg N _
  have hCM : 0 ≤ CM := by
    have hMp : 0 < MertensProd (Rpar D) := by
      unfold MertensProd
      refine Finset.prod_pos fun p hp => ?_
      have hp2 : 2 ≤ p := (Finset.mem_filter.mp hp).2.two_le
      have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp2)
      exact inv_pos.mpr (by linarith)
    have hlogR : 0 < Real.log (Rpar D) := by rw [log_Rpar hD0]; positivity
    by_contra h
    push Not at h
    nlinarith
  have hpre : ((N.totient : ℝ) / N) * PhiR N (Rpar D)
      ≤ (QR N (Rpar D)) ^ 2 * (CM * (1 / 100 * Real.log D)) := by
    calc ((N.totient : ℝ) / N) * PhiR N (Rpar D)
        ≤ QR N (Rpar D) * (QR N (Rpar D) * (CM * (1 / 100 * Real.log D))) :=
          mul_le_mul hφ hΦ hΦ0 hQ0
      _ = _ := by ring
  calc ∑ k ∈ S, ‖((N.totient : ℂ) / N) * ((PhiR N (Rpar D) : ℝ) : ℂ)
        * G1 (M0par D) (Xpar D) (ellpar D) (-(𝔰 k))‖
      = ∑ k ∈ S, ((N.totient : ℝ) / N) * PhiR N (Rpar D)
          * ‖G1 (M0par D) (Xpar D) (ellpar D) (-(𝔰 k))‖ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΦ0,
          show ((N.totient : ℂ) / N) = (((N.totient : ℝ) / N : ℝ) : ℂ) from by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hφ0]
    _ ≤ ∑ k ∈ S, ((N.totient : ℝ) / N) * PhiR N (Rpar D) * (C7 * Real.log D * binWeight (g k)) := by
        refine Finset.sum_le_sum fun k hk => ?_
        exact mul_le_mul_of_nonneg_left (hterm k hk) (by positivity)
    _ = ((N.totient : ℝ) / N) * PhiR N (Rpar D) * (C7 * Real.log D)
          * ∑ k ∈ S, binWeight (g k) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    _ ≤ ((QR N (Rpar D)) ^ 2 * (CM * (1 / 100 * Real.log D))) * (C7 * Real.log D)
          * (5 + 2 * Real.log 400) := by
        have h400 : 0 ≤ 5 + 2 * Real.log 400 := by
          have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 400); linarith
        have hsum0 : 0 ≤ ∑ k ∈ S, binWeight (g k) :=
          Finset.sum_nonneg fun k _ => binWeight_nonneg _
        gcongr
    _ = C9 CM * (QR N (Rpar D)) ^ 2 * (1 / 100) * (Real.log D) ^ 2 := by
        rw [C9]; ring

/-! ## §10. Specializations: the detector coefficients and majorant, and frozen parameters -/

/-- `F(ρ − σ, χ)` with the detector coefficients `c_n = a(n)P(n)e^{−n/X}n^{−σ}` (`n > z₁`) is
the detector `Fdet` of Z6c. -/
lemma Fgen_cDet_eq_Fdet {N : ℕ} (χ : DirichletCharacter ℂ N) {z1 z2 R X σ : ℝ} (hz1 : 0 < z1)
    (ρ : ℂ) :
    Fgen (fun n => ((cDet N z1 z2 R X σ n : ℝ) : ℂ)) χ (ρ - σ) = Fdet χ z1 z2 R X ρ := by
  unfold Fgen Fdet
  refine tsum_congr fun n => ?_
  dsimp only
  unfold cDet
  split_ifs with h
  · have hn0 : (0 : ℝ) < n := lt_trans hz1 h
    have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
    rw [Complex.ofReal_mul, Complex.ofReal_cpow hn0.le, Complex.ofReal_natCast,
      Complex.ofReal_neg]
    have : (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(ρ - σ)) = (n : ℂ) ^ (-ρ) := by
      rw [← Complex.cpow_add _ _ hnc]; congr 1; ring
    rw [← this]
    ring
  · simp only [Complex.ofReal_zero, zero_mul]

/-- Window lower bound on `n > z₁` when `M₀e^ℓ ≤ z₁` and `2z₁ ≤ X`: `W(n) ≥ (1/3)e^{−n/X}`
(blueprint Lemma 8.1, Step 1, in the form needed for the summability of `∑|c_n|²/b_n`). -/
lemma Wwin_ge_third {M0 X ell z1 : ℝ} (hM0 : 0 < M0) (hell : 0 < ell) (hz1 : 0 < z1)
    (hMz : M0 * Real.exp ell ≤ z1) (hzX : 2 * z1 ≤ X) {n : ℕ} (hn : z1 < n) :
    (1 / 3) * Real.exp (-(n : ℝ) / X) ≤ Wwin M0 X ell n := by
  have hX : 0 < X := by linarith
  have hMe : 0 < M0 * Real.exp ell := by positivity
  refine le_trans ?_ (exp_sub_exp_le_Wwin hM0 hX hell n)
  have hn0 : (0 : ℝ) < n := lt_trans hz1 hn
  -- `e^{−n/(M₀e^ℓ)} ≤ e^{−n/z₁} ≤ e^{−1/2} e^{−n/X}`
  have h1 : Real.exp (-(n : ℝ) / (M0 * Real.exp ell)) ≤ Real.exp (-(n : ℝ) / z1) := by
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hn0.le hMe hMz
  have h2 : Real.exp (-(n : ℝ) / z1) ≤ Real.exp (-(1 / 2)) * Real.exp (-(n : ℝ) / X) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    -- `n/z₁ − n/X = n(X − z₁)/(z₁X) ≥ z₁(X − z₁)/(z₁X) = 1 − z₁/X ≥ 1/2`
    have key : (1 / 2 : ℝ) ≤ (n : ℝ) / z1 - (n : ℝ) / X := by
      have e : (n : ℝ) / z1 - (n : ℝ) / X = (n : ℝ) * ((X - z1) / (z1 * X)) := by
        field_simp
      rw [e]
      have h3 : (z1 : ℝ) * ((X - z1) / (z1 * X)) = 1 - z1 / X := by field_simp
      have h4 : z1 / X ≤ 1 / 2 := by rw [div_le_iff₀ hX]; linarith
      have h5 : 0 ≤ (X - z1) / (z1 * X) := by
        apply div_nonneg <;> nlinarith
      calc (1 / 2 : ℝ) ≤ 1 - z1 / X := by linarith
        _ = z1 * ((X - z1) / (z1 * X)) := h3.symm
        _ ≤ (n : ℝ) * ((X - z1) / (z1 * X)) := mul_le_mul_of_nonneg_right hn.le h5
    have e1 : -(n : ℝ) / z1 = -((n : ℝ) / z1) := neg_div _ _
    have e2 : -(n : ℝ) / X = -((n : ℝ) / X) := neg_div _ _
    rw [e1, e2]
    linarith
  have h3 : Real.exp (-(1 / 2 : ℝ)) ≤ 2 / 3 := by
    have := Real.add_one_le_exp (1 / 2 : ℝ)
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have h4 : 0 < Real.exp (-(n : ℝ) / X) := Real.exp_pos _
  calc (1 / 3) * Real.exp (-(n : ℝ) / X)
      = Real.exp (-(n : ℝ) / X) - (2 / 3) * Real.exp (-(n : ℝ) / X) := by ring
    _ ≤ Real.exp (-(n : ℝ) / X) - Real.exp (-(n : ℝ) / (M0 * Real.exp ell)) := by
        have : Real.exp (-(n : ℝ) / (M0 * Real.exp ell)) ≤ (2 / 3) * Real.exp (-(n : ℝ) / X) := by
          calc Real.exp (-(n : ℝ) / (M0 * Real.exp ell)) ≤ Real.exp (-(1 / 2)) * Real.exp (-(n : ℝ) / X) :=
                h1.trans h2
            _ ≤ (2 / 3) * Real.exp (-(n : ℝ) / X) := mul_le_mul_of_nonneg_right h3 h4.le
        linarith

/-- The diagonal quotient `|c_n|²/b_n` is dominated by `3n³e^{−n/X}` (summable). -/
lemma cDet_sq_div_bMaj_le (N : ℕ) {z1 z2 R M0 X ell σ : ℝ} (hz1 : 1 ≤ z1) (hz12 : z1 < z2)
    (hM0 : 0 < M0) (hell : 0 < ell) (hMz : M0 * Real.exp ell ≤ z1) (hzX : 2 * z1 ≤ X)
    (hσ : 0 ≤ σ) (n : ℕ) :
    (cDet N z1 z2 R X σ n) ^ 2 / bMaj N R M0 X ell n
      ≤ 3 * ((n : ℝ) ^ 3 * Real.exp (-(1 / X)) ^ n) := by
  have hz10 : 0 < z1 := by linarith
  have hX : 0 < X := by linarith
  have hexp : Real.exp (-(1 / X)) ^ n = Real.exp (-(n : ℝ) / X) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hexp]
  unfold cDet bMaj
  split_ifs with h
  · have hn0 : (0 : ℝ) < n := lt_trans hz10 h
    have hn1 : (1 : ℝ) ≤ n := by linarith
    have hW := Wwin_ge_third hM0 hell hz10 hMz hzX h
    have hWpos : 0 < Wwin M0 X ell n := lt_of_lt_of_le (by positivity) hW
    rcases eq_or_ne (Pfun N R n) 0 with hP | hP
    · rw [hP]; simp; positivity
    · have hPsq : 0 < (Pfun N R n) ^ 2 := by positivity
      have hb : 0 < (n : ℝ)⁻¹ * (Pfun N R n) ^ 2 * Wwin M0 X ell n := by positivity
      rw [div_le_iff₀ hb]
      have hA : (bvA z1 z2 n) ^ 2 ≤ (n : ℝ) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_bvA_le hz10 hz12 n) 2
      have hpow : ((n : ℝ) ^ (-σ)) ^ 2 ≤ 1 := by
        refine pow_le_one₀ (by positivity) ?_
        exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by linarith)
      have he : 0 < Real.exp (-(n : ℝ) / X) := Real.exp_pos _
      -- `(a P e n^{−σ})² = a² P² e² (n^{−σ})²`, and `(n⁻¹ P² W)·3n³e ≥ P² e² a² (n^{-σ})²` since
      -- `W ≥ e/3`, `a² ≤ n²`, `(n^{−σ})² ≤ 1`
      have hWe : Real.exp (-(n : ℝ) / X) ≤ 3 * Wwin M0 X ell n := by linarith
      calc (bvA z1 z2 n * Pfun N R n * Real.exp (-(n : ℝ) / X) * (n : ℝ) ^ (-σ)) ^ 2
          = (Pfun N R n) ^ 2 * Real.exp (-(n : ℝ) / X)
            * ((bvA z1 z2 n) ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2 * Real.exp (-(n : ℝ) / X)) := by ring
        _ ≤ (Pfun N R n) ^ 2 * Real.exp (-(n : ℝ) / X)
            * ((n : ℝ) ^ 2 * 1 * (3 * Wwin M0 X ell n)) := by gcongr
        _ = 3 * ((n : ℝ) ^ 3 * Real.exp (-(n : ℝ) / X))
            * ((n : ℝ)⁻¹ * (Pfun N R n) ^ 2 * Wwin M0 X ell n) := by
          field_simp
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
    positivity

/-- **Blueprint Lemma 5.1, applied** (Theorem 8.3's use): with the detector coefficients
`c_n = cDet` and the Halász majorant `b_n = bMaj`, points `s_j = ρ_j − σ` (`Re ρ_j ≥ σ ≥ 0`):
`(∑_j ‖F(ρ_j,χ_j)‖)² ≤ Σ_diag · ∑_{j,k} ‖B(s_j + conj s_k, χ_jχ_k⁻¹)‖`,
`Σ_diag = ∑_n c_n²/b_n`.  Hypotheses: `1 ≤ z₁ < z₂`, `M₀e^ℓ ≤ z₁`, `2z₁ ≤ X` (window sandwich). -/
theorem halasz_duality_detector (N : ℕ) [NeZero N] {J : Type*} [Fintype J]
    (ρ : J → ℂ) (χ : J → DirichletCharacter ℂ N) {σ : ℝ} (hσ : 0 ≤ σ)
    (hρ : ∀ j, σ ≤ (ρ j).re) {z1 z2 R M0 X ell : ℝ} (hz1 : 1 ≤ z1) (hz12 : z1 < z2)
    (hM0 : 0 < M0) (hell : 0 < ell) (hMz : M0 * Real.exp ell ≤ z1) (hzX : 2 * z1 ≤ X) :
    (∑ j, ‖Fdet (χ j) z1 z2 R X (ρ j)‖) ^ 2
      ≤ (∑' n, (cDet N z1 z2 R X σ n) ^ 2 / bMaj N R M0 X ell n)
        * ∑ j, ∑ k, ‖Bgram N R M0 X ell (χ j * (χ k)⁻¹) ((ρ j - σ) + conj (ρ k - σ))‖ := by
  have hz10 : 0 < z1 := by linarith
  have hX : 0 < X := by linarith
  have hlt : M0 * Real.exp ell < X := by linarith
  set c : ℕ → ℂ := fun n => ((cDet N z1 z2 R X σ n : ℝ) : ℂ) with hc
  set b : ℕ → ℝ := bMaj N R M0 X ell with hb
  have hcn : ∀ n, ‖c n‖ ^ 2 = (cDet N z1 z2 R X σ n) ^ 2 := by
    intro n; rw [hc]; simp only; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hb0 : b 0 = 0 := bMaj_zero N R M0 X ell
  have hbnn : ∀ n, 0 ≤ b n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hb0]
    · simp only [hb, bMaj]
      have := Wwin_pos hM0 hell hlt hn
      positivity
  have hbc : ∀ n, c n ≠ 0 → 0 < b n := by
    intro n hcn0
    simp only [hc, cDet, ne_eq, Complex.ofReal_eq_zero] at hcn0
    split_ifs at hcn0 with h
    · have hn : 1 ≤ n := by
        have : (0 : ℝ) < n := lt_trans hz10 h
        exact_mod_cast this
      have hP : Pfun N R n ≠ 0 := by
        intro hP; apply hcn0; rw [hP]; ring
      simp only [hb, bMaj]
      have := Wwin_pos hM0 hell hlt hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hPsq : 0 < (Pfun N R n) ^ 2 := by positivity
      positivity
    · exact absurd rfl hcn0
  have hsum : Summable fun n => ‖c n‖ ^ 2 / b n := by
    simp_rw [hcn]
    refine Summable.of_nonneg_of_le (fun n => div_nonneg (sq_nonneg _) (hbnn n))
      (fun n => cDet_sq_div_bMaj_le N hz1 hz12 hM0 hell hMz hzX hσ n) ?_
    refine Summable.mul_left 3 ?_
    have hq : ‖Real.exp (-(1 / X))‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
      have : (0 : ℝ) < 1 / X := by positivity
      linarith
    exact summable_pow_mul_geometric_of_norm_lt_one 3 hq
  have hbs : Summable b := by
    refine Summable.of_nonneg_of_le hbnn (fun n => ?_)
      ((summable_pow_mul_geometric_of_norm_lt_one 1 (by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
        have : (0 : ℝ) < 1 / (X * Real.exp ell) := by positivity
        linarith : ‖Real.exp (-(1 / (X * Real.exp ell)))‖ < 1)).mul_left ((⌊R⌋₊ : ℝ) ^ 2))
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hb0]; positivity
    · simp only [hb, bMaj]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      -- `W(n) ≤ e^{−n/(Xe^ℓ)}` (upper window) and `P(n)² ≤ ⌊R⌋₊²`
      have hW : Wwin M0 X ell n ≤ Real.exp (-(1 / (X * Real.exp ell))) ^ n := by
        rw [← Real.exp_nat_mul]
        have hint : ∀ a b : ℝ, IntervalIntegrable (fun η : ℝ => Real.exp (-(n : ℝ) / Real.exp η))
            volume a b := fun a b => (continuous_windowIntegrand n).intervalIntegrable a b
        have h2 : 0 ≤ ∫ ξ in Real.log M0..(Real.log M0 + ell), Real.exp (-(n : ℝ) / Real.exp ξ) :=
          intervalIntegral.integral_nonneg (by linarith) fun ξ _ => (Real.exp_pos _).le
        have h1 : ∫ η in Real.log X..(Real.log X + ell), Real.exp (-(n : ℝ) / Real.exp η)
            ≤ ell * Real.exp (-(n : ℝ) / (X * Real.exp ell)) := by
          have hmono : ∀ η ∈ Set.Icc (Real.log X) (Real.log X + ell),
              Real.exp (-(n : ℝ) / Real.exp η) ≤ Real.exp (-(n : ℝ) / (X * Real.exp ell)) := by
            intro η hη
            have hXη : Real.exp η ≤ X * Real.exp ell := by
              calc Real.exp η ≤ Real.exp (Real.log X + ell) := Real.exp_le_exp.mpr hη.2
                _ = X * Real.exp ell := by rw [Real.exp_add, Real.exp_log hX]
            refine Real.exp_le_exp.mpr ?_
            rw [neg_div, neg_div, neg_le_neg_iff]
            exact div_le_div_of_nonneg_left hn0.le (Real.exp_pos η) hXη
          calc ∫ η in Real.log X..(Real.log X + ell), Real.exp (-(n : ℝ) / Real.exp η)
              ≤ ∫ _η in Real.log X..(Real.log X + ell), Real.exp (-(n : ℝ) / (X * Real.exp ell)) :=
                intervalIntegral.integral_mono_on (by linarith) (hint _ _)
                  intervalIntegrable_const hmono
            _ = ell * Real.exp (-(n : ℝ) / (X * Real.exp ell)) := by
                rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left]
        rw [Wwin]
        have : (1 / ell) * (∫ η in Real.log X..(Real.log X + ell), Real.exp (-(n : ℝ) / Real.exp η))
            ≤ Real.exp (-(n : ℝ) / (X * Real.exp ell)) := by
          calc (1 / ell) * (∫ η in Real.log X..(Real.log X + ell), Real.exp (-(n : ℝ) / Real.exp η))
              ≤ (1 / ell) * (ell * Real.exp (-(n : ℝ) / (X * Real.exp ell))) :=
                mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = Real.exp (-(n : ℝ) / (X * Real.exp ell)) := by field_simp
        have e : (n : ℝ) * -(1 / (X * Real.exp ell)) = -(n : ℝ) / (X * Real.exp ell) := by ring
        rw [e]
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / ell) h2]
      have hP : (Pfun N R n) ^ 2 ≤ (⌊R⌋₊ : ℝ) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_Pfun_le N R n) 2
      have hWnn : 0 ≤ Wwin M0 X ell n := (Wwin_pos hM0 hell hlt hn).le
      calc (n : ℝ)⁻¹ * (Pfun N R n) ^ 2 * Wwin M0 X ell n
          ≤ 1 * (⌊R⌋₊ : ℝ) ^ 2 * Real.exp (-(1 / (X * Real.exp ell))) ^ n := by
            gcongr
            exact inv_le_one_of_one_le₀ hn1
        _ ≤ (⌊R⌋₊ : ℝ) ^ 2 * ((n : ℝ) ^ 1 * Real.exp (-(1 / (X * Real.exp ell))) ^ n) := by
            rw [pow_one, one_mul]
            exact mul_le_mul_of_nonneg_left
              (le_mul_of_one_le_left (pow_nonneg (Real.exp_pos _).le n) hn1) (by positivity)
  have h := halasz_duality (fun j => ρ j - σ) χ
    (fun j => by simp only [Complex.sub_re, Complex.ofReal_re]; linarith [hρ j])
    c b hb0 hbnn hbc hsum hbs
  simp only [hcn] at h
  have hF : ∀ j, Fgen c (χ j) (ρ j - σ) = Fdet (χ j) z1 z2 R X (ρ j) :=
    fun j => Fgen_cDet_eq_Fdet (χ j) hz10 (ρ j)
  simp only [hF] at h
  exact h

/-- Parameter sanity at the frozen values: `M₀e^ℓ = D^{61/100} ≤ z₁ = D^{31/50}` and
`2z₁ ≤ X = D^{6/5}` once `log D ≥ 2`. -/
lemma frozen_window_hyps {D : ℝ} (hD : 1 < D) (hLD : 2 ≤ Real.log D) :
    1 ≤ z1par D ∧ z1par D < z2par D ∧ M0par D * Real.exp (ellpar D) ≤ z1par D
      ∧ 2 * z1par D ≤ Xpar D := by
  have hD0 : 0 < D := by linarith
  refine ⟨Real.one_le_rpow hD.le (by norm_num), ?_, ?_, ?_⟩
  · exact Real.rpow_lt_rpow_of_exponent_lt hD (by norm_num)
  · rw [M0par, z1par, ellpar, Real.rpow_def_of_pos hD0, Real.rpow_def_of_pos hD0,
      ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  · rw [z1par, Xpar]
    have h : (2 : ℝ) ≤ D ^ (29 / 50 : ℝ) := by
      rw [Real.rpow_def_of_pos hD0]
      have := Real.add_one_le_exp (Real.log D * (29 / 50))
      linarith
    calc 2 * D ^ (31 / 50 : ℝ) ≤ D ^ (29 / 50 : ℝ) * D ^ (31 / 50 : ℝ) :=
          mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hD0.le _)
      _ = D ^ (6 / 5 : ℝ) := by rw [← Real.rpow_add hD0]; norm_num

/-- **Lemma 5.1 at the frozen parameters** (the form Theorem 8.3 consumes): for zeros
`ρ_j` with `Re ρ_j ≥ σ ≥ 0`, `D > 1`, `log D ≥ 2`. -/
theorem halasz_duality_frozen (N : ℕ) [NeZero N] {D : ℝ} (hD : 1 < D) (hLD : 2 ≤ Real.log D)
    {J : Type*} [Fintype J] (ρ : J → ℂ) (χ : J → DirichletCharacter ℂ N) {σ : ℝ} (hσ : 0 ≤ σ)
    (hρ : ∀ j, σ ≤ (ρ j).re) :
    (∑ j, ‖Fdet (χ j) (z1par D) (z2par D) (Rpar D) (Xpar D) (ρ j)‖) ^ 2
      ≤ (∑' n, (cDet N (z1par D) (z2par D) (Rpar D) (Xpar D) σ n) ^ 2
            / bMaj N (Rpar D) (M0par D) (Xpar D) (ellpar D) n)
        * ∑ j, ∑ k, ‖Bgram N (Rpar D) (M0par D) (Xpar D) (ellpar D) (χ j * (χ k)⁻¹)
            ((ρ j - σ) + conj (ρ k - σ))‖ := by
  obtain ⟨h1, h2, h3, h4⟩ := frozen_window_hyps hD hLD
  exact halasz_duality_detector N ρ χ hσ hρ h1 h2 (Real.rpow_pos_of_pos (by linarith) _)
    (ellpar_pos hD) h3 h4

open scoped Classical in
/-- **Proposition 6.1 at the frozen parameters.** -/
theorem Bgram_eq_main_add_rem_frozen (N : ℕ) [NeZero N] {D : ℝ} (hD : 1 < D)
    (χ : DirichletCharacter ℂ N) {𝔰 : ℂ} (hx0 : 0 ≤ 𝔰.re) (hx1 : 𝔰.re ≤ 1 / 50) :
    Bgram N (Rpar D) (M0par D) (Xpar D) (ellpar D) χ 𝔰
      = (if χ = 1 then ((N.totient : ℂ) / N) * ((PhiR N (Rpar D) : ℝ) : ℂ)
            * G1 (M0par D) (Xpar D) (ellpar D) (-𝔰) else 0)
        + Brem N (Rpar D) (M0par D) (Xpar D) (ellpar D) χ 𝔰 := by
  have hD0 : 0 < D := by linarith
  have hL : 0 ≤ Real.log D := Real.log_nonneg hD.le
  exact Bgram_eq_main_add_rem N (Rpar D) (M0par D) (Xpar D)
    (by rw [log_M0par hD0]; linarith) (by rw [log_Xpar hD0]; linarith) (ellpar_pos hD) χ hx0 hx1

/-- `G₁(0) = (3/5)𝓛` at the frozen parameters (the residue at `𝔰 = 0`). -/
lemma G1_zero_frozen {D : ℝ} (hD : 1 < D) :
    G1 (M0par D) (Xpar D) (ellpar D) 0 = ((3 / 5 * Real.log D : ℝ) : ℂ) := by
  have hD0 : 0 < D := by linarith
  rw [G1_zero _ _ (ellpar_pos hD), log_Xpar hD0, log_M0par hD0]
  congr 1; ring

end GramFunction
end Carmichael
