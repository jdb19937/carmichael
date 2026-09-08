/-
Route Z, sortie Z6c-shift: blueprint Lemmas 4.1 (detection identity) and 4.2
(contour term is small), assembled into `Detector.DetectionEstimate` and
blueprint Proposition 4.4, for EVERY Dirichlet character `χ mod N`.
Blueprint: routez/Z0b-density.md §4, §9–§10 (principal character), §11.1 rows
1, 2, 3, 4, 5, §12.3 (frozen Z6c statement).

No `sorry`, no `axiom`, no `native_decide` in this file.

SCOPE.  All `χ mod N` (primitive, imprimitive, principal).  The convexity input
is `LConvexityCorollaries.norm_LFunction_le_convexity_all` (constant
`2·10⁵·2^{ω(N)}`, pole term `1/‖s−1‖`), with `2^{ω(N)}` absorbed by I9(d)
(`two_pow_card_primeFactors_le_rpow`, `2^{ω(N)} ≤ C_τ·N^{1/800}`,
`C_τ := 2^{2^{800}}`, here `Ctau`).  For `χ = χ₀` the contour shift crosses
the `L`-pole at `w = 1−ρ`; its residue is exactly `Detector.Epole`.  The
principal case needs `ρ ≠ 1` (the pole of `L(·,χ₀)` is not a zero: at `ρ = 1`
the integrand would carry a double pole at `w = 0` and the identity is
meaningless); in Proposition 4.4 this is implied by the frozen height clause
`|Im ρ| ≥ Λ₀(σ)` since `Λ₀ > 0`.

THRESHOLD (T1), frozen here:  `2·10¹⁴·C_τ·log D ≤ D^{79/4000}`, exponent
`79/4000 = 0.01975` = blueprint §11.1 rows 1+2+3+4 against row 5
(`1.176 − 0.495 − 0.63 − 0.03 − 0.00125`).  Constant walk:
`C₄ = 6·10⁵ · 6432·C_Γ · C_τ = 20006092800000·C_τ` (`C_Γ = 5184`, I8(d)'s
`6432·C_Γ`, `6·10⁵ = 3·2·10⁵` from the master convexity constant `2·10⁵`, the
factor `2` of `log(N(|t|+3)) ≤ 2𝓛(1+|u|)`, and the pole term `1/‖s−1‖ ≤ 2`
folded as a third unit), and `8·C₄ ≤ 2·10¹⁴·C_τ`.  The threshold is supplied
as a hypothesis everywhere; nothing downstream is silently retuned.  It is far
stronger than `Detection.lean`'s `200 ≤ log D` (which is also carried).

DELIVERED (all fully proved):

§1  `integral_Gamma_cpow_line` — the Mellin identity
    `∫_ℝ y^{−(c+iu)}Γ(c+iu) du = 2π e^{−y}` for `y > 0`, `1/100 ≤ c ≤ 3`.
    Route: Mathlib `mellinInv_mellin_eq` (Fourier inversion) at `f x = e^{−x}`,
    whose Mellin transform is `Γ` (`Complex.GammaIntegral_eq_mellin`); the
    vertical integrability side condition is I8(d)
    (`GammaStrip.integrable_norm_Gamma_line`).

§2  `Ectr`, `ectrInt` (definitions), `Ctau` (irreducible), the spent I9(d)
    `two_pow_card_primeFactors_le_Ctau_mul`, I1 on the shifted line
    `norm_LFunction_shifted_le` (all `χ`:
    `‖L(ρ+w,χ)‖ ≤ 6·10⁵·C_τ·D^{397/800}·𝓛·(1+|u|)²` on `Re(ρ+w) = ε₂`), and
    **blueprint Lemma 4.2**, `norm_Ectr_le` (all `χ`): under (T1),
    `‖E_ctr(ρ,χ)‖ ≤ P(1)/8` at every `ρ` with `99/100 ≤ Re ρ ≤ 1` and
    `N(|Im ρ|+2) ≤ D`.  Exponent walk (§11.1): row 1 `+0.495`, row 2 `+0.63`
    (`z₂`), row 3 `+0.03` (`R³`, `sum_inv_mul_cube_le`), row 4 `+0.00125`
    (`D^{1/800}`), row 5 `−1.176` (`X^{ε₂−β} ≤ X^{−49/50}`); total `−0.01975`.
    `P(1) ≥ 1` (`one_le_P1`) replaces the blueprint's `P(1) ≥ (ε/2)Q_R𝓛` on
    the right-hand side, which is why (T1) here has no `Q_R^{-1}` factor.

§3  Analyticity and the removable singularity at `w = 0`: `Hfun`, `Ghat`,
    `differentiableAt_Hfun` (off the `L`-pole `ρ + w = 1` when `χ = χ₀`),
    `differentiableAt_dslope_Hfun`, `differentiableAt_Ghat` (on `Re w > −1`),
    `Ghat_eq_of_ne`, `Hfun_zero_of_LFunction_eq_zero`.  The residue at `w = 0`
    is `L(ρ,χ)M_r(ρ,χ) = 0` BECAUSE `ρ` is a zero; packaged as
    `Ĝ(w) := Γ(w+1)·dslope H 0 w`, holomorphic near `0`, equal to `Γ(w)H(w)`
    off `w = 0`.
    Principal-character regularisation: `Hone` (`H₁(w) = X^w·L₁(ρ+w)·M_r`, with
    `L₁ = ` Mathlib's entire `LFunctionTrivChar₁`), `Gone`
    (`Ĝ₁ = Γ(w+1)·dslope H₁ 0`), `Hone_eq_of_ne` (`H₁ = (w−(1−ρ))·H` off the
    pole), `Hone_zero`, `Hone_at_pole` (`H₁(1−ρ) = X^{1−ρ}(φ(N)/N)M_r(1,χ₀)`,
    via `LFunctionTrivChar₁_one` and `prod_one_sub_inv_eq_totient_div`),
    `differentiableAt_Gone`, `Gone_eq_of_ne`.

§4  `anchor_identity` — the `Re w = 3` display of blueprint Lemma 4.1, all `χ`:
    `∑_n a(n)ψ_r(n)χ(n)e^{−n/X}n^{−ρ} = (1/2πi)∫_{(3)} Γ(w)X^w L(ρ+w,χ)M_r(ρ+w,χ)dw`.
    Route: §1 termwise, `integral_tsum_of_summable_integral_norm`, Lemma 3.1
    (`LSeries_bvA_psi_eq_LFunction_mul_Mr`).  Support: `ofReal_div_cpow`,
    `Fterm`, `Sterm`, `norm_Fterm_le`, `integrable_Fterm`, `integral_Fterm`,
    `Fterm_eq_term`, `tsum_Fterm`.

§5  The contour shift `Re w = 3 → Re w = ε₂ − β`:
 * `norm_LFunction_strip_le` (all `χ`, polynomial bound on `Re s ≥ 1/100` at
   distance `≥ 99/100` from `s = 1`), `norm_Hfun_le`, `norm_Ghat_le`,
   `continuous_Ghat_line`, `integrable_Ghat_line` (edge lines `Re w = ε₂−β`
   and `Re w = 3`, both at distance `≥ 99/100` from the `L`-pole).
 * Rectangle toolkit: `rectInt_cauchy_on` (Cauchy formula on a rectangle for a
   numerator holomorphic on the closed rectangle; extends
   `PerronKernel.rectInt_cauchy` via `continuousOn_dslope`), `rectInt_coord`,
   `shift_lines_residue` (generic: rectangle integrals eventually equal to `K`
   give `∫_{(b)} − ∫_{(a)} = −i·K`), `shift_lines` (`K = 0`).
 * Horizontal edges (all `χ`): `norm_integral_Ghat_horiz_le` at heights
   `T ≥ |Im ρ| + 1`, `tendsto_Ghat_horiz`, `tendsto_one_add_sq_mul_exp_neg`.
 * `rectInt_Ghat_principal`: for `χ₀`, `∮ Ĝ = 2πi·Γ(1−ρ)X^{1−ρ}(φ(N)/N)M_r(1,χ₀)`
   over `[ε₂−β, 3] × [−T, T]`, `T ≥ |Im ρ| + 1` (on the frame `Ĝ = Ĝ₁/(w−(1−ρ))`,
   then `rectInt_cauchy_on`).
 * `Ghat_line_shift` (`χ ≠ χ₀`, Cauchy–Goursat) and `Ghat_line_shift_principal`
   (`χ = χ₀`, `ρ ≠ 1`: `∫_{(3)} = ∫_{(ε₂−β)} + 2π·Γ(1−ρ)X^{1−ρ}(φ(N)/N)M_r(1,χ₀)`).

§6  `summable_Sterm`, `ofReal_Pfun`, `sum_Rset_Sterm`, `tsum_detector_split`
    (`∑_n a(n)P(n)e^{−n/X}χ(n)n^{−ρ} = F(ρ,χ) + e^{−1/X}P(1)`, using the BV
    vanishing property `bvA_eq_zero`).

§7  Assembly (hypotheses common to all: `1 < D`, `99/100 ≤ Re ρ ≤ 1`,
    `L(ρ,χ) = 0`; the estimates add `200 ≤ log D`, `N(|Im ρ|+2) ≤ D`, (T1)):
 * `tsum_Sterm_eq_integral_shift` (`χ ≠ χ₀`) and
   `tsum_Sterm_eq_integral_shift_principal` (`χ₀`, `ρ ≠ 1`): Lemma 4.1 at a
   single modulus `r`, the latter with the residue term.
 * **Blueprint Lemma 4.1**: `detection_identity_all` (all `χ`, `χ = χ₀ → ρ ≠ 1`):
   `F(ρ,χ) + e^{−1/X}·P(1) = E_ctr(ρ,χ) + E_pole(ρ,χ)` with `E_pole` literally
   `Detector.Epole`; corollaries `detection_identity` (`χ ≠ 1`, `E_pole = 0`)
   and `detection_identity_principal` (`χ₀`, `ρ ≠ 1`).
 * **Lemmas 4.1 + 4.2**: `detection_estimate_all` (all `χ`, `χ = χ₀ → ρ ≠ 1`)
   `: Detector.DetectionEstimate χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ`;
   corollaries `detection_estimate` (`χ ≠ 1`), `detection_estimate_principal`.
 * **Blueprint Proposition 4.4 = frozen Z6c, unconditional**:
   `detector_lower_bound_of_zero_all` (all `χ`; clause
   `χ = 1 → Λ₀(99/100) ≤ |Im ρ|` with `Λ₀ = Lambda0 D (99/100) (log(3200·e·60))`,
   exactly `Detection.detector_lower_bound_uncond`'s):
   `(1/400)·(φ(N)/N)·log D ≤ ‖F(ρ,χ)‖`; corollaries `detector_lower_bound_of_zero`
   (`χ ≠ 1`, no height clause) and `detector_lower_bound_of_zero_principal`.
   `#print axioms` on every theorem above: [propext, Classical.choice, Quot.sound].

CONTOUR DESIGN.  Rectangle corners `c − iT` and `3 + iT`,
`c := ε₂ − β = 1/100 − Re ρ ∈ [−99/100, −98/100]`, `T ≥ |Im ρ| + 1`, `T → ∞`.
 * anchor / right edge `Re w = 3`: pays the Mellin/Fubini convergence — the
   weight `n^{−3}` against `|a(n)ψ_r(n)| ≤ n·r` gives `∑ n^{−2}`, so no `rpow`
   series is ever needed (this is why the anchor is at `3`, not the blueprint's
   `2`; `3` is also the right endpoint of `GammaStrip`'s frozen strip).
 * left edge `Re w = c`: pays the whole size estimate — I1 at `Re(ρ+w) = ε₂`,
   `‖M_r‖ ≤ z₂r³`, I8(d), I9(d), and the drop `X^{c} ≤ X^{−49/50}`.
 * horizontal edges `Im w = ±T`: pay nothing; killed by I8(b)
   (`GammaStrip.norm_Gamma_le_of_dist`, `‖Γ‖ ≤ 201·C_Γ·e^{−|T|}` at distance
   `≥ 1/100` from `{0,−1}`) against the polynomial `(1+|T|)²` from
   `norm_Hfun_le`; `T ≥ |Im ρ| + 1` keeps them at distance `≥ 1` from the
   `L`-pole, so the master convexity bound's `1/‖s−1‖` term is `≤ 1` there.
 * the pole at `w = 0` is absent (removable, §3); the pole at `w = 1−ρ` is
   absent for `χ ≠ χ₀` and is the residue `E_pole` for `χ = χ₀`.

DELTAS VS. THE SPEC (routez/Z0b-density.md), all reported, none silent:
 * (T1) is `2·10¹⁴·C_τ·log D ≤ D^{79/4000}` with the explicit
   `C_τ = 2^{2^{800}}`, and no `Q_R^{-1}` factor (see §2).  Multiplicative
   constants are free on this campaign; the exponent `79/4000` and the single
   power of `log D` are the frozen ones.
 * Lemma 4.1 and `DetectionEstimate` for `χ = χ₀` carry the extra hypothesis
   `ρ ≠ 1`; Proposition 4.4 does not (it follows from the frozen `Λ₀` clause).
 * The strip bound on `Re s ≥ 1/100` (used only for the horizontal edges and
   integrability, never for size) carries the constant `6·10⁵·2^{ω(N)}` rather
   than the blueprint's `C_cx`; `2^{ω(N)}` is not spent there.

BLUEPRINT / MATHLIB NOTES:
 * Mathlib's `DirichletCharacter.LFunctionTrivChar₁ N` is
   `Function.update (fun s ↦ (s−1)·L(s,χ₀)) 1 (∏_{p∣N}(1 − p⁻¹))` (an `abbrev`);
   `Function.update_of_ne`/`update_self` inside `simp only` unfold it.
   `Nat.totient_eq_mul_prod_factors` (in `ℚ`) gives `∏(1−1/p) = φ(N)/N`.
 * `DirichletCharacter.differentiableAt_LFunction χ s (hs : s ≠ 1 ∨ χ ≠ 1)` is
   the pin's name and hypothesis order.
 * `Ctau` must be `irreducible_def`: with a plain `def`, `positivity` and
   `ring` unfold it and hit `maxRecDepth` on `2^{2^{800}}`.
 * `ContinuousAt.comp` needs `(f := fun u : ℝ => a + u·I)` explicitly when the
   inner point is already known (first-order unification picks
   `HAdd.hAdd a` otherwise).
 * `differentiable_id'` does not exist in the pin; use `differentiable_id (𝕜 := ℂ)`.
 * `abs_add` is gone; use `abs_add_le`.
 * `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero` is in the `Real` namespace.
 * `summable_Sterm` needs `maxHeartbeats 4000000` (as does `Detector.summable_fdetTerm`).
 * `tsum_sum` is named `Summable.tsum_finsetSum` in the pin.
 * The whole-file check takes ~65 s.
-/
import Carmichael.GammaStrip
import Carmichael.PerronKernel
import Carmichael.LConvexityCorollaries
import Mathlib.Analysis.MellinInversion

set_option autoImplicit false

namespace Carmichael

open Complex MeasureTheory
open scoped Real

namespace DetectionShift

/-! ## §1.  The Mellin identity `e^{−y} = (1/2πi)∫_{(c)} Γ(w) y^{−w} dw`

Blueprint Lemma 4.1, first display.  Route: Mathlib's `mellinInv_mellin_eq`
(Fourier inversion) applied to `f x = e^{−x}`, whose Mellin transform is `Γ`.
-/

/-- The exponential kernel whose Mellin transform is `Γ`. -/
noncomputable def expNeg : ℝ → ℂ := fun x => ((Real.exp (-x) : ℝ) : ℂ)

lemma mellin_expNeg {s : ℂ} (hs : 0 < s.re) : mellin expNeg s = Complex.Gamma s := by
  have h : mellin expNeg s = Complex.GammaIntegral s :=
    (congrFun Complex.GammaIntegral_eq_mellin s).symm
  rw [h, Complex.Gamma_eq_integral hs]

lemma mellinConvergent_expNeg {c : ℝ} (hc : 0 < c) :
    MellinConvergent expNeg (c : ℂ) := by
  have h := Complex.GammaIntegral_convergent (s := (c : ℂ)) (by simpa using hc)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp only [expNeg, smul_eq_mul]
  ring

/-- On a vertical line `Re w = c` with `1/100 ≤ c ≤ 3`, `Γ` is continuous. -/
lemma continuous_Gamma_line' {c : ℝ} (hc : 0 < c) :
    Continuous (fun u : ℝ => Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)) := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have hinner : Continuous (fun u : ℝ => ((c : ℂ) + (u : ℂ) * Complex.I)) := by fun_prop
  have hne : ∀ n : ℕ, ((c : ℂ) + (u : ℂ) * Complex.I) ≠ -n := by
    intro n hcontra
    have := congrArg Complex.re hcontra
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  exact ContinuousAt.comp (f := fun u : ℝ => ((c : ℂ) + (u : ℂ) * Complex.I))
    (Complex.differentiableAt_Gamma _ hne).continuousAt hinner.continuousAt

/-- `Γ` is integrable on the vertical line `Re w = c`, `1/100 ≤ c ≤ 3` (I8(d)). -/
lemma integrable_Gamma_line {c : ℝ} (hc1 : 1/100 ≤ c) (hc2 : c ≤ 3) :
    Integrable (fun u : ℝ => Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have h1 : -(101/100 : ℝ) ≤ c := by linarith
  have h3 : (1:ℝ)/100 ≤ |c| := by rwa [abs_of_pos hc0]
  have h4 : (1:ℝ)/100 ≤ |c + 1| := by rw [abs_of_pos (by linarith)]; linarith
  refine Integrable.mono' (GammaStrip.integrable_norm_Gamma_line h1 hc2 h3 h4)
    (continuous_Gamma_line' hc0).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  have : (1 : ℝ) ≤ (1 + |u|) ^ 2 := by nlinarith [abs_nonneg u]
  nlinarith [norm_nonneg (Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I))]

lemma verticalIntegrable_mellin_expNeg {c : ℝ} (hc1 : 1/100 ≤ c) (hc2 : c ≤ 3) :
    Complex.VerticalIntegrable (mellin expNeg) c := by
  have hc0 : (0 : ℝ) < c := by linarith
  refine (integrable_Gamma_line hc1 hc2).congr ?_
  refine Filter.Eventually.of_forall fun u => ?_
  refine (mellin_expNeg ?_).symm
  simp [hc0]

/-- **The Mellin identity** (blueprint Lemma 4.1, first display):
`∫_ℝ y^{−(c+iu)} Γ(c+iu) du = 2π e^{−y}` for `y > 0` and `1/100 ≤ c ≤ 3`. -/
theorem integral_Gamma_cpow_line {c : ℝ} (hc1 : 1/100 ≤ c) (hc2 : c ≤ 3) {y : ℝ} (hy : 0 < y) :
    ∫ u : ℝ, (y : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))
        * Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
      = ((2 * π : ℝ) : ℂ) * ((Real.exp (-y) : ℝ) : ℂ) := by
  have hc0 : (0 : ℝ) < c := by linarith
  have hcont : Continuous expNeg := by
    unfold expNeg
    fun_prop
  have hkey : mellinInv c (mellin expNeg) y = expNeg y :=
    mellinInv_mellin_eq c expNeg hy (mellinConvergent_expNeg hc0)
      (verticalIntegrable_mellin_expNeg hc1 hc2) hcont.continuousAt
  rw [mellinInv] at hkey
  have hrw : ∀ u : ℝ, (y : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))
      • mellin expNeg ((c : ℂ) + (u : ℂ) * Complex.I)
      = (y : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))
        * Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I) := by
    intro u
    rw [smul_eq_mul, mellin_expNeg (by simp [hc0])]
  simp only [hrw] at hkey
  set J : ℂ := ∫ u : ℝ, (y : ℂ) ^ (-((c : ℂ) + (u : ℂ) * Complex.I))
      * Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I) with hJ
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have h2 : ((2 * π : ℝ) : ℂ) * (((1 : ℝ) / (2 * π) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, show (2 * π) * (1 / (2 * π)) = 1 from by field_simp]
    norm_num
  calc J = (((2 * π : ℝ) : ℂ) * (((1 : ℝ) / (2 * π) : ℝ) : ℂ)) * J := by rw [h2, one_mul]
    _ = ((2 * π : ℝ) : ℂ) * ((((1 : ℝ) / (2 * π) : ℝ) : ℂ) * J) := by ring
    _ = ((2 * π : ℝ) : ℂ) * ((Real.exp (-y) : ℝ) : ℂ) := by
        have hsm : (((1 : ℝ) / (2 * π) : ℝ) : ℂ) * J = ((1 : ℝ) / (2 * π)) • J :=
          Complex.real_smul.symm
        rw [hsm, hkey]
        rfl

/-! ## §2.  The contour term `E_ctr` and blueprint Lemma 4.2 -/

open Detector

/-- The blueprint's `ε₂ = 1/100`, the detector contour line (§1 parameter table). -/
noncomputable def eps2 : ℝ := 1/100

/-- The integrand of the shifted contour term on the line `Re w = c`:
`Γ(w)·X^w·L(ρ+w,χ)·M_r(ρ+w,χ)` at `w = c + iu`. -/
noncomputable def ectrInt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 X : ℝ) (r : ℕ) (ρ : ℂ) (c u : ℝ) : ℂ :=
  Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
    * (X : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I)
    * DirichletCharacter.LFunction χ (ρ + ((c : ℂ) + (u : ℂ) * Complex.I))
    * Mr χ z1 z2 r (ρ + ((c : ℂ) + (u : ℂ) * Complex.I))

/-- Blueprint `E_ctr(ρ,χ)` (Lemma 4.1): the contour term after the shift to
`Re w = ε₂ − β`. -/
noncomputable def Ectr {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 R X : ℝ) (ρ : ℂ) : ℂ :=
  (((1 / (2 * π) : ℝ)) : ℂ) * ∑ r ∈ Rset N R, ((r : ℂ))⁻¹ *
    ∫ u : ℝ, ectrInt χ z1 z2 X r ρ (eps2 - ρ.re) u

/-! ### Elementary ingredients -/

/-- `P(1) ≥ 1`: the `r = 1` term. -/
lemma one_le_P1 (N : ℕ) {R : ℝ} (hR : 1 ≤ R) : 1 ≤ P1 N R := by
  have h1 : (1 : ℕ) ∈ Rset N R := by
    refine mem_Rset.mpr ⟨⟨le_rfl, ?_⟩, squarefree_one, Nat.coprime_one_left N⟩
    exact Nat.le_floor (by exact_mod_cast hR)
  have := Finset.single_le_sum (f := fun r : ℕ => ((r : ℝ))⁻¹)
    (fun r _ => by positivity) h1
  simpa [P1] using this

/-- `∑'_{r ≤ R} r⁻¹·r³ ≤ R³` (the pseudocharacter mass, §11.1 row 3). -/
lemma sum_inv_mul_cube_le (N : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    ∑ r ∈ Rset N R, (r : ℝ)⁻¹ * (r : ℝ) ^ 3 ≤ R ^ 3 := by
  have hstep : ∀ r ∈ Rset N R, (r : ℝ)⁻¹ * (r : ℝ) ^ 3 ≤ R ^ 2 := by
    intro r hrs
    obtain ⟨⟨hr1, hrfloor⟩, -, -⟩ := mem_Rset.mp hrs
    have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have hrne : (r : ℝ) ≠ 0 := by linarith
    have hrleR : (r : ℝ) ≤ R := by
      calc (r : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast hrfloor
        _ ≤ R := Nat.floor_le (by linarith)
    have : (r : ℝ)⁻¹ * (r : ℝ) ^ 3 = (r : ℝ) ^ 2 := by field_simp
    rw [this]
    nlinarith
  calc ∑ r ∈ Rset N R, (r : ℝ)⁻¹ * (r : ℝ) ^ 3
      ≤ ∑ _r ∈ Rset N R, R ^ 2 := Finset.sum_le_sum hstep
    _ = ((Rset N R).card : ℝ) * R ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ R * R ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc ((Rset N R).card : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast card_Rset_le N R
          _ ≤ R := Nat.floor_le (by linarith)
    _ = R ^ 3 := by ring

/-- `C_τ = 2^{2^{800}}`, the I9(d) constant of
`LConvexityCorollaries.two_pow_card_primeFactors_le_rpow` (`2^{ω(m)} ≤ C_τ·m^{1/800}`).
Irreducible: nothing may ever try to evaluate it. -/
irreducible_def Ctau : ℝ := (2 : ℝ) ^ (2 ^ 800 : ℕ)

lemma one_le_Ctau : 1 ≤ Ctau := by rw [Ctau_def]; exact one_le_pow₀ (by norm_num)

lemma Ctau_pos : 0 < Ctau := by linarith [one_le_Ctau]

/-- **I9(d), spent** (blueprint §11.1 row 4): `2^{ω(N)} ≤ C_τ·D^{1/800}` for `N ≤ D`. -/
lemma two_pow_card_primeFactors_le_Ctau_mul {N : ℕ} [NeZero N] {D : ℝ}
    (hND : (N : ℝ) ≤ D) :
    (2 : ℝ) ^ N.primeFactors.card ≤ Ctau * D ^ (1/800 : ℝ) := by
  refine (two_pow_card_primeFactors_le_rpow (NeZero.ne N)).trans ?_
  rw [← Ctau_def]
  refine mul_le_mul_of_nonneg_left ?_ Ctau_pos.le
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) hND (by norm_num)

/-- **I1 on the shifted line** (blueprint §11.1 rows 1 and 4, used in Lemma 4.2).
For every `χ mod N`, on the line `Re(ρ+w) = ε₂ = 1/100`:
`‖L(ρ+w,χ)‖ ≤ 6·10⁵·C_τ·D^{397/800}·𝓛·(1+|u|)²`, where `D ≥ N(|γ|+2)`.  Route: the
master convexity bound `norm_LFunction_le_convexity_all` (its pole term
`1/‖s−1‖ ≤ 100/99` on this line), the factor `2^{ω(N)}` absorbed by I9(d) as
`C_τ·D^{1/800}` (`397/800 = 99/200 + 1/800`). -/
lemma norm_LFunction_shifted_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {D : ℝ} (hD1 : 1 < D) (hLD : 200 ≤ Real.log D)
    {ρ : ℂ} {c : ℝ} (hc : ρ.re + c = 1/100)
    (hDN : (N : ℝ) * (|ρ.im| + 2) ≤ D) (u : ℝ) :
    ‖DirichletCharacter.LFunction χ (ρ + ((c : ℂ) + (u : ℂ) * Complex.I))‖
      ≤ 600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  set s : ℂ := ρ + ((c : ℂ) + (u : ℂ) * Complex.I) with hs
  have hsre : s.re = 1/100 := by
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
  have hmax : max ((1 - (1:ℝ)/100)/2) 0 = 99/200 := by
    rw [max_eq_left (by norm_num)]; norm_num
  rw [hmax] at hconv
  refine hconv.trans ?_
  have hu0 : (0 : ℝ) ≤ |u| := abs_nonneg u
  have hu1 : (1 : ℝ) ≤ 1 + |u| := by linarith
  have habs : |s.im| ≤ |ρ.im| + |u| := by rw [hsim]; exact abs_add_le _ _
  have hρ0 : (0 : ℝ) ≤ |ρ.im| := abs_nonneg _
  -- the pole term
  have hpole : 1 / ‖s - 1‖ ≤ 2 := by
    have h1 : (99/100 : ℝ) ≤ ‖s - 1‖ := by
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
  have hpow : ((N : ℝ) * (|s.im| + 2)) ^ (99/200 : ℝ) ≤ D ^ (99/200 : ℝ) * (1 + |u|) := by
    calc ((N : ℝ) * (|s.im| + 2)) ^ (99/200 : ℝ) ≤ (D * (1 + |u|)) ^ (99/200 : ℝ) :=
          Real.rpow_le_rpow hbase0 hbase (by norm_num)
      _ = D ^ (99/200 : ℝ) * (1 + |u|) ^ (99/200 : ℝ) :=
          Real.mul_rpow hD0.le (by linarith)
      _ ≤ D ^ (99/200 : ℝ) * (1 + |u|) ^ (1 : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hD0.le _)
          exact Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
      _ = D ^ (99/200 : ℝ) * (1 + |u|) := by rw [Real.rpow_one]
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
  have hAnn : (0 : ℝ) ≤ D ^ (99/200 : ℝ) := Real.rpow_nonneg hD0.le _
  have hA1 : (1 : ℝ) ≤ D ^ (99/200 : ℝ) := by
    calc (1 : ℝ) = D ^ (0 : ℝ) := (Real.rpow_zero D).symm
      _ ≤ D ^ (99/200 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by norm_num)
  have hlognn : (0 : ℝ) ≤ Real.log D := by linarith
  have hsq1 : (1 : ℝ) ≤ (1 + |u|) ^ 2 := by nlinarith
  -- the main product
  have hmain : ((N : ℝ) * (|s.im| + 2)) ^ (99/200 : ℝ) * Real.log ((N : ℝ) * (|s.im| + 3))
      ≤ 2 * D ^ (99/200 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by
    calc ((N : ℝ) * (|s.im| + 2)) ^ (99/200 : ℝ) * Real.log ((N : ℝ) * (|s.im| + 3))
        ≤ (D ^ (99/200 : ℝ) * (1 + |u|)) * (2 * Real.log D * (1 + |u|)) :=
          mul_le_mul hpow hlog hL0 (by positivity)
      _ = 2 * D ^ (99/200 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by ring
  have hinner : ((N : ℝ) * (|s.im| + 2)) ^ (99/200 : ℝ) * Real.log ((N : ℝ) * (|s.im| + 3))
      + 1 / ‖s - 1‖ ≤ 3 * D ^ (99/200 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by
    have h2 : (2 : ℝ) ≤ D ^ (99/200 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by
      have : (200 : ℝ) ≤ D ^ (99/200 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by
        calc (200 : ℝ) = 1 * 200 * 1 := by norm_num
          _ ≤ D ^ (99/200 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by gcongr
      linarith
    linarith
  have hω : (2 : ℝ) ^ N.primeFactors.card ≤ Ctau * D ^ (1/800 : ℝ) :=
    two_pow_card_primeFactors_le_Ctau_mul hND
  have hin0 : (0 : ℝ) ≤ ((N : ℝ) * (|s.im| + 2)) ^ (99/200 : ℝ)
      * Real.log ((N : ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖ := by positivity
  have hexp : D ^ (1/800 : ℝ) * D ^ (99/200 : ℝ) = D ^ (397/800 : ℝ) := by
    rw [← Real.rpow_add hD0]; norm_num
  calc 200000 * (2 : ℝ) ^ N.primeFactors.card
        * (((N : ℝ) * (|s.im| + 2)) ^ (99/200 : ℝ) * Real.log ((N : ℝ) * (|s.im| + 3))
          + 1 / ‖s - 1‖)
      ≤ 200000 * (Ctau * D ^ (1/800 : ℝ))
        * (3 * D ^ (99/200 : ℝ) * Real.log D * (1 + |u|) ^ 2) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hω (by norm_num)) hinner hin0 ?_
        have := Ctau_pos
        positivity
    _ = 600000 * Ctau * (D ^ (1/800 : ℝ) * D ^ (99/200 : ℝ)) * Real.log D * (1 + |u|) ^ 2 := by
        ring
    _ = 600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D * (1 + |u|) ^ 2 := by rw [hexp]

/-- Pointwise bound for the `E_ctr` integrand on the shifted line. -/
lemma norm_ectrInt_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {D : ℝ} (hD1 : 1 < D) (hLD : 200 ≤ Real.log D)
    {ρ : ℂ} {c : ℝ} (hc : ρ.re + c = 1/100)
    (hDN : (N : ℝ) * (|ρ.im| + 2) ≤ D) {r : ℕ} (hr : Squarefree r) (u : ℝ) :
    ‖ectrInt χ (z1par D) (z2par D) (Xpar D) r ρ c u‖
      ≤ (Xpar D ^ c * (600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D)
          * (z2par D * (r : ℝ) ^ 3))
        * (‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * (1 + |u|) ^ 2) := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hX0 : (0 : ℝ) < Xpar D := Real.rpow_pos_of_pos hD0 _
  have hz10 : (0 : ℝ) < z1par D := Real.rpow_pos_of_pos hD0 _
  have hz12 : z1par D < z2par D := by
    rw [z1par, z2par]
    exact Real.rpow_lt_rpow_left_iff hD1 |>.mpr (by norm_num)
  have hz20 : (0 : ℝ) < z2par D := Real.rpow_pos_of_pos hD0 _
  have hre : (ρ + ((c : ℂ) + (u : ℂ) * Complex.I)).re = 1/100 := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im]
    linarith [hc]
  have hXn : ‖(Xpar D : ℂ) ^ ((c : ℂ) + (u : ℂ) * Complex.I)‖ = Xpar D ^ c := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0]
    congr 1
    simp
  have hLn := norm_LFunction_shifted_le χ hD1 hLD hc hDN u
  have hMn : ‖Mr χ (z1par D) (z2par D) r (ρ + ((c : ℂ) + (u : ℂ) * Complex.I))‖
      ≤ z2par D * (r : ℝ) ^ 3 :=
    norm_Mr_le hr hz10 hz12 χ (by rw [hre]; norm_num)
  rw [ectrInt, norm_mul, norm_mul, norm_mul, hXn]
  have hCt := Ctau_pos
  have hA0 : (0 : ℝ) ≤ 600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D := by
    have : (0 : ℝ) ≤ Real.log D := by linarith
    have h2 : (0 : ℝ) ≤ D ^ (397/800 : ℝ) := Real.rpow_nonneg hD0.le _
    positivity
  have hXc0 : (0 : ℝ) ≤ Xpar D ^ c := Real.rpow_nonneg hX0.le _
  have hM0 : (0 : ℝ) ≤ z2par D * (r : ℝ) ^ 3 := by positivity
  have hG0 : (0 : ℝ) ≤ ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ := norm_nonneg _
  calc ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * Xpar D ^ c
        * ‖DirichletCharacter.LFunction χ (ρ + ((c : ℂ) + (u : ℂ) * Complex.I))‖
        * ‖Mr χ (z1par D) (z2par D) r (ρ + ((c : ℂ) + (u : ℂ) * Complex.I))‖
      ≤ ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * Xpar D ^ c
        * (600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D * (1 + |u|) ^ 2)
        * (z2par D * (r : ℝ) ^ 3) := by
        have hstep : ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * Xpar D ^ c
            * ‖DirichletCharacter.LFunction χ (ρ + ((c : ℂ) + (u : ℂ) * Complex.I))‖
            ≤ ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * Xpar D ^ c
              * (600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D * (1 + |u|) ^ 2) :=
          mul_le_mul_of_nonneg_left hLn (by positivity)
        exact mul_le_mul hstep hMn (norm_nonneg _) (by positivity)
    _ = (Xpar D ^ c * (600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D)
          * (z2par D * (r : ℝ) ^ 3))
        * (‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * (1 + |u|) ^ 2) := by ring

/-- Line-integral bound for one pseudocharacter modulus `r` (I8(d) applied). -/
lemma norm_integral_ectrInt_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {D : ℝ} (hD1 : 1 < D) (hLD : 200 ≤ Real.log D)
    {ρ : ℂ} {c : ℝ} (hc : ρ.re + c = 1/100)
    (hc1 : -(99/100 : ℝ) ≤ c) (hc2 : c ≤ -(98/100 : ℝ))
    (hDN : (N : ℝ) * (|ρ.im| + 2) ≤ D) {r : ℕ} (hr : Squarefree r) :
    ‖∫ u : ℝ, ectrInt χ (z1par D) (z2par D) (Xpar D) r ρ c u‖
      ≤ (Xpar D ^ c * (600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D) * z2par D
          * (6432 * GammaStrip.CGamma)) * (r : ℝ) ^ 3 := by
  have hD0 : (0 : ℝ) < D := by linarith
  have h1 : -(101/100 : ℝ) ≤ c := by linarith
  have h2 : c ≤ 3 := by linarith
  have h3 : (1:ℝ)/100 ≤ |c| := by rw [abs_of_nonpos (by linarith)]; linarith
  have h4 : (1:ℝ)/100 ≤ |c + 1| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hGint := GammaStrip.integrable_norm_Gamma_line h1 h2 h3 h4
  have hGle := GammaStrip.integral_norm_Gamma_line_le h1 h2 h3 h4
  set K : ℝ := Xpar D ^ c * (600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D)
      * (z2par D * (r : ℝ) ^ 3) with hKdef
  have hCt := Ctau_pos
  have hK0 : (0 : ℝ) ≤ K := by
    have hXc0 : (0 : ℝ) ≤ Xpar D ^ c := Real.rpow_nonneg (Real.rpow_pos_of_pos hD0 _).le _
    have hA0 : (0 : ℝ) ≤ 600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D := by
      have hl : (0 : ℝ) ≤ Real.log D := by linarith
      have h2' : (0 : ℝ) ≤ D ^ (397/800 : ℝ) := Real.rpow_nonneg hD0.le _
      positivity
    have hz0 : (0 : ℝ) ≤ z2par D * (r : ℝ) ^ 3 := by
      have : (0 : ℝ) ≤ z2par D := (Real.rpow_pos_of_pos hD0 _).le
      positivity
    rw [hKdef]; positivity
  calc ‖∫ u : ℝ, ectrInt χ (z1par D) (z2par D) (Xpar D) r ρ c u‖
      ≤ ∫ u : ℝ, ‖ectrInt χ (z1par D) (z2par D) (Xpar D) r ρ c u‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, K * (‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * (1 + |u|) ^ 2) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
          (hGint.const_mul K) (Filter.Eventually.of_forall fun u => ?_)
        exact norm_ectrInt_le χ hD1 hLD hc hDN hr u
    _ = K * ∫ u : ℝ, ‖Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)‖ * (1 + |u|) ^ 2 :=
        integral_const_mul _ _
    _ ≤ K * (6432 * GammaStrip.CGamma) := mul_le_mul_of_nonneg_left hGle hK0
    _ = (Xpar D ^ c * (600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D) * z2par D
          * (6432 * GammaStrip.CGamma)) * (r : ℝ) ^ 3 := by rw [hKdef]; ring

/-- **Blueprint Lemma 4.2** (the contour term is small).  For every `χ mod N`, at
a point `ρ` with `99/100 ≤ Re ρ ≤ 1` and `N(|Im ρ|+2) ≤ D`, under the threshold
(T1) `2·10¹⁴·C_τ·𝓛 ≤ D^{79/4000}`: `‖E_ctr(ρ,χ)‖ ≤ P(1)/8`.

The `D`-exponent walk is blueprint §11.1: convexity at `Re = ε₂` gives `0.495`
(row 1), the BV upper cut `z₂` gives `0.63` (row 2), the pseudocharacter mass
`R³` gives `0.03` (row 3), the divisor bound I9(d) gives `1/800 = 0.00125`
(row 4), and the contour drop `X^{ε₂−β} ≤ X^{−49/50}` gives `−1.176` (row 5);
total `−0.01975 = −79/4000`. -/
theorem norm_Ectr_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {D : ℝ} (hD1 : 1 < D) (hLD : 200 ≤ Real.log D)
    {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hDN : (N : ℝ) * (|ρ.im| + 2) ≤ D)
    (hT1 : 2 * 10 ^ 14 * Ctau * Real.log D ≤ D ^ (79/4000 : ℝ)) :
    ‖Ectr χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖ ≤ P1 N (Rpar D) / 8 := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hlog0 : (0 : ℝ) ≤ Real.log D := by linarith
  have hCt := Ctau_pos
  set c : ℝ := eps2 - ρ.re with hcdef
  have hc : ρ.re + c = 1/100 := by rw [hcdef, eps2]; ring
  have hc1 : -(99/100 : ℝ) ≤ c := by rw [hcdef, eps2]; linarith
  have hc2 : c ≤ -(98/100 : ℝ) := by rw [hcdef, eps2]; linarith
  have hR1 : (1 : ℝ) ≤ Rpar D := by
    rw [Rpar]
    calc (1 : ℝ) = D ^ (0 : ℝ) := (Real.rpow_zero D).symm
      _ ≤ D ^ (1/100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by norm_num)
  set Kmain : ℝ := Xpar D ^ c * (600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D) * z2par D
      * (6432 * GammaStrip.CGamma) with hKmain
  have hXc0 : (0 : ℝ) ≤ Xpar D ^ c := Real.rpow_nonneg (Real.rpow_pos_of_pos hD0 _).le _
  have hz20 : (0 : ℝ) ≤ z2par D := (Real.rpow_pos_of_pos hD0 _).le
  have hA0 : (0 : ℝ) ≤ 600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D := by
    have h2' : (0 : ℝ) ≤ D ^ (397/800 : ℝ) := Real.rpow_nonneg hD0.le _
    positivity
  have hCG0 : (0 : ℝ) ≤ 6432 * GammaStrip.CGamma := by
    rw [GammaStrip.CGamma_def]; norm_num
  have hKmain0 : (0 : ℝ) ≤ Kmain := by rw [hKmain]; positivity
  -- the `r`-sum
  have hsum : ∑ r ∈ Rset N (Rpar D), (r : ℝ)⁻¹
      * ‖∫ u : ℝ, ectrInt χ (z1par D) (z2par D) (Xpar D) r ρ c u‖
      ≤ Kmain * Rpar D ^ 3 := by
    have hstep : ∀ r ∈ Rset N (Rpar D), (r : ℝ)⁻¹
        * ‖∫ u : ℝ, ectrInt χ (z1par D) (z2par D) (Xpar D) r ρ c u‖
        ≤ (r : ℝ)⁻¹ * (Kmain * (r : ℝ) ^ 3) := by
      intro r hrs
      obtain ⟨-, hrsf, -⟩ := mem_Rset.mp hrs
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact norm_integral_ectrInt_le χ hD1 hLD hc hc1 hc2 hDN hrsf
    refine (Finset.sum_le_sum hstep).trans ?_
    have hfac : ∑ r ∈ Rset N (Rpar D), (r : ℝ)⁻¹ * (Kmain * (r : ℝ) ^ 3)
        = Kmain * ∑ r ∈ Rset N (Rpar D), (r : ℝ)⁻¹ * (r : ℝ) ^ 3 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [hfac]
    exact mul_le_mul_of_nonneg_left (sum_inv_mul_cube_le N hR1) hKmain0
  -- from the definition of `E_ctr`
  have hEnorm : ‖Ectr χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖ ≤ Kmain * Rpar D ^ 3 := by
    have hπ : (0 : ℝ) < 2 * π := by positivity
    have h2π : (1 : ℝ) / (2 * π) ≤ 1 := by
      rw [div_le_one hπ]
      nlinarith [Real.pi_gt_three]
    have hsplit : ‖Ectr χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖
        = (1 / (2 * π)) * ‖∑ r ∈ Rset N (Rpar D), ((r : ℂ))⁻¹ *
            ∫ u : ℝ, ectrInt χ (z1par D) (z2par D) (Xpar D) r ρ c u‖ := by
      rw [Ectr, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
    rw [hsplit]
    have hnrm : ‖∑ r ∈ Rset N (Rpar D), ((r : ℂ))⁻¹ *
        ∫ u : ℝ, ectrInt χ (z1par D) (z2par D) (Xpar D) r ρ c u‖
        ≤ ∑ r ∈ Rset N (Rpar D), (r : ℝ)⁻¹
          * ‖∫ u : ℝ, ectrInt χ (z1par D) (z2par D) (Xpar D) r ρ c u‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    have hRR : (0 : ℝ) ≤ Kmain * Rpar D ^ 3 := by positivity
    calc (1 / (2 * π)) * ‖∑ r ∈ Rset N (Rpar D), ((r : ℂ))⁻¹ *
            ∫ u : ℝ, ectrInt χ (z1par D) (z2par D) (Xpar D) r ρ c u‖
        ≤ (1 / (2 * π)) * (Kmain * Rpar D ^ 3) :=
          mul_le_mul_of_nonneg_left (hnrm.trans hsum) (by positivity)
      _ ≤ 1 * (Kmain * Rpar D ^ 3) := mul_le_mul_of_nonneg_right h2π hRR
      _ = Kmain * Rpar D ^ 3 := one_mul _
  refine hEnorm.trans ?_
  -- the exponent walk
  have hXc : Xpar D ^ c ≤ D ^ (-147/125 : ℝ) := by
    rw [Xpar, ← Real.rpow_mul hD0.le]
    exact Real.rpow_le_rpow_of_exponent_le hD1.le (by linarith)
  have hR3 : Rpar D ^ 3 = D ^ (3/100 : ℝ) := by
    rw [Rpar, ← Real.rpow_natCast (D ^ (1/100 : ℝ)) 3, ← Real.rpow_mul hD0.le]
    norm_num
  have hz2e : z2par D = D ^ (63/100 : ℝ) := rfl
  have hprod : D ^ (-147/125 : ℝ) * D ^ (397/800 : ℝ) * D ^ (63/100 : ℝ) * D ^ (3/100 : ℝ)
      = D ^ (-79/4000 : ℝ) := by
    rw [← Real.rpow_add hD0, ← Real.rpow_add hD0, ← Real.rpow_add hD0]
    norm_num
  have hnn : (0 : ℝ) ≤ (600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D) * D ^ (63/100 : ℝ)
      * (6432 * GammaStrip.CGamma) * D ^ (3/100 : ℝ) := by
    have : (0 : ℝ) ≤ D ^ (63/100 : ℝ) := Real.rpow_nonneg hD0.le _
    have h3 : (0 : ℝ) ≤ D ^ (3/100 : ℝ) := Real.rpow_nonneg hD0.le _
    positivity
  have hstep1 : Kmain * Rpar D ^ 3
      = Xpar D ^ c * ((600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D) * D ^ (63/100 : ℝ)
          * (6432 * GammaStrip.CGamma) * D ^ (3/100 : ℝ)) := by
    rw [hKmain, hR3, hz2e]; ring
  have hstep2 : Kmain * Rpar D ^ 3
      ≤ D ^ (-147/125 : ℝ) * ((600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D)
          * D ^ (63/100 : ℝ) * (6432 * GammaStrip.CGamma) * D ^ (3/100 : ℝ)) := by
    rw [hstep1]
    exact mul_le_mul_of_nonneg_right hXc hnn
  have hstep3 : D ^ (-147/125 : ℝ) * ((600000 * Ctau * D ^ (397/800 : ℝ) * Real.log D)
        * D ^ (63/100 : ℝ) * (6432 * GammaStrip.CGamma) * D ^ (3/100 : ℝ))
      = 20006092800000 * Ctau * Real.log D * D ^ (-79/4000 : ℝ) := by
    rw [GammaStrip.CGamma_def, ← hprod]; ring
  refine hstep2.trans (le_of_eq hstep3 |>.trans ?_)
  -- (T1)
  have hQ0 : (0 : ℝ) < D ^ (79/4000 : ℝ) := Real.rpow_pos_of_pos hD0 _
  have hneg : D ^ (-79/4000 : ℝ) = (D ^ (79/4000 : ℝ))⁻¹ := by
    rw [show (-79/4000 : ℝ) = -(79/4000 : ℝ) from by norm_num, Real.rpow_neg hD0.le]
  have hfin : 20006092800000 * Ctau * Real.log D * D ^ (-79/4000 : ℝ) ≤ 1/8 := by
    rw [hneg]
    have hs : 20006092800000 * Ctau * Real.log D ≤ (D ^ (79/4000 : ℝ)) / 8 := by
      nlinarith [hT1, hlog0, mul_nonneg hCt.le hlog0]
    calc 20006092800000 * Ctau * Real.log D * (D ^ (79/4000 : ℝ))⁻¹
        ≤ ((D ^ (79/4000 : ℝ)) / 8) * (D ^ (79/4000 : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right hs (by positivity)
      _ = 1/8 := by field_simp
  refine hfin.trans ?_
  have := one_le_P1 N hR1
  linarith

/-! ## §3.  Analyticity of the integrand, and the removable singularity at `w = 0`

The residue of `Γ(w)·X^w·L(ρ+w,χ)·M_r(ρ+w,χ)` at `w = 0` is
`L(ρ,χ)·M_r(ρ,χ) = 0` **because `ρ` is a zero of `L(·,χ)`**; equivalently, the
singularity is removable.  This is the detection mechanism of blueprint
Lemma 4.1, and in Lean it is cleanest as: the `dslope`-regularised function
`Ĝ(w) = Γ(w+1)·(H(w)/w)` is holomorphic on `Re w > −1` and agrees with the
integrand off `w = 0`. -/

lemma differentiable_cpow_neg {a : ℕ} (ha : a ≠ 0) :
    Differentiable ℂ (fun s : ℂ => ((a : ℕ) : ℂ) ^ (-s)) := by
  have ha0 : ((a : ℕ) : ℂ) ≠ 0 := by exact_mod_cast ha
  exact fun s => (differentiableAt_id.neg).const_cpow (Or.inl ha0)

lemma differentiable_eulerT {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℕ) :
    Differentiable ℂ (fun s : ℂ => eulerT χ s t) := by
  unfold eulerT
  refine Differentiable.fun_finsetProd ?_
  intro p hp
  have hp0 : p ≠ 0 := (Nat.pos_of_mem_primeFactors hp).ne'
  exact (differentiable_const 1).add
    ((differentiable_const _).mul (differentiable_cpow_neg hp0))

lemma differentiable_Mr {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z1 z2 : ℝ)
    (r : ℕ) : Differentiable ℂ (fun s : ℂ => Mr χ z1 z2 r s) := by
  unfold Mr
  refine Differentiable.fun_sum ?_
  intro δ hδ
  have hδ0 : δ ≠ 0 := by
    have := (Finset.mem_Icc.mp hδ).1
    omega
  exact (((differentiable_const _).mul (differentiable_cpow_neg hδ0)).mul
    (differentiable_eulerT χ _))

/-- `H(w) = X^w·L(ρ+w,χ)·M_r(ρ+w,χ)`, the non-`Γ` part of the Mellin integrand. -/
noncomputable def Hfun {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 X : ℝ) (r : ℕ) (ρ : ℂ) (w : ℂ) : ℂ :=
  (X : ℂ) ^ w * DirichletCharacter.LFunction χ (ρ + w) * Mr χ z1 z2 r (ρ + w)

/-- The `dslope`-regularised integrand `Ĝ(w) = Γ(w+1)·(H(w) − H(0))/w`. -/
noncomputable def Ghat {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 X : ℝ) (r : ℕ) (ρ : ℂ) (w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * dslope (Hfun χ z1 z2 X r ρ) 0 w

/-- `H` is holomorphic wherever `L(ρ+w,χ)` is: everywhere for `χ ≠ 1`, off the
pole `ρ + w = 1` for `χ = χ₀` (Mathlib `DirichletCharacter.differentiableAt_LFunction`). -/
lemma differentiableAt_Hfun {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {X : ℝ} (hX : 0 < X) (z1 z2 : ℝ) (r : ℕ) (ρ : ℂ) {w : ℂ} (hw : ρ + w ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (Hfun χ z1 z2 X r ρ) w := by
  have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have h1 : DifferentiableAt ℂ (fun w : ℂ => (X : ℂ) ^ w) w :=
    differentiableAt_id.const_cpow (Or.inl hX0)
  have h2 : DifferentiableAt ℂ (fun w : ℂ => DirichletCharacter.LFunction χ (ρ + w)) w :=
    (DirichletCharacter.differentiableAt_LFunction χ (ρ + w) hw).comp w
      ((differentiableAt_const ρ).add differentiableAt_id)
  have h3 : DifferentiableAt ℂ (fun w : ℂ => Mr χ z1 z2 r (ρ + w)) w :=
    ((differentiable_Mr χ z1 z2 r) (ρ + w)).comp w
      ((differentiableAt_const ρ).add differentiableAt_id)
  exact (h1.mul h2).mul h3

lemma differentiable_Hfun {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {X : ℝ} (hX : 0 < X) (z1 z2 : ℝ) (r : ℕ) (ρ : ℂ) :
    Differentiable ℂ (Hfun χ z1 z2 X r ρ) :=
  fun _ => differentiableAt_Hfun χ hX z1 z2 r ρ (Or.inr hχ)

/-- The `dslope` at `0` is holomorphic wherever `H` is, provided `H` is holomorphic
near `0` (`ρ ≠ 1` when `χ = χ₀`). -/
lemma differentiableAt_dslope_Hfun {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {X : ℝ} (hX : 0 < X) (z1 z2 : ℝ) (r : ℕ) {ρ : ℂ} (hρ : ρ ≠ 1 ∨ χ ≠ 1)
    {w : ℂ} (hw : ρ + w ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (dslope (Hfun χ z1 z2 X r ρ) 0) w := by
  rcases eq_or_ne w 0 with rfl | hw0
  · set s : Set ℂ := {v | ρ + v ≠ 1 ∨ χ ≠ 1} with hs
    have hopen : IsOpen s := by
      rcases eq_or_ne χ 1 with hχ | hχ
      · have heq : s = {v : ℂ | ρ + v ≠ 1} := by ext v; simp [hs, hχ]
        rw [heq]
        exact isOpen_ne_fun (continuous_const.add continuous_id) continuous_const
      · have : s = Set.univ := by ext v; simp [hs, hχ]
        rw [this]; exact isOpen_univ
    have hmem : s ∈ nhds (0 : ℂ) := hopen.mem_nhds (by simpa [hs] using hρ)
    have h := (Complex.differentiableOn_dslope (f := Hfun χ z1 z2 X r ρ) (s := s) (c := 0)
      hmem).mpr (fun v hv => (differentiableAt_Hfun χ hX z1 z2 r ρ hv).differentiableWithinAt)
    exact h.differentiableAt hmem
  · exact (differentiableAt_dslope_of_ne hw0).mpr (differentiableAt_Hfun χ hX z1 z2 r ρ hw)

/-- `Ĝ` is holomorphic on the half-plane `Re w > −1` (the only `Γ(w+1)` poles are
at `w = −1, −2, …`), off the `L`-pole `ρ + w = 1` when `χ = χ₀`. -/
lemma differentiableAt_Ghat {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {X : ℝ} (hX : 0 < X) (z1 z2 : ℝ) (r : ℕ) {ρ : ℂ} (hρ : ρ ≠ 1 ∨ χ ≠ 1)
    {w : ℂ} (hw : -1 < w.re) (hw' : ρ + w ≠ 1 ∨ χ ≠ 1) :
    DifferentiableAt ℂ (Ghat χ z1 z2 X r ρ) w := by
  have hne : ∀ n : ℕ, w + 1 ≠ -n := by
    intro n hcontra
    have := congrArg Complex.re hcontra
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)) w :=
    (Complex.differentiableAt_Gamma _ hne).comp w (differentiableAt_id.add_const 1)
  exact hΓ.mul (differentiableAt_dslope_Hfun χ hX z1 z2 r hρ hw')

/-- Off `w = 0`, `Ĝ` **is** the Mellin integrand `Γ(w)·H(w)`. -/
lemma Ghat_eq_of_ne {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z1 z2 X : ℝ) (r : ℕ)
    {ρ : ℂ} (hρ : Hfun χ z1 z2 X r ρ 0 = 0) {w : ℂ} (hw : w ≠ 0) :
    Ghat χ z1 z2 X r ρ w = Complex.Gamma w * Hfun χ z1 z2 X r ρ w := by
  rw [Ghat, dslope_of_ne _ hw, slope_def_field, hρ, sub_zero, sub_zero,
    Complex.Gamma_add_one w hw]
  field_simp

/-- The value at the origin vanishes **because `ρ` is a zero of `L(·,χ)`**. -/
lemma Hfun_zero_of_LFunction_eq_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 X : ℝ) (r : ℕ) {ρ : ℂ} (hρ : DirichletCharacter.LFunction χ ρ = 0) :
    Hfun χ z1 z2 X r ρ 0 = 0 := by
  rw [Hfun, add_zero, hρ]
  simp


/-! ### The principal character: the pole at `w = 1 − ρ` and its regularisation

For `χ = χ₀`, `L(ρ+w,χ₀)` has a simple pole at `w₀ := 1 − ρ`, with
`(s−1)·L(s,χ₀)` entire (Mathlib `DirichletCharacter.LFunctionTrivChar₁`, value
`∏_{p∣N}(1−1/p) = φ(N)/N` at `s = 1`).  Put `H₁(w) := X^w·L₁(ρ+w)·M_r(ρ+w,χ₀)`
(entire) and `Ĝ₁(w) := Γ(w+1)·dslope H₁ 0 w` (holomorphic on `Re w > −1`).  Off
`{0, w₀}`, `Ĝ(w) = Γ(w)H(w) = Ĝ₁(w)/(w − w₀)`, so the rectangle integral of `Ĝ`
is `2πi·Ĝ₁(w₀)` by the Cauchy formula, and
`Ĝ₁(w₀) = Γ(1−ρ)·X^{1−ρ}·(φ(N)/N)·M_r(1,χ₀)` — the per-`r` summand of
`Detector.Epole`. -/

/-- `∏_{p ∣ N}(1 − 1/p) = φ(N)/N` in `ℂ`. -/
lemma prod_one_sub_inv_eq_totient_div (N : ℕ) [NeZero N] :
    ∏ p ∈ N.primeFactors, (1 - (p : ℂ)⁻¹) = (N.totient : ℂ) / N := by
  have h := Nat.totient_eq_mul_prod_factors N
  have h' : ((N.totient : ℚ) : ℂ)
      = (((N : ℚ) * ∏ p ∈ N.primeFactors, (1 - (p : ℚ)⁻¹) : ℚ) : ℂ) := by rw [h]
  push_cast at h'
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [h']
  field_simp

lemma LFunctionTrivChar₁_of_ne (N : ℕ) [NeZero N] {s : ℂ} (hs : s ≠ 1) :
    DirichletCharacter.LFunctionTrivChar₁ N s
      = (s - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) s := by
  simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs]

lemma LFunctionTrivChar₁_one (N : ℕ) [NeZero N] :
    DirichletCharacter.LFunctionTrivChar₁ N 1 = (N.totient : ℂ) / N := by
  simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_self]
  exact prod_one_sub_inv_eq_totient_div N

/-- `H₁(w) = X^w · L₁(ρ+w) · M_r(ρ+w, χ₀)`, with `L₁(s) = (s−1)·L(s,χ₀)` entire. -/
noncomputable def Hone (N : ℕ) [NeZero N] (z1 z2 X : ℝ) (r : ℕ) (ρ : ℂ) (w : ℂ) : ℂ :=
  (X : ℂ) ^ w * DirichletCharacter.LFunctionTrivChar₁ N (ρ + w)
    * Mr (1 : DirichletCharacter ℂ N) z1 z2 r (ρ + w)

/-- `Ĝ₁(w) = Γ(w+1)·(H₁(w) − H₁(0))/w`. -/
noncomputable def Gone (N : ℕ) [NeZero N] (z1 z2 X : ℝ) (r : ℕ) (ρ : ℂ) (w : ℂ) : ℂ :=
  Complex.Gamma (w + 1) * dslope (Hone N z1 z2 X r ρ) 0 w

lemma differentiable_Hone (N : ℕ) [NeZero N] (z1 z2 : ℝ) {X : ℝ} (hX : 0 < X) (r : ℕ)
    (ρ : ℂ) : Differentiable ℂ (Hone N z1 z2 X r ρ) := by
  have hX0 : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have h1 : Differentiable ℂ (fun w : ℂ => (X : ℂ) ^ w) := fun w =>
    differentiableAt_id.const_cpow (Or.inl hX0)
  have h2 : Differentiable ℂ (fun w : ℂ => DirichletCharacter.LFunctionTrivChar₁ N (ρ + w)) :=
    (DirichletCharacter.differentiable_LFunctionTrivChar₁ N).comp
      ((differentiable_const ρ).add (differentiable_id (𝕜 := ℂ)))
  have h3 : Differentiable ℂ (fun w : ℂ => Mr (1 : DirichletCharacter ℂ N) z1 z2 r (ρ + w)) :=
    (differentiable_Mr _ z1 z2 r).comp ((differentiable_const ρ).add (differentiable_id (𝕜 := ℂ)))
  exact (h1.mul h2).mul h3

lemma Hone_eq_of_ne (N : ℕ) [NeZero N] (z1 z2 X : ℝ) (r : ℕ) (ρ : ℂ) {w : ℂ}
    (hw : ρ + w ≠ 1) :
    Hone N z1 z2 X r ρ w = (ρ + w - 1) * Hfun (1 : DirichletCharacter ℂ N) z1 z2 X r ρ w := by
  rw [Hone, Hfun, LFunctionTrivChar₁_of_ne N hw]; ring

/-- `H₁(0) = (ρ−1)·L(ρ,χ₀)·M_r(ρ,χ₀) = 0` because `ρ` is a zero (and `ρ ≠ 1`). -/
lemma Hone_zero (N : ℕ) [NeZero N] (z1 z2 X : ℝ) (r : ℕ) {ρ : ℂ} (hρ : ρ ≠ 1)
    (hLρ : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) ρ = 0) :
    Hone N z1 z2 X r ρ 0 = 0 := by
  rw [Hone, add_zero, LFunctionTrivChar₁_of_ne N hρ, hLρ]; simp

/-- The value at the pole: `H₁(1−ρ) = X^{1−ρ}·(φ(N)/N)·M_r(1,χ₀)`. -/
lemma Hone_at_pole (N : ℕ) [NeZero N] (z1 z2 X : ℝ) (r : ℕ) (ρ : ℂ) :
    Hone N z1 z2 X r ρ (1 - ρ)
      = (X : ℂ) ^ ((1 : ℂ) - ρ) * ((N.totient : ℂ) / N)
          * Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1 := by
  rw [Hone, show ρ + (1 - ρ) = 1 from by ring, LFunctionTrivChar₁_one]

lemma differentiableAt_Gone (N : ℕ) [NeZero N] (z1 z2 : ℝ) {X : ℝ} (hX : 0 < X) (r : ℕ)
    (ρ : ℂ) {w : ℂ} (hw : -1 < w.re) : DifferentiableAt ℂ (Gone N z1 z2 X r ρ) w := by
  have hne : ∀ n : ℕ, w + 1 ≠ -n := by
    intro n hcontra
    have := congrArg Complex.re hcontra
    simp at this
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)) w :=
    (Complex.differentiableAt_Gamma _ hne).comp w (differentiableAt_id.add_const 1)
  have hd : Differentiable ℂ (dslope (Hone N z1 z2 X r ρ) 0) := by
    have h := (Complex.differentiableOn_dslope (f := Hone N z1 z2 X r ρ)
      (s := (Set.univ : Set ℂ)) (c := 0) Filter.univ_mem).mpr
        (differentiable_Hone N z1 z2 hX r ρ).differentiableOn
    intro v
    exact h.differentiableAt Filter.univ_mem
  exact hΓ.mul (hd w)

/-- Off `w = 0`, `Ĝ₁(w) = Γ(w)·H₁(w)`. -/
lemma Gone_eq_of_ne (N : ℕ) [NeZero N] (z1 z2 X : ℝ) (r : ℕ) {ρ : ℂ}
    (hH0 : Hone N z1 z2 X r ρ 0 = 0) {w : ℂ} (hw : w ≠ 0) :
    Gone N z1 z2 X r ρ w = Complex.Gamma w * Hone N z1 z2 X r ρ w := by
  rw [Gone, dslope_of_ne _ hw, slope_def_field, hH0, sub_zero, sub_zero,
    Complex.Gamma_add_one w hw]
  field_simp

/-! ## §4.  The anchor identity on the line `Re w = 3`

`∑_n a(n)ψ_r(n)χ(n)e^{−n/X}n^{−ρ} = (1/2πi)∫_{(3)} Γ(w)X^w L(ρ+w,χ)M_r(ρ+w,χ) dw`
(blueprint Lemma 4.1, the `Re w = 2` display; the anchor is taken at `Re w = 3`,
where the trivial Dirichlet-series bound and the `n^{−3}` weight make every
convergence estimate elementary). -/

lemma ofReal_div_cpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (w : ℂ) :
    ((a / b : ℝ) : ℂ) ^ w = (a : ℂ) ^ w / (b : ℂ) ^ w := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (div_pos ha hb).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast ha.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hb.ne'), ← Complex.exp_sub]
  congr 1
  rw [← Complex.ofReal_log (div_pos ha hb).le, ← Complex.ofReal_log ha.le,
    ← Complex.ofReal_log hb.le, Real.log_div ha.ne' hb.ne']
  push_cast
  ring

lemma ectrInt_eq_Gamma_mul_Hfun {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 X : ℝ) (r : ℕ) (ρ : ℂ) (c u : ℝ) :
    ectrInt χ z1 z2 X r ρ c u
      = Complex.Gamma ((c : ℂ) + (u : ℂ) * Complex.I)
        * Hfun χ z1 z2 X r ρ ((c : ℂ) + (u : ℂ) * Complex.I) := by
  rw [ectrInt, Hfun]; ring

/-- The `n`-th term of the Mellin-expanded detector sum on the anchor line. -/
noncomputable def Fterm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 X : ℝ) (r : ℕ) (ρ : ℂ) (n : ℕ) (u : ℝ) : ℂ :=
  ((bvA z1 z2 n * psi r n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-ρ)
    * (((n : ℝ) / X : ℝ) : ℂ) ^ (-((3 : ℂ) + (u : ℂ) * Complex.I))
    * Complex.Gamma ((3 : ℂ) + (u : ℂ) * Complex.I)

/-- The detector summand `a(n)ψ_r(n)χ(n)e^{−n/X}n^{−ρ}`. -/
noncomputable def Sterm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 X : ℝ) (r : ℕ) (ρ : ℂ) (n : ℕ) : ℂ :=
  ((bvA z1 z2 n * psi r n : ℝ) : ℂ) * χ n
    * ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) * (n : ℂ) ^ (-ρ)

lemma bvA_zero (z1 z2 : ℝ) : bvA z1 z2 0 = 0 := by simp [bvA]

lemma Fterm_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 X : ℝ) (r : ℕ) (ρ : ℂ) (u : ℝ) :
    Fterm χ z1 z2 X r ρ 0 u = 0 := by
  simp [Fterm, bvA_zero]

lemma Sterm_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 X : ℝ) (r : ℕ) (ρ : ℂ) :
    Sterm χ z1 z2 X r ρ 0 = 0 := by
  simp [Sterm, bvA_zero]

/-- Norm of the `n`-th Mellin term: `|a(n)ψ_r(n)|·n^{−β}·(n/X)^{−3}·‖Γ(3+iu)‖`. -/
lemma norm_Fterm_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2) (hX : 0 < X) {r : ℕ} (hr : r ≠ 0)
    {ρ : ℂ} (hβ : 0 ≤ ρ.re) (n : ℕ) (u : ℝ) :
    ‖Fterm χ z1 z2 X r ρ n u‖
      ≤ ((r : ℝ) * X ^ 3 * ((n : ℝ) ^ 2)⁻¹)
        * ‖Complex.Gamma ((3 : ℂ) + (u : ℂ) * Complex.I)‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Fterm, bvA_zero]
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Fterm, norm_mul, norm_mul, norm_mul, norm_mul]
  have h1 : ‖((bvA z1 z2 n * psi r n : ℝ) : ℂ)‖ ≤ (n : ℝ) * r := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_bvA_le hz1 hz12 n) (abs_psi_le hr n) (abs_nonneg _)
      (le_trans zero_le_one hn1)
  have h2 : ‖χ ((n : ℕ) : ZMod N)‖ ≤ 1 := χ.norm_le_one _
  have h3 : ‖((n : ℕ) : ℂ) ^ (-ρ)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by simp [hβ])
  have h4 : ‖(((n : ℝ) / X : ℝ) : ℂ) ^ (-((3 : ℂ) + (u : ℂ) * Complex.I))‖
      = X ^ 3 * ((n : ℝ) ^ 2)⁻¹ * (n : ℝ)⁻¹ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have hre : (-((3 : ℂ) + (u : ℂ) * Complex.I)).re = -3 := by simp
    rw [hre, Real.rpow_neg (by positivity), show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast, div_pow]
    field_simp
  have hnn : (0 : ℝ) ≤ (n : ℝ) * r := by positivity
  calc ‖((bvA z1 z2 n * psi r n : ℝ) : ℂ)‖ * ‖χ ((n : ℕ) : ZMod N)‖
        * ‖((n : ℕ) : ℂ) ^ (-ρ)‖
        * ‖(((n : ℝ) / X : ℝ) : ℂ) ^ (-((3 : ℂ) + (u : ℂ) * Complex.I))‖
        * ‖Complex.Gamma ((3 : ℂ) + (u : ℂ) * Complex.I)‖
      ≤ ((n : ℝ) * r) * 1 * 1 * (X ^ 3 * ((n : ℝ) ^ 2)⁻¹ * (n : ℝ)⁻¹)
        * ‖Complex.Gamma ((3 : ℂ) + (u : ℂ) * Complex.I)‖ := by
        rw [h4]
        gcongr
    _ = ((r : ℝ) * X ^ 3 * ((n : ℝ) ^ 2)⁻¹)
        * ‖Complex.Gamma ((3 : ℂ) + (u : ℂ) * Complex.I)‖ := by
        have hne : (n : ℝ) ≠ 0 := hn0.ne'
        field_simp

lemma integral_Gamma_cpow_line_three {y : ℝ} (hy : 0 < y) :
    ∫ u : ℝ, (y : ℂ) ^ (-((3 : ℂ) + (u : ℂ) * Complex.I))
        * Complex.Gamma ((3 : ℂ) + (u : ℂ) * Complex.I)
      = ((2 * π : ℝ) : ℂ) * ((Real.exp (-y) : ℝ) : ℂ) := by
  have h := integral_Gamma_cpow_line (c := 3) (by norm_num) (by norm_num) hy
  simpa only [Complex.ofReal_ofNat] using h

lemma continuous_Fterm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 : ℝ) {X : ℝ} (hX : 0 < X) (r : ℕ) (ρ : ℂ) (n : ℕ) :
    Continuous (fun u : ℝ => Fterm χ z1 z2 X r ρ n u) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [Fterm, bvA_zero] using continuous_const
  have hy : (0 : ℝ) < (n : ℝ) / X := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  have hyc : (((n : ℝ) / X : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hG : Continuous (fun u : ℝ => Complex.Gamma ((3 : ℂ) + (u : ℂ) * Complex.I)) := by
    have := continuous_Gamma_line' (c := 3) (by norm_num)
    simpa using this
  have hc : Continuous (fun u : ℝ =>
      (((n : ℝ) / X : ℝ) : ℂ) ^ (-((3 : ℂ) + (u : ℂ) * Complex.I))) := by
    have hinner : Continuous (fun u : ℝ => -((3 : ℂ) + (u : ℂ) * Complex.I)) := by fun_prop
    exact hinner.const_cpow (Or.inl hyc)
  unfold Fterm
  exact (((continuous_const.mul continuous_const).mul continuous_const).mul hc).mul hG

lemma integrable_Fterm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2) (hX : 0 < X) {r : ℕ} (hr : r ≠ 0)
    {ρ : ℂ} (hβ : 0 ≤ ρ.re) (n : ℕ) :
    Integrable (fun u : ℝ => Fterm χ z1 z2 X r ρ n u) := by
  have hΓ : Integrable (fun u : ℝ => ‖Complex.Gamma ((3 : ℂ) + (u : ℂ) * Complex.I)‖) := by
    have := (integrable_Gamma_line (c := 3) (by norm_num) le_rfl).norm
    simpa using this
  refine Integrable.mono' (hΓ.const_mul ((r : ℝ) * X ^ 3 * ((n : ℝ) ^ 2)⁻¹))
    (continuous_Fterm χ z1 z2 hX r ρ n).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  exact norm_Fterm_le χ hz1 hz12 hX hr hβ n u

lemma integral_Fterm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 : ℝ) {X : ℝ} (hX : 0 < X) (r : ℕ) (ρ : ℂ) {n : ℕ} (hn : 0 < n) :
    ∫ u : ℝ, Fterm χ z1 z2 X r ρ n u
      = ((2 * π : ℝ) : ℂ) * Sterm χ z1 z2 X r ρ n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hy : (0 : ℝ) < (n : ℝ) / X := by positivity
  set K : ℂ := ((bvA z1 z2 n * psi r n : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-ρ) with hK
  have hrw : ∀ u : ℝ, Fterm χ z1 z2 X r ρ n u
      = K * ((((n : ℝ) / X : ℝ) : ℂ) ^ (-((3 : ℂ) + (u : ℂ) * Complex.I))
        * Complex.Gamma ((3 : ℂ) + (u : ℂ) * Complex.I)) := by
    intro u; rw [Fterm, hK]; ring
  simp only [hrw]
  rw [integral_const_mul, integral_Gamma_cpow_line_three hy]
  rw [hK, Sterm]
  have hexp : ((Real.exp (-((n : ℝ) / X)) : ℝ) : ℂ)
      = ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) := by
    congr 2
    ring
  rw [hexp]
  ring

/-- Termwise: the Mellin term is `Γ(w)X^w` times the Dirichlet-series term. -/
lemma Fterm_eq_term {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 : ℝ) {X : ℝ} (hX : 0 < X) (r : ℕ) (ρ : ℂ) (u : ℝ) (n : ℕ) :
    Fterm χ z1 z2 X r ρ n u
      = (Complex.Gamma ((3 : ℂ) + (u : ℂ) * Complex.I)
          * (X : ℂ) ^ ((3 : ℂ) + (u : ℂ) * Complex.I))
        * LSeries.term (fun m => ((bvA z1 z2 m * psi r m : ℝ) : ℂ) * χ m)
            (ρ + ((3 : ℂ) + (u : ℂ) * Complex.I)) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Fterm_zero, LSeries.term_zero, mul_zero]
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hXc : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hpn : ∀ y : ℂ, (n : ℂ) ^ y ≠ 0 := fun y => by
    rw [Complex.cpow_def_of_ne_zero hnc]; exact Complex.exp_ne_zero _
  have hpX : ∀ y : ℂ, (X : ℂ) ^ y ≠ 0 := fun y => by
    rw [Complex.cpow_def_of_ne_zero hXc]; exact Complex.exp_ne_zero _
  have hsplit2 : (n : ℂ) ^ (ρ + ((3 : ℂ) + (u : ℂ) * Complex.I))
      = (n : ℂ) ^ ρ * (n : ℂ) ^ ((3 : ℂ) + (u : ℂ) * Complex.I) :=
    Complex.cpow_add _ _ hnc
  rw [LSeries.term_of_ne_zero (by omega : n ≠ 0), Fterm, ofReal_div_cpow hn0 hX,
    show (((n : ℕ) : ℝ) : ℂ) = ((n : ℕ) : ℂ) from by push_cast; ring,
    Complex.cpow_neg, Complex.cpow_neg, Complex.cpow_neg, hsplit2,
    div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_inv]
  ring

lemma tsum_Fterm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 ≤ z2) (hX : 0 < X)
    {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ : 0 ≤ ρ.re) (u : ℝ) :
    ∑' n : ℕ, Fterm χ z1 z2 X r ρ n u = ectrInt χ z1 z2 X r ρ 3 u := by
  simp only [Fterm_eq_term χ z1 z2 hX r ρ u]
  rw [tsum_mul_left]
  have hs : 1 < (ρ + ((3 : ℂ) + (u : ℂ) * Complex.I)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im]
    norm_num
    linarith
  have hL : ∑' n : ℕ, LSeries.term (fun m => ((bvA z1 z2 m * psi r m : ℝ) : ℂ) * χ m)
      (ρ + ((3 : ℂ) + (u : ℂ) * Complex.I)) n
      = χ.LFunction (ρ + ((3 : ℂ) + (u : ℂ) * Complex.I))
        * Mr χ z1 z2 r (ρ + ((3 : ℂ) + (u : ℂ) * Complex.I)) :=
    LSeries_bvA_psi_eq_LFunction_mul_Mr hr hz1 hz12 χ hs
  rw [hL, ectrInt]
  norm_num
  ring

/-- **Blueprint Lemma 4.1, anchor line.**  `∑_n a(n)ψ_r(n)χ(n)e^{−n/X}n^{−ρ}` equals
`(1/2πi)∫_{(3)} Γ(w)X^w L(ρ+w,χ)M_r(ρ+w,χ) dw`. -/
theorem anchor_identity {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2) (hX : 0 < X)
    {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ : 0 ≤ ρ.re) :
    ∑' n : ℕ, Sterm χ z1 z2 X r ρ n
      = (((1 / (2 * π) : ℝ)) : ℂ) * ∫ u : ℝ, ectrInt χ z1 z2 X r ρ 3 u := by
  have hr0 : r ≠ 0 := hr.ne_zero
  have hΓnorm : Integrable (fun u : ℝ => ‖Complex.Gamma ((3 : ℂ) + (u : ℂ) * Complex.I)‖) := by
    have := (integrable_Gamma_line (c := 3) (by norm_num) le_rfl).norm
    simpa using this
  set CG : ℝ := ∫ u : ℝ, ‖Complex.Gamma ((3 : ℂ) + (u : ℂ) * Complex.I)‖ with hCG
  have hCG0 : 0 ≤ CG := integral_nonneg fun u => norm_nonneg _
  -- summability of the integral norms
  have hbnd : ∀ n : ℕ, ∫ u : ℝ, ‖Fterm χ z1 z2 X r ρ n u‖
      ≤ ((r : ℝ) * X ^ 3 * ((n : ℝ) ^ 2)⁻¹) * CG := by
    intro n
    have hmaj : Integrable (fun u : ℝ => ((r : ℝ) * X ^ 3 * ((n : ℝ) ^ 2)⁻¹)
        * ‖Complex.Gamma ((3 : ℂ) + (u : ℂ) * Complex.I)‖) := hΓnorm.const_mul _
    calc ∫ u : ℝ, ‖Fterm χ z1 z2 X r ρ n u‖
        ≤ ∫ u : ℝ, ((r : ℝ) * X ^ 3 * ((n : ℝ) ^ 2)⁻¹)
            * ‖Complex.Gamma ((3 : ℂ) + (u : ℂ) * Complex.I)‖ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _) hmaj
            (Filter.Eventually.of_forall fun u => norm_Fterm_le χ hz1 hz12 hX hr0 hβ n u)
      _ = ((r : ℝ) * X ^ 3 * ((n : ℝ) ^ 2)⁻¹) * CG := integral_const_mul _ _
  have hsummable : Summable fun n : ℕ => ∫ u : ℝ, ‖Fterm χ z1 z2 X r ρ n u‖ := by
    refine Summable.of_nonneg_of_le
      (fun n => integral_nonneg fun u => norm_nonneg _) hbnd ?_
    have hb : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
      simpa using Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    have := (hb.mul_left ((r : ℝ) * X ^ 3)).mul_right CG
    refine this.congr fun n => ?_
    ring
  -- interchange
  have hswap : ∑' n : ℕ, (∫ u : ℝ, Fterm χ z1 z2 X r ρ n u)
      = ∫ u : ℝ, ∑' n : ℕ, Fterm χ z1 z2 X r ρ n u :=
    integral_tsum_of_summable_integral_norm
      (fun n => integrable_Fterm χ hz1 hz12 hX hr0 hβ n) hsummable
  have hinner : ∀ u : ℝ, ∑' n : ℕ, Fterm χ z1 z2 X r ρ n u = ectrInt χ z1 z2 X r ρ 3 u :=
    fun u => tsum_Fterm χ hz1 hz12.le hX hr hβ u
  simp only [hinner] at hswap
  -- evaluate each integral
  have hval : ∀ n : ℕ, (∫ u : ℝ, Fterm χ z1 z2 X r ρ n u)
      = ((2 * π : ℝ) : ℂ) * Sterm χ z1 z2 X r ρ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Fterm_zero, Sterm_zero]
    · exact integral_Fterm χ z1 z2 hX r ρ hn
  simp only [hval, tsum_mul_left] at hswap
  -- solve for the detector sum
  have hπ : (0 : ℝ) < 2 * π := by positivity
  have hne : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hπ.ne'
  rw [← hswap]
  rw [show (((1 / (2 * π) : ℝ)) : ℂ) = (((2 * π : ℝ) : ℂ))⁻¹ from by
    rw [Complex.ofReal_div, Complex.ofReal_one, one_div]]
  field_simp

/-! ## §5.  The contour shift `Re w = 3 → Re w = ε₂ − β`

The integrand `Ĝ` is holomorphic on `Re w > −1` off the `L`-pole (§3), decays
like `e^{−|Im w|}` by I8(b), and grows at most polynomially in `|Im w|` by I1; so
Cauchy–Goursat (`χ ≠ χ₀`) or the Cauchy formula (`χ = χ₀`, pole at `w = 1−ρ`
strictly inside) on the rectangle `[ε₂−β, 3] × [−T, T]` plus `T → ∞` moves the
line. -/

/-- Uniform polynomial bound for `L` on the half-strip `Re s ≥ 1/100`, at distance
`≥ 99/100` from the point `s = 1` (I1 for `Re s ≤ 2`, the trivial Dirichlet-series
bound above); every `χ mod N`. -/
lemma norm_LFunction_strip_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 99/100 ≤ ‖s - 1‖) (h1 : 1/100 ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖
      ≤ 600000 * 2 ^ N.primeFactors.card
        * (((N : ℝ) * (|s.im| + 2)) ^ (1/2 : ℝ) * Real.log ((N : ℝ) * (|s.im| + 3))) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  have ha : (0 : ℝ) ≤ |s.im| := abs_nonneg _
  have hb2 : (2 : ℝ) ≤ (N : ℝ) * (|s.im| + 2) := by nlinarith
  have hb3 : (3 : ℝ) ≤ (N : ℝ) * (|s.im| + 3) := by nlinarith
  have hlog1 : (1 : ℝ) ≤ Real.log ((N : ℝ) * (|s.im| + 3)) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    linarith
  have hpow1 : (1 : ℝ) ≤ ((N : ℝ) * (|s.im| + 2)) ^ (1/2 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (1/2 : ℝ) := (Real.one_rpow _).symm
      _ ≤ ((N : ℝ) * (|s.im| + 2)) ^ (1/2 : ℝ) :=
          Real.rpow_le_rpow zero_le_one (by linarith) (by norm_num)
  have hω1 : (1 : ℝ) ≤ (2 : ℝ) ^ N.primeFactors.card := one_le_pow₀ (by norm_num)
  have hP1 : (1 : ℝ) ≤ ((N : ℝ) * (|s.im| + 2)) ^ (1/2 : ℝ)
      * Real.log ((N : ℝ) * (|s.im| + 3)) := by nlinarith
  rcases le_or_gt s.re 2 with h | h
  · have hs1 : s ≠ 1 := by
      intro h; rw [h, sub_self, norm_zero] at hs; norm_num at hs
    refine (norm_LFunction_le_convexity_all χ (Or.inr hs1) (by linarith) h).trans ?_
    have hexp : max ((1 - s.re)/2) 0 ≤ (1/2 : ℝ) := by
      refine max_le ?_ (by norm_num)
      linarith
    have hmono : ((N : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
        ≤ ((N : ℝ) * (|s.im| + 2)) ^ (1/2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) hexp
    have hL0 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|s.im| + 3)) := by linarith
    have h0 : (0 : ℝ) ≤ ((N : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0) :=
      Real.rpow_nonneg (by linarith) _
    have hpole : 1 / ‖s - 1‖ ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]
      linarith
    have hin : ((N : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
        * Real.log ((N : ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖
        ≤ 3 * (((N : ℝ) * (|s.im| + 2)) ^ (1/2 : ℝ) * Real.log ((N : ℝ) * (|s.im| + 3))) := by
      have := mul_le_mul_of_nonneg_right hmono hL0
      linarith
    calc 200000 * (2 : ℝ) ^ N.primeFactors.card
          * (((N : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
            * Real.log ((N : ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖)
        ≤ 200000 * (2 : ℝ) ^ N.primeFactors.card
          * (3 * (((N : ℝ) * (|s.im| + 2)) ^ (1/2 : ℝ)
            * Real.log ((N : ℝ) * (|s.im| + 3)))) :=
          mul_le_mul_of_nonneg_left hin (by positivity)
      _ = 600000 * 2 ^ N.primeFactors.card
          * (((N : ℝ) * (|s.im| + 2)) ^ (1/2 : ℝ) * Real.log ((N : ℝ) * (|s.im| + 3))) := by
          ring
  · refine (norm_LFunction_le_of_one_lt_re χ (by linarith)).trans ?_
    have h1' : (1 : ℝ) / (s.re - 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    nlinarith

/-- The `H`-factor grows at most quadratically in `|Im w|` on the shift strip, at
distance `≥ 99/100` from the `L`-pole `ρ + w = 1`. -/
lemma norm_Hfun_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ}
    {w : ℂ} (hw1 : eps2 - ρ.re ≤ w.re) (hw2 : w.re ≤ 3) (hw3 : 99/100 ≤ ‖ρ + w - 1‖) :
    ‖Hfun χ z1 z2 X r ρ w‖
      ≤ (X ^ 3 * (600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|ρ.im| + 3)) ^ 2)
          * (z2 * (r : ℝ) ^ 3)) * (1 + |w.im|) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  have hX0 : (0 : ℝ) < X := by linarith
  have hv0 : (0 : ℝ) ≤ |w.im| := abs_nonneg _
  have hv1 : (1 : ℝ) ≤ 1 + |w.im| := by linarith
  have hγ0 : (0 : ℝ) ≤ |ρ.im| := abs_nonneg _
  set A0 : ℝ := (N : ℝ) * (|ρ.im| + 3) with hA0
  have hA3 : (3 : ℝ) ≤ A0 := by rw [hA0]; nlinarith
  have hA0' : (0 : ℝ) ≤ A0 := by linarith
  have hre : (ρ + w).re = ρ.re + w.re := by simp
  have him : (ρ + w).im = ρ.im + w.im := by simp
  have hlow : 1/100 ≤ (ρ + w).re := by rw [hre]; rw [eps2] at hw1; linarith
  -- the three factors
  have hXn : ‖(X : ℂ) ^ w‖ ≤ X ^ 3 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0,
      show (X : ℝ) ^ (3 : ℕ) = X ^ ((3 : ℕ) : ℝ) from (Real.rpow_natCast X 3).symm]
    exact Real.rpow_le_rpow_of_exponent_le hX1 (by exact_mod_cast hw2)
  have hMn : ‖Mr χ z1 z2 r (ρ + w)‖ ≤ z2 * (r : ℝ) ^ 3 :=
    norm_Mr_le hr hz1 hz12 χ (by linarith)
  have habs : |(ρ + w).im| ≤ |ρ.im| + |w.im| := by rw [him]; exact abs_add_le _ _
  have hbase2 : (N : ℝ) * (|(ρ + w).im| + 2) ≤ A0 * (1 + |w.im|) := by
    have h1 : (N : ℝ) * (|(ρ + w).im| + 2) ≤ (N : ℝ) * ((|ρ.im| + 3) * (1 + |w.im|)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      nlinarith
    rw [hA0]; linarith [h1]
  have hbase3 : (N : ℝ) * (|(ρ + w).im| + 3) ≤ A0 * (1 + |w.im|) := by
    have h1 : (N : ℝ) * (|(ρ + w).im| + 3) ≤ (N : ℝ) * ((|ρ.im| + 3) * (1 + |w.im|)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      nlinarith
    rw [hA0]; linarith [h1]
  have hA1 : (1 : ℝ) ≤ A0 * (1 + |w.im|) := by nlinarith
  have hpow : ((N : ℝ) * (|(ρ + w).im| + 2)) ^ (1/2 : ℝ) ≤ A0 * (1 + |w.im|) := by
    calc ((N : ℝ) * (|(ρ + w).im| + 2)) ^ (1/2 : ℝ)
        ≤ (A0 * (1 + |w.im|)) ^ (1/2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hbase2 (by norm_num)
      _ ≤ (A0 * (1 + |w.im|)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num)
      _ = A0 * (1 + |w.im|) := Real.rpow_one _
  have hlogb : Real.log ((N : ℝ) * (|(ρ + w).im| + 3)) ≤ A0 * (1 + |w.im|) := by
    have h1 : Real.log ((N : ℝ) * (|(ρ + w).im| + 3)) ≤ Real.log (A0 * (1 + |w.im|)) :=
      Real.log_le_log (by positivity) hbase3
    have h2 : Real.log (A0 * (1 + |w.im|)) ≤ A0 * (1 + |w.im|) - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    linarith
  have hLn : ‖DirichletCharacter.LFunction χ (ρ + w)‖
      ≤ 600000 * 2 ^ N.primeFactors.card * A0 ^ 2 * (1 + |w.im|) ^ 2 := by
    refine (norm_LFunction_strip_le χ hw3 hlow).trans ?_
    have hl0 : (0 : ℝ) ≤ Real.log ((N : ℝ) * (|(ρ + w).im| + 3)) := by
      refine Real.log_nonneg ?_
      nlinarith [abs_nonneg (ρ + w).im]
    have hprod : ((N : ℝ) * (|(ρ + w).im| + 2)) ^ (1/2 : ℝ)
        * Real.log ((N : ℝ) * (|(ρ + w).im| + 3)) ≤ A0 ^ 2 * (1 + |w.im|) ^ 2 := by
      calc ((N : ℝ) * (|(ρ + w).im| + 2)) ^ (1/2 : ℝ)
            * Real.log ((N : ℝ) * (|(ρ + w).im| + 3))
          ≤ (A0 * (1 + |w.im|)) * (A0 * (1 + |w.im|)) :=
            mul_le_mul hpow hlogb hl0 (by positivity)
        _ = A0 ^ 2 * (1 + |w.im|) ^ 2 := by ring
    calc 600000 * (2 : ℝ) ^ N.primeFactors.card
          * (((N : ℝ) * (|(ρ + w).im| + 2)) ^ (1/2 : ℝ)
            * Real.log ((N : ℝ) * (|(ρ + w).im| + 3)))
        ≤ 600000 * (2 : ℝ) ^ N.primeFactors.card * (A0 ^ 2 * (1 + |w.im|) ^ 2) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = 600000 * 2 ^ N.primeFactors.card * A0 ^ 2 * (1 + |w.im|) ^ 2 := by ring
  -- assemble
  have h1 : (0 : ℝ) ≤ X ^ 3 := by positivity
  have h2 : (0 : ℝ) ≤ 600000 * 2 ^ N.primeFactors.card * A0 ^ 2 * (1 + |w.im|) ^ 2 := by
    positivity
  have h3 : (0 : ℝ) ≤ z2 * (r : ℝ) ^ 3 := by
    have : (0 : ℝ) ≤ z2 := by linarith
    positivity
  rw [Hfun, norm_mul, norm_mul]
  calc ‖(X : ℂ) ^ w‖ * ‖DirichletCharacter.LFunction χ (ρ + w)‖ * ‖Mr χ z1 z2 r (ρ + w)‖
      ≤ X ^ 3 * (600000 * 2 ^ N.primeFactors.card * A0 ^ 2 * (1 + |w.im|) ^ 2)
        * (z2 * (r : ℝ) ^ 3) := by
        refine mul_le_mul (mul_le_mul hXn hLn (norm_nonneg _) h1) hMn (norm_nonneg _) ?_
        positivity
    _ = (X ^ 3 * (600000 * 2 ^ N.primeFactors.card * A0 ^ 2) * (z2 * (r : ℝ) ^ 3))
        * (1 + |w.im|) ^ 2 := by ring

/-- Pointwise bound on `Ĝ` in the shift strip: exponential decay (I8(b)) times the
polynomial growth of `H`. -/
lemma norm_Ghat_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ1 : ρ.re ≤ 1)
    (hLρ : DirichletCharacter.LFunction χ ρ = 0)
    {w : ℂ} (hw1 : eps2 - ρ.re ≤ w.re) (hw2 : w.re ≤ 3)
    (hn1 : 1/100 ≤ ‖w‖) (hn2 : 1/100 ≤ ‖w + 1‖) (hw3 : 99/100 ≤ ‖ρ + w - 1‖) :
    ‖Ghat χ z1 z2 X r ρ w‖
      ≤ (201 * GammaStrip.CGamma
          * (X ^ 3 * (600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|ρ.im| + 3)) ^ 2)
            * (z2 * (r : ℝ) ^ 3)))
        * ((1 + |w.im|) ^ 2 * Real.exp (-|w.im|)) := by
  have hwne : w ≠ 0 := by
    intro h
    rw [h] at hn1
    simp at hn1
    linarith
  have hre1 : -(101/100 : ℝ) ≤ w.re := by rw [eps2] at hw1; linarith
  have hΓ : ‖Complex.Gamma w‖ ≤ 201 * GammaStrip.CGamma * Real.exp (-|w.im|) :=
    GammaStrip.norm_Gamma_le_of_dist w hre1 hw2 hn1 hn2
  have hH := norm_Hfun_le χ hz1 hz12 hX1 hr hw1 hw2 hw3
  rw [Ghat_eq_of_ne χ z1 z2 X r (Hfun_zero_of_LFunction_eq_zero χ z1 z2 X r hLρ) hwne, norm_mul]
  have h1 : (0 : ℝ) ≤ 201 * GammaStrip.CGamma * Real.exp (-|w.im|) := by
    rw [GammaStrip.CGamma_def]; positivity
  have h2 : (0 : ℝ) ≤ X ^ 3 * (600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|ρ.im| + 3)) ^ 2)
      * (z2 * (r : ℝ) ^ 3) := by
    have hz20 : (0 : ℝ) ≤ z2 := by linarith
    have hX0 : (0 : ℝ) ≤ X := by linarith
    positivity
  calc ‖Complex.Gamma w‖ * ‖Hfun χ z1 z2 X r ρ w‖
      ≤ (201 * GammaStrip.CGamma * Real.exp (-|w.im|))
        * ((X ^ 3 * (600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|ρ.im| + 3)) ^ 2)
          * (z2 * (r : ℝ) ^ 3)) * (1 + |w.im|) ^ 2) := mul_le_mul hΓ hH (norm_nonneg _) h1
    _ = (201 * GammaStrip.CGamma
          * (X ^ 3 * (600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|ρ.im| + 3)) ^ 2)
            * (z2 * (r : ℝ) ^ 3)))
        * ((1 + |w.im|) ^ 2 * Real.exp (-|w.im|)) := by ring

lemma continuous_Ghat_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {X : ℝ} (hX : 0 < X) (z1 z2 : ℝ) (r : ℕ) {ρ : ℂ} (hρ : ρ ≠ 1 ∨ χ ≠ 1)
    {a : ℝ} (ha : -1 < a) (ha' : ρ.re + a ≠ 1) :
    Continuous (fun u : ℝ => Ghat χ z1 z2 X r ρ ((a : ℂ) + (u : ℂ) * Complex.I)) := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have hinner : Continuous (fun u : ℝ => ((a : ℂ) + (u : ℂ) * Complex.I)) := by fun_prop
  have hre : (((a : ℂ) + (u : ℂ) * Complex.I)).re = a := by simp
  have hne : ρ + ((a : ℂ) + (u : ℂ) * Complex.I) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, hre, Complex.one_re] at this
    exact ha' this
  exact ContinuousAt.comp (f := fun u : ℝ => ((a : ℂ) + (u : ℂ) * Complex.I))
    (differentiableAt_Ghat χ hX z1 z2 r hρ (by rw [hre]; exact ha) (Or.inl hne)).continuousAt
    hinner.continuousAt

/-- `Ĝ` is integrable on any vertical line of the shift strip away from `{0, −1}`
and at distance `≥ 99/100` from the `L`-pole. -/
lemma integrable_Ghat_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ1 : ρ.re ≤ 1)
    (hρ : ρ ≠ 1 ∨ χ ≠ 1) (hLρ : DirichletCharacter.LFunction χ ρ = 0)
    {a : ℝ} (ha1 : eps2 - ρ.re ≤ a) (ha2 : a ≤ 3) (ha3 : 1/100 ≤ |a|) (ha4 : 1/100 ≤ |a + 1|)
    (ha5 : 99/100 ≤ |ρ.re + a - 1|) :
    Integrable (fun u : ℝ => Ghat χ z1 z2 X r ρ ((a : ℂ) + (u : ℂ) * Complex.I)) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hane : -1 < a := by rw [eps2] at ha1; linarith
  have ha' : ρ.re + a ≠ 1 := by
    intro h; rw [h, sub_self, abs_zero] at ha5; norm_num at ha5
  have hre1 : -(101/100 : ℝ) ≤ a := by linarith
  have hGint := GammaStrip.integrable_norm_Gamma_line hre1 ha2 ha3 ha4
  set CH : ℝ := X ^ 3 * (600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|ρ.im| + 3)) ^ 2)
    * (z2 * (r : ℝ) ^ 3) with hCH
  refine Integrable.mono' (hGint.const_mul CH)
    (continuous_Ghat_line χ hX0 z1 z2 r hρ hane ha').aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  have hre : (((a : ℂ) + (u : ℂ) * Complex.I)).re = a := by simp
  have him : (((a : ℂ) + (u : ℂ) * Complex.I)).im = u := by simp
  have hwne : ((a : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    rw [this] at ha3
    simp at ha3
    linarith
  have hw3 : 99/100 ≤ ‖ρ + ((a : ℂ) + (u : ℂ) * Complex.I) - 1‖ := by
    have := Complex.abs_re_le_norm (ρ + ((a : ℂ) + (u : ℂ) * Complex.I) - 1)
    simp only [Complex.sub_re, Complex.add_re, hre, Complex.one_re] at this
    linarith
  rw [Ghat_eq_of_ne χ z1 z2 X r (Hfun_zero_of_LFunction_eq_zero χ z1 z2 X r hLρ) hwne, norm_mul]
  have hH := norm_Hfun_le χ hz1 hz12 hX1 hr (w := (a : ℂ) + (u : ℂ) * Complex.I)
    (by rw [hre]; exact ha1) (by rw [hre]; exact ha2) hw3
  rw [him] at hH
  have hG0 : (0 : ℝ) ≤ ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)‖ := norm_nonneg _
  calc ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)‖
        * ‖Hfun χ z1 z2 X r ρ ((a : ℂ) + (u : ℂ) * Complex.I)‖
      ≤ ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)‖ * (CH * (1 + |u|) ^ 2) :=
        mul_le_mul_of_nonneg_left hH hG0
    _ = CH * (‖Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)‖ * (1 + |u|) ^ 2) := by ring

/-! ### Rectangle toolkit: the Cauchy formula for a locally holomorphic numerator,
and the generic line shift with a residue -/

/-- **Cauchy integral formula on a rectangle** for a numerator holomorphic on the
closed rectangle (extends `PerronKernel.rectInt_cauchy`, which asks for an entire
numerator): `∮ f(s)/(s − p) ds = 2πi·f(p)` when `p` is strictly inside. -/
theorem rectInt_cauchy_on {f : ℂ → ℂ} {z w p : ℂ}
    (hf : ∀ x ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im, DifferentiableAt ℂ f x)
    (h1 : z.re < p.re) (h2 : p.re < w.re) (h3 : z.im < p.im) (h4 : p.im < w.im) :
    rectInt (fun s => f s / (s - p)) z w = 2 * π * Complex.I * f p := by
  have hpf : p ∉ rectFrame z w := notMem_rectFrame h1 h2 h3 h4
  have hne : ∀ s ∈ rectFrame z w, s ≠ p := fun s hs h => hpf (h ▸ hs)
  have hrect_nhds : (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) ∈ nhds p := by
    have hopen : IsOpen (Set.Ioo z.re w.re ×ℂ Set.Ioo z.im w.im) :=
      isOpen_Ioo.reProdIm isOpen_Ioo
    refine Filter.mem_of_superset (hopen.mem_nhds ?_) ?_
    · exact Complex.mem_reProdIm.mpr ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    · intro x hx
      rw [Complex.mem_reProdIm] at hx ⊢
      rw [Set.uIcc_of_le (h1.le.trans h2.le), Set.uIcc_of_le (h3.le.trans h4.le)]
      exact ⟨Set.Ioo_subset_Icc_self hx.1, Set.Ioo_subset_Icc_self hx.2⟩
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
  have hpmem : p ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im := mem_of_mem_nhds hrect_nhds
  have cont2full : ContinuousOn (dslope f p) (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    rw [continuousOn_dslope hrect_nhds]
    exact ⟨fun x hx => (hf x hx).continuousAt.continuousWithinAt, hf p hpmem⟩
  have cont2 : ContinuousOn (dslope f p) (rectFrame z w) :=
    cont2full.mono (rectFrame_subset z w)
  have hds0 : rectInt (dslope f p) z w = 0 := by
    apply rectInt_eq_zero {p} (Set.countable_singleton p)
    · exact cont2full
    · intro x hx
      have hxp : x ≠ p := by
        intro h
        exact hx.2 (h ▸ rfl)
      have hxmem : x ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im := by
        have hx1 := hx.1
        rw [Complex.mem_reProdIm] at hx1 ⊢
        rw [min_eq_left (h1.le.trans h2.le), max_eq_right (h1.le.trans h2.le),
          min_eq_left (h3.le.trans h4.le), max_eq_right (h3.le.trans h4.le)] at hx1
        rw [Set.uIcc_of_le (h1.le.trans h2.le), Set.uIcc_of_le (h3.le.trans h4.le)]
        exact ⟨Set.Ioo_subset_Icc_self hx1.1, Set.Ioo_subset_Icc_self hx1.2⟩
      exact (differentiableAt_dslope_of_ne hxp).mpr (hf x hxmem)
  rw [rectInt_congr key, rectInt_add cont1 cont2, hds0, add_zero,
    rectInt_const_mul, rectInt_inv_sub_pole h1 h2 h3 h4]
  ring

/-- The rectangle boundary integral in coordinates. -/
lemma rectInt_coord (f : ℂ → ℂ) (a b T₁ T₂ : ℝ) :
    rectInt f ((a : ℂ) + (T₁ : ℂ) * Complex.I) ((b : ℂ) + (T₂ : ℂ) * Complex.I)
      = (∫ x : ℝ in a..b, f ((x : ℂ) + (T₁ : ℂ) * Complex.I))
        - (∫ x : ℝ in a..b, f ((x : ℂ) + (T₂ : ℂ) * Complex.I))
        + Complex.I • (∫ y : ℝ in T₁..T₂, f ((b : ℂ) + (y : ℂ) * Complex.I))
        - Complex.I • (∫ y : ℝ in T₁..T₂, f ((a : ℂ) + (y : ℂ) * Complex.I)) := by
  simp [rectInt]

open Filter Topology in
/-- **Generic line shift with a residue.**  If the rectangle boundary integrals of
`f` over `[a, b] × [−T, T]` equal the constant `K` for all `T ≥ T₀`, `f` is
integrable on both edge lines, and the horizontal-edge integrals vanish in the
limit, then `∫_{(b)} f du − ∫_{(a)} f du = −i·K`. -/
theorem shift_lines_residue {f : ℂ → ℂ} {a b T₀ : ℝ} {K : ℂ}
    (hrect : ∀ T : ℝ, T₀ ≤ T →
      rectInt f ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        ((b : ℂ) + ((T : ℝ) : ℂ) * Complex.I) = K)
    (hia : Integrable (fun u : ℝ => f ((a : ℂ) + (u : ℂ) * Complex.I)))
    (hib : Integrable (fun u : ℝ => f ((b : ℂ) + (u : ℂ) * Complex.I)))
    (htop : Tendsto (fun T : ℝ => ∫ x in a..b, f ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
      atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in a..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      atTop (𝓝 0)) :
    (∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * Complex.I))
      - (∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * Complex.I)) = -Complex.I * K := by
  have hrect' : ∀ T : ℝ, T₀ ≤ T →
      (∫ x in a..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        - (∫ x in a..b, f ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        + Complex.I • (∫ y in (-T)..T, f ((b : ℂ) + (y : ℂ) * Complex.I))
        - Complex.I • (∫ y in (-T)..T, f ((a : ℂ) + (y : ℂ) * Complex.I)) = K := by
    intro T hT
    have h := hrect T hT
    rwa [rectInt_coord] at h
  have hL : Tendsto (fun T : ℝ => ∫ y in (-T)..T, f ((a : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 (∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral hia tendsto_neg_atTop_atBot tendsto_id
  have hR : Tendsto (fun T : ℝ => ∫ y in (-T)..T, f ((b : ℂ) + (y : ℂ) * Complex.I))
      atTop (𝓝 (∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral hib tendsto_neg_atTop_atBot tendsto_id
  have hcomb : Tendsto (fun T : ℝ =>
      (∫ x in a..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
        - (∫ x in a..b, f ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        + Complex.I • (∫ y in (-T)..T, f ((b : ℂ) + (y : ℂ) * Complex.I))
        - Complex.I • (∫ y in (-T)..T, f ((a : ℂ) + (y : ℂ) * Complex.I)))
      atTop (𝓝 (0 - 0 + Complex.I • (∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * Complex.I))
        - Complex.I • (∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * Complex.I)))) :=
    ((hbot.sub htop).add (hR.const_smul Complex.I)).sub (hL.const_smul Complex.I)
  have hconst : Tendsto (fun _ : ℝ => K) atTop (𝓝 K) := tendsto_const_nhds
  have hlim := tendsto_nhds_unique
    (hcomb.congr' (by filter_upwards [eventually_ge_atTop T₀] with T hT using hrect' T hT))
    hconst
  simp only [smul_eq_mul, sub_zero] at hlim
  set R := ∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * Complex.I)
  set L := ∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * Complex.I)
  have hIK : Complex.I * (R - L) = K := by rw [mul_sub]; linear_combination hlim
  calc R - L = -Complex.I * (Complex.I * (R - L)) := by
        rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    _ = -Complex.I * K := by rw [hIK]

open Filter Topology in
/-- **Generic line shift** (no pole).  If `f` is holomorphic on the closed strip
`a ≤ Re w ≤ b`, integrable on both edge lines, and its horizontal-edge integrals
vanish in the limit, then the two line integrals agree. -/
theorem shift_lines {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hdiff : ∀ w : ℂ, a ≤ w.re → w.re ≤ b → DifferentiableAt ℂ f w)
    (hia : Integrable (fun u : ℝ => f ((a : ℂ) + (u : ℂ) * Complex.I)))
    (hib : Integrable (fun u : ℝ => f ((b : ℂ) + (u : ℂ) * Complex.I)))
    (htop : Tendsto (fun T : ℝ => ∫ x in a..b, f ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
      atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in a..b, f ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      atTop (𝓝 0)) :
    ∫ u : ℝ, f ((a : ℂ) + (u : ℂ) * Complex.I)
      = ∫ u : ℝ, f ((b : ℂ) + (u : ℂ) * Complex.I) := by
  -- the rectangle identity at every height `T`
  have hrect : ∀ T : ℝ, (0 : ℝ) ≤ T →
      rectInt f ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        ((b : ℂ) + ((T : ℝ) : ℂ) * Complex.I) = 0 := by
    intro T _
    set z : ℂ := (a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I with hz
    set w : ℂ := (b : ℂ) + ((T : ℝ) : ℂ) * Complex.I with hw
    have hzre : z.re = a := by rw [hz]; simp
    have hwre : w.re = b := by rw [hw]; simp
    have hmemre : ∀ x : ℂ, x.re ∈ Set.uIcc a b → a ≤ x.re ∧ x.re ≤ b := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ⟨hx.1, hx.2⟩
    refine rectInt_eq_zero ∅ Set.countable_empty ?_ ?_
    · intro x hx
      rw [hzre, hwre] at hx
      have hx' := (Complex.mem_reProdIm.mp hx).1
      obtain ⟨h1, h2⟩ := hmemre x hx'
      exact (hdiff x h1 h2).continuousAt.continuousWithinAt
    · intro x hx
      have hx1 := (Complex.mem_reProdIm.mp hx.1).1
      rw [hzre, hwre, min_eq_left hab, max_eq_right hab] at hx1
      exact hdiff x hx1.1.le hx1.2.le
  have h := shift_lines_residue hrect hia hib htop hbot
  rw [mul_zero, sub_eq_zero] at h
  exact h.symm

open Filter Topology in
/-- `(1+T)²e^{−T} → 0`. -/
lemma tendsto_one_add_sq_mul_exp_neg :
    Tendsto (fun T : ℝ => (1 + T) ^ 2 * Real.exp (-T)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have hshift : Tendsto (fun T : ℝ => 1 + T) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 tendsto_id
  have hcomp : Tendsto (fun T : ℝ => (1 + T) ^ 2 * Real.exp (-(1 + T))) atTop (𝓝 0) :=
    hbase.comp hshift
  have hmul : Tendsto (fun T : ℝ => Real.exp 1 * ((1 + T) ^ 2 * Real.exp (-(1 + T))))
      atTop (𝓝 0) := by
    simpa using hcomp.const_mul (Real.exp 1)
  refine hmul.congr fun T => ?_
  have hexp : Real.exp 1 * Real.exp (-(1 + T)) = Real.exp (-T) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Real.exp 1 * ((1 + T) ^ 2 * Real.exp (-(1 + T)))
      = (1 + T) ^ 2 * (Real.exp 1 * Real.exp (-(1 + T))) := by ring
    _ = (1 + T) ^ 2 * Real.exp (-T) := by rw [hexp]

/-! ### The horizontal edges (all `χ`) -/

/-- Horizontal-edge bound for `Ĝ` at height `|v| = T ≥ |γ| + 1` (so that the edge
stays at distance `≥ 1` from both `w = 0` and the `L`-pole `w = 1 − ρ`). -/
lemma norm_integral_Ghat_horiz_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hLρ : DirichletCharacter.LFunction χ ρ = 0)
    {T : ℝ} (hT : |ρ.im| + 1 ≤ T) {v : ℝ} (hv : v = T ∨ v = -T) :
    ‖∫ x in (eps2 - ρ.re)..(3 : ℝ), Ghat χ z1 z2 X r ρ ((x : ℂ) + (v : ℂ) * Complex.I)‖
      ≤ ((201 * GammaStrip.CGamma
          * (X ^ 3 * (600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|ρ.im| + 3)) ^ 2)
            * (z2 * (r : ℝ) ^ 3))) * ((1 + T) ^ 2 * Real.exp (-T)))
        * |(3 : ℝ) - (eps2 - ρ.re)| := by
  have hab : eps2 - ρ.re ≤ (3 : ℝ) := by rw [eps2]; linarith
  have hT1 : 1 ≤ T := by linarith [abs_nonneg ρ.im]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Set.uIoc_of_le hab] at hx
  have hxre : ((x : ℂ) + (v : ℂ) * Complex.I).re = x := by simp
  have hxim : ((x : ℂ) + (v : ℂ) * Complex.I).im = v := by simp
  have habsv : |v| = T := by
    rcases hv with rfl | rfl
    · exact abs_of_nonneg (by linarith)
    · rw [abs_neg]; exact abs_of_nonneg (by linarith)
  have hnorm1 : (1 : ℝ) ≤ ‖(x : ℂ) + (v : ℂ) * Complex.I‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) + (v : ℂ) * Complex.I)
    rw [hxim, habsv] at this
    linarith
  have hnorm2 : (1 : ℝ) ≤ ‖((x : ℂ) + (v : ℂ) * Complex.I) + 1‖ := by
    have := Complex.abs_im_le_norm (((x : ℂ) + (v : ℂ) * Complex.I) + 1)
    simp only [Complex.add_im, Complex.one_im, add_zero, hxim] at this
    rw [habsv] at this
    linarith
  have hw3 : 99/100 ≤ ‖ρ + ((x : ℂ) + (v : ℂ) * Complex.I) - 1‖ := by
    have hle := Complex.abs_im_le_norm (ρ + ((x : ℂ) + (v : ℂ) * Complex.I) - 1)
    simp only [Complex.sub_im, Complex.add_im, hxim, Complex.one_im, sub_zero] at hle
    have h := abs_sub_abs_le_abs_sub v (-ρ.im)
    rw [abs_neg, sub_neg_eq_add, habsv] at h
    have h3 : |ρ.im + v| = |v + ρ.im| := by rw [add_comm]
    linarith
  have hbd := norm_Ghat_le χ hz1 hz12 hX1 hr hβ1 hLρ
    (w := (x : ℂ) + (v : ℂ) * Complex.I)
    (by rw [hxre]; exact hx.1.le) (by rw [hxre]; exact hx.2)
    (by linarith) (by linarith) hw3
  rw [hxim, habsv] at hbd
  exact hbd

open Filter Topology in
/-- The horizontal edges vanish as `T → ∞` (I8(b) against polynomial growth). -/
lemma tendsto_Ghat_horiz {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hLρ : DirichletCharacter.LFunction χ ρ = 0) :
    Tendsto (fun T : ℝ => ∫ x in (eps2 - ρ.re)..(3 : ℝ),
        Ghat χ z1 z2 X r ρ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0)
    ∧ Tendsto (fun T : ℝ => ∫ x in (eps2 - ρ.re)..(3 : ℝ),
        Ghat χ z1 z2 X r ρ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
  set KK : ℝ := 201 * GammaStrip.CGamma
      * (X ^ 3 * (600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|ρ.im| + 3)) ^ 2)
        * (z2 * (r : ℝ) ^ 3)) with hKK
  have hlim0 : Tendsto (fun T : ℝ => (KK * ((1 + T) ^ 2 * Real.exp (-T)))
      * |(3 : ℝ) - (eps2 - ρ.re)|) atTop (𝓝 0) := by
    have := (tendsto_one_add_sq_mul_exp_neg.const_mul KK).mul_const |(3 : ℝ) - (eps2 - ρ.re)|
    simpa using this
  constructor
  · refine squeeze_zero_norm' ?_ hlim0
    filter_upwards [eventually_ge_atTop (|ρ.im| + 1)] with T hT
    exact norm_integral_Ghat_horiz_le χ hz1 hz12 hX1 hr hβ hβ1 hLρ hT (Or.inl rfl)
  · refine squeeze_zero_norm' ?_ hlim0
    filter_upwards [eventually_ge_atTop (|ρ.im| + 1)] with T hT
    exact norm_integral_Ghat_horiz_le χ hz1 hz12 hX1 hr hβ hβ1 hLρ hT (Or.inr rfl)

/-! ### The two rectangle identities and the shifts -/

/-- **The rectangle identity for `χ₀`**: the boundary integral of `Ĝ` over
`[ε₂−β, 3] × [−T, T]`, `T ≥ |γ|+1`, is `2πi` times the residue at `w = 1−ρ`,
`Γ(1−ρ)·X^{1−ρ}·(φ(N)/N)·M_r(1,χ₀)`. -/
theorem rectInt_Ghat_principal {N : ℕ} [NeZero N] (z1 z2 : ℝ) {X : ℝ} (hX : 0 < X) (r : ℕ)
    {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) (hρ1 : ρ ≠ 1)
    (hLρ : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) ρ = 0)
    {T : ℝ} (hT : |ρ.im| + 1 ≤ T) :
    rectInt (Ghat (1 : DirichletCharacter ℂ N) z1 z2 X r ρ)
        (((eps2 - ρ.re : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        (((3 : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
      = 2 * π * Complex.I * (Complex.Gamma (1 - ρ) * (X : ℂ) ^ ((1 : ℂ) - ρ)
          * ((N.totient : ℂ) / N) * Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1) := by
  set c : ℝ := eps2 - ρ.re with hcdef
  have hc1 : -(99/100 : ℝ) ≤ c := by rw [hcdef, eps2]; linarith [hβ1]
  have hc2 : c ≤ -(98/100 : ℝ) := by rw [hcdef, eps2]; linarith [hβ]
  set z : ℂ := (c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I with hz
  set w : ℂ := ((3 : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I with hw
  set p : ℂ := 1 - ρ with hp
  have hzre : z.re = c := by rw [hz]; simp
  have hzim : z.im = -T := by rw [hz]; simp
  have hwre : w.re = 3 := by rw [hw]; simp
  have hwim : w.im = T := by rw [hw]; simp
  have hpre : p.re = 1 - ρ.re := by rw [hp]; simp
  have hpim : p.im = -ρ.im := by rw [hp]; simp
  have hγ : |ρ.im| < T := by linarith
  have h1 : z.re < p.re := by rw [hzre, hpre]; linarith
  have h2 : p.re < w.re := by rw [hpre, hwre]; linarith
  have h3 : z.im < p.im := by rw [hzim, hpim]; linarith [le_abs_self ρ.im]
  have h4 : p.im < w.im := by rw [hpim, hwim]; linarith [neg_le_abs ρ.im]
  have h1' : z.re < (0 : ℂ).re := by rw [hzre]; simp; linarith
  have h2' : (0 : ℂ).re < w.re := by rw [hwre]; simp
  have h3' : z.im < (0 : ℂ).im := by rw [hzim]; simp; linarith [abs_nonneg ρ.im]
  have h4' : (0 : ℂ).im < w.im := by rw [hwim]; simp; linarith [abs_nonneg ρ.im]
  have hp0 : p ∉ rectFrame z w := notMem_rectFrame h1 h2 h3 h4
  have h00 : (0 : ℂ) ∉ rectFrame z w := notMem_rectFrame h1' h2' h3' h4'
  have hH0 : Hfun (1 : DirichletCharacter ℂ N) z1 z2 X r ρ 0 = 0 :=
    Hfun_zero_of_LFunction_eq_zero _ z1 z2 X r hLρ
  have hH10 : Hone N z1 z2 X r ρ 0 = 0 := Hone_zero N z1 z2 X r hρ1 hLρ
  have hpne : p ≠ 0 := by
    intro h; apply hρ1; rw [hp] at h; linear_combination -h
  -- the integrands agree on the frame
  have key : ∀ s ∈ rectFrame z w, Ghat (1 : DirichletCharacter ℂ N) z1 z2 X r ρ s
      = Gone N z1 z2 X r ρ s / (s - p) := by
    intro s hs
    have hs0 : s ≠ 0 := fun h => h00 (h ▸ hs)
    have hsp : s ≠ p := fun h => hp0 (h ▸ hs)
    have hsp' : ρ + s ≠ 1 := by
      intro h; apply hsp; rw [hp]; linear_combination h
    have hspne : s - p ≠ 0 := sub_ne_zero.mpr hsp
    rw [Ghat_eq_of_ne _ z1 z2 X r hH0 hs0, Gone_eq_of_ne N z1 z2 X r hH10 hs0,
      Hone_eq_of_ne N z1 z2 X r ρ hsp', show ρ + s - 1 = s - p from by rw [hp]; ring]
    field_simp
  rw [rectInt_congr key]
  have hdiff : ∀ x ∈ Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im,
      DifferentiableAt ℂ (Gone N z1 z2 X r ρ) x := by
    intro x hx
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (h1.le.trans h2.le)] at hx
    have hxre : z.re ≤ x.re := hx.1.1
    rw [hzre] at hxre
    exact differentiableAt_Gone N z1 z2 hX r ρ (by linarith)
  rw [rectInt_cauchy_on hdiff h1 h2 h3 h4, Gone_eq_of_ne N z1 z2 X r hH10 hpne, hp,
    Hone_at_pole]
  ring

open Filter Topology in
/-- **The contour shift, `χ ≠ χ₀`** (blueprint Lemma 4.1): with the residue at
`w = 0` removed (it vanishes because `L(ρ,χ) = 0`) and no other pole in the
strip, the line `Re w = 3` may be moved to `Re w = ε₂ − β`. -/
theorem Ghat_line_shift {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hLρ : DirichletCharacter.LFunction χ ρ = 0) :
    ∫ u : ℝ, Ghat χ z1 z2 X r ρ (((eps2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * Complex.I)
      = ∫ u : ℝ, Ghat χ z1 z2 X r ρ (((3 : ℝ) : ℂ) + (u : ℂ) * Complex.I) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hc1 : -(99/100 : ℝ) ≤ eps2 - ρ.re := by rw [eps2]; linarith
  have hc2 : eps2 - ρ.re ≤ -(98/100 : ℝ) := by rw [eps2]; linarith
  have hab : eps2 - ρ.re ≤ (3 : ℝ) := by linarith
  obtain ⟨htop, hbot⟩ := tendsto_Ghat_horiz χ hz1 hz12 hX1 hr hβ hβ1 hLρ
  refine shift_lines hab ?_ ?_ ?_ htop hbot
  · intro w h1 _
    exact differentiableAt_Ghat χ hX0 z1 z2 r (Or.inr hχ) (by linarith) (Or.inr hχ)
  · exact integrable_Ghat_line χ hz1 hz12 hX1 hr hβ1 (Or.inr hχ) hLρ le_rfl hab
      (by rw [abs_of_nonpos (by linarith)]; linarith)
      (by rw [abs_of_nonneg (by linarith)]; linarith)
      (by rw [eps2, abs_of_nonpos (by linarith)]; linarith)
  · exact integrable_Ghat_line χ hz1 hz12 hX1 hr hβ1 (Or.inr hχ) hLρ hab le_rfl
      (by rw [abs_of_nonneg (by norm_num)]; norm_num)
      (by rw [abs_of_nonneg (by norm_num)]; norm_num)
      (by rw [abs_of_nonneg (by linarith)]; linarith)

open Filter Topology in
/-- **The contour shift, `χ = χ₀`** (blueprint Lemma 4.1): the residue at `w = 0`
is removed as before, and the pole of `L(ρ+w,χ₀)` at `w = 1−ρ` (strictly inside
the strip for `ρ ≠ 1`) contributes `2π·Γ(1−ρ)·X^{1−ρ}·(φ(N)/N)·M_r(1,χ₀)`. -/
theorem Ghat_line_shift_principal {N : ℕ} [NeZero N]
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hρ1 : ρ ≠ 1)
    (hLρ : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) ρ = 0) :
    ∫ u : ℝ, Ghat (1 : DirichletCharacter ℂ N) z1 z2 X r ρ
        (((3 : ℝ) : ℂ) + (u : ℂ) * Complex.I)
      = (∫ u : ℝ, Ghat (1 : DirichletCharacter ℂ N) z1 z2 X r ρ
          (((eps2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * Complex.I))
        + 2 * (π : ℂ) * (Complex.Gamma (1 - ρ) * (X : ℂ) ^ ((1 : ℂ) - ρ)
          * ((N.totient : ℂ) / N) * Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hc1 : -(99/100 : ℝ) ≤ eps2 - ρ.re := by rw [eps2]; linarith
  have hc2 : eps2 - ρ.re ≤ -(98/100 : ℝ) := by rw [eps2]; linarith
  have hab : eps2 - ρ.re ≤ (3 : ℝ) := by linarith
  obtain ⟨htop, hbot⟩ :=
    tendsto_Ghat_horiz (1 : DirichletCharacter ℂ N) hz1 hz12 hX1 hr hβ hβ1 hLρ
  set c₀ : ℂ := Complex.Gamma (1 - ρ) * (X : ℂ) ^ ((1 : ℂ) - ρ)
    * ((N.totient : ℂ) / N) * Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1 with hc₀
  have hrect : ∀ T : ℝ, |ρ.im| + 1 ≤ T →
      rectInt (Ghat (1 : DirichletCharacter ℂ N) z1 z2 X r ρ)
        (((eps2 - ρ.re : ℝ) : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        (((3 : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I) = 2 * π * Complex.I * c₀ :=
    fun T hT => rectInt_Ghat_principal z1 z2 hX0 r hβ hβ1 hρ1 hLρ hT
  have hia := integrable_Ghat_line (1 : DirichletCharacter ℂ N) hz1 hz12 hX1 hr hβ1
    (Or.inl hρ1) hLρ le_rfl hab
    (by rw [abs_of_nonpos (by linarith)]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith)
    (by rw [eps2, abs_of_nonpos (by linarith)]; linarith)
  have hib := integrable_Ghat_line (1 : DirichletCharacter ℂ N) hz1 hz12 hX1 hr hβ1
    (Or.inl hρ1) hLρ hab le_rfl
    (by rw [abs_of_nonneg (by norm_num)]; norm_num)
    (by rw [abs_of_nonneg (by norm_num)]; norm_num)
    (by rw [abs_of_nonneg (by linarith)]; linarith)
  have h := shift_lines_residue hrect hia hib htop hbot
  have hI : -Complex.I * (2 * π * Complex.I * c₀) = 2 * (π : ℂ) * c₀ := by
    linear_combination (-(2 * (π : ℂ) * c₀)) * Complex.I_mul_I
  rw [hI] at h
  linear_combination h

/-! ## §6.  Assembly: blueprint Lemma 4.1 and `DetectionEstimate` -/

set_option maxHeartbeats 4000000 in
lemma summable_Sterm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2) (hX : 0 < X)
    {r : ℕ} (hr : r ≠ 0) {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    Summable (fun n : ℕ => Sterm χ z1 z2 X r ρ n) := by
  have hq1 : |Real.exp (-1 / X)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff, neg_div]
    have h0 : (0 : ℝ) < 1 / X := one_div_pos.mpr hX
    linarith
  have hsum : Summable (fun n : ℕ => (r : ℝ) * ((n : ℝ) ^ (1 : ℕ)
      * Real.exp (-1 / X) ^ n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_eq_abs])).mul_left _
  refine Summable.of_norm_bounded hsum ?_
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Sterm_zero, norm_zero]
    simp
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [Sterm, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_real, Real.norm_eq_abs]
  have h1 : |bvA z1 z2 n * psi r n| ≤ (n : ℝ) * r := by
    rw [abs_mul]
    exact mul_le_mul (abs_bvA_le hz1 hz12 n) (abs_psi_le hr n) (abs_nonneg _)
      (by linarith)
  have h2 : ‖χ ((n : ℕ) : ZMod N)‖ ≤ 1 := χ.norm_le_one _
  have h3 : ‖((n : ℕ) : ℂ) ^ (-ρ)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hn]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1 (by simp [hρ])
  have hexp : |Real.exp (-(n : ℝ) / X)| = Real.exp (-1 / X) ^ n := by
    rw [abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [hexp]
  have hE0 : (0 : ℝ) ≤ Real.exp (-1 / X) ^ n := pow_nonneg (Real.exp_pos _).le n
  calc |bvA z1 z2 n * psi r n| * ‖χ ((n : ℕ) : ZMod N)‖ * Real.exp (-1 / X) ^ n
        * ‖((n : ℕ) : ℂ) ^ (-ρ)‖
      ≤ ((n : ℝ) * r) * 1 * Real.exp (-1 / X) ^ n * 1 := by
        gcongr
    _ = (r : ℝ) * ((n : ℝ) ^ (1 : ℕ) * Real.exp (-1 / X) ^ n) := by ring

lemma ofReal_Pfun (N : ℕ) (R : ℝ) (n : ℕ) :
    ((Pfun N R n : ℝ) : ℂ) = ∑ r ∈ Rset N R, ((r : ℂ))⁻¹ * ((psi r n : ℝ) : ℂ) := by
  rw [Pfun, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Complex.ofReal_div, Complex.ofReal_natCast, div_eq_inv_mul]

/-- Weighted `r`-sum of the per-`r` summands is the detector summand. -/
lemma sum_Rset_Sterm {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 R X : ℝ) (ρ : ℂ) (n : ℕ) :
    ∑ r ∈ Rset N R, ((r : ℂ))⁻¹ * Sterm χ z1 z2 X r ρ n
      = ((bvA z1 z2 n * Pfun N R n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) * χ n
        * (n : ℂ) ^ (-ρ) := by
  set Q : ℂ := ((bvA z1 z2 n : ℝ) : ℂ) * χ n * ((Real.exp (-(n : ℝ) / X) : ℝ) : ℂ)
      * (n : ℂ) ^ (-ρ) with hQ
  calc ∑ r ∈ Rset N R, ((r : ℂ))⁻¹ * Sterm χ z1 z2 X r ρ n
      = ∑ r ∈ Rset N R, (((r : ℂ))⁻¹ * ((psi r n : ℝ) : ℂ)) * Q := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Sterm, hQ, Complex.ofReal_mul]
        ring
    _ = (∑ r ∈ Rset N R, ((r : ℂ))⁻¹ * ((psi r n : ℝ) : ℂ)) * Q := (Finset.sum_mul _ _ _).symm
    _ = ((bvA z1 z2 n * Pfun N R n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) * χ n
        * (n : ℂ) ^ (-ρ) := by
        rw [← ofReal_Pfun, hQ, Complex.ofReal_mul, Complex.ofReal_mul]
        ring

/-- Splitting off the `n = 1` term: `∑_n a(n)P(n)e^{−n/X}χ(n)n^{−ρ} = F(ρ,χ) + e^{−1/X}P(1)`
(the vanishing property `a(n) = 0` for `1 < n ≤ z₁` kills everything between). -/
lemma tsum_detector_split {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 R X : ℝ} (hz1 : 1 ≤ z1) (hz12 : z1 < z2) (hX : 0 < X) {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    ∑' n : ℕ, ((bvA z1 z2 n * Pfun N R n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) * χ n
        * (n : ℂ) ^ (-ρ)
      = Fdet χ z1 z2 R X ρ + ((Real.exp (-1 / X) * P1 N R : ℝ) : ℂ) := by
  have hz10 : (0 : ℝ) < z1 := by linarith
  set f1 : ℕ → ℂ := fun n => if z1 < (n : ℝ) then
      ((bvA z1 z2 n * Pfun N R n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-ρ)
    else 0 with hf1
  set f2 : ℕ → ℂ := fun n => if n = 1 then ((Real.exp (-1 / X) * P1 N R : ℝ) : ℂ) else 0
    with hf2
  have hsplit : ∀ n : ℕ,
      ((bvA z1 z2 n * Pfun N R n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-ρ)
      = f1 n + f2 n := by
    intro n
    simp only [hf1, hf2]
    by_cases hgt : z1 < (n : ℝ)
    · have hn1 : n ≠ 1 := by
        intro h
        rw [h] at hgt
        norm_num at hgt
        linarith
      rw [if_pos hgt, if_neg hn1, add_zero]
    · rw [if_neg hgt, zero_add]
      push_neg at hgt
      match n with
      | 0 => simp [bvA_zero]
      | 1 =>
          rw [if_pos rfl, bvA_one hz1 hz12, Pfun_one]
          simp only [Nat.cast_one, map_one, Complex.one_cpow, mul_one]
          push_cast
          ring
      | (k + 2) =>
          have hn0 : 1 < k + 2 := by omega
          rw [if_neg (by omega), bvA_eq_zero hz1 hz12 hn0 hgt]
          simp
  have hsum1 : Summable f1 := summable_fdetTerm χ hz10 hz12 hX hρ
  have hsum2 : Summable f2 := by
    refine summable_of_ne_finset_zero (s := {1}) fun n hn => ?_
    have hne : n ≠ 1 := by simpa using hn
    simp only [hf2, if_neg hne]
  calc ∑' n : ℕ, ((bvA z1 z2 n * Pfun N R n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) * χ n
        * (n : ℂ) ^ (-ρ)
      = ∑' n : ℕ, (f1 n + f2 n) := tsum_congr hsplit
    _ = (∑' n : ℕ, f1 n) + ∑' n : ℕ, f2 n := hsum1.tsum_add hsum2
    _ = Fdet χ z1 z2 R X ρ + ((Real.exp (-1 / X) * P1 N R : ℝ) : ℂ) := by
        congr 1
        simp only [hf2]
        exact tsum_ite_eq 1 _


/-! ## §7.  Assembly: blueprint Lemma 4.1, `DetectionEstimate`, and the
unconditional detector lower bound, for every `χ mod N` -/

/-- Off `w = 0`, the line integrand `ectrInt` is `Ĝ` restricted to the line. -/
lemma ectrInt_line_eq_Ghat {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 X : ℝ) (r : ℕ) {ρ : ℂ} (hLρ : DirichletCharacter.LFunction χ ρ = 0)
    {c : ℝ} (hc : c ≠ 0) :
    (fun u : ℝ => ectrInt χ z1 z2 X r ρ c u)
      = fun u : ℝ => Ghat χ z1 z2 X r ρ ((c : ℂ) + (u : ℂ) * Complex.I) := by
  have hH0 : Hfun χ z1 z2 X r ρ 0 = 0 :=
    Hfun_zero_of_LFunction_eq_zero χ z1 z2 X r hLρ
  funext u
  have hw : (c : ℂ) + (u : ℂ) * Complex.I ≠ 0 := by
    intro hcontra
    have hre := congrArg Complex.re hcontra
    simp at hre
    exact hc hre
  rw [ectrInt_eq_Gamma_mul_Hfun, ← Ghat_eq_of_ne χ z1 z2 X r hH0 hw]

lemma eps2_sub_re_ne_zero {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) : eps2 - ρ.re ≠ 0 := by
  have hlt : eps2 - ρ.re < 0 := by rw [eps2]; linarith
  exact ne_of_lt hlt

/-- One pseudocharacter modulus, shifted (blueprint Lemma 4.1, single `r`, `χ ≠ χ₀`):
`∑_n a(n)ψ_r(n)χ(n)e^{−n/X}n^{−ρ} = (1/2π)∫ Γ(w)X^w L(ρ+w,χ)M_r(ρ+w,χ) du`
on the line `Re w = ε₂ − β`.  Route: `anchor_identity` at `Re w = 3`, rewrite
both lines through `Ĝ` via `ectrInt_line_eq_Ghat` (legal: neither line passes
through `w = 0`), and shift with `Ghat_line_shift`. -/
lemma tsum_Sterm_eq_integral_shift {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ : 99/100 ≤ ρ.re)
    (hβ1 : ρ.re ≤ 1) (hLρ : DirichletCharacter.LFunction χ ρ = 0) :
    ∑' n : ℕ, Sterm χ z1 z2 X r ρ n
      = (((1 / (2 * π) : ℝ)) : ℂ)
          * ∫ u : ℝ, ectrInt χ z1 z2 X r ρ (eps2 - ρ.re) u := by
  have hX0 : (0 : ℝ) < X := by linarith
  calc ∑' n : ℕ, Sterm χ z1 z2 X r ρ n
      = (((1 / (2 * π) : ℝ)) : ℂ) * ∫ u : ℝ, ectrInt χ z1 z2 X r ρ 3 u :=
        anchor_identity χ hz1 hz12 hX0 hr (by linarith)
    _ = (((1 / (2 * π) : ℝ)) : ℂ)
          * ∫ u : ℝ, Ghat χ z1 z2 X r ρ (((3 : ℝ) : ℂ) + (u : ℂ) * Complex.I) := by
        rw [ectrInt_line_eq_Ghat χ z1 z2 X r hLρ (by norm_num : (3 : ℝ) ≠ 0)]
    _ = (((1 / (2 * π) : ℝ)) : ℂ)
          * ∫ u : ℝ, Ghat χ z1 z2 X r ρ (((eps2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * Complex.I) := by
        rw [← Ghat_line_shift hχ hz1 hz12 hX1 hr hβ hβ1 hLρ]
    _ = (((1 / (2 * π) : ℝ)) : ℂ)
          * ∫ u : ℝ, ectrInt χ z1 z2 X r ρ (eps2 - ρ.re) u := by
        rw [ectrInt_line_eq_Ghat χ z1 z2 X r hLρ (eps2_sub_re_ne_zero hβ)]

/-- One pseudocharacter modulus, shifted, `χ = χ₀` (blueprint Lemma 4.1, single
`r`): the shifted line integral plus the residue at the `L`-pole,
`Γ(1−ρ)·X^{1−ρ}·(φ(N)/N)·M_r(1,χ₀)`. -/
lemma tsum_Sterm_eq_integral_shift_principal {N : ℕ} [NeZero N]
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ : 99/100 ≤ ρ.re)
    (hβ1 : ρ.re ≤ 1) (hρ1 : ρ ≠ 1)
    (hLρ : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) ρ = 0) :
    ∑' n : ℕ, Sterm (1 : DirichletCharacter ℂ N) z1 z2 X r ρ n
      = (((1 / (2 * π) : ℝ)) : ℂ)
          * (∫ u : ℝ, ectrInt (1 : DirichletCharacter ℂ N) z1 z2 X r ρ (eps2 - ρ.re) u)
        + Complex.Gamma (1 - ρ) * (X : ℂ) ^ ((1 : ℂ) - ρ) * ((N.totient : ℂ) / N)
          * Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1 := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hπ0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hπ : (((1 / (2 * π) : ℝ)) : ℂ) * (2 * (π : ℂ)) = 1 := by
    push_cast
    field_simp
  calc ∑' n : ℕ, Sterm (1 : DirichletCharacter ℂ N) z1 z2 X r ρ n
      = (((1 / (2 * π) : ℝ)) : ℂ)
          * ∫ u : ℝ, ectrInt (1 : DirichletCharacter ℂ N) z1 z2 X r ρ 3 u :=
        anchor_identity _ hz1 hz12 hX0 hr (by linarith)
    _ = (((1 / (2 * π) : ℝ)) : ℂ)
          * ∫ u : ℝ, Ghat (1 : DirichletCharacter ℂ N) z1 z2 X r ρ
              (((3 : ℝ) : ℂ) + (u : ℂ) * Complex.I) := by
        rw [ectrInt_line_eq_Ghat _ z1 z2 X r hLρ (by norm_num : (3 : ℝ) ≠ 0)]
    _ = (((1 / (2 * π) : ℝ)) : ℂ)
          * ((∫ u : ℝ, Ghat (1 : DirichletCharacter ℂ N) z1 z2 X r ρ
              (((eps2 - ρ.re : ℝ) : ℂ) + (u : ℂ) * Complex.I))
            + 2 * (π : ℂ) * (Complex.Gamma (1 - ρ) * (X : ℂ) ^ ((1 : ℂ) - ρ)
              * ((N.totient : ℂ) / N) * Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1)) := by
        rw [Ghat_line_shift_principal hz1 hz12 hX1 hr hβ hβ1 hρ1 hLρ]
    _ = (((1 / (2 * π) : ℝ)) : ℂ)
          * (∫ u : ℝ, ectrInt (1 : DirichletCharacter ℂ N) z1 z2 X r ρ (eps2 - ρ.re) u)
        + Complex.Gamma (1 - ρ) * (X : ℂ) ^ ((1 : ℂ) - ρ) * ((N.totient : ℂ) / N)
          * Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1 := by
        rw [ectrInt_line_eq_Ghat _ z1 z2 X r hLρ (eps2_sub_re_ne_zero hβ), mul_add,
          ← mul_assoc, hπ, one_mul]

/-- **Blueprint Lemma 4.1** (assembled, every `χ mod N`): at a zero `ρ` of
`L(·,χ)` with `99/100 ≤ Re ρ ≤ 1` (and `ρ ≠ 1` if `χ = χ₀`):
`F(ρ,χ) + e^{−1/X}·P(1) = E_ctr(ρ,χ) + E_pole(ρ,χ)`, with `E_pole` exactly
`Detector.Epole` (zero for `χ ≠ χ₀`). -/
theorem detection_identity_all {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {D : ℝ} (hD1 : 1 < D)
    {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) (hρ1 : χ = 1 → ρ ≠ 1)
    (hLρ : DirichletCharacter.LFunction χ ρ = 0) :
    Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ
        + ((Real.exp (-1 / Xpar D) * P1 N (Rpar D) : ℝ) : ℂ)
      = Ectr χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ
        + Epole χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hz1pos : 0 < z1par D := Real.rpow_pos_of_pos hD0 _
  have hz11 : 1 ≤ z1par D := by
    rw [z1par]
    calc (1 : ℝ) = D ^ (0 : ℝ) := (Real.rpow_zero D).symm
      _ ≤ D ^ (31/50 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by norm_num)
  have hz12 : z1par D < z2par D := by
    rw [z1par, z2par]
    exact Real.rpow_lt_rpow_of_exponent_lt hD1 (by norm_num)
  have hX1 : 1 ≤ Xpar D := by
    rw [Xpar]
    calc (1 : ℝ) = D ^ (0 : ℝ) := (Real.rpow_zero D).symm
      _ ≤ D ^ (6/5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by norm_num)
  have hX0 : (0 : ℝ) < Xpar D := by linarith
  have hρ0 : (0 : ℝ) ≤ ρ.re := by linarith
  have hsummable : ∀ r ∈ Rset N (Rpar D),
      Summable (fun n : ℕ => ((r : ℂ))⁻¹ * Sterm χ (z1par D) (z2par D) (Xpar D) r ρ n) := by
    intro r hrmem
    obtain ⟨⟨hr1, -⟩, -, -⟩ := mem_Rset.mp hrmem
    exact (summable_Sterm χ hz1pos hz12 hX0 (by omega) hρ0).mul_left _
  have hpre : Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ
        + ((Real.exp (-1 / Xpar D) * P1 N (Rpar D) : ℝ) : ℂ)
      = ∑ r ∈ Rset N (Rpar D),
          ∑' n : ℕ, ((r : ℂ))⁻¹ * Sterm χ (z1par D) (z2par D) (Xpar D) r ρ n := by
    calc Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ
          + ((Real.exp (-1 / Xpar D) * P1 N (Rpar D) : ℝ) : ℂ)
        = ∑' n : ℕ, ((bvA (z1par D) (z2par D) n * Pfun N (Rpar D) n
              * Real.exp (-(n : ℝ) / Xpar D) : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-ρ) :=
          (tsum_detector_split χ hz11 hz12 hX0 hρ0).symm
      _ = ∑' n : ℕ, ∑ r ∈ Rset N (Rpar D),
            ((r : ℂ))⁻¹ * Sterm χ (z1par D) (z2par D) (Xpar D) r ρ n :=
          tsum_congr fun n =>
            (sum_Rset_Sterm χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ n).symm
      _ = ∑ r ∈ Rset N (Rpar D),
            ∑' n : ℕ, ((r : ℂ))⁻¹ * Sterm χ (z1par D) (z2par D) (Xpar D) r ρ n :=
          Summable.tsum_finsetSum hsummable
  rw [hpre]
  by_cases hχ : χ = 1
  · subst hχ
    have hρ1' : ρ ≠ 1 := hρ1 rfl
    calc ∑ r ∈ Rset N (Rpar D),
          ∑' n : ℕ, ((r : ℂ))⁻¹ * Sterm (1 : DirichletCharacter ℂ N) (z1par D) (z2par D)
            (Xpar D) r ρ n
        = ∑ r ∈ Rset N (Rpar D), (((r : ℂ))⁻¹
            * ((((1 / (2 * π) : ℝ)) : ℂ)
              * ∫ u : ℝ, ectrInt (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) (Xpar D)
                  r ρ (eps2 - ρ.re) u)
            + ((r : ℂ))⁻¹ * (Complex.Gamma (1 - ρ) * (Xpar D : ℂ) ^ ((1 : ℂ) - ρ)
              * ((N.totient : ℂ) / N)
              * Mr (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) r 1)) := by
          refine Finset.sum_congr rfl fun r hrmem => ?_
          obtain ⟨-, hsq, -⟩ := mem_Rset.mp hrmem
          rw [tsum_mul_left,
            tsum_Sterm_eq_integral_shift_principal hz1pos hz12 hX1 hsq hβ hβ1 hρ1' hLρ,
            mul_add]
      _ = Ectr (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) (Rpar D) (Xpar D) ρ
          + Epole (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) (Rpar D) (Xpar D) ρ := by
          rw [Finset.sum_add_distrib, Ectr, Epole, if_pos rfl, Finset.mul_sum, Finset.mul_sum]
          congr 1
          · exact Finset.sum_congr rfl fun r _ => by ring
          · exact Finset.sum_congr rfl fun r _ => by ring
  · calc ∑ r ∈ Rset N (Rpar D),
          ∑' n : ℕ, ((r : ℂ))⁻¹ * Sterm χ (z1par D) (z2par D) (Xpar D) r ρ n
        = ∑ r ∈ Rset N (Rpar D), ((r : ℂ))⁻¹
            * ((((1 / (2 * π) : ℝ)) : ℂ)
              * ∫ u : ℝ, ectrInt χ (z1par D) (z2par D) (Xpar D) r ρ (eps2 - ρ.re) u) := by
          refine Finset.sum_congr rfl fun r hrmem => ?_
          obtain ⟨-, hsq, -⟩ := mem_Rset.mp hrmem
          rw [tsum_mul_left,
            tsum_Sterm_eq_integral_shift hχ hz1pos hz12 hX1 hsq hβ hβ1 hLρ]
      _ = Ectr χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ := by
          rw [Ectr, Finset.mul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          ring
      _ = Ectr χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ
          + Epole χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ := by
          rw [Epole_eq_zero hχ, add_zero]

/-- **Blueprint Lemma 4.1, `χ ≠ χ₀`**: `F(ρ,χ) + e^{−1/X}·P(1) = E_ctr(ρ,χ)`. -/
theorem detection_identity {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {D : ℝ} (hD1 : 1 < D)
    {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hLρ : DirichletCharacter.LFunction χ ρ = 0) :
    Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ
        + ((Real.exp (-1 / Xpar D) * P1 N (Rpar D) : ℝ) : ℂ)
      = Ectr χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ := by
  have h := detection_identity_all χ hD1 hβ hβ1 (fun h1 => absurd h1 hχ) hLρ
  rwa [Epole_eq_zero hχ, add_zero] at h

/-- **Blueprint Lemma 4.1, `χ = χ₀`**: `F(ρ,χ₀) + e^{−1/X}·P(1) = E_ctr + E_pole`
at a zero `ρ ≠ 1`. -/
theorem detection_identity_principal {N : ℕ} [NeZero N] {D : ℝ} (hD1 : 1 < D)
    {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) (hρ1 : ρ ≠ 1)
    (hLρ : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) ρ = 0) :
    Fdet (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) (Rpar D) (Xpar D) ρ
        + ((Real.exp (-1 / Xpar D) * P1 N (Rpar D) : ℝ) : ℂ)
      = Ectr (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) (Rpar D) (Xpar D) ρ
        + Epole (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) (Rpar D) (Xpar D) ρ :=
  detection_identity_all _ hD1 hβ hβ1 (fun _ => hρ1) hLρ

/-- **Blueprint Lemmas 4.1 + 4.2 combined, every `χ mod N`**: the
`DetectionEstimate` hypothesis of `Detector.detector_lower_bound` holds at
every zero `ρ` of `L(·,χ)` in the detection box (`ρ ≠ 1` if `χ = χ₀`), under
(T1) `2·10¹⁴·C_τ·log D ≤ D^{79/4000}`. -/
theorem detection_estimate_all {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {D : ℝ} (hD1 : 1 < D)
    (hLD : 200 ≤ Real.log D) {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hDN : (N : ℝ) * (|ρ.im| + 2) ≤ D)
    (hT1 : 2 * 10 ^ 14 * Ctau * Real.log D ≤ D ^ (79/4000 : ℝ))
    (hρ1 : χ = 1 → ρ ≠ 1)
    (hLρ : DirichletCharacter.LFunction χ ρ = 0) :
    DetectionEstimate χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ := by
  rw [DetectionEstimate, detection_identity_all χ hD1 hβ hβ1 hρ1 hLρ, add_sub_cancel_right]
  exact norm_Ectr_le χ hD1 hLD hβ hβ1 hDN hT1

/-- **Blueprint Lemmas 4.1 + 4.2 combined, `χ ≠ χ₀`.** -/
theorem detection_estimate {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {D : ℝ} (hD1 : 1 < D)
    (hLD : 200 ≤ Real.log D) {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hDN : (N : ℝ) * (|ρ.im| + 2) ≤ D)
    (hT1 : 2 * 10 ^ 14 * Ctau * Real.log D ≤ D ^ (79/4000 : ℝ))
    (hLρ : DirichletCharacter.LFunction χ ρ = 0) :
    DetectionEstimate χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ :=
  detection_estimate_all χ hD1 hLD hβ hβ1 hDN hT1 (fun h1 => absurd h1 hχ) hLρ

/-- **Blueprint Lemmas 4.1 + 4.2 combined, `χ = χ₀`** (zero `ρ ≠ 1`). -/
theorem detection_estimate_principal {N : ℕ} [NeZero N] {D : ℝ} (hD1 : 1 < D)
    (hLD : 200 ≤ Real.log D) {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hDN : (N : ℝ) * (|ρ.im| + 2) ≤ D)
    (hT1 : 2 * 10 ^ 14 * Ctau * Real.log D ≤ D ^ (79/4000 : ℝ))
    (hρ1 : ρ ≠ 1)
    (hLρ : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) ρ = 0) :
    DetectionEstimate (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) (Rpar D) (Xpar D) ρ :=
  detection_estimate_all _ hD1 hLD hβ hβ1 hDN hT1 (fun _ => hρ1) hLρ

/-- **Blueprint Proposition 4.4, unconditional, every `χ mod N`** (the frozen
Z6c statement of §12.3 at `σ = 99/100`): at every zero `ρ` of `L(·,χ)` with
`99/100 ≤ Re ρ ≤ 1` and `N(|Im ρ|+2) ≤ D`, and `|Im ρ| ≥ Λ₀(99/100)` if
`χ = χ₀`: `‖F(ρ,χ)‖ ≥ (1/400)·(φ(N)/N)·log D`.  Thresholds carried explicitly:
`200 ≤ log D` (Detection.lean's) and (T1) `2·10¹⁴·C_τ·log D ≤ D^{79/4000}`
(this file's; by far the stronger one).  The `Λ₀` clause is Lemma 4.3's
(`Detector.norm_Epole_le`, consumed inside `detector_lower_bound_uncond`); it
also forces `ρ ≠ 1`, as `Λ₀ > 0`. -/
theorem detector_lower_bound_of_zero_all {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {D : ℝ} (hD1 : 1 < D)
    (hLD : 200 ≤ Real.log D) {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hDN : (N : ℝ) * (|ρ.im| + 2) ≤ D)
    (hT1 : 2 * 10 ^ 14 * Ctau * Real.log D ≤ D ^ (79/4000 : ℝ))
    (hγ : χ = 1 → Lambda0 D (99/100) (Real.log (3200 * Real.exp 1 * 60)) ≤ |ρ.im|)
    (hLρ : DirichletCharacter.LFunction χ ρ = 0) :
    (1/400) * ((N.totient : ℝ) / N) * Real.log D
      ≤ ‖Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖ := by
  have hρ1 : χ = 1 → ρ ≠ 1 := by
    intro h1 hρ
    have hΛ := hγ h1
    have hpos : 0 < Lambda0 D (99/100) (Real.log (3200 * Real.exp 1 * 60)) := by
      rw [Lambda0]
      have h1' : 0 < Real.log (Real.log D) := Real.log_pos (by linarith)
      have h2' : 0 < Real.log (3200 * Real.exp 1 * 60) := by
        refine Real.log_pos ?_
        nlinarith [Real.exp_pos 1, Real.add_one_le_exp 1]
      have h3' : 0 ≤ (6/5) * ((1 - 99/100) * Real.log D) := by nlinarith
      linarith
    rw [hρ, Complex.one_im, abs_zero] at hΛ
    linarith
  exact detector_lower_bound_uncond (σ := 99/100) hD1 hLD (by norm_num) (by norm_num)
    hβ hβ1 hγ (detection_estimate_all χ hD1 hLD hβ hβ1 hDN hT1 hρ1 hLρ)

/-- **Blueprint Proposition 4.4, unconditional, `χ ≠ χ₀`.** -/
theorem detector_lower_bound_of_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {D : ℝ} (hD1 : 1 < D)
    (hLD : 200 ≤ Real.log D) {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hDN : (N : ℝ) * (|ρ.im| + 2) ≤ D)
    (hT1 : 2 * 10 ^ 14 * Ctau * Real.log D ≤ D ^ (79/4000 : ℝ))
    (hLρ : DirichletCharacter.LFunction χ ρ = 0) :
    (1/400) * ((N.totient : ℝ) / N) * Real.log D
      ≤ ‖Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖ :=
  detector_lower_bound_of_zero_all χ hD1 hLD hβ hβ1 hDN hT1 (fun h1 => absurd h1 hχ) hLρ

/-- **Blueprint Proposition 4.4, unconditional, `χ = χ₀`** (height clause
`|Im ρ| ≥ Λ₀(99/100)`). -/
theorem detector_lower_bound_of_zero_principal {N : ℕ} [NeZero N] {D : ℝ} (hD1 : 1 < D)
    (hLD : 200 ≤ Real.log D) {ρ : ℂ} (hβ : 99/100 ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hDN : (N : ℝ) * (|ρ.im| + 2) ≤ D)
    (hT1 : 2 * 10 ^ 14 * Ctau * Real.log D ≤ D ^ (79/4000 : ℝ))
    (hγ : Lambda0 D (99/100) (Real.log (3200 * Real.exp 1 * 60)) ≤ |ρ.im|)
    (hLρ : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) ρ = 0) :
    (1/400) * ((N.totient : ℝ) / N) * Real.log D
      ≤ ‖Fdet (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖ :=
  detector_lower_bound_of_zero_all _ hD1 hLD hβ hβ1 hDN hT1 (fun _ => hγ) hLρ

end DetectionShift
end Carmichael
