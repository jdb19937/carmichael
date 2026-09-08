/-
Route Z, sortie L1a: the logged zero detector's contour identity on the half-line
and its pole bound (routez/Z6-logged.md §2 Lemmas 2.1–2.2, §6.1 items 1, 4, 5, 6;
routez/Z6-logged-audit.md F2, F3, F6 and §4 "the additive route").

No `sorry`, no `axiom`, no `native_decide` in this file.

STATEMENTS (namespace `Carmichael.LoggedDetector`, parameters from `LoggedParams`):

 * L1.a  `detection_identity_half χ hD hβ hβ1 hρ1 hLρ`
     (`1 < D`, `39/50 ≤ Re ρ ≤ 1`, `χ = 1 → ρ ≠ 1`, `L(ρ,χ) = 0`):
     `Fdet χ D (2D) 1 (Ypar D) ρ + e^{−1/Ypar D} = EctrHalf χ D (Ypar D) ρ
        + Epole χ D (2D) 1 (Ypar D) ρ`.
 * L1.b  `norm_Epole_le_of_height N hL hσ hβ hβ1 hγ`
     (`40 ≤ log D`, `39/50 ≤ σ ≤ Re ρ ≤ 1`, `log D ≤ |Im ρ|`; `N` explicit per audit F3):
     `‖Epole (1 : DirichletCharacter ℂ N) D (2D) 1 (Ypar D) ρ‖ ≤ 1/8`.

DELIVERED:

§A  The `R = 1` collapse (blueprint §6.1 internal item 1): `Rset_one`
    (`Rset N 1 = {1}`), `P1_one`, `psi_one_left`, `Pfun_one_eq_one`, `tOf_one_right`,
    `eulerT_one`, `Mr_one_eq` (`M_1(s,χ) = ∑_{δ ≤ ⌊z₂⌋} λ_δ χ(δ) δ^{−s}`),
    `Sterm_one_eq`, `Ectr_one_eq`, `Epole_one_eq`
    (`E_pole = if χ = 1 then Γ(1−ρ)X^{1−ρ}(φ(N)/N)·M_1(1,χ₀) else 0`).
    `pole_threshold_numeric`: `16671744·x ≤ e^{(3339/5000)x}` for `x ≥ 40`.

§B  The contour machinery of `DetectionShift` §5 with a FREE ABSCISSA (internal
    item 4; audit F6, additive route — `DetectionShift.lean` is consumed unmodified):
    `norm_LFunction_strip_le_half` (distance `1/2 ≤ ‖s − 1‖`, same constant `6·10⁵`),
    `norm_Hfun_le_half`, `norm_Ghat_le_half`, `integrable_Ghat_line_half`,
    `norm_integral_Ghat_horiz_le_half`, `tendsto_Ghat_horiz_half`,
    `rectInt_Ghat_principal_half`, `Ghat_line_shift_half`,
    `Ghat_line_shift_principal_half`, `tsum_Sterm_eq_integral_shift_half`,
    `tsum_Sterm_eq_integral_shift_principal_half`.
    Abscissa range: `c` with `1/100 ≤ Re ρ + c`, `c ≤ −1/4`, `Re ρ + c ≤ 1/2`, under
    `Re ρ ≤ 1` (hence `−99/100 ≤ c < 0`, `|c| ≥ 1/4`, `|c + 1| ≥ 1/100`,
    `|Re ρ + c − 1| ≥ 1/2`; the rectangle identity needs only the first two).
    The strip hypotheses are `1/100 ≤ Re ρ + Re w` (in place of `ε₂ − Re ρ ≤ Re w`)
    and `1/2 ≤ ‖ρ + w − 1‖` (in place of `99/100 ≤ ‖ρ + w − 1‖`); everything else is
    the delivered proof verbatim.  No lower bound on `Re ρ` is needed in §B: the
    application takes `c = 1/2 − Re ρ`, where `c ≤ −1/4` is `Re ρ ≥ 3/4`.

§C  L1.a `detection_identity_half`: `tsum_detector_split` at `R = 1` (`P1 N 1 = 1`),
    `Sterm_one_eq`, then the free-abscissa shift at `c = 1/2 − Re ρ`, `r = 1`.

§D  L1.b `norm_Epole_le_of_height`: I8(b) `GammaStrip.norm_Gamma_le_of_dist` at
    `1 − ρ`; `‖Y^{1−ρ}‖ = Y^{1−Re ρ} ≤ D^{1661/5000}`; `φ(N)/N ≤ 1`;
    `Detector.norm_Mr_one_principal_le` at `r = 1` (`≤ 1 + log 2D ≤ 2 log D`);
    `e^{−|Im ρ|} ≤ D^{−1}`; and `pole_threshold_numeric`.  The bound is
    `2083968·𝓛·D^{−3339/5000} ≤ 1/8`, i.e. `16671744·𝓛 ≤ e^{(3339/5000)𝓛}`, proved
    from `e^{x/2}·e^{x/6} ≥ 2.7^{20}·(x/6 + 1)` at `x ≥ 40` (`Real.exp_one_gt_d9`,
    `Real.add_one_le_exp`).

DELTAS VS. THE BLUEPRINT / AUDIT (all reported):
 * §B's abscissa hypotheses are `1/100 ≤ Re ρ + c`, `c ≤ −1/4`, `Re ρ + c ≤ 1/2`
   (the blueprint's `−99/100 ≤ c` is implied by the first and `Re ρ ≤ 1`, so it is
   not a hypothesis).  The strip lemmas take `1/100 ≤ Re ρ + Re w` instead of the
   delivered `eps2 − Re ρ ≤ Re w` (same content, no `eps2` in the interface).
 * L1.b has `(N : ℕ)` explicit (audit F3); otherwise byte-faithful to §6.1.  The
   statement carries no `1 < D`: for `D ≤ 0` the pole term is `0` (`⌊2D⌋₊ = 0`),
   for `D > 0` the hypothesis `40 ≤ log D` forces `D > 1`.
 * The `R = 1` collapse also records `Ectr_one_eq` (the delivered `Ectr` on the
   line `Re w = ε₂ − β`); `EctrHalf` is `LoggedParams`' definition, used as is.

MATHLIB / PIN NOTES: `Epole`'s `if χ = 1` needs `open scoped Classical in`;
`Nat.floor_of_nonpos`; `mul_inv_le_iff₀`; `Real.exp_nat_mul`; `Real.log_neg_eq_log`
is why `40 ≤ log D` does not give `0 < D`.
-/
import Carmichael.LoggedParams

set_option autoImplicit false

namespace Carmichael

open Complex MeasureTheory
open scoped Real

namespace LoggedDetector

open Detector DetectionShift

/-! ## §A.  The `R = 1` collapse -/

lemma Rset_one (N : ℕ) : Rset N 1 = {1} := by
  ext r
  rw [mem_Rset, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, -, -⟩
    have : ⌊(1 : ℝ)⌋₊ = 1 := Nat.floor_one
    omega
  · rintro rfl
    exact ⟨⟨le_rfl, by rw [Nat.floor_one]⟩, squarefree_one, Nat.coprime_one_left N⟩

lemma P1_one (N : ℕ) : P1 N 1 = 1 := by
  rw [P1, Rset_one, Finset.sum_singleton]
  simp

lemma psi_one_left (n : ℕ) : psi 1 n = 1 := by
  rw [psi, Nat.gcd_one_left, fmp_one]

lemma Pfun_one_eq_one (N : ℕ) (n : ℕ) : Pfun N 1 n = 1 := by
  rw [Pfun, Rset_one, Finset.sum_singleton, psi_one_left]
  simp

lemma tOf_one_right (δ : ℕ) : tOf δ 1 = 1 := by
  simp [tOf]

lemma eulerT_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ) :
    eulerT χ s 1 = 1 := by
  simp [eulerT]

/-- The mollifier at `r = 1`: `M(s,χ) = ∑_{δ ≤ z₂} λ_δ χ(δ) δ^{−s}`. -/
lemma Mr_one_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z1 z2 : ℝ) (s : ℂ) :
    Mr χ z1 z2 1 s
      = ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊, ((bvLam z1 z2 δ : ℝ) : ℂ) * χ δ * (δ : ℂ) ^ (-s) := by
  unfold Mr
  refine Finset.sum_congr rfl fun δ _ => ?_
  rw [Nat.gcd_one_left, fmp_one, mul_one, tOf_one_right, eulerT_one, mul_one]

/-- The detector summand at `r = 1` is the `R = 1` detector summand. -/
lemma Sterm_one_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z1 z2 X : ℝ) (ρ : ℂ)
    (n : ℕ) :
    Sterm χ z1 z2 X 1 ρ n
      = ((bvA z1 z2 n * Pfun N 1 n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) * χ n
        * (n : ℂ) ^ (-ρ) := by
  rw [Sterm, psi_one_left, Pfun_one_eq_one]
  push_cast
  ring

/-- `E_ctr` at `R = 1` is the single line integral (on `Re w = ε₂ − β`). -/
lemma Ectr_one_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z1 z2 X : ℝ) (ρ : ℂ) :
    Ectr χ z1 z2 1 X ρ
      = (((1 / (2 * π) : ℝ)) : ℂ) * ∫ u : ℝ, ectrInt χ z1 z2 X 1 ρ (eps2 - ρ.re) u := by
  rw [Ectr, Rset_one, Finset.sum_singleton]
  simp

open scoped Classical in
/-- `E_pole` at `R = 1`: `Γ(1−ρ)·X^{1−ρ}·(φ(N)/N)·M(1,χ₀)` for `χ = χ₀`, else `0`. -/
lemma Epole_one_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (z1 z2 X : ℝ) (ρ : ℂ) :
    Epole χ z1 z2 1 X ρ
      = if χ = 1 then
          Complex.Gamma (1 - ρ) * (X : ℂ) ^ ((1 : ℂ) - ρ) * ((N.totient : ℂ) / N)
            * Mr χ z1 z2 1 1
        else 0 := by
  rw [Epole, Rset_one, Finset.sum_singleton]
  simp

/-! ### The numeric threshold for L1.b -/

/-- `16671744·x ≤ e^{(3339/5000)x}` for `x ≥ 40` (the pole-term threshold at `𝓛 = 40`;
`16671744 = 8·2083968 = 8·201·C_Γ·2`). -/
lemma pole_threshold_numeric {x : ℝ} (hx : 40 ≤ x) :
    16671744 * x ≤ Real.exp ((3339/5000 : ℝ) * x) := by
  have h1 : Real.exp 20 ≤ Real.exp (x / 2) := Real.exp_le_exp.mpr (by linarith)
  have h2 : (2.7 : ℝ) ^ 20 ≤ Real.exp 20 := by
    have := Real.exp_one_gt_d9
    calc (2.7 : ℝ) ^ 20 ≤ (Real.exp 1) ^ 20 :=
          pow_le_pow_left₀ (by norm_num) (by linarith) 20
      _ = Real.exp 20 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : x / 6 + 1 ≤ Real.exp (x / 6) := Real.add_one_le_exp _
  have h4 : Real.exp (x / 2) * Real.exp (x / 6) ≤ Real.exp ((3339/5000 : ℝ) * x) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have h5 : (0 : ℝ) ≤ x / 6 + 1 := by linarith
  have h6 : (0 : ℝ) ≤ Real.exp (x / 2) := (Real.exp_pos _).le
  calc 16671744 * x ≤ (2.7 : ℝ) ^ 20 * (x / 6 + 1) := by norm_num; nlinarith
    _ ≤ Real.exp (x / 2) * Real.exp (x / 6) := by
        refine mul_le_mul (h2.trans h1) h3 h5 h6
    _ ≤ Real.exp ((3339/5000 : ℝ) * x) := h4


/-! ## §B.  The contour machinery of `DetectionShift` §5 with a free abscissa

Every lemma below is the delivered lemma of the same stem with (i) the distance
hypothesis `99/100 ≤ ‖s − 1‖` weakened to `1/2 ≤ ‖s − 1‖` (the proofs only use
`1/‖s − 1‖ ≤ 2`), and (ii) the line `Re w = ε₂ − β` replaced by a free abscissa
`c` under `1/100 ≤ Re ρ + c`, `c ≤ −1/4`, `Re ρ + c ≤ 1/2`, `Re ρ ≤ 1` (so
`−99/100 ≤ c < 0`, `|c| ≥ 1/4`, `|c + 1| ≥ 1/100`, and `|Re ρ + c − 1| ≥ 1/2`).
Proofs are copied from `DetectionShift.lean` with only those numerals changed. -/

/-- Uniform polynomial bound for `L` on the half-strip `Re s ≥ 1/100`, at distance
`≥ 1/2` from `s = 1`; same constant as `norm_LFunction_strip_le`. -/
lemma norm_LFunction_strip_le_half {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1/2 ≤ ‖s - 1‖) (h1 : 1/100 ≤ s.re) :
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

/-- The `H`-factor grows at most quadratically in `|Im w|` on the strip
`1/100 ≤ Re(ρ + w)`, `Re w ≤ 3`, at distance `≥ 1/2` from the `L`-pole. -/
lemma norm_Hfun_le_half {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ}
    {w : ℂ} (hw1 : 1/100 ≤ ρ.re + w.re) (hw2 : w.re ≤ 3) (hw3 : 1/2 ≤ ‖ρ + w - 1‖) :
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
  have hlow : 1/100 ≤ (ρ + w).re := by rw [hre]; exact hw1
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
    refine (norm_LFunction_strip_le_half χ hw3 hlow).trans ?_
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

/-- Pointwise bound on `Ĝ` in the strip: exponential decay (I8(b)) times the
polynomial growth of `H`, at distance `≥ 1/2` from the `L`-pole. -/
lemma norm_Ghat_le_half {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ1 : ρ.re ≤ 1)
    (hLρ : DirichletCharacter.LFunction χ ρ = 0)
    {w : ℂ} (hw1 : 1/100 ≤ ρ.re + w.re) (hw2 : w.re ≤ 3)
    (hn1 : 1/100 ≤ ‖w‖) (hn2 : 1/100 ≤ ‖w + 1‖) (hw3 : 1/2 ≤ ‖ρ + w - 1‖) :
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
  have hre1 : -(101/100 : ℝ) ≤ w.re := by linarith
  have hΓ : ‖Complex.Gamma w‖ ≤ 201 * GammaStrip.CGamma * Real.exp (-|w.im|) :=
    GammaStrip.norm_Gamma_le_of_dist w hre1 hw2 hn1 hn2
  have hH := norm_Hfun_le_half χ hz1 hz12 hX1 hr hw1 hw2 hw3
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

/-- `Ĝ` is integrable on any vertical line `Re w = a` with `1/100 ≤ Re ρ + a`, `a ≤ 3`,
away from `{0, −1}` and at distance `≥ 1/2` from the `L`-pole. -/
lemma integrable_Ghat_line_half {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ1 : ρ.re ≤ 1)
    (hρ : ρ ≠ 1 ∨ χ ≠ 1) (hLρ : DirichletCharacter.LFunction χ ρ = 0)
    {a : ℝ} (ha1 : 1/100 ≤ ρ.re + a) (ha2 : a ≤ 3) (ha3 : 1/100 ≤ |a|) (ha4 : 1/100 ≤ |a + 1|)
    (ha5 : 1/2 ≤ |ρ.re + a - 1|) :
    Integrable (fun u : ℝ => Ghat χ z1 z2 X r ρ ((a : ℂ) + (u : ℂ) * Complex.I)) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hane : -1 < a := by linarith
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
  have hw3 : 1/2 ≤ ‖ρ + ((a : ℂ) + (u : ℂ) * Complex.I) - 1‖ := by
    have := Complex.abs_re_le_norm (ρ + ((a : ℂ) + (u : ℂ) * Complex.I) - 1)
    simp only [Complex.sub_re, Complex.add_re, hre, Complex.one_re] at this
    linarith
  rw [Ghat_eq_of_ne χ z1 z2 X r (Hfun_zero_of_LFunction_eq_zero χ z1 z2 X r hLρ) hwne, norm_mul]
  have hH := norm_Hfun_le_half χ hz1 hz12 hX1 hr (w := (a : ℂ) + (u : ℂ) * Complex.I)
    (by rw [hre]; exact ha1) (by rw [hre]; exact ha2) hw3
  rw [him] at hH
  have hG0 : (0 : ℝ) ≤ ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)‖ := norm_nonneg _
  calc ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)‖
        * ‖Hfun χ z1 z2 X r ρ ((a : ℂ) + (u : ℂ) * Complex.I)‖
      ≤ ‖Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)‖ * (CH * (1 + |u|) ^ 2) :=
        mul_le_mul_of_nonneg_left hH hG0
    _ = CH * (‖Complex.Gamma ((a : ℂ) + (u : ℂ) * Complex.I)‖ * (1 + |u|) ^ 2) := by ring

/-! ### The horizontal edges (all `χ`), free abscissa -/

/-- Horizontal-edge bound for `Ĝ` over `[c, 3]` at height `|v| = T ≥ |γ| + 1`. -/
lemma norm_integral_Ghat_horiz_le_half {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ1 : ρ.re ≤ 1)
    (hLρ : DirichletCharacter.LFunction χ ρ = 0)
    {c : ℝ} (hc0 : 1/100 ≤ ρ.re + c) (hc3 : c ≤ 3)
    {T : ℝ} (hT : |ρ.im| + 1 ≤ T) {v : ℝ} (hv : v = T ∨ v = -T) :
    ‖∫ x in c..(3 : ℝ), Ghat χ z1 z2 X r ρ ((x : ℂ) + (v : ℂ) * Complex.I)‖
      ≤ ((201 * GammaStrip.CGamma
          * (X ^ 3 * (600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|ρ.im| + 3)) ^ 2)
            * (z2 * (r : ℝ) ^ 3))) * ((1 + T) ^ 2 * Real.exp (-T)))
        * |(3 : ℝ) - c| := by
  have hT1 : 1 ≤ T := by linarith [abs_nonneg ρ.im]
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
  rw [Set.uIoc_of_le hc3] at hx
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
  have hw3 : 1/2 ≤ ‖ρ + ((x : ℂ) + (v : ℂ) * Complex.I) - 1‖ := by
    have hle := Complex.abs_im_le_norm (ρ + ((x : ℂ) + (v : ℂ) * Complex.I) - 1)
    simp only [Complex.sub_im, Complex.add_im, hxim, Complex.one_im, sub_zero] at hle
    have h := abs_sub_abs_le_abs_sub v (-ρ.im)
    rw [abs_neg, sub_neg_eq_add, habsv] at h
    have h3 : |ρ.im + v| = |v + ρ.im| := by rw [add_comm]
    linarith
  have hbd := norm_Ghat_le_half χ hz1 hz12 hX1 hr hβ1 hLρ
    (w := (x : ℂ) + (v : ℂ) * Complex.I)
    (by rw [hxre]; linarith [hx.1]) (by rw [hxre]; exact hx.2)
    (by linarith) (by linarith) hw3
  rw [hxim, habsv] at hbd
  exact hbd

open Filter Topology in
/-- The horizontal edges over `[c, 3]` vanish as `T → ∞`. -/
lemma tendsto_Ghat_horiz_half {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ1 : ρ.re ≤ 1)
    (hLρ : DirichletCharacter.LFunction χ ρ = 0)
    {c : ℝ} (hc0 : 1/100 ≤ ρ.re + c) (hc3 : c ≤ 3) :
    Tendsto (fun T : ℝ => ∫ x in c..(3 : ℝ),
        Ghat χ z1 z2 X r ρ ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0)
    ∧ Tendsto (fun T : ℝ => ∫ x in c..(3 : ℝ),
        Ghat χ z1 z2 X r ρ ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
  set KK : ℝ := 201 * GammaStrip.CGamma
      * (X ^ 3 * (600000 * 2 ^ N.primeFactors.card * ((N : ℝ) * (|ρ.im| + 3)) ^ 2)
        * (z2 * (r : ℝ) ^ 3)) with hKK
  have hlim0 : Tendsto (fun T : ℝ => (KK * ((1 + T) ^ 2 * Real.exp (-T)))
      * |(3 : ℝ) - c|) atTop (𝓝 0) := by
    have := (tendsto_one_add_sq_mul_exp_neg.const_mul KK).mul_const |(3 : ℝ) - c|
    simpa using this
  constructor
  · refine squeeze_zero_norm' ?_ hlim0
    filter_upwards [eventually_ge_atTop (|ρ.im| + 1)] with T hT
    exact norm_integral_Ghat_horiz_le_half χ hz1 hz12 hX1 hr hβ1 hLρ hc0 hc3 hT (Or.inl rfl)
  · refine squeeze_zero_norm' ?_ hlim0
    filter_upwards [eventually_ge_atTop (|ρ.im| + 1)] with T hT
    exact norm_integral_Ghat_horiz_le_half χ hz1 hz12 hX1 hr hβ1 hLρ hc0 hc3 hT (Or.inr rfl)

/-! ### The rectangle identity and the shifts, free abscissa -/

/-- **The rectangle identity for `χ₀`** over `[c, 3] × [−T, T]`, `T ≥ |γ|+1`,
`1/100 ≤ Re ρ + c`, `c ≤ −1/4`: the boundary integral of `Ĝ` is `2πi` times
the residue at `w = 1−ρ`. -/
theorem rectInt_Ghat_principal_half {N : ℕ} [NeZero N] (z1 z2 : ℝ) {X : ℝ} (hX : 0 < X) (r : ℕ)
    {ρ : ℂ} (hβ1 : ρ.re ≤ 1) (hρ1 : ρ ≠ 1)
    (hLρ : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) ρ = 0)
    {c : ℝ} (hc0 : 1/100 ≤ ρ.re + c) (hc2 : c ≤ -(1/4 : ℝ))
    {T : ℝ} (hT : |ρ.im| + 1 ≤ T) :
    rectInt (Ghat (1 : DirichletCharacter ℂ N) z1 z2 X r ρ)
        ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        (((3 : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
      = 2 * π * Complex.I * (Complex.Gamma (1 - ρ) * (X : ℂ) ^ ((1 : ℂ) - ρ)
          * ((N.totient : ℂ) / N) * Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1) := by
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
/-- **The contour shift, `χ ≠ χ₀`, free abscissa**: the line `Re w = 3` may be moved
to `Re w = c`. -/
theorem Ghat_line_shift_half {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ1 : ρ.re ≤ 1)
    (hLρ : DirichletCharacter.LFunction χ ρ = 0)
    {c : ℝ} (hc0 : 1/100 ≤ ρ.re + c) (hc2 : c ≤ -(1/4 : ℝ)) (hc3 : ρ.re + c ≤ 1/2) :
    ∫ u : ℝ, Ghat χ z1 z2 X r ρ ((c : ℂ) + (u : ℂ) * Complex.I)
      = ∫ u : ℝ, Ghat χ z1 z2 X r ρ (((3 : ℝ) : ℂ) + (u : ℂ) * Complex.I) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hab : c ≤ (3 : ℝ) := by linarith
  obtain ⟨htop, hbot⟩ := tendsto_Ghat_horiz_half χ hz1 hz12 hX1 hr hβ1 hLρ hc0 hab
  refine shift_lines hab ?_ ?_ ?_ htop hbot
  · intro w h1 _
    exact differentiableAt_Ghat χ hX0 z1 z2 r (Or.inr hχ) (by linarith) (Or.inr hχ)
  · exact integrable_Ghat_line_half χ hz1 hz12 hX1 hr hβ1 (Or.inr hχ) hLρ hc0 hab
      (by rw [abs_of_nonpos (by linarith)]; linarith)
      (by rw [abs_of_nonneg (by linarith)]; linarith)
      (by rw [abs_of_nonpos (by linarith)]; linarith)
  · exact integrable_Ghat_line_half χ hz1 hz12 hX1 hr hβ1 (Or.inr hχ) hLρ (by linarith) le_rfl
      (by rw [abs_of_nonneg (by norm_num)]; norm_num)
      (by rw [abs_of_nonneg (by norm_num)]; norm_num)
      (by rw [abs_of_nonneg (by linarith)]; linarith)

open Filter Topology in
/-- **The contour shift, `χ = χ₀`, free abscissa**: the pole of `L(ρ+w,χ₀)` at
`w = 1−ρ` (strictly inside the strip for `ρ ≠ 1`) contributes
`2π·Γ(1−ρ)·X^{1−ρ}·(φ(N)/N)·M_r(1,χ₀)`. -/
theorem Ghat_line_shift_principal_half {N : ℕ} [NeZero N]
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ} (hβ1 : ρ.re ≤ 1)
    (hρ1 : ρ ≠ 1)
    (hLρ : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) ρ = 0)
    {c : ℝ} (hc0 : 1/100 ≤ ρ.re + c) (hc2 : c ≤ -(1/4 : ℝ)) (hc3 : ρ.re + c ≤ 1/2) :
    ∫ u : ℝ, Ghat (1 : DirichletCharacter ℂ N) z1 z2 X r ρ
        (((3 : ℝ) : ℂ) + (u : ℂ) * Complex.I)
      = (∫ u : ℝ, Ghat (1 : DirichletCharacter ℂ N) z1 z2 X r ρ
          ((c : ℂ) + (u : ℂ) * Complex.I))
        + 2 * (π : ℂ) * (Complex.Gamma (1 - ρ) * (X : ℂ) ^ ((1 : ℂ) - ρ)
          * ((N.totient : ℂ) / N) * Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hab : c ≤ (3 : ℝ) := by linarith
  obtain ⟨htop, hbot⟩ :=
    tendsto_Ghat_horiz_half (1 : DirichletCharacter ℂ N) hz1 hz12 hX1 hr hβ1 hLρ hc0 hab
  set c₀ : ℂ := Complex.Gamma (1 - ρ) * (X : ℂ) ^ ((1 : ℂ) - ρ)
    * ((N.totient : ℂ) / N) * Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1 with hc₀
  have hrect : ∀ T : ℝ, |ρ.im| + 1 ≤ T →
      rectInt (Ghat (1 : DirichletCharacter ℂ N) z1 z2 X r ρ)
        ((c : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        (((3 : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I) = 2 * π * Complex.I * c₀ :=
    fun T hT => rectInt_Ghat_principal_half z1 z2 hX0 r hβ1 hρ1 hLρ hc0 hc2 hT
  have hia := integrable_Ghat_line_half (1 : DirichletCharacter ℂ N) hz1 hz12 hX1 hr hβ1
    (Or.inl hρ1) hLρ hc0 hab
    (by rw [abs_of_nonpos (by linarith)]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith)
    (by rw [abs_of_nonpos (by linarith)]; linarith)
  have hib := integrable_Ghat_line_half (1 : DirichletCharacter ℂ N) hz1 hz12 hX1 hr hβ1
    (Or.inl hρ1) hLρ (by linarith) le_rfl
    (by rw [abs_of_nonneg (by norm_num)]; norm_num)
    (by rw [abs_of_nonneg (by norm_num)]; norm_num)
    (by rw [abs_of_nonneg (by linarith)]; linarith)
  have h := shift_lines_residue hrect hia hib htop hbot
  have hI : -Complex.I * (2 * π * Complex.I * c₀) = 2 * (π : ℂ) * c₀ := by
    linear_combination (-(2 * (π : ℂ) * c₀)) * Complex.I_mul_I
  rw [hI] at h
  linear_combination h

/-! ### The shifted single-modulus identities, free abscissa -/

/-- One pseudocharacter modulus, shifted to `Re w = c`, `χ ≠ χ₀`. -/
lemma tsum_Sterm_eq_integral_shift_half {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ}
    (hβ1 : ρ.re ≤ 1) (hLρ : DirichletCharacter.LFunction χ ρ = 0)
    {c : ℝ} (hc0 : 1/100 ≤ ρ.re + c) (hc2 : c ≤ -(1/4 : ℝ)) (hc3 : ρ.re + c ≤ 1/2) :
    ∑' n : ℕ, Sterm χ z1 z2 X r ρ n
      = (((1 / (2 * π) : ℝ)) : ℂ) * ∫ u : ℝ, ectrInt χ z1 z2 X r ρ c u := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hcne : c ≠ 0 := ne_of_lt (by linarith)
  calc ∑' n : ℕ, Sterm χ z1 z2 X r ρ n
      = (((1 / (2 * π) : ℝ)) : ℂ) * ∫ u : ℝ, ectrInt χ z1 z2 X r ρ 3 u :=
        anchor_identity χ hz1 hz12 hX0 hr (by linarith)
    _ = (((1 / (2 * π) : ℝ)) : ℂ)
          * ∫ u : ℝ, Ghat χ z1 z2 X r ρ (((3 : ℝ) : ℂ) + (u : ℂ) * Complex.I) := by
        rw [ectrInt_line_eq_Ghat χ z1 z2 X r hLρ (by norm_num : (3 : ℝ) ≠ 0)]
    _ = (((1 / (2 * π) : ℝ)) : ℂ)
          * ∫ u : ℝ, Ghat χ z1 z2 X r ρ ((c : ℂ) + (u : ℂ) * Complex.I) := by
        rw [← Ghat_line_shift_half hχ hz1 hz12 hX1 hr hβ1 hLρ hc0 hc2 hc3]
    _ = (((1 / (2 * π) : ℝ)) : ℂ) * ∫ u : ℝ, ectrInt χ z1 z2 X r ρ c u := by
        rw [ectrInt_line_eq_Ghat χ z1 z2 X r hLρ hcne]

/-- One pseudocharacter modulus, shifted to `Re w = c`, `χ = χ₀`: the shifted line
integral plus the residue at the `L`-pole. -/
lemma tsum_Sterm_eq_integral_shift_principal_half {N : ℕ} [NeZero N]
    {z1 z2 X : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (hX1 : 1 ≤ X) {r : ℕ} (hr : Squarefree r) {ρ : ℂ}
    (hβ1 : ρ.re ≤ 1) (hρ1 : ρ ≠ 1)
    (hLρ : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) ρ = 0)
    {c : ℝ} (hc0 : 1/100 ≤ ρ.re + c) (hc2 : c ≤ -(1/4 : ℝ)) (hc3 : ρ.re + c ≤ 1/2) :
    ∑' n : ℕ, Sterm (1 : DirichletCharacter ℂ N) z1 z2 X r ρ n
      = (((1 / (2 * π) : ℝ)) : ℂ)
          * (∫ u : ℝ, ectrInt (1 : DirichletCharacter ℂ N) z1 z2 X r ρ c u)
        + Complex.Gamma (1 - ρ) * (X : ℂ) ^ ((1 : ℂ) - ρ) * ((N.totient : ℂ) / N)
          * Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1 := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hcne : c ≠ 0 := ne_of_lt (by linarith)
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
              ((c : ℂ) + (u : ℂ) * Complex.I))
            + 2 * (π : ℂ) * (Complex.Gamma (1 - ρ) * (X : ℂ) ^ ((1 : ℂ) - ρ)
              * ((N.totient : ℂ) / N) * Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1)) := by
        rw [Ghat_line_shift_principal_half hz1 hz12 hX1 hr hβ1 hρ1 hLρ hc0 hc2 hc3]
    _ = (((1 / (2 * π) : ℝ)) : ℂ)
          * (∫ u : ℝ, ectrInt (1 : DirichletCharacter ℂ N) z1 z2 X r ρ c u)
        + Complex.Gamma (1 - ρ) * (X : ℂ) ^ ((1 : ℂ) - ρ) * ((N.totient : ℂ) / N)
          * Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1 := by
        rw [ectrInt_line_eq_Ghat _ z1 z2 X r hLρ hcne, mul_add,
          ← mul_assoc, hπ, one_mul]


/-! ## §C.  L1.a — the detection identity on the half-line (Z6-logged Lemma 2.1) -/

/-- **Z6-logged Lemma 2.1** (L1.a), every `χ mod N`: at a zero `ρ` of `L(·,χ)` with
`39/50 ≤ Re ρ ≤ 1` (and `ρ ≠ 1` if `χ = χ₀`), for the `R = 1` detector at cuts
`(D, 2D)` and smoothing length `Y = D^{151/100}`:
`F(ρ,χ) + e^{−1/Y} = E_ctr(ρ,χ) + E_pole(ρ,χ)`, with the contour on
`Re(ρ + w) = 1/2` and `E_pole` literally `Detector.Epole` (zero for `χ ≠ χ₀`). -/
theorem detection_identity_half {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {D : ℝ} (hD : 1 < D) {ρ : ℂ} (hβ : 39/50 ≤ ρ.re) (hβ1 : ρ.re ≤ 1) (hρ1 : χ = 1 → ρ ≠ 1)
    (hLρ : DirichletCharacter.LFunction χ ρ = 0) :
    Detector.Fdet χ D (2 * D) 1 (Ypar D) ρ + ((Real.exp (-1 / Ypar D) : ℝ) : ℂ)
      = EctrHalf χ D (Ypar D) ρ + Detector.Epole χ D (2 * D) 1 (Ypar D) ρ := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hD1 : (1 : ℝ) ≤ D := hD.le
  have hz12 : D < 2 * D := by linarith
  have hY1 : 1 ≤ Ypar D := by
    rw [Ypar]
    calc (1 : ℝ) = D ^ (0 : ℝ) := (Real.rpow_zero D).symm
      _ ≤ D ^ (151/100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1 (by norm_num)
  have hY0 : (0 : ℝ) < Ypar D := by linarith
  have hρ0 : (0 : ℝ) ≤ ρ.re := by linarith
  have hc0 : 1/100 ≤ ρ.re + (1/2 - ρ.re) := by linarith
  have hc2 : 1/2 - ρ.re ≤ -(1/4 : ℝ) := by linarith
  have hc3 : ρ.re + (1/2 - ρ.re) ≤ 1/2 := by linarith
  have hpre : Fdet χ D (2 * D) 1 (Ypar D) ρ + ((Real.exp (-1 / Ypar D) : ℝ) : ℂ)
      = ∑' n : ℕ, Sterm χ D (2 * D) (Ypar D) 1 ρ n := by
    have h := tsum_detector_split χ (R := 1) hD1 hz12 hY0 hρ0
    rw [P1_one, mul_one] at h
    rw [← h]
    exact tsum_congr fun n => (Sterm_one_eq χ D (2 * D) (Ypar D) ρ n).symm
  rw [hpre, EctrHalf]
  by_cases hχ : χ = 1
  · subst hχ
    rw [tsum_Sterm_eq_integral_shift_principal_half hD0 hz12 hY1 squarefree_one hβ1 (hρ1 rfl)
      hLρ hc0 hc2 hc3, Epole_one_eq, if_pos rfl]
  · rw [tsum_Sterm_eq_integral_shift_half hχ hD0 hz12 hY1 squarefree_one hβ1 hLρ hc0 hc2 hc3,
      Epole_eq_zero hχ, add_zero]

/-! ## §D.  L1.b — the pole term at height `≥ 𝓛` (Z6-logged Lemma 2.2) -/

/-- **Z6-logged Lemma 2.2** (L1.b): for the principal character, at a point `ρ` with
`39/50 ≤ σ ≤ Re ρ ≤ 1` and `|Im ρ| ≥ 𝓛 = log D ≥ 40`, the pole term of the `R = 1`
detector is at most `1/8`.  (Audit F3: `N` explicit.)  Route: I8(b) at `1 − ρ`,
`‖Y^{1−ρ}‖ = Y^{1−Re ρ} ≤ D^{1661/5000}`, `φ(N)/N ≤ 1`, `norm_Mr_one_principal_le` at
`r = 1`, `e^{−|Im ρ|} ≤ D^{−1}`, and `pole_threshold_numeric`.  If `D ≤ 0` the
mollifier is the empty sum and the pole term vanishes. -/
theorem norm_Epole_le_of_height (N : ℕ) [NeZero N] {D : ℝ} (hL : 40 ≤ Real.log D)
    {σ : ℝ} (hσ : 39/50 ≤ σ) {ρ : ℂ} (hβ : σ ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hγ : Real.log D ≤ |ρ.im|) :
    ‖Detector.Epole (1 : DirichletCharacter ℂ N) D (2 * D) 1 (Ypar D) ρ‖ ≤ 1/8 := by
  rw [Epole_one_eq, if_pos rfl]
  rcases le_or_gt D 0 with hD0 | hD0
  · -- degenerate `D ≤ 0`: `⌊2D⌋₊ = 0`, the mollifier is the empty sum
    have hfl : ⌊2 * D⌋₊ = 0 := Nat.floor_of_nonpos (by linarith)
    rw [Mr_one_eq, hfl]
    simp
  have hD1 : 1 < D := by
    by_contra h
    push Not at h
    have := Real.log_le_log hD0 h
    rw [Real.log_one] at this
    linarith
  have hz12 : D < 2 * D := by linarith
  have hY0 : (0 : ℝ) < Ypar D := Real.rpow_pos_of_pos hD0 _
  have hre : (1 - ρ).re = 1 - ρ.re := by simp
  have him : (1 - ρ).im = -ρ.im := by simp
  -- the Γ-factor (I8(b) at `1 − ρ`, at distance `≥ |Im ρ| ≥ 40` from `{0, −1}`)
  have hΓ : ‖Complex.Gamma (1 - ρ)‖
      ≤ 201 * GammaStrip.CGamma * Real.exp (-|(1 - ρ).im|) := by
    refine GammaStrip.norm_Gamma_le_of_dist (1 - ρ) ?_ ?_ ?_ ?_
    · rw [hre]; linarith
    · rw [hre]; linarith
    · have := Complex.abs_im_le_norm (1 - ρ)
      rw [him, abs_neg] at this
      linarith
    · have := Complex.abs_im_le_norm (1 - ρ + 1)
      simp only [Complex.add_im, him, Complex.one_im, add_zero, abs_neg] at this
      linarith
  have hexp : Real.exp (-|(1 - ρ).im|) ≤ Real.exp (-Real.log D) := by
    rw [him, abs_neg]
    exact Real.exp_le_exp.mpr (by linarith)
  -- `‖Y^{1−ρ}‖ = Y^{1−Re ρ} ≤ D^{1661/5000}`
  have hYn : ‖(Ypar D : ℂ) ^ ((1 : ℂ) - ρ)‖ = Ypar D ^ (1 - ρ.re) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY0, hre]
  have hYle : Ypar D ^ (1 - ρ.re) ≤ D ^ (1661/5000 : ℝ) := by
    rw [Ypar, ← Real.rpow_mul hD0.le]
    exact Real.rpow_le_rpow_of_exponent_le hD1.le (by linarith)
  -- `φ(N)/N ≤ 1`
  have hφ : ‖((N.totient : ℂ) / N)‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    rw [div_le_one hN]
    exact_mod_cast Nat.totient_le N
  -- `‖M(1,χ₀)‖ ≤ 1 + log(2D) ≤ 2 log D`
  have hM : ‖Mr (1 : DirichletCharacter ℂ N) D (2 * D) 1 1‖ ≤ 2 * Real.log D := by
    have h := norm_Mr_one_principal_le squarefree_one (Nat.coprime_one_left N) hD0 hz12
      (by linarith : (1 : ℝ) ≤ 2 * D)
    rw [Nat.totient_one, Nat.cast_one, div_one, one_mul,
      Real.log_mul (by norm_num) hD0.ne'] at h
    have hlog2 : Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  -- assemble
  have hC0 : (0 : ℝ) ≤ 201 * GammaStrip.CGamma := by rw [GammaStrip.CGamma_def]; norm_num
  have hE0 : (0 : ℝ) ≤ Real.exp (-Real.log D) := (Real.exp_pos _).le
  have hP0 : (0 : ℝ) ≤ D ^ (1661/5000 : ℝ) := Real.rpow_nonneg hD0.le _
  have hL0 : (0 : ℝ) ≤ 2 * Real.log D := by linarith
  have hstep : ‖Complex.Gamma (1 - ρ)‖ * ‖(Ypar D : ℂ) ^ ((1 : ℂ) - ρ)‖
        * ‖((N.totient : ℂ) / N)‖ * ‖Mr (1 : DirichletCharacter ℂ N) D (2 * D) 1 1‖
      ≤ (201 * GammaStrip.CGamma * Real.exp (-Real.log D)) * D ^ (1661/5000 : ℝ) * 1
        * (2 * Real.log D) := by
    refine mul_le_mul (mul_le_mul (mul_le_mul (hΓ.trans ?_) ?_ (norm_nonneg _) ?_) hφ
      (norm_nonneg _) ?_) hM (norm_nonneg _) ?_
    · exact mul_le_mul_of_nonneg_left hexp hC0
    · rw [hYn]; exact hYle
    · positivity
    · positivity
    · positivity
  rw [norm_mul, norm_mul, norm_mul]
  refine hstep.trans ?_
  -- the numeric clause: `2083968 · 𝓛 · e^{−(3339/5000)𝓛} ≤ 1/8`
  have hkey : Real.exp (-Real.log D) * D ^ (1661/5000 : ℝ)
      = (Real.exp ((3339/5000 : ℝ) * Real.log D))⁻¹ := by
    rw [Real.rpow_def_of_pos hD0, ← Real.exp_add, ← Real.exp_neg]
    congr 1
    ring
  have hnum := pole_threshold_numeric hL
  have hEpos : (0 : ℝ) < Real.exp ((3339/5000 : ℝ) * Real.log D) := Real.exp_pos _
  rw [GammaStrip.CGamma_def]
  calc 201 * 5184 * Real.exp (-Real.log D) * D ^ (1661/5000 : ℝ) * 1 * (2 * Real.log D)
      = (2083968 * Real.log D)
          * (Real.exp (-Real.log D) * D ^ (1661/5000 : ℝ)) := by ring
    _ = (2083968 * Real.log D) * (Real.exp ((3339/5000 : ℝ) * Real.log D))⁻¹ := by rw [hkey]
    _ ≤ 1/8 := by
        rw [mul_inv_le_iff₀ hEpos]
        linarith

end LoggedDetector
end Carmichael
