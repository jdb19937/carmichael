/-
Route Z, sortie Z6d-C: blueprint §8 (the master count `J`), §9 (Theorem Z, the principal
character / `ζ` branch) and §10 (Theorem A, assembly) of routez/Z0b-density.md — the
log-free zero-density theorem, ending in the frozen interface `Carmichael.LogFreeDensity`
of `DensityInterface.lean`.  No `sorry`, no `axiom`, no `native_decide`, no hypothesis
carried; `#print axioms` on every theorem below: [propext, Classical.choice, Quot.sound].

NOTATION.  `d ≥ 1` (`[NeZero d]`), `t` the height, `σ` the abscissa, `D = d(t+2)` written
`(d:ℝ) * (t + 2)`, `𝓛 = Real.log D`, `λ = (1−σ)𝓛`; the frozen §1 parameters are
`Detector`'s `Rpar D = D^{1/100}`, `M0par`, `z1par`, `z2par`, `Xpar D = D^{6/5}`,
`ellpar D = 𝓛/100`; `Q_R = Detector.QR d (Rpar D)`; `N(σ,t,χ) = zeroCountBox χ σ t`.

STATEMENTS.

§1  Lemma 8.1 (diagonal, the BV step), `sigma_diag_le (N) (hD : 1 < D) (hLD : 200 ≤ log D)
    (hσ : 99/100 ≤ σ) (hσ1 : σ ≤ 1)`:
      `∑' n, cDet N z₁ z₂ R X σ n ^ 2 / bMaj N R M₀ X ℓ n ≤ C12 * (Xpar D) ^ (2 − 2σ)`,
    `C12 = 10⁹`.  Log-free: the `log Y` of I4* (`BVL2.bvL2_star_uncond`, constant `5·10⁵`)
    is cancelled by the window width `ℓ = 𝓛/100`.
§2  Lemma 8.2 (one Gram row), `gram_row_le`: for an index `p` of a parity system,
      `∑_q ‖Bgram (χ_p χ_q⁻¹) (𝔰_pq)‖ ≤ C9 CM·Q_R²·(1/100)·𝓛² + J·C11·𝓛³·D^{−7/100}`
    (`gramArg σ t good p q = (ρ_p − σ) + conj(ρ_q − σ)`; main term only on `χ_q = χ_p`,
    Proposition 6.1; row by Lemma 6.4 with Construction 7.2(b); `B_rem` by Lemma 6.3).
    Theorem 8.3 (master count), `card_paritySystem_le`: under `99/100 ≤ σ ≤ 1`, `0 ≤ t`,
    `200 ≤ 𝓛`, (T1) `2·10¹⁴·Ctau·𝓛 ≤ D^{79/4000}`, (T2) `320000·C12·C11·𝓛 ≤ D^{13/500}`,
    the `χ₀` height clause through `good`, and `hMertens : MertensProd (Rpar D) ≤ CM·log(Rpar D)`
    (`0 ≤ CM`): each parity system has `J ≤ CJ CM · (Xpar D)^(2−2σ)`, `CJ CM = 3200·C12·C9 CM`.
    Auxiliary: `inv_le_QR` (`1/R ≤ Q_R`, telescoping, no Mertens), `QR_sq_mul_rpow_ge`.
§3  Corollary 8.4, `sum_good_le_density` (same hypotheses): the good zero mass over `𝒳` is
    `≤ gamM CM · D^((5/2)(1−σ))`, `gamM CM = 20·Cloc·CJ CM`; `(1+λ) ≤ 10·e^{λ/10}` glues
    `12/5 + 1/10 = 5/2`.  Theorem M with explicit thresholds:
    `sum_zeroCountBox_nonprincipal_le_of_thresholds`; frozen form under `MertensHyp`:
    `sum_zeroCountBox_nonprincipal_le_of_mertens`.  Thresholds: `log_le_rpow_eventually`
    (`A log D ≤ D^a` for `D ≥ (2A/a+1)^{2/a}`), `thresholds_eventually`
    (`D₀ = max(e^200, D₁, D₂)`).  `MertensHyp : ∃ CM, 0 ≤ CM ∧ ∀ R ≥ 2, MertensProd R ≤ CM log R`.
§4  Theorem Z under `MertensHyp`: `zeroCountBox_one_le_density_of_mertens` (modulus `1`),
    `zeroCountBox_trivChar_le_density_of_mertens` (`χ₀ mod d`, every `d`, via
    `ZeroCount.zeroCountBox_trivChar_eq`).  `band_thresholds` folds `𝓛_a, 𝓛_b, 𝓛_c`.
§5  Theorem H, `theoremH`: from `LoggedDensity`'s bound (`P ≤ 7/2`, `c₀ ≥ 1`), on
    `σ ∈ [9/10, 99/100]`: `∑_χ N ≤ CH·(400(K+1))^K·(d t^{c₀})^((9/2)(1−σ))`, no threshold.
    `logfree_of_logged_of_mertens (hM : MertensHyp) (h : LoggedDensity) : LogFreeDensity`
    with `c₀' := c₀`, `γ₂ := 2(γm + γζ) + 1120·D₀² + CH·(400(K+1))^K + 1`.
§6  Mertens discharged (from the vendored `Contrib.Mertens`, `∑_{n≤x} Λ(n)/n = log x + O(1)`
    with `|O(1)| ≤ log 4 + 4`): `abel_identity` (discrete Abel summation
    `∑_{0<i≤N} Λ(i)/(i log i) = T(N)/log N + ∑_{1≤i<N} (1/log i − 1/log(i+1)) T(i)`),
    `sum_prime_inv_le` (`∑_{p≤N} 1/p ≤ log log N + 1 + 2(log 4 + 4)/log 2 − log log 2`, using
    `1 − log i/log(i+1) ≤ log log(i+1) − log log i`), `inv_one_sub_le_exp`
    (`(1−x)⁻¹ ≤ e^{x+2x²}` on `[0,1/2]`), `sum_Ioc_inv_sq_le_one`, and
      `mertensProd_le_log (hR : 2 ≤ R) : MertensProd R ≤ CM * log R`,
      `CM = exp(3 + 2(log 4 + 4)/log 2 − log log 2)`;  `mertensHyp : MertensHyp`.
§7  THE UNCONDITIONAL STATEMENTS.
    Theorem M: `sum_zeroCountBox_nonprincipal_le : ∃ γm D₀, 0 ≤ γm ∧ 1 ≤ D₀ ∧
      ∀ d [NeZero d] t σ, 2 ≤ t → 99/100 ≤ σ → σ ≤ 1 → D₀ ≤ d(t+2) →
        ∑ χ ∈ univ.erase 1, N(σ,t,χ) ≤ γm · (d(t+2))^((5/2)(1−σ))`.
    Theorem Z: `zeroCountBox_trivChar_le_density : ∃ γζ ≥ 1, ∀ d [NeZero d] t σ, 2 ≤ t →
      99/100 ≤ σ → σ ≤ 1 → N(σ,t,χ₀) ≤ γζ · (t+2)^((5/2)(1−σ))`.
    THE FROZEN OUTPUT:  `theorem logfree_of_logged (h : LoggedDensity) : LogFreeDensity`.

CONSTANTS.  `C12 = 10⁹` (blueprint `3.7·10⁶/ε = 3.7·10⁸`); `CJ CM = 3200·C12·C9 CM`
(blueprint `32 C₁₂ C₉/ε²`, the `ε` bookkeeping of `C₁₂` absorbed); `gamM CM = 20·Cloc·CJ CM`
(blueprint `(41/5)·C_loc·C_J`); `CM = exp(3 + 2(log 4 + 4)/log 2 − log log 2)`
(blueprint `2e^γ`; the vendored Mertens error `log 4 + 4` is crude); `C6 = log(3200·e·60)`;
`γζ = 1 + 1120·ν₀·log(ν₀+2) + gamM CM + 1120` with `ν₀ = max(D₀, e^{L₀})`,
`L₀ = max(200, (16/c_ζ²)², 2(C6+3))` (`c_ζ` from `zeta_zero_re_lt`, existential);
`D₀ = max(e^200, K₁^{2/a₁}, K₂^{2/a₂})` with `K_i = 2A_i/a_i + 1`, `(A₁,a₁) = (2·10¹⁴·Ctau,
79/4000)`, `(A₂,a₂) = (320000·C12·C11, 13/500)`; `γ₂` as in §5.  Every constant is effective
modulo `c_ζ` (I5) — no ineffective input anywhere.

DELTAS VS. THE BLUEPRINT (none silent).
 1. Lemma 8.1 is proved by a discrete dyadic block decomposition (`sum_mul_exp_le_blocks`:
    `∑_{n ≤ 2^J X} f(n)e^{−n/X} ≤ ∑_{j ≤ J} w_j·A(2^j X)`, `w₀ = 1`, `w_{j+1} = e^{−2^j}`)
    against the finite-sum I4*, not by a Stieltjes integral; `W(n) ≥ e^{−n/X}/3`
    (`GramFunction.Wwin_ge_third`) replaces the blueprint's `1/2`; `C12 = 10⁹`.
    Thresholds `log X ≥ 6`, `z₁ ≥ 100` are subsumed by `200 ≤ 𝓛`.
 2. (T2) is discharged with the crude `Q_R ≥ 1/R` (telescoping product), exponent
    `13/500 = 23/500 − 2/100` instead of the blueprint's `0.0487` with `(d/φ(d))²`.  Mertens
    enters only through `GramFunction.row_sum_le` (Lemma 6.4) and is proved here (§6), not
    quoted from Rosser–Schoenfeld.
 3. Corollary 8.4 uses `(1+λ) ≤ 10e^{λ/10}` (linear `1 + λ/10 ≤ e^{λ/10}`) in place of
    `(41/10)e^{λ/10}`, hence `gamM = 20·Cloc·CJ`.
 4. Theorem Z carries NO ineffective constant: band (a) (`t + 2 ≤ ν₀`) is I6 at the fixed
    height (`zeroCountBox_one_le`), not I7/compactness; `n_ζ(ν₀)` does not appear.  The
    band-(b) case split is `λ² ≤ 𝓛` vs `λ² > 𝓛` (squares, no `√`); in the first case the
    whole band `|γ| < Λ₀` is empty by I5 (`zeta_zero_re_lt`), in the second it is counted by
    I6 in the box `[1/2,1] × [−Λ₀, Λ₀]` and `𝓛² ≤ λ⁴ ≤ e^{(5/2)λ}`.  Thresholds folded into
    `band_thresholds`: `log 𝓛 ≤ 𝓛/4`, `(log 𝓛)² ≤ c_ζ²𝓛`, `C6 + 3 ≤ 𝓛/2`.
 5. Theorem A goes straight to the frozen `9/2` form (not `13/5`): on `σ ≥ 99/100`, M + Z at
    `5/2` with `d(t+2) ≤ 2·d t^{c₀}` and `2^{(5/2)(1−σ)} ≤ 2`; Theorem H needs no threshold
    `D₁(K)` — `log^K(d(t+2)) ≤ (2 log E)^K ≤ (400(K+1))^K·E^{1/200}` for `E = d t^{c₀} ≥ 2`,
    absorbed by `(9/2 − P)(1−σ) ≥ 1/100`; small-`D` absorption is `1120·D₀²` (I6 with
    `t·d ≤ D`, `log D ≤ D`), not `C₁D₀³`.
 6. Internal statements take `0 ≤ t`; the frozen forms take `2 ≤ t`.
-/
import Carmichael.GramFunction
import Carmichael.Representatives
import Carmichael.BVL2
import Carmichael.DensityInterface
import Carmichael.ZetaZeroFree
import Mathlib.Algebra.Order.Field.GeomSum
import Contrib.Mertens

set_option autoImplicit false

namespace Carmichael
namespace ZeroDensity

open Complex Finset Detector DetectionShift GramFunction Representatives
open scoped Classical Real ComplexConjugate

noncomputable section

/-! ## §1 Lemma 8.1: the diagonal `Σ_diag = ∑ c_n²/b_n` -/

/-- `C₁₂ := 10⁹` (blueprint: `3.7·10⁶/ε = 3.7·10⁸`; see the header for the retuning). -/
def C12 : ℝ := 1000000000

lemma C12_pos : 0 < C12 := by rw [C12]; norm_num

/-- Pointwise: `c_n²/b_n ≤ 3·n^{1−2σ}·a(n)²·e^{−n/X}` (blueprint Lemma 8.1, Step 1, with
`W(n) ≥ e^{−n/X}/3`). -/
lemma cDet_sq_div_bMaj_le_term (N : ℕ) {D σ : ℝ} (hD : 1 < D) (hLD : 2 ≤ Real.log D)
    (_hσ : 0 ≤ σ) (n : ℕ) :
    (cDet N (z1par D) (z2par D) (Rpar D) (Xpar D) σ n) ^ 2
        / bMaj N (Rpar D) (M0par D) (Xpar D) (ellpar D) n
      ≤ 3 * ((n : ℝ) ^ (1 - 2 * σ) * (bvA (z1par D) (z2par D) n) ^ 2
          * Real.exp (-(n : ℝ) / Xpar D)) := by
  obtain ⟨hz1, hz12, hMz, hzX⟩ := frozen_window_hyps hD hLD
  have hD0 : 0 < D := by linarith
  have hM0 : 0 < M0par D := Real.rpow_pos_of_pos hD0 _
  have hell : 0 < ellpar D := ellpar_pos hD
  have hz10 : 0 < z1par D := by linarith
  have hX : 0 < Xpar D := by linarith
  have hRHS0 : 0 ≤ (n : ℝ) ^ (1 - 2 * σ) * (bvA (z1par D) (z2par D) n) ^ 2
      * Real.exp (-(n : ℝ) / Xpar D) := by
    have := Real.rpow_nonneg (Nat.cast_nonneg n) (1 - 2 * σ)
    positivity
  unfold cDet bMaj
  split_ifs with h
  · have hn0 : (0 : ℝ) < n := lt_trans hz10 h
    have hW := Wwin_ge_third hM0 hell hz10 hMz hzX h
    have hWpos : 0 < Wwin (M0par D) (Xpar D) (ellpar D) n :=
      lt_of_lt_of_le (by positivity) hW
    rcases eq_or_ne (Pfun N (Rpar D) n) 0 with hP | hP
    · rw [hP]; simp; positivity
    · have hPsq : 0 < (Pfun N (Rpar D) n) ^ 2 := by positivity
      have hb : 0 < (n : ℝ)⁻¹ * (Pfun N (Rpar D) n) ^ 2 * Wwin (M0par D) (Xpar D) (ellpar D) n := by
        positivity
      rw [div_le_iff₀ hb]
      have he : 0 < Real.exp (-(n : ℝ) / Xpar D) := Real.exp_pos _
      -- `n^{1−2σ}·n⁻¹ = (n^{−σ})²`
      have hpow : (n : ℝ) ^ (1 - 2 * σ) * (n : ℝ)⁻¹ = ((n : ℝ) ^ (-σ)) ^ 2 := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hn0, ← Real.rpow_mul_natCast hn0.le]
        congr 1; push_cast; ring
      have hq0 : 0 ≤ ((n : ℝ) ^ (-σ)) ^ 2 := sq_nonneg _
      have hWe : Real.exp (-(n : ℝ) / Xpar D) ≤ 3 * Wwin (M0par D) (Xpar D) (ellpar D) n := by
        linarith
      set a := bvA (z1par D) (z2par D) n
      set P := Pfun N (Rpar D) n
      set W := Wwin (M0par D) (Xpar D) (ellpar D) n
      set E := Real.exp (-(n : ℝ) / Xpar D)
      set q := ((n : ℝ) ^ (-σ)) ^ 2
      have hkey : 3 * ((n : ℝ) ^ (1 - 2 * σ) * a ^ 2 * E) * ((n : ℝ)⁻¹ * P ^ 2 * W)
          = (a ^ 2 * P ^ 2 * E * q) * (3 * W) := by
        have : (n : ℝ) ^ (1 - 2 * σ) * (n : ℝ)⁻¹ = q := hpow
        calc 3 * ((n : ℝ) ^ (1 - 2 * σ) * a ^ 2 * E) * ((n : ℝ)⁻¹ * P ^ 2 * W)
            = (a ^ 2 * P ^ 2 * E * ((n : ℝ) ^ (1 - 2 * σ) * (n : ℝ)⁻¹)) * (3 * W) := by ring
          _ = (a ^ 2 * P ^ 2 * E * q) * (3 * W) := by rw [this]
      have hlhs : (a * P * E * (n : ℝ) ^ (-σ)) ^ 2 = (a ^ 2 * P ^ 2 * E * q) * E := by
        simp only [q]; ring
      rw [hkey, hlhs]
      apply mul_le_mul_of_nonneg_left hWe
      positivity
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
    positivity

/-- The block weights: `w 0 = 1`, `w (j+1) = e^{−2^j}`. -/
def wgt : ℕ → ℝ
  | 0 => 1
  | (j + 1) => Real.exp (-(2 : ℝ) ^ j)

lemma wgt_nonneg (j : ℕ) : 0 ≤ wgt j := by
  cases j with
  | zero => simp [wgt]
  | succ j => exact (Real.exp_pos _).le

/-- `w j ≤ e^{−j}`. -/
lemma wgt_le (j : ℕ) : wgt j ≤ Real.exp (-(j : ℝ)) := by
  cases j with
  | zero => simp [wgt]
  | succ j =>
    simp only [wgt]
    refine Real.exp_le_exp.mpr ?_
    have h : ((j + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ j := by
      have := @Nat.lt_two_pow_self j
      exact_mod_cast this
    push_cast at h ⊢
    linarith

/-- **Block decomposition** (blueprint Lemma 8.1, Step 2, in discrete dyadic form): for
`f ≥ 0`, `∑_{n ≤ 2^J X} f(n) e^{−n/X} ≤ ∑_{j ≤ J} w_j · A(2^j X)`, `A(Y) = ∑_{n ≤ Y} f(n)`. -/
lemma sum_mul_exp_le_blocks {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) {X : ℝ} (hX : 0 < X) (J : ℕ) :
    ∑ n ∈ Ioc 0 ⌊(2 : ℝ) ^ J * X⌋₊, f n * Real.exp (-(n : ℝ) / X)
      ≤ ∑ j ∈ range (J + 1), wgt j * ∑ n ∈ Ioc 0 ⌊(2 : ℝ) ^ j * X⌋₊, f n := by
  induction J with
  | zero =>
    rw [sum_range_one]
    simp only [pow_zero, one_mul, wgt]
    refine sum_le_sum fun n _ => ?_
    have h1 : Real.exp (-(n : ℝ) / X) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (n : ℝ) / X := by positivity
      rw [neg_div]; linarith
    calc f n * Real.exp (-(n : ℝ) / X) ≤ f n * 1 :=
          mul_le_mul_of_nonneg_left h1 (hf n)
      _ = f n := mul_one _
  | succ J ih =>
    have hmono : ⌊(2 : ℝ) ^ J * X⌋₊ ≤ ⌊(2 : ℝ) ^ (J + 1) * X⌋₊ := by
      apply Nat.floor_mono
      have : (2 : ℝ) ^ J ≤ (2 : ℝ) ^ (J + 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_succ J)
      exact mul_le_mul_of_nonneg_right this hX.le
    rw [← sum_Ioc_consecutive _ (Nat.zero_le _) hmono, sum_range_succ]
    refine add_le_add ih ?_
    -- the new block: `n > ⌊2^J X⌋₊` forces `e^{−n/X} ≤ e^{−2^J}`
    have hblock : ∀ n ∈ Ioc ⌊(2 : ℝ) ^ J * X⌋₊ ⌊(2 : ℝ) ^ (J + 1) * X⌋₊,
        f n * Real.exp (-(n : ℝ) / X) ≤ wgt (J + 1) * f n := by
      intro n hn
      rw [mem_Ioc] at hn
      have h2 : (2 : ℝ) ^ J * X < n := by
        have h0 : 0 ≤ (2 : ℝ) ^ J * X := by positivity
        exact (Nat.floor_lt h0).mp hn.1
      have hexp : Real.exp (-(n : ℝ) / X) ≤ wgt (J + 1) := by
        simp only [wgt]
        refine Real.exp_le_exp.mpr ?_
        rw [neg_div, neg_le_neg_iff, le_div_iff₀ hX]
        linarith
      calc f n * Real.exp (-(n : ℝ) / X) ≤ f n * wgt (J + 1) :=
            mul_le_mul_of_nonneg_left hexp (hf n)
        _ = wgt (J + 1) * f n := mul_comm _ _
    calc ∑ n ∈ Ioc ⌊(2 : ℝ) ^ J * X⌋₊ ⌊(2 : ℝ) ^ (J + 1) * X⌋₊, f n * Real.exp (-(n : ℝ) / X)
        ≤ ∑ n ∈ Ioc ⌊(2 : ℝ) ^ J * X⌋₊ ⌊(2 : ℝ) ^ (J + 1) * X⌋₊, wgt (J + 1) * f n :=
          sum_le_sum hblock
      _ = wgt (J + 1) * ∑ n ∈ Ioc ⌊(2 : ℝ) ^ J * X⌋₊ ⌊(2 : ℝ) ^ (J + 1) * X⌋₊, f n := by
          rw [mul_sum]
      _ ≤ wgt (J + 1) * ∑ n ∈ Ioc 0 ⌊(2 : ℝ) ^ (J + 1) * X⌋₊, f n := by
          apply mul_le_mul_of_nonneg_left _ (wgt_nonneg _)
          apply sum_le_sum_of_subset_of_nonneg
          · intro n hn
            rw [mem_Ioc] at hn ⊢
            omega
          · intro n _ _; exact hf n

/-- `2^x ≤ e^x` for `x ≥ 0`. -/
lemma two_rpow_le_exp {x : ℝ} (hx : 0 ≤ x) : (2 : ℝ) ^ x ≤ Real.exp x := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  refine Real.exp_le_exp.mpr ?_
  have := Real.log_two_lt_d9
  nlinarith

/-- The per-block weight: `w_j·(2^j X)^β·log(2^j X) ≤ e^{−j/4}·X^β·(log X + 3)` for
`0 ≤ β ≤ 1/50`, `X ≥ 1`. -/
lemma block_weight_le {X β : ℝ} (hX : 1 ≤ X) (_hβ : 0 ≤ β) (hβ1 : β ≤ 1 / 50) (j : ℕ) :
    wgt j * ((2 : ℝ) ^ j * X) ^ β * Real.log ((2 : ℝ) ^ j * X)
      ≤ Real.exp (-(j : ℝ) / 4) * X ^ β * (Real.log X + 3) := by
  have hX0 : 0 < X := by linarith
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hXβ : 0 ≤ X ^ β := Real.rpow_nonneg hX0.le _
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  -- `(2^j X)^β = 2^{jβ} X^β`
  have hsplit : ((2 : ℝ) ^ j * X) ^ β = (2 : ℝ) ^ ((j : ℝ) * β) * X ^ β := by
    rw [Real.mul_rpow (by positivity) hX0.le, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  -- `log(2^j X) = j log 2 + log X`
  have hlog : Real.log ((2 : ℝ) ^ j * X) = (j : ℝ) * Real.log 2 + Real.log X := by
    rw [Real.log_mul (by positivity) hX0.ne', Real.log_pow]
  -- `w_j 2^{jβ} ≤ e^{−j} e^{j/50} ≤ e^{−j/2}`
  have h2 : (2 : ℝ) ^ ((j : ℝ) * β) ≤ Real.exp ((j : ℝ) / 50) := by
    calc (2 : ℝ) ^ ((j : ℝ) * β) ≤ (2 : ℝ) ^ ((j : ℝ) / 50) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)
      _ ≤ Real.exp ((j : ℝ) / 50) := two_rpow_le_exp (by positivity)
  have hw : wgt j * (2 : ℝ) ^ ((j : ℝ) * β) ≤ Real.exp (-(j : ℝ) / 2) := by
    calc wgt j * (2 : ℝ) ^ ((j : ℝ) * β)
        ≤ Real.exp (-(j : ℝ)) * Real.exp ((j : ℝ) / 50) :=
          mul_le_mul (wgt_le j) h2 (Real.rpow_nonneg (by norm_num) _) (Real.exp_pos _).le
      _ = Real.exp (-(j : ℝ) + (j : ℝ) / 50) := by rw [Real.exp_add]
      _ ≤ Real.exp (-(j : ℝ) / 2) := Real.exp_le_exp.mpr (by linarith)
  -- `e^{−j/2}(j log 2 + log X) ≤ e^{−j/4}(log X + 3)`
  have hje : (j : ℝ) * Real.exp (-(j : ℝ) / 4) ≤ 4 := by
    have h1 := Real.add_one_le_exp ((j : ℝ) / 4)
    have h2 : Real.exp (-(j : ℝ) / 4) = (Real.exp ((j : ℝ) / 4))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [h2, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
    linarith
  have hlog2 : Real.log 2 ≤ 3 / 4 := by have := Real.log_two_lt_d9; linarith
  have hsplit2 : Real.exp (-(j : ℝ) / 2) = Real.exp (-(j : ℝ) / 4) * Real.exp (-(j : ℝ) / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  have he4 : 0 < Real.exp (-(j : ℝ) / 4) := Real.exp_pos _
  have he4' : Real.exp (-(j : ℝ) / 4) ≤ 1 := by
    rw [Real.exp_le_one_iff]; rw [neg_div]; linarith [show 0 ≤ (j : ℝ) / 4 by positivity]
  have hfin : Real.exp (-(j : ℝ) / 2) * ((j : ℝ) * Real.log 2 + Real.log X)
      ≤ Real.exp (-(j : ℝ) / 4) * (Real.log X + 3) := by
    rw [hsplit2]
    have hA : Real.exp (-(j : ℝ) / 4) * ((j : ℝ) * Real.log 2) ≤ 3 := by
      have : Real.exp (-(j : ℝ) / 4) * ((j : ℝ) * Real.log 2)
          = ((j : ℝ) * Real.exp (-(j : ℝ) / 4)) * Real.log 2 := by ring
      rw [this]
      have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith [mul_le_mul hje hlog2 hl2 (by norm_num : (0 : ℝ) ≤ 4)]
    have hB : Real.exp (-(j : ℝ) / 4) * Real.log X ≤ Real.log X :=
      by nlinarith
    nlinarith
  rw [hsplit, hlog]
  calc wgt j * ((2 : ℝ) ^ ((j : ℝ) * β) * X ^ β) * ((j : ℝ) * Real.log 2 + Real.log X)
      = (wgt j * (2 : ℝ) ^ ((j : ℝ) * β)) * ((j : ℝ) * Real.log 2 + Real.log X) * X ^ β := by
        ring
    _ ≤ Real.exp (-(j : ℝ) / 2) * ((j : ℝ) * Real.log 2 + Real.log X) * X ^ β := by
        apply mul_le_mul_of_nonneg_right _ hXβ
        apply mul_le_mul_of_nonneg_right hw
        have : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        positivity
    _ ≤ Real.exp (-(j : ℝ) / 4) * (Real.log X + 3) * X ^ β :=
        mul_le_mul_of_nonneg_right hfin hXβ
    _ = Real.exp (-(j : ℝ) / 4) * X ^ β * (Real.log X + 3) := by ring

/-- `∑_{j < n} e^{−j/4} ≤ 5`. -/
lemma sum_exp_neg_quarter_le (n : ℕ) : ∑ j ∈ range n, Real.exp (-(j : ℝ) / 4) ≤ 5 := by
  have hx : Real.exp (-(1 : ℝ) / 4) = Real.exp (-(1 / 4 : ℝ)) := by norm_num
  have heq : ∀ j : ℕ, Real.exp (-(j : ℝ) / 4) = Real.exp (-(1 / 4 : ℝ)) ^ j := by
    intro j
    rw [← Real.exp_nat_mul]; congr 1; ring
  simp only [heq]
  have h0 : Real.exp (-(1 / 4 : ℝ)) ≠ 0 := (Real.exp_pos _).ne'
  have h1 : Real.exp (-(1 / 4 : ℝ)) < 1 := by
    rw [Real.exp_lt_one_iff]; norm_num
  have hlt : ∑ j ∈ range n, Real.exp (-(1 / 4 : ℝ)) ^ j ≤ (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹ := by
    rw [range_eq_Ico]
    have := geom_sum_Ico_le_of_lt_one (m := 0) (n := n) (Real.exp_pos _).le h1
    rw [pow_zero] at this
    rw [inv_eq_one_div]; exact this
  have h45 : Real.exp (-(1 / 4 : ℝ)) ≤ 4 / 5 := by
    have := Real.add_one_le_exp (1 / 4 : ℝ)
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
    linarith
  have h5 : (1 - Real.exp (-(1 / 4 : ℝ)))⁻¹ ≤ 5 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    linarith
  linarith

lemma Icc_one_eq_Ioc_zero (n : ℕ) : Finset.Icc 1 n = Finset.Ioc 0 n := by
  ext m; simp only [mem_Icc, mem_Ioc]; omega

/-- `b_n ≥ 0` at the frozen parameters. -/
lemma bMaj_nonneg (N : ℕ) {D : ℝ} (hD : 1 < D) (hLD : 2 ≤ Real.log D) (n : ℕ) :
    0 ≤ bMaj N (Rpar D) (M0par D) (Xpar D) (ellpar D) n := by
  obtain ⟨hz1, hz12, hMz, hzX⟩ := frozen_window_hyps hD hLD
  have hD0 : 0 < D := by linarith
  have hM0 : 0 < M0par D := Real.rpow_pos_of_pos hD0 _
  have hell : 0 < ellpar D := ellpar_pos hD
  unfold bMaj
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hW : 0 < Wwin (M0par D) (Xpar D) (ellpar D) n :=
      Wwin_pos hM0 hell (by linarith) hn
    positivity

/-- Parameter sanity at `log D ≥ 200`: `100 ≤ z₁ ≤ X`, `1 ≤ X`. -/
lemma frozen_params_large {D : ℝ} (hD : 1 < D) (hLD : 200 ≤ Real.log D) :
    100 ≤ z1par D ∧ z1par D ≤ Xpar D ∧ 1 ≤ Xpar D := by
  have hD0 : 0 < D := by linarith
  have hz1 : (100 : ℝ) ≤ z1par D := by
    rw [z1par, Real.rpow_def_of_pos hD0]
    have h1 : Real.exp 5 ≤ Real.exp (Real.log D * (31 / 50)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2 : (100 : ℝ) ≤ Real.exp 5 := by
      have h3 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
      have h4 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
      rw [h3]; nlinarith [pow_le_pow_left₀ (by norm_num) h4 5]
    linarith
  have hzX : z1par D ≤ Xpar D := by
    rw [z1par, Xpar]
    exact Real.rpow_le_rpow_of_exponent_le hD.le (by norm_num)
  exact ⟨hz1, hzX, by linarith⟩

/-- **Lemma 8.1 (the diagonal, BV step).**  `Σ_diag = ∑_n c_n²/b_n ≤ C₁₂·X^{2−2σ}` for
`log D ≥ 200`, `σ ∈ [99/100, 1]`, any modulus `N`.  Log-free: the `log X` of I4* is
cancelled by the window width `ℓ = 𝓛/100`. -/
theorem sigma_diag_le (N : ℕ) {D σ : ℝ} (hD : 1 < D) (hLD : 200 ≤ Real.log D)
    (hσ : 99 / 100 ≤ σ) (hσ1 : σ ≤ 1) :
    ∑' n, (cDet N (z1par D) (z2par D) (Rpar D) (Xpar D) σ n) ^ 2
        / bMaj N (Rpar D) (M0par D) (Xpar D) (ellpar D) n
      ≤ C12 * (Xpar D) ^ (2 - 2 * σ) := by
  have hLD2 : 2 ≤ Real.log D := by linarith
  have hD0 : 0 < D := by linarith
  obtain ⟨hz100, hz1X, hX1⟩ := frozen_params_large hD hLD
  have hX0 : 0 < Xpar D := by linarith
  have hell : 0 < ellpar D := ellpar_pos hD
  set f : ℕ → ℝ := fun n => (n : ℝ) ^ (1 - 2 * σ) * (bvA (z1par D) (z2par D) n) ^ 2 with hfdef
  have hf0 : ∀ n, 0 ≤ f n := fun n => by
    simp only [hfdef]
    have := Real.rpow_nonneg (Nat.cast_nonneg n) (1 - 2 * σ)
    positivity
  have hfzero : f 0 = 0 := by
    simp only [hfdef, Nat.cast_zero]
    rw [Real.zero_rpow (by linarith)]; ring
  set β := 2 - 2 * σ with hβdef
  have hβ0 : 0 ≤ β := by linarith
  have hβ1 : β ≤ 1 / 50 := by linarith
  -- I4* at `Y = 2^j X`
  have hA : ∀ j : ℕ, ∑ n ∈ Ioc 0 ⌊(2 : ℝ) ^ j * Xpar D⌋₊, f n
      ≤ 500000 * ((2 : ℝ) ^ j * Xpar D) ^ β * Real.log ((2 : ℝ) ^ j * Xpar D) / ellpar D := by
    intro j
    rw [← Icc_one_eq_Ioc_zero]
    have h2j : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hY : z1par D ≤ (2 : ℝ) ^ j * Xpar D := by nlinarith
    exact BVL2.bvL2_star_uncond hD hz100 hY (by linarith) hσ1
  -- the block-weighted sum
  have hlogX : Real.log (Xpar D) = (6 / 5) * Real.log D := log_Xpar hD0
  have hell' : ellpar D = Real.log D / 100 := by rw [ellpar]; ring
  have hXβ : 0 ≤ (Xpar D) ^ β := Real.rpow_nonneg hX0.le _
  have hbound : ∀ J : ℕ, ∑ j ∈ range (J + 1), wgt j * ∑ n ∈ Ioc 0 ⌊(2 : ℝ) ^ j * Xpar D⌋₊, f n
      ≤ (C12 / 3) * (Xpar D) ^ β := by
    intro J
    calc ∑ j ∈ range (J + 1), wgt j * ∑ n ∈ Ioc 0 ⌊(2 : ℝ) ^ j * Xpar D⌋₊, f n
        ≤ ∑ j ∈ range (J + 1), wgt j * (500000 * ((2 : ℝ) ^ j * Xpar D) ^ β
            * Real.log ((2 : ℝ) ^ j * Xpar D) / ellpar D) :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hA j) (wgt_nonneg j)
      _ = (500000 / ellpar D) * ∑ j ∈ range (J + 1),
            wgt j * ((2 : ℝ) ^ j * Xpar D) ^ β * Real.log ((2 : ℝ) ^ j * Xpar D) := by
          rw [mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
      _ ≤ (500000 / ellpar D) * ∑ j ∈ range (J + 1),
            Real.exp (-(j : ℝ) / 4) * (Xpar D) ^ β * (Real.log (Xpar D) + 3) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_le_sum fun j _ => block_weight_le hX1 hβ0 hβ1 j
      _ = (500000 / ellpar D) * ((Xpar D) ^ β * (Real.log (Xpar D) + 3))
            * ∑ j ∈ range (J + 1), Real.exp (-(j : ℝ) / 4) := by
          rw [mul_sum, mul_sum]; refine sum_congr rfl fun j _ => ?_; ring
      _ ≤ (500000 / ellpar D) * ((Xpar D) ^ β * (Real.log (Xpar D) + 3)) * 5 := by
          apply mul_le_mul_of_nonneg_left (sum_exp_neg_quarter_le _)
          have : 0 ≤ Real.log (Xpar D) + 3 := by rw [hlogX]; linarith
          positivity
      _ ≤ (C12 / 3) * (Xpar D) ^ β := by
          rw [hlogX, hell']
          have hL0 : 0 < Real.log D := by linarith
          have h1 : (500000 / (Real.log D / 100)) * ((Xpar D) ^ β * (6 / 5 * Real.log D + 3)) * 5
              = (Xpar D) ^ β * (500000 * 100 * 5 * (6 / 5 * Real.log D + 3) / Real.log D) := by
            field_simp
          have h2 : 500000 * 100 * 5 * (6 / 5 * Real.log D + 3) / Real.log D ≤ C12 / 3 := by
            rw [C12, div_le_iff₀ hL0]; nlinarith
          rw [h1]
          calc (Xpar D) ^ β * (500000 * 100 * 5 * (6 / 5 * Real.log D + 3) / Real.log D)
              ≤ (Xpar D) ^ β * (C12 / 3) := mul_le_mul_of_nonneg_left h2 hXβ
            _ = (C12 / 3) * (Xpar D) ^ β := mul_comm _ _
  -- termwise domination and the finite-sum bound
  have hterm : ∀ n, (cDet N (z1par D) (z2par D) (Rpar D) (Xpar D) σ n) ^ 2
        / bMaj N (Rpar D) (M0par D) (Xpar D) (ellpar D) n
      ≤ 3 * (f n * Real.exp (-(n : ℝ) / Xpar D)) := fun n =>
    cDet_sq_div_bMaj_le_term N hD hLD2 (by linarith) n
  have hterm0 : ∀ n, 0 ≤ (cDet N (z1par D) (z2par D) (Rpar D) (Xpar D) σ n) ^ 2
        / bMaj N (Rpar D) (M0par D) (Xpar D) (ellpar D) n := fun n =>
    div_nonneg (sq_nonneg _) (bMaj_nonneg N hD hLD2 n)
  refine Real.tsum_le_of_sum_le (fun n => hterm0 n) fun u => ?_
  set M := u.sup id with hMdef
  have hsub : u ⊆ insert 0 (Ioc 0 ⌊(2 : ℝ) ^ M * Xpar D⌋₊) := by
    intro n hn
    rw [mem_insert, mem_Ioc]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · exact Or.inl rfl
    · right
      refine ⟨hn0, Nat.le_floor ?_⟩
      have h1 : n ≤ M := Finset.le_sup (f := id) hn
      have h2 : (n : ℝ) ≤ (2 : ℝ) ^ M := by
        have h3 : (M : ℝ) < (2 : ℝ) ^ M := by exact_mod_cast @Nat.lt_two_pow_self M
        have h4 : (n : ℝ) ≤ M := by exact_mod_cast h1
        linarith
      nlinarith
  have hF0 : ∀ n, 0 ≤ f n * Real.exp (-(n : ℝ) / Xpar D) := fun n =>
    mul_nonneg (hf0 n) (Real.exp_pos _).le
  calc ∑ n ∈ u, (cDet N (z1par D) (z2par D) (Rpar D) (Xpar D) σ n) ^ 2
        / bMaj N (Rpar D) (M0par D) (Xpar D) (ellpar D) n
      ≤ ∑ n ∈ u, 3 * (f n * Real.exp (-(n : ℝ) / Xpar D)) := sum_le_sum fun n _ => hterm n
    _ ≤ ∑ n ∈ insert 0 (Ioc 0 ⌊(2 : ℝ) ^ M * Xpar D⌋₊),
          3 * (f n * Real.exp (-(n : ℝ) / Xpar D)) :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by have := hF0 n; positivity
    _ = 3 * ∑ n ∈ Ioc 0 ⌊(2 : ℝ) ^ M * Xpar D⌋₊, f n * Real.exp (-(n : ℝ) / Xpar D) := by
        rw [sum_insert (by simp), hfzero, mul_sum]; ring
    _ ≤ 3 * ∑ j ∈ range (M + 1), wgt j * ∑ n ∈ Ioc 0 ⌊(2 : ℝ) ^ j * Xpar D⌋₊, f n :=
        mul_le_mul_of_nonneg_left (sum_mul_exp_le_blocks hf0 hX0 M) (by norm_num)
    _ ≤ 3 * ((C12 / 3) * (Xpar D) ^ β) := mul_le_mul_of_nonneg_left (hbound M) (by norm_num)
    _ = C12 * (Xpar D) ^ (2 - 2 * σ) := by rw [hβdef]; ring

/-! ## §2 Lemma 8.2 and Theorem 8.3: the master count for one parity system -/

section ParitySystem

variable {d : ℕ} [NeZero d]

/-- The Gram argument `𝔰_{pq} = (ρ_p − σ) + conj(ρ_q − σ)` of blueprint §5/§8. -/
def gramArg (σ t : ℝ) (good : ℂ → Prop) (p q : DirichletCharacter ℂ d × ℕ) : ℂ :=
  (rep p.1 σ t good p.2 - σ) + conj (rep q.1 σ t good q.2 - σ)

lemma gramArg_re (σ t : ℝ) (good : ℂ → Prop) (p q : DirichletCharacter ℂ d × ℕ) :
    (gramArg σ t good p q).re = ((rep p.1 σ t good p.2).re - σ) + ((rep q.1 σ t good q.2).re - σ) := by
  simp [gramArg]

lemma gramArg_im (σ t : ℝ) (good : ℂ → Prop) (p q : DirichletCharacter ℂ d × ℕ) :
    (gramArg σ t good p q).im = (rep p.1 σ t good p.2).im - (rep q.1 σ t good q.2).im := by
  simp [gramArg]; ring

/-- `0 ≤ Re 𝔰_{pq} ≤ 1/50` at two representatives (blueprint §5 computation). -/
lemma gramArg_re_bounds {σ t : ℝ} (hσ : 99 / 100 ≤ σ) {𝒳 : Finset (DirichletCharacter ℂ d)}
    {good : ℂ → Prop} {par : ℕ} {p q : DirichletCharacter ℂ d × ℕ}
    (hp : p ∈ repIndex σ t 𝒳 good par) (hq : q ∈ repIndex σ t 𝒳 good par) :
    0 ≤ (gramArg σ t good p q).re ∧ (gramArg σ t good p q).re ≤ 1 / 50 := by
  rw [gramArg_re]
  have h1 := mem_zeroFinset.mp (rep_mem_zeroFinset hp)
  have h2 := mem_zeroFinset.mp (rep_mem_zeroFinset hq)
  constructor <;> linarith [h1.1, h1.2.1, h2.1, h2.2.1]

/-- `d·(|Im 𝔰_{pq}| + 2) ≤ 2·d(t+2)` at two representatives (`|γ_p − γ_q| ≤ 2t`). -/
lemma gramArg_height {σ t : ℝ} {𝒳 : Finset (DirichletCharacter ℂ d)}
    {good : ℂ → Prop} {par : ℕ} {p q : DirichletCharacter ℂ d × ℕ}
    (hp : p ∈ repIndex σ t 𝒳 good par) (hq : q ∈ repIndex σ t 𝒳 good par) :
    (d : ℝ) * (|(gramArg σ t good p q).im| + 2) ≤ 2 * ((d : ℝ) * (t + 2)) := by
  rw [gramArg_im]
  have h1 := abs_im_rep_le hp
  have h2 := abs_im_rep_le hq
  have h3 : |(rep p.1 σ t good p.2).im - (rep q.1 σ t good q.2).im| ≤ 2 * t := by
    calc |(rep p.1 σ t good p.2).im - (rep q.1 σ t good q.2).im|
        ≤ |(rep p.1 σ t good p.2).im| + |(rep q.1 σ t good q.2).im| := abs_sub _ _
      _ ≤ 2 * t := by linarith
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  nlinarith

/-- **Lemma 8.2, one row.**  For an index `p` of a parity system,
`∑_q ‖B(𝔰_{pq}, χ_p χ̄_q)‖ ≤ C₉·Q_R²·(1/100)·𝓛² + J·C₁₁·𝓛³·D^{−7/100}`: the main term
survives only on `χ_q = χ_p` (Proposition 6.1) and is summed by Lemma 6.4 with the spacing
of Construction 7.2(b); every pair contributes at most `‖B_rem‖` (Lemma 6.3). -/
theorem gram_row_le {σ t : ℝ} (hσ : 99 / 100 ≤ σ) (ht : 0 ≤ t)
    (hLD : 2 ≤ Real.log ((d : ℝ) * (t + 2)))
    {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop} {par : ℕ}
    {CM : ℝ} (hMertens : MertensProd (Rpar ((d : ℝ) * (t + 2)))
      ≤ CM * Real.log (Rpar ((d : ℝ) * (t + 2))))
    {p : DirichletCharacter ℂ d × ℕ} (hp : p ∈ repIndex σ t 𝒳 good par) :
    ∑ q ∈ repIndex σ t 𝒳 good par,
        ‖Bgram d (Rpar ((d : ℝ) * (t + 2))) (M0par ((d : ℝ) * (t + 2)))
          (Xpar ((d : ℝ) * (t + 2))) (ellpar ((d : ℝ) * (t + 2)))
          (p.1 * (q.1)⁻¹) (gramArg σ t good p q)‖
      ≤ C9 CM * (QR d (Rpar ((d : ℝ) * (t + 2)))) ^ 2 * (1 / 100)
          * (Real.log ((d : ℝ) * (t + 2))) ^ 2
        + ((repIndex σ t 𝒳 good par).card : ℝ)
          * (C11 * (Real.log ((d : ℝ) * (t + 2))) ^ 3
              * ((d : ℝ) * (t + 2)) ^ (-(7 / 100) : ℝ)) := by
  set D : ℝ := (d : ℝ) * (t + 2) with hDdef
  set S := repIndex σ t 𝒳 good par with hSdef
  have hD1 : 1 < D := by
    have := two_le_scale (d := d) ht; linarith
  have hL1 : 1 ≤ Real.log D := by linarith
  set crem : ℝ := C11 * (Real.log D) ^ 3 * D ^ (-(7 / 100) : ℝ) with hcrem
  set main : DirichletCharacter ℂ d × ℕ → ℝ := fun q =>
    ‖((d.totient : ℂ) / d) * ((PhiR d (Rpar D) : ℝ) : ℂ)
      * G1 (M0par D) (Xpar D) (ellpar D) (-(gramArg σ t good p q))‖ with hmain
  -- termwise: `‖B‖ ≤ [χ_q = χ_p]·main + crem`
  have hterm : ∀ q ∈ S,
      ‖Bgram d (Rpar D) (M0par D) (Xpar D) (ellpar D) (p.1 * (q.1)⁻¹) (gramArg σ t good p q)‖
        ≤ (if q.1 = p.1 then main q else 0) + crem := by
    intro q hq
    obtain ⟨hre0, hre1⟩ := gramArg_re_bounds hσ hp hq
    have hθ := gramArg_height hp hq
    rw [Bgram_eq_main_add_rem_frozen d hD1 (p.1 * (q.1)⁻¹) hre0 hre1]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · by_cases h : q.1 = p.1
      · have h' : p.1 * (q.1)⁻¹ = 1 := mul_inv_eq_one.mpr h.symm
        rw [if_pos h', if_pos h]
      · have h' : ¬ p.1 * (q.1)⁻¹ = 1 := fun h'' => h (mul_inv_eq_one.mp h'').symm
        simp only [h, h', if_false, norm_zero, le_refl]
    · exact norm_Brem_le' d hD1 hLD _ hre0 hre1 hθ
  -- the main-term row via Lemma 6.4
  have hrow : ∑ q ∈ S.filter (fun q => q.1 = p.1), main q
      ≤ C9 CM * (QR d (Rpar D)) ^ 2 * (1 / 100) * (Real.log D) ^ 2 := by
    refine row_sum_le d hD1 hL1 (S.filter (fun q => q.1 = p.1)) p (gramArg σ t good p)
      ?_ ?_ ?_ hMertens
    · intro q hq
      exact gramArg_re_bounds hσ hp (mem_filter.mp hq).1
    · intro q hq hne
      obtain ⟨hqS, hχ⟩ := mem_filter.mp hq
      rw [gramArg_im]
      exact rep_spacing ht hp hqS hχ.symm (Ne.symm hne)
    · intro m _
      refine le_trans (card_le_card ?_) (rep_band_card_le ht hp m)
      intro q hq
      simp only [mem_filter] at hq ⊢
      obtain ⟨⟨hqS, hχ⟩, h1, h2⟩ := hq
      rw [gramArg_im] at h1 h2
      refine ⟨hqS, hχ, ?_, ?_⟩
      · rw [abs_sub_comm, ← div_eq_mul_one_div]; exact h1
      · rw [abs_sub_comm, ← div_eq_mul_one_div]; exact h2
  calc ∑ q ∈ S, ‖Bgram d (Rpar D) (M0par D) (Xpar D) (ellpar D) (p.1 * (q.1)⁻¹)
          (gramArg σ t good p q)‖
      ≤ ∑ q ∈ S, ((if q.1 = p.1 then main q else 0) + crem) := sum_le_sum hterm
    _ = ∑ q ∈ S.filter (fun q => q.1 = p.1), main q + (S.card : ℝ) * crem := by
        rw [sum_add_distrib, sum_const, nsmul_eq_mul, sum_filter]
    _ ≤ C9 CM * (QR d (Rpar D)) ^ 2 * (1 / 100) * (Real.log D) ^ 2 + (S.card : ℝ) * crem :=
        add_le_add hrow le_rfl

end ParitySystem

/-! ### The crude lower bound `Q_R ≥ 1/R` (no Mertens; used only in threshold (T2)) -/

/-- `∏_{1 < n ≤ M}(1 − 1/n) = 1/M` (telescoping). -/
lemma prod_Ioc_one_sub_inv (M : ℕ) (hM : 1 ≤ M) :
    ∏ n ∈ Ioc 1 M, (1 - (n : ℝ)⁻¹) = (M : ℝ)⁻¹ := by
  induction M with
  | zero => omega
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with rfl | hM0
    · simp
    · rw [prod_Ioc_succ_top hM0, ih hM0]
      have hM' : (0 : ℝ) < M := by exact_mod_cast hM0
      push_cast
      field_simp
      ring

/-- Product over a subset dominates the product over the whole set, when all factors lie
in `[0,1]`. -/
lemma prod_le_prod_subset_of_le_one' {s t : Finset ℕ} (h : s ⊆ t) (f : ℕ → ℝ)
    (h0 : ∀ p ∈ t, 0 ≤ f p) (h1 : ∀ p ∈ t, f p ≤ 1) :
    ∏ p ∈ t, f p ≤ ∏ p ∈ s, f p := by
  rw [← prod_sdiff h]
  have hA : (0 : ℝ) ≤ ∏ p ∈ t \ s, f p :=
    prod_nonneg fun p hp => h0 p (mem_sdiff.mp hp).1
  have hA1 : ∏ p ∈ t \ s, f p ≤ 1 :=
    prod_le_one (fun p hp => h0 p (mem_sdiff.mp hp).1) (fun p hp => h1 p (mem_sdiff.mp hp).1)
  have hB : (0 : ℝ) ≤ ∏ p ∈ s, f p := prod_nonneg fun p hp => h0 p (h hp)
  nlinarith

/-- `Q_R ≥ 1/R` for `R ≥ 1`: `∏_{p ∣ d, p ≤ R}(1 − 1/p) ≥ ∏_{1 < n ≤ R}(1 − 1/n) = 1/⌊R⌋₊`. -/
lemma inv_le_QR (N : ℕ) {R : ℝ} (hR : 1 ≤ R) : R⁻¹ ≤ QR N R := by
  rw [QR_eq_prod]
  have hR0 : 0 < R := by linarith
  have hM : 1 ≤ ⌊R⌋₊ := Nat.le_floor (by simpa using hR)
  have hsub : N.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ R) ⊆ Ioc 1 ⌊R⌋₊ := by
    intro p hp
    rw [mem_filter] at hp
    rw [mem_Ioc]
    exact ⟨(Nat.prime_of_mem_primeFactors hp.1).one_lt, Nat.le_floor hp.2⟩
  have h1 : ∏ n ∈ Ioc 1 ⌊R⌋₊, (1 - (n : ℝ)⁻¹)
      ≤ ∏ p ∈ N.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ R), (1 - (p : ℝ)⁻¹) := by
    refine prod_le_prod_subset_of_le_one' hsub _ ?_ ?_
    · intro n hn
      rw [mem_Ioc] at hn
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn.1.le
      have : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ this
      linarith
    · intro n hn
      rw [mem_Ioc] at hn
      have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have : 0 ≤ (n : ℝ)⁻¹ := by positivity
      linarith
  rw [prod_Ioc_one_sub_inv _ hM] at h1
  refine le_trans ?_ h1
  have hfl : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR0.le
  have hfl0 : (0 : ℝ) < ⌊R⌋₊ := by exact_mod_cast hM
  exact inv_anti₀ hfl0 hfl

/-- `Q_R² · D^{23/500} ≥ D^{13/500}` at `R = D^{1/100}`. -/
lemma QR_sq_mul_rpow_ge (N : ℕ) {D : ℝ} (hD : 1 < D) :
    D ^ (13 / 500 : ℝ) ≤ (QR N (Rpar D)) ^ 2 * D ^ (23 / 500 : ℝ) := by
  have hD0 : 0 < D := by linarith
  have hR1 : 1 ≤ Rpar D := Real.one_le_rpow hD.le (by norm_num)
  have hQ := inv_le_QR N hR1
  have hRinv : (Rpar D)⁻¹ = D ^ (-(1 / 100) : ℝ) := by
    rw [Rpar, Real.rpow_neg hD0.le]
  have hQ0 : 0 ≤ (Rpar D)⁻¹ := by positivity
  have hsq : ((Rpar D)⁻¹) ^ 2 ≤ (QR N (Rpar D)) ^ 2 := pow_le_pow_left₀ hQ0 hQ 2
  have hpow : ((Rpar D)⁻¹) ^ 2 = D ^ (-(2 / 100) : ℝ) := by
    rw [hRinv, ← Real.rpow_natCast, ← Real.rpow_mul hD0.le]; norm_num
  have hD23 : 0 ≤ D ^ (23 / 500 : ℝ) := Real.rpow_nonneg hD0.le _
  calc D ^ (13 / 500 : ℝ) = D ^ (-(2 / 100) : ℝ) * D ^ (23 / 500 : ℝ) := by
        rw [← Real.rpow_add hD0]; norm_num
    _ = ((Rpar D)⁻¹) ^ 2 * D ^ (23 / 500 : ℝ) := by rw [hpow]
    _ ≤ (QR N (Rpar D)) ^ 2 * D ^ (23 / 500 : ℝ) := mul_le_mul_of_nonneg_right hsq hD23

/-! ### Theorem 8.3 -/

/-- `C_J := 3200·C₁₂·C₉(C_M)` (blueprint `32 C₁₂ C₉/ε²` with the `ε`-bookkeeping of `C₁₂`
absorbed). -/
def CJ (CM : ℝ) : ℝ := 3200 * C12 * C9 CM

lemma C9_nonneg {CM : ℝ} (hCM : 0 ≤ CM) : 0 ≤ C9 CM := by
  rw [C9]
  have h1 := C7_pos
  have h2 : 0 ≤ Real.log 400 := Real.log_nonneg (by norm_num)
  positivity

lemma CJ_nonneg {CM : ℝ} (hCM : 0 ≤ CM) : 0 ≤ CJ CM := by
  rw [CJ]; have := C9_nonneg hCM; have := C12_pos; positivity

/-- `X^{2−2σ} ≤ D^{12/500}` on `σ ≥ 99/100`. -/
lemma Xpar_rpow_le {D σ : ℝ} (hD : 1 < D) (hσ : 99 / 100 ≤ σ) :
    (Xpar D) ^ (2 - 2 * σ) ≤ D ^ (12 / 500 : ℝ) := by
  have hD0 : 0 < D := by linarith
  rw [Xpar, ← Real.rpow_mul hD0.le]
  exact Real.rpow_le_rpow_of_exponent_le hD.le (by linarith)

/-- **Theorem 8.3 (master count).**  Under `200 ≤ 𝓛`, (T1), (T2) and the Mertens
hypothesis, each parity system of Construction 7.2 has `J ≤ C_J·X^{2−2σ}`. -/
theorem card_paritySystem_le {d : ℕ} [NeZero d] {σ t : ℝ} (hσ : 99 / 100 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 0 ≤ t) (hLD : 200 ≤ Real.log ((d : ℝ) * (t + 2)))
    (hT1 : 2 * 10 ^ 14 * Ctau * Real.log ((d : ℝ) * (t + 2))
      ≤ ((d : ℝ) * (t + 2)) ^ (79 / 4000 : ℝ))
    (hT2 : 320000 * C12 * C11 * Real.log ((d : ℝ) * (t + 2))
      ≤ ((d : ℝ) * (t + 2)) ^ (13 / 500 : ℝ))
    {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop}
    (hgood : ∀ χ ∈ 𝒳, χ = 1 → ∀ ρ : ℂ, good ρ →
      Lambda0 ((d : ℝ) * (t + 2)) σ (Real.log (3200 * Real.exp 1 * 60)) ≤ |ρ.im|)
    {CM : ℝ} (hCM : 0 ≤ CM) (hMertens : MertensProd (Rpar ((d : ℝ) * (t + 2)))
      ≤ CM * Real.log (Rpar ((d : ℝ) * (t + 2))))
    (par : ℕ) :
    ((repIndex σ t 𝒳 good par).card : ℝ) ≤ CJ CM * (Xpar ((d : ℝ) * (t + 2))) ^ (2 - 2 * σ) := by
  set D : ℝ := (d : ℝ) * (t + 2) with hDdef
  set S := repIndex σ t 𝒳 good par with hSdef
  have hD1 : 1 < D := by have := two_le_scale (d := d) ht; linarith
  have hD0 : 0 < D := by linarith
  have hL0 : 0 < Real.log D := by linarith
  have hLD2 : 2 ≤ Real.log D := by linarith
  set Q := QR d (Rpar D) with hQdef
  have hQ0 : 0 < Q := QR_pos d (Rpar D)
  set V : ℝ := (1 / 400) * Q * Real.log D with hVdef
  have hV0 : 0 < V := by positivity
  set J : ℝ := (S.card : ℝ) with hJdef
  have hJ0 : 0 ≤ J := Nat.cast_nonneg _
  set β : ℝ := 2 - 2 * σ with hβdef
  set Xβ : ℝ := (Xpar D) ^ β with hXβ
  have hXβ0 : 0 ≤ Xβ := Real.rpow_nonneg (Real.rpow_pos_of_pos hD0 _).le _
  set row : ℝ := C9 CM * Q ^ 2 * (1 / 100) * (Real.log D) ^ 2 with hrowdef
  set crem : ℝ := C11 * (Real.log D) ^ 3 * D ^ (-(7 / 100) : ℝ) with hcrem
  have hrow0 : 0 ≤ row := by have := C9_nonneg hCM; positivity
  -- detection at every representative
  have hdet : ∀ p ∈ S, V ≤ ‖Fdet p.1 (z1par D) (z2par D) (Rpar D) (Xpar D)
      (rep p.1 σ t good p.2)‖ := fun p hp =>
    rep_detect_QR_of_good hσ hσ1 ht hLD hT1 hgood hp
  -- Halász duality on the parity system
  let ρ : S → ℂ := fun p => rep p.1.1 σ t good p.1.2
  let χ : S → DirichletCharacter ℂ d := fun p => p.1.1
  have hρ : ∀ j : S, σ ≤ (ρ j).re := fun j =>
    (mem_zeroFinset.mp (rep_mem_zeroFinset j.2)).1
  have hH := halasz_duality_frozen d hD1 hLD2 ρ χ (by linarith) hρ
  have hF : J * V ≤ ∑ j : S, ‖Fdet (χ j) (z1par D) (z2par D) (Rpar D) (Xpar D) (ρ j)‖ := by
    have h := Finset.card_nsmul_le_sum S
      (fun p => ‖Fdet p.1 (z1par D) (z2par D) (Rpar D) (Xpar D) (rep p.1 σ t good p.2)‖) V hdet
    rw [nsmul_eq_mul] at h
    rw [Finset.sum_coe_sort S
      (fun p => ‖Fdet p.1 (z1par D) (z2par D) (Rpar D) (Xpar D) (rep p.1 σ t good p.2)‖)]
    exact h
  have hF0 : 0 ≤ ∑ j : S, ‖Fdet (χ j) (z1par D) (z2par D) (Rpar D) (Xpar D) (ρ j)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  -- the Gram double sum via Lemma 8.2
  have hrow : ∀ j : S, ∑ k : S, ‖Bgram d (Rpar D) (M0par D) (Xpar D) (ellpar D)
      (χ j * (χ k)⁻¹) (ρ j - σ + conj (ρ k - σ))‖ ≤ row + J * crem := by
    intro j
    have h := gram_row_le hσ ht hLD2 hMertens j.2
    rw [← Finset.sum_coe_sort S] at h
    exact h
  have hG : ∑ j : S, ∑ k : S, ‖Bgram d (Rpar D) (M0par D) (Xpar D) (ellpar D)
      (χ j * (χ k)⁻¹) (ρ j - σ + conj (ρ k - σ))‖ ≤ J * (row + J * crem) := by
    have h := Finset.sum_le_card_nsmul (Finset.univ : Finset S) _ _ (fun j _ => hrow j)
    rw [Finset.card_univ, Fintype.card_coe, nsmul_eq_mul] at h
    exact h
  -- the diagonal via Lemma 8.1
  have hSig := sigma_diag_le d hD1 hLD hσ hσ1
  have hSig0 : 0 ≤ ∑' n, (cDet d (z1par D) (z2par D) (Rpar D) (Xpar D) σ n) ^ 2
      / bMaj d (Rpar D) (M0par D) (Xpar D) (ellpar D) n :=
    tsum_nonneg fun n => div_nonneg (sq_nonneg _) (bMaj_nonneg d hD1 hLD2 n)
  have hG0 : 0 ≤ ∑ j : S, ∑ k : S, ‖Bgram d (Rpar D) (M0par D) (Xpar D) (ellpar D)
      (χ j * (χ k)⁻¹) (ρ j - σ + conj (ρ k - σ))‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  -- assemble: `J²V² ≤ C₁₂ X^β (J·row + J²·crem)`
  have hmain : (J * V) ^ 2 ≤ C12 * Xβ * (J * (row + J * crem)) := by
    calc (J * V) ^ 2
        ≤ (∑ j : S, ‖Fdet (χ j) (z1par D) (z2par D) (Rpar D) (Xpar D) (ρ j)‖) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hF 2
      _ ≤ _ := hH
      _ ≤ C12 * Xβ * (J * (row + J * crem)) :=
          mul_le_mul hSig hG hG0 (by have := C12_pos; positivity)
  -- (T2): `C₁₂ X^β crem ≤ V²/2`
  have hb : C12 * Xβ * crem ≤ V ^ 2 / 2 := by
    have hX12 : Xβ ≤ D ^ (12 / 500 : ℝ) := Xpar_rpow_le hD1 hσ
    have hT2' := QR_sq_mul_rpow_ge d hD1
    have hpow : D ^ (12 / 500 : ℝ) * D ^ (-(7 / 100) : ℝ) = D ^ (-(23 / 500) : ℝ) := by
      rw [← Real.rpow_add hD0]; norm_num
    have hpow2 : D ^ (23 / 500 : ℝ) * D ^ (-(23 / 500) : ℝ) = 1 := by
      rw [← Real.rpow_add hD0]; norm_num
    have hneg0 : 0 < D ^ (-(23 / 500) : ℝ) := Real.rpow_pos_of_pos hD0 _
    have hC11 : 0 < C11 := by
      rw [C11]; have := GammaStrip.CGamma_pos; have := Ctau_pos; positivity
    have h1 : C12 * Xβ * crem ≤ C12 * C11 * (Real.log D) ^ 3 * D ^ (-(23 / 500) : ℝ) := by
      rw [← hpow]
      have : C12 * Xβ * crem = C12 * C11 * (Real.log D) ^ 3 * D ^ (-(7 / 100) : ℝ) * Xβ := by
        rw [hcrem]; ring
      rw [this]
      have hc0 : 0 ≤ C12 * C11 * (Real.log D) ^ 3 * D ^ (-(7 / 100) : ℝ) := by
        have := C12_pos; have := Real.rpow_pos_of_pos hD0 (-(7 / 100) : ℝ); positivity
      calc C12 * C11 * (Real.log D) ^ 3 * D ^ (-(7 / 100) : ℝ) * Xβ
          ≤ C12 * C11 * (Real.log D) ^ 3 * D ^ (-(7 / 100) : ℝ) * D ^ (12 / 500 : ℝ) :=
            mul_le_mul_of_nonneg_left hX12 hc0
        _ = C12 * C11 * (Real.log D) ^ 3 * (D ^ (12 / 500 : ℝ) * D ^ (-(7 / 100) : ℝ)) := by ring
    -- `320000 C₁₂ C₁₁ 𝓛 D^{−23/500} ≤ Q²`
    have h2 : 320000 * C12 * C11 * Real.log D * D ^ (-(23 / 500) : ℝ) ≤ Q ^ 2 := by
      have h3 : 320000 * C12 * C11 * Real.log D ≤ Q ^ 2 * D ^ (23 / 500 : ℝ) := hT2.trans hT2'
      calc 320000 * C12 * C11 * Real.log D * D ^ (-(23 / 500) : ℝ)
          ≤ Q ^ 2 * D ^ (23 / 500 : ℝ) * D ^ (-(23 / 500) : ℝ) :=
            mul_le_mul_of_nonneg_right h3 hneg0.le
        _ = Q ^ 2 := by rw [mul_assoc, hpow2, mul_one]
    have hV2 : V ^ 2 / 2 = Q ^ 2 * (Real.log D) ^ 2 / 320000 := by rw [hVdef]; ring
    rw [hV2]
    refine h1.trans ?_
    have h4 : C12 * C11 * (Real.log D) ^ 3 * D ^ (-(23 / 500) : ℝ)
        = (320000 * C12 * C11 * Real.log D * D ^ (-(23 / 500) : ℝ)) * (Real.log D) ^ 2 / 320000 := by
      ring
    rw [h4]
    have hL2 : 0 ≤ (Real.log D) ^ 2 / 320000 := by positivity
    calc (320000 * C12 * C11 * Real.log D * D ^ (-(23 / 500) : ℝ)) * (Real.log D) ^ 2 / 320000
        = (320000 * C12 * C11 * Real.log D * D ^ (-(23 / 500) : ℝ)) * ((Real.log D) ^ 2 / 320000) := by
          ring
      _ ≤ Q ^ 2 * ((Real.log D) ^ 2 / 320000) := mul_le_mul_of_nonneg_right h2 hL2
      _ = Q ^ 2 * (Real.log D) ^ 2 / 320000 := by ring
  -- absorb and divide
  set a : ℝ := C12 * Xβ * row with hadef
  have ha0 : 0 ≤ a := by have := C12_pos; positivity
  have hkey : (V ^ 2 / 2) * J ^ 2 ≤ a * J := by
    have h1 : (J * V) ^ 2 = V ^ 2 * J ^ 2 := by ring
    have h2 : C12 * Xβ * (J * (row + J * crem)) = a * J + (C12 * Xβ * crem) * J ^ 2 := by
      rw [hadef]; ring
    rw [h1, h2] at hmain
    have h3 : (C12 * Xβ * crem) * J ^ 2 ≤ (V ^ 2 / 2) * J ^ 2 :=
      mul_le_mul_of_nonneg_right hb (sq_nonneg J)
    linarith
  rcases eq_or_lt_of_le hJ0 with hJ | hJ
  · rw [← hJ]
    exact mul_nonneg (CJ_nonneg hCM) hXβ0
  · have h4 : (V ^ 2 / 2) * J ≤ a := by
      have : ((V ^ 2 / 2) * J) * J ≤ a * J := by rw [mul_assoc, ← sq]; exact hkey
      exact le_of_mul_le_mul_right this hJ
    have hV2 : 0 < V ^ 2 / 2 := by positivity
    have h5 : J ≤ a / (V ^ 2 / 2) := by
      rw [le_div_iff₀ hV2]; linarith
    refine h5.trans (le_of_eq ?_)
    rw [hadef, hrowdef, hVdef, CJ]
    field_simp
    ring

/-! ## §3 Corollary 8.4: the density bound for the good zero mass, and Theorem M -/

/-- `γ_m(C_M) := 20·C_loc·C_J(C_M)` (blueprint `(41/5)·C_loc·C_J`; the `(1+λ) ≤ 10e^{λ/10}`
absorption is used in place of `(41/10)e^{λ/10}`). -/
def gamM (CM : ℝ) : ℝ := 20 * Cloc * CJ CM

lemma Cloc_pos : 0 < Cloc := by rw [Cloc_eq]; norm_num

lemma gamM_nonneg {CM : ℝ} (hCM : 0 ≤ CM) : 0 ≤ gamM CM := by
  rw [gamM]; have := CJ_nonneg hCM; have := Cloc_pos; positivity

/-- `1 + x ≤ 10·e^{x/10}` for `x ≥ 0`. -/
lemma one_add_le_ten_exp {x : ℝ} (_hx : 0 ≤ x) : 1 + x ≤ 10 * Real.exp (x / 10) := by
  have := Real.add_one_le_exp (x / 10)
  linarith

/-- `X^{2−2σ}·e^{λ/10} = D^{(5/2)(1−σ)}` at `X = D^{6/5}`, `λ = (1−σ)𝓛`. -/
lemma Xpar_rpow_mul_exp {D σ : ℝ} (hD : 0 < D) :
    (Xpar D) ^ (2 - 2 * σ) * Real.exp ((1 - σ) * Real.log D / 10)
      = D ^ ((5 / 2 : ℝ) * (1 - σ)) := by
  rw [Xpar, ← Real.rpow_mul hD.le, Real.rpow_def_of_pos hD, Real.rpow_def_of_pos hD,
    ← Real.exp_add]
  congr 1; ring

/-- **Corollary 8.4, general `good` (the machine's output).**  Under `200 ≤ 𝓛`, (T1), (T2),
the `χ₀` height clause and Mertens: the good zero mass over `𝒳` is
`≤ γ_m·D^{(5/2)(1−σ)}`.  Log-free. -/
theorem sum_good_le_density {d : ℕ} [NeZero d] {σ t : ℝ} (hσ : 99 / 100 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 0 ≤ t) (hLD : 200 ≤ Real.log ((d : ℝ) * (t + 2)))
    (hT1 : 2 * 10 ^ 14 * Ctau * Real.log ((d : ℝ) * (t + 2))
      ≤ ((d : ℝ) * (t + 2)) ^ (79 / 4000 : ℝ))
    (hT2 : 320000 * C12 * C11 * Real.log ((d : ℝ) * (t + 2))
      ≤ ((d : ℝ) * (t + 2)) ^ (13 / 500 : ℝ))
    {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop}
    (hgood : ∀ χ ∈ 𝒳, χ = 1 → ∀ ρ : ℂ, good ρ →
      Lambda0 ((d : ℝ) * (t + 2)) σ (Real.log (3200 * Real.exp 1 * 60)) ≤ |ρ.im|)
    {CM : ℝ} (hCM : 0 ≤ CM) (hMertens : MertensProd (Rpar ((d : ℝ) * (t + 2)))
      ≤ CM * Real.log (Rpar ((d : ℝ) * (t + 2)))) :
    ((∑ χ ∈ 𝒳, ∑ ρ ∈ (zeroFinset χ σ t).filter good,
        analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ)
      ≤ gamM CM * ((d : ℝ) * (t + 2)) ^ ((5 / 2 : ℝ) * (1 - σ)) := by
  set D : ℝ := (d : ℝ) * (t + 2) with hDdef
  have hD1 : 1 < D := by have := two_le_scale (d := d) ht; linarith
  have hD0 : 0 < D := by linarith
  have h0 := card_paritySystem_le hσ hσ1 ht hLD hT1 hT2 hgood hCM hMertens 0
  have h1 := card_paritySystem_le hσ hσ1 ht hLD hT1 hT2 hgood hCM hMertens 1
  have hcov := sum_good_le hσ hσ1 ht (by linarith) 𝒳 good
  set lam : ℝ := (1 - σ) * Real.log D with hlam
  have hlam0 : 0 ≤ lam := mul_nonneg (by linarith) (by linarith)
  have habs := one_add_le_ten_exp hlam0
  set Xβ := (Xpar D) ^ (2 - 2 * σ) with hXβ
  have hXβ0 : 0 ≤ Xβ := Real.rpow_nonneg (Real.rpow_pos_of_pos hD0 _).le _
  have hCJ := CJ_nonneg hCM
  have hCloc := Cloc_pos
  have hE0 : 0 < Real.exp (lam / 10) := Real.exp_pos _
  calc ((∑ χ ∈ 𝒳, ∑ ρ ∈ (zeroFinset χ σ t).filter good,
        analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ)
      ≤ Cloc * (1 + lam) * (((repIndex σ t 𝒳 good 0).card : ℝ)
          + (repIndex σ t 𝒳 good 1).card) := hcov
    _ ≤ Cloc * (10 * Real.exp (lam / 10)) * (CJ CM * Xβ + CJ CM * Xβ) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left habs hCloc.le) (add_le_add h0 h1)
          (by positivity) (by positivity)
    _ = gamM CM * (Xβ * Real.exp ((1 - σ) * Real.log D / 10)) := by
        rw [gamM, hlam]; ring
    _ = gamM CM * D ^ ((5 / 2 : ℝ) * (1 - σ)) := by rw [hXβ, Xpar_rpow_mul_exp hD0]

/-- **Theorem M (Corollary 8.4), explicit-threshold form.**  For `d ≥ 1`, `t ≥ 0`,
`σ ∈ [99/100, 1]` with `200 ≤ 𝓛`, (T1), (T2) and Mertens at `R = D^{1/100}`:
`∑_{χ ≠ χ₀} N(σ,t,χ) ≤ γ_m·(d(t+2))^{(5/2)(1−σ)}`. -/
theorem sum_zeroCountBox_nonprincipal_le_of_thresholds {d : ℕ} [NeZero d] {σ t : ℝ}
    (hσ : 99 / 100 ≤ σ) (hσ1 : σ ≤ 1) (ht : 0 ≤ t)
    (hLD : 200 ≤ Real.log ((d : ℝ) * (t + 2)))
    (hT1 : 2 * 10 ^ 14 * Ctau * Real.log ((d : ℝ) * (t + 2))
      ≤ ((d : ℝ) * (t + 2)) ^ (79 / 4000 : ℝ))
    (hT2 : 320000 * C12 * C11 * Real.log ((d : ℝ) * (t + 2))
      ≤ ((d : ℝ) * (t + 2)) ^ (13 / 500 : ℝ))
    {CM : ℝ} (hCM : 0 ≤ CM) (hMertens : MertensProd (Rpar ((d : ℝ) * (t + 2)))
      ≤ CM * Real.log (Rpar ((d : ℝ) * (t + 2)))) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1, (zeroCountBox χ σ t : ℝ)
      ≤ gamM CM * ((d : ℝ) * (t + 2)) ^ ((5 / 2 : ℝ) * (1 - σ)) := by
  have hgood : ∀ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1, χ = 1 →
      ∀ ρ : ℂ, (fun _ : ℂ => True) ρ →
        Lambda0 ((d : ℝ) * (t + 2)) σ (Real.log (3200 * Real.exp 1 * 60)) ≤ |ρ.im| := by
    intro χ hχ h1
    exact absurd h1 (Finset.ne_of_mem_erase hχ)
  have h := sum_good_le_density hσ hσ1 ht hLD hT1 hT2 hgood hCM hMertens
  simp only [Finset.filter_true] at h
  rw [Nat.cast_sum] at h
  exact h

/-! ### Thresholds: everything is eventually true in `D` -/

/-- `A·log D ≤ D^a` for all `D ≥ D₀(A, a)`, explicitly. -/
lemma log_le_rpow_eventually {A a : ℝ} (hA : 0 ≤ A) (ha : 0 < a) :
    ∃ D₀ : ℝ, 1 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D → A * Real.log D ≤ D ^ a := by
  set K : ℝ := 2 * A / a + 1 with hK
  have hK1 : 1 ≤ K := by
    have : 0 ≤ 2 * A / a := by positivity
    linarith
  refine ⟨K ^ (2 / a), Real.one_le_rpow hK1 (by positivity), fun D hD => ?_⟩
  have hD1 : 1 ≤ D := le_trans (Real.one_le_rpow hK1 (by positivity)) hD
  have hD0 : 0 < D := by linarith
  have hlog : Real.log D ≤ D ^ (a / 2) / (a / 2) :=
    Real.log_le_rpow_div hD0.le (by positivity)
  have hKD : K ≤ D ^ (a / 2) := by
    calc K = (K ^ (2 / a)) ^ (a / 2) := by
          rw [← Real.rpow_mul (by linarith)]
          rw [show 2 / a * (a / 2) = 1 by field_simp, Real.rpow_one]
      _ ≤ D ^ (a / 2) := Real.rpow_le_rpow (by positivity) hD (by positivity)
  have hsplit : D ^ a = D ^ (a / 2) * D ^ (a / 2) := by
    rw [← Real.rpow_add hD0]; congr 1; ring
  have hpos : 0 < D ^ (a / 2) := Real.rpow_pos_of_pos hD0 _
  calc A * Real.log D ≤ A * (D ^ (a / 2) / (a / 2)) := mul_le_mul_of_nonneg_left hlog hA
    _ = (2 * A / a) * D ^ (a / 2) := by field_simp
    _ ≤ K * D ^ (a / 2) := by
        apply mul_le_mul_of_nonneg_right _ hpos.le
        rw [hK]; linarith
    _ ≤ D ^ (a / 2) * D ^ (a / 2) := mul_le_mul_of_nonneg_right hKD hpos.le
    _ = D ^ a := hsplit.symm

/-- The machine threshold `D₀`: `200 ≤ 𝓛`, (T1), (T2) all hold for `D ≥ D₀`. -/
theorem thresholds_eventually : ∃ D₀ : ℝ, 1 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    200 ≤ Real.log D
    ∧ 2 * 10 ^ 14 * Ctau * Real.log D ≤ D ^ (79 / 4000 : ℝ)
    ∧ 320000 * C12 * C11 * Real.log D ≤ D ^ (13 / 500 : ℝ) := by
  have hC11 : 0 < C11 := by
    rw [C11]; have := GammaStrip.CGamma_pos; have := Ctau_pos; positivity
  have hCt := Ctau_pos
  obtain ⟨D₁, hD₁1, hD₁⟩ := log_le_rpow_eventually
    (A := 2 * 10 ^ 14 * Ctau) (a := 79 / 4000) (by positivity) (by norm_num)
  obtain ⟨D₂, hD₂1, hD₂⟩ := log_le_rpow_eventually
    (A := 320000 * C12 * C11) (a := 13 / 500) (by have := C12_pos; positivity) (by norm_num)
  refine ⟨max (Real.exp 200) (max D₁ D₂), ?_, fun D hD => ⟨?_, ?_, ?_⟩⟩
  · exact le_trans hD₁1 (le_trans (le_max_left _ _) (le_max_right _ _))
  · have h : Real.exp 200 ≤ D := le_trans (le_max_left _ _) hD
    have hD0 : 0 < D := lt_of_lt_of_le (Real.exp_pos _) h
    have := Real.log_le_log (Real.exp_pos _) h
    rwa [Real.log_exp] at this
  · exact hD₁ D (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hD)
  · exact hD₂ D (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hD)

/-- The Mertens hypothesis (blueprint I9(c), last step; Mertens' third theorem in upper-bound
form).  Carried as a named hypothesis (routez/Z0b-density.md §12.3 authorises this). -/
def MertensHyp : Prop :=
  ∃ CM : ℝ, 0 ≤ CM ∧ ∀ R : ℝ, 2 ≤ R → MertensProd R ≤ CM * Real.log R

/-- `R = D^{1/100} ≥ 2` once `log D ≥ 200`. -/
lemma two_le_Rpar {D : ℝ} (hD : 0 < D) (hLD : 200 ≤ Real.log D) : 2 ≤ Rpar D := by
  rw [Rpar, Real.rpow_def_of_pos hD]
  have := Real.add_one_le_exp (Real.log D * (1 / 100))
  linarith

/-- **Theorem M (frozen form).**  Under the Mertens hypothesis there are `γ_m ≥ 0` and
`D₀ ≥ 1` such that for every modulus `d`, `t ≥ 2`, `σ ∈ [99/100, 1]` and `d(t+2) ≥ D₀`:
`∑_{χ ≠ χ₀} N(σ,t,χ) ≤ γ_m·(d(t+2))^{(5/2)(1−σ)}`.  Log-free. -/
theorem sum_zeroCountBox_nonprincipal_le_of_mertens (hM : MertensHyp) :
    ∃ γm D₀ : ℝ, 0 ≤ γm ∧ 1 ≤ D₀ ∧
      ∀ (d : ℕ) [NeZero d] (t σ : ℝ), 2 ≤ t → 99 / 100 ≤ σ → σ ≤ 1 →
        D₀ ≤ (d : ℝ) * (t + 2) →
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            (zeroCountBox χ σ t : ℝ)
          ≤ γm * ((d : ℝ) * (t + 2)) ^ ((5 / 2 : ℝ) * (1 - σ)) := by
  obtain ⟨CM, hCM, hMer⟩ := hM
  obtain ⟨D₀, hD₀1, hD₀⟩ := thresholds_eventually
  refine ⟨gamM CM, D₀, gamM_nonneg hCM, hD₀1, ?_⟩
  intro d _ t σ ht hσ hσ1 hD
  obtain ⟨hL, hT1, hT2⟩ := hD₀ _ hD
  have hD0 : 0 < (d : ℝ) * (t + 2) := by linarith
  exact sum_zeroCountBox_nonprincipal_le_of_thresholds hσ hσ1 (by linarith) hL hT1 hT2 hCM
    (hMer _ (two_le_Rpar hD0 hL))

/-! ## §4 Theorem Z: the principal character (blueprint §9) -/

/-- `C₆ = log(3200·e·60)`, the constant of the `χ₀` height clause `Λ₀(σ) ≤ |Im ρ|`. -/
def C6 : ℝ := Real.log (3200 * Real.exp 1 * 60)

lemma C6_nonneg : 0 ≤ C6 := by
  rw [C6]
  have := Real.add_one_le_exp (1 : ℝ)
  exact Real.log_nonneg (by nlinarith)

/-- **The §9 thresholds** (`𝓛_a, 𝓛_b, 𝓛_c` of the blueprint, folded): for `L ≥ L₀(c, C)`,
`log L ≤ L/4`, `(log L)² ≤ c²L`, `C + 3 ≤ L/2`. -/
lemma band_thresholds {c C : ℝ} (hc : 0 < c) : ∃ L₀ : ℝ, 200 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
    Real.log L ≤ L / 4 ∧ (Real.log L) ^ 2 ≤ c ^ 2 * L ∧ C + 3 ≤ L / 2 := by
  refine ⟨max 200 (max ((16 / c ^ 2) ^ 2) (2 * (C + 3))), le_max_left _ _, fun L hL => ?_⟩
  have h200 : 200 ≤ L := le_trans (le_max_left _ _) hL
  have h16 : (16 / c ^ 2) ^ 2 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hC : 2 * (C + 3) ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL0 : 0 < L := by linarith
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  set s : ℝ := L ^ (1 / 2 : ℝ) with hs
  set q : ℝ := L ^ (1 / 4 : ℝ) with hq
  have hs0 : 0 ≤ s := Real.rpow_nonneg hL0.le _
  have hq0 : 0 ≤ q := Real.rpow_nonneg hL0.le _
  have hs2 : s ^ 2 = L := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hq2 : q ^ 2 = s := by
    rw [hq, hs, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hlog2 : Real.log L ≤ 2 * s := by
    have := Real.log_le_rpow_div hL0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← hs] at this; linarith
  have hlog4 : Real.log L ≤ 4 * q := by
    have := Real.log_le_rpow_div hL0.le (by norm_num : (0 : ℝ) < 1 / 4)
    rw [← hq] at this; linarith
  have hs8 : 8 ≤ s := le_of_sq_le_sq (by rw [hs2]; linarith) hs0
  have hs16 : 16 / c ^ 2 ≤ s := le_of_sq_le_sq (by rw [hs2]; exact h16) hs0
  refine ⟨?_, ?_, by linarith⟩
  · nlinarith
  · have h1 : (Real.log L) ^ 2 ≤ (4 * q) ^ 2 := pow_le_pow_left₀ hlog0 hlog4 2
    have h2 : (4 * q) ^ 2 = 16 * s := by rw [mul_pow, hq2]; norm_num
    have hc2 : 0 < c ^ 2 := by positivity
    have h3 : 16 ≤ c ^ 2 * s := by
      rw [div_le_iff₀ hc2] at hs16; linarith
    calc (Real.log L) ^ 2 ≤ 16 * s := h1.trans_eq h2
      _ ≤ (c ^ 2 * s) * s := mul_le_mul_of_nonneg_right h3 hs0
      _ = c ^ 2 * L := by rw [← hs2]; ring

/-- `u⁴ ≤ e^{(5/2)u}` for `u ≥ 0`. -/
lemma pow_four_le_exp {u : ℝ} (hu : 0 ≤ u) : u ^ 4 ≤ Real.exp ((5 / 2) * u) := by
  have h := Real.pow_div_factorial_le_exp ((5 / 2) * u) (by positivity) 4
  have h4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h4] at h
  have : u ^ 4 ≤ ((5 / 2) * u) ^ 4 / 24 := by
    have hu4 : 0 ≤ u ^ 4 := by positivity
    nlinarith
  linarith

/-- **Theorem Z (blueprint §9), modulus `1`.**  Under the Mertens hypothesis there is
`γ_ζ ≥ 1` with `N_ζ(σ,t) ≤ γ_ζ·(t+2)^{(5/2)(1−σ)}` for all `t ≥ 2`, `σ ∈ [99/100, 1]`.
Effective: the small-height band is I6 at a fixed height (no compactness), band (b) is
I5 (`zeta_zero_re_lt`), band (c) is the machine at `d = 1` with `good ρ := Λ₀(σ) ≤ |Im ρ|`. -/
theorem zeroCountBox_one_le_density_of_mertens (hM : MertensHyp) :
    ∃ γζ : ℝ, 1 ≤ γζ ∧ ∀ t σ : ℝ, 2 ≤ t → 99 / 100 ≤ σ → σ ≤ 1 →
      (zeroCountBox (1 : DirichletCharacter ℂ 1) σ t : ℝ)
        ≤ γζ * (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) := by
  obtain ⟨CM, hCM, hMer⟩ := hM
  obtain ⟨D₀, hD₀1, hD₀⟩ := thresholds_eventually
  obtain ⟨c, hc0, _, hzf⟩ := zeta_zero_re_lt
  obtain ⟨L₀, hL₀200, hL₀⟩ := band_thresholds (c := c) (C := C6) hc0
  set ν₀ : ℝ := max D₀ (Real.exp L₀) with hν₀
  have hν₀1 : 1 ≤ ν₀ := le_trans hD₀1 (le_max_left _ _)
  have hlogν : 0 ≤ Real.log (ν₀ + 2) := Real.log_nonneg (by linarith)
  have hgm := gamM_nonneg hCM
  have hνlog : 0 ≤ 1120 * ν₀ * Real.log (ν₀ + 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hlogν
  refine ⟨1 + 1120 * ν₀ * Real.log (ν₀ + 2) + gamM CM + 1120, by linarith, ?_⟩
  intro t σ ht hσ hσ1
  have ht2 : 0 < t + 2 := by linarith
  have hbase : 1 ≤ (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) :=
    Real.one_le_rpow (by linarith) (by nlinarith)
  have hγ0 : 0 ≤ 1 + 1120 * ν₀ * Real.log (ν₀ + 2) + gamM CM + 1120 := by linarith
  by_cases hsmall : t + 2 ≤ ν₀
  · -- small height: I6 at the fixed height `ν₀`
    have h1 : (zeroCountBox (1 : DirichletCharacter ℂ 1) σ t : ℝ)
        ≤ (zeroCountBox (1 : DirichletCharacter ℂ 1) (1 / 2) t : ℝ) := by
      exact_mod_cast zeroCountBox_mono (by linarith : (1 / 2 : ℝ) ≤ σ)
    have h2 := zeroCountBox_one_le (by linarith : (1 : ℝ) ≤ t)
    have h3 : 1120 * t * Real.log (t + 2) ≤ 1120 * ν₀ * Real.log (ν₀ + 2) := by
      have hl : Real.log (t + 2) ≤ Real.log (ν₀ + 2) := Real.log_le_log ht2 (by linarith)
      have hl0 : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
      have : t ≤ ν₀ := by linarith
      nlinarith
    calc (zeroCountBox (1 : DirichletCharacter ℂ 1) σ t : ℝ)
        ≤ 1120 * ν₀ * Real.log (ν₀ + 2) := by linarith
      _ ≤ (1 + 1120 * ν₀ * Real.log (ν₀ + 2) + gamM CM + 1120) * 1 := by linarith
      _ ≤ (1 + 1120 * ν₀ * Real.log (ν₀ + 2) + gamM CM + 1120)
            * (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) := mul_le_mul_of_nonneg_left hbase hγ0
  · have hsmall' : ν₀ < t + 2 := not_le.mp hsmall
    -- large height: `D = t + 2 ≥ D₀` and `𝓛 ≥ L₀`
    have hDeq : ((1 : ℕ) : ℝ) * (t + 2) = t + 2 := by simp
    have hDD₀ : D₀ ≤ t + 2 := le_trans (le_max_left _ _) hsmall'.le
    obtain ⟨hL, hT1, hT2⟩ := hD₀ (t + 2) hDD₀
    have hL0 : 0 < Real.log (t + 2) := by linarith
    have hLL₀ : L₀ ≤ Real.log (t + 2) := by
      have := Real.log_le_log (Real.exp_pos _) (le_trans (le_max_right _ _) hsmall'.le)
      rwa [Real.log_exp] at this
    obtain ⟨hlogL, hlogsq, hC6⟩ := hL₀ _ hLL₀
    set 𝓛 : ℝ := Real.log (t + 2) with h𝓛
    set lam : ℝ := (1 - σ) * 𝓛 with hlam
    have hlam0 : 0 ≤ lam := mul_nonneg (by linarith) hL0.le
    have hlam100 : lam ≤ 𝓛 / 100 := by rw [hlam]; nlinarith
    set Λ : ℝ := Lambda0 (t + 2) σ C6 with hΛ
    have hΛeq : Λ = Real.log 𝓛 + (6 / 5) * lam + C6 := by rw [hΛ, Lambda0]
    have hlog𝓛1 : 1 ≤ Real.log 𝓛 := by
      have h3 : Real.exp 1 ≤ 𝓛 := by
        have := Real.exp_one_lt_d9; linarith
      have := Real.log_le_log (Real.exp_pos _) h3
      rwa [Real.log_exp] at this
    have hΛ1 : 1 ≤ Λ := by rw [hΛeq]; linarith [C6_nonneg]
    have hexp : Real.exp ((5 / 2) * lam) = (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) := by
      rw [Real.rpow_def_of_pos ht2, hlam]; congr 1; ring
    have hpow0 : 0 ≤ (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) := Real.rpow_nonneg ht2.le _
    -- the band split at `good ρ := Λ ≤ |Im ρ|`
    set good : ℂ → Prop := fun ρ => Λ ≤ |ρ.im| with hgood
    have hsplit : (zeroCountBox (1 : DirichletCharacter ℂ 1) σ t : ℝ)
        = ((∑ ρ ∈ (zeroFinset (1 : DirichletCharacter ℂ 1) σ t).filter good,
              analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ρ
              : ℕ) : ℝ)
          + ((∑ ρ ∈ (zeroFinset (1 : DirichletCharacter ℂ 1) σ t).filter (fun ρ => ¬ good ρ),
              analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ρ
              : ℕ) : ℝ) := by
      rw [zeroCountBox, ← Nat.cast_add, Finset.sum_filter_add_sum_filter_not]
    -- band (c): the machine at `d = 1`
    have hgoodc : ((∑ ρ ∈ (zeroFinset (1 : DirichletCharacter ℂ 1) σ t).filter good,
          analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ρ
          : ℕ) : ℝ) ≤ gamM CM * (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) := by
      have hg : ∀ χ ∈ ({1} : Finset (DirichletCharacter ℂ 1)), χ = 1 → ∀ ρ : ℂ, good ρ →
          Lambda0 (((1 : ℕ) : ℝ) * (t + 2)) σ (Real.log (3200 * Real.exp 1 * 60)) ≤ |ρ.im| := by
        intro χ _ _ ρ hρ
        rw [hDeq]; exact hρ
      have h := sum_good_le_density (d := 1) hσ hσ1 (by linarith) (by rw [hDeq]; exact hL)
        (by rw [hDeq]; exact hT1) (by rw [hDeq]; exact hT2) hg hCM
        (by rw [hDeq]; exact hMer _ (two_le_Rpar ht2 hL))
      rw [hDeq, Finset.sum_singleton] at h
      exact h
    -- bands (a)+(b): `|Im ρ| < Λ`
    have hbad : ((∑ ρ ∈ (zeroFinset (1 : DirichletCharacter ℂ 1) σ t).filter (fun ρ => ¬ good ρ),
          analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ρ
          : ℕ) : ℝ) ≤ 1120 * (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) := by
      by_cases hcase : lam ^ 2 ≤ 𝓛
      · -- the band is empty: the zero-free region excludes every zero with `|γ| < Λ`
        have hlam24 : lam ≤ 5 * 𝓛 / 24 :=
          le_of_sq_le_sq (by nlinarith) (by positivity)
        have hΛ3 : Λ + 3 ≤ 𝓛 := by rw [hΛeq]; linarith
        have hempty : ∀ ρ ∈ (zeroFinset (1 : DirichletCharacter ℂ 1) σ t).filter
            (fun ρ => ¬ good ρ), False := by
          intro ρ hρ
          rw [Finset.mem_filter, mem_zeroFinset] at hρ
          obtain ⟨⟨hβ, _, _, _, hLρ⟩, hng⟩ := hρ
          have hγ : |ρ.im| < Λ := not_le.mp hng
          rw [DirichletCharacter.LFunction_modOne_eq] at hLρ
          have hzero := hzf ρ hLρ
          have hpos3 : 0 < Real.log (|ρ.im| + 3) :=
            Real.log_pos (by linarith [abs_nonneg ρ.im])
          have hle3 : Real.log (|ρ.im| + 3) ≤ Real.log 𝓛 :=
            Real.log_le_log (by linarith [abs_nonneg ρ.im]) (by linarith)
          have hdiv : c / Real.log 𝓛 ≤ c / Real.log (|ρ.im| + 3) :=
            div_le_div_of_nonneg_left hc0.le hpos3 hle3
          -- `(1−σ)·log 𝓛 ≤ c` from `lam² ≤ 𝓛` and `(log 𝓛)² ≤ c²𝓛`
          have hlogL0 : 0 < Real.log 𝓛 := by linarith
          have hsq : (lam * Real.log 𝓛) ^ 2 ≤ (c * 𝓛) ^ 2 := by
            calc (lam * Real.log 𝓛) ^ 2 = lam ^ 2 * (Real.log 𝓛) ^ 2 := by ring
              _ ≤ 𝓛 * (c ^ 2 * 𝓛) := mul_le_mul hcase hlogsq (by positivity) hL0.le
              _ = (c * 𝓛) ^ 2 := by ring
          have hll : lam * Real.log 𝓛 ≤ c * 𝓛 := le_of_sq_le_sq hsq (by positivity)
          have h1σ : (1 - σ) * Real.log 𝓛 ≤ c := by
            have : ((1 - σ) * Real.log 𝓛) * 𝓛 ≤ c * 𝓛 := by
              rw [hlam] at hll; linarith [hll]
            exact le_of_mul_le_mul_right this hL0
          have h1σ' : 1 - σ ≤ c / Real.log 𝓛 := by
            rw [le_div_iff₀ hlogL0]; exact h1σ
          linarith
        have : ∑ ρ ∈ (zeroFinset (1 : DirichletCharacter ℂ 1) σ t).filter (fun ρ => ¬ good ρ),
            analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ρ
            = 0 := Finset.sum_eq_zero fun ρ hρ => (hempty ρ hρ).elim
        rw [this, Nat.cast_zero]
        positivity
      · -- crude count in the box `[1/2, 1] × [−Λ, Λ]`
        have hcase' : 𝓛 < lam ^ 2 := not_le.mp hcase
        have hsub : (zeroFinset (1 : DirichletCharacter ℂ 1) σ t).filter (fun ρ => ¬ good ρ)
            ⊆ zeroFinset (1 : DirichletCharacter ℂ 1) (1 / 2) Λ := by
          intro ρ hρ
          rw [Finset.mem_filter, mem_zeroFinset] at hρ
          obtain ⟨⟨hβ, hβ1, _, hne, hLρ⟩, hng⟩ := hρ
          have hγ : |ρ.im| < Λ := not_le.mp hng
          rw [mem_zeroFinset]
          exact ⟨by linarith, hβ1, hγ.le, hne, hLρ⟩
        have h1 : ((∑ ρ ∈ (zeroFinset (1 : DirichletCharacter ℂ 1) σ t).filter
              (fun ρ => ¬ good ρ),
              analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ρ
              : ℕ) : ℝ)
            ≤ (zeroCountBox (1 : DirichletCharacter ℂ 1) (1 / 2) Λ : ℝ) := by
          rw [zeroCountBox]
          exact_mod_cast Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
        have h2 := zeroCountBox_one_le hΛ1
        have hΛ2 : Λ + 2 ≤ 𝓛 := by rw [hΛeq]; linarith
        have h3 : Real.log (Λ + 2) ≤ 𝓛 := by
          have := Real.log_le_sub_one_of_pos (by linarith : 0 < Λ + 2); linarith
        have h4 : 1120 * Λ * Real.log (Λ + 2) ≤ 1120 * 𝓛 * 𝓛 := by
          have hl0 : 0 ≤ Real.log (Λ + 2) := Real.log_nonneg (by linarith)
          have hΛ𝓛 : Λ ≤ 𝓛 := by linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left hΛ𝓛 (by norm_num)) h3 hl0 (by positivity)
        -- `𝓛² < lam⁴ ≤ e^{(5/2)lam}`
        have h5 : 𝓛 ^ 2 ≤ Real.exp ((5 / 2) * lam) := by
          have h6 : 𝓛 ^ 2 ≤ lam ^ 4 := by
            have := pow_le_pow_left₀ hL0.le hcase'.le 2
            calc 𝓛 ^ 2 ≤ (lam ^ 2) ^ 2 := this
              _ = lam ^ 4 := by ring
          exact h6.trans (pow_four_le_exp hlam0)
        rw [hexp] at h5
        calc ((∑ ρ ∈ (zeroFinset (1 : DirichletCharacter ℂ 1) σ t).filter (fun ρ => ¬ good ρ),
              analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ρ
              : ℕ) : ℝ)
            ≤ 1120 * 𝓛 * 𝓛 := le_trans h1 (le_trans h2 h4)
          _ = 1120 * 𝓛 ^ 2 := by ring
          _ ≤ 1120 * (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) := by
              apply mul_le_mul_of_nonneg_left h5 (by norm_num)
    rw [hsplit]
    calc _ ≤ gamM CM * (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ))
          + 1120 * (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) := add_le_add hgoodc hbad
      _ = (gamM CM + 1120) * (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) := by ring
      _ ≤ (1 + 1120 * ν₀ * Real.log (ν₀ + 2) + gamM CM + 1120)
            * (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) :=
          mul_le_mul_of_nonneg_right (by linarith) hpow0

/-- **Theorem Z (frozen form), every modulus.**  `N(σ,t,χ₀) ≤ γ_ζ·(t+2)^{(5/2)(1−σ)}` for
all `d`, `t ≥ 2`, `σ ∈ [99/100, 1]` (the Euler factors of `L(s,χ₀) = ζ(s)∏_{p∣d}(1−p^{−s})`
do not vanish on `Re s > 0`: `zeroCountBox_trivChar_eq`). -/
theorem zeroCountBox_trivChar_le_density_of_mertens (hM : MertensHyp) :
    ∃ γζ : ℝ, 1 ≤ γζ ∧ ∀ (d : ℕ) [NeZero d] (t σ : ℝ), 2 ≤ t → 99 / 100 ≤ σ → σ ≤ 1 →
      (zeroCountBox (1 : DirichletCharacter ℂ d) σ t : ℝ)
        ≤ γζ * (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) := by
  obtain ⟨γζ, hγ1, h⟩ := zeroCountBox_one_le_density_of_mertens hM
  refine ⟨γζ, hγ1, fun d _ t σ ht hσ hσ1 => ?_⟩
  rw [zeroCountBox_trivChar_eq d (by linarith : (0 : ℝ) < σ)]
  exact h t σ ht hσ hσ1

/-! ## §5 Theorem A: assembly of the frozen log-free interface (blueprint §10) -/

/-- I6 absorption: `∑_χ N(σ,t,χ) ≤ 1120·(d(t+2))²` for `t ≥ 1`, `σ ≥ 1/2`. -/
lemma sum_zeroCountBox_le_sq {d : ℕ} [NeZero d] {t σ : ℝ} (ht : 1 ≤ t) (hσ : 1 / 2 ≤ σ) :
    ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ) ≤ 1120 * ((d : ℝ) * (t + 2)) ^ 2 := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hD1 : 1 ≤ (d : ℝ) * (t + 2) := by nlinarith
  have h1 : ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
      ≤ ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ (1 / 2) t : ℝ) :=
    Finset.sum_le_sum fun χ _ => by exact_mod_cast zeroCountBox_mono hσ
  have h2 := Carmichael.sum_zeroCountBox_le d ht
  have hlog : Real.log ((d : ℝ) * (t + 2)) ≤ (d : ℝ) * (t + 2) := by
    have := Real.log_le_sub_one_of_pos (by linarith : 0 < (d : ℝ) * (t + 2)); linarith
  have hlog0 : 0 ≤ Real.log ((d : ℝ) * (t + 2)) := Real.log_nonneg hD1
  have htd : t * (d : ℝ) ≤ (d : ℝ) * (t + 2) := by nlinarith
  calc ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
      ≤ 1120 * t * d * Real.log ((d : ℝ) * (t + 2)) := h1.trans h2
    _ = 1120 * ((t * d) * Real.log ((d : ℝ) * (t + 2))) := by ring
    _ ≤ 1120 * (((d : ℝ) * (t + 2)) * ((d : ℝ) * (t + 2))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul htd hlog hlog0 (by linarith)
    _ = 1120 * ((d : ℝ) * (t + 2)) ^ 2 := by ring

/-- `t + 2 ≤ 2t` and `d(t+2) ≤ 2·d·t^{c₀}` for `t ≥ 2`, `c₀ ≥ 1`. -/
lemma scale_le_two_mul {d : ℕ} [NeZero d] {t c₀ : ℝ} (ht : 2 ≤ t) (hc₀ : 1 ≤ c₀) :
    (d : ℝ) * (t + 2) ≤ 2 * ((d : ℝ) * t ^ c₀) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have htc : t ≤ t ^ c₀ := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ t) hc₀
    rwa [Real.rpow_one] at this
  nlinarith

/-- `1 ≤ d·t^{c₀}` (indeed `≥ 2`). -/
lemma two_le_scale' {d : ℕ} [NeZero d] {t c₀ : ℝ} (ht : 2 ≤ t) (hc₀ : 1 ≤ c₀) :
    2 ≤ (d : ℝ) * t ^ c₀ := by
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have htc : t ≤ t ^ c₀ := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ t) hc₀
    rwa [Real.rpow_one] at this
  nlinarith

/-- **Theorem H (blueprint §10, middle range), log-absorbed form.**  From the logged density
with profile `P ≤ 7/2`: on `σ ∈ [9/10, 99/100]`, `∑_χ N(σ,t,χ) ≤ C_H·(400(K+1))^K·
(d t^{c₀})^{(9/2)(1−σ)}` — the gap `(9/2 − P)(1−σ) ≥ 1/100` absorbs `log^K(d(t+2))
≤ (400(K+1))^K·(d t^{c₀})^{1/200}`, with no threshold. -/
theorem theoremH {CH P c₀ : ℝ} {K : ℕ} (_hP0 : 0 ≤ P) (hP : P ≤ 7 / 2) (hc₀ : 1 ≤ c₀)
    (hlog : ∀ (d : ℕ) [NeZero d] (t σ : ℝ), 2 ≤ t → 39 / 50 ≤ σ → σ ≤ 1 →
      ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
        ≤ CH * ((d : ℝ) * t ^ c₀) ^ (P * (1 - σ)) * Real.log ((d : ℝ) * (t + 2)) ^ K)
    (d : ℕ) [NeZero d] (t σ : ℝ) (ht : 2 ≤ t) (hσ : 9 / 10 ≤ σ) (hσ1 : σ ≤ 99 / 100) :
    ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
      ≤ CH * (400 * ((K : ℝ) + 1)) ^ K * ((d : ℝ) * t ^ c₀) ^ ((9 / 2 : ℝ) * (1 - σ)) := by
  set E : ℝ := (d : ℝ) * t ^ c₀ with hE
  have hE2 : 2 ≤ E := two_le_scale' ht hc₀
  have hE0 : 0 < E := by linarith
  have hE1 : 1 ≤ E := by linarith
  have hlogE0 : 0 ≤ Real.log E := Real.log_nonneg hE1
  have hCH0 : 0 ≤ CH := by
    -- from the logged bound at any point: the left side is nonnegative
    have h := hlog d t σ ht (by linarith) (by linarith)
    have hL : 0 ≤ ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    by_contra hneg
    push Not at hneg
    have hEp : 0 < E ^ (P * (1 - σ)) := Real.rpow_pos_of_pos hE0 _
    have hlogD : 0 < Real.log ((d : ℝ) * (t + 2)) := by
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
      exact Real.log_pos (by nlinarith)
    have hlogK : 0 < Real.log ((d : ℝ) * (t + 2)) ^ K := pow_pos hlogD K
    have : CH * E ^ (P * (1 - σ)) * Real.log ((d : ℝ) * (t + 2)) ^ K < 0 := by
      have := mul_pos hEp hlogK
      nlinarith
    linarith
  -- `log(d(t+2)) ≤ 2 log E`
  have hlogD : Real.log ((d : ℝ) * (t + 2)) ≤ 2 * Real.log E := by
    have h1 : Real.log ((d : ℝ) * (t + 2)) ≤ Real.log (2 * E) := by
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
      exact Real.log_le_log (by nlinarith) (scale_le_two_mul ht hc₀)
    have h2 : Real.log (2 * E) = Real.log 2 + Real.log E := Real.log_mul (by norm_num) hE0.ne'
    have h3 : Real.log 2 ≤ Real.log E := Real.log_le_log (by norm_num) hE2
    linarith
  have hlogD0 : 0 ≤ Real.log ((d : ℝ) * (t + 2)) := by
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
    exact Real.log_nonneg (by nlinarith)
  -- `2 log E ≤ 400(K+1)·E^{1/(200(K+1))}`
  set ε : ℝ := 1 / (200 * ((K : ℝ) + 1)) with hε
  have hK0 : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hε0 : 0 < ε := by positivity
  have hlogE : 2 * Real.log E ≤ 400 * ((K : ℝ) + 1) * E ^ ε := by
    have := Real.log_le_rpow_div hE0.le hε0
    have h2 : E ^ ε / ε = 200 * ((K : ℝ) + 1) * E ^ ε := by rw [hε]; field_simp
    linarith
  have hEε0 : 0 ≤ E ^ ε := Real.rpow_nonneg hE0.le _
  -- `log^K(d(t+2)) ≤ (400(K+1))^K · E^{εK} ≤ (400(K+1))^K · E^{1/200}`
  have hpowK : Real.log ((d : ℝ) * (t + 2)) ^ K
      ≤ (400 * ((K : ℝ) + 1)) ^ K * E ^ (1 / 200 : ℝ) := by
    calc Real.log ((d : ℝ) * (t + 2)) ^ K
        ≤ (400 * ((K : ℝ) + 1) * E ^ ε) ^ K :=
          pow_le_pow_left₀ hlogD0 (hlogD.trans hlogE) K
      _ = (400 * ((K : ℝ) + 1)) ^ K * (E ^ ε) ^ K := mul_pow _ _ _
      _ = (400 * ((K : ℝ) + 1)) ^ K * E ^ (ε * K) := by
          rw [Real.rpow_mul_natCast hE0.le]
      _ ≤ (400 * ((K : ℝ) + 1)) ^ K * E ^ (1 / 200 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.rpow_le_rpow_of_exponent_le hE1
          rw [hε, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  -- the exponent gap
  have hexp : E ^ (P * (1 - σ)) * E ^ (1 / 200 : ℝ) ≤ E ^ ((9 / 2 : ℝ) * (1 - σ)) := by
    rw [← Real.rpow_add hE0]
    apply Real.rpow_le_rpow_of_exponent_le hE1
    nlinarith
  have hEP0 : 0 ≤ E ^ (P * (1 - σ)) := Real.rpow_nonneg hE0.le _
  calc ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
      ≤ CH * E ^ (P * (1 - σ)) * Real.log ((d : ℝ) * (t + 2)) ^ K :=
        hlog d t σ ht (by linarith) (by linarith)
    _ ≤ CH * E ^ (P * (1 - σ)) * ((400 * ((K : ℝ) + 1)) ^ K * E ^ (1 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left hpowK (by positivity)
    _ = CH * (400 * ((K : ℝ) + 1)) ^ K * (E ^ (P * (1 - σ)) * E ^ (1 / 200 : ℝ)) := by ring
    _ ≤ CH * (400 * ((K : ℝ) + 1)) ^ K * E ^ ((9 / 2 : ℝ) * (1 - σ)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)

/-- **Theorem A = the frozen log-free interface.**  Under the Mertens hypothesis, the logged
density (`LoggedDensity`, any uniform profile `P ≤ 7/2`, `c₀ ∈ [1, 5/4]`) implies the log-free
density `LogFreeDensity` (coefficient `9/2`, `c₀' := c₀`).  The three ranges: `σ ≥ 99/100`,
`d(t+2) ≥ D₀` — Theorem M + Theorem Z at coefficient `5/2`; `σ ≥ 99/100`, `d(t+2) < D₀` — I6;
`σ ∈ [9/10, 99/100)` — Theorem H.  No power of `log` survives anywhere. -/
theorem logfree_of_logged_of_mertens (hM : MertensHyp) (h : LoggedDensity) : LogFreeDensity := by
  obtain ⟨CH, P, c₀, K, hCH, hP0, hP, hc₀, hc₀', hlog⟩ := h
  obtain ⟨γm, D₀, hγm, hD₀, hMthm⟩ := sum_zeroCountBox_nonprincipal_le_of_mertens hM
  obtain ⟨γζ, hγζ, hZ⟩ := zeroCountBox_trivChar_le_density_of_mertens hM
  set γH : ℝ := CH * (400 * ((K : ℝ) + 1)) ^ K with hγH
  have hγH0 : 0 ≤ γH := by rw [hγH]; positivity
  set γ₂ : ℝ := 2 * (γm + γζ) + 1120 * D₀ ^ 2 + γH + 1 with hγ₂
  refine ⟨γ₂, c₀, by rw [hγ₂]; nlinarith, hc₀, by linarith, ?_⟩
  intro d _ t σ ht hσ hσ1
  set E : ℝ := (d : ℝ) * t ^ c₀ with hE
  have hE2 : 2 ≤ E := two_le_scale' ht hc₀
  have hE0 : 0 < E := by linarith
  have hE1 : 1 ≤ E := by linarith
  have hbase : 1 ≤ E ^ ((9 / 2 : ℝ) * (1 - σ)) := Real.one_le_rpow hE1 (by nlinarith)
  have hbase0 : 0 ≤ E ^ ((9 / 2 : ℝ) * (1 - σ)) := by linarith
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  set D : ℝ := (d : ℝ) * (t + 2) with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  have hγ₂0 : 0 ≤ γ₂ := by rw [hγ₂]; nlinarith
  by_cases hσ99 : 99 / 100 ≤ σ
  · by_cases hDD₀ : D₀ ≤ D
    · -- Theorem M + Theorem Z
      have hsplit : ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
          = (zeroCountBox (1 : DirichletCharacter ℂ d) σ t : ℝ)
            + ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
                (zeroCountBox χ σ t : ℝ) :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm
      have hMz := hMthm d t σ ht hσ99 hσ1 hDD₀
      have hZz := hZ d t σ ht hσ99 hσ1
      have hexp0 : 0 ≤ (5 / 2 : ℝ) * (1 - σ) := by nlinarith
      have ht2D : (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) ≤ D ^ ((5 / 2 : ℝ) * (1 - σ)) :=
        Real.rpow_le_rpow (by linarith) (by rw [hD]; nlinarith) hexp0
      have hD2E : D ^ ((5 / 2 : ℝ) * (1 - σ)) ≤ 2 * E ^ ((9 / 2 : ℝ) * (1 - σ)) := by
        calc D ^ ((5 / 2 : ℝ) * (1 - σ)) ≤ (2 * E) ^ ((5 / 2 : ℝ) * (1 - σ)) :=
              Real.rpow_le_rpow hD0.le (scale_le_two_mul ht hc₀) hexp0
          _ = 2 ^ ((5 / 2 : ℝ) * (1 - σ)) * E ^ ((5 / 2 : ℝ) * (1 - σ)) :=
              Real.mul_rpow (by norm_num) hE0.le
          _ ≤ 2 * E ^ ((9 / 2 : ℝ) * (1 - σ)) := by
              apply mul_le_mul
              · have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
                  (by nlinarith : (5 / 2 : ℝ) * (1 - σ) ≤ 1)
                rwa [Real.rpow_one] at this
              · exact Real.rpow_le_rpow_of_exponent_le hE1 (by nlinarith)
              · exact Real.rpow_nonneg hE0.le _
              · norm_num
      have hDpow0 : 0 ≤ D ^ ((5 / 2 : ℝ) * (1 - σ)) := Real.rpow_nonneg hD0.le _
      calc ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
          = (zeroCountBox (1 : DirichletCharacter ℂ d) σ t : ℝ)
            + ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
                (zeroCountBox χ σ t : ℝ) := hsplit
        _ ≤ γζ * (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) + γm * D ^ ((5 / 2 : ℝ) * (1 - σ)) :=
            add_le_add hZz hMz
        _ ≤ γζ * D ^ ((5 / 2 : ℝ) * (1 - σ)) + γm * D ^ ((5 / 2 : ℝ) * (1 - σ)) := by
            have := mul_le_mul_of_nonneg_left ht2D (by linarith : (0 : ℝ) ≤ γζ)
            linarith
        _ = (γm + γζ) * D ^ ((5 / 2 : ℝ) * (1 - σ)) := by ring
        _ ≤ (γm + γζ) * (2 * E ^ ((9 / 2 : ℝ) * (1 - σ))) :=
            mul_le_mul_of_nonneg_left hD2E (by linarith)
        _ = (2 * (γm + γζ)) * E ^ ((9 / 2 : ℝ) * (1 - σ)) := by ring
        _ ≤ γ₂ * E ^ ((9 / 2 : ℝ) * (1 - σ)) := by
            apply mul_le_mul_of_nonneg_right _ hbase0
            rw [hγ₂]; nlinarith
    · -- small `D`: I6
      have hlt : D < D₀ := not_le.mp hDD₀
      have h1 := sum_zeroCountBox_le_sq (d := d) (σ := σ) (by linarith : (1 : ℝ) ≤ t)
        (by linarith)
      have h2 : D ^ 2 ≤ D₀ ^ 2 := pow_le_pow_left₀ hD0.le hlt.le 2
      calc ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
          ≤ 1120 * D ^ 2 := h1
        _ ≤ 1120 * D₀ ^ 2 := by linarith
        _ ≤ γ₂ * 1 := by rw [hγ₂]; nlinarith
        _ ≤ γ₂ * E ^ ((9 / 2 : ℝ) * (1 - σ)) := mul_le_mul_of_nonneg_left hbase hγ₂0
  · -- Theorem H
    have hσ99' : σ ≤ 99 / 100 := (not_le.mp hσ99).le
    have hH := theoremH hP0 hP hc₀ hlog d t σ ht hσ hσ99'
    calc ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
        ≤ γH * E ^ ((9 / 2 : ℝ) * (1 - σ)) := hH
      _ ≤ γ₂ * E ^ ((9 / 2 : ℝ) * (1 - σ)) := by
          apply mul_le_mul_of_nonneg_right _ hbase0
          rw [hγ₂]; nlinarith

section Mertens

open ArithmeticFunction

/-! ## §6 Mertens' third theorem, upper bound: `∏_{p ≤ R}(1 − 1/p)⁻¹ ≤ C_M log R` -/

/-- `T(m) = ∑_{0 < j ≤ m} Λ(j)/j`. -/
def Tsum (m : ℕ) : ℝ := ∑ j ∈ Ioc 0 m, (Λ j : ℝ) / j

lemma Tsum_succ (m : ℕ) : Tsum (m + 1) = Tsum m + (Λ (m + 1) : ℝ) / (m + 1 : ℕ) := by
  rw [Tsum, Tsum, sum_Ioc_succ_top (Nat.zero_le m)]

lemma Tsum_one : Tsum 1 = 0 := by
  rw [Tsum]
  simp [vonMangoldt_apply_one]

lemma Tsum_zero : Tsum 0 = 0 := by simp [Tsum]

/-- Mertens' first theorem (vendored): `T(m) ≤ log m + (log 4 + 4)` for `m ≥ 1`. -/
lemma Tsum_le {m : ℕ} (hm : 1 ≤ m) : Tsum m ≤ Real.log m + (Real.log 4 + 4) := by
  have h := Mertens.sum_mangoldt_div_eq_log (x := (m : ℝ)) (by exact_mod_cast hm)
  rw [Nat.floor_natCast] at h
  have := (abs_le.mp h).2
  rw [Tsum]; linarith

/-- The weights `f(i) = 1/log i` (Lean: `f 0 = f 1 = 0`). -/
def wlog (i : ℕ) : ℝ := (Real.log i)⁻¹

/-- **Discrete Abel summation**: `∑_{0<i≤N} f(i) Λ(i)/i = f(N) T(N) + ∑_{1≤i<N} (f(i) − f(i+1)) T(i)`. -/
lemma abel_identity (N : ℕ) (hN : 1 ≤ N) :
    ∑ i ∈ Ioc 0 N, wlog i * ((Λ i : ℝ) / i)
      = wlog N * Tsum N + ∑ i ∈ Ico 1 N, (wlog i - wlog (i + 1)) * Tsum i := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.eq_zero_or_pos N with rfl | hN0
    · simp [Tsum, wlog]
    · rw [sum_Ioc_succ_top (Nat.zero_le N), ih hN0, sum_Ico_succ_top hN0, Tsum_succ]
      push_cast
      ring

/-- `1 − log i / log(i+1) ≤ log log(i+1) − log log i` for `i ≥ 2`. -/
lemma one_sub_div_log_le {i : ℕ} (hi : 2 ≤ i) :
    1 - Real.log i / Real.log ((i : ℕ) + 1 : ℕ)
      ≤ Real.log (Real.log ((i : ℕ) + 1 : ℕ)) - Real.log (Real.log i) := by
  have hi1 : (1 : ℝ) < i := by exact_mod_cast hi
  have hl0 : 0 < Real.log i := Real.log_pos hi1
  have hl1 : 0 < Real.log ((i : ℕ) + 1 : ℕ) := Real.log_pos (by push_cast; linarith)
  have hy : 0 < Real.log ((i : ℕ) + 1 : ℕ) / Real.log i := div_pos hl1 hl0
  have h := Real.one_sub_inv_le_log_of_pos hy
  rw [Real.log_div hl1.ne' hl0.ne', inv_div] at h
  exact h

/-- `f(i) ≥ f(i+1)` for `i ≥ 2`. -/
lemma wlog_antitone {i : ℕ} (hi : 2 ≤ i) : wlog (i + 1) ≤ wlog i := by
  have hi1 : (1 : ℝ) < i := by exact_mod_cast hi
  have hl0 : 0 < Real.log i := Real.log_pos hi1
  have hle : Real.log i ≤ Real.log ((i : ℕ) + 1 : ℕ) :=
    Real.log_le_log (by linarith) (by push_cast; linarith)
  exact inv_anti₀ hl0 hle

lemma wlog_nonneg {i : ℕ} (hi : 1 ≤ i) : 0 ≤ wlog i := by
  rw [wlog]
  have : (1 : ℝ) ≤ i := by exact_mod_cast hi
  exact inv_nonneg.mpr (Real.log_nonneg this)

/-- Telescoping over `Ico 2 N`. -/
lemma sum_Ico_two_telescope (u : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ∑ i ∈ Ico 2 N, (u (i + 1) - u i) = u N - u 2 := by
  induction N with
  | zero => omega
  | succ N ih =>
    rcases Nat.lt_or_ge N 2 with h | h
    · have : N = 1 := by omega
      subst this; simp
    · rw [sum_Ico_succ_top h, ih h]; ring

/-- **Mertens' second theorem, upper form**: `∑_{p ≤ N} 1/p ≤ log log N + C₀` for `N ≥ 2`,
`C₀ = 1 + 2(log 4 + 4)/log 2 − log log 2`. -/
theorem sum_prime_inv_le {N : ℕ} (hN : 2 ≤ N) :
    ∑ p ∈ (Ioc 0 N).filter Nat.Prime, (p : ℝ)⁻¹
      ≤ Real.log (Real.log N) + (1 + 2 * (Real.log 4 + 4) / Real.log 2 - Real.log (Real.log 2)) := by
  set c : ℝ := Real.log 4 + 4 with hc
  have hc0 : 0 ≤ c := by rw [hc]; have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4); linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hlog2N : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
  -- Step 1: the prime sum is dominated by the `Λ`-weighted sum
  have h1 : ∑ p ∈ (Ioc 0 N).filter Nat.Prime, (p : ℝ)⁻¹
      ≤ ∑ i ∈ Ioc 0 N, wlog i * ((Λ i : ℝ) / i) := by
    have heq : ∀ p ∈ (Ioc 0 N).filter Nat.Prime, (p : ℝ)⁻¹ = wlog p * ((Λ p : ℝ) / p) := by
      intro p hp
      have hpp : p.Prime := (mem_filter.mp hp).2
      rw [wlog, vonMangoldt_apply_prime hpp]
      have hl : Real.log p ≠ 0 := by
        have : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
        exact (Real.log_pos this).ne'
      field_simp
    rw [sum_congr rfl heq]
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro i hi _
    rw [mem_Ioc] at hi
    exact mul_nonneg (wlog_nonneg hi.1) (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
  -- Step 2: Abel summation
  rw [abel_identity N (by omega)] at h1
  -- Step 3: the boundary term
  have h2 : wlog N * Tsum N ≤ 1 + c / Real.log 2 := by
    have hT := Tsum_le (m := N) (by omega)
    have hw : wlog N = (Real.log N)⁻¹ := rfl
    have hw0 : 0 ≤ wlog N := wlog_nonneg (by omega)
    calc wlog N * Tsum N ≤ wlog N * (Real.log N + c) := mul_le_mul_of_nonneg_left hT hw0
      _ = 1 + c * (Real.log N)⁻¹ := by rw [hw]; field_simp
      _ ≤ 1 + c / Real.log 2 := by
          have : (Real.log N)⁻¹ ≤ (Real.log 2)⁻¹ := inv_anti₀ hlog2 hlog2N
          have := mul_le_mul_of_nonneg_left this hc0
          rw [div_eq_mul_inv]; linarith
  -- Step 4: the interior sum; the `i = 1` term vanishes (`T(1) = 0`)
  have h3 : ∑ i ∈ Ico 1 N, (wlog i - wlog (i + 1)) * Tsum i
      = ∑ i ∈ Ico 2 N, (wlog i - wlog (i + 1)) * Tsum i := by
    have hsplit : Ico 1 N = insert 1 (Ico 2 N) := by
      ext i; simp only [mem_Ico, mem_insert]; omega
    rw [hsplit, sum_insert (by simp), Tsum_one, mul_zero, zero_add]
  have h4 : ∑ i ∈ Ico 2 N, (wlog i - wlog (i + 1)) * Tsum i
      ≤ ∑ i ∈ Ico 2 N, ((Real.log (Real.log ((i : ℕ) + 1 : ℕ)) - Real.log (Real.log i))
          + c * (wlog i - wlog (i + 1))) := by
    apply sum_le_sum
    intro i hi
    rw [mem_Ico] at hi
    have hi2 : 2 ≤ i := hi.1
    have hi1 : (1 : ℝ) < i := by exact_mod_cast hi2
    have hl0 : 0 < Real.log i := Real.log_pos hi1
    have hl1 : 0 < Real.log ((i : ℕ) + 1 : ℕ) := Real.log_pos (by push_cast; linarith)
    have hanti : 0 ≤ wlog i - wlog (i + 1) := by linarith [wlog_antitone hi2]
    have hT := Tsum_le (m := i) (by omega)
    have hkey : (wlog i - wlog (i + 1)) * Real.log i
        = 1 - Real.log i / Real.log ((i : ℕ) + 1 : ℕ) := by
      simp only [wlog]
      field_simp
    calc (wlog i - wlog (i + 1)) * Tsum i
        ≤ (wlog i - wlog (i + 1)) * (Real.log i + c) := mul_le_mul_of_nonneg_left hT hanti
      _ = (wlog i - wlog (i + 1)) * Real.log i + c * (wlog i - wlog (i + 1)) := by ring
      _ = (1 - Real.log i / Real.log ((i : ℕ) + 1 : ℕ)) + c * (wlog i - wlog (i + 1)) := by
          rw [hkey]
      _ ≤ (Real.log (Real.log ((i : ℕ) + 1 : ℕ)) - Real.log (Real.log i))
            + c * (wlog i - wlog (i + 1)) := by
          linarith [one_sub_div_log_le hi2]
  -- Step 5: telescope
  have h5 : ∑ i ∈ Ico 2 N, ((Real.log (Real.log ((i : ℕ) + 1 : ℕ)) - Real.log (Real.log i))
          + c * (wlog i - wlog (i + 1)))
      = (Real.log (Real.log N) - Real.log (Real.log 2)) + c * (wlog 2 - wlog N) := by
    rw [sum_add_distrib, ← mul_sum]
    have hA := sum_Ico_two_telescope (fun i => Real.log (Real.log i)) hN
    have hB := sum_Ico_two_telescope (fun i => -wlog i) hN
    have hB' : ∑ i ∈ Ico 2 N, (wlog i - wlog (i + 1)) = wlog 2 - wlog N := by
      have : ∀ i, wlog i - wlog (i + 1) = -wlog (i + 1) - -wlog i := fun i => by ring
      simp only [this]; rw [hB]; ring
    rw [hB']
    congr 1
  have h6 : c * (wlog 2 - wlog N) ≤ c / Real.log 2 := by
    have hw2 : wlog 2 = (Real.log 2)⁻¹ := by simp [wlog]
    have hwN : 0 ≤ wlog N := wlog_nonneg (by omega)
    rw [hw2, div_eq_mul_inv]
    nlinarith
  have h7 : 2 * c / Real.log 2 = c / Real.log 2 + c / Real.log 2 := by ring
  rw [h3] at h1
  linarith

/-- `(1 − x)⁻¹ ≤ e^{x + 2x²}` for `0 ≤ x ≤ 1/2`. -/
lemma inv_one_sub_le_exp {x : ℝ} (_hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    (1 - x)⁻¹ ≤ Real.exp (x + 2 * x ^ 2) := by
  have h1x : 0 < 1 - x := by linarith
  have h1 : (1 - x)⁻¹ = 1 + x / (1 - x) := by field_simp; ring
  have h2 : x / (1 - x) ≤ x + 2 * x ^ 2 := by
    rw [div_le_iff₀ h1x]; nlinarith
  have h3 := Real.add_one_le_exp (x / (1 - x))
  have h4 : Real.exp (x / (1 - x)) ≤ Real.exp (x + 2 * x ^ 2) := Real.exp_le_exp.mpr h2
  linarith

/-- `∑_{1 < n ≤ M} 1/n² ≤ 1`. -/
lemma sum_Ioc_inv_sq_le_one (M : ℕ) : ∑ n ∈ Ioc 1 M, ((n : ℝ)⁻¹) ^ 2 ≤ 1 := by
  suffices h : ∀ M : ℕ, 1 ≤ M → ∑ n ∈ Ioc 1 M, ((n : ℝ)⁻¹) ^ 2 ≤ 1 - (M : ℝ)⁻¹ by
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · simp
    · have := h M hM
      have : (0 : ℝ) ≤ (M : ℝ)⁻¹ := by positivity
      linarith
  intro M hM
  induction M with
  | zero => omega
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with rfl | hM0
    · simp
    · rw [sum_Ioc_succ_top hM0]
      have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM0
      have h1 : (((M + 1 : ℕ) : ℝ)⁻¹) ^ 2 ≤ (M : ℝ)⁻¹ - ((M + 1 : ℕ) : ℝ)⁻¹ := by
        push_cast
        have hM0' : (0 : ℝ) < M := by linarith
        have hM1' : (0 : ℝ) < (M : ℝ) + 1 := by linarith
        rw [inv_pow]
        simp only [inv_eq_one_div]
        rw [div_sub_div _ _ hM0'.ne' hM1'.ne', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith [ih hM0]

/-- **Mertens' third theorem, upper bound (`MertensHyp` discharged).**
`∏_{p ≤ R}(1 − 1/p)⁻¹ ≤ C_M·log R` for all `R ≥ 2`, with
`C_M = exp(3 + 2(log 4 + 4)/log 2 − log log 2)`. -/
theorem mertensProd_le_log {R : ℝ} (hR : 2 ≤ R) :
    MertensProd R ≤ Real.exp (3 + 2 * (Real.log 4 + 4) / Real.log 2 - Real.log (Real.log 2))
      * Real.log R := by
  set N := ⌊R⌋₊ with hNdef
  have hN2 : 2 ≤ N := Nat.le_floor (by simpa using hR)
  have hR0 : 0 < R := by linarith
  have hNR : (N : ℝ) ≤ R := Nat.floor_le hR0.le
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN2
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hlogR : Real.log N ≤ Real.log R := Real.log_le_log (by linarith) hNR
  have hlogR0 : 0 < Real.log R := lt_of_lt_of_le hlogN hlogR
  have hprimes : primesLe R = (Ioc 0 N).filter Nat.Prime := by
    ext p; rw [mem_primesLe, mem_filter, mem_Ioc]
    constructor
    · rintro ⟨hp, hpN⟩; exact ⟨⟨hp.pos, hpN⟩, hp⟩
    · rintro ⟨⟨_, hpN⟩, hp⟩; exact ⟨hp, hpN⟩
  -- Step A: the product is at most `exp(∑ 1/p + 2∑ 1/p²) ≤ exp(∑ 1/p + 2)`
  have hA : MertensProd R ≤ Real.exp (∑ p ∈ primesLe R, ((p : ℝ)⁻¹ + 2 * ((p : ℝ)⁻¹) ^ 2)) := by
    rw [MertensProd, Real.exp_sum]
    apply prod_le_prod
    · intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesLe.mp hp).1.two_le
      have : (p : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hp2
      have : 0 < 1 - (p : ℝ)⁻¹ := by linarith
      positivity
    · intro p hp
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_primesLe.mp hp).1.two_le
      have h1 : (p : ℝ)⁻¹ ≤ 1 / 2 := by
        rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hp2
      exact inv_one_sub_le_exp (by positivity) h1
  have hsq : ∑ p ∈ primesLe R, 2 * ((p : ℝ)⁻¹) ^ 2 ≤ 2 := by
    rw [← mul_sum]
    have hsub : primesLe R ⊆ Ioc 1 N := by
      intro p hp
      rw [mem_primesLe] at hp
      rw [mem_Ioc]; exact ⟨hp.1.one_lt, hp.2⟩
    have := sum_le_sum_of_subset_of_nonneg hsub (f := fun p : ℕ => ((p : ℝ)⁻¹) ^ 2)
      (fun _ _ _ => by positivity)
    linarith [sum_Ioc_inv_sq_le_one N]
  have hB := sum_prime_inv_le hN2
  rw [← hprimes] at hB
  -- assemble
  have hsum : ∑ p ∈ primesLe R, ((p : ℝ)⁻¹ + 2 * ((p : ℝ)⁻¹) ^ 2)
      ≤ Real.log (Real.log R) + (3 + 2 * (Real.log 4 + 4) / Real.log 2 - Real.log (Real.log 2)) := by
    rw [sum_add_distrib]
    have hll : Real.log (Real.log N) ≤ Real.log (Real.log R) := Real.log_le_log hlogN hlogR
    linarith
  calc MertensProd R
      ≤ Real.exp (∑ p ∈ primesLe R, ((p : ℝ)⁻¹ + 2 * ((p : ℝ)⁻¹) ^ 2)) := hA
    _ ≤ Real.exp (Real.log (Real.log R)
          + (3 + 2 * (Real.log 4 + 4) / Real.log 2 - Real.log (Real.log 2))) :=
        Real.exp_le_exp.mpr hsum
    _ = Real.exp (3 + 2 * (Real.log 4 + 4) / Real.log 2 - Real.log (Real.log 2)) * Real.log R := by
        rw [Real.exp_add, Real.exp_log hlogR0]; ring


/-- **`MertensHyp` discharged**: `C_M = exp(3 + 2(log 4 + 4)/log 2 − log log 2)`. -/
theorem mertensHyp : MertensHyp :=
  ⟨Real.exp (3 + 2 * (Real.log 4 + 4) / Real.log 2 - Real.log (Real.log 2)),
    (Real.exp_pos _).le, fun _ hR => mertensProd_le_log hR⟩

end Mertens

/-! ## §7 The unconditional statements -/

/-- **Theorem M (frozen form), unconditional.** -/
theorem sum_zeroCountBox_nonprincipal_le :
    ∃ γm D₀ : ℝ, 0 ≤ γm ∧ 1 ≤ D₀ ∧
      ∀ (d : ℕ) [NeZero d] (t σ : ℝ), 2 ≤ t → 99 / 100 ≤ σ → σ ≤ 1 →
        D₀ ≤ (d : ℝ) * (t + 2) →
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ d)).erase 1,
            (zeroCountBox χ σ t : ℝ)
          ≤ γm * ((d : ℝ) * (t + 2)) ^ ((5 / 2 : ℝ) * (1 - σ)) :=
  sum_zeroCountBox_nonprincipal_le_of_mertens mertensHyp

/-- **Theorem Z (frozen form), unconditional.** -/
theorem zeroCountBox_trivChar_le_density :
    ∃ γζ : ℝ, 1 ≤ γζ ∧ ∀ (d : ℕ) [NeZero d] (t σ : ℝ), 2 ≤ t → 99 / 100 ≤ σ → σ ≤ 1 →
      (zeroCountBox (1 : DirichletCharacter ℂ d) σ t : ℝ)
        ≤ γζ * (t + 2) ^ ((5 / 2 : ℝ) * (1 - σ)) :=
  zeroCountBox_trivChar_le_density_of_mertens mertensHyp

/-- **THE FROZEN OUTPUT (Theorem A), unconditional**: the logged density implies the
log-free density. -/
theorem logfree_of_logged (h : LoggedDensity) : LogFreeDensity :=
  logfree_of_logged_of_mertens mertensHyp h

end

end ZeroDensity
end Carmichael
