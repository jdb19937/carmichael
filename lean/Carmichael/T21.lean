/-
Route Z, sortie Z9a: **T2.1** — the θ-in-progressions bound with exceptional set
at level 191/900 (routez/Z0a-ledger.md §4), assembled from the explicit formula
(Z5, `Carmichael.EF.explicit_formula`, C₅ = 10¹²), the crude zero count (Z4b,
`sum_zeroCountBox_le`, C₁ = 1120), the census (Z7, `Census.card_badConductors_le`
with `CensusMid.midCensusHyp`), the ζ box clearance (Z8, `zeta_box_clearance`),
and the two zone-density interfaces of `Carmichael/DensityInterface.lean`,
carried as the hypothesis `DensityInputs`.

STATEMENTS

  structure DensityInputs : Prop where
    logfree : LogFreeDensity      -- Z6d, log-free, coefficient 9/2, σ ∈ [9/10,1]
    logged  : LoggedDensity       -- Z6-logged, uniform profile P ≤ 7/2, σ ∈ [39/50,1]

  theorem theta_AP_T21 (hden : DensityInputs) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1/3) :
      ∃ D : ℕ, ∃ x₂ : ℝ, ∃ bad : ℕ → Finset ℕ,
        (∀ x, (bad x).card ≤ D) ∧ (∀ x, ∀ m ∈ bad x, 2 ≤ m) ∧
        ∀ (x : ℕ) (d : ℕ) [NeZero d] (a : ZMod d) (y : ℝ), x₂ ≤ x → IsUnit a →
          (d : ℝ) ≤ (x : ℝ) ^ (191/900 : ℝ) → (d : ℝ) * (x : ℝ) ^ (709/900 : ℝ) ≤ y →
          y ≤ x → (∀ m ∈ bad x, ¬ m ∣ d) →
          |thetaAP a y - y / d.totient| ≤ ε * y / d.totient

  `bad x = badSet ρ ν x₂ x`: the conductors `m ∈ [2, x^{191/900}]` carrying a
  primitive character with a zero in `[1 − ρ/log x, 1] × [−ν, ν]` (empty for
  `x < x₂`), `D = ⌈c₂(ν)·e^{(191/900)c₃ρ}⌉`.

DELIVERED (all under `Carmichael.T21`)
  * zero-set helpers; (L-γ) `Lgamma_char`/`Lgamma_sum` in the exact form
    `∑ ord/(1+|γ|) ≤ N(σ,T)/T + ∑_{1≤n≤⌊T⌋} N(σ,n)/(n(n+1))`;
  * the fold corollary `fold`: `N(σ,t,d) ≤ C(d t^c)^e L` on `2 ≤ t ≤ T` with
    `c e ≤ 1 − s` gives `∑ ord/(1+|γ|) ≤ C d^e L (2 + 1/s)`, T-free;
  * the level lemma `dpow_le`, the σ-grid `grid_bound` (step h, buckets by
    ⌊(β−σ₁)/h⌋) and its geometric evaluation `grid_geom` (h = 1/log x, constant 64);
  * zone sums `zoneSum`, the full sum `zeroSumTotal`, the split `zeroSumTotal_split`;
  * zones: `zoneI_le` (S_I ≤ 28000·d·log²x·y^{39/50} ≤ εy/27), `zoneII_le`
    (S_II ≤ 1856·5^K·C_H·y·(log x)^{−9/2} ≤ εy/27), `zoneIII_le`
    (S_III ≤ 256·γ₂·y·e^{−(9/200)ρ}), `zoneIV_le` (S_IV ≤ γ₂e^{28ρ}y/ν);
  * the exceptional set `badSet`, `badSet_ge_two`, `badSet_card_le`, and the zero
    transfer `no_zero_in_box` (imprimitive → inducing primitive character via
    `LFunction_eq_primitive_mul_prod`; conductor 1 and the principal character via ζ);
  * the explicit formula for every χ mod d, `explicit_formula_all` (principal
    character through the level-1 formula, `zeroFinset_trivChar_eq`, and
    `psiChar_one_sub_le`), the orthogonality assembly `psiAP_sub_le`, and
    `thetaAP_sub_le`; truncation `efErr_le`; the small terms `small_terms_le`.

CONSTANTS  T = x³; ρ = (200/9)·log(6912γ₂/ε); ν = 27γ₂e^{28ρ}/ε; C* = 50(K+2),
σ* = 1 − C*·log log x/log x, τ = 1 − ρ/log x; budget 17ε/27 (EF ε/9, zones 4ε/9,
prime powers + ω(d)-cushion 2ε/27).

THRESHOLDS (conjuncts of the eventually-statement defining x₂; log = log x)
  1. e^{10} ≤ x                                 (x ≥ 2, x^{709/900} ≥ 100, x^{191/900} ≥ 2)
  2. log² ≤ ε/(675·10¹²)·x^{293/1800}           (truncation, all three EF terms)
  3. log ≤ (ε/81)·x^{259/900}                   (prime powers 2√y·log y and ω(d)·log y)
  4. log² ≤ (ε/756000)·x^{7/900}                (zone I, κ = 7/900)
  5. 50112·5^K·C_H/ε ≤ log^{9/2}                (zone II)
  6. 18·C*·log log ≤ log                         (σ* ≥ 9/10, and the zone-III fold exponent ≤ 1/2)
  7. ρ/C* ≤ log log                              (σ* ≤ τ)
  8. max(ρ/(1−σ_ζ), 40ρ) ≤ log                  (τ ≥ σ_ζ from Z8; τ ≥ 39/40 for the census)

DELTAS VS. THE LEDGER (routez/Z0a-ledger.md)
  * Logged density is the uniform-profile form `LoggedDensity` (P ≤ 7/2) of
    `DensityInterface.lean`; fold exponent ≤ 77/80, fold constant 2 + 80/3 ≤ 29.
  * The σ-integral of §3.2/3.3 is replaced by a discrete σ-grid of step 1/log x;
    the resulting constant 64 replaces 1 + 200/9, so ρ is pinned at
    (200/9)·log(6912γ₂/ε) (real, no ceiling) instead of ⌈(200/9)·log(3600γ₂/ε)⌉.
  * Fold constants 29 (zone II) and 4 (zone III) replace 450 and 22; zone II's
    C_II is 1856·5^K·C_H; log(d(T+2)) ≤ 5 log x is used throughout (ledger: 4 log x).
  * (L-γ) is proved without the factor 8 and without min(n,T); the n = 1 bucket
    uses N(σ,1) ≤ N(σ,2) so density inputs are consumed only at t ≥ 2.
  * Prime powers: Mathlib's `ψ − θ ≤ 2√y·log y`; the imprimitive cushion ω(d)·log y
    is bounded crudely by d·log x and shares threshold 3 with it.
  * The principal character mod d ≥ 2 is handled through the N = 1 explicit
    formula (ζ) plus `ψ(y,χ₀) − ψ(y) = −∑_{(n,d)>1} Λ(n)`, not through
    `primitiveCharacter`; nonprincipal imprimitive χ use `explicit_formula` at level d.
  * `badSet` is empty below x₂, so `card ≤ D` holds for every x.
-/
import Carmichael.ExplicitFormula
import Carmichael.PsiTheta
import Carmichael.ZeroCount
import Carmichael.Census
import Carmichael.CensusMid
import Carmichael.ZetaBox
import Carmichael.LConvexityCorollaries
import Carmichael.DensityInterface
import Carmichael.BMembership

set_option autoImplicit false

namespace Carmichael.T21

open Complex Finset

/-! ### Zero-set helpers -/

section ZeroSets

variable {N : ℕ} [NeZero N]

lemma zeroFinset_eq_filter (χ : DirichletCharacter ℂ N) {σ₀ σ T : ℝ} (h : σ₀ ≤ σ) :
    zeroFinset χ σ T = (zeroFinset χ σ₀ T).filter (fun ρ : ℂ => σ ≤ ρ.re) := by
  ext ρ
  simp only [mem_zeroFinset, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨le_trans h h1, h2, h3, h4, h5⟩, h1⟩
  · rintro ⟨⟨_, h2, h3, h4, h5⟩, h1⟩
    exact ⟨h1, h2, h3, h4, h5⟩

lemma zeroFinset_subset_of_le (χ : DirichletCharacter ℂ N) {σ t t' : ℝ} (h : t ≤ t') :
    zeroFinset χ σ t ⊆ zeroFinset χ σ t' := by
  intro ρ hρ
  rw [mem_zeroFinset] at hρ ⊢
  exact ⟨hρ.1, hρ.2.1, le_trans hρ.2.2.1 h, hρ.2.2.2⟩

lemma zeroCountBox_real (χ : DirichletCharacter ℂ N) (σ T : ℝ) :
    (zeroCountBox χ σ T : ℝ)
      = ∑ ρ ∈ zeroFinset χ σ T,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
  rw [zeroCountBox]; push_cast; rfl

lemma zeroCountBox_mono_T (χ : DirichletCharacter ℂ N) {σ t t' : ℝ} (h : t ≤ t') :
    zeroCountBox χ σ t ≤ zeroCountBox χ σ t' :=
  Finset.sum_le_sum_of_subset (zeroFinset_subset_of_le χ h)

lemma re_lt_one_of_mem_zeroFinset {χ : DirichletCharacter ℂ N} {σ T : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ zeroFinset χ σ T) : ρ.re < 1 := by
  rw [mem_zeroFinset] at hρ
  obtain ⟨_, h2, _, h4, h5⟩ := hρ
  rcases lt_or_eq_of_le h2 with h | h
  · exact h
  · exact absurd h5 (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr h4) h.ge)

lemma ord_nonneg (χ : DirichletCharacter ℂ N) (ρ : ℂ) :
    (0:ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) :=
  Nat.cast_nonneg _

end ZeroSets

/-! ### The partial-summation lemma (L-γ) -/

section Lgamma

lemma one_div_telescope {a M : ℕ} (ha : 1 ≤ a) (haM : a ≤ M) :
    (1:ℝ) / a = 1 / M + ∑ n ∈ Finset.Ico a M, 1 / ((n:ℝ) * (n + 1)) := by
  induction M, haM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ico_succ_top hM, ih]
    have hM0 : (0:ℝ) < M := by exact_mod_cast (lt_of_lt_of_le ha hM)
    push_cast
    field_simp
    ring

variable {N : ℕ} [NeZero N]

/-- **(L-γ), per character**: bucketing `|γ|` and Abel summation. -/
lemma Lgamma_char (χ : DirichletCharacter ℂ N) {σ T : ℝ} (hT : 1 ≤ T) :
    ∑ ρ ∈ zeroFinset χ σ T,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / (1 + |ρ.im|)
      ≤ (zeroCountBox χ σ T : ℝ) / T
        + ∑ n ∈ Finset.Ico 1 (⌊T⌋₊ + 1), (zeroCountBox χ σ n : ℝ) / ((n:ℝ) * (n + 1)) := by
  set M : ℕ := ⌊T⌋₊ + 1 with hM
  set F := zeroFinset χ σ T with hF
  set w : ℂ → ℝ := fun ρ => (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
    with hw
  have hw0 : ∀ ρ, 0 ≤ w ρ := fun ρ => Nat.cast_nonneg _
  have hT0 : (0:ℝ) < T := by linarith
  have hMT : T ≤ (M:ℝ) := by
    rw [hM]; push_cast
    exact (Nat.lt_floor_add_one T).le
  -- bucket index
  set a : ℂ → ℕ := fun ρ => ⌊|ρ.im|⌋₊ + 1 with ha
  have ha1 : ∀ ρ, 1 ≤ a ρ := fun ρ => by simp [ha]
  have haM : ∀ ρ ∈ F, a ρ ≤ M := by
    intro ρ hρ
    rw [hF, mem_zeroFinset] at hρ
    simp only [ha, hM]
    have := Nat.floor_le_floor hρ.2.2.1
    omega
  have hpt : ∀ ρ ∈ F, w ρ / (1 + |ρ.im|)
      ≤ w ρ * (1 / M + ∑ n ∈ Finset.Ico (a ρ) M, 1 / ((n:ℝ) * (n + 1))) := by
    intro ρ hρ
    rw [← one_div_telescope (ha1 ρ) (haM ρ hρ)]
    have h1 : (0:ℝ) < 1 + |ρ.im| := by positivity
    have h2 : (a ρ : ℝ) ≤ 1 + |ρ.im| := by
      simp only [ha]; push_cast
      linarith [Nat.floor_le (abs_nonneg ρ.im)]
    have h3 : (0:ℝ) < a ρ := by exact_mod_cast ha1 ρ
    rw [div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_left _ (hw0 ρ)
    exact one_div_le_one_div_of_le h3 h2
  refine le_trans (Finset.sum_le_sum hpt) ?_
  have hsplit : ∑ ρ ∈ F, w ρ * (1 / M + ∑ n ∈ Finset.Ico (a ρ) M, 1 / ((n:ℝ) * (n + 1)))
      = (∑ ρ ∈ F, w ρ) / M
        + ∑ n ∈ Finset.Ico 1 M, (∑ ρ ∈ F.filter (fun ρ => a ρ ≤ n), w ρ) / ((n:ℝ) * (n + 1)) := by
    simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      ring
    · have hIco : ∀ ρ ∈ F, Finset.Ico (a ρ) M = (Finset.Ico 1 M).filter (fun n => a ρ ≤ n) := by
        intro ρ hρ
        ext n
        simp only [Finset.mem_Ico, Finset.mem_filter]
        have := ha1 ρ
        omega
      rw [Finset.sum_congr rfl (fun ρ hρ => by rw [hIco ρ hρ, Finset.sum_filter])]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_filter, Finset.sum_div]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      split_ifs <;> ring
  rw [hsplit]
  have hcount : (∑ ρ ∈ F, w ρ) / M ≤ (zeroCountBox χ σ T : ℝ) / T := by
    rw [zeroCountBox_real]
    have h0 : 0 ≤ ∑ ρ ∈ F, w ρ := Finset.sum_nonneg fun ρ _ => hw0 ρ
    exact div_le_div_of_nonneg_left h0 hT0 hMT
  refine add_le_add hcount (Finset.sum_le_sum fun n hn => ?_)
  rw [Finset.mem_Ico] at hn
  have hn0 : (0:ℝ) < (n:ℝ) * (n + 1) := by
    have : (1:ℝ) ≤ n := by exact_mod_cast hn.1
    positivity
  apply div_le_div_of_nonneg_right _ hn0.le
  rw [zeroCountBox_real]
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun ρ _ _ => hw0 ρ)
  intro ρ hρ
  rw [Finset.mem_filter, hF, mem_zeroFinset] at hρ
  obtain ⟨⟨h1, h2, _, h4, h5⟩, h6⟩ := hρ
  rw [mem_zeroFinset]
  refine ⟨h1, h2, ?_, h4, h5⟩
  have : ⌊|ρ.im|⌋₊ < n := by simp only [ha] at h6; omega
  exact ((Nat.floor_lt (abs_nonneg _)).mp this).le

/-- **(L-γ), summed over the characters mod `N`.** -/
lemma Lgamma_sum (N : ℕ) [NeZero N] {σ T : ℝ} (hT : 1 ≤ T) :
    ∑ χ : DirichletCharacter ℂ N, ∑ ρ ∈ zeroFinset χ σ T,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / (1 + |ρ.im|)
      ≤ (∑ χ : DirichletCharacter ℂ N, (zeroCountBox χ σ T : ℝ)) / T
        + ∑ n ∈ Finset.Ico 1 (⌊T⌋₊ + 1),
            (∑ χ : DirichletCharacter ℂ N, (zeroCountBox χ σ n : ℝ)) / ((n:ℝ) * (n + 1)) := by
  refine le_trans (Finset.sum_le_sum fun χ _ => Lgamma_char χ hT) ?_
  rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_comm]
  apply le_of_eq
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_div]

end Lgamma

/-! ### The fold corollary -/

section Fold

/-- Bernoulli step: `s·n^{−1−s} ≤ (n−1)^{−s} − n^{−s}` for real `n ≥ 2`, `0 < s ≤ 1`. -/
lemma rpow_telescope_step {n s : ℝ} (hn : 2 ≤ n) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    s * n ^ (-1 - s) + n ^ (-s) ≤ (n - 1) ^ (-s) := by
  have hn0 : 0 < n := by linarith
  have hn1 : 0 < n - 1 := by linarith
  have hu : 0 < 1 - 1 / n := by
    rw [sub_pos, div_lt_one hn0]; linarith
  have hfac : n - 1 = n * (1 - 1 / n) := by field_simp
  have hbern : (1 - 1 / n) ^ s ≤ 1 - s * (1 / n) := by
    have := rpow_one_add_le_one_add_mul_self (s := -(1 / n)) (by
      have : 1 / n ≤ 1 := by rw [div_le_one hn0]; linarith
      linarith) hs0.le hs1
    simpa [sub_eq_add_neg, mul_neg] using this
  have hpos : 0 < 1 - s * (1 / n) := by
    have : s * (1 / n) ≤ 1 / 2 := by
      have : 1 / n ≤ 1 / 2 := by
        rw [div_le_div_iff₀ hn0 (by norm_num)]; linarith
      nlinarith
    linarith
  have hinv : 1 + s / n ≤ (1 - 1 / n) ^ (-s) := by
    rw [Real.rpow_neg hu.le]
    rw [le_inv_comm₀ (by positivity) (Real.rpow_pos_of_pos hu s)]
    refine le_trans hbern ?_
    have hsn : 0 ≤ s / n := by positivity
    rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
    have : s * (1 / n) = s / n := by ring
    rw [this]
    nlinarith
  have hsplit : (n - 1) ^ (-s) = n ^ (-s) * (1 - 1 / n) ^ (-s) := by
    rw [hfac, Real.mul_rpow hn0.le hu.le]
  have hns : n ^ (-1 - s) = n ^ (-s) / n := by
    rw [show -1 - s = -s + (-1 : ℝ) by ring, Real.rpow_add hn0, Real.rpow_neg_one]
    ring
  rw [hsplit, hns]
  have hnsp : 0 < n ^ (-s) := Real.rpow_pos_of_pos hn0 _
  calc s * (n ^ (-s) / n) + n ^ (-s) = n ^ (-s) * (1 + s / n) := by ring
    _ ≤ n ^ (-s) * (1 - 1 / n) ^ (-s) := mul_le_mul_of_nonneg_left hinv hnsp.le

/-- `∑_{2 ≤ n < M} n^{−1−s} ≤ 1/s`. -/
lemma sum_rpow_neg_one_sub_le {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (M : ℕ) :
    ∑ n ∈ Finset.Ico 2 M, ((n:ℝ)) ^ (-1 - s) ≤ 1 / s := by
  rcases lt_or_ge M 2 with hM | hM
  · rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty]; positivity
  have key : ∀ M : ℕ, 2 ≤ M → ∑ n ∈ Finset.Ico 2 M, ((n:ℝ)) ^ (-1 - s)
      ≤ (1 / s) * (1 - ((M:ℝ) - 1) ^ (-s)) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => norm_num [Real.one_rpow]
    | succ M hM ih =>
      rw [Finset.sum_Ico_succ_top hM]
      have hstep := rpow_telescope_step (n := (M:ℝ)) (by exact_mod_cast hM) hs0 hs1
      push_cast
      have : (M:ℝ) ^ (-1 - s) ≤ (1 / s) * (((M:ℝ) - 1) ^ (-s) - (M:ℝ) ^ (-s)) := by
        rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hs0]
        linarith
      rw [add_sub_cancel_right]
      linarith
  refine le_trans (key M hM) ?_
  have : 0 ≤ ((M:ℝ) - 1) ^ (-s) := Real.rpow_nonneg (by
    have : (2:ℝ) ≤ M := by exact_mod_cast hM
    linarith) _
  have hs' : 0 ≤ 1 / s := by positivity
  nlinarith

/-- **The fold corollary** (Z0a §2): a density input of the shape
`N(σ,t,d) ≤ C·(d·t^c)^e·L` on `2 ≤ t ≤ T` with fold exponent `c·e ≤ 1 − s`
gives a `T`-free bound on the `1/(1+|γ|)`-weighted zero sum. -/
theorem fold (d : ℕ) [NeZero d] {σ T C c e L s : ℝ} (hT : 2 ≤ T) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (_hc : 0 ≤ c) (_he : 0 ≤ e) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (ha : c * e ≤ 1 - s)
    (hden : ∀ t : ℝ, 2 ≤ t → t ≤ T →
      ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ) ≤ C * ((d:ℝ) * t ^ c) ^ e * L) :
    ∑ χ : DirichletCharacter ℂ d, ∑ ρ ∈ zeroFinset χ σ T,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / (1 + |ρ.im|)
      ≤ C * (d:ℝ) ^ e * L * (2 + 1 / s) := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd0 : (0:ℝ) ≤ d := by linarith
  have hT0 : 0 < T := by linarith
  set B := C * (d:ℝ) ^ e * L with hB
  have hB0 : 0 ≤ B := by positivity
  -- generic: N(σ,t) ≤ B t^{ce} for 2 ≤ t ≤ T
  have hgen : ∀ t : ℝ, 2 ≤ t → t ≤ T →
      ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ) ≤ B * t ^ (c * e) := by
    intro t ht htT
    refine le_trans (hden t ht htT) (le_of_eq ?_)
    have ht0 : 0 ≤ t := by linarith
    rw [hB, Real.mul_rpow hd0 (Real.rpow_nonneg ht0 _), ← Real.rpow_mul ht0]
    ring
  refine le_trans (Lgamma_sum d (by linarith)) ?_
  -- term 1
  have h1 : (∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ T : ℝ)) / T ≤ B := by
    rw [div_le_iff₀ hT0]
    refine le_trans (hgen T hT le_rfl) ?_
    have : T ^ (c * e) ≤ T ^ (1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    rw [Real.rpow_one] at this
    exact mul_le_mul_of_nonneg_left this hB0
  -- the n-sum: n = 1 and n ≥ 2
  have hM : 1 < ⌊T⌋₊ + 1 := by
    have : 2 ≤ ⌊T⌋₊ := Nat.le_floor (by exact_mod_cast hT)
    omega
  have hsum : ∑ n ∈ Finset.Ico 1 (⌊T⌋₊ + 1),
      (∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ n : ℝ)) / ((n:ℝ) * (n + 1))
      ≤ B + B * (1 / s) := by
    rw [Finset.sum_eq_sum_Ico_succ_bot hM]
    refine add_le_add ?_ ?_
    · -- n = 1
      have hmono : ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ (1:ℕ) : ℝ)
          ≤ ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ 2 : ℝ) := by
        refine Finset.sum_le_sum fun χ _ => ?_
        exact_mod_cast zeroCountBox_mono_T χ (by norm_num : ((1:ℕ):ℝ) ≤ 2)
      refine le_trans (div_le_div_of_nonneg_right hmono (by positivity)) ?_
      refine le_trans (div_le_div_of_nonneg_right (hgen 2 le_rfl hT) (by positivity)) ?_
      push_cast
      have h2 : (2:ℝ) ^ (c * e) ≤ 2 ^ (1:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      rw [Real.rpow_one] at h2
      rw [div_le_iff₀ (by norm_num)]
      nlinarith
    · -- n ≥ 2
      have hpt : ∀ n ∈ Finset.Ico 2 (⌊T⌋₊ + 1),
          (∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ n : ℝ)) / ((n:ℝ) * (n + 1))
            ≤ B * ((n:ℝ)) ^ (-1 - s) := by
        intro n hn
        rw [Finset.mem_Ico] at hn
        have hn2 : (2:ℝ) ≤ n := by exact_mod_cast hn.1
        have hnT : (n:ℝ) ≤ T := by
          have : n ≤ ⌊T⌋₊ := by omega
          exact le_trans (by exact_mod_cast this) (Nat.floor_le hT0.le)
        have hn0 : (0:ℝ) < n := by linarith
        refine le_trans (div_le_div_of_nonneg_right (hgen n hn2 hnT) (by positivity)) ?_
        rw [div_le_iff₀ (by positivity)]
        have hpow : (n:ℝ) ^ (c * e) ≤ (n:ℝ) ^ (-1 - s) * ((n:ℝ) * (n + 1)) := by
          have hnn : (n:ℝ) * (n + 1) ≤ n ^ (2:ℝ) * 2 := by
            rw [Real.rpow_two]; nlinarith
          calc (n:ℝ) ^ (c * e) ≤ (n:ℝ) ^ (1 - s) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) ha
            _ = (n:ℝ) ^ (-1 - s) * (n:ℝ) ^ (2:ℝ) := by
                rw [← Real.rpow_add hn0]; ring_nf
            _ ≤ (n:ℝ) ^ (-1 - s) * ((n:ℝ) * (n + 1)) := by
                apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hn0.le _)
                rw [Real.rpow_two]; nlinarith
        calc B * (n:ℝ) ^ (c * e) ≤ B * ((n:ℝ) ^ (-1 - s) * ((n:ℝ) * (n + 1))) :=
              mul_le_mul_of_nonneg_left hpow hB0
          _ = B * (n:ℝ) ^ (-1 - s) * ((n:ℝ) * (n + 1)) := by ring
      refine le_trans (Finset.sum_le_sum hpt) ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_rpow_neg_one_sub_le hs0 hs1 _) hB0
  calc _ ≤ B + (B + B * (1 / s)) := add_le_add h1 hsum
    _ = B * (2 + 1 / s) := by ring

end Fold

/-! ### Level bookkeeping -/

/-- The level lemma: from `1 ≤ d ≤ x^u` and `d·x^v ≤ y`, every power `d^α` with
`0 ≤ β ≤ α` is at most `x^{u(α−β) − vβ}·y^β`. -/
lemma dpow_le {x d y u v α β : ℝ} (hx : 1 ≤ x) (hd1 : 1 ≤ d) (hdx : d ≤ x ^ u)
    (hy : d * x ^ v ≤ y) (hβ : 0 ≤ β) (hαβ : β ≤ α) :
    d ^ α ≤ x ^ (u * (α - β) - v * β) * y ^ β := by
  have hx0 : 0 < x := by linarith
  have hd0 : 0 ≤ d := by linarith
  have hxv : 0 < x ^ v := Real.rpow_pos_of_pos hx0 v
  have hdy : d ≤ y * x ^ (-v) := by
    rw [Real.rpow_neg hx0.le, ← div_eq_mul_inv, le_div_iff₀ hxv]
    exact hy
  have hy0 : 0 ≤ y := le_trans (by positivity) hy
  have h1 : d ^ (α - β) ≤ x ^ (u * (α - β)) := by
    rw [Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow hd0 hdx (by linarith)
  have h2 : d ^ β ≤ y ^ β * x ^ (-v * β) := by
    rw [show -v * β = (-v) * β by ring, Real.rpow_mul hx0.le,
      ← Real.mul_rpow hy0 (Real.rpow_nonneg hx0.le _)]
    exact Real.rpow_le_rpow hd0 hdy hβ
  calc d ^ α = d ^ (α - β) * d ^ β := by
        rw [← Real.rpow_add (by linarith : 0 < d)]; ring_nf
    _ ≤ x ^ (u * (α - β)) * (y ^ β * x ^ (-v * β)) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg hd0 _) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (u * (α - β) - v * β) * y ^ β := by
        rw [show u * (α - β) - v * β = u * (α - β) + (-v * β) by ring, Real.rpow_add hx0]
        ring

/-! ### The σ-grid lemma -/

/-- **σ-grid bound.**  Bucket the zeros with `σ₁ ≤ β < σ₂` by `⌊(β−σ₁)/h⌋`; on the
`k`-th bucket `y^β ≤ y^{σ₁+(k+1)h}` and the bucket mass is at most the tail mass
`B k` above `σ₁ + k h`. -/
lemma grid_bound {ι : Type*} (s : Finset ι) (F : ι → Finset ℂ) (v : ι → ℂ → ℝ)
    (hv : ∀ i ρ, 0 ≤ v i ρ) {y σ₁ σ₂ h : ℝ} (hy : 1 ≤ y) (hh : 0 < h) (M : ℕ)
    (hM : σ₂ ≤ σ₁ + M * h) (B : ℕ → ℝ)
    (hB : ∀ k, k < M →
      ∑ i ∈ s, ∑ ρ ∈ (F i).filter (fun ρ : ℂ => σ₁ + k * h ≤ ρ.re), v i ρ ≤ B k) :
    ∑ i ∈ s, ∑ ρ ∈ (F i).filter (fun ρ : ℂ => σ₁ ≤ ρ.re ∧ ρ.re < σ₂), v i ρ * y ^ ρ.re
      ≤ ∑ k ∈ Finset.range M, y ^ (σ₁ + (k + 1) * h) * B k := by
  classical
  set g : ℂ → ℕ := fun ρ => ⌊(ρ.re - σ₁) / h⌋₊ with hg
  have hmaps : ∀ i, ∀ ρ ∈ (F i).filter (fun ρ : ℂ => σ₁ ≤ ρ.re ∧ ρ.re < σ₂),
      g ρ ∈ Finset.range M := by
    intro i ρ hρ
    rw [Finset.mem_filter] at hρ
    rw [Finset.mem_range, hg]
    apply Nat.floor_lt (by
      apply div_nonneg _ hh.le
      linarith [hρ.2.1]) |>.mpr
    rw [div_lt_iff₀ hh]
    linarith [hρ.2.2]
  -- fiberwise decomposition of each inner sum, then swap
  have hfib : ∀ i, ∑ ρ ∈ (F i).filter (fun ρ : ℂ => σ₁ ≤ ρ.re ∧ ρ.re < σ₂), v i ρ * y ^ ρ.re
      = ∑ k ∈ Finset.range M,
          ∑ ρ ∈ ((F i).filter (fun ρ : ℂ => σ₁ ≤ ρ.re ∧ ρ.re < σ₂)).filter (fun ρ => g ρ = k),
            v i ρ * y ^ ρ.re := by
    intro i
    rw [Finset.sum_fiberwise_of_maps_to (hmaps i)]
  simp_rw [hfib]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun k hk => ?_
  rw [Finset.mem_range] at hk
  have hy0 : 0 < y := by linarith
  -- pointwise: on bucket k, y^β ≤ y^{σ₁+(k+1)h}
  have hpt : ∀ i, ∀ ρ ∈ ((F i).filter (fun ρ : ℂ => σ₁ ≤ ρ.re ∧ ρ.re < σ₂)).filter
        (fun ρ => g ρ = k),
      v i ρ * y ^ ρ.re ≤ v i ρ * y ^ (σ₁ + (k + 1) * h) := by
    intro i ρ hρ
    rw [Finset.mem_filter, Finset.mem_filter] at hρ
    apply mul_le_mul_of_nonneg_left _ (hv i ρ)
    apply Real.rpow_le_rpow_of_exponent_le hy
    have h1 : (ρ.re - σ₁) / h < k + 1 := by
      have := Nat.lt_floor_add_one ((ρ.re - σ₁) / h)
      rw [← hρ.2]
      exact this
    rw [div_lt_iff₀ hh] at h1
    linarith
  refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum (hpt i)) ?_
  -- pull out the constant and compare the bucket mass to the tail mass
  have hconst : ∑ i ∈ s, ∑ ρ ∈ ((F i).filter (fun ρ : ℂ => σ₁ ≤ ρ.re ∧ ρ.re < σ₂)).filter
        (fun ρ => g ρ = k), v i ρ * y ^ (σ₁ + (k + 1) * h)
      = y ^ (σ₁ + (k + 1) * h) * ∑ i ∈ s, ∑ ρ ∈ ((F i).filter
          (fun ρ : ℂ => σ₁ ≤ ρ.re ∧ ρ.re < σ₂)).filter (fun ρ => g ρ = k), v i ρ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    ring
  rw [hconst]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy0.le _)
  refine le_trans ?_ (hB k hk)
  refine Finset.sum_le_sum fun i _ => ?_
  apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun ρ _ _ => hv i ρ)
  intro ρ hρ
  rw [Finset.mem_filter, Finset.mem_filter] at hρ
  rw [Finset.mem_filter]
  refine ⟨hρ.1.1, ?_⟩
  have h1 : (k:ℝ) ≤ (ρ.re - σ₁) / h := by
    rw [← hρ.2]
    exact Nat.floor_le (by
      apply div_nonneg _ hh.le
      linarith [hρ.1.2.1])
  rw [le_div_iff₀ hh] at h1
  linarith

/-! ### The geometric sum along the grid -/

lemma sum_geom_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (M : ℕ) :
    ∑ j ∈ Finset.range M, r ^ j ≤ 1 / (1 - r) := by
  have h1r : 0 < 1 - r := by linarith
  rw [geom_sum_eq hr1.ne, le_div_iff₀ h1r]
  have : 0 ≤ r ^ M := pow_nonneg hr0 M
  have hne : r - 1 ≠ 0 := by linarith
  rw [div_mul_eq_mul_div, div_le_iff_of_neg (by linarith)]
  nlinarith

lemma one_div_one_sub_exp_le : 1 / (1 - Real.exp (-(9 / 200 : ℝ))) ≤ 209 / 9 := by
  have h1 : (9 / 200 : ℝ) + 1 ≤ Real.exp (9 / 200) := Real.add_one_le_exp _
  have h2 : Real.exp (-(9 / 200 : ℝ)) ≤ 1 / (1 + 9 / 200) := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  have h3 : 0 < 1 - Real.exp (-(9 / 200 : ℝ)) := by
    have : Real.exp (-(9 / 200 : ℝ)) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
    linarith
  rw [div_le_iff₀ h3]
  norm_num at h2 ⊢
  linarith

/-- **Geometric bound along the grid**: with `h = 1/log x` and `M = ⌈(σ₂−σ₁)log x⌉`,
`∑_{k<M} y^{σ₁+(k+1)h}·d^{(9/2)(1−σ₁−kh)} ≤ 64·y·x^{−(9/200)(1−σ₂)}`, using
`d^{9/2} ≤ x^{−9/200}·y`. -/
lemma grid_geom {x y d σ₁ σ₂ : ℝ} (hx : Real.exp 1 ≤ x) (hy1 : 1 ≤ y) (hyx : y ≤ x)
    (hd1 : 1 ≤ d) (hdy : d ^ (9 / 2 : ℝ) ≤ x ^ (-(9 / 200) : ℝ) * y)
    (hσ : σ₁ ≤ σ₂) (hσ2 : σ₂ ≤ 1) :
    ∑ k ∈ Finset.range ⌈(σ₂ - σ₁) * Real.log x⌉₊,
        y ^ (σ₁ + (k + 1) * (1 / Real.log x))
          * d ^ ((9 / 2 : ℝ) * (1 - (σ₁ + k * (1 / Real.log x))))
      ≤ 64 * y * x ^ (-(9 / 200 : ℝ) * (1 - σ₂)) := by
  have he : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hx1 : 1 ≤ x := le_trans he hx
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ Real.log x := by
    have := Real.log_le_log (by positivity) hx
    rwa [Real.log_exp] at this
  have hL0 : 0 < Real.log x := by linarith
  have hy0 : 0 < y := by linarith
  have hd0 : 0 < d := by linarith
  set L := Real.log x with hLdef
  set M := ⌈(σ₂ - σ₁) * L⌉₊ with hMdef
  set r := Real.exp (-(9 / 200 : ℝ)) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  set E := x ^ (-(9 / 200 : ℝ) * (1 - σ₂)) with hEdef
  have hE0 : 0 < E := Real.rpow_pos_of_pos hx0 _
  -- y^{1/L} ≤ e
  have hyh : y ^ (1 / L) ≤ Real.exp 1 := by
    calc y ^ (1 / L) ≤ x ^ (1 / L) := Real.rpow_le_rpow hy0.le hyx (by positivity)
      _ = Real.exp 1 := by
          rw [Real.rpow_def_of_pos hx0, ← hLdef]
          congr 1
          field_simp
  -- M − 1 < (σ₂ − σ₁) L
  have hMlt : (M:ℝ) < (σ₂ - σ₁) * L + 1 := Nat.ceil_lt_add_one (by nlinarith)
  -- per-term bound
  have hterm : ∀ k ∈ Finset.range M,
      y ^ (σ₁ + (k + 1) * (1 / L)) * d ^ ((9 / 2 : ℝ) * (1 - (σ₁ + k * (1 / L))))
        ≤ Real.exp 1 * y * E * r ^ (M - 1 - k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    set σk := σ₁ + k * (1 / L) with hσk
    have hkM : (k:ℝ) + 1 ≤ M := by exact_mod_cast hk
    have hσkσ₂ : σk < σ₂ := by
      rw [hσk]
      have : (k:ℝ) * (1 / L) < σ₂ - σ₁ := by
        rw [mul_one_div, div_lt_iff₀ hL0]
        linarith
      linarith
    have hσk1 : 0 ≤ 1 - σk := by linarith
    -- y^{σk + h} = y^{σk} y^h
    have hsplit : y ^ (σ₁ + (k + 1) * (1 / L)) = y ^ σk * y ^ (1 / L) := by
      rw [← Real.rpow_add hy0, hσk]; ring_nf
    -- d^{(9/2)(1−σk)} ≤ (x^{−9/200} y)^{1−σk} = x^{−(9/200)(1−σk)} y^{1−σk}
    have hdk : d ^ ((9 / 2 : ℝ) * (1 - σk))
        ≤ x ^ (-(9 / 200 : ℝ) * (1 - σk)) * y ^ (1 - σk) := by
      rw [Real.rpow_mul hd0.le, Real.rpow_mul hx0.le,
        ← Real.mul_rpow (Real.rpow_nonneg hx0.le _) hy0.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hd0.le _) hdy hσk1
    -- x^{−(9/200)(1−σk)} = E · x^{−(9/200)(σ₂−σk)} ≤ E · r^{M−1−k}
    have hxk : x ^ (-(9 / 200 : ℝ) * (1 - σk)) ≤ E * r ^ (M - 1 - k) := by
      have hsplit2 : x ^ (-(9 / 200 : ℝ) * (1 - σk))
          = E * x ^ (-(9 / 200 : ℝ) * (σ₂ - σk)) := by
        rw [hEdef, ← Real.rpow_add hx0]; ring_nf
      rw [hsplit2]
      apply mul_le_mul_of_nonneg_left _ hE0.le
      rw [Real.rpow_def_of_pos hx0, ← hLdef, hrdef, ← Real.exp_nat_mul, Real.exp_le_exp]
      have hcast : ((M - 1 - k : ℕ) : ℝ) = (M:ℝ) - 1 - k := by
        have : k + 1 ≤ M := hk
        push_cast [Nat.cast_sub (by omega : k ≤ M - 1), Nat.cast_sub (by omega : 1 ≤ M)]
        ring
      rw [hcast]
      have : (σ₂ - σk) * L ≥ (M:ℝ) - 1 - k := by
        rw [hσk]
        have : (k:ℝ) * (1 / L) * L = k := by field_simp
        nlinarith
      nlinarith
    calc y ^ (σ₁ + (k + 1) * (1 / L)) * d ^ ((9 / 2 : ℝ) * (1 - σk))
        = y ^ σk * y ^ (1 / L) * d ^ ((9 / 2 : ℝ) * (1 - σk)) := by rw [hsplit]
      _ ≤ y ^ σk * Real.exp 1 * (x ^ (-(9 / 200 : ℝ) * (1 - σk)) * y ^ (1 - σk)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hyh (Real.rpow_nonneg hy0.le _)) hdk
            (Real.rpow_nonneg hd0.le _) (by positivity)
      _ = Real.exp 1 * y * x ^ (-(9 / 200 : ℝ) * (1 - σk)) := by
          have : y ^ σk * y ^ (1 - σk) = y := by
            rw [← Real.rpow_add hy0]; simp
          calc y ^ σk * Real.exp 1 * (x ^ (-(9 / 200 : ℝ) * (1 - σk)) * y ^ (1 - σk))
              = Real.exp 1 * (y ^ σk * y ^ (1 - σk)) * x ^ (-(9 / 200 : ℝ) * (1 - σk)) := by
                ring
            _ = _ := by rw [this]
      _ ≤ Real.exp 1 * y * (E * r ^ (M - 1 - k)) := by
          apply mul_le_mul_of_nonneg_left hxk (by positivity)
      _ = Real.exp 1 * y * E * r ^ (M - 1 - k) := by ring
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum, Finset.sum_range_reflect (fun j => r ^ j) M]
  have hgeom := sum_geom_le hr0 hr1 M
  have hexp : Real.exp 1 ≤ 2.72 := by
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have h209 := one_div_one_sub_exp_le
  rw [← hrdef] at h209
  have hyE : 0 ≤ y * E := by positivity
  calc Real.exp 1 * y * E * ∑ j ∈ Finset.range M, r ^ j
      ≤ Real.exp 1 * y * E * (1 / (1 - r)) := by
        apply mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ ≤ 2.72 * y * E * (209 / 9) := by
        have h1 : Real.exp 1 * y * E * (1 / (1 - r)) = (Real.exp 1 * (1 / (1 - r))) * (y * E) := by
          ring
        have h2 : 2.72 * y * E * (209 / 9) = (2.72 * (209 / 9)) * (y * E) := by ring
        rw [h1, h2]
        apply mul_le_mul_of_nonneg_right _ hyE
        have h0 : 0 ≤ 1 / (1 - r) := by
          apply div_nonneg zero_le_one; linarith
        calc Real.exp 1 * (1 / (1 - r)) ≤ 2.72 * (1 / (1 - r)) :=
              mul_le_mul_of_nonneg_right hexp h0
          _ ≤ 2.72 * (209 / 9) := mul_le_mul_of_nonneg_left h209 (by norm_num)
    _ ≤ 64 * y * E := by nlinarith

/-! ### Harmonic-type sum -/

lemma sum_inv_succ_le_log (M : ℕ) (hM : 1 ≤ M) :
    ∑ n ∈ Finset.Ico 1 M, 1 / ((n:ℝ) + 1) ≤ Real.log M := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ico_succ_top hM]
    have hM0 : (0:ℝ) < M := by exact_mod_cast hM
    have hstep : 1 / ((M:ℝ) + 1) ≤ Real.log ((M:ℝ) + 1) - Real.log M := by
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < M / (M + 1) by positivity)
      rw [Real.log_div hM0.ne' (by positivity)] at h
      have : (M:ℝ) / (M + 1) - 1 = -(1 / ((M:ℝ) + 1)) := by field_simp; ring
      linarith
    push_cast
    linarith

/-! ### Zone sums -/

section Zones

/-- The weight `ord(ρ)/(1+|γ|)` of a zero. -/
noncomputable def wt {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℝ :=
  (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / (1 + |ρ.im|)

lemma wt_nonneg {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ) : 0 ≤ wt χ ρ := by
  unfold wt; positivity

/-- The zone sum `∑_χ ∑_{ρ : σ₁ ≤ β < σ₂, |γ| ≤ T} ord(ρ)·y^β/(1+|γ|)`. -/
noncomputable def zoneSum (d : ℕ) [NeZero d] (T y σ₁ σ₂ : ℝ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ d,
    ∑ ρ ∈ (zeroFinset χ (1/2) T).filter (fun ρ : ℂ => σ₁ ≤ ρ.re ∧ ρ.re < σ₂),
      wt χ ρ * y ^ ρ.re

/-- The full weighted zero sum `∑_χ ∑_{ρ : β ≥ 1/2, |γ| ≤ T} ord(ρ)·y^β/(1+|γ|)`. -/
noncomputable def zeroSumTotal (d : ℕ) [NeZero d] (T y : ℝ) : ℝ :=
  ∑ χ : DirichletCharacter ℂ d, ∑ ρ ∈ zeroFinset χ (1/2) T, wt χ ρ * y ^ ρ.re

lemma zoneSum_nonneg (d : ℕ) [NeZero d] {T y : ℝ} (hy : 0 ≤ y) (σ₁ σ₂ : ℝ) :
    0 ≤ zoneSum d T y σ₁ σ₂ := by
  unfold zoneSum
  apply Finset.sum_nonneg; intro χ _
  apply Finset.sum_nonneg; intro ρ _
  exact mul_nonneg (wt_nonneg χ ρ) (Real.rpow_nonneg hy _)

/-- The four-zone split of the full zero sum. -/
lemma zeroSumTotal_split (d : ℕ) [NeZero d] (T y : ℝ) {σa σb σc : ℝ}
    (_h1 : 1/2 ≤ σa) (h2 : σa ≤ σb) (h3 : σb ≤ σc) (_h4 : σc ≤ 1) :
    zeroSumTotal d T y
      = zoneSum d T y (1/2) σa + zoneSum d T y σa σb + zoneSum d T y σb σc
        + zoneSum d T y σc 1 := by
  unfold zeroSumTotal zoneSum
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun χ _ => ?_
  set F := zeroFinset χ (1/2) T with hF
  set f : ℂ → ℝ := fun ρ => wt χ ρ * y ^ ρ.re with hf
  have key : ∀ ρ ∈ F, f ρ
      = (if 1/2 ≤ ρ.re ∧ ρ.re < σa then f ρ else 0)
        + (if σa ≤ ρ.re ∧ ρ.re < σb then f ρ else 0)
        + (if σb ≤ ρ.re ∧ ρ.re < σc then f ρ else 0)
        + (if σc ≤ ρ.re ∧ ρ.re < 1 then f ρ else 0) := by
    intro ρ hρ
    have hlo : 1/2 ≤ ρ.re := (mem_zeroFinset.mp hρ).1
    have hhi : ρ.re < 1 := re_lt_one_of_mem_zeroFinset hρ
    by_cases ha : ρ.re < σa
    · rw [if_pos ⟨hlo, ha⟩, if_neg (fun h => by linarith [h.1]),
        if_neg (fun h => by linarith [h.1]), if_neg (fun h => by linarith [h.1])]
      ring
    · by_cases hb : ρ.re < σb
      · rw [if_neg (fun h => ha h.2), if_pos ⟨not_lt.mp ha, hb⟩,
          if_neg (fun h => by linarith [h.1]), if_neg (fun h => by linarith [h.1])]
        ring
      · by_cases hc : ρ.re < σc
        · rw [if_neg (fun h => ha h.2), if_neg (fun h => hb h.2),
            if_pos ⟨not_lt.mp hb, hc⟩, if_neg (fun h => by linarith [h.1])]
          ring
        · rw [if_neg (fun h => ha h.2), if_neg (fun h => hb h.2), if_neg (fun h => hc h.2),
            if_pos ⟨not_lt.mp hc, hhi⟩]
          ring
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl key

/-! #### Numerics at the parameter point `T = x³` -/

lemma log_d_T_le {x d : ℝ} (hx : 2 ≤ x) (hd1 : 1 ≤ d) (hd : d ≤ x ^ (191/900 : ℝ)) :
    Real.log (d * (x ^ 3 + 2)) ≤ 5 * Real.log x := by
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hdx : d ≤ x := le_trans hd (Real.rpow_le_self_of_one_le hx1 (by norm_num))
  have hT : x ^ 3 + 2 ≤ x ^ 4 := by
    have h8 : (8:ℝ) ≤ x ^ 3 := by
      calc (8:ℝ) = 2 ^ 3 := by norm_num
        _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
    have h2x : 2 * x ^ 3 ≤ x * x ^ 3 := mul_le_mul_of_nonneg_right hx (by positivity)
    nlinarith
  calc Real.log (d * (x ^ 3 + 2)) ≤ Real.log (x * x ^ 4) := by
        apply Real.log_le_log (by positivity)
        apply mul_le_mul hdx hT (by positivity) hx0.le
    _ = 5 * Real.log x := by
        rw [Real.log_mul hx0.ne' (by positivity), Real.log_pow]; push_cast; ring

lemma one_le_log_of_exp_le {x : ℝ} (hx : Real.exp 1 ≤ x) : 1 ≤ Real.log x := by
  have := Real.log_le_log (Real.exp_pos 1) hx
  rwa [Real.log_exp] at this

/-- `d^{9/2} ≤ x^{−9/200}·y` at the parameter point. -/
lemma d_ninehalf_le {x d y : ℝ} (hx : 1 ≤ x) (hd1 : 1 ≤ d) (hd : d ≤ x ^ (191/900 : ℝ))
    (hy : d * x ^ (709/900 : ℝ) ≤ y) :
    d ^ (9/2 : ℝ) ≤ x ^ (-(9/200) : ℝ) * y := by
  have := dpow_le hx hd1 hd hy (β := 1) (α := 9/2) zero_le_one (by norm_num)
  rw [Real.rpow_one] at this
  convert this using 3
  norm_num

/-! #### Zone I -/

/-- **Zone I** (`1/2 ≤ β < 39/50`): the crude count `C₁ = 1120` and (L-γ) at
`T = x³` give `S_I ≤ 28000·d·log²x·y^{39/50} ≤ εy/27` once
`756000·log²x ≤ ε·x^{7/900}`. -/
theorem zoneI_le (d : ℕ) [NeZero d] {x y ε : ℝ} (hx : Real.exp 1 ≤ x) (hx2 : 2 ≤ x)
    (hd : (d:ℝ) ≤ x ^ (191/900 : ℝ)) (hy : (d:ℝ) * x ^ (709/900 : ℝ) ≤ y)
    (hxI : 756000 * Real.log x ^ 2 ≤ ε * x ^ (7/900 : ℝ)) :
    zoneSum d (x ^ 3) y (1/2) (39/50) ≤ ε * y / 27 := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ Real.log x := one_le_log_of_exp_le hx
  have hL0 : 0 < Real.log x := by linarith
  have hxp : (1:ℝ) ≤ x ^ (709/900 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (0:ℝ) ≤ 709/900)
    rwa [Real.rpow_zero] at this
  have hy1 : 1 ≤ y := by nlinarith
  have hy0 : 0 < y := by linarith
  have hT2 : (2:ℝ) ≤ x ^ 3 := by nlinarith [pow_pos hx0 2]
  have hT0 : (0:ℝ) < x ^ 3 := by positivity
  set L := Real.log x with hLdef
  set T := x ^ 3 with hTdef
  set Λ := Real.log ((d:ℝ) * (T + 2)) with hΛ
  have hΛ5 : Λ ≤ 5 * L := log_d_T_le hx2 hd1 hd
  have hΛ0 : 0 ≤ Λ := Real.log_nonneg (by nlinarith)
  -- Step 1: pull `y^{39/50}` out
  have h1 : zoneSum d T y (1/2) (39/50)
      ≤ y ^ (39/50 : ℝ) * ∑ χ : DirichletCharacter ℂ d, ∑ ρ ∈ zeroFinset χ (1/2) T, wt χ ρ := by
    unfold zoneSum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun χ _ => ?_
    rw [Finset.mul_sum]
    calc ∑ ρ ∈ (zeroFinset χ (1/2) T).filter (fun ρ : ℂ => 1/2 ≤ ρ.re ∧ ρ.re < 39/50),
          wt χ ρ * y ^ ρ.re
        ≤ ∑ ρ ∈ (zeroFinset χ (1/2) T).filter (fun ρ : ℂ => 1/2 ≤ ρ.re ∧ ρ.re < 39/50),
          y ^ (39/50 : ℝ) * wt χ ρ := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [Finset.mem_filter] at hρ
          rw [mul_comm]
          apply mul_le_mul_of_nonneg_right _ (wt_nonneg χ ρ)
          exact Real.rpow_le_rpow_of_exponent_le hy1 hρ.2.2.le
      _ ≤ ∑ ρ ∈ zeroFinset χ (1/2) T, y ^ (39/50 : ℝ) * wt χ ρ :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun ρ _ _ => mul_nonneg (Real.rpow_nonneg hy0.le _) (wt_nonneg χ ρ))
  -- Step 2: (L-γ) with the crude count
  have hcrude : ∀ t : ℝ, 1 ≤ t → t ≤ T →
      ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ (1/2) t : ℝ) ≤ 1120 * t * d * Λ := by
    intro t ht htT
    refine le_trans (sum_zeroCountBox_le d ht) ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.log_le_log (by positivity)
    apply mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : ∑ χ : DirichletCharacter ℂ d, ∑ ρ ∈ zeroFinset χ (1/2) T, wt χ ρ
      ≤ 1120 * d * Λ * (1 + Real.log (⌊T⌋₊ + 1 : ℕ)) := by
    refine le_trans (Lgamma_sum d (by linarith)) ?_
    have hA : (∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ (1/2) T : ℝ)) / T
        ≤ 1120 * d * Λ := by
      rw [div_le_iff₀ hT0]
      refine le_trans (hcrude T (by linarith) le_rfl) (le_of_eq (by ring))
    have hB : ∑ n ∈ Finset.Ico 1 (⌊T⌋₊ + 1),
        (∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ (1/2) n : ℝ)) / ((n:ℝ) * (n + 1))
        ≤ 1120 * d * Λ * Real.log (⌊T⌋₊ + 1 : ℕ) := by
      have hpt : ∀ n ∈ Finset.Ico 1 (⌊T⌋₊ + 1),
          (∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ (1/2) n : ℝ)) / ((n:ℝ) * (n + 1))
            ≤ 1120 * d * Λ * (1 / ((n:ℝ) + 1)) := by
        intro n hn
        rw [Finset.mem_Ico] at hn
        have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn.1
        have hnT : (n:ℝ) ≤ T := by
          have : n ≤ ⌊T⌋₊ := by omega
          exact le_trans (by exact_mod_cast this) (Nat.floor_le hT0.le)
        rw [div_le_iff₀ (by positivity)]
        refine le_trans (hcrude n hn1 hnT) (le_of_eq ?_)
        field_simp
      refine le_trans (Finset.sum_le_sum hpt) ?_
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left (sum_inv_succ_le_log _ (by omega)) (by positivity)
    linarith
  -- Step 3: numerics: log(⌊T⌋+1) ≤ 4L, Λ ≤ 5L
  have hlogT : Real.log (⌊T⌋₊ + 1 : ℕ) ≤ 4 * L := by
    have h1' : ((⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ x ^ 4 := by
      push_cast
      have := Nat.floor_le hT0.le
      nlinarith [pow_pos hx0 3]
    calc Real.log (⌊T⌋₊ + 1 : ℕ) ≤ Real.log (x ^ 4) :=
          Real.log_le_log (by positivity) h1'
      _ = 4 * L := by rw [Real.log_pow]; push_cast; ring
  have h3 : ∑ χ : DirichletCharacter ℂ d, ∑ ρ ∈ zeroFinset χ (1/2) T, wt χ ρ
      ≤ 28000 * d * L ^ 2 := by
    refine le_trans h2 ?_
    have hbr : 1 + Real.log (⌊T⌋₊ + 1 : ℕ) ≤ 5 * L := by linarith
    calc 1120 * d * Λ * (1 + Real.log (⌊T⌋₊ + 1 : ℕ))
        ≤ 1120 * d * (5 * L) * (5 * L) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hΛ5 (by positivity)) hbr
            (by positivity) (by positivity)
      _ = 28000 * d * L ^ 2 := by ring
  -- Step 4: the level check
  have hlev : (d:ℝ) ≤ x ^ (-(7/900) : ℝ) * y ^ (11/50 : ℝ) := by
    have := dpow_le hx1 hd1 hd hy (β := 11/50) (α := 1) (by norm_num) (by norm_num)
    rw [Real.rpow_one] at this
    convert this using 3
    norm_num
  have hkey : 756000 * d * L ^ 2 ≤ ε * y ^ (11/50 : ℝ) := by
    have hxneg : x ^ (-(7/900) : ℝ) = 1 / x ^ (7/900 : ℝ) := by
      rw [Real.rpow_neg hx0.le, one_div]
    have hx7 : 0 < x ^ (7/900 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hy11 : 0 ≤ y ^ (11/50 : ℝ) := Real.rpow_nonneg hy0.le _
    calc 756000 * d * L ^ 2 = 756000 * L ^ 2 * d := by ring
      _ ≤ 756000 * L ^ 2 * (x ^ (-(7/900) : ℝ) * y ^ (11/50 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlev (by positivity)
      _ = (756000 * L ^ 2 / x ^ (7/900 : ℝ)) * y ^ (11/50 : ℝ) := by
          rw [hxneg]; ring
      _ ≤ ε * y ^ (11/50 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hy11
          rw [div_le_iff₀ hx7]
          exact hxI
  have hysplit : y = y ^ (39/50 : ℝ) * y ^ (11/50 : ℝ) := by
    rw [← Real.rpow_add hy0]; norm_num
  calc zoneSum d T y (1/2) (39/50)
      ≤ y ^ (39/50 : ℝ) * (28000 * d * L ^ 2) :=
        le_trans h1 (mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hy0.le _))
    _ ≤ y ^ (39/50 : ℝ) * (ε * y ^ (11/50 : ℝ) / 27) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hy0.le _)
        linarith
    _ = ε * y / 27 := by
        conv_rhs => rw [hysplit]
        ring


/-! #### Zone II -/

/-- `σ* = 1 − 50(K+2)·log log x / log x`. -/
noncomputable def sigmaStar (K : ℕ) (x : ℝ) : ℝ :=
  1 - 50 * ((K:ℝ) + 2) * Real.log (Real.log x) / Real.log x

lemma sigmaStar_le_one {K : ℕ} {x : ℝ} (hx : Real.exp 1 ≤ x) : sigmaStar K x ≤ 1 := by
  unfold sigmaStar
  have hL := one_le_log_of_exp_le hx
  have : 0 ≤ 50 * ((K:ℝ) + 2) * Real.log (Real.log x) / Real.log x := by
    have := Real.log_nonneg hL
    positivity
  linarith

/-- **Zone II** (`39/50 ≤ β < σ*`): the logged density (uniform profile `P ≤ 7/2`,
`c₀ ≤ 5/4`, fold constant `2 + 80/3 ≤ 29`) folded at `T = x³` and integrated along
the σ-grid; the decay `x^{−(9/200)(1−σ*)} = (log x)^{−(9/4)(K+2)}` absorbs the
`(5 log x)^K`. -/
theorem zoneII_le (d : ℕ) [NeZero d] {x y ε CH P c₀ : ℝ} {K : ℕ}
    (hCH : 1 ≤ CH) (hP0 : 0 ≤ P) (hP : P ≤ 7/2) (hc₀ : 1 ≤ c₀) (hc₀' : c₀ ≤ 5/4)
    (hlog : ∀ (t σ : ℝ), 2 ≤ t → 39/50 ≤ σ → σ ≤ 1 →
      ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
        ≤ CH * ((d : ℝ) * t ^ c₀) ^ (P * (1 - σ)) * Real.log ((d : ℝ) * (t + 2)) ^ K)
    (hx : Real.exp 1 ≤ x) (hx2 : 2 ≤ x) (hd : (d:ℝ) ≤ x ^ (191/900 : ℝ))
    (hy : (d:ℝ) * x ^ (709/900 : ℝ) ≤ y) (hyx : y ≤ x)
    (hσ : 39/50 ≤ sigmaStar K x)
    (hxII : 50112 * 5 ^ K * CH ≤ ε * Real.log x ^ (9/2 : ℝ)) :
    zoneSum d (x ^ 3) y (39/50) (sigmaStar K x) ≤ ε * y / 27 := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd0 : (0:ℝ) < d := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ Real.log x := one_le_log_of_exp_le hx
  have hL0 : 0 < Real.log x := by linarith
  have hlogL : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL
  have hxp : (1:ℝ) ≤ x ^ (709/900 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (0:ℝ) ≤ 709/900)
    rwa [Real.rpow_zero] at this
  have hy1 : 1 ≤ y := by nlinarith
  have hy0 : 0 < y := by linarith
  have hT2 : (2:ℝ) ≤ x ^ 3 := by nlinarith [pow_pos hx0 2]
  have hT0 : (0:ℝ) < x ^ 3 := by positivity
  have hσs1 : sigmaStar K x ≤ 1 := sigmaStar_le_one hx
  set L := Real.log x with hLdef
  set T := x ^ 3 with hTdef
  set σs := sigmaStar K x with hσs
  set h : ℝ := 1 / L with hh
  have hh0 : 0 < h := by positivity
  set M : ℕ := ⌈(σs - 39/50) * L⌉₊ with hM
  set Lg : ℝ := (5 * L) ^ K with hLg
  have hLg0 : 0 ≤ Lg := by positivity
  -- log power bound on `2 ≤ t ≤ T`
  have hΛ : ∀ t : ℝ, 2 ≤ t → t ≤ T → Real.log ((d:ℝ) * (t + 2)) ^ K ≤ Lg := by
    intro t ht htT
    apply pow_le_pow_left₀ (Real.log_nonneg (by nlinarith))
    calc Real.log ((d:ℝ) * (t + 2)) ≤ Real.log ((d:ℝ) * (T + 2)) := by
          apply Real.log_le_log (by positivity)
          apply mul_le_mul_of_nonneg_left (by linarith) hd0.le
      _ ≤ 5 * L := log_d_T_le hx2 hd1 hd
  -- the tail bound at each grid point
  have hB : ∀ k : ℕ, k < M →
      ∑ χ : DirichletCharacter ℂ d,
        ∑ ρ ∈ (zeroFinset χ (1/2) T).filter (fun ρ : ℂ => 39/50 + k * h ≤ ρ.re), wt χ ρ
      ≤ 29 * CH * Lg * (d:ℝ) ^ ((9/2 : ℝ) * (1 - (39/50 + k * h))) := by
    intro k hk
    have hkM : (k:ℝ) + 1 ≤ M := by exact_mod_cast hk
    have hMlt : (M:ℝ) < (σs - 39/50) * L + 1 := Nat.ceil_lt_add_one (by nlinarith)
    have hσk1 : 39/50 + k * h < σs := by
      have : (k:ℝ) * h < σs - 39/50 := by
        rw [hh, mul_one_div, div_lt_iff₀ hL0]; linarith
      linarith
    have hσk0 : 39/50 ≤ 39/50 + k * h := by
      have : 0 ≤ (k:ℝ) * h := by positivity
      linarith
    have hσk2 : 39/50 + k * h ≤ 1 := by linarith
    have h11 : 1 - (39/50 + k * h) ≤ 11/50 := by linarith
    have h1σ : 0 ≤ 1 - (39/50 + k * h) := by linarith
    have hrw : ∀ χ : DirichletCharacter ℂ d,
        (zeroFinset χ (1/2) T).filter (fun ρ : ℂ => 39/50 + k * h ≤ ρ.re)
          = zeroFinset χ (39/50 + k * h) T :=
      fun χ => (zeroFinset_eq_filter χ (by linarith)).symm
    simp_rw [hrw]
    have he1 : P * (1 - (39/50 + k * h)) ≤ 77/100 := by
      calc P * (1 - (39/50 + k * h)) ≤ (7/2) * (11/50) :=
            mul_le_mul hP h11 h1σ (by norm_num)
        _ = 77/100 := by norm_num
    have ha : c₀ * (P * (1 - (39/50 + k * h))) ≤ 1 - 3/80 := by
      calc c₀ * (P * (1 - (39/50 + k * h))) ≤ (5/4) * (77/100) :=
            mul_le_mul hc₀' he1 (by positivity) (by norm_num)
        _ = 1 - 3/80 := by norm_num
    have hfold := fold d (σ := 39/50 + k * h) (T := T) (C := CH) (c := c₀)
      (e := P * (1 - (39/50 + k * h))) (L := Lg) (s := 3/80) hT2 (by linarith) hLg0
      (by linarith) (by positivity) (by norm_num) (by norm_num) ha
      (fun t ht htT => le_trans (hlog t _ ht hσk0 hσk2)
        (mul_le_mul_of_nonneg_left (hΛ t ht htT) (by positivity)))
    refine le_trans hfold ?_
    have hdpow : (d:ℝ) ^ (P * (1 - (39/50 + k * h)))
        ≤ (d:ℝ) ^ ((9/2 : ℝ) * (1 - (39/50 + k * h))) := by
      apply Real.rpow_le_rpow_of_exponent_le hd1
      apply mul_le_mul_of_nonneg_right _ h1σ
      linarith
    have hdp0 : 0 ≤ (d:ℝ) ^ ((9/2 : ℝ) * (1 - (39/50 + k * h))) := Real.rpow_nonneg hd0.le _
    calc CH * (d:ℝ) ^ (P * (1 - (39/50 + k * h))) * Lg * (2 + 1 / (3/80))
        ≤ CH * (d:ℝ) ^ ((9/2 : ℝ) * (1 - (39/50 + k * h))) * Lg * 29 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdpow (by linarith)) hLg0) (by norm_num)
            (by norm_num) (by positivity)
      _ = 29 * CH * Lg * (d:ℝ) ^ ((9/2 : ℝ) * (1 - (39/50 + k * h))) := by ring
  -- the grid
  have hMh : σs ≤ 39/50 + M * h := by
    have : (σs - 39/50) * L ≤ M := Nat.le_ceil _
    have : σs - 39/50 ≤ M * h := by
      rw [hh, mul_one_div, le_div_iff₀ hL0]; linarith
    linarith
  have hgrid := grid_bound (Finset.univ : Finset (DirichletCharacter ℂ d))
    (fun χ => zeroFinset χ (1/2) T) (fun χ ρ => wt χ ρ) (fun χ ρ => wt_nonneg χ ρ)
    hy1 hh0 M hMh
    (fun k => 29 * CH * Lg * (d:ℝ) ^ ((9/2 : ℝ) * (1 - (39/50 + k * h)))) hB
  have hgeom := grid_geom (d := (d:ℝ)) hx hy1 hyx hd1 (d_ninehalf_le hx1 hd1 hd hy) hσ hσs1
  -- assemble
  have hzone : zoneSum d T y (39/50) σs
      ≤ 29 * CH * Lg * (64 * y * x ^ (-(9/200 : ℝ) * (1 - σs))) := by
    refine le_trans hgrid ?_
    rw [← hM] at hgeom
    have : ∑ k ∈ Finset.range M, y ^ (39/50 + (k + 1) * h)
        * (29 * CH * Lg * (d:ℝ) ^ ((9/2 : ℝ) * (1 - (39/50 + k * h))))
        = 29 * CH * Lg * ∑ k ∈ Finset.range M, y ^ (39/50 + (k + 1) * h)
            * (d:ℝ) ^ ((9/2 : ℝ) * (1 - (39/50 + k * h))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hgeom (by positivity)
  -- the decay: x^{−(9/200)(1−σ*)} = L^{−(9/4)(K+2)}
  have hxσ : x ^ (-(9/200 : ℝ) * (1 - σs)) = L ^ (-(9/4 : ℝ) * ((K:ℝ) + 2)) := by
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hL0, ← hLdef]
    congr 1
    rw [hσs, sigmaStar, ← hLdef]
    field_simp
    ring
  have hLgL : Lg * L ^ (-(9/4 : ℝ) * ((K:ℝ) + 2)) ≤ 5 ^ K * L ^ (-(9/2 : ℝ)) := by
    rw [hLg, mul_pow, ← Real.rpow_natCast L K, mul_assoc, ← Real.rpow_add hL0]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hL
    have : (0:ℝ) ≤ K := Nat.cast_nonneg K
    linarith
  have hLneg : L ^ (-(9/2 : ℝ)) = 1 / L ^ (9/2 : ℝ) := by
    rw [Real.rpow_neg hL0.le, one_div]
  have hL92 : 0 < L ^ (9/2 : ℝ) := Real.rpow_pos_of_pos hL0 _
  calc zoneSum d T y (39/50) σs
      ≤ 29 * CH * Lg * (64 * y * x ^ (-(9/200 : ℝ) * (1 - σs))) := hzone
    _ = 1856 * CH * y * (Lg * L ^ (-(9/4 : ℝ) * ((K:ℝ) + 2))) := by rw [hxσ]; ring
    _ ≤ 1856 * CH * y * (5 ^ K * L ^ (-(9/2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hLgL (by positivity)
    _ = (1856 * 5 ^ K * CH / L ^ (9/2 : ℝ)) * y := by rw [hLneg]; ring
    _ ≤ (ε / 27) * y := by
        apply mul_le_mul_of_nonneg_right _ hy0.le
        rw [div_le_iff₀ hL92]
        linarith
    _ = ε * y / 27 := by ring

/-! #### Zone III -/

/-- **Zone III** (`σ₁ ≤ β < τ`, log-free): the log-free density folded (exponent
`c₀'·(9/2)(1−σ₁) ≤ 1/2`, fold constant `4`) and integrated along the σ-grid gives
`S_III ≤ 256·γ₂·y·e^{−(9/200)ρ}`. -/
theorem zoneIII_le (d : ℕ) [NeZero d] {x y γ₂ c₀' ρ σ₁ : ℝ}
    (hγ : 1 ≤ γ₂) (hc : 1 ≤ c₀')
    (hlf : ∀ (t σ : ℝ), 2 ≤ t → 9/10 ≤ σ → σ ≤ 1 →
      ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
        ≤ γ₂ * ((d : ℝ) * t ^ c₀') ^ ((9/2 : ℝ) * (1 - σ)))
    (hx : Real.exp 1 ≤ x) (hd : (d:ℝ) ≤ x ^ (191/900 : ℝ))
    (hy : (d:ℝ) * x ^ (709/900 : ℝ) ≤ y) (hyx : y ≤ x)
    (hρ : 0 < ρ) (hσ1 : 9/10 ≤ σ₁) (hστ : σ₁ ≤ 1 - ρ / Real.log x)
    (hfold : c₀' * ((9/2 : ℝ) * (1 - σ₁)) ≤ 1/2) :
    zoneSum d (x ^ 3) y σ₁ (1 - ρ / Real.log x) ≤ 256 * γ₂ * y * Real.exp (-(9/200) * ρ) := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd0 : (0:ℝ) < d := by linarith
  have hx2 : 2 ≤ x := by have := Real.exp_one_gt_d9; linarith
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ Real.log x := one_le_log_of_exp_le hx
  have hL0 : 0 < Real.log x := by linarith
  have hxp : (1:ℝ) ≤ x ^ (709/900 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (0:ℝ) ≤ 709/900)
    rwa [Real.rpow_zero] at this
  have hy1 : 1 ≤ y := by nlinarith
  have hy0 : 0 < y := by linarith
  have hT2 : (2:ℝ) ≤ x ^ 3 := by nlinarith [pow_pos hx0 2]
  set L := Real.log x with hLdef
  set T := x ^ 3 with hTdef
  set τ := 1 - ρ / L with hτ
  have hτ1 : τ ≤ 1 := by
    have : 0 ≤ ρ / L := by positivity
    linarith
  set h : ℝ := 1 / L with hh
  have hh0 : 0 < h := by positivity
  set M : ℕ := ⌈(τ - σ₁) * L⌉₊ with hM
  have hB : ∀ k : ℕ, k < M →
      ∑ χ : DirichletCharacter ℂ d,
        ∑ ρ ∈ (zeroFinset χ (1/2) T).filter (fun ρ : ℂ => σ₁ + k * h ≤ ρ.re), wt χ ρ
      ≤ 4 * γ₂ * (d:ℝ) ^ ((9/2 : ℝ) * (1 - (σ₁ + k * h))) := by
    intro k hk
    have hkM : (k:ℝ) + 1 ≤ M := by exact_mod_cast hk
    have hMlt : (M:ℝ) < (τ - σ₁) * L + 1 := Nat.ceil_lt_add_one (by nlinarith)
    have hσk1 : σ₁ + k * h < τ := by
      have : (k:ℝ) * h < τ - σ₁ := by
        rw [hh, mul_one_div, div_lt_iff₀ hL0]; linarith
      linarith
    have hσk0 : σ₁ ≤ σ₁ + k * h := by
      have : 0 ≤ (k:ℝ) * h := by positivity
      linarith
    have hσk2 : σ₁ + k * h ≤ 1 := by linarith
    have h1σ : 0 ≤ 1 - (σ₁ + k * h) := by linarith
    have hrw : ∀ χ : DirichletCharacter ℂ d,
        (zeroFinset χ (1/2) T).filter (fun ρ : ℂ => σ₁ + k * h ≤ ρ.re)
          = zeroFinset χ (σ₁ + k * h) T :=
      fun χ => (zeroFinset_eq_filter χ (by linarith)).symm
    simp_rw [hrw]
    have ha : c₀' * ((9/2 : ℝ) * (1 - (σ₁ + k * h))) ≤ 1 - 1/2 := by
      refine le_trans ?_ (hfold.trans (by norm_num))
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      linarith
    have hfold' := fold d (σ := σ₁ + k * h) (T := T) (C := γ₂) (c := c₀')
      (e := (9/2 : ℝ) * (1 - (σ₁ + k * h))) (L := 1) (s := 1/2) hT2 (by linarith) zero_le_one
      (by linarith) (by positivity) (by norm_num) (by norm_num) ha
      (fun t ht htT => by
        rw [mul_one]
        exact hlf t _ ht (by linarith) hσk2)
    refine le_trans hfold' (le_of_eq ?_)
    norm_num
    ring
  have hMh : τ ≤ σ₁ + M * h := by
    have : (τ - σ₁) * L ≤ M := Nat.le_ceil _
    have : τ - σ₁ ≤ M * h := by
      rw [hh, mul_one_div, le_div_iff₀ hL0]; linarith
    linarith
  have hgrid := grid_bound (Finset.univ : Finset (DirichletCharacter ℂ d))
    (fun χ => zeroFinset χ (1/2) T) (fun χ ρ => wt χ ρ) (fun χ ρ => wt_nonneg χ ρ)
    hy1 hh0 M hMh
    (fun k => 4 * γ₂ * (d:ℝ) ^ ((9/2 : ℝ) * (1 - (σ₁ + k * h)))) hB
  have hgeom := grid_geom (d := (d:ℝ)) hx hy1 hyx hd1 (d_ninehalf_le hx1 hd1 hd hy) hστ hτ1
  rw [← hM] at hgeom
  have hzone : zoneSum d T y σ₁ τ ≤ 4 * γ₂ * (64 * y * x ^ (-(9/200 : ℝ) * (1 - τ))) := by
    refine le_trans hgrid ?_
    have : ∑ k ∈ Finset.range M, y ^ (σ₁ + (k + 1) * h)
        * (4 * γ₂ * (d:ℝ) ^ ((9/2 : ℝ) * (1 - (σ₁ + k * h))))
        = 4 * γ₂ * ∑ k ∈ Finset.range M, y ^ (σ₁ + (k + 1) * h)
            * (d:ℝ) ^ ((9/2 : ℝ) * (1 - (σ₁ + k * h))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hgeom (by positivity)
  have hxτ : x ^ (-(9/200 : ℝ) * (1 - τ)) = Real.exp (-(9/200) * ρ) := by
    rw [Real.rpow_def_of_pos hx0, ← hLdef]
    congr 1
    rw [hτ]
    field_simp
    ring
  rw [hxτ] at hzone
  linarith

/-! #### Zone IV -/

/-- **Zone IV(b)** (`τ ≤ β < 1`, `|γ| > ν`): given that no zero of any `χ mod d`
lies in `[τ,1] × [−ν,ν]` (zone IV(a), the census), each remaining zero weighs at
most `y/ν`, and the log-free density at `σ = τ`, `t = x³` counts them by
`γ₂·e^{28ρ}`. -/
theorem zoneIV_le (d : ℕ) [NeZero d] {x y γ₂ c₀' ρ ν : ℝ}
    (hγ : 1 ≤ γ₂) (_hc : 1 ≤ c₀') (hc2 : c₀' ≤ 2)
    (hlf : ∀ (t σ : ℝ), 2 ≤ t → 9/10 ≤ σ → σ ≤ 1 →
      ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
        ≤ γ₂ * ((d : ℝ) * t ^ c₀') ^ ((9/2 : ℝ) * (1 - σ)))
    (hx : Real.exp 1 ≤ x) (hd : (d:ℝ) ≤ x ^ (191/900 : ℝ)) (hy1 : 1 ≤ y)
    (hρ : 0 < ρ) (hν : 0 < ν) (hxρ : 10 * ρ ≤ Real.log x)
    (hempty : ∀ χ : DirichletCharacter ℂ d, ∀ ζ ∈ zeroFinset χ (1/2) (x ^ 3),
      1 - ρ / Real.log x ≤ ζ.re → |ζ.im| ≤ ν → False) :
    zoneSum d (x ^ 3) y (1 - ρ / Real.log x) 1 ≤ γ₂ * Real.exp (28 * ρ) * y / ν := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd0 : (0:ℝ) < d := by linarith
  have hx2 : 2 ≤ x := by have := Real.exp_one_gt_d9; linarith
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ Real.log x := one_le_log_of_exp_le hx
  have hL0 : 0 < Real.log x := by linarith
  have hy0 : 0 < y := by linarith
  have hT2 : (2:ℝ) ≤ x ^ 3 := by nlinarith [pow_pos hx0 2]
  set L := Real.log x with hLdef
  set T := x ^ 3 with hTdef
  set τ := 1 - ρ / L with hτ
  have hτ9 : 9/10 ≤ τ := by
    rw [hτ]
    have : ρ / L ≤ 1/10 := by
      rw [div_le_iff₀ hL0]; linarith
    linarith
  have hτ1 : τ ≤ 1 := by
    have : 0 ≤ ρ / L := by positivity
    linarith
  -- Step 1: each remaining zero weighs at most `ord·y/ν`
  have hpt : ∀ χ : DirichletCharacter ℂ d,
      ∑ ρ ∈ (zeroFinset χ (1/2) T).filter (fun ρ : ℂ => τ ≤ ρ.re ∧ ρ.re < 1), wt χ ρ * y ^ ρ.re
        ≤ (y / ν) * (zeroCountBox χ τ T : ℝ) := by
    intro χ
    rw [zeroCountBox_real, Finset.mul_sum]
    calc ∑ ρ ∈ (zeroFinset χ (1/2) T).filter (fun ρ : ℂ => τ ≤ ρ.re ∧ ρ.re < 1),
          wt χ ρ * y ^ ρ.re
        ≤ ∑ ρ ∈ (zeroFinset χ (1/2) T).filter (fun ρ : ℂ => τ ≤ ρ.re ∧ ρ.re < 1),
          (y / ν) * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
          refine Finset.sum_le_sum fun ζ hζ => ?_
          rw [Finset.mem_filter] at hζ
          have hbig : ν < |ζ.im| := by
            by_contra hcon
            exact hempty χ ζ hζ.1 hζ.2.1 (not_lt.mp hcon)
          have hw : wt χ ζ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ζ : ℝ) / ν := by
            unfold wt
            apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) hν
            linarith
          have hyr : y ^ ζ.re ≤ y := by
            have := Real.rpow_le_rpow_of_exponent_le hy1 hζ.2.2.le
            rwa [Real.rpow_one] at this
          calc wt χ ζ * y ^ ζ.re
              ≤ ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ζ : ℝ) / ν) * y :=
                mul_le_mul hw hyr (Real.rpow_nonneg hy0.le _) (by positivity)
            _ = (y / ν) * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ζ : ℝ) := by ring
      _ ≤ ∑ ρ ∈ zeroFinset χ τ T,
          (y / ν) * (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro ζ hζ
            rw [Finset.mem_filter, mem_zeroFinset] at hζ
            rw [mem_zeroFinset]
            exact ⟨hζ.2.1, hζ.1.2.1, hζ.1.2.2.1, hζ.1.2.2.2⟩
          · intro ζ _ _
            positivity
  have h1 : zoneSum d T y τ 1 ≤ (y / ν) * ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ τ T : ℝ) := by
    unfold zoneSum
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun χ _ => hpt χ
  -- Step 2: the count at `σ = τ`, `t = T`
  have h2 : ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ τ T : ℝ) ≤ γ₂ * Real.exp (28 * ρ) := by
    refine le_trans (hlf T τ hT2 hτ9 hτ1) ?_
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    have hTc : T ^ c₀' ≤ x ^ (6:ℝ) := by
      rw [hTdef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      apply Real.rpow_le_rpow_of_exponent_le hx1
      push_cast; linarith
    have hdT : (d:ℝ) * T ^ c₀' ≤ x ^ (191/900 + 6 : ℝ) := by
      rw [Real.rpow_add hx0]
      exact mul_le_mul hd hTc (by positivity) (by positivity)
    have he0 : 0 ≤ (9/2 : ℝ) * (1 - τ) := by linarith
    calc ((d:ℝ) * T ^ c₀') ^ ((9/2 : ℝ) * (1 - τ))
        ≤ (x ^ (191/900 + 6 : ℝ)) ^ ((9/2 : ℝ) * (1 - τ)) :=
          Real.rpow_le_rpow (by positivity) hdT he0
      _ = Real.exp (L * ((191/900 + 6) * ((9/2 : ℝ) * (1 - τ)))) := by
          rw [← Real.rpow_mul hx0.le, Real.rpow_def_of_pos hx0]
      _ ≤ Real.exp (28 * ρ) := by
          rw [Real.exp_le_exp, hτ]
          have : L * ((191/900 + 6) * ((9/2 : ℝ) * (1 - (1 - ρ / L)))) = (5591/200) * ρ := by
            field_simp
            ring
          rw [this]
          linarith
  calc zoneSum d T y τ 1 ≤ (y / ν) * (γ₂ * Real.exp (28 * ρ)) :=
        le_trans h1 (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = γ₂ * Real.exp (28 * ρ) * y / ν := by ring

end Zones

/-! ### Zone IV(a): the exceptional set and the zero transfer -/

section BadSet

open Classical in
/-- **The exceptional set** `𝓓(x)` (Z0a §1): conductors `d' ∈ [2, x^{191/900}]`
carrying a primitive character with a zero in `[τ,1] × [−ν,ν]`, `τ = 1 − ρ/log x`;
empty below the threshold `x₀` (so that the census bound is available). -/
noncomputable def badSet (ρ ν x₀ : ℝ) (x : ℕ) : Finset ℕ :=
  if x₀ ≤ (x:ℝ) then
    (Finset.Icc 2 ⌊(x:ℝ) ^ (191/900 : ℝ)⌋₊).filter
      (fun m => (Census.badChars (1 - ρ / Real.log x) ν m).Nonempty)
  else ∅

lemma badSet_ge_two (ρ ν x₀ : ℝ) (x : ℕ) : ∀ m ∈ badSet ρ ν x₀ x, 2 ≤ m := by
  intro m hm
  unfold badSet at hm
  split_ifs at hm with h
  · rw [Finset.mem_filter, Finset.mem_Icc] at hm
    exact hm.1.1
  · simp at hm

/-- The census bound `|𝓓(x)| ≤ c₂(ν)·e^{(191/900)c₃ρ}`, uniform in `x`. -/
lemma badSet_card_le {ρ ν x₀ : ℝ} (hν : 1 ≤ ν) (hρ : 0 < ρ)
    (hx₀ : ∀ x : ℕ, x₀ ≤ x → (2:ℝ) ≤ (x:ℝ) ^ (191/900 : ℝ) ∧ 1 < (x:ℝ)
      ∧ 39/40 ≤ 1 - ρ / Real.log x) (x : ℕ) :
    ((badSet ρ ν x₀ x).card : ℝ)
      ≤ Census.censusC₂ ν * Real.exp ((191/900) * Census.censusC₃ * ρ) := by
  have hc2 : 0 ≤ Census.censusC₂ ν := by
    unfold Census.censusC₂
    have : (0:ℝ) ≤ (10:ℝ) ^ (1000000000 : ℕ) := pow_nonneg (by norm_num) _
    have : (0:ℝ) ≤ ν + 2 := by linarith
    positivity
  unfold badSet
  split_ifs with h
  · obtain ⟨hZ, hx1, hτ⟩ := hx₀ x h
    have hx0 : (0:ℝ) < x := by linarith
    have hL0 : 0 < Real.log x := Real.log_pos hx1
    have hτ1 : 1 - ρ / Real.log x ≤ 1 := by
      have : 0 ≤ ρ / Real.log x := by positivity
      linarith
    refine le_trans (Census.card_badConductors_le Carmichael.CensusMid.midCensusHyp hτ hτ1 hν hZ
      _ ?_) (le_of_eq ?_)
    · intro m hm
      rw [Finset.mem_filter, Finset.mem_Icc] at hm
      refine ⟨hm.1.1, ?_, hm.2⟩
      exact le_trans (by exact_mod_cast hm.1.2) (Nat.floor_le (by positivity))
    · congr 1
      rw [← Real.rpow_mul hx0.le, Real.rpow_def_of_pos hx0]
      congr 1
      field_simp
      ring
  · rw [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hc2 (Real.exp_pos _).le

/-- A nontrivial Euler factor does not vanish at `Re s > 0`. -/
lemma euler_factor_prim_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 0 < s.re) :
    ∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hp0 : (0:ℝ) < p := by positivity
  have hnorm : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    have h1 : ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ ≤ 1 :=
      DirichletCharacter.norm_le_one _ _
    have h2 : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [show ((p:ℕ):ℂ) = ((p:ℝ):ℂ) by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hp0]
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · exact_mod_cast hp2.trans_lt' one_lt_two
      · simpa using hs
    have h0 : 0 ≤ ‖(p : ℂ) ^ (-s)‖ := norm_nonneg _
    calc ‖χ.primitiveCharacter (p : ZMod χ.conductor)‖ * ‖(p : ℂ) ^ (-s)‖
        ≤ 1 * ‖(p : ℂ) ^ (-s)‖ := mul_le_mul_of_nonneg_right h1 h0
      _ < 1 := by linarith
  intro h
  rw [sub_eq_zero] at h
  rw [← h] at hnorm
  simp at hnorm

/-- **Zero transfer (zone IV(a)).**  If `ζ` has no zero in `[τ,1] × [−ν,ν]` and no
member of the exceptional set divides `d`, then no `χ mod d` has a zero there:
zeros of `χ` with `Re > 0` are zeros of the inducing primitive character, whose
conductor divides `d` and is either `1` (ζ) or a member of `𝓓(x)`. -/
theorem no_zero_in_box (d : ℕ) [NeZero d] {x τ ν T : ℝ} (hτ : 0 < τ)
    (hζ : ∀ s : ℂ, τ ≤ s.re → s.re ≤ 1 → |s.im| ≤ ν → riemannZeta s ≠ 0)
    (hd : (d:ℝ) ≤ x ^ (191/900 : ℝ))
    (hbad : ∀ m ∈ (Finset.Icc 2 ⌊x ^ (191/900 : ℝ)⌋₊).filter
      (fun m => (Census.badChars τ ν m).Nonempty), ¬ m ∣ d) :
    ∀ χ : DirichletCharacter ℂ d, ∀ ζ ∈ zeroFinset χ (1/2) T, τ ≤ ζ.re → |ζ.im| ≤ ν → False := by
  intro χ ζ hζmem hre him
  rw [mem_zeroFinset] at hζmem
  obtain ⟨hhalf, hre1, _, hne1, hL0⟩ := hζmem
  have hrepos : 0 < ζ.re := by linarith
  -- the mod-1 case, stated for an arbitrary level equal to 1
  have key1 : ∀ (n : ℕ) [NeZero n] (ψ : DirichletCharacter ℂ n), n = 1 →
      DirichletCharacter.LFunction ψ ζ = 0 → False := by
    intro n _ ψ hn hψ
    subst hn
    rw [DirichletCharacter.LFunction_modOne_eq] at hψ
    exact hζ ζ hre hre1 him hψ
  by_cases hχ : χ = 1
  · subst hχ
    have hfact : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ d) ζ
        = (∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-ζ))) * riemannZeta ζ :=
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hne1
    rw [hfact] at hL0
    rcases mul_eq_zero.mp hL0 with h | h
    · exact absurd h (by simpa [eulerFactor] using eulerFactor_ne_zero (N := d) hrepos)
    · exact hζ ζ hre hre1 him h
  · rw [LFunction_eq_primitive_mul_prod hχ ζ] at hL0
    rcases mul_eq_zero.mp hL0 with h | h
    · -- the primitive character vanishes at ζ
      set c := χ.conductor with hc
      have hcd : c ∣ d := χ.conductor_dvd_level
      have hc0 : c ≠ 0 := by
        intro h0
        rw [h0] at hcd
        exact NeZero.ne d (Nat.eq_zero_of_zero_dvd hcd)
      have : NeZero c := ⟨hc0⟩
      rcases Nat.lt_or_ge c 2 with hc1 | hc2
      · have : c = 1 := by omega
        exact key1 c χ.primitiveCharacter this h
      · have hmem : c ∈ (Finset.Icc 2 ⌊x ^ (191/900 : ℝ)⌋₊).filter
            (fun m => (Census.badChars τ ν m).Nonempty) := by
          rw [Finset.mem_filter, Finset.mem_Icc]
          refine ⟨⟨hc2, ?_⟩, ?_⟩
          · apply Nat.le_floor
            have : (c:ℝ) ≤ d := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne d)) hcd
            linarith
          · refine ⟨χ.primitiveCharacter, ?_⟩
            rw [Census.mem_badChars]
            refine ⟨χ.primitiveCharacter_isPrimitive, ⟨ζ, ?_⟩⟩
            rw [mem_zeroFinset]
            exact ⟨hre, hre1, him, hne1, h⟩
        exact hbad c hmem hcd
    · exact euler_factor_prim_ne_zero χ hrepos h

end BadSet

/-! ### The explicit formula for every character mod `d` -/

section ExplicitFormula

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
lemma psiChi_eq_psiChar (χ : DirichletCharacter ℂ d) (y : ℝ) :
    EF.psiChi χ y = psiChar χ y := by
  rw [EF.psiChi, psiChar_def]
  have hcomm : ∀ n : ℕ, χ (n : ZMod d) * (ArithmeticFunction.vonMangoldt n : ℂ)
      = (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d) := fun n => mul_comm _ _
  simp only [hcomm]
  symm
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_Ioc] at hn
    rw [Finset.mem_range]; omega
  · intro n hn hn'
    rw [Finset.mem_range] at hn
    rw [Finset.mem_Ioc] at hn'
    have : n = 0 := by omega
    subst this
    simp

/-- The zero set of the principal character mod `d` coincides with that of `ζ`
(as the mod-1 character), on any box with `σ > 0`. -/
lemma zeroFinset_trivChar_eq {σ T : ℝ} (hσ : 0 < σ) :
    zeroFinset (1 : DirichletCharacter ℂ d) σ T
      = zeroFinset (1 : DirichletCharacter ℂ 1) σ T := by
  ext ρ
  rw [mem_zeroFinset, mem_zeroFinset]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, h4, ?_⟩
    rw [DirichletCharacter.LFunction_modOne_eq]
    have hρre : 0 < ρ.re := lt_of_lt_of_le hσ h1
    have hfact : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ d) ρ
        = (∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-ρ))) * riemannZeta ρ :=
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta h4
    rw [hfact] at h5
    rcases mul_eq_zero.mp h5 with h | h
    · exact absurd h (by simpa [eulerFactor] using eulerFactor_ne_zero (N := d) hρre)
    · exact h
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, h4, ?_⟩
    rw [DirichletCharacter.LFunction_modOne_eq] at h5
    have hfact : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ d) ρ
        = (∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-ρ))) * riemannZeta ρ :=
      DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta h4
    rw [hfact, h5, mul_zero]

/-- The zero sum of the principal character mod `d` equals the `ζ` zero sum. -/
lemma zeroSum_trivChar_eq {T : ℝ} (y : ℝ) :
    ∑ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ d) (1/2) T,
        (analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ d)) ρ : ℂ)
          * ((y:ℂ) ^ ρ / ρ)
      = ∑ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T,
        (analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ρ : ℂ)
          * ((y:ℂ) ^ ρ / ρ) := by
  rw [zeroFinset_trivChar_eq (by norm_num)]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [mem_zeroFinset] at hρ
  have hρre : 0 < ρ.re := by linarith [hρ.1]
  rw [analyticOrderNatAt_trivChar_eq hρre hρ.2.2.2.1, DirichletCharacter.LFunction_modOne_eq]

/-- The principal character mod `d` versus the mod-1 character: the twisted `ψ`'s
differ by the prime powers dividing `d`, at most `ω(d)·log y`. -/
lemma psiChar_one_sub_le {y : ℝ} (hy : 1 ≤ y) :
    ‖psiChar (1 : DirichletCharacter ℂ d) y - psiChar (1 : DirichletCharacter ℂ 1) y‖
      ≤ (d.primeFactors.card : ℝ) * Real.log y := by
  rw [psiChar_def, psiChar_def, ← Finset.sum_sub_distrib]
  have hpt : ∀ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      ‖(1 : DirichletCharacter ℂ d) n * (ArithmeticFunction.vonMangoldt n : ℂ)
          - (1 : DirichletCharacter ℂ 1) n * (ArithmeticFunction.vonMangoldt n : ℂ)‖
        ≤ (if n.Coprime d then 0 else ArithmeticFunction.vonMangoldt n) := by
    intro n _
    have h1 : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 :=
      MulChar.one_apply (isUnit_of_subsingleton _)
    rw [h1, one_mul]
    by_cases hn : n.Coprime d
    · rw [if_pos hn, MulChar.one_apply ((ZMod.isUnit_iff_coprime n d).mpr hn), one_mul,
        sub_self, norm_zero]
    · rw [if_neg hn]
      have hunit : ¬IsUnit ((n : ZMod d)) := fun h =>
        hn ((ZMod.isUnit_iff_coprime n d).mp h)
      rw [MulChar.map_nonunit _ hunit, zero_mul, zero_sub, norm_neg, Complex.norm_real,
        Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hpt) ?_)
  have hsum : ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, (if n.Coprime d then 0 else ArithmeticFunction.vonMangoldt n)
      = ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n : ℕ => ¬n.Coprime d),
          ArithmeticFunction.vonMangoldt n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n.Coprime d <;> simp [hn]
  rw [hsum]
  exact sum_vonMangoldt_not_coprime_le (NeZero.ne d) hy

/-- The explicit-formula error term at level `d`, height `T`, point `y`
(`C₅ = 10¹²`). -/
noncomputable def efErr (d : ℕ) (T y : ℝ) : ℝ :=
  10 ^ 12 * (y * Real.log ((d:ℝ) * T * y) ^ 2 / T
    + y ^ ((5:ℝ)/8) * Real.log ((d:ℝ) * (T + 2)) ^ 2 + Real.log ((d:ℝ) * T * y) ^ 2)

/-- **The explicit formula for every character mod `d`** (principal included): the
principal case goes through `ζ` (level 1), with the imprimitive correction
`ω(d)·log y` added to the error. -/
theorem explicit_formula_all (χ : DirichletCharacter ℂ d) {y T : ℝ} (hy : 100 ≤ y)
    (hT : 2 ≤ T) (hyd : (d:ℝ) ≤ y) :
    ‖psiChar χ y - (if χ = 1 then (y:ℂ) else 0)
        + ∑ ρ ∈ zeroFinset χ (1/2) T,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((y:ℂ) ^ ρ / ρ)‖
      ≤ efErr d T y + (d.primeFactors.card : ℝ) * Real.log y := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hy0 : 0 < y := by linarith
  have hT0 : 0 < T := by linarith
  have hω : 0 ≤ (d.primeFactors.card : ℝ) * Real.log y :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith))
  by_cases hχ : χ = 1
  · subst hχ
    rw [if_pos rfl]
    have hEF := EF.explicit_formula (1 : DirichletCharacter ℂ 1) (Or.inr rfl) hy hT
      (by rw [Nat.cast_one]; linarith)
    rw [if_pos rfl, psiChi_eq_psiChar, Nat.cast_one, one_mul, one_mul] at hEF
    have hsplit : psiChar (1 : DirichletCharacter ℂ d) y - (y:ℂ)
        + ∑ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ d) (1/2) T,
            (analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ d)) ρ : ℂ)
              * ((y:ℂ) ^ ρ / ρ)
        = (psiChar (1 : DirichletCharacter ℂ d) y - psiChar (1 : DirichletCharacter ℂ 1) y)
          + (psiChar (1 : DirichletCharacter ℂ 1) y - (y:ℂ)
            + ∑ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T,
              (analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ρ : ℂ)
                * ((y:ℂ) ^ ρ / ρ)) := by
      rw [zeroSum_trivChar_eq]; ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    have h1 := psiChar_one_sub_le (d := d) (y := y) (by linarith)
    -- the level-1 error is dominated by the level-d error
    have hlog1 : Real.log (T * y) ≤ Real.log ((d:ℝ) * T * y) := by
      apply Real.log_le_log (by positivity)
      nlinarith [mul_pos hT0 hy0]
    have hlog2 : Real.log (T + 2) ≤ Real.log ((d:ℝ) * (T + 2)) := by
      apply Real.log_le_log (by positivity)
      nlinarith
    have hl1 : 0 ≤ Real.log (T * y) := Real.log_nonneg (by nlinarith)
    have hl2 : 0 ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
    have hsq1 : Real.log (T * y) ^ 2 ≤ Real.log ((d:ℝ) * T * y) ^ 2 := by nlinarith
    have hsq2 : Real.log (T + 2) ^ 2 ≤ Real.log ((d:ℝ) * (T + 2)) ^ 2 := by nlinarith
    have hEF' : ‖psiChar (1 : DirichletCharacter ℂ 1) y - (y:ℂ)
        + ∑ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T,
            (analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ρ : ℂ)
              * ((y:ℂ) ^ ρ / ρ)‖ ≤ efErr d T y := by
      refine le_trans hEF ?_
      unfold efErr
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hy58 : 0 ≤ y ^ ((5:ℝ)/8) := Real.rpow_nonneg hy0.le _
      have ha : y * Real.log (T * y) ^ 2 / T ≤ y * Real.log ((d:ℝ) * T * y) ^ 2 / T := by
        apply div_le_div_of_nonneg_right _ hT0.le
        exact mul_le_mul_of_nonneg_left hsq1 hy0.le
      have hb : y ^ ((5:ℝ)/8) * Real.log (T + 2) ^ 2
          ≤ y ^ ((5:ℝ)/8) * Real.log ((d:ℝ) * (T + 2)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq2 hy58
      linarith
    linarith
  · rw [if_neg hχ, sub_zero]
    have hEF := EF.explicit_formula χ (Or.inl hχ) hy hT hyd
    rw [if_neg hχ, sub_zero, psiChi_eq_psiChar] at hEF
    unfold efErr
    linarith

end ExplicitFormula

/-! ### Orthogonality assembly -/

section Orthogonality

variable {d : ℕ} [NeZero d]

lemma card_dirichletCharacter_eq :
    ((Finset.univ : Finset (DirichletCharacter ℂ d)).card : ℝ) = d.totient := by
  have h1 : Nat.card (DirichletCharacter ℂ d) = d.totient :=
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h1]

lemma norm_zeroSum_le (χ : DirichletCharacter ℂ d) {y T : ℝ} (hy : 0 < y) :
    ‖∑ ρ ∈ zeroFinset χ (1/2) T,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((y:ℂ) ^ ρ / ρ)‖
      ≤ 3 * ∑ ρ ∈ zeroFinset χ (1/2) T, wt χ ρ * y ^ ρ.re := by
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  rw [mem_zeroFinset] at hρ
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at hρ; norm_num at hρ
  have hnρ : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ0
  have hre : 1/2 ≤ |ρ.re| := le_trans hρ.1 (le_abs_self _)
  have h3 : 1 + |ρ.im| ≤ 3 * ‖ρ‖ := by
    have := Complex.abs_re_le_norm ρ
    have := Complex.abs_im_le_norm ρ
    linarith
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  unfold wt
  have hord : (0:ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) :=
    Nat.cast_nonneg _
  have hyr : 0 ≤ y ^ ρ.re := Real.rpow_nonneg hy.le _
  have key : y ^ ρ.re / ‖ρ‖ ≤ y ^ ρ.re * (3 / (1 + |ρ.im|)) := by
    rw [div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_left _ hyr
    rw [div_le_div_iff₀ hnρ (by positivity)]
    linarith
  calc (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) * (y ^ ρ.re / ‖ρ‖)
      ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
          * (y ^ ρ.re * (3 / (1 + |ρ.im|))) := mul_le_mul_of_nonneg_left key hord
    _ = _ := by ring

/-- **ψ in progressions from the explicit formula**: for `a` a unit mod `d`,
`|ψ(y;d,a) − y/φ(d)| ≤ efErr + ω(d)·log y + (3/φ(d))·(full weighted zero sum)`. -/
theorem psiAP_sub_le {a : ZMod d} (ha : IsUnit a) {y T : ℝ} (hy : 100 ≤ y) (hT : 2 ≤ T)
    (hyd : (d:ℝ) ≤ y) :
    |psiAP a y - y / d.totient|
      ≤ efErr d T y + (d.primeFactors.card : ℝ) * Real.log y
        + 3 / d.totient * zeroSumTotal d T y := by
  have hy0 : 0 < y := by linarith
  have hφ : (0:ℝ) < d.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hainv : IsUnit (a⁻¹) := by
    rw [← ha.unit_spec, ZMod.inv_coe_unit]; exact Units.isUnit _
  set Z : DirichletCharacter ℂ d → ℂ := fun χ => ∑ ρ ∈ zeroFinset χ (1/2) T,
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((y:ℂ) ^ ρ / ρ) with hZ
  set E : DirichletCharacter ℂ d → ℂ := fun χ =>
    psiChar χ y - (if χ = 1 then (y:ℂ) else 0) + Z χ with hE
  have hpsi : ∀ χ, psiChar χ y = (if χ = 1 then (y:ℂ) else 0) - Z χ + E χ := by
    intro χ; simp only [hE]; ring
  have horth := psiAP_eq_inv_totient_mul_sum_psiChar ha y
  simp_rw [hpsi, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at horth
  have hmain : ∑ χ : DirichletCharacter ℂ d, χ a⁻¹ * (if χ = 1 then (y:ℂ) else 0) = y := by
    rw [Finset.sum_eq_single (1 : DirichletCharacter ℂ d)]
    · rw [if_pos rfl, MulChar.one_apply hainv, one_mul]
    · intro χ _ hχ; rw [if_neg hχ, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hmain] at horth
  -- the complex identity for the deviation
  have hdev : ((psiAP a y - y / d.totient : ℝ) : ℂ)
      = (d.totient : ℂ)⁻¹ * (∑ χ : DirichletCharacter ℂ d, χ a⁻¹ * E χ
          - ∑ χ : DirichletCharacter ℂ d, χ a⁻¹ * Z χ) := by
    push_cast
    rw [horth]
    have hφc : (d.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
    field_simp
    ring
  have hnorm : |psiAP a y - y / d.totient|
      = ‖((psiAP a y - y / d.totient : ℝ) : ℂ)‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm, hdev, norm_mul, norm_inv, Complex.norm_natCast]
  -- bound the two sums
  have hEχ : ∀ χ : DirichletCharacter ℂ d, ‖χ a⁻¹ * E χ‖
      ≤ efErr d T y + (d.primeFactors.card : ℝ) * Real.log y := by
    intro χ
    rw [norm_mul]
    calc ‖χ a⁻¹‖ * ‖E χ‖ ≤ 1 * ‖E χ‖ :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one _ _) (norm_nonneg _)
      _ = ‖E χ‖ := one_mul _
      _ ≤ _ := explicit_formula_all χ hy hT hyd
  have hZχ : ∀ χ : DirichletCharacter ℂ d, ‖χ a⁻¹ * Z χ‖
      ≤ 3 * ∑ ρ ∈ zeroFinset χ (1/2) T, wt χ ρ * y ^ ρ.re := by
    intro χ
    rw [norm_mul]
    calc ‖χ a⁻¹‖ * ‖Z χ‖ ≤ 1 * ‖Z χ‖ :=
          mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one _ _) (norm_nonneg _)
      _ = ‖Z χ‖ := one_mul _
      _ ≤ _ := norm_zeroSum_le χ hy0
  have hsumE : ‖∑ χ : DirichletCharacter ℂ d, χ a⁻¹ * E χ‖
      ≤ (d.totient : ℝ) * (efErr d T y + (d.primeFactors.card : ℝ) * Real.log y) := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun χ _ => hEχ χ) ?_
    rw [Finset.sum_const, nsmul_eq_mul, card_dirichletCharacter_eq]
  have hsumZ : ‖∑ χ : DirichletCharacter ℂ d, χ a⁻¹ * Z χ‖ ≤ 3 * zeroSumTotal d T y := by
    refine le_trans (norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum fun χ _ => hZχ χ) ?_
    unfold zeroSumTotal
    rw [Finset.mul_sum]
  calc (d.totient : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ d, χ a⁻¹ * E χ
        - ∑ χ : DirichletCharacter ℂ d, χ a⁻¹ * Z χ‖
      ≤ (d.totient : ℝ)⁻¹ * (‖∑ χ : DirichletCharacter ℂ d, χ a⁻¹ * E χ‖
          + ‖∑ χ : DirichletCharacter ℂ d, χ a⁻¹ * Z χ‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)
    _ ≤ (d.totient : ℝ)⁻¹ * ((d.totient : ℝ) * (efErr d T y
          + (d.primeFactors.card : ℝ) * Real.log y) + 3 * zeroSumTotal d T y) :=
        mul_le_mul_of_nonneg_left (add_le_add hsumE hsumZ) (by positivity)
    _ = efErr d T y + (d.primeFactors.card : ℝ) * Real.log y
        + 3 / d.totient * zeroSumTotal d T y := by
        field_simp

/-- **θ in progressions from the explicit formula**: add the prime-power gap
`ψ − θ ≤ 2√y·log y`. -/
theorem thetaAP_sub_le {a : ZMod d} (ha : IsUnit a) {y T : ℝ} (hy : 100 ≤ y) (hT : 2 ≤ T)
    (hyd : (d:ℝ) ≤ y) :
    |thetaAP a y - y / d.totient|
      ≤ efErr d T y + (d.primeFactors.card : ℝ) * Real.log y
        + 3 / d.totient * zeroSumTotal d T y + 2 * Real.sqrt y * Real.log y := by
  have h1 := psiAP_sub_le ha hy hT hyd
  have h2 := psiAP_sub_thetaAP_le_sqrt_mul_log a (by linarith : 1 ≤ y)
  have h3 := psiAP_sub_thetaAP_nonneg a y
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [h1.1, h1.2]

end Orthogonality

/-! ### Truncation and the small terms at `T = x³` -/

section Truncation

lemma omega_le_self (d : ℕ) : (d.primeFactors.card : ℝ) ≤ d := by
  have h1 : d.primeFactors ⊆ d.divisors := fun p hp => by
    rw [Nat.mem_primeFactors] at hp
    exact Nat.mem_divisors.mpr ⟨hp.2.1, hp.2.2⟩
  exact_mod_cast (Finset.card_le_card h1).trans (Nat.card_divisors_le_self d)

lemma one_le_rpow_of_one_le {x r : ℝ} (hx : 1 ≤ x) (hr : 0 ≤ r) : 1 ≤ x ^ r := by
  have := Real.rpow_le_rpow_of_exponent_le hx hr
  rwa [Real.rpow_zero] at this

/-- **Truncation** (Z0a §2): at `T = x³` the three explicit-formula error terms total
at most `75·10¹²·log²x·y^{5/8} ≤ (ε/9)·y/d` once `675·10¹²·log²x ≤ ε·x^{293/1800}`. -/
theorem efErr_le (d : ℕ) [NeZero d] {x y ε : ℝ} (hx : Real.exp 1 ≤ x) (hx2 : 2 ≤ x)
    (hd : (d:ℝ) ≤ x ^ (191/900 : ℝ)) (hy : (d:ℝ) * x ^ (709/900 : ℝ) ≤ y) (hyx : y ≤ x)
    (hxa : 675 * 10 ^ 12 * Real.log x ^ 2 ≤ ε * x ^ (293/1800 : ℝ)) :
    efErr d (x ^ 3) y ≤ ε / 9 * y / d := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd0 : (0:ℝ) < d := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ Real.log x := one_le_log_of_exp_le hx
  have hy1 : 1 ≤ y := by nlinarith [one_le_rpow_of_one_le hx1 (by norm_num : (0:ℝ) ≤ 709/900)]
  have hy0 : 0 < y := by linarith
  have hdx : (d:ℝ) ≤ x := le_trans hd (Real.rpow_le_self_of_one_le hx1 (by norm_num))
  have hT0 : (0:ℝ) < x ^ 3 := by positivity
  set L := Real.log x with hLdef
  set T := x ^ 3 with hTdef
  have hlog1 : Real.log ((d:ℝ) * T * y) ≤ 5 * L := by
    calc Real.log ((d:ℝ) * T * y) ≤ Real.log (x * x ^ 3 * x) := by
          apply Real.log_le_log (by positivity)
          apply mul_le_mul (mul_le_mul_of_nonneg_right hdx hT0.le) hyx hy0.le (by positivity)
      _ = 5 * L := by
          rw [show x * x ^ 3 * x = x ^ 5 by ring, Real.log_pow]; push_cast; ring
  have hlog10 : 0 ≤ Real.log ((d:ℝ) * T * y) := Real.log_nonneg (by
    have : (1:ℝ) ≤ T := by nlinarith [pow_pos hx0 2]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hd1 this) hy1)
  have hlog2 : Real.log ((d:ℝ) * (T + 2)) ≤ 5 * L := log_d_T_le hx2 hd1 hd
  have hlog20 : 0 ≤ Real.log ((d:ℝ) * (T + 2)) := Real.log_nonneg (by nlinarith)
  have hsq1 : Real.log ((d:ℝ) * T * y) ^ 2 ≤ 25 * L ^ 2 := by nlinarith
  have hsq2 : Real.log ((d:ℝ) * (T + 2)) ^ 2 ≤ 25 * L ^ 2 := by nlinarith
  have h58 : 1 ≤ y ^ ((5:ℝ)/8) := one_le_rpow_of_one_le hy1 (by norm_num)
  have hyT : y / T ≤ 1 := by
    rw [div_le_one hT0]
    calc y ≤ x := hyx
      _ ≤ x ^ 3 := by nlinarith [pow_pos hx0 2]
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg _
  have hbound : efErr d T y ≤ 75 * 10 ^ 12 * L ^ 2 * y ^ ((5:ℝ)/8) := by
    unfold efErr
    have ht1 : y * Real.log ((d:ℝ) * T * y) ^ 2 / T ≤ 25 * L ^ 2 * y ^ ((5:ℝ)/8) := by
      calc y * Real.log ((d:ℝ) * T * y) ^ 2 / T = (y / T) * Real.log ((d:ℝ) * T * y) ^ 2 := by
            ring
        _ ≤ 1 * (25 * L ^ 2) :=
            mul_le_mul hyT hsq1 (sq_nonneg _) zero_le_one
        _ ≤ 25 * L ^ 2 * y ^ ((5:ℝ)/8) := by nlinarith
    have ht2 : y ^ ((5:ℝ)/8) * Real.log ((d:ℝ) * (T + 2)) ^ 2 ≤ 25 * L ^ 2 * y ^ ((5:ℝ)/8) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hsq2 (by positivity)
    have ht3 : Real.log ((d:ℝ) * T * y) ^ 2 ≤ 25 * L ^ 2 * y ^ ((5:ℝ)/8) := by nlinarith
    linarith
  -- the level check
  have hlev : (d:ℝ) ≤ x ^ (-(293/1800) : ℝ) * y ^ (3/8 : ℝ) := by
    have := dpow_le hx1 hd1 hd hy (β := 3/8) (α := 1) (by norm_num) (by norm_num)
    rw [Real.rpow_one] at this
    convert this using 3
    norm_num
  have hkey : 675 * 10 ^ 12 * L ^ 2 * d ≤ ε * y ^ (3/8 : ℝ) := by
    have hxneg : x ^ (-(293/1800) : ℝ) = 1 / x ^ (293/1800 : ℝ) := by
      rw [Real.rpow_neg hx0.le, one_div]
    have hxr : 0 < x ^ (293/1800 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have hy38 : 0 ≤ y ^ (3/8 : ℝ) := Real.rpow_nonneg hy0.le _
    calc 675 * 10 ^ 12 * L ^ 2 * d
        ≤ 675 * 10 ^ 12 * L ^ 2 * (x ^ (-(293/1800) : ℝ) * y ^ (3/8 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlev (by positivity)
      _ = (675 * 10 ^ 12 * L ^ 2 / x ^ (293/1800 : ℝ)) * y ^ (3/8 : ℝ) := by
          rw [hxneg]; ring
      _ ≤ ε * y ^ (3/8 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hy38
          rw [div_le_iff₀ hxr]
          exact hxa
  have hysplit : y = y ^ ((5:ℝ)/8) * y ^ (3/8 : ℝ) := by
    rw [← Real.rpow_add hy0]; norm_num
  calc efErr d T y ≤ 75 * 10 ^ 12 * L ^ 2 * y ^ ((5:ℝ)/8) := hbound
    _ = (675 * 10 ^ 12 * L ^ 2 * d) * y ^ ((5:ℝ)/8) / (9 * d) := by
        field_simp
        ring
    _ ≤ (ε * y ^ (3/8 : ℝ)) * y ^ ((5:ℝ)/8) / (9 * d) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hkey (by positivity)
    _ = ε / 9 * y / d := by
        conv_rhs => rw [hysplit]
        field_simp

/-- **Prime powers and the imprimitive cushion**: `ω(d)·log y + 2√y·log y ≤ (2ε/27)·y/d`
once `81·log x ≤ ε·x^{259/900}`. -/
theorem small_terms_le (d : ℕ) [NeZero d] {x y ε : ℝ} (hx : Real.exp 1 ≤ x)
    (hd : (d:ℝ) ≤ x ^ (191/900 : ℝ)) (hy : (d:ℝ) * x ^ (709/900 : ℝ) ≤ y) (hyx : y ≤ x)
    (hxb : 81 * Real.log x ≤ ε * x ^ (259/900 : ℝ)) :
    (d.primeFactors.card : ℝ) * Real.log y + 2 * Real.sqrt y * Real.log y
      ≤ 2 * ε / 27 * y / d := by
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd0 : (0:ℝ) < d := by linarith
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (1:ℝ)]
  have hx0 : 0 < x := by linarith
  have hL : 1 ≤ Real.log x := one_le_log_of_exp_le hx
  have hL0 : 0 < Real.log x := by linarith
  have hy1 : 1 ≤ y := by nlinarith [one_le_rpow_of_one_le hx1 (by norm_num : (0:ℝ) ≤ 709/900)]
  have hy0 : 0 < y := by linarith
  set L := Real.log x with hLdef
  have hlogy : Real.log y ≤ L := Real.log_le_log hy0 hyx
  have hlogy0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  have hω := omega_le_self d
  have hxr : 0 < x ^ (259/900 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hε0 : 0 ≤ ε := by
    by_contra h
    push Not at h
    have : ε * x ^ (259/900 : ℝ) < 0 := mul_neg_of_neg_of_pos h hxr
    linarith
  -- term A
  have hA : (d.primeFactors.card : ℝ) * Real.log y ≤ ε / 27 * y / d := by
    have hlev : (d:ℝ) ^ (2:ℝ) ≤ x ^ (-(518/900) : ℝ) * y := by
      have := dpow_le hx1 hd1 hd hy (β := 1) (α := 2) zero_le_one (by norm_num)
      rw [Real.rpow_one] at this
      convert this using 3
      norm_num
    rw [Real.rpow_two] at hlev
    have hx518 : x ^ (259/900 : ℝ) ≤ x ^ (518/900 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    have hxneg : x ^ (-(518/900) : ℝ) = 1 / x ^ (518/900 : ℝ) := by
      rw [Real.rpow_neg hx0.le, one_div]
    have hx518' : 0 < x ^ (518/900 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have h27 : 27 * L ≤ ε * x ^ (518/900 : ℝ) := by nlinarith
    calc (d.primeFactors.card : ℝ) * Real.log y ≤ d * L :=
          mul_le_mul hω hlogy hlogy0 hd0.le
      _ = (d ^ 2 * L) / d := by field_simp
      _ ≤ (x ^ (-(518/900) : ℝ) * y * L) / d := by
          apply div_le_div_of_nonneg_right _ hd0.le
          exact mul_le_mul_of_nonneg_right hlev (by linarith)
      _ = (L / x ^ (518/900 : ℝ)) * y / d := by rw [hxneg]; ring
      _ ≤ (ε / 27) * y / d := by
          apply div_le_div_of_nonneg_right _ hd0.le
          apply mul_le_mul_of_nonneg_right _ hy0.le
          rw [div_le_div_iff₀ hx518' (by norm_num)]
          linarith
  -- term B
  have hB : 2 * Real.sqrt y * Real.log y ≤ ε / 27 * y / d := by
    have hlev : (d:ℝ) ≤ x ^ (-(259/900) : ℝ) * y ^ (1/2 : ℝ) := by
      have := dpow_le hx1 hd1 hd hy (β := 1/2) (α := 1) (by norm_num) (by norm_num)
      rw [Real.rpow_one] at this
      convert this using 3
      norm_num
    rw [← Real.sqrt_eq_rpow] at hlev
    have hs0 : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy0
    have hss : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
    have hxneg : x ^ (-(259/900) : ℝ) = 1 / x ^ (259/900 : ℝ) := by
      rw [Real.rpow_neg hx0.le, one_div]
    have h54 : 54 * L ≤ ε * x ^ (259/900 : ℝ) := by linarith
    -- 54 d L ≤ ε √y
    have hkey : 54 * d * L ≤ ε * Real.sqrt y := by
      calc 54 * d * L ≤ 54 * (x ^ (-(259/900) : ℝ) * Real.sqrt y) * L :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlev (by norm_num))
              (by linarith)
        _ = (54 * L / x ^ (259/900 : ℝ)) * Real.sqrt y := by rw [hxneg]; ring
        _ ≤ ε * Real.sqrt y := by
            apply mul_le_mul_of_nonneg_right _ hs0.le
            rw [div_le_iff₀ hxr]
            exact h54
    calc 2 * Real.sqrt y * Real.log y ≤ 2 * Real.sqrt y * L :=
          mul_le_mul_of_nonneg_left hlogy (by positivity)
      _ = (54 * d * L) * Real.sqrt y / (27 * d) := by field_simp; ring
      _ ≤ (ε * Real.sqrt y) * Real.sqrt y / (27 * d) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hkey hs0.le
      _ = ε / 27 * y / d := by
          rw [mul_assoc, hss]; ring
  have : 2 * ε / 27 * y / d = ε / 27 * y / d + ε / 27 * y / d := by ring
  linarith

end Truncation

/-! ### Thresholds -/

section Thresholds

open Filter Asymptotics

lemma eventually_log_pow_le {r C : ℝ} (hr : 0 < r) (hC : 0 < C) (n : ℕ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ^ n ≤ C * x ^ r := by
  have h := (isLittleO_log_rpow_rpow_atTop (n:ℝ) hr).def hC
  filter_upwards [h, eventually_ge_atTop (1:ℝ)] with x hx hx1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_natCast,
    abs_of_nonneg (pow_nonneg (Real.log_nonneg hx1) _),
    abs_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hx
  exact hx

lemma eventually_loglog_le {C : ℝ} (hC : 0 < C) :
    ∀ᶠ x : ℝ in atTop, C * Real.log (Real.log x) ≤ Real.log x := by
  have h := (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).def
    (inv_pos.mpr hC)
  filter_upwards [h, Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hx hx1
  simp only [Function.comp_apply, id, Real.norm_eq_abs] at hx
  rw [abs_of_nonneg (Real.log_nonneg hx1), abs_of_nonneg (by linarith)] at hx
  have := mul_le_mul_of_nonneg_left hx hC.le
  rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul] at this
  exact this

lemma eventually_le_loglog (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, A ≤ Real.log (Real.log x) := by
  have := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop A
  filter_upwards [this] with x hx
  simpa using hx

lemma eventually_le_log_rpow {r : ℝ} (hr : 0 < r) (A : ℝ) :
    ∀ᶠ x : ℝ in atTop, A ≤ Real.log x ^ r := by
  have := ((tendsto_rpow_atTop hr).comp Real.tendsto_log_atTop).eventually_ge_atTop A
  filter_upwards [this] with x hx
  simpa using hx

end Thresholds

/-! ### The density inputs and T2.1 -/

/-- **The two zone-density inputs** (routez/Z0a-ledger.md §7; forms frozen in
`Carmichael/DensityInterface.lean`), carried as hypotheses: Z6d log-free and
Z6-logged (uniform profile `P ≤ 7/2`). -/
structure DensityInputs : Prop where
  /-- Z6d: `∑_χ N(σ,t,χ) ≤ γ₂·(d·t^{c₀'})^{(9/2)(1−σ)}` on `σ ∈ [9/10,1]`, `t ≥ 2`. -/
  logfree : LogFreeDensity
  /-- Z6-logged: `∑_χ N(σ,t,χ) ≤ C_H·(d·t^{c₀})^{P(1−σ)}·log^K(d(t+2))` on
  `σ ∈ [39/50,1]`, `t ≥ 2`, with `P ≤ 7/2`, `c₀ ∈ [1,5/4]`. -/
  logged : LoggedDensity

set_option maxHeartbeats 2000000 in
/-- **T2.1** (routez/Z0a-ledger.md §4, frozen): for `0 < ε < 1/3` there are `D`, `x₂`
and exceptional sets `bad x` of size `≤ D`, members `≥ 2`, such that for `x ≥ x₂`,
`a` a unit mod `d`, `d ≤ x^{191/900}`, `d·x^{709/900} ≤ y ≤ x`, and no member of
`bad x` dividing `d`: `|θ(y;d,a) − y/φ(d)| ≤ ε·y/φ(d)`.  The proof delivers the
constant `17/27·ε`. -/
theorem theta_AP_T21 (hden : DensityInputs) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1/3) :
    ∃ D : ℕ, ∃ x₂ : ℝ, ∃ bad : ℕ → Finset ℕ,
      (∀ x, (bad x).card ≤ D) ∧ (∀ x, ∀ m ∈ bad x, 2 ≤ m) ∧
      ∀ (x : ℕ) (d : ℕ) [NeZero d] (a : ZMod d) (y : ℝ), x₂ ≤ x → IsUnit a →
        (d : ℝ) ≤ (x : ℝ) ^ (191/900 : ℝ) → (d : ℝ) * (x : ℝ) ^ (709/900 : ℝ) ≤ y → y ≤ x →
        (∀ m ∈ bad x, ¬ m ∣ d) →
        |thetaAP a y - y / d.totient| ≤ ε * y / d.totient := by
  obtain ⟨γ₂, c₀', hγ, hc, hc2, hlf⟩ := hden.logfree
  obtain ⟨CH, P, c₀, K, hCH, hP0, hP, hc₀, hc₀', hlog⟩ := hden.logged
  -- the pinned constants
  set ρ : ℝ := (200 / 9) * Real.log (6912 * γ₂ / ε) with hρdef
  have h6912 : 1 < 6912 * γ₂ / ε := by
    rw [lt_div_iff₀ hε0]; nlinarith
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact mul_pos (by norm_num) (Real.log_pos h6912)
  have hexpρ : Real.exp (-(9/200) * ρ) = ε / (6912 * γ₂) := by
    rw [hρdef, show -(9/200 : ℝ) * ((200 / 9) * Real.log (6912 * γ₂ / ε))
        = -Real.log (6912 * γ₂ / ε) by ring, Real.exp_neg, Real.exp_log (by positivity)]
    rw [inv_div]
  set ν : ℝ := 27 * γ₂ * Real.exp (28 * ρ) / ε with hνdef
  have hν0 : 0 < ν := by positivity
  have hν1 : 1 ≤ ν := by
    rw [hνdef, le_div_iff₀ hε0]
    have := Real.add_one_le_exp (28 * ρ)
    nlinarith
  obtain ⟨σζ, hσζ1, hζ⟩ := zeta_box_clearance ν hν0
  set Cs : ℝ := 50 * ((K:ℝ) + 2) with hCs
  have hCs0 : 0 < Cs := by positivity
  -- the thresholds, as an eventually-statement
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp 10 ≤ x
      ∧ Real.log x ^ 2 ≤ ε / (675 * 10 ^ 12) * x ^ (293/1800 : ℝ)
      ∧ Real.log x ≤ ε / 81 * x ^ (259/900 : ℝ)
      ∧ Real.log x ^ 2 ≤ ε / 756000 * x ^ (7/900 : ℝ)
      ∧ 50112 * 5 ^ K * CH / ε ≤ Real.log x ^ (9/2 : ℝ)
      ∧ 18 * Cs * Real.log (Real.log x) ≤ Real.log x
      ∧ ρ / Cs ≤ Real.log (Real.log x)
      ∧ max (ρ / (1 - σζ)) (40 * ρ) ≤ Real.log x := by
    refine (Filter.eventually_ge_atTop _).and (Filter.Eventually.and ?_ (Filter.Eventually.and ?_
      (Filter.Eventually.and ?_ (Filter.Eventually.and ?_ (Filter.Eventually.and ?_
      (Filter.Eventually.and ?_ ?_))))))
    · exact eventually_log_pow_le (r := 293/1800) (C := ε / (675 * 10 ^ 12)) (by norm_num)
        (by positivity) 2
    · exact (eventually_log_pow_le (r := 259/900) (C := ε / 81) (by norm_num)
        (by positivity) 1).mono (fun x hx => by simpa using hx)
    · exact eventually_log_pow_le (r := 7/900) (C := ε / 756000) (by norm_num)
        (by positivity) 2
    · exact eventually_le_log_rpow (by norm_num) _
    · exact eventually_loglog_le (by positivity)
    · exact eventually_le_loglog _
    · exact Real.tendsto_log_atTop.eventually_ge_atTop _
  obtain ⟨x₂, hx₂⟩ := Filter.eventually_atTop.mp hev
  -- the exceptional set and its size bound
  set D : ℕ := ⌈Census.censusC₂ ν * Real.exp ((191/900) * Census.censusC₃ * ρ)⌉₊ with hD
  have hbase : ∀ x : ℕ, x₂ ≤ x → (2:ℝ) ≤ (x:ℝ) ^ (191/900 : ℝ) ∧ 1 < (x:ℝ)
      ∧ 39/40 ≤ 1 - ρ / Real.log x := by
    intro x hx
    obtain ⟨h0, -, -, -, -, -, -, h8⟩ := hx₂ x hx
    have he10 : (1:ℝ) < Real.exp 10 := by
      have := Real.add_one_le_exp (10:ℝ); linarith
    have hx1 : 1 < (x:ℝ) := lt_of_lt_of_le he10 h0
    have hL0 : 0 < Real.log x := Real.log_pos hx1
    refine ⟨?_, hx1, ?_⟩
    · calc (2:ℝ) ≤ Real.exp (10 * (191/900)) := by
            have := Real.add_one_le_exp (10 * (191/900 : ℝ)); norm_num at this ⊢; linarith
        _ = (Real.exp 10) ^ (191/900 : ℝ) := by rw [← Real.exp_mul]
        _ ≤ (x:ℝ) ^ (191/900 : ℝ) := Real.rpow_le_rpow (Real.exp_pos _).le h0 (by norm_num)
    · have h40 : 40 * ρ ≤ Real.log x := le_trans (le_max_right _ _) h8
      have : ρ / Real.log x ≤ 1/40 := by
        rw [div_le_iff₀ hL0]; linarith
      linarith
  refine ⟨D, x₂, badSet ρ ν x₂, ?_, badSet_ge_two ρ ν x₂, ?_⟩
  · intro x
    have h := badSet_card_le hν1 hρ hbase x
    have h2 : Census.censusC₂ ν * Real.exp ((191/900) * Census.censusC₃ * ρ) ≤ (D:ℝ) :=
      Nat.le_ceil _
    exact_mod_cast h.trans h2
  -- the main inequality
  intro x d _ a y hxx ha hd hy hyx hbad
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h8⟩ := hx₂ x hxx
  set X : ℝ := (x:ℝ) with hX
  have he1 : Real.exp 1 ≤ X := le_trans (Real.exp_le_exp.mpr (by norm_num)) h0
  have he : (1:ℝ) < Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
  have hX2 : 2 ≤ X := by
    have := Real.exp_one_gt_d9; linarith
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hL : 1 ≤ Real.log X := one_le_log_of_exp_le he1
  have hL0 : 0 < Real.log X := by linarith
  have hlogL : 0 ≤ Real.log (Real.log X) := Real.log_nonneg hL
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hd0 : (0:ℝ) < d := by linarith
  have hφ : (0:ℝ) < d.totient := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hφd : (d.totient : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  have hXp : (1:ℝ) ≤ X ^ (709/900 : ℝ) := one_le_rpow_of_one_le hX1 (by norm_num)
  have hXp0 : 0 ≤ X ^ (709/900 : ℝ) := by linarith
  have hdXp : X ^ (709/900 : ℝ) ≤ (d:ℝ) * X ^ (709/900 : ℝ) := le_mul_of_one_le_left hXp0 hd1
  have hy1 : 1 ≤ y := by linarith
  have hy0 : 0 < y := by linarith
  have hyd : (d:ℝ) ≤ y := by
    have : (d:ℝ) * 1 ≤ (d:ℝ) * X ^ (709/900 : ℝ) := mul_le_mul_of_nonneg_left hXp hd0.le
    linarith
  have hy100 : 100 ≤ y := by
    have hexp5 : (100:ℝ) ≤ Real.exp 5 := by
      have h := Real.exp_one_gt_d9
      have h5 : (2.7182818283:ℝ) ^ 5 ≤ (Real.exp 1) ^ 5 :=
        pow_le_pow_left₀ (by norm_num) h.le 5
      rw [Real.exp_one_pow] at h5
      push_cast at h5
      norm_num at h5 ⊢; linarith
    have h5 : Real.exp 5 ≤ X ^ (709/900 : ℝ) := by
      calc Real.exp 5 ≤ Real.exp (10 * (709/900)) := Real.exp_le_exp.mpr (by norm_num)
        _ = (Real.exp 10) ^ (709/900 : ℝ) := by rw [← Real.exp_mul]
        _ ≤ X ^ (709/900 : ℝ) := Real.rpow_le_rpow (Real.exp_pos _).le h0 (by norm_num)
    linarith
  have hT2 : (2:ℝ) ≤ X ^ 3 := by nlinarith [pow_pos hX0 2]
  -- the threshold consequences
  have hxa : 675 * 10 ^ 12 * Real.log X ^ 2 ≤ ε * X ^ (293/1800 : ℝ) := by
    have := mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 675 * 10 ^ 12)
    calc 675 * 10 ^ 12 * Real.log X ^ 2 ≤ 675 * 10 ^ 12 * (ε / (675 * 10 ^ 12) * X ^ (293/1800 : ℝ))
          := this
      _ = ε * X ^ (293/1800 : ℝ) := by field_simp
  have hxb : 81 * Real.log X ≤ ε * X ^ (259/900 : ℝ) := by
    have := mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 81)
    calc 81 * Real.log X ≤ 81 * (ε / 81 * X ^ (259/900 : ℝ)) := this
      _ = ε * X ^ (259/900 : ℝ) := by field_simp
  have hxI : 756000 * Real.log X ^ 2 ≤ ε * X ^ (7/900 : ℝ) := by
    have := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 756000)
    calc 756000 * Real.log X ^ 2 ≤ 756000 * (ε / 756000 * X ^ (7/900 : ℝ)) := this
      _ = ε * X ^ (7/900 : ℝ) := by field_simp
  have hxII : 50112 * 5 ^ K * CH ≤ ε * Real.log X ^ (9/2 : ℝ) := by
    rw [div_le_iff₀ hε0] at h4; linarith
  set σs := sigmaStar K X with hσs
  set τ : ℝ := 1 - ρ / Real.log X with hτ
  have hCsL : Cs * Real.log (Real.log X) / Real.log X ≤ 1/18 := by
    rw [div_le_iff₀ hL0]; linarith
  have hCsL0 : 0 ≤ Cs * Real.log (Real.log X) / Real.log X := by positivity
  have hσs_eq : σs = 1 - Cs * Real.log (Real.log X) / Real.log X := by
    rw [hσs, sigmaStar, hCs]
  have hσs39 : 39/50 ≤ σs := by rw [hσs_eq]; linarith
  have hσs9 : 9/10 ≤ σs := by rw [hσs_eq]; linarith
  have hσsτ : σs ≤ τ := by
    rw [hσs_eq, hτ]
    have : ρ / Real.log X ≤ Cs * Real.log (Real.log X) / Real.log X := by
      apply div_le_div_of_nonneg_right _ hL0.le
      rw [div_le_iff₀ hCs0] at h6; linarith
    linarith
  have hτ1 : τ ≤ 1 := by
    rw [hτ]; have : 0 ≤ ρ / Real.log X := by positivity
    linarith
  have hτ0 : 0 < τ := by
    rw [hτ]
    have h40 : 40 * ρ ≤ Real.log X := le_trans (le_max_right _ _) h8
    have : ρ / Real.log X ≤ 1/40 := by rw [div_le_iff₀ hL0]; linarith
    linarith
  have hτζ : σζ ≤ τ := by
    rw [hτ]
    have h7 : ρ / (1 - σζ) ≤ Real.log X := le_trans (le_max_left _ _) h8
    have h1σ : 0 < 1 - σζ := by linarith
    rw [div_le_iff₀ h1σ] at h7
    have : ρ / Real.log X ≤ 1 - σζ := by rw [div_le_iff₀ hL0]; linarith
    linarith
  have hfoldIII : c₀' * ((9/2 : ℝ) * (1 - σs)) ≤ 1/2 := by
    rw [hσs_eq]
    have : (9/2 : ℝ) * (1 - (1 - Cs * Real.log (Real.log X) / Real.log X)) ≤ 1/4 := by
      linarith
    calc c₀' * ((9/2 : ℝ) * (1 - (1 - Cs * Real.log (Real.log X) / Real.log X)))
        ≤ 2 * (1/4) := mul_le_mul hc2 this (by linarith) (by norm_num)
      _ = 1/2 := by norm_num
  have h10ρ : 10 * ρ ≤ Real.log X := by
    have h40 : 40 * ρ ≤ Real.log X := le_trans (le_max_right _ _) h8
    linarith
  -- zone IV(a): no zero of any χ mod d in the census box
  have hempty : ∀ χ : DirichletCharacter ℂ d, ∀ ζ ∈ zeroFinset χ (1/2) (X ^ 3),
      τ ≤ ζ.re → |ζ.im| ≤ ν → False := by
    have hbad' : ∀ m ∈ (Finset.Icc 2 ⌊X ^ (191/900 : ℝ)⌋₊).filter
        (fun m => (Census.badChars τ ν m).Nonempty), ¬ m ∣ d := by
      intro m hm
      apply hbad m
      unfold badSet
      rw [if_pos hxx]
      exact hm
    exact no_zero_in_box d hτ0 (fun s hs1 hs2 hs3 => hζ s (le_trans hτζ hs1) hs2 hs3) hd hbad'
  -- the four zones
  have hI := zoneI_le d he1 hX2 hd hy hxI
  have hII := zoneII_le d hCH hP0 hP hc₀ hc₀' (fun t σ ht hσ1 hσ2 => hlog d t σ ht hσ1 hσ2)
    he1 hX2 hd hy hyx hσs39 hxII
  have hIII := zoneIII_le d hγ hc (fun t σ ht hσ1 hσ2 => hlf d t σ ht hσ1 hσ2) he1 hd hy hyx
    hρ hσs9 hσsτ hfoldIII
  have hIV := zoneIV_le d hγ hc hc2 (fun t σ ht hσ1 hσ2 => hlf d t σ ht hσ1 hσ2) he1 hd hy1
    hρ hν0 h10ρ hempty
  rw [hexpρ] at hIII
  have hIII' : zoneSum d (X ^ 3) y σs τ ≤ ε * y / 27 := by
    refine le_trans hIII (le_of_eq ?_)
    field_simp
    ring
  have hIV' : zoneSum d (X ^ 3) y τ 1 ≤ ε * y / 27 := by
    refine le_trans hIV (le_of_eq ?_)
    rw [hνdef]
    field_simp
  have hsplit := zeroSumTotal_split d (X ^ 3) y (σa := 39/50) (σb := σs) (σc := τ)
    (by norm_num) hσs39 hσsτ hτ1
  have hZ : zeroSumTotal d (X ^ 3) y ≤ 4 * ε * y / 27 := by
    rw [hsplit]; linarith
  -- the explicit-formula pieces
  have hEF := efErr_le d he1 hX2 hd hy hyx hxa
  have hsmall := small_terms_le d he1 hd hy hyx hxb
  have hmain := thetaAP_sub_le ha hy100 hT2 hyd
  -- assemble: everything in units of y/φ(d)
  have hyφ : y / d ≤ y / d.totient := div_le_div_of_nonneg_left hy0.le hφ hφd
  have hZφ : 3 / d.totient * zeroSumTotal d (X ^ 3) y ≤ 4 / 9 * (ε * y / d.totient) := by
    calc 3 / d.totient * zeroSumTotal d (X ^ 3) y ≤ 3 / d.totient * (4 * ε * y / 27) :=
          mul_le_mul_of_nonneg_left hZ (by positivity)
      _ = 4 / 9 * (ε * y / d.totient) := by field_simp; ring
  have hEFφ : efErr d (X ^ 3) y ≤ 1 / 9 * (ε * y / d.totient) := by
    calc efErr d (X ^ 3) y ≤ ε / 9 * y / d := hEF
      _ = ε / 9 * (y / d) := by ring
      _ ≤ ε / 9 * (y / d.totient) := mul_le_mul_of_nonneg_left hyφ (by positivity)
      _ = 1 / 9 * (ε * y / d.totient) := by ring
  have hsmallφ : (d.primeFactors.card : ℝ) * Real.log y + 2 * Real.sqrt y * Real.log y
      ≤ 2 / 27 * (ε * y / d.totient) := by
    calc _ ≤ 2 * ε / 27 * y / d := hsmall
      _ = 2 * ε / 27 * (y / d) := by ring
      _ ≤ 2 * ε / 27 * (y / d.totient) := mul_le_mul_of_nonneg_left hyφ (by positivity)
      _ = 2 / 27 * (ε * y / d.totient) := by ring
  have hpos : 0 ≤ ε * y / d.totient := by positivity
  calc |thetaAP a y - y / d.totient|
      ≤ efErr d (X ^ 3) y + (d.primeFactors.card : ℝ) * Real.log y
        + 3 / d.totient * zeroSumTotal d (X ^ 3) y + 2 * Real.sqrt y * Real.log y := hmain
    _ ≤ 1 / 9 * (ε * y / d.totient) + 4 / 9 * (ε * y / d.totient)
        + 2 / 27 * (ε * y / d.totient) := by linarith
    _ = 17 / 27 * (ε * y / d.totient) := by ring
    _ ≤ ε * y / d.totient := by linarith


end Carmichael.T21
