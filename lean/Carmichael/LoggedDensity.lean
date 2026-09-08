/-
Route Z, sortie L2: the logged zero-density theorem (routez/Z6-logged.md §3, Theorem L;
routez/Z6-logged-audit.md F1–F3, F5, F8/F9) assembled from the logged detector
(`LoggedDetector`, L1.e `detector_large_value` and L1.f `sum_sq_EctrHalf_le`), the
large-values engine LV1 (`LargeValues.large_values_mean`), the well-spaced representatives
(`Representatives`: `repIndex`, `rep`, `sum_good_le_of_localCount`, `idx_bounds`) and the
Jensen disk counts (`ZeroCount`: `sum_ord_LFunction_disk_le`, `sum_ord_etaFun_disk_le`,
`zeroCountBox_trivChar_le`, `sum_zeroCountBox_le`, `zeroCountBox_mono`); discharge of the
frozen interface `Carmichael.LoggedDensity` (`DensityInterface`).

No `sorry`, no `axiom`, no `native_decide` in this file.

NOTATION.  `d ≥ 1` (`[NeZero d]`), `t ≥ 2`, `σ ∈ [39/50, 1]`, `D = d(t+2)` written
`(d:ℝ) * (t + 2)`, `𝓛 = Real.log ((d:ℝ) * (t + 2))`, `P = 151/50`, `J = Jpar D = ⌈𝓛⌉₊`,
`V₁ = Vthr D = 1/(8J(J+1))`, `Q₁ = Q1 d t = ⌈𝓛⌉₊ + 1`.

STATEMENTS (namespace `Carmichael.LoggedDensity`):

 * Lemma 3.1  `localCount_le_logged χ hσ hσ1 ht hL hγ₀`
     (`39/50 ≤ σ ≤ 1`, `0 ≤ t`, `1 ≤ 𝓛`, `|γ₀| ≤ t`): `localCount χ σ t γ₀ ≤ 112·𝓛`, every `χ`.
 * Lemma 3.3  `cls d t p = (p.2 / 2) % Q1 d t`; `thin_spacing` (same parity system, same
     character, same class, distinct ⇒ `1 ≤ |Im ρ_p − Im ρ_q|`);
     `card_repIndex_eq_sum_cls` (`|repIndex| = ∑_{c < Q₁} |class c|`).
 * Lemma 3.4  `classI_card_le` (one `(j,k)`, LV1 at `N = ⌈2^{j+1}D⌉₊`, audit F1):
     `|𝓕_{j,k}| ≤ 10¹⁰·𝓛¹⁰·D^{P(1−σ)}`.
 * §3.6 core `family_card_le`: a `1`-spaced family of box zeros (with the `χ₀` height
     clause) has `card ≤ 2·10²³·C_τ²·C_Γ²·𝓛¹²·D^{P(1−σ)}`.
 * `card_repIndex_le`: `|repIndex σ t 𝒳 good par| ≤ 2𝓛·(2·10²³·C_τ²·C_Γ²·𝓛¹²·D^{P(1−σ)})`.
 * `low_zeta_count`: the `χ₀` zeros with `|γ| < 𝓛` carry mass `≤ 2240·𝓛²`.
 * `logged_density_large` (`𝓛 ≥ 40`), `logged_density_small` (`𝓛 < 40`, I6 fallback).
 * THEOREM L  `logged_density d hσ hσ1 ht`:
     `∑_χ N(σ,t,χ) ≤ 10²⁷·C_τ²·C_Γ²·D^{(151/50)(1−σ)}·𝓛¹⁴`.
 * LEDGER FORM  `logged_density_ledger d hσ hσ1 ht`:
     `∑_χ N(σ,t,χ) ≤ 2·10²⁷·C_τ²·C_Γ²·(d·t)^{(151/50)(1−σ)}·𝓛¹⁴` (audit F3: no `t ^ (1:ℝ)`).
 * INTERFACE  `loggedDensity : Carmichael.LoggedDensity` with
     `CH = 2·10²⁷·C_τ²·C_Γ²`, `P = 151/50`, `c₀ = 1`, `K = 14`.

CONSTANTS AND EXPONENT BOOKKEEPING (all at `𝓛 ≥ 40`).
 * Class I, one `(j,k)` (`classI_card_le`): the block is empty unless `2^j D < Nmax D`
   (`coeffJK` vanishes beyond `Nmax`), so `N_b := 2^j D < Nmax D ≤ 9𝓛·D^{151/100}`.
   LV1 with `N = ⌈2^{j+1}D⌉₊ ≤ 3N_b`, `dt ≤ D ≤ N_b`, `G ≤ N_b^{−2σ}·N(1+log N)³`
   (`|coeffJK| ≤ τ(n)·N_b^{−σ}`, `sum_card_divisors_sq_le`):
   `card ≤ 300(1+log N)²·(N+dt)G·(8J(J+1))² ≤ 300·(3𝓛)²·12(3𝓛)³·N_b^{2−2σ}·(32𝓛²)²`
   and `N_b^{2−2σ} ≤ (9𝓛)^{2−2σ}·D^{(151/100)(2−2σ)} ≤ 9𝓛·D^{(151/50)(1−σ)}`;
   total `8062156800·𝓛¹⁰·D^{P(1−σ)} ≤ 10¹⁰·𝓛¹⁰·D^{P(1−σ)}`.  The D-exponent is exactly
   `P(1−σ)` (the `Nmax` cap is what keeps it there: the naive `2^J D = D^{1+log 2}` would
   give `3.39(1−σ)`).
 * Class I total: `J(J+1) ≤ 4𝓛²` pairs: `≤ 4·10¹⁰·𝓛¹²·D^{P(1−σ)}`.
 * Class II (L1.f): `card ≤ 16·∑‖E_ctr‖² ≤ 16·10²²·C_τ²C_Γ²·𝓛⁵·D^{P(1−σ)}`.
 * One thinned family: `≤ 2·10²³·C_τ²C_Γ²·𝓛¹²·D^{P(1−σ)}`; `Q₁ ≤ 2𝓛` classes per parity.
 * Covering (`sum_good_le_of_localCount` at `B = 112𝓛`, two instances
   `𝒳₁ = univ.erase 1, good = True` and `𝒳₀ = {1}, good = goodHigh 𝓛`), plus the low `χ₀`
   zeros `≤ 1120𝓛·log(𝓛+2) ≤ 2240𝓛²`:
   `∑_χ N ≤ 2·112𝓛·4𝓛·(2·10²³…𝓛¹²) + 2240𝓛² ≤ 10²⁷·C_τ²C_Γ²·𝓛¹⁴·D^{P(1−σ)}`.
 * Small `D` (`𝓛 < 40`, audit F5): `∑_χ N(σ) ≤ ∑_χ N(1/2) ≤ 1120·t·d·𝓛 ≤ 1120·40·e^{40}
   ≤ 1120·40·2.72⁴⁰ ≤ 10²⁷ ≤ RHS`.
 * Log power: `K = 14` = local count (1) + thinning (1) + class I (12: `J(J+1)` 2,
   `V₁^{−2}` 4, `(1+log N)⁵` 5, `N_b^{2−2σ}` 1) — the audit's §3.4 table.
 * Ledger: `D = d(t+2) ≤ 2dt`, `P(1−σ) ≤ 1661/2500 ≤ 1`, so `D^{P(1−σ)} ≤ 2(dt)^{P(1−σ)}`.

DELTAS VS. THE BLUEPRINT / AUDIT (all reported):
 * Lemma 3.1 carries `1 ≤ 𝓛` (so that `Δ = 1/𝓛 ≤ 1` puts the window in the `13/8`-disk);
   the blueprint states it for `t ≥ 0` alone, where `Δ ≤ 1/log 2` does not fit.  `t ≥ 2`
   gives `𝓛 ≥ log 4 > 1`.
 * `classI_card_le` and `family_card_le` are generic in the index type (as L1.f), with `D`
   free in `classI_card_le` (`1 < D`, `40 ≤ log D`, `d·t ≤ D`).
 * `goodHigh Λ ρ := Λ ≤ |ρ.im|` is a `def` so that the classical `DecidablePred` instance
   of `sum_good_le_of_localCount` coincides with the one elaborated here.
 * Class-I constant `10¹⁰` per `(j,k)` (audit: `5.4·10⁹`), `4·10¹⁰` total (audit `C_I =
   3·10¹⁰`); class II `1.6·10²³ ≤ C_II = 2·10²³`; `C_H = 10²⁷C_τ²C_Γ²` as frozen.
 * Consumer-facing note (audit F8): Z0b Theorem H must be read with the interior
   coefficient `31/10` (gap `2/25`, threshold `D^{1/1250} ≥ 𝓛¹⁴`), including the Z0b §12.4
   parenthetical; nothing in Lean consumes `13/5`.

MATHLIB / PIN NOTES: `add_le_add_right h a : a + b ≤ a + c` in this pin; `Nat.modEq_iff_dvd'`
for the thinning divisibility; `Finset.card_eq_sum_card_fiberwise` for the class split;
`Finset.card_nsmul_le_sum` for the class-II counting; `Real.rpow_le_rpow_of_nonpos` for
`n^{−σ} ≤ N_b^{−σ}`; `Real.rpow_le_self_of_one_le` for `(9𝓛)^{2−2σ} ≤ 9𝓛`.
-/
import Carmichael.LoggedDetector
import Carmichael.Representatives
import Carmichael.DensityInterface

set_option autoImplicit false

namespace Carmichael
namespace LoggedDensity

open Complex Finset Metric
open LoggedDetector
open Representatives (localCount repIndex rep idx mem_repIndex rep_mem_zeroFinset good_rep
  idx_rep abs_im_rep_le sum_good_le_of_localCount)
open scoped Classical

noncomputable section

/-! ## §0 Scale facts -/

section Scale

variable {d : ℕ} [NeZero d]

lemma one_le_d : (1 : ℝ) ≤ d := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)

lemma four_le_scale {t : ℝ} (ht : 2 ≤ t) : (4 : ℝ) ≤ (d : ℝ) * (t + 2) := by
  have := one_le_d (d := d)
  nlinarith

lemma one_lt_log_four : (1 : ℝ) < Real.log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

lemma one_lt_log_scale {t : ℝ} (ht : 2 ≤ t) : 1 < Real.log ((d : ℝ) * (t + 2)) :=
  lt_of_lt_of_le one_lt_log_four (Real.log_le_log (by norm_num) (four_le_scale ht))

lemma mul_le_scale {t : ℝ} (_ht : 2 ≤ t) : (d : ℝ) * t ≤ (d : ℝ) * (t + 2) := by
  have := one_le_d (d := d)
  nlinarith

lemma scale_le_two_mul {t : ℝ} (ht : 2 ≤ t) : (d : ℝ) * (t + 2) ≤ 2 * ((d : ℝ) * t) := by
  have := one_le_d (d := d)
  nlinarith

end Scale

/-! ## §1 Lemma 3.1: the logged local count -/

/-- Window geometry: a point of `[σ,1] × [γ₀−1, γ₀+1]` with `σ ≥ 39/50` lies in the closed
`13/8`-disk around `2 + iγ₀`. -/
lemma mem_disk_of_window {σ γ₀ : ℝ} (hσ : 39/50 ≤ σ) {ρ : ℂ} (hβ : σ ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (him : |ρ.im - γ₀| ≤ 1) : ρ ∈ closedBall ((2 : ℂ) + γ₀ * I) (13/8 : ℝ) := by
  rw [mem_closedBall, Complex.dist_eq]
  have hre : (ρ - ((2 : ℂ) + γ₀ * I)).re = ρ.re - 2 := by simp
  have him' : (ρ - ((2 : ℂ) + γ₀ * I)).im = ρ.im - γ₀ := by simp
  refine norm_le_of_sq_le (by norm_num) ?_
  rw [hre, him']
  have h1 := abs_le.mp him
  have h2 : (ρ.re - 2) ^ 2 ≤ (61/50 : ℝ) ^ 2 := by nlinarith
  have h3 : (ρ.im - γ₀) ^ 2 ≤ 1 := by nlinarith
  nlinarith

/-- **Lemma 3.1 (logged local count), every `χ mod d`.**  For `σ ∈ [39/50, 1]`, `t ≥ 0`,
`𝓛 ≥ 1`, `|γ₀| ≤ t`: the zeros of `L(·,χ)` with multiplicity in
`[σ,1] × [γ₀ − 1/𝓛, γ₀ + 1/𝓛]` number at most `112·𝓛`. -/
theorem localCount_le_logged {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) {σ t γ₀ : ℝ}
    (hσ : 39/50 ≤ σ) (_hσ1 : σ ≤ 1) (_ht : 0 ≤ t)
    (hL : 1 ≤ Real.log ((d : ℝ) * (t + 2))) (hγ₀ : |γ₀| ≤ t) :
    (localCount χ σ t γ₀ : ℝ) ≤ 112 * Real.log ((d : ℝ) * (t + 2)) := by
  have h𝓛 : 0 < Real.log ((d : ℝ) * (t + 2)) := by linarith
  have hΔ : 1 / Real.log ((d : ℝ) * (t + 2)) ≤ 1 := by
    rw [div_le_one h𝓛]; exact hL
  have hdisk : ∀ ρ ∈ (zeroFinset χ σ t).filter
      (fun ρ : ℂ => |ρ.im - γ₀| ≤ 1 / Real.log ((d : ℝ) * (t + 2))),
      ρ ∈ closedBall ((2 : ℂ) + γ₀ * I) (13/8 : ℝ) := by
    intro ρ hρ
    rw [Finset.mem_filter, mem_zeroFinset] at hρ
    obtain ⟨⟨h1, h2, -, -, -⟩, h6⟩ := hρ
    exact mem_disk_of_window hσ h1 h2 (h6.trans hΔ)
  have hcast : (localCount χ σ t γ₀ : ℝ)
      = ∑ ρ ∈ (zeroFinset χ σ t).filter
          (fun ρ : ℂ => |ρ.im - γ₀| ≤ 1 / Real.log ((d : ℝ) * (t + 2))),
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
    rw [localCount, Nat.cast_sum]
  rw [hcast]
  by_cases hχ : χ = 1
  · subst hχ
    have hstep : ∀ ρ ∈ (zeroFinset (1 : DirichletCharacter ℂ d) σ t).filter
        (fun ρ : ℂ => |ρ.im - γ₀| ≤ 1 / Real.log ((d : ℝ) * (t + 2))),
        (analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ d)) ρ : ℝ)
          ≤ (analyticOrderNatAt etaFun ρ : ℝ) := by
      intro ρ hρ
      rw [Finset.mem_filter, mem_zeroFinset] at hρ
      obtain ⟨⟨h1, -, -, h4, -⟩, -⟩ := hρ
      have hre : 0 < ρ.re := by linarith
      rw [analyticOrderNatAt_trivChar_eq hre h4]
      exact_mod_cast analyticOrderNatAt_zeta_le_etaFun hre h4
    calc _ ≤ ∑ ρ ∈ (zeroFinset (1 : DirichletCharacter ℂ d) σ t).filter
          (fun ρ : ℂ => |ρ.im - γ₀| ≤ 1 / Real.log ((d : ℝ) * (t + 2))),
          (analyticOrderNatAt etaFun ρ : ℝ) := Finset.sum_le_sum hstep
      _ ≤ 112 * Real.log (|γ₀| + 2) := sum_ord_etaFun_disk_le γ₀ hdisk
      _ ≤ 112 * Real.log ((d : ℝ) * (t + 2)) := by
          have := Representatives.log_height_le_one (d := d) hγ₀
          linarith
  · calc _ ≤ 112 * Real.log ((d : ℝ) * (|γ₀| + 2)) := sum_ord_LFunction_disk_le χ hχ γ₀ hdisk
      _ ≤ 112 * Real.log ((d : ℝ) * (t + 2)) := by
          have := Representatives.log_height_le (d := d) hγ₀
          linarith

/-! ## §2 Lemma 3.3: thinning of a parity system into `1`-spaced classes -/

section Thinning

variable {d : ℕ} [NeZero d]

/-- `Q₁ = ⌈𝓛⌉₊ + 1`, the number of thinning classes per parity system. -/
def Q1 (d : ℕ) (t : ℝ) : ℕ := ⌈Real.log ((d : ℝ) * (t + 2))⌉₊ + 1

/-- The thinning class of an index: `⌊m/2⌋ mod Q₁`. -/
def cls (d : ℕ) (t : ℝ) (p : DirichletCharacter ℂ d × ℕ) : ℕ := (p.2 / 2) % Q1 d t

omit [NeZero d] in
lemma Q1_pos {t : ℝ} : 0 < Q1 d t := Nat.succ_pos _

omit [NeZero d] in
lemma cls_lt {t : ℝ} {p : DirichletCharacter ℂ d × ℕ} : cls d t p < Q1 d t :=
  Nat.mod_lt _ Q1_pos

omit [NeZero d] in
lemma log_add_one_le_Q1 {t : ℝ} : Real.log ((d : ℝ) * (t + 2)) + 1 ≤ Q1 d t := by
  rw [Q1]; push_cast
  linarith [Nat.le_ceil (Real.log ((d : ℝ) * (t + 2)))]

omit [NeZero d] in
lemma Q1_le_two_mul {t : ℝ} (hL : 2 ≤ Real.log ((d : ℝ) * (t + 2))) :
    (Q1 d t : ℝ) ≤ 2 * Real.log ((d : ℝ) * (t + 2)) := by
  rw [Q1]; push_cast
  have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Real.log ((d : ℝ) * (t + 2)))
  linarith

/-- Same parity, same `⌊·/2⌋ mod Q`, distinct ⇒ at least `2Q` apart. -/
lemma two_mul_le_sub_of_cls_eq {Q a b : ℕ} (_hQ : 0 < Q) (hab : a < b) (hpar : a % 2 = b % 2)
    (hc : (a / 2) % Q = (b / 2) % Q) : 2 * Q ≤ b - a := by
  have h1 : a / 2 < b / 2 := by omega
  have hdvd : Q ∣ b / 2 - a / 2 := (Nat.modEq_iff_dvd' h1.le).mp hc
  have h2 : Q ≤ b / 2 - a / 2 := Nat.le_of_dvd (by omega) hdvd
  omega

/-- The `k`-step cell geometry: `idx ρ + k ≤ idx ρ'` forces `Im ρ' − Im ρ > (k−1)Δ`. -/
lemma idx_add_le_imp {t : ℝ} (ht : 0 ≤ t) {ρ ρ' : ℂ} (hρ : |ρ.im| ≤ t) (hρ' : |ρ'.im| ≤ t)
    {k : ℕ} (h : idx d t ρ + k ≤ idx d t ρ') :
    ((k : ℝ) - 1) / Real.log ((d : ℝ) * (t + 2)) < ρ'.im - ρ.im := by
  have h𝓛 : 0 < Real.log ((d : ℝ) * (t + 2)) := Representatives.log_scale_pos (d := d) ht
  obtain ⟨h1, h2⟩ := Representatives.idx_bounds (d := d) ht hρ
  obtain ⟨h3, h4⟩ := Representatives.idx_bounds (d := d) ht hρ'
  have hcast : ((idx d t ρ : ℕ) : ℝ) + k ≤ ((idx d t ρ' : ℕ) : ℝ) := by exact_mod_cast h
  rw [div_lt_iff₀ h𝓛]
  nlinarith

/-- One-sided thinning spacing: `p.2 < q.2` in the same class ⇒ `Im ρ_q − Im ρ_p ≥ 1`. -/
lemma thin_spacing_lt {σ t : ℝ} (ht : 0 ≤ t) (hL : 1 ≤ Real.log ((d : ℝ) * (t + 2)))
    {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop} {par : ℕ}
    {p q : DirichletCharacter ℂ d × ℕ}
    (hp : p ∈ repIndex σ t 𝒳 good par) (hq : q ∈ repIndex σ t 𝒳 good par)
    (hlt : p.2 < q.2) (hc : cls d t p = cls d t q) :
    1 ≤ (rep q.1 σ t good q.2).im - (rep p.1 σ t good p.2).im := by
  have hp' := mem_repIndex.mp hp
  have hq' := mem_repIndex.mp hq
  have hpar : p.2 % 2 = q.2 % 2 := by rw [hp'.2.2.2, hq'.2.2.2]
  have h2Q := two_mul_le_sub_of_cls_eq (Q1_pos (d := d) (t := t)) hlt hpar hc
  have hidx : idx d t (rep p.1 σ t good p.2) + 2 * Q1 d t ≤ idx d t (rep q.1 σ t good q.2) := by
    rw [idx_rep hp, idx_rep hq]; omega
  have h := idx_add_le_imp ht (abs_im_rep_le hp) (abs_im_rep_le hq) hidx
  have hQ := log_add_one_le_Q1 (d := d) (t := t)
  have h𝓛 : 0 < Real.log ((d : ℝ) * (t + 2)) := by linarith
  have h1 : (1 : ℝ) ≤ (((2 * Q1 d t : ℕ) : ℝ) - 1) / Real.log ((d : ℝ) * (t + 2)) := by
    rw [le_div_iff₀ h𝓛]; push_cast; linarith
  linarith

/-- **Lemma 3.3(b): thinning spacing.**  Two distinct indices of one parity system with the
same character and the same thinning class have ordinates at least `1` apart. -/
theorem thin_spacing {σ t : ℝ} (ht : 0 ≤ t) (hL : 1 ≤ Real.log ((d : ℝ) * (t + 2)))
    {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop} {par : ℕ}
    {p q : DirichletCharacter ℂ d × ℕ}
    (hp : p ∈ repIndex σ t 𝒳 good par) (hq : q ∈ repIndex σ t 𝒳 good par)
    (hχ : p.1 = q.1) (hne : p ≠ q) (hc : cls d t p = cls d t q) :
    1 ≤ |(rep p.1 σ t good p.2).im - (rep q.1 σ t good q.2).im| := by
  have hm : p.2 ≠ q.2 := fun h => hne (Prod.ext hχ h)
  rcases lt_or_gt_of_ne hm with h | h
  · have := thin_spacing_lt ht hL hp hq h hc
    rw [abs_sub_comm]
    exact this.trans (le_abs_self _)
  · have := thin_spacing_lt ht hL hq hp h hc.symm
    exact this.trans (le_abs_self _)

/-- **Lemma 3.3(a): class decomposition.** -/
theorem card_repIndex_eq_sum_cls {σ t : ℝ} {𝒳 : Finset (DirichletCharacter ℂ d)}
    {good : ℂ → Prop} {par : ℕ} :
    (repIndex σ t 𝒳 good par).card
      = ∑ c ∈ Finset.range (Q1 d t),
          ((repIndex σ t 𝒳 good par).filter (fun p => cls d t p = c)).card :=
  Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_range.mpr cls_lt)

end Thinning

/-! ## §3 Class I: LV1 on each `(j,k)` (Lemma 3.4, audit F1) -/

section ClassI

/-- The LV1 threshold `V₁ = 1/(8J(J+1))`. -/
def Vthr (D : ℝ) : ℝ := 1 / (8 * (Jpar D : ℝ) * ((Jpar D : ℝ) + 1))

/-- The `(j,k)` Taylor component over the frozen block range (the L1.e / LV1 sum). -/
def twistSum {d : ℕ} (D σ : ℝ) (j k : ℕ) (χ : DirichletCharacter ℂ d) (γ : ℝ) : ℂ :=
  ∑ n ∈ blockRange D j,
    coeffJK D σ j k n * χ n * Complex.exp ((-Real.log n * γ : ℝ) * Complex.I)

lemma Vthr_pos {D : ℝ} (hL : 1 ≤ Real.log D) : 0 < Vthr D := by
  have hJ1 : 1 ≤ Jpar D := one_le_Jpar hL
  have hJR : (1 : ℝ) ≤ Jpar D := by exact_mod_cast hJ1
  rw [Vthr]; positivity

/-- `|coeffJK D σ j k n| ≤ τ(n)·(2^j D)^{−σ}` (the coefficient mass, §3.2). -/
lemma norm_coeffJK_le {D σ : ℝ} (hD : 0 < D) (hσ : 0 ≤ σ) (j k n : ℕ) :
    ‖coeffJK D σ j k n‖ ≤ (n.divisors.card : ℝ) * (2 ^ j * D) ^ (-σ) := by
  have hNb : (0 : ℝ) < 2 ^ j * D := by positivity
  have hR0 : 0 ≤ (2 ^ j * D) ^ (-σ) := Real.rpow_nonneg hNb.le _
  rw [coeffJK]
  split_ifs with h
  · obtain ⟨h1, h2, -⟩ := h
    have hn0 : (0 : ℝ) < n := lt_trans hNb h1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.rpow_pos_of_pos hn0 _), abs_pow]
    have hb : |Detector.bvA D (2 * D) n| ≤ (n.divisors.card : ℝ) :=
      abs_bvA_le_card_divisors hD (by linarith) n
    have he : Real.exp (-(n : ℝ) / Ypar D) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have hY := Ypar_pos hD
      exact div_nonpos_iff.mpr (Or.inr ⟨by linarith, hY.le⟩)
    have hq1 : 1 < (n : ℝ) / (2 ^ j * D) := (one_lt_div hNb).mpr h1
    have hq2 : (n : ℝ) / (2 ^ j * D) ≤ 2 := by
      have h2' : (2 : ℝ) ^ (j + 1) * D = 2 * (2 ^ j * D) := by rw [pow_succ]; ring
      rw [div_le_iff₀ hNb]; linarith
    have hl : |-(Real.log ((n : ℝ) / (2 ^ j * D)))| ≤ 1 := by
      rw [abs_neg, abs_of_nonneg (Real.log_nonneg hq1.le)]
      have := Real.log_le_log (by linarith) hq2
      have := Real.log_two_lt_d9
      linarith
    have hlk : |-(Real.log ((n : ℝ) / (2 ^ j * D)))| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg _) hl
    have hp : (n : ℝ) ^ (-σ) ≤ (2 ^ j * D) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos hNb h1.le (by linarith)
    have hτ0 : (0 : ℝ) ≤ n.divisors.card := Nat.cast_nonneg _
    calc |Detector.bvA D (2 * D) n| * Real.exp (-(n : ℝ) / Ypar D)
          * |-(Real.log ((n : ℝ) / (2 ^ j * D)))| ^ k * (n : ℝ) ^ (-σ)
        ≤ (n.divisors.card : ℝ) * 1 * 1 * (2 ^ j * D) ^ (-σ) := by
          gcongr
      _ = (n.divisors.card : ℝ) * (2 ^ j * D) ^ (-σ) := by ring
  · rw [norm_zero]
    positivity

/-- `G = ∑_{n ≤ N} ‖coeffJK‖² ≤ (2^j D)^{−2σ}·N(1+log N)³`. -/
lemma sum_sq_coeffJK_le {D σ : ℝ} (hD : 0 < D) (hσ : 0 ≤ σ) (j k N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖coeffJK D σ j k n‖ ^ 2
      ≤ ((2 ^ j * D) ^ (-σ)) ^ 2 * ((N : ℝ) * (1 + Real.log N) ^ 3) := by
  have hNb : (0 : ℝ) < 2 ^ j * D := by positivity
  have hR0 : 0 ≤ (2 ^ j * D) ^ (-σ) := Real.rpow_nonneg hNb.le _
  calc ∑ n ∈ Finset.Icc 1 N, ‖coeffJK D σ j k n‖ ^ 2
      ≤ ∑ n ∈ Finset.Icc 1 N, ((2 ^ j * D) ^ (-σ)) ^ 2 * (n.divisors.card : ℝ) ^ 2 := by
        refine Finset.sum_le_sum fun n _ => ?_
        calc ‖coeffJK D σ j k n‖ ^ 2 ≤ ((n.divisors.card : ℝ) * (2 ^ j * D) ^ (-σ)) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (norm_coeffJK_le hD hσ j k n) 2
          _ = ((2 ^ j * D) ^ (-σ)) ^ 2 * (n.divisors.card : ℝ) ^ 2 := by ring
    _ = ((2 ^ j * D) ^ (-σ)) ^ 2 * ∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ ((2 ^ j * D) ^ (-σ)) ^ 2 * ((N : ℝ) * (1 + Real.log N) ^ 3) :=
        mul_le_mul_of_nonneg_left (sum_card_divisors_sq_le N) (by positivity)

lemma rpow_neg_sq_mul_sq {x σ : ℝ} (hx : 0 < x) :
    (x ^ (-σ)) ^ 2 * x ^ 2 = x ^ (2 - 2 * σ) := by
  rw [← Real.rpow_natCast (x ^ (-σ)) 2, ← Real.rpow_mul hx.le, ← Real.rpow_natCast x 2,
    ← Real.rpow_add hx]
  congr 1; push_cast; ring

/-- The block exponent: for a nonempty block `2^j D < Nmax D ≤ 9𝓛·D^{151/100}`,
`(2^j D)^{2−2σ} ≤ 9𝓛·D^{(151/50)(1−σ)}`. -/
lemma block_rpow_le {D σ : ℝ} (hD : 1 < D) (hL : 40 ≤ Real.log D) (hσ : 39/50 ≤ σ)
    (hσ1 : σ ≤ 1) {j : ℕ} (hblock : 2 ^ j * D < Nmax D) :
    (2 ^ j * D) ^ (2 - 2 * σ) ≤ 9 * Real.log D * D ^ ((151/50 : ℝ) * (1 - σ)) := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hL0 : (0 : ℝ) ≤ Real.log D := by linarith
  have hY := Ypar_pos hD0
  have hY1 := one_le_Ypar hD.le
  have hNb : (0 : ℝ) < 2 ^ j * D := by positivity
  have he0 : 0 ≤ 2 - 2 * σ := by linarith
  have he1 : 2 - 2 * σ ≤ 1 := by linarith
  have hNmax : (Nmax D : ℝ) ≤ 9 * Real.log D * Ypar D := by
    have := Nmax_le hD0 hL0
    have : 1 ≤ Ypar D * Real.log D := by nlinarith
    nlinarith
  have h9L : 1 ≤ 9 * Real.log D := by linarith
  calc (2 ^ j * D) ^ (2 - 2 * σ) ≤ (9 * Real.log D * Ypar D) ^ (2 - 2 * σ) :=
        Real.rpow_le_rpow hNb.le (by linarith) he0
    _ = (9 * Real.log D) ^ (2 - 2 * σ) * Ypar D ^ (2 - 2 * σ) :=
        Real.mul_rpow (by linarith) hY.le
    _ ≤ (9 * Real.log D) * Ypar D ^ (2 - 2 * σ) := by
        gcongr
        exact Real.rpow_le_self_of_one_le h9L he1
    _ = 9 * Real.log D * D ^ ((151/50 : ℝ) * (1 - σ)) := by
        rw [Ypar, ← Real.rpow_mul hD0.le,
          show (151/100 : ℝ) * (2 - 2 * σ) = (151/50 : ℝ) * (1 - σ) by ring]

/-- **Lemma 3.4 (one `(j,k)`, LV1 at `N = ⌈2^{j+1}D⌉₊`).**  A `1`-spaced family on which the
`(j,k)` Taylor component is `≥ V₁` has at most `10¹⁰·𝓛¹⁰·D^{(151/50)(1−σ)}` members. -/
theorem classI_card_le {ι : Type*} (d : ℕ) [NeZero d] {D σ t : ℝ} (hD1 : 1 < D)
    (hL : 40 ≤ Real.log D) (hσ : 39/50 ≤ σ) (hσ1 : σ ≤ 1) (ht : 2 ≤ t)
    (hdt : (d : ℝ) * t ≤ D)
    (s : Finset ι) (chi : ι → DirichletCharacter ℂ d) (ρ : ι → ℂ)
    (hρ : ∀ r ∈ s, |(ρ r).im| ≤ t)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → chi r = chi r' → 1 ≤ |(ρ r).im - (ρ r').im|)
    {j k : ℕ} (hj : j < Jpar D)
    (hlarge : ∀ r ∈ s, Vthr D ≤ ‖twistSum D σ j k (chi r) (ρ r).im‖) :
    (s.card : ℝ) ≤ 10 ^ 10 * Real.log D ^ 10 * D ^ ((151/50 : ℝ) * (1 - σ)) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hD0 : (0 : ℝ) < D := by linarith
  have hL0 : (0 : ℝ) ≤ Real.log D := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log D := by linarith
  have hJ1 : 1 ≤ Jpar D := one_le_Jpar hL1
  have hJR : (1 : ℝ) ≤ Jpar D := by exact_mod_cast hJ1
  have hJle : (Jpar D : ℝ) ≤ Real.log D + 1 := Jpar_le hL0
  have hV : 0 < Vthr D := Vthr_pos hL1
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hP0 : 0 < D ^ ((151/50 : ℝ) * (1 - σ)) := Real.rpow_pos_of_pos hD0 _
  have hNb0 : (0 : ℝ) < 2 ^ j * D := by positivity
  have hNb1 : (1 : ℝ) ≤ 2 ^ j * D :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hD1.le
  by_cases hblock : 2 ^ j * D < Nmax D
  swap
  · -- the block is empty: `coeffJK` vanishes, so no member can be large
    push Not at hblock
    rcases s.eq_empty_or_nonempty with hs | ⟨r, hr⟩
    · rw [hs, Finset.card_empty]; push_cast; positivity
    · exfalso
      have h := hlarge r hr
      have hzero : twistSum D σ j k (chi r) (ρ r).im = 0 := by
        rw [twistSum]
        refine Finset.sum_eq_zero fun n _ => ?_
        have hc : coeffJK D σ j k n = 0 := by
          rw [coeffJK, if_neg]
          rintro ⟨h1, -, h3⟩
          have : (n : ℝ) ≤ Nmax D := by exact_mod_cast h3
          linarith
        rw [hc, zero_mul, zero_mul]
      rw [hzero, norm_zero] at h
      linarith
  · -- LV1 on the block
    set N : ℕ := ⌈2 ^ (j + 1) * D⌉₊ with hNdef
    have hNpos : 0 < N := Nat.ceil_pos.mpr (by positivity)
    have hN1 : 1 ≤ N := hNpos
    have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have hNle : (N : ℝ) ≤ 3 * (2 ^ j * D) := by
      have h1 := (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 ^ (j + 1) * D)).le
      have h2 : (2 : ℝ) ^ (j + 1) * D = 2 * (2 ^ j * D) := by rw [pow_succ]; ring
      rw [hNdef]
      linarith
    have hLV := LargeValues.large_values_mean d hd t ht N hN1 (coeffJK D σ j k) (Vthr D) hV.le
      s chi (fun r => (ρ r).im) hρ hsep hlarge
    -- the coefficient mass
    have hG := sum_sq_coeffJK_le (σ := σ) hD0 (by linarith) j k N
    have hA0 : 0 ≤ 1 + Real.log N := by
      have := Real.log_nonneg hNR1
      linarith
    have hA3 : 1 + Real.log N ≤ 3 * Real.log D := by
      have h1 : Real.log N ≤ Real.log (3 * (2 ^ j * D)) := Real.log_le_log (by positivity) hNle
      have h2 : Real.log (3 * (2 ^ j * D)) = Real.log 3 + j * Real.log 2 + Real.log D := by
        rw [Real.log_mul (by norm_num) hNb0.ne', Real.log_mul (by positivity) hD0.ne',
          Real.log_pow]
        ring
      have h3 : Real.log 3 ≤ 2 := by
        linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)]
      have h4 : (j : ℝ) ≤ Real.log D := by
        have : (j : ℝ) + 1 ≤ Jpar D := by exact_mod_cast hj
        linarith
      have h5 := Real.log_two_lt_d9
      have h6 : (j : ℝ) * Real.log 2 ≤ Real.log D * 1 :=
        mul_le_mul h4 (by linarith) (Real.log_nonneg (by norm_num)) hL0
      linarith
    have hNdt : (N : ℝ) + d * t ≤ 4 * (2 ^ j * D) := by
      have : (d : ℝ) * t ≤ 2 ^ j * D :=
        hdt.trans (le_mul_of_one_le_left hD0.le (one_le_pow₀ (by norm_num)))
      linarith
    have hX : ((N : ℝ) + d * t) * ∑ n ∈ Finset.Icc 1 N, ‖coeffJK D σ j k n‖ ^ 2
        ≤ 12 * (3 * Real.log D) ^ 3 * (9 * Real.log D * D ^ ((151/50 : ℝ) * (1 - σ))) := by
      have hR0 : 0 ≤ ((2 ^ j * D) ^ (-σ)) ^ 2 := by positivity
      have hA3' : (1 + Real.log N) ^ 3 ≤ (3 * Real.log D) ^ 3 := pow_le_pow_left₀ hA0 hA3 3
      calc ((N : ℝ) + d * t) * ∑ n ∈ Finset.Icc 1 N, ‖coeffJK D σ j k n‖ ^ 2
          ≤ (4 * (2 ^ j * D)) * (((2 ^ j * D) ^ (-σ)) ^ 2 * ((N : ℝ) * (1 + Real.log N) ^ 3)) :=
            mul_le_mul hNdt hG (by positivity) (by positivity)
        _ ≤ (4 * (2 ^ j * D)) * (((2 ^ j * D) ^ (-σ)) ^ 2
              * ((3 * (2 ^ j * D)) * (3 * Real.log D) ^ 3)) := by
            gcongr
        _ = 12 * (3 * Real.log D) ^ 3 * (((2 ^ j * D) ^ (-σ)) ^ 2 * (2 ^ j * D) ^ 2) := by ring
        _ = 12 * (3 * Real.log D) ^ 3 * (2 ^ j * D) ^ (2 - 2 * σ) := by
            rw [rpow_neg_sq_mul_sq hNb0]
        _ ≤ 12 * (3 * Real.log D) ^ 3 * (9 * Real.log D * D ^ ((151/50 : ℝ) * (1 - σ))) := by
            gcongr
            exact block_rpow_le hD1 hL hσ hσ1 hblock
    -- remove the threshold
    have hW0 : 0 < 8 * (Jpar D : ℝ) * ((Jpar D : ℝ) + 1) := by positivity
    have hW : 8 * (Jpar D : ℝ) * ((Jpar D : ℝ) + 1) ≤ 32 * Real.log D ^ 2 := by
      have hJ2 : (Jpar D : ℝ) ≤ 2 * Real.log D := Jpar_le_two_mul hL1
      have hJ2' : (Jpar D : ℝ) + 1 ≤ 2 * Real.log D := by linarith
      calc 8 * (Jpar D : ℝ) * ((Jpar D : ℝ) + 1) ≤ 8 * (2 * Real.log D) * (2 * Real.log D) := by
            gcongr
        _ = 32 * Real.log D ^ 2 := by ring
    have hVW : Vthr D * (8 * (Jpar D : ℝ) * ((Jpar D : ℝ) + 1)) = 1 := by
      rw [Vthr]; field_simp
    have hcard : (s.card : ℝ) ≤ 300 * (1 + Real.log N) ^ 2
        * (((N : ℝ) + d * t) * ∑ n ∈ Finset.Icc 1 N, ‖coeffJK D σ j k n‖ ^ 2)
        * (8 * (Jpar D : ℝ) * ((Jpar D : ℝ) + 1)) ^ 2 := by
      calc (s.card : ℝ)
          = (s.card : ℝ) * Vthr D ^ 2 * (8 * (Jpar D : ℝ) * ((Jpar D : ℝ) + 1)) ^ 2 := by
            rw [mul_assoc, ← mul_pow, hVW]; ring
        _ ≤ 300 * (1 + Real.log N) ^ 2 * ((N : ℝ) + d * t)
              * (∑ n ∈ Finset.Icc 1 N, ‖coeffJK D σ j k n‖ ^ 2)
              * (8 * (Jpar D : ℝ) * ((Jpar D : ℝ) + 1)) ^ 2 :=
            mul_le_mul_of_nonneg_right hLV (by positivity)
        _ = _ := by ring
    have hA2 : (1 + Real.log N) ^ 2 ≤ (3 * Real.log D) ^ 2 := pow_le_pow_left₀ hA0 hA3 2
    have hW2 : (8 * (Jpar D : ℝ) * ((Jpar D : ℝ) + 1)) ^ 2 ≤ (32 * Real.log D ^ 2) ^ 2 :=
      pow_le_pow_left₀ hW0.le hW 2
    have hXnn : 0 ≤ ((N : ℝ) + d * t) * ∑ n ∈ Finset.Icc 1 N, ‖coeffJK D σ j k n‖ ^ 2 := by
      positivity
    calc (s.card : ℝ) ≤ _ := hcard
      _ ≤ 300 * (3 * Real.log D) ^ 2
            * (12 * (3 * Real.log D) ^ 3 * (9 * Real.log D * D ^ ((151/50 : ℝ) * (1 - σ))))
            * (32 * Real.log D ^ 2) ^ 2 := by
          gcongr
      _ = 8062156800 * (Real.log D ^ 10 * D ^ ((151/50 : ℝ) * (1 - σ))) := by ring
      _ ≤ 10 ^ 10 * (Real.log D ^ 10 * D ^ ((151/50 : ℝ) * (1 - σ))) := by
          gcongr; norm_num
      _ = 10 ^ 10 * Real.log D ^ 10 * D ^ ((151/50 : ℝ) * (1 - σ)) := by ring

end ClassI

/-! ## §4 One thinned family: class I ∪ class II (Proposition 2.8 + Cor. 3.5 + Cor. 3.8) -/

/-- **The family bound.**  A `1`-spaced (per character) family of zeros in the box
`[σ,1] × [−t,t]`, whose `χ₀` members have `|γ| ≥ 𝓛`, has at most
`2·10²³·C_τ²·C_Γ²·𝓛¹²·D^{(151/50)(1−σ)}` members (`𝓛 ≥ 40`). -/
theorem family_card_le {ι : Type*} (d : ℕ) [NeZero d] {σ t : ℝ} (hσ : 39/50 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 2 ≤ t) (hL : 40 ≤ Real.log ((d : ℝ) * (t + 2)))
    (s : Finset ι) (chi : ι → DirichletCharacter ℂ d) (ρ : ι → ℂ)
    (hρ : ∀ r ∈ s, σ ≤ (ρ r).re ∧ (ρ r).re ≤ 1 ∧ |(ρ r).im| ≤ t ∧
      DirichletCharacter.LFunction (chi r) (ρ r) = 0 ∧
      (chi r = 1 → Real.log ((d : ℝ) * (t + 2)) ≤ |(ρ r).im|))
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → chi r = chi r' → 1 ≤ |(ρ r).im - (ρ r').im|) :
    (s.card : ℝ) ≤ 2 * 10 ^ 23 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
      * Real.log ((d : ℝ) * (t + 2)) ^ 12 * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ)) := by
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = (d : ℝ) * (t + 2) := ⟨_, rfl⟩
  rw [← hD] at hL hρ ⊢
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hD1 : 1 < D := by rw [hD]; linarith [four_le_scale (d := d) ht]
  have hD0 : 0 < D := by linarith
  have hdt : (d : ℝ) * t ≤ D := by rw [hD]; exact mul_le_scale ht
  have hL1 : 1 ≤ Real.log D := by linarith
  have hL0 : 0 ≤ Real.log D := by linarith
  have hJ1 : 1 ≤ Jpar D := one_le_Jpar hL1
  have hP0 : 0 < D ^ ((151/50 : ℝ) * (1 - σ)) := Real.rpow_pos_of_pos hD0 _
  have hCG1 : 1 ≤ GammaStrip.CGamma := by rw [GammaStrip.CGamma_def]; norm_num
  have hCτ1 := DetectionShift.one_le_Ctau
  have hK : 1 ≤ DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCτ1) (one_le_pow₀ hCG1)
  -- the class-II family and the class-I families
  set sII := s.filter (fun r => 1/4 ≤ ‖EctrHalf (chi r) D (Ypar D) (ρ r)‖) with hsII
  set sJK : ℕ → ℕ → Finset ι := fun j k =>
    s.filter (fun r => Vthr D ≤ ‖twistSum D σ j k (chi r) (ρ r).im‖) with hsJK
  have hcover : s ⊆ sII ∪ (Finset.range (Jpar D)).biUnion
      (fun j => (Finset.range (Jpar D + 1)).biUnion (fun k => sJK j k)) := by
    intro r hr
    obtain ⟨h1, h2, h3, h4, h5⟩ := hρ r hr
    rcases detector_large_value (chi r) hD1 hL hσ hσ1 h1 h2 h5 h4 with h | ⟨j, hj, k, hk, h⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hr, h⟩)
    · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
        Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk),
          Finset.mem_filter.mpr ⟨hr, ?_⟩⟩⟩)
      exact h
  have hcardN : s.card ≤ sII.card + ∑ j ∈ Finset.range (Jpar D),
      ∑ k ∈ Finset.range (Jpar D + 1), (sJK j k).card := by
    calc s.card ≤ (sII ∪ (Finset.range (Jpar D)).biUnion
          (fun j => (Finset.range (Jpar D + 1)).biUnion (fun k => sJK j k))).card :=
          Finset.card_le_card hcover
      _ ≤ sII.card + ((Finset.range (Jpar D)).biUnion
          (fun j => (Finset.range (Jpar D + 1)).biUnion (fun k => sJK j k))).card :=
          Finset.card_union_le _ _
      _ ≤ sII.card + ∑ j ∈ Finset.range (Jpar D),
            ((Finset.range (Jpar D + 1)).biUnion (fun k => sJK j k)).card :=
          add_le_add le_rfl Finset.card_biUnion_le
      _ ≤ sII.card + ∑ j ∈ Finset.range (Jpar D),
            ∑ k ∈ Finset.range (Jpar D + 1), (sJK j k).card :=
          add_le_add le_rfl (Finset.sum_le_sum fun j _ => Finset.card_biUnion_le)
  have hcardR : (s.card : ℝ) ≤ sII.card + ∑ j ∈ Finset.range (Jpar D),
      ∑ k ∈ Finset.range (Jpar D + 1), ((sJK j k).card : ℝ) := by exact_mod_cast hcardN
  -- class II
  have hII : (sII.card : ℝ) ≤ 16 * (10 ^ 22 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
      * Real.log D ^ 5 * D ^ ((151/50 : ℝ) * (1 - σ))) := by
    have h1 : sII.card • (1/16 : ℝ) ≤ ∑ r ∈ sII, ‖EctrHalf (chi r) D (Ypar D) (ρ r)‖ ^ 2 := by
      refine Finset.card_nsmul_le_sum _ _ _ fun r hr => ?_
      have h := (Finset.mem_filter.mp hr).2
      calc (1/16 : ℝ) = (1/4) ^ 2 := by norm_num
        _ ≤ ‖EctrHalf (chi r) D (Ypar D) (ρ r)‖ ^ 2 := pow_le_pow_left₀ (by norm_num) h 2
    rw [nsmul_eq_mul] at h1
    have h2 := sum_sq_EctrHalf_le d hD ht hL hσ hσ1 sII chi ρ
      (fun r hr => by
        obtain ⟨a, b, c, -, -⟩ := hρ r (Finset.mem_filter.mp hr).1
        exact ⟨a, b, c⟩)
      (fun r hr r' hr' hne hc =>
        hsep r (Finset.mem_filter.mp hr).1 r' (Finset.mem_filter.mp hr').1 hne hc)
    linarith
  -- class I, per `(j,k)`
  have hI : ∀ j ∈ Finset.range (Jpar D), ∀ k ∈ Finset.range (Jpar D + 1),
      ((sJK j k).card : ℝ) ≤ 10 ^ 10 * Real.log D ^ 10 * D ^ ((151/50 : ℝ) * (1 - σ)) := by
    intro j hj k _
    exact classI_card_le d hD1 hL hσ hσ1 ht hdt (sJK j k) chi ρ
      (fun r hr => (hρ r (Finset.mem_filter.mp hr).1).2.2.1)
      (fun r hr r' hr' hne hc =>
        hsep r (Finset.mem_filter.mp hr).1 r' (Finset.mem_filter.mp hr').1 hne hc)
      (Finset.mem_range.mp hj) (fun r hr => (Finset.mem_filter.mp hr).2)
  have hsum : (∑ j ∈ Finset.range (Jpar D), ∑ k ∈ Finset.range (Jpar D + 1), ((sJK j k).card : ℝ))
      ≤ (Jpar D : ℝ) * ((Jpar D : ℝ) + 1)
        * (10 ^ 10 * Real.log D ^ 10 * D ^ ((151/50 : ℝ) * (1 - σ))) := by
    calc (∑ j ∈ Finset.range (Jpar D), ∑ k ∈ Finset.range (Jpar D + 1), ((sJK j k).card : ℝ))
        ≤ ∑ j ∈ Finset.range (Jpar D), ∑ k ∈ Finset.range (Jpar D + 1),
            (10 ^ 10 * Real.log D ^ 10 * D ^ ((151/50 : ℝ) * (1 - σ))) :=
          Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => hI j hj k hk
      _ = (Jpar D : ℝ) * ((Jpar D : ℝ) + 1)
            * (10 ^ 10 * Real.log D ^ 10 * D ^ ((151/50 : ℝ) * (1 - σ))) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast; ring
  have hJ2 : (Jpar D : ℝ) ≤ 2 * Real.log D := Jpar_le_two_mul hL1
  have hJ2' : (Jpar D : ℝ) + 1 ≤ 2 * Real.log D := by
    have := Jpar_le hL0; linarith
  have hJ0 : (0 : ℝ) ≤ Jpar D := Nat.cast_nonneg _
  have hI' : (∑ j ∈ Finset.range (Jpar D), ∑ k ∈ Finset.range (Jpar D + 1), ((sJK j k).card : ℝ))
      ≤ 4 * 10 ^ 10 * (DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
          * D ^ ((151/50 : ℝ) * (1 - σ))) * Real.log D ^ 12 := by
    calc _ ≤ (Jpar D : ℝ) * ((Jpar D : ℝ) + 1)
          * (10 ^ 10 * Real.log D ^ 10 * D ^ ((151/50 : ℝ) * (1 - σ))) := hsum
      _ ≤ (2 * Real.log D) * (2 * Real.log D)
          * (10 ^ 10 * Real.log D ^ 10 * D ^ ((151/50 : ℝ) * (1 - σ))) := by
          gcongr
      _ = 4 * 10 ^ 10 * D ^ ((151/50 : ℝ) * (1 - σ)) * Real.log D ^ 12 := by ring
      _ ≤ 4 * 10 ^ 10 * (DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
            * D ^ ((151/50 : ℝ) * (1 - σ))) * Real.log D ^ 12 := by
          have : D ^ ((151/50 : ℝ) * (1 - σ)) ≤ DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
              * D ^ ((151/50 : ℝ) * (1 - σ)) := le_mul_of_one_le_left hP0.le hK
          gcongr
  have hII' : (sII.card : ℝ) ≤ 16 * 10 ^ 22 * (DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
      * D ^ ((151/50 : ℝ) * (1 - σ))) * Real.log D ^ 12 := by
    have hL512 : Real.log D ^ 5 ≤ Real.log D ^ 12 := pow_le_pow_right₀ hL1 (by norm_num)
    calc (sII.card : ℝ) ≤ _ := hII
      _ = 16 * 10 ^ 22 * (DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
            * D ^ ((151/50 : ℝ) * (1 - σ))) * Real.log D ^ 5 := by ring
      _ ≤ 16 * 10 ^ 22 * (DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
            * D ^ ((151/50 : ℝ) * (1 - σ))) * Real.log D ^ 12 := by
          gcongr
  have hfin : 16 * 10 ^ 22 * (DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
        * D ^ ((151/50 : ℝ) * (1 - σ))) * Real.log D ^ 12
      + 4 * 10 ^ 10 * (DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
        * D ^ ((151/50 : ℝ) * (1 - σ))) * Real.log D ^ 12
      ≤ 2 * 10 ^ 23 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
        * Real.log D ^ 12 * D ^ ((151/50 : ℝ) * (1 - σ)) := by
    have h0 : 0 ≤ DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
        * D ^ ((151/50 : ℝ) * (1 - σ)) * Real.log D ^ 12 := by positivity
    nlinarith
  linarith

/-! ## §5 The representative systems: `card_repIndex_le`, the low `χ₀` zeros -/

/-- The height predicate of the `χ₀` instance (`good ρ := Λ ≤ |Im ρ|`); a `def`, so that the
classical `DecidablePred` instance of `sum_good_le_of_localCount` is the one used here. -/
def goodHigh (Λ : ℝ) (ρ : ℂ) : Prop := Λ ≤ |ρ.im|

/-- One parity system, thinned into `Q₁ ≤ 2𝓛` classes and counted by `family_card_le`. -/
theorem card_repIndex_le (d : ℕ) [NeZero d] {σ t : ℝ} (hσ : 39/50 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 2 ≤ t) (hL : 40 ≤ Real.log ((d : ℝ) * (t + 2)))
    (𝒳 : Finset (DirichletCharacter ℂ d)) (good : ℂ → Prop) (par : ℕ)
    (hgood : ∀ p ∈ repIndex σ t 𝒳 good par, p.1 = 1 →
      Real.log ((d : ℝ) * (t + 2)) ≤ |(rep p.1 σ t good p.2).im|) :
    ((repIndex σ t 𝒳 good par).card : ℝ)
      ≤ 2 * Real.log ((d : ℝ) * (t + 2))
        * (2 * 10 ^ 23 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
          * Real.log ((d : ℝ) * (t + 2)) ^ 12
          * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ))) := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hL1 : 1 ≤ Real.log ((d : ℝ) * (t + 2)) := by linarith
  rw [card_repIndex_eq_sum_cls]
  push_cast
  calc ∑ c ∈ Finset.range (Q1 d t),
        (((repIndex σ t 𝒳 good par).filter (fun p => cls d t p = c)).card : ℝ)
      ≤ ∑ c ∈ Finset.range (Q1 d t),
          (2 * 10 ^ 23 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
            * Real.log ((d : ℝ) * (t + 2)) ^ 12
            * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ))) := by
        refine Finset.sum_le_sum fun c _ => ?_
        refine family_card_le d hσ hσ1 ht hL _ Prod.fst (fun p => rep p.1 σ t good p.2)
          (fun p hp => ?_) (fun p hp q hq hne hχ => ?_)
        · have hp' := (Finset.mem_filter.mp hp).1
          obtain ⟨h1, h2, h3, -, h5⟩ := mem_zeroFinset.mp (rep_mem_zeroFinset hp')
          exact ⟨h1, h2, h3, h5, hgood p hp'⟩
        · exact thin_spacing ht0 hL1 (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 hχ
            hne ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm)
    _ = (Q1 d t : ℝ) * (2 * 10 ^ 23 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
            * Real.log ((d : ℝ) * (t + 2)) ^ 12
            * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ 2 * Real.log ((d : ℝ) * (t + 2))
        * (2 * 10 ^ 23 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
          * Real.log ((d : ℝ) * (t + 2)) ^ 12
          * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ))) := by
        have hD0 : (0 : ℝ) < (d : ℝ) * (t + 2) := by linarith [four_le_scale (d := d) ht]
        have hCG := GammaStrip.CGamma_pos
        have hCτ := DetectionShift.Ctau_pos
        exact mul_le_mul_of_nonneg_right (Q1_le_two_mul (by linarith)) (by positivity)

/-- The `χ₀` zeros of the box below height `𝓛` carry multiplicity mass `≤ 2240·𝓛²`
(`zeroCountBox_trivChar_le` at height `𝓛`). -/
lemma low_zeta_count (d : ℕ) [NeZero d] {σ t : ℝ} (hσ : 39/50 ≤ σ) (ht : 2 ≤ t) :
    ((∑ ρ ∈ (zeroFinset (1 : DirichletCharacter ℂ d) σ t).filter
        (fun ρ => ¬ goodHigh (Real.log ((d : ℝ) * (t + 2))) ρ),
        analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ d)) ρ : ℕ) : ℝ)
      ≤ 2240 * Real.log ((d : ℝ) * (t + 2)) ^ 2 := by
  have h𝓛 : 1 < Real.log ((d : ℝ) * (t + 2)) := one_lt_log_scale ht
  have hsub : (zeroFinset (1 : DirichletCharacter ℂ d) σ t).filter
        (fun ρ => ¬ goodHigh (Real.log ((d : ℝ) * (t + 2))) ρ)
      ⊆ zeroFinset (1 : DirichletCharacter ℂ d) (1/2) (Real.log ((d : ℝ) * (t + 2))) := by
    intro ρ hρ
    rw [Finset.mem_filter, mem_zeroFinset] at hρ
    obtain ⟨⟨h1, h2, -, h4, h5⟩, h6⟩ := hρ
    rw [mem_zeroFinset]
    refine ⟨by linarith, h2, ?_, h4, h5⟩
    rw [goodHigh] at h6
    push Not at h6
    exact h6.le
  calc _ ≤ ((zeroCountBox (1 : DirichletCharacter ℂ d) (1/2)
        (Real.log ((d : ℝ) * (t + 2))) : ℕ) : ℝ) := by
        rw [zeroCountBox]
        exact_mod_cast Finset.sum_le_sum_of_subset hsub
    _ ≤ 1120 * Real.log ((d : ℝ) * (t + 2)) * Real.log (Real.log ((d : ℝ) * (t + 2)) + 2) :=
        zeroCountBox_trivChar_le h𝓛.le
    _ ≤ 2240 * Real.log ((d : ℝ) * (t + 2)) ^ 2 := by
        have := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.log ((d : ℝ) * (t + 2)) + 2)
        nlinarith

/-! ## §6 Theorem L -/

/-- Theorem L for `𝓛 ≥ 40` (§3.6): the two covering instances plus the low `χ₀` zeros. -/
theorem logged_density_large (d : ℕ) [NeZero d] {σ t : ℝ} (hσ : 39/50 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 2 ≤ t) (hL : 40 ≤ Real.log ((d : ℝ) * (t + 2))) :
    ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
      ≤ 10 ^ 27 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
          * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ))
          * Real.log ((d : ℝ) * (t + 2)) ^ 14 := by
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hD0 : (0 : ℝ) < (d : ℝ) * (t + 2) := by linarith [four_le_scale (d := d) ht]
  have hP0 : 0 < ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ)) := Real.rpow_pos_of_pos hD0 _
  have hCG1 : 1 ≤ GammaStrip.CGamma := by rw [GammaStrip.CGamma_def]; norm_num
  have hCτ1 := DetectionShift.one_le_Ctau
  have hloc : ∀ χ : DirichletCharacter ℂ d, ∀ γ₀ : ℝ, |γ₀| ≤ t →
      (localCount χ σ t γ₀ : ℝ) ≤ 112 * Real.log ((d : ℝ) * (t + 2)) :=
    fun χ γ₀ hγ₀ => localCount_le_logged χ hσ hσ1 ht0 (by linarith) hγ₀
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 2 * 10 ^ 23 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
      * Real.log ((d : ℝ) * (t + 2)) ^ 12 * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ)) :=
    ⟨_, rfl⟩
  have h𝓛0 : 0 ≤ 112 * Real.log ((d : ℝ) * (t + 2)) := by linarith
  -- instance 1: the non-principal characters, all zeros
  have hJ1 : ∀ par, ((repIndex σ t (Finset.univ.erase 1) (fun _ => True) par).card : ℝ)
      ≤ 2 * Real.log ((d : ℝ) * (t + 2)) * B := fun par => by
    rw [hB]
    exact card_repIndex_le d hσ hσ1 ht hL _ _ par
      (fun p hp h1 => absurd h1 (Finset.ne_of_mem_erase (mem_repIndex.mp hp).1))
  have hsum1 := sum_good_le_of_localCount (d := d) (σ := σ) (t := t)
    (𝒳 := Finset.univ.erase 1) (good := fun _ => True) ht0 (fun χ _ γ₀ hγ₀ => hloc χ γ₀ hγ₀)
  simp only [Finset.filter_true, Nat.cast_sum] at hsum1
  have h1 : ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d), (zeroCountBox χ σ t : ℝ)
      ≤ 112 * Real.log ((d : ℝ) * (t + 2)) * (2 * (2 * Real.log ((d : ℝ) * (t + 2)) * B)) := by
    have hcast : ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d), (zeroCountBox χ σ t : ℝ)
        = ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d), ∑ ρ ∈ zeroFinset χ σ t,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
      simp only [zeroCountBox, Nat.cast_sum]
    rw [hcast]
    refine hsum1.trans (mul_le_mul_of_nonneg_left ?_ h𝓛0)
    linarith [hJ1 0, hJ1 1]
  -- instance 0: the principal character, zeros at height ≥ 𝓛
  have hJ0 : ∀ par, ((repIndex σ t {1} (goodHigh (Real.log ((d : ℝ) * (t + 2)))) par).card : ℝ)
      ≤ 2 * Real.log ((d : ℝ) * (t + 2)) * B := fun par => by
    rw [hB]
    exact card_repIndex_le d hσ hσ1 ht hL _ _ par (fun p hp _ => good_rep hp)
  have hsum0 := sum_good_le_of_localCount (d := d) (σ := σ) (t := t)
    (𝒳 := {1}) (good := goodHigh (Real.log ((d : ℝ) * (t + 2)))) ht0
    (fun χ _ γ₀ hγ₀ => hloc χ γ₀ hγ₀)
  rw [Finset.sum_singleton] at hsum0
  have hlow := low_zeta_count d hσ ht
  have h0 : (zeroCountBox (1 : DirichletCharacter ℂ d) σ t : ℝ)
      ≤ 112 * Real.log ((d : ℝ) * (t + 2)) * (2 * (2 * Real.log ((d : ℝ) * (t + 2)) * B))
        + 2240 * Real.log ((d : ℝ) * (t + 2)) ^ 2 := by
    have hsplit : (zeroCountBox (1 : DirichletCharacter ℂ d) σ t : ℝ)
        = ((∑ ρ ∈ (zeroFinset (1 : DirichletCharacter ℂ d) σ t).filter
              (goodHigh (Real.log ((d : ℝ) * (t + 2)))),
              analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ d)) ρ
              : ℕ) : ℝ)
          + ((∑ ρ ∈ (zeroFinset (1 : DirichletCharacter ℂ d) σ t).filter
              (fun ρ => ¬ goodHigh (Real.log ((d : ℝ) * (t + 2))) ρ),
              analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ d)) ρ
              : ℕ) : ℝ) := by
      rw [zeroCountBox, ← Nat.cast_add, Finset.sum_filter_add_sum_filter_not]
    rw [hsplit]
    have hJsum : ((repIndex σ t ({1} : Finset (DirichletCharacter ℂ d))
          (goodHigh (Real.log ((d : ℝ) * (t + 2)))) 0).card : ℝ)
        + ((repIndex σ t ({1} : Finset (DirichletCharacter ℂ d))
          (goodHigh (Real.log ((d : ℝ) * (t + 2)))) 1).card : ℝ)
        ≤ 2 * (2 * Real.log ((d : ℝ) * (t + 2)) * B) := by linarith [hJ0 0, hJ0 1]
    have hgoodpart := hsum0.trans (mul_le_mul_of_nonneg_left hJsum h𝓛0)
    linarith
  -- assemble
  have htot : ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
      = (zeroCountBox (1 : DirichletCharacter ℂ d) σ t : ℝ)
        + ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ d), (zeroCountBox χ σ t : ℝ) :=
    (Finset.add_sum_erase Finset.univ _ (Finset.mem_univ 1)).symm
  rw [htot]
  have hB' : 896 * Real.log ((d : ℝ) * (t + 2)) ^ 2 * B
      = 1792 * 10 ^ 23 * (DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
          * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ)) * Real.log ((d : ℝ) * (t + 2)) ^ 14) := by
    rw [hB]; ring
  have hK : 1 ≤ DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
      * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ)) :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCτ1) (one_le_pow₀ hCG1))
      (Real.one_le_rpow (by linarith [four_le_scale (d := d) ht]) (by nlinarith))
  have hL14 : Real.log ((d : ℝ) * (t + 2)) ^ 2 ≤ Real.log ((d : ℝ) * (t + 2)) ^ 14 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have h2240 : Real.log ((d : ℝ) * (t + 2)) ^ 2
      ≤ DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
          * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ)) * Real.log ((d : ℝ) * (t + 2)) ^ 14 := by
    have := mul_le_mul hK hL14 (by positivity) (by linarith)
    linarith
  linarith

/-- Theorem L for `𝓛 < 40` (§3.5, audit F5): the I6 fallback, absorbed into `C_H`. -/
theorem logged_density_small (d : ℕ) [NeZero d] {σ t : ℝ} (hσ : 39/50 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 2 ≤ t) (hL : Real.log ((d : ℝ) * (t + 2)) < 40) :
    ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
      ≤ 10 ^ 27 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
          * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ))
          * Real.log ((d : ℝ) * (t + 2)) ^ 14 := by
  have hD4 := four_le_scale (d := d) ht
  have h𝓛1 := one_lt_log_scale (d := d) ht
  have hd1 := one_le_d (d := d)
  have ht0 : (0 : ℝ) ≤ t := by linarith
  have hmono : ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
      ≤ ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ (1/2) t : ℝ) :=
    Finset.sum_le_sum fun χ _ => by
      exact_mod_cast zeroCountBox_mono (χ := χ) (T := t) (by linarith : (1/2 : ℝ) ≤ σ)
  have hI6 := Carmichael.sum_zeroCountBox_le d (by linarith : (1 : ℝ) ≤ t)
  have hDexp : (d : ℝ) * (t + 2) < Real.exp 40 := by
    rw [← Real.exp_log (by linarith : (0 : ℝ) < (d : ℝ) * (t + 2))]
    exact Real.exp_lt_exp.mpr hL
  have hexp40 : Real.exp 40 ≤ (2.72 : ℝ) ^ 40 := by
    have := Real.exp_one_lt_d9
    calc Real.exp 40 = (Real.exp 1) ^ 40 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 2.72 ^ 40 := pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) 40
  have hlhs : ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ) ≤ 10 ^ 27 := by
    have h1 : 1120 * t * d * Real.log ((d : ℝ) * (t + 2)) ≤ 1120 * ((d : ℝ) * (t + 2)) * 40 := by
      have hdt : t * d ≤ (d : ℝ) * (t + 2) := by nlinarith
      have h0 : (0 : ℝ) ≤ 1120 * t * d := by positivity
      have hlog0 : (0 : ℝ) ≤ Real.log ((d : ℝ) * (t + 2)) := by linarith
      nlinarith
    have h2 : (1120 : ℝ) * ((d : ℝ) * (t + 2)) * 40 ≤ 1120 * 2.72 ^ 40 * 40 := by nlinarith
    have h3 : (1120 : ℝ) * 2.72 ^ 40 * 40 ≤ 10 ^ 27 := by norm_num
    linarith
  have hrhs : (10 : ℝ) ^ 27 ≤ 10 ^ 27 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
      * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ)) * Real.log ((d : ℝ) * (t + 2)) ^ 14 := by
    have hCG1 : 1 ≤ GammaStrip.CGamma := by rw [GammaStrip.CGamma_def]; norm_num
    have hCτ1 := DetectionShift.one_le_Ctau
    have hK : 1 ≤ DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
        * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ)) * Real.log ((d : ℝ) * (t + 2)) ^ 14 :=
      one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCτ1) (one_le_pow₀ hCG1))
          (Real.one_le_rpow (by linarith) (by nlinarith)))
        (one_le_pow₀ h𝓛1.le)
    calc (10 : ℝ) ^ 27 = 10 ^ 27 * 1 := by ring
      _ ≤ 10 ^ 27 * (DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
          * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ))
          * Real.log ((d : ℝ) * (t + 2)) ^ 14) := mul_le_mul_of_nonneg_left hK (by norm_num)
      _ = _ := by ring
  linarith

/-- **THEOREM L** (routez/Z6-logged.md §3.6): for every `d ≥ 1`, `t ≥ 2`, `σ ∈ [39/50, 1]`,
`∑_{χ mod d} N(σ,t,χ) ≤ 10²⁷·C_τ²·C_Γ²·(d(t+2))^{(151/50)(1−σ)}·log¹⁴(d(t+2))`. -/
theorem logged_density (d : ℕ) [NeZero d] {σ t : ℝ} (hσ : 39/50 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 2 ≤ t) :
    ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
      ≤ 10 ^ 27 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
          * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ))
          * Real.log ((d : ℝ) * (t + 2)) ^ 14 := by
  rcases lt_or_ge (Real.log ((d : ℝ) * (t + 2))) 40 with h | h
  · exact logged_density_small d hσ hσ1 ht h
  · exact logged_density_large d hσ hσ1 ht h

/-- **The Z0a §7 / Z0b I3′ form** (§3.7, audit F3): profile `151/50`, `c₀ = 1`, `K = 14`,
`C_H' = 2·10²⁷·C_τ²·C_Γ²`, with `(d·t)` in place of `d(t+2)`. -/
theorem logged_density_ledger (d : ℕ) [NeZero d] {σ t : ℝ} (hσ : 39/50 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 2 ≤ t) :
    ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ)
      ≤ 2 * 10 ^ 27 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
          * ((d : ℝ) * t) ^ ((151/50 : ℝ) * (1 - σ))
          * Real.log ((d : ℝ) * (t + 2)) ^ 14 := by
  have h := logged_density d hσ hσ1 ht
  have hdt0 : 0 < (d : ℝ) * t := by have := one_le_d (d := d); nlinarith
  have hD0 : (0 : ℝ) < (d : ℝ) * (t + 2) := by linarith [four_le_scale (d := d) ht]
  have he0 : 0 ≤ (151/50 : ℝ) * (1 - σ) := by nlinarith
  have he1 : (151/50 : ℝ) * (1 - σ) ≤ 1 := by nlinarith
  have hpow : ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ))
      ≤ 2 * ((d : ℝ) * t) ^ ((151/50 : ℝ) * (1 - σ)) := by
    calc ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ))
        ≤ (2 * ((d : ℝ) * t)) ^ ((151/50 : ℝ) * (1 - σ)) :=
          Real.rpow_le_rpow hD0.le (scale_le_two_mul ht) he0
      _ = 2 ^ ((151/50 : ℝ) * (1 - σ)) * ((d : ℝ) * t) ^ ((151/50 : ℝ) * (1 - σ)) :=
          Real.mul_rpow (by norm_num) hdt0.le
      _ ≤ 2 * ((d : ℝ) * t) ^ ((151/50 : ℝ) * (1 - σ)) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le (by norm_num) he1)
            (Real.rpow_nonneg hdt0.le _)
  have hc : 0 ≤ 10 ^ 27 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
      * Real.log ((d : ℝ) * (t + 2)) ^ 14 := by
    have := DetectionShift.Ctau_pos
    have := GammaStrip.CGamma_pos
    positivity
  calc ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ σ t : ℝ) ≤ _ := h
    _ = (10 ^ 27 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
          * Real.log ((d : ℝ) * (t + 2)) ^ 14)
          * ((d : ℝ) * (t + 2)) ^ ((151/50 : ℝ) * (1 - σ)) := by ring
    _ ≤ (10 ^ 27 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2
          * Real.log ((d : ℝ) * (t + 2)) ^ 14)
          * (2 * ((d : ℝ) * t) ^ ((151/50 : ℝ) * (1 - σ))) :=
        mul_le_mul_of_nonneg_left hpow hc
    _ = _ := by ring

/-- **THE FROZEN INTERFACE** (`Carmichael.LoggedDensity`, routez/Z0a-ledger.md §7 Z6-logged
form): `CH = 2·10²⁷·C_τ²·C_Γ²`, `P = 151/50`, `c₀ = 1`, `K = 14`. -/
theorem loggedDensity : Carmichael.LoggedDensity := by
  refine ⟨2 * 10 ^ 27 * DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2, 151/50, 1, 14,
    ?_, by norm_num, by norm_num, le_rfl, by norm_num, ?_⟩
  · have hCG1 : 1 ≤ GammaStrip.CGamma := by rw [GammaStrip.CGamma_def]; norm_num
    have hCτ1 := DetectionShift.one_le_Ctau
    have hK : 1 ≤ DetectionShift.Ctau ^ 2 * GammaStrip.CGamma ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hCτ1) (one_le_pow₀ hCG1)
    nlinarith
  · intro d _ t σ ht hσ hσ1
    rw [Real.rpow_one]
    exact logged_density_ledger d hσ hσ1 ht

end

end LoggedDensity
end Carmichael

