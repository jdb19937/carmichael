/-
Route Z, sortie Z6d-B: blueprint §7 of routez/Z0b-density.md — the log-free local
zero count (Lemma 7.1) and the well-spaced representatives in two parity systems
(Construction 7.2 with properties (a) covering, (b) spacing, (c) detection).
Consumed by §8 (the master count, Theorem 8.3) and §9 band (c) of the zero-density
theorem Z6d.  No `sorry`, no `axiom`, no `native_decide`.

NOTATION.  `d ≥ 1` (`[NeZero d]`) is the modulus, `t` the height, `σ` the abscissa,
`D = d·(t+2)` written out as `(d:ℝ) * (t + 2)`, `𝓛 = Real.log ((d:ℝ) * (t + 2))`,
`Δ = 1/𝓛`, `λ = (1 − σ)·𝓛`.  Zeros are `ZeroCount.zeroFinset χ σ t` (distinct zeros of
`L(·,χ)` in `[σ,1] × [−t,t]`, `s = 1` excluded) weighted by
`analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ`; `N(σ,t,χ)` is
`ZeroCount.zeroCountBox χ σ t`.  A predicate `good : ℂ → Prop` (classical
decidability) selects which zeros count: `fun _ => True` for Theorem M,
`fun ρ => Λ₀ ≤ |ρ.im|` for §9 band (c).

STATEMENTS.

§1  Lemma 7.1 (log-free local count).
 * `Cloc : ℝ := 2600015` (`= 5·(1 + C_z + C_Lan)`, `C_z = 2`, `C_Lan = 520000`).
 * `localCount χ σ t γ₀ : ℕ` :=
     `∑ ρ ∈ (zeroFinset χ σ t).filter (|Im ρ − γ₀| ≤ 1/𝓛), ord(ρ)`.
 * `localCount_le (χ) (hσ : 99/100 ≤ σ) (hσ1 : σ ≤ 1) (ht : 0 ≤ t) (hL : 25 ≤ 𝓛)
     (hγ₀ : |γ₀| ≤ t) : (localCount χ σ t γ₀ : ℝ) ≤ Cloc * (1 + (1 − σ) * 𝓛)`
   — EVERY `χ mod d`, the principal character included.  Log-free: no power of `𝓛`.
   Engines: `localCount_le_of_ne_one` (`χ ≠ 1`, bound `5 + 2400000(1+λ)`, from
   `SmallDiskZeroCount.sum_ord_smallDisk_le` at radius `η = (1−σ) + Δ ≤ 1/20`) and
   `localCount_le_of_eq_one` (`χ = χ₀`, bound `13 + 2400000(1+λ)`, from the new
   `sum_ord_zeta_smallDisk_le`).
 * `sum_ord_zeta_smallDisk_le (τ) (hw0 : 0 < w) (hw : w ≤ 1/20) {F : Finset ℂ}
     (hF : ∀ ρ ∈ F, ζ(ρ) = 0 ∧ dist ρ (1 + τI) ≤ w) :
     ∑ ρ ∈ F, ord_ζ(ρ) ≤ 13 + 2400000·w·log(|τ|+2)`
   — the `ζ` small-disk count, via the generic Landau expansion
   `EF.norm_logDeriv_sub_sum_diskZeros_le` for the Abel-summed eta function
   (`EF.diskData_etaFun`), `ζ′/ζ = η′/η − g′/g` (`EF.logDeriv_eta_split`),
   `‖g′/g‖ ≤ 2/w` (`norm_logDeriv_gFun_le`), `‖ζ′/ζ‖ ≤ 1/w + 2`
   (`SmallDiskZeroCount.norm_logDeriv_le_of_re_eq` at modulus `1`), and
   `ord_ζ ≤ ord_η` (`ZeroCount.analyticOrderNatAt_zeta_le_etaFun`).

§2  Construction 7.2 (the family/interface type).
 * `idx d t ρ : ℕ := ⌊(Im ρ + t)·𝓛⌋₊` — the cell index (`[−t,t]` cut into half-open
   intervals `I_m = [−t + mΔ, −t + (m+1)Δ)`); `Qpar d t := ⌊2t𝓛⌋₊`, so `m ≤ Qpar`.
 * `cell χ σ t good m : Finset ℂ` — the good zeros of `L(·,χ)` in the box with
   `idx = m`.
 * `rep χ σ t good m : ℂ` — the chosen representative (`Classical.choose` on
   `(cell …).Nonempty`; junk `0` when the cell is empty).
 * `repIndex σ t 𝒳 good par : Finset (DirichletCharacter ℂ d × ℕ)` — the parity
   system `par ∈ {0,1}`: pairs `(χ, m)` with `χ ∈ 𝒳`, `m ≤ Qpar`, `m % 2 = par`,
   nonempty cell.  `J_ev = (repIndex … 0).card`, `J_od = (repIndex … 1).card`.
   For an index `p`, the character is `p.1`, the zero is `rep p.1 σ t good p.2`, and
   the shifted point of §8 is `repPoint σ t good p := rep p.1 σ t good p.2 − σ`
   (`repPoint_re`, `repPoint_im`).
 * Membership vocabulary: `mem_cell`, `mem_repIndex`, `rep_mem_cell_of_mem`,
   `rep_mem_zeroFinset` (every representative is a zero in the box: `σ ≤ Re ≤ 1`,
   `|Im| ≤ t`, `ρ ≠ 1`, `L(ρ,χ) = 0`), `good_rep`, `idx_rep`, `abs_im_rep_le`,
   `repPoint_re_nonneg` (`0 ≤ Re(ρ_p − σ)`).

§3  Property (b), spacing — exactly the hypothesis of Lemma 6.4.
 * `rep_spacing (ht : 0 ≤ t) (hp hq : ∈ repIndex σ t 𝒳 good par) (hχ : p.1 = q.1)
     (hne : p ≠ q) : 1/𝓛 ≤ |Im ρ_p − Im ρ_q|`.
 * `rep_band_card_le (ht : 0 ≤ t) (hp : p ∈ repIndex σ t 𝒳 good par) (m : ℕ) :
     ((repIndex σ t 𝒳 good par).filter (fun q => q.1 = p.1 ∧
        m·(1/𝓛) ≤ |Im ρ_q − Im ρ_p| ∧ |Im ρ_q − Im ρ_p| < (m+1)·(1/𝓛))).card ≤ 2`
   — for every `m` (no `m ≥ 1` needed).

§4/§6  Property (a), covering.
 * `sum_good_le_of_localCount (ht : 0 ≤ t) (hloc : ∀ χ ∈ 𝒳, ∀ γ₀, |γ₀| ≤ t →
     localCount χ σ t γ₀ ≤ B) :
     ∑ χ ∈ 𝒳, ∑ ρ ∈ (zeroFinset χ σ t).filter good, ord(ρ) ≤ B·(J_ev + J_od)`
   (abstract form, any local-count bound `B`).
 * `sum_good_le (hσ) (hσ1) (ht) (hL : 25 ≤ 𝓛) (𝒳) (good) :
     ∑ χ ∈ 𝒳, ∑ ρ ∈ (zeroFinset χ σ t).filter good, ord(ρ)
       ≤ Cloc·(1 + (1−σ)𝓛)·(J_ev + J_od)` — with Lemma 7.1 inserted.
 * `sum_zeroCountBox_le (hσ) (hσ1) (ht) (hL) (𝒳) :
     ∑ χ ∈ 𝒳, zeroCountBox χ σ t ≤ Cloc·(1 + (1−σ)𝓛)·(J_ev + J_od)`
   at `good := fun _ => True` (Theorem M / Corollary 8.4's instance).

§5  Property (c), detection (blueprint Proposition 4.4 at every representative).
   Common hypotheses: `99/100 ≤ σ ≤ 1`, `0 ≤ t`, `200 ≤ 𝓛`, (T1)
   `2·10¹⁴·Ctau·𝓛 ≤ D^{79/4000}`, `p ∈ repIndex σ t 𝒳 good par`, and the `χ₀`
   height clause `hγ : p.1 = 1 → Lambda0 D σ (log(3200·e·60)) ≤ |Im ρ_p|`.
 * `rep_detect_QR … : (1/400)·QR d (Rpar D)·𝓛 ≤ ‖Fdet p.1 (z1par D) (z2par D)
     (Rpar D) (Xpar D) ρ_p‖` — the `Q_R` form §8.3 consumes.
 * `rep_detect … : (1/400)·(φ(d)/d)·𝓛 ≤ ‖Fdet … ρ_p‖` — the `φ(d)/d` form.
 * `rep_detect_QR_of_good … (hgood : ∀ χ ∈ 𝒳, χ = 1 → ∀ ρ, good ρ → Λ₀(σ) ≤ |Im ρ|)`
   — the height clause discharged through `good` (§9 band (c); vacuous when
   `χ₀ ∉ 𝒳`).
 * `norm_Fdet_ge_half_P1` — the `P(1)/2 ≤ ‖Fdet‖` assembly (the last step of
   `Detection.detector_lower_bound_of_P1` with the conclusion kept in `P(1)`), so
   that both `P1_lower_QR` and `totient_div_le_QR` can be matched against it.

DELTAS VS. THE BLUEPRINT (none silent).
 1. `C_loc = 2600015` is the blueprint numeral `5(1 + 2 + 520000)`; the proof goes
    through the delivered small-disk counts (`5 + 2400000·η𝓛` for `χ ≠ 1`,
    `13 + 2400000·η𝓛` for `χ₀`) rather than through I2 + I9(a) directly; both are
    `≤ C_loc(1+λ)` since `η𝓛 = 1 + λ` exactly (`eta_mul_log`).
 2. Threshold for Lemma 7.1: `25 ≤ 𝓛` (needed for `η ≤ 1/100 + 1/25 = 1/20`, the
    range of `Census.tsum_vonMangoldt_rpow_le`); weaker than the blueprint's
    `D ≥ D₀ ≥ e^{100}` and than the detector's `200 ≤ 𝓛`.
 3. The height hypothesis is `0 ≤ t` throughout (the blueprint's `t ≥ 2` is not
    used here); `1 < D` follows from `d ≥ 1`, `t ≥ 0` and is not carried.
 4. The `χ₀` clause in (c) is at `Λ₀(σ)` (via `Detector.detector_lower_bound_of_P1`
    at the actual `σ`), which is weaker than the frozen Z6c display's `Λ₀(99/100)`
    since `Λ₀` decreases in `σ`; either may be supplied.
 5. Cells are indexed `m = 0, …, Qpar = ⌊2t𝓛⌋₊` (so `Qpar + 1 ≤ ⌈2t𝓛⌉ + 1` cells,
    versus the blueprint's `Q = ⌈2t𝓛⌉`); only the parity structure matters.
 6. The `χ₀` case of Lemma 7.1 is delivered unconditionally (no hypothesis carried):
    the `ζ` Landau input is `EF.norm_logDeriv_sub_sum_diskZeros_le` from
    `ExplicitFormula.lean` (generic `DiskData`), instantiated at `etaFun`.
 7. (b)'s second clause is proved for every `m : ℕ`, not only `m ≥ 1`.

HYPOTHESES CARRIED (summary): `[NeZero d]`; `99/100 ≤ σ ≤ 1`; `0 ≤ t`; `25 ≤ 𝓛`
(Lemma 7.1 and (a)); `200 ≤ 𝓛` and (T1) with `DetectionShift.Ctau = 2^{2^{800}}`
((c) only); the `χ₀` height clause ((c) only, through `hγ` or `good`).
-/
import Carmichael.SmallDiskZeroCount
import Carmichael.ExplicitFormula
import Carmichael.DetectionShift

set_option autoImplicit false

namespace Carmichael
namespace Representatives

open Complex Finset Metric
open scoped Classical

noncomputable section

/-! ### §1 The log-free local count (blueprint Lemma 7.1) -/

/-- `C_loc := 5·(1 + C_z + C_Lan)` with `C_z = 2`, `C_Lan = 520000` (blueprint §7). -/
def Cloc : ℝ := 2600015

lemma Cloc_eq : Cloc = 2600015 := rfl

variable {d : ℕ} [NeZero d]

/-- **The local count**: zeros of `L(·,χ)` (with multiplicity) in the box
`[σ,1] × [−t,t]` whose ordinate is within `Δ = 1/log(d(t+2))` of `γ₀`. -/
def localCount (χ : DirichletCharacter ℂ d) (σ t γ₀ : ℝ) : ℕ :=
  ∑ ρ ∈ (zeroFinset χ σ t).filter
      (fun ρ : ℂ => |ρ.im - γ₀| ≤ 1 / Real.log ((d : ℝ) * (t + 2))),
    analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

/-- `d·(t+2) ≥ 2` for `t ≥ 0`. -/
lemma two_le_scale {t : ℝ} (ht : 0 ≤ t) : (2 : ℝ) ≤ (d : ℝ) * (t + 2) := by
  have hd : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  nlinarith

/-- `log(d(t+2)) > 0` for `t ≥ 0`. -/
lemma log_scale_pos {t : ℝ} (ht : 0 ≤ t) : 0 < Real.log ((d : ℝ) * (t + 2)) :=
  Real.log_pos (by linarith [two_le_scale (d := d) ht])

/-- `log(d(|γ₀|+2)) ≤ log(d(t+2))` for `|γ₀| ≤ t`. -/
lemma log_height_le {t γ₀ : ℝ} (hγ₀ : |γ₀| ≤ t) :
    Real.log ((d : ℝ) * (|γ₀| + 2)) ≤ Real.log ((d : ℝ) * (t + 2)) := by
  have hd : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have h0 : (0 : ℝ) < (d : ℝ) * (|γ₀| + 2) := by
    have := abs_nonneg γ₀
    positivity
  exact Real.log_le_log h0 (by nlinarith [abs_nonneg γ₀])

/-- `log(|γ₀|+2) ≤ log(d(t+2))` for `|γ₀| ≤ t` (the `ζ` scale at modulus `1`). -/
lemma log_height_le_one {t γ₀ : ℝ} (hγ₀ : |γ₀| ≤ t) :
    Real.log (|γ₀| + 2) ≤ Real.log ((d : ℝ) * (t + 2)) := by
  have hd : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have h0 : (0 : ℝ) < |γ₀| + 2 := by linarith [abs_nonneg γ₀]
  exact Real.log_le_log h0 (by nlinarith [abs_nonneg γ₀])

/-- Window geometry: a point of `[σ,1] × [γ₀−Δ, γ₀+Δ]` lies in the closed disk of
radius `η = (1−σ) + Δ` around `1 + iγ₀`. -/
lemma dist_le_eta {σ Δ γ₀ : ℝ} (hσ1 : σ ≤ 1) (hΔ : 0 ≤ Δ) {ρ : ℂ}
    (hβ : σ ≤ ρ.re) (hβ1 : ρ.re ≤ 1) (him : |ρ.im - γ₀| ≤ Δ) :
    dist ρ (1 + γ₀ * I) ≤ (1 - σ) + Δ := by
  rw [Complex.dist_eq]
  have hre : (ρ - (1 + γ₀ * I)).re = ρ.re - 1 := by simp
  have him' : (ρ - (1 + γ₀ * I)).im = ρ.im - γ₀ := by simp
  refine norm_le_of_sq_le (by linarith) ?_
  rw [hre, him']
  have h1 := abs_le.mp him
  nlinarith [h1.1, h1.2]

/-- The `η`-disk around `1 + iγ₀` sits inside the Landau `13/8`-disk around
`2 + iγ₀` as soon as `η ≤ 5/8`. -/
lemma mem_closedBall_two_of_dist_le {γ₀ η : ℝ} (hη : η ≤ 5/8) {ρ : ℂ}
    (h : dist ρ (1 + γ₀ * I) ≤ η) :
    ρ ∈ closedBall ((2 : ℂ) + γ₀ * I) (13/8 : ℝ) := by
  rw [mem_closedBall]
  have h1 : dist (1 + γ₀ * I) ((2 : ℂ) + γ₀ * I) = 1 := by
    rw [Complex.dist_eq]
    have : (1 + γ₀ * I) - ((2 : ℂ) + γ₀ * I) = -1 := by ring
    rw [this, norm_neg, norm_one]
  linarith [dist_triangle ρ (1 + γ₀ * I) ((2 : ℂ) + γ₀ * I)]

/-- `η·𝓛 = 1 + λ` where `η = (1−σ) + 1/𝓛`, `λ = (1−σ)𝓛`. -/
lemma eta_mul_log {σ 𝓛 : ℝ} (h𝓛 : 0 < 𝓛) :
    ((1 - σ) + 1 / 𝓛) * 𝓛 = 1 + (1 - σ) * 𝓛 := by
  field_simp
  ring

/-- Blueprint Lemma 7.1 for `χ ≠ χ₀`, via the small-disk count
`sum_ord_smallDisk_le` at radius `η = (1−σ) + 1/𝓛 ≤ 1/20`. -/
theorem localCount_le_of_ne_one {χ : DirichletCharacter ℂ d} (hχ : χ ≠ 1)
    {σ t γ₀ : ℝ} (hσ : 99/100 ≤ σ) (hσ1 : σ ≤ 1) (ht : 0 ≤ t)
    (hL : 25 ≤ Real.log ((d : ℝ) * (t + 2))) (hγ₀ : |γ₀| ≤ t) :
    (localCount χ σ t γ₀ : ℝ)
      ≤ 5 + 2400000 * (1 + (1 - σ) * Real.log ((d : ℝ) * (t + 2))) := by
  set 𝓛 := Real.log ((d : ℝ) * (t + 2)) with h𝓛def
  have h𝓛 : 0 < 𝓛 := log_scale_pos (d := d) ht
  set η : ℝ := (1 - σ) + 1 / 𝓛 with hηdef
  have hΔ : 1 / 𝓛 ≤ 1 / 25 := one_div_le_one_div_of_le (by norm_num) hL
  have hΔ0 : 0 < 1 / 𝓛 := by positivity
  have hη0 : 0 < η := by rw [hηdef]; linarith
  have hη : η ≤ 1/20 := by rw [hηdef]; linarith
  -- the window is inside the `η`-disk, which is inside the Landau disk
  have hsub : (zeroFinset χ σ t).filter (fun ρ : ℂ => |ρ.im - γ₀| ≤ 1 / 𝓛)
      ⊆ (zeroDiskFinset χ γ₀).filter (fun ρ => dist ρ (1 + γ₀ * I) ≤ η) := by
    intro ρ hρ
    rw [Finset.mem_filter, mem_zeroFinset] at hρ
    obtain ⟨⟨h1, h2, _, _, h5⟩, h6⟩ := hρ
    have hd : dist ρ (1 + γ₀ * I) ≤ η := dist_le_eta hσ1 hΔ0.le h1 h2 h6
    rw [Finset.mem_filter, mem_zeroDiskFinset hχ]
    exact ⟨⟨mem_closedBall_two_of_dist_le (by linarith) hd, h5⟩, hd⟩
  have hmono : (localCount χ σ t γ₀ : ℝ)
      ≤ ((∑ ρ ∈ (zeroDiskFinset χ γ₀).filter (fun ρ => dist ρ (1 + γ₀ * I) ≤ η),
          analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) := by
    rw [localCount]
    exact_mod_cast Finset.sum_le_sum_of_subset hsub
  have hdisk := sum_ord_smallDisk_le hχ γ₀ hη0 hη
  have hlog : Real.log ((d : ℝ) * (|γ₀| + 2)) ≤ 𝓛 := log_height_le hγ₀
  have hprod : η * 𝓛 = 1 + (1 - σ) * 𝓛 := eta_mul_log h𝓛
  have hstep : 2400000 * η * Real.log ((d : ℝ) * (|γ₀| + 2)) ≤ 2400000 * η * 𝓛 := by
    have : 0 ≤ 2400000 * η := by positivity
    exact mul_le_mul_of_nonneg_left hlog this
  calc (localCount χ σ t γ₀ : ℝ)
      ≤ 5 + 2400000 * η * Real.log ((d : ℝ) * (|γ₀| + 2)) := le_trans hmono hdisk
    _ ≤ 5 + 2400000 * η * 𝓛 := by linarith
    _ = 5 + 2400000 * (1 + (1 - σ) * 𝓛) := by rw [mul_assoc, hprod]

/-- `‖g′/g‖ ≤ 2/w` on the line `Re s = 1 + w`, `0 < w ≤ 1/20`, for the correction
factor `g(s) = 1 − 2^{1−s}` of the eta function. -/
lemma norm_logDeriv_gFun_le {w : ℝ} (hw0 : 0 < w) (hw : w ≤ 1/20) {s : ℂ}
    (hs : s.re = 1 + w) :
    ‖deriv EF.gFun s / EF.gFun s‖ ≤ 2 / w := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hpow : ‖(2:ℂ) ^ ((1:ℂ) - s)‖ = Real.exp (-(w * Real.log 2)) := by
    rw [EF.norm_two_cpow, hs, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 1; ring
  set x := w * Real.log 2 with hxdef
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 := by nlinarith
  have hexp : Real.exp (-x) ≤ 1 - x / 2 := by
    have h1 : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
    have h2 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have h3 : 0 < Real.exp (-x) := Real.exp_pos _
    have h4 : Real.exp (-x) * (1 + x) ≤ 1 := by nlinarith
    have h5 : 1 ≤ (1 - x / 2) * (1 + x) := by nlinarith
    by_contra hcon
    push Not at hcon
    have := mul_lt_mul_of_pos_right hcon (by linarith : (0:ℝ) < 1 + x)
    linarith
  have hnum : ‖deriv EF.gFun s‖ ≤ Real.log 2 := by
    rw [EF.deriv_gFun, norm_mul, hpow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog2]
    have : Real.exp (-x) ≤ 1 := by linarith
    nlinarith
  have hden : x / 2 ≤ ‖EF.gFun s‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((2:ℂ) ^ ((1:ℂ) - s))
    rw [norm_one, hpow] at this
    unfold EF.gFun
    linarith
  have hden0 : 0 < ‖EF.gFun s‖ := by linarith
  rw [norm_div, div_le_div_iff₀ hden0 hw0]
  nlinarith

/-- **Small-disk count for `ζ`** (the principal-character engine): the total
multiplicity of any finite set `F` of zeros of `ζ` in the closed `w`-disk around
`1 + iτ` is at most `13 + 2400000·w·log(|τ|+2)`, for `0 < w ≤ 1/20`.  Route: the
generic Landau expansion `EF.norm_logDeriv_sub_sum_diskZeros_le` for the Abel-summed
eta function (`EF.diskData_etaFun`), `ζ′/ζ = η′/η − g′/g` and `ord_ζ ≤ ord_η`. -/
theorem sum_ord_zeta_smallDisk_le (τ : ℝ) {w : ℝ} (hw0 : 0 < w) (hw : w ≤ 1/20)
    {F : Finset ℂ} (hF : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ dist ρ (1 + τ * I) ≤ w) :
    (∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℝ)
      ≤ 13 + 2400000 * w * Real.log (|τ| + 2) := by
  have hDD := EF.diskData_etaFun
  set s₀ : ℂ := ((1 + w : ℝ) : ℂ) + τ * I with hs₀def
  have hs₀re : s₀.re = 1 + w := by simp [hs₀def]
  have hlog0 : 0 ≤ Real.log (|τ| + 2) := Real.log_nonneg (by linarith [abs_nonneg τ])
  -- members of `F`
  have hFprop : ∀ ρ ∈ F, 0 < ρ.re ∧ ρ ≠ 1 ∧ ρ ∈ EF.diskZeros etaFun τ := by
    intro ρ hρ
    obtain ⟨hz, hd⟩ := hF ρ hρ
    have hre : |ρ.re - 1| ≤ w := by
      have h := Complex.abs_re_le_norm (ρ - (1 + τ * I))
      rw [Complex.dist_eq] at hd
      have hre' : (ρ - (1 + τ * I)).re = ρ.re - 1 := by simp
      rw [hre'] at h
      linarith
    have hre0 : 0 < ρ.re := by have := abs_le.mp hre; linarith
    have hne1 : ρ ≠ 1 := by
      intro h
      rw [h] at hz
      exact riemannZeta_one_ne_zero hz
    have heta : etaFun ρ = 0 := by rw [EF.etaFun_eq_mul hre0 hne1, hz, mul_zero]
    refine ⟨hre0, hne1, ?_⟩
    rw [EF.mem_diskZeros hDD]
    exact ⟨mem_closedBall_two_of_dist_le (by linarith) hd, heta⟩
  set G := (EF.diskZeros etaFun τ).filter (fun ρ => dist ρ (1 + τ * I) ≤ w) with hGdef
  have hFG : F ⊆ G := by
    intro ρ hρ
    rw [hGdef, Finset.mem_filter]
    exact ⟨(hFprop ρ hρ).2.2, (hF ρ hρ).2⟩
  have h1 : (∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℝ)
      ≤ ∑ ρ ∈ G, (analyticOrderNatAt etaFun ρ : ℝ) := by
    calc (∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℝ)
        ≤ ∑ ρ ∈ F, (analyticOrderNatAt etaFun ρ : ℝ) := by
          refine Finset.sum_le_sum (fun ρ hρ => ?_)
          exact_mod_cast analyticOrderNatAt_zeta_le_etaFun (hFprop ρ hρ).1 (hFprop ρ hρ).2.1
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hFG (fun _ _ _ => by positivity)
  -- the Landau expansion of `η′/η` at `s₀`
  have hmem : s₀ ∈ closedBall ((2:ℂ) + τ * I) (3/2 : ℝ) := by
    rw [mem_closedBall, Complex.dist_eq]
    have : s₀ - ((2:ℂ) + τ * I) = ((1 + w - 2 : ℝ) : ℂ) := by rw [hs₀def]; push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hη0 : etaFun s₀ ≠ 0 := hDD.nz s₀ (by rw [hs₀re]; linarith)
  have hpf := EF.norm_logDeriv_sub_sum_diskZeros_le hDD τ hmem hη0
  rw [one_mul] at hpf
  have hzre : ∀ ρ ∈ EF.diskZeros etaFun τ, ρ.re ≤ 1 := by
    intro ρ hρ
    by_contra hcon
    push Not at hcon
    exact hDD.nz ρ hcon ((EF.mem_diskZeros hDD).mp hρ).2
  have hnonneg : ∀ ρ ∈ EF.diskZeros etaFun τ,
      0 ≤ ((analyticOrderNatAt etaFun ρ : ℂ) / (s₀ - ρ)).re := by
    intro ρ hρ
    apply Census.re_natCast_div_nonneg
    rw [Complex.sub_re, hs₀re]
    linarith [hzre ρ hρ]
  have hstrong : ∀ ρ ∈ G, (analyticOrderNatAt etaFun ρ : ℝ) / (4 * w)
      ≤ ((analyticOrderNatAt etaFun ρ : ℂ) / (s₀ - ρ)).re := by
    intro ρ hρ
    rw [hGdef, Finset.mem_filter] at hρ
    obtain ⟨hρD, hρd⟩ := hρ
    refine re_natCast_div_ge hw0 ?_ ?_
    · rw [Complex.sub_re, hs₀re]
      linarith [hzre ρ hρD]
    · have hdd : s₀ - ρ = ((w : ℝ) : ℂ) + ((1 + (τ : ℂ) * I) - ρ) := by
        rw [hs₀def]; push_cast; ring
      have hin : ‖(1 + (τ : ℂ) * I) - ρ‖ ≤ w := by
        rw [norm_sub_rev, ← Complex.dist_eq]
        exact hρd
      have hnorm : ‖s₀ - ρ‖ ≤ 2 * w := by
        rw [hdd]
        refine le_trans (norm_add_le _ _) ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
        linarith
      have h3 := normSq_le_of_norm_le hnorm
      nlinarith [h3]
  have hchain : (∑ ρ ∈ G, (analyticOrderNatAt etaFun ρ : ℝ)) / (4 * w)
      ≤ (∑ ρ ∈ EF.diskZeros etaFun τ,
          (analyticOrderNatAt etaFun ρ : ℂ) / (s₀ - ρ)).re := by
    rw [Finset.sum_div, Complex.re_sum]
    refine le_trans (Finset.sum_le_sum hstrong) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun ρ hρ _ => hnonneg ρ hρ)
  -- `‖η′/η(s₀)‖ ≤ 2/w + (1/w + 2)`
  have hLD : ‖deriv etaFun s₀ / etaFun s₀‖ ≤ 2 / w + (1 / w + 2) := by
    rw [EF.logDeriv_eta_split (by rw [hs₀re]; linarith)]
    refine le_trans (norm_add_le _ _) (add_le_add (norm_logDeriv_gFun_le hw0 hw hs₀re) ?_)
    have h := norm_logDeriv_le_of_re_eq (χ := (1 : DirichletCharacter ℂ 1)) hw0 hw hs₀re
    rwa [DirichletCharacter.LFunction_modOne_eq] at h
  have hPFside : (∑ ρ ∈ EF.diskZeros etaFun τ,
      (analyticOrderNatAt etaFun ρ : ℂ) / (s₀ - ρ)).re
      ≤ (2 / w + (1 / w + 2)) + 520000 * Real.log (|τ| + 2) := by
    have habs := Complex.abs_re_le_norm (deriv etaFun s₀ / etaFun s₀
      - ∑ ρ ∈ EF.diskZeros etaFun τ, (analyticOrderNatAt etaFun ρ : ℂ) / (s₀ - ρ))
    rw [Complex.sub_re] at habs
    have h1 := abs_le.mp (le_trans habs hpf)
    have h2 := abs_le.mp (Complex.abs_re_le_norm (deriv etaFun s₀ / etaFun s₀))
    linarith [h1.1, h2.2]
  have hmass := le_trans hchain hPFside
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * w)] at hmass
  have hwinv : w * (1 / w) = 1 := by field_simp
  have hwinv2 : w * (2 / w) = 2 := by field_simp
  nlinarith [hmass, hlog0, hw0, hw, hwinv, hwinv2, h1]

/-- Blueprint Lemma 7.1 for the principal character `χ₀ mod d`: its zeros in
`Re > 0` are the zeros of `ζ` with the same multiplicity, and the `ζ` small-disk
count applies. -/
theorem localCount_le_of_eq_one {σ t γ₀ : ℝ} (hσ : 99/100 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 0 ≤ t) (hL : 25 ≤ Real.log ((d : ℝ) * (t + 2))) (hγ₀ : |γ₀| ≤ t) :
    (localCount (1 : DirichletCharacter ℂ d) σ t γ₀ : ℝ)
      ≤ 13 + 2400000 * (1 + (1 - σ) * Real.log ((d : ℝ) * (t + 2))) := by
  set 𝓛 := Real.log ((d : ℝ) * (t + 2)) with h𝓛def
  have h𝓛 : 0 < 𝓛 := log_scale_pos (d := d) ht
  set η : ℝ := (1 - σ) + 1 / 𝓛 with hηdef
  have hΔ : 1 / 𝓛 ≤ 1 / 25 := one_div_le_one_div_of_le (by norm_num) hL
  have hΔ0 : 0 < 1 / 𝓛 := by positivity
  have hη0 : 0 < η := by rw [hηdef]; linarith
  have hη : η ≤ 1/20 := by rw [hηdef]; linarith
  set F := (zeroFinset (1 : DirichletCharacter ℂ d) σ t).filter
    (fun ρ : ℂ => |ρ.im - γ₀| ≤ 1 / 𝓛) with hFdef
  have hFprop : ∀ ρ ∈ F, riemannZeta ρ = 0 ∧ dist ρ (1 + γ₀ * I) ≤ η
      ∧ analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ d)) ρ
        = analyticOrderNatAt riemannZeta ρ := by
    intro ρ hρ
    rw [hFdef, Finset.mem_filter, mem_zeroFinset] at hρ
    obtain ⟨⟨h1, h2, _, h4, h5⟩, h6⟩ := hρ
    have hre0 : 0 < ρ.re := by linarith
    have hζ : riemannZeta ρ = 0 := by
      have hL' : DirichletCharacter.LFunctionTrivChar d ρ = 0 := h5
      rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta h4] at hL'
      rcases mul_eq_zero.mp hL' with h | h
      · exact absurd h (eulerFactor_ne_zero hre0)
      · exact h
    exact ⟨hζ, dist_le_eta hσ1 hΔ0.le h1 h2 h6, analyticOrderNatAt_trivChar_eq hre0 h4⟩
  have hsum : (localCount (1 : DirichletCharacter ℂ d) σ t γ₀ : ℝ)
      = ∑ ρ ∈ F, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
    rw [localCount]
    push_cast
    exact Finset.sum_congr rfl (fun ρ hρ => by rw [(hFprop ρ hρ).2.2])
  rw [hsum]
  have hζ := sum_ord_zeta_smallDisk_le γ₀ hη0 hη (F := F)
    (fun ρ hρ => ⟨(hFprop ρ hρ).1, (hFprop ρ hρ).2.1⟩)
  have hlog : Real.log (|γ₀| + 2) ≤ 𝓛 := log_height_le_one (d := d) hγ₀
  have hprod : η * 𝓛 = 1 + (1 - σ) * 𝓛 := eta_mul_log h𝓛
  have hstep : 2400000 * η * Real.log (|γ₀| + 2) ≤ 2400000 * η * 𝓛 := by
    have : 0 ≤ 2400000 * η := by positivity
    exact mul_le_mul_of_nonneg_left hlog this
  calc (∑ ρ ∈ F, analyticOrderNatAt riemannZeta ρ : ℝ)
      ≤ 13 + 2400000 * η * Real.log (|γ₀| + 2) := hζ
    _ ≤ 13 + 2400000 * η * 𝓛 := by linarith
    _ = 13 + 2400000 * (1 + (1 - σ) * 𝓛) := by rw [mul_assoc, hprod]

/-- **Blueprint Lemma 7.1 (log-free local count), every `χ mod d`.**  For
`σ ∈ [99/100, 1]`, `t ≥ 0`, `𝓛 = log(d(t+2)) ≥ 25`, `|γ₀| ≤ t`: the number of zeros
of `L(·,χ)` with multiplicity in `[σ,1] × [γ₀ − 1/𝓛, γ₀ + 1/𝓛]` is at most
`C_loc·(1 + λ)`, `λ = (1−σ)𝓛`.  No power of `𝓛` appears. -/
theorem localCount_le (χ : DirichletCharacter ℂ d) {σ t γ₀ : ℝ}
    (hσ : 99/100 ≤ σ) (hσ1 : σ ≤ 1) (ht : 0 ≤ t)
    (hL : 25 ≤ Real.log ((d : ℝ) * (t + 2))) (hγ₀ : |γ₀| ≤ t) :
    (localCount χ σ t γ₀ : ℝ) ≤ Cloc * (1 + (1 - σ) * Real.log ((d : ℝ) * (t + 2))) := by
  have hlam : 0 ≤ (1 - σ) * Real.log ((d : ℝ) * (t + 2)) :=
    mul_nonneg (by linarith) (by linarith)
  rw [Cloc_eq]
  by_cases hχ : χ = 1
  · subst hχ
    have h := localCount_le_of_eq_one (d := d) hσ hσ1 ht hL hγ₀
    nlinarith
  · have h := localCount_le_of_ne_one hχ hσ hσ1 ht hL hγ₀
    nlinarith

/-! ### §2 Construction 7.2: cells, representatives, the two parity systems -/

/-- The cell index of a point: `[−t, t]` is cut into half-open intervals
`I_m = [−t + m/𝓛, −t + (m+1)/𝓛)`, `𝓛 = log(d(t+2))`, and `idx ρ = m` iff `Im ρ ∈ I_m`. -/
def idx (d : ℕ) (t : ℝ) (ρ : ℂ) : ℕ := ⌊(ρ.im + t) * Real.log ((d : ℝ) * (t + 2))⌋₊

/-- The number of cells is `Qpar + 1`, `Qpar = ⌊2t𝓛⌋₊`. -/
def Qpar (d : ℕ) (t : ℝ) : ℕ := ⌊2 * t * Real.log ((d : ℝ) * (t + 2))⌋₊

/-- The `good` zeros of `L(·,χ)` in the box `[σ,1] × [−t,t]` whose ordinate lies in
cell `m`. -/
def cell (χ : DirichletCharacter ℂ d) (σ t : ℝ) (good : ℂ → Prop) (m : ℕ) : Finset ℂ :=
  (zeroFinset χ σ t).filter (fun ρ : ℂ => good ρ ∧ idx d t ρ = m)

/-- **The representative** `ρ_{m,χ}`: a chosen good zero of `L(·,χ)` in cell `m`
(junk value `0` when the cell is empty). -/
def rep (χ : DirichletCharacter ℂ d) (σ t : ℝ) (good : ℂ → Prop) (m : ℕ) : ℂ :=
  if h : (cell χ σ t good m).Nonempty then h.choose else 0

/-- **The parity system** `par ∈ {0, 1}`: the index set of pairs `(χ, m)`, `χ ∈ 𝒳`,
`m ≤ Qpar`, `m ≡ par (mod 2)`, whose cell is nonempty.  Its cardinality is
`J_ev` (`par = 0`) resp. `J_od` (`par = 1`); the point attached to `(χ, m)` is
`rep χ σ t good m` (the zero) resp. `repPoint … (χ, m) = rep χ σ t good m − σ`. -/
def repIndex (σ t : ℝ) (𝒳 : Finset (DirichletCharacter ℂ d)) (good : ℂ → Prop)
    (par : ℕ) : Finset (DirichletCharacter ℂ d × ℕ) :=
  (𝒳 ×ˢ Finset.range (Qpar d t + 1)).filter
    (fun p => (cell p.1 σ t good p.2).Nonempty ∧ p.2 % 2 = par)

/-- The shifted point `s_j = ρ_j − σ` of blueprint §7/§8. -/
def repPoint (σ t : ℝ) (good : ℂ → Prop) (p : DirichletCharacter ℂ d × ℕ) : ℂ :=
  rep p.1 σ t good p.2 - σ

lemma mem_cell {χ : DirichletCharacter ℂ d} {σ t : ℝ} {good : ℂ → Prop} {m : ℕ} {ρ : ℂ} :
    ρ ∈ cell χ σ t good m ↔ ρ ∈ zeroFinset χ σ t ∧ good ρ ∧ idx d t ρ = m := by
  rw [cell, Finset.mem_filter]

lemma rep_mem_cell {χ : DirichletCharacter ℂ d} {σ t : ℝ} {good : ℂ → Prop} {m : ℕ}
    (h : (cell χ σ t good m).Nonempty) : rep χ σ t good m ∈ cell χ σ t good m := by
  rw [rep, dif_pos h]
  exact h.choose_spec

lemma mem_repIndex {σ t : ℝ} {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop}
    {par : ℕ} {p : DirichletCharacter ℂ d × ℕ} :
    p ∈ repIndex σ t 𝒳 good par ↔
      p.1 ∈ 𝒳 ∧ p.2 ≤ Qpar d t ∧ (cell p.1 σ t good p.2).Nonempty ∧ p.2 % 2 = par := by
  rw [repIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff]
  tauto

/-- The representative of an index in a parity system lies in its cell. -/
lemma rep_mem_cell_of_mem {σ t : ℝ} {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop}
    {par : ℕ} {p : DirichletCharacter ℂ d × ℕ} (hp : p ∈ repIndex σ t 𝒳 good par) :
    rep p.1 σ t good p.2 ∈ cell p.1 σ t good p.2 :=
  rep_mem_cell (mem_repIndex.mp hp).2.2.1

/-- Every representative is a zero of `L(·, χ)` in the box (blueprint 7.2(c), first
clause): `σ ≤ Re ρ ≤ 1`, `|Im ρ| ≤ t`, `ρ ≠ 1`, `L(ρ,χ) = 0`. -/
lemma rep_mem_zeroFinset {σ t : ℝ} {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop}
    {par : ℕ} {p : DirichletCharacter ℂ d × ℕ} (hp : p ∈ repIndex σ t 𝒳 good par) :
    rep p.1 σ t good p.2 ∈ zeroFinset p.1 σ t :=
  (mem_cell.mp (rep_mem_cell_of_mem hp)).1

/-- Every representative is `good`. -/
lemma good_rep {σ t : ℝ} {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop}
    {par : ℕ} {p : DirichletCharacter ℂ d × ℕ} (hp : p ∈ repIndex σ t 𝒳 good par) :
    good (rep p.1 σ t good p.2) :=
  (mem_cell.mp (rep_mem_cell_of_mem hp)).2.1

/-- Every representative sits in its own cell. -/
lemma idx_rep {σ t : ℝ} {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop}
    {par : ℕ} {p : DirichletCharacter ℂ d × ℕ} (hp : p ∈ repIndex σ t 𝒳 good par) :
    idx d t (rep p.1 σ t good p.2) = p.2 :=
  (mem_cell.mp (rep_mem_cell_of_mem hp)).2.2

lemma repPoint_re {σ t : ℝ} {good : ℂ → Prop} (p : DirichletCharacter ℂ d × ℕ) :
    (repPoint σ t good p).re = (rep p.1 σ t good p.2).re - σ := by
  simp [repPoint]

lemma repPoint_im {σ t : ℝ} {good : ℂ → Prop} (p : DirichletCharacter ℂ d × ℕ) :
    (repPoint σ t good p).im = (rep p.1 σ t good p.2).im := by
  simp [repPoint]

/-- `Re (ρ_j − σ) ≥ 0` at every representative (blueprint 7.2(c), last clause). -/
lemma repPoint_re_nonneg {σ t : ℝ} {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop}
    {par : ℕ} {p : DirichletCharacter ℂ d × ℕ} (hp : p ∈ repIndex σ t 𝒳 good par) :
    0 ≤ (repPoint σ t good p).re := by
  rw [repPoint_re]
  have := (mem_zeroFinset.mp (rep_mem_zeroFinset hp)).1
  linarith

/-! #### Cell arithmetic -/

/-- Floor bounds for the cell index. -/
lemma idx_bounds {t : ℝ} (ht : 0 ≤ t) {ρ : ℂ} (hρ : |ρ.im| ≤ t) :
    ((idx d t ρ : ℕ) : ℝ) ≤ (ρ.im + t) * Real.log ((d : ℝ) * (t + 2))
      ∧ (ρ.im + t) * Real.log ((d : ℝ) * (t + 2)) < (idx d t ρ : ℕ) + 1 := by
  have h𝓛 : 0 < Real.log ((d : ℝ) * (t + 2)) := log_scale_pos (d := d) ht
  have h0 : 0 ≤ (ρ.im + t) * Real.log ((d : ℝ) * (t + 2)) := by
    have := (abs_le.mp hρ).1
    exact mul_nonneg (by linarith) h𝓛.le
  exact ⟨Nat.floor_le h0, Nat.lt_floor_add_one _⟩

/-- Every point of the box has cell index `≤ Qpar`. -/
lemma idx_le_Qpar {t : ℝ} (ht : 0 ≤ t) {ρ : ℂ} (hρ : |ρ.im| ≤ t) :
    idx d t ρ ≤ Qpar d t := by
  have h𝓛 : 0 < Real.log ((d : ℝ) * (t + 2)) := log_scale_pos (d := d) ht
  apply Nat.floor_le_floor
  have := (abs_le.mp hρ).2
  nlinarith

/-- Two points of the box in the same cell have ordinates within `Δ = 1/𝓛`. -/
lemma abs_im_sub_lt_of_idx_eq {t : ℝ} (ht : 0 ≤ t) {ρ ρ' : ℂ}
    (hρ : |ρ.im| ≤ t) (hρ' : |ρ'.im| ≤ t) (h : idx d t ρ = idx d t ρ') :
    |ρ.im - ρ'.im| < 1 / Real.log ((d : ℝ) * (t + 2)) := by
  have h𝓛 : 0 < Real.log ((d : ℝ) * (t + 2)) := log_scale_pos (d := d) ht
  obtain ⟨h1, h2⟩ := idx_bounds (d := d) ht hρ
  obtain ⟨h3, h4⟩ := idx_bounds (d := d) ht hρ'
  rw [h] at h1 h2
  rw [abs_lt]
  constructor
  · rw [neg_lt, lt_div_iff₀ h𝓛]
    linarith
  · rw [lt_div_iff₀ h𝓛]
    linarith

/-- Two points of the box in cells `m, m'` with `m + 2 ≤ m'` have ordinates at least
`Δ` apart (in fact `Im ρ' − Im ρ > Δ`). -/
lemma delta_lt_im_sub_of_idx_add_two_le {t : ℝ} (ht : 0 ≤ t) {ρ ρ' : ℂ}
    (hρ : |ρ.im| ≤ t) (hρ' : |ρ'.im| ≤ t) (h : idx d t ρ + 2 ≤ idx d t ρ') :
    1 / Real.log ((d : ℝ) * (t + 2)) < ρ'.im - ρ.im := by
  have h𝓛 : 0 < Real.log ((d : ℝ) * (t + 2)) := log_scale_pos (d := d) ht
  obtain ⟨h1, h2⟩ := idx_bounds (d := d) ht hρ
  obtain ⟨h3, h4⟩ := idx_bounds (d := d) ht hρ'
  have hcast : ((idx d t ρ : ℕ) : ℝ) + 2 ≤ ((idx d t ρ' : ℕ) : ℝ) := by exact_mod_cast h
  rw [div_lt_iff₀ h𝓛]
  linarith

/-! ### §3 Property (b): spacing within one parity system -/

/-- `|Im ρ| ≤ t` at every representative. -/
lemma abs_im_rep_le {σ t : ℝ} {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop}
    {par : ℕ} {p : DirichletCharacter ℂ d × ℕ} (hp : p ∈ repIndex σ t 𝒳 good par) :
    |(rep p.1 σ t good p.2).im| ≤ t :=
  (mem_zeroFinset.mp (rep_mem_zeroFinset hp)).2.2.1

/-- **Blueprint 7.2(b), first clause.**  Two distinct indices of one parity system
carrying the same character have ordinates at least `Δ = 1/𝓛` apart. -/
theorem rep_spacing {σ t : ℝ} (ht : 0 ≤ t) {𝒳 : Finset (DirichletCharacter ℂ d)}
    {good : ℂ → Prop} {par : ℕ} {p q : DirichletCharacter ℂ d × ℕ}
    (hp : p ∈ repIndex σ t 𝒳 good par) (hq : q ∈ repIndex σ t 𝒳 good par)
    (hχ : p.1 = q.1) (hne : p ≠ q) :
    1 / Real.log ((d : ℝ) * (t + 2))
      ≤ |(rep p.1 σ t good p.2).im - (rep q.1 σ t good q.2).im| := by
  have hp' := mem_repIndex.mp hp
  have hq' := mem_repIndex.mp hq
  have hm : p.2 ≠ q.2 := fun h => hne (Prod.ext hχ h)
  have hpar : p.2 % 2 = q.2 % 2 := by rw [hp'.2.2.2, hq'.2.2.2]
  have hρp := abs_im_rep_le hp
  have hρq := abs_im_rep_le hq
  have hip := idx_rep hp
  have hiq := idx_rep hq
  rcases lt_or_gt_of_ne hm with h | h
  · have h2 : idx d t (rep p.1 σ t good p.2) + 2 ≤ idx d t (rep q.1 σ t good q.2) := by
      rw [hip, hiq]; omega
    have h3 := delta_lt_im_sub_of_idx_add_two_le (d := d) ht hρp hρq h2
    rw [abs_sub_comm]
    exact le_trans h3.le (le_abs_self _)
  · have h2 : idx d t (rep q.1 σ t good q.2) + 2 ≤ idx d t (rep p.1 σ t good p.2) := by
      rw [hip, hiq]; omega
    have h3 := delta_lt_im_sub_of_idx_add_two_le (d := d) ht hρq hρp h2
    exact le_trans h3.le (le_abs_self _)

/-- **Blueprint 7.2(b), second clause (the hypothesis of Lemma 6.4).**  For a fixed
index `p` of a parity system and every `m : ℕ`, at most two indices `q` of the same
system with the same character have `|Im ρ_q − Im ρ_p| ∈ [mΔ, (m+1)Δ)`. -/
theorem rep_band_card_le {σ t : ℝ} (ht : 0 ≤ t) {𝒳 : Finset (DirichletCharacter ℂ d)}
    {good : ℂ → Prop} {par : ℕ} {p : DirichletCharacter ℂ d × ℕ}
    (hp : p ∈ repIndex σ t 𝒳 good par) (m : ℕ) :
    ((repIndex σ t 𝒳 good par).filter (fun q => q.1 = p.1 ∧
        (m : ℝ) * (1 / Real.log ((d : ℝ) * (t + 2)))
          ≤ |(rep q.1 σ t good q.2).im - (rep p.1 σ t good p.2).im| ∧
        |(rep q.1 σ t good q.2).im - (rep p.1 σ t good p.2).im|
          < ((m : ℝ) + 1) * (1 / Real.log ((d : ℝ) * (t + 2))))).card ≤ 2 := by
  have h𝓛 : 0 < Real.log ((d : ℝ) * (t + 2)) := log_scale_pos (d := d) ht
  have hp' := mem_repIndex.mp hp
  have hρp := abs_im_rep_le hp
  obtain ⟨b1, b2⟩ := idx_bounds (d := d) ht hρp
  rw [idx_rep hp] at b1 b2
  -- every member of the band is one of two explicit indices
  have key : ∀ q ∈ (repIndex σ t 𝒳 good par).filter (fun q => q.1 = p.1 ∧
        (m : ℝ) * (1 / Real.log ((d : ℝ) * (t + 2)))
          ≤ |(rep q.1 σ t good q.2).im - (rep p.1 σ t good p.2).im| ∧
        |(rep q.1 σ t good q.2).im - (rep p.1 σ t good p.2).im|
          < ((m : ℝ) + 1) * (1 / Real.log ((d : ℝ) * (t + 2)))),
      q = (p.1, p.2 + (m + m % 2)) ∨ q = (p.1, p.2 - (m + m % 2)) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    obtain ⟨hqI, hχ, hlo, hhi⟩ := hq
    have hq' := mem_repIndex.mp hqI
    have hρq := abs_im_rep_le hqI
    obtain ⟨a1, a2⟩ := idx_bounds (d := d) ht hρq
    rw [idx_rep hqI] at a1 a2
    have hpar : q.2 % 2 = p.2 % 2 := by rw [hq'.2.2.2, hp'.2.2.2]
    have hcancel : 1 / Real.log ((d : ℝ) * (t + 2)) * Real.log ((d : ℝ) * (t + 2)) = 1 :=
      one_div_mul_cancel h𝓛.ne'
    have e1 : (m : ℝ) ≤ |(rep q.1 σ t good q.2).im - (rep p.1 σ t good p.2).im|
        * Real.log ((d : ℝ) * (t + 2)) := by
      have := mul_le_mul_of_nonneg_right hlo h𝓛.le
      rwa [mul_assoc, hcancel, mul_one] at this
    have e2 : |(rep q.1 σ t good q.2).im - (rep p.1 σ t good p.2).im|
        * Real.log ((d : ℝ) * (t + 2)) < (m : ℝ) + 1 := by
      have := mul_lt_mul_of_pos_right hhi h𝓛
      rwa [mul_assoc, hcancel, mul_one] at this
    rcases le_or_gt 0 ((rep q.1 σ t good q.2).im - (rep p.1 σ t good p.2).im) with hd | hd
    · rw [abs_of_nonneg hd] at e1 e2
      have i1 : ((q.2 : ℤ) : ℝ) - ((p.2 : ℤ) : ℝ) < ((m : ℤ) : ℝ) + 2 := by
        push_cast; linarith
      have i2 : ((m : ℤ) : ℝ) - 1 < ((q.2 : ℤ) : ℝ) - ((p.2 : ℤ) : ℝ) := by
        push_cast; linarith
      have i1' : (q.2 : ℤ) - (p.2 : ℤ) < (m : ℤ) + 2 := by exact_mod_cast i1
      have i2' : (m : ℤ) - 1 < (q.2 : ℤ) - (p.2 : ℤ) := by exact_mod_cast i2
      left
      refine Prod.ext hχ ?_
      show q.2 = p.2 + (m + m % 2)
      omega
    · rw [abs_of_neg hd] at e1 e2
      have i1 : ((p.2 : ℤ) : ℝ) - ((q.2 : ℤ) : ℝ) < ((m : ℤ) : ℝ) + 2 := by
        push_cast; linarith
      have i2 : ((m : ℤ) : ℝ) - 1 < ((p.2 : ℤ) : ℝ) - ((q.2 : ℤ) : ℝ) := by
        push_cast; linarith
      have i1' : (p.2 : ℤ) - (q.2 : ℤ) < (m : ℤ) + 2 := by exact_mod_cast i1
      have i2' : (m : ℤ) - 1 < (p.2 : ℤ) - (q.2 : ℤ) := by exact_mod_cast i2
      right
      refine Prod.ext hχ ?_
      show q.2 = p.2 - (m + m % 2)
      omega
  have hsub : (repIndex σ t 𝒳 good par).filter (fun q => q.1 = p.1 ∧
        (m : ℝ) * (1 / Real.log ((d : ℝ) * (t + 2)))
          ≤ |(rep q.1 σ t good q.2).im - (rep p.1 σ t good p.2).im| ∧
        |(rep q.1 σ t good q.2).im - (rep p.1 σ t good p.2).im|
          < ((m : ℝ) + 1) * (1 / Real.log ((d : ℝ) * (t + 2))))
      ⊆ ({(p.1, p.2 + (m + m % 2)), (p.1, p.2 - (m + m % 2))} :
          Finset (DirichletCharacter ℂ d × ℕ)) := by
    intro q hq
    rw [Finset.mem_insert, Finset.mem_singleton]
    exact key q hq
  exact le_trans (Finset.card_le_card hsub) Finset.card_le_two

/-! ### §4 Property (a): covering -/

/-- **Blueprint 7.2(a), abstract form.**  If every local count at height `|γ₀| ≤ t`
is `≤ B` for the characters of `𝒳`, then the total good zero mass over `𝒳` is
`≤ B·(J_ev + J_od)`. -/
theorem sum_good_le_of_localCount {σ t : ℝ} (ht : 0 ≤ t)
    {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop} {B : ℝ}
    (hloc : ∀ χ ∈ 𝒳, ∀ γ₀ : ℝ, |γ₀| ≤ t → (localCount χ σ t γ₀ : ℝ) ≤ B) :
    ((∑ χ ∈ 𝒳, ∑ ρ ∈ (zeroFinset χ σ t).filter good,
        analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ)
      ≤ B * (((repIndex σ t 𝒳 good 0).card : ℝ) + (repIndex σ t 𝒳 good 1).card) := by
  set Q := Qpar d t with hQdef
  set S : DirichletCharacter ℂ d × ℕ → ℝ := fun p =>
    ∑ ρ ∈ cell p.1 σ t good p.2,
      (analyticOrderNatAt (DirichletCharacter.LFunction p.1) ρ : ℝ) with hSdef
  -- fiberwise decomposition of each character's good zero mass by cell index
  have hfib : ∀ χ ∈ 𝒳, (∑ ρ ∈ (zeroFinset χ σ t).filter good,
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))
        = ∑ m ∈ Finset.range (Q + 1), S (χ, m) := by
    intro χ _
    rw [← Finset.sum_fiberwise_of_maps_to (g := idx d t) (t := Finset.range (Q + 1)) ?_]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      simp only [hSdef, cell, Finset.filter_filter]
    · intro ρ hρ
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact idx_le_Qpar (d := d) ht (mem_zeroFinset.mp (Finset.mem_filter.mp hρ).1).2.2.1
  -- the filtered index set
  set T := (𝒳 ×ˢ Finset.range (Q + 1)).filter
    (fun p => (cell p.1 σ t good p.2).Nonempty) with hTdef
  have hS_zero : ∀ p ∈ 𝒳 ×ˢ Finset.range (Q + 1), S p ≠ 0 →
      (cell p.1 σ t good p.2).Nonempty := by
    intro p _ hS
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    apply hS
    simp only [hSdef, hcon, Finset.sum_empty]
  have hS_le : ∀ p ∈ T, S p ≤ B := by
    intro p hp
    rw [hTdef, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hχ, _⟩, hne⟩ := hp
    have hrep := rep_mem_cell hne
    rw [mem_cell] at hrep
    obtain ⟨hrepZ, _, hrepidx⟩ := hrep
    have hrepim := (mem_zeroFinset.mp hrepZ).2.2.1
    have hsub : cell p.1 σ t good p.2 ⊆ (zeroFinset p.1 σ t).filter
        (fun ρ : ℂ => |ρ.im - (rep p.1 σ t good p.2).im|
          ≤ 1 / Real.log ((d : ℝ) * (t + 2))) := by
      intro ρ hρ
      rw [mem_cell] at hρ
      obtain ⟨hρZ, _, hρidx⟩ := hρ
      rw [Finset.mem_filter]
      refine ⟨hρZ, le_of_lt ?_⟩
      exact abs_im_sub_lt_of_idx_eq (d := d) ht (mem_zeroFinset.mp hρZ).2.2.1 hrepim
        (by rw [hρidx, hrepidx])
    calc S p ≤ (localCount p.1 σ t (rep p.1 σ t good p.2).im : ℝ) := by
          simp only [hSdef, localCount]
          push_cast
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
      _ ≤ B := hloc p.1 hχ _ hrepim
  -- the parity split of the index set
  have hsplit : T.card = (repIndex σ t 𝒳 good 0).card + (repIndex σ t 𝒳 good 1).card := by
    rw [← Finset.card_filter_add_card_filter_not (s := T) (p := fun p => p.2 % 2 = 0)]
    congr 1
    · rw [hTdef, repIndex, Finset.filter_filter]
    · rw [hTdef, repIndex, Finset.filter_filter]
      congr 1
      ext q
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h0, h1, h2⟩; exact ⟨h0, h1, by omega⟩
      · rintro ⟨h0, h1, h2⟩; exact ⟨h0, h1, by omega⟩
  calc ((∑ χ ∈ 𝒳, ∑ ρ ∈ (zeroFinset χ σ t).filter good,
        analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ)
      = ∑ χ ∈ 𝒳, ∑ m ∈ Finset.range (Q + 1), S (χ, m) := by
        push_cast
        exact Finset.sum_congr rfl hfib
    _ = ∑ p ∈ 𝒳 ×ˢ Finset.range (Q + 1), S p := (Finset.sum_product _ _ _).symm
    _ = ∑ p ∈ T, S p := (Finset.sum_filter_of_ne hS_zero).symm
    _ ≤ T.card • B := Finset.sum_le_card_nsmul _ _ _ hS_le
    _ = B * (((repIndex σ t 𝒳 good 0).card : ℝ) + (repIndex σ t 𝒳 good 1).card) := by
        rw [nsmul_eq_mul, hsplit]
        push_cast
        ring

/-! ### §5 Property (c): detection at every representative -/

open Detector in
/-- The final triangle-inequality assembly of `Detector.detector_lower_bound_of_P1`,
with the conclusion kept in terms of `P(1)`: `‖F(ρ,χ)‖ ≥ P(1)/2` at every point where
the detection estimate (blueprint Lemmas 4.1 + 4.2) holds and the pole term is
controlled (Lemma 4.3 for `χ₀`, via the `Λ₀` clause). -/
theorem norm_Fdet_ge_half_P1 {N : ℕ} [NeZero N] {D σ : ℝ} (hD1 : 1 < D)
    (hL : 200 ≤ Real.log D) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    {χ : DirichletCharacter ℂ N} {ρ : ℂ} (hβ : σ ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hγ : χ = 1 → Lambda0 D σ (Real.log (3200 * Real.exp 1 * 60)) ≤ |ρ.im|)
    (hdet : DetectionEstimate χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ) :
    P1 N (Rpar D) / 2 ≤ ‖Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖ := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hP0 : 0 ≤ P1 N (Rpar D) := P1_nonneg N (Rpar D)
  have hEp : ‖Epole χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖
      ≤ P1 N (Rpar D) / 8 := by
    by_cases h1 : χ = 1
    · subst h1
      exact norm_Epole_le' hD1 hL hσ1 hσ0 (by norm_num)
        (fun z hz0 hz1 hz2 => norm_Gamma_le_exp_neg_im z hz0 hz1 hz2) hβ hβ1 (hγ rfl)
    · rw [Epole_eq_zero h1, norm_zero]
      linarith only [hP0]
  have hdet' : ‖Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ
      + ((Real.exp (-1 / Xpar D) * P1 N (Rpar D) : ℝ) : ℂ)
      - Epole χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖
      ≤ P1 N (Rpar D) / 8 := hdet
  have hX4 : (4 : ℝ) ≤ Xpar D := by
    have hD4 : (4 : ℝ) ≤ D := by
      have h1 : Real.exp 200 ≤ Real.exp (Real.log D) := Real.exp_le_exp.mpr hL
      rw [Real.exp_log hD0] at h1
      have h2 : (201 : ℝ) ≤ Real.exp 200 := by
        have := Real.add_one_le_exp (200 : ℝ)
        linarith
      linarith
    calc (4 : ℝ) ≤ D := hD4
      _ = D ^ (1 : ℝ) := (Real.rpow_one D).symm
      _ ≤ D ^ (6/5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by norm_num)
  have hexp : (3/4 : ℝ) ≤ Real.exp (-1 / Xpar D) := by
    have h1 : -1 / Xpar D + 1 ≤ Real.exp (-1 / Xpar D) := Real.add_one_le_exp _
    have h2 : 1 / Xpar D ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hX4
    have h3 : -1 / Xpar D = -(1 / Xpar D) := by ring
    linarith
  have hc : ‖((Real.exp (-1 / Xpar D) * P1 N (Rpar D) : ℝ) : ℂ)‖
      = Real.exp (-1 / Xpar D) * P1 N (Rpar D) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg (Real.exp_pos _).le hP0
  set F := Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ with hFdef
  set E := Epole χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ with hEdef
  set c := ((Real.exp (-1 / Xpar D) * P1 N (Rpar D) : ℝ) : ℂ) with hcdef
  have htri : ‖c‖ ≤ ‖F + c - E‖ + ‖F‖ + ‖E‖ := by
    calc ‖c‖ = ‖((F + c - E) - F) + E‖ := by
          rw [show ((F + c - E) - F) + E = c from by ring]
      _ ≤ ‖(F + c - E) - F‖ + ‖E‖ := norm_add_le _ _
      _ ≤ (‖F + c - E‖ + ‖F‖) + ‖E‖ := add_le_add (norm_sub_le _ _) le_rfl
  have h34 : (3/4 : ℝ) * P1 N (Rpar D)
      ≤ Real.exp (-1 / Xpar D) * P1 N (Rpar D) :=
    mul_le_mul_of_nonneg_right hexp hP0
  linarith only [htri, hc, h34, hdet', hEp]

open Detector DetectionShift in
/-- **Blueprint 7.2(c), `Q_R` form (the form §8.3 consumes).**  At every index `p`
of a parity system, with `D = d(t+2)`, `σ ∈ [99/100, 1]`, `200 ≤ log D`, (T1)
`2·10¹⁴·C_τ·log D ≤ D^{79/4000}`, and the `χ₀` height clause
`Λ₀(σ) ≤ |Im ρ_p|` (only when `p.1 = χ₀`; supplied by `good` in §9):
`(1/400)·Q_R·log D ≤ ‖F(ρ_p, χ_p)‖`. -/
theorem rep_detect_QR {σ t : ℝ} (hσ : 99/100 ≤ σ) (hσ1 : σ ≤ 1) (ht : 0 ≤ t)
    (hLD : 200 ≤ Real.log ((d : ℝ) * (t + 2)))
    (hT1 : 2 * 10 ^ 14 * Ctau * Real.log ((d : ℝ) * (t + 2))
      ≤ ((d : ℝ) * (t + 2)) ^ (79/4000 : ℝ))
    {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop} {par : ℕ}
    {p : DirichletCharacter ℂ d × ℕ} (hp : p ∈ repIndex σ t 𝒳 good par)
    (hγ : p.1 = 1 → Lambda0 ((d : ℝ) * (t + 2)) σ (Real.log (3200 * Real.exp 1 * 60))
      ≤ |(rep p.1 σ t good p.2).im|) :
    (1/400) * QR d (Rpar ((d : ℝ) * (t + 2))) * Real.log ((d : ℝ) * (t + 2))
      ≤ ‖Fdet p.1 (z1par ((d : ℝ) * (t + 2))) (z2par ((d : ℝ) * (t + 2)))
          (Rpar ((d : ℝ) * (t + 2))) (Xpar ((d : ℝ) * (t + 2))) (rep p.1 σ t good p.2)‖ := by
  have hD1 : (1 : ℝ) < (d : ℝ) * (t + 2) := by linarith [two_le_scale (d := d) ht]
  have hD0 : (0 : ℝ) < (d : ℝ) * (t + 2) := by linarith
  obtain ⟨hβ, hβ1, him, hne1, hLρ⟩ := mem_zeroFinset.mp (rep_mem_zeroFinset hp)
  have hDN : (d : ℝ) * (|(rep p.1 σ t good p.2).im| + 2) ≤ (d : ℝ) * (t + 2) := by
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    exact mul_le_mul_of_nonneg_left (by linarith) hd
  have hdet := detection_estimate_all p.1 hD1 hLD (le_trans hσ hβ) hβ1 hDN hT1
    (fun _ => hne1) hLρ
  have hhalf := norm_Fdet_ge_half_P1 hD1 hLD (by linarith) hσ1 hβ hβ1 hγ hdet
  have hP1 := P1_lower_QR d hD0
  linarith

open Detector DetectionShift in
/-- **Blueprint 7.2(c), `φ(d)/d` form** (the frozen Z6c display), a corollary of
the `Q_R` form via `φ(d)/d ≤ Q_R`. -/
theorem rep_detect {σ t : ℝ} (hσ : 99/100 ≤ σ) (hσ1 : σ ≤ 1) (ht : 0 ≤ t)
    (hLD : 200 ≤ Real.log ((d : ℝ) * (t + 2)))
    (hT1 : 2 * 10 ^ 14 * Ctau * Real.log ((d : ℝ) * (t + 2))
      ≤ ((d : ℝ) * (t + 2)) ^ (79/4000 : ℝ))
    {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop} {par : ℕ}
    {p : DirichletCharacter ℂ d × ℕ} (hp : p ∈ repIndex σ t 𝒳 good par)
    (hγ : p.1 = 1 → Lambda0 ((d : ℝ) * (t + 2)) σ (Real.log (3200 * Real.exp 1 * 60))
      ≤ |(rep p.1 σ t good p.2).im|) :
    (1/400) * ((d.totient : ℝ) / d) * Real.log ((d : ℝ) * (t + 2))
      ≤ ‖Fdet p.1 (z1par ((d : ℝ) * (t + 2))) (z2par ((d : ℝ) * (t + 2)))
          (Rpar ((d : ℝ) * (t + 2))) (Xpar ((d : ℝ) * (t + 2))) (rep p.1 σ t good p.2)‖ := by
  have h := rep_detect_QR hσ hσ1 ht hLD hT1 hp hγ
  have hQ := totient_div_le_QR d (NeZero.ne d) (Rpar ((d : ℝ) * (t + 2)))
  have hlog : 0 ≤ Real.log ((d : ℝ) * (t + 2)) := by linarith
  have : (1/400) * ((d.totient : ℝ) / d) * Real.log ((d : ℝ) * (t + 2))
      ≤ (1/400) * QR d (Rpar ((d : ℝ) * (t + 2))) * Real.log ((d : ℝ) * (t + 2)) := by
    apply mul_le_mul_of_nonneg_right _ hlog
    exact mul_le_mul_of_nonneg_left hQ (by norm_num)
  linarith

open Detector DetectionShift in
/-- **Blueprint 7.2(c), `Q_R` form, height clause supplied by `good`** (the §9
band-(c) instance: `good ρ := Λ₀(σ) ≤ |Im ρ|`; for `𝒳 ∌ χ₀` the clause is vacuous). -/
theorem rep_detect_QR_of_good {σ t : ℝ} (hσ : 99/100 ≤ σ) (hσ1 : σ ≤ 1) (ht : 0 ≤ t)
    (hLD : 200 ≤ Real.log ((d : ℝ) * (t + 2)))
    (hT1 : 2 * 10 ^ 14 * Ctau * Real.log ((d : ℝ) * (t + 2))
      ≤ ((d : ℝ) * (t + 2)) ^ (79/4000 : ℝ))
    {𝒳 : Finset (DirichletCharacter ℂ d)} {good : ℂ → Prop}
    (hgood : ∀ χ ∈ 𝒳, χ = 1 → ∀ ρ : ℂ, good ρ →
      Lambda0 ((d : ℝ) * (t + 2)) σ (Real.log (3200 * Real.exp 1 * 60)) ≤ |ρ.im|)
    {par : ℕ} {p : DirichletCharacter ℂ d × ℕ} (hp : p ∈ repIndex σ t 𝒳 good par) :
    (1/400) * QR d (Rpar ((d : ℝ) * (t + 2))) * Real.log ((d : ℝ) * (t + 2))
      ≤ ‖Fdet p.1 (z1par ((d : ℝ) * (t + 2))) (z2par ((d : ℝ) * (t + 2)))
          (Rpar ((d : ℝ) * (t + 2))) (Xpar ((d : ℝ) * (t + 2))) (rep p.1 σ t good p.2)‖ :=
  rep_detect_QR hσ hσ1 ht hLD hT1 hp
    (fun h1 => hgood p.1 (mem_repIndex.mp hp).1 h1 _ (good_rep hp))

/-! ### §6 Property (a) with Lemma 7.1 inserted -/

/-- **Blueprint 7.2(a) + Lemma 7.1, general `good`.**  For `σ ∈ [99/100, 1]`, `t ≥ 0`,
`𝓛 = log(d(t+2)) ≥ 25`: the good zero mass over `𝒳` is
`≤ C_loc·(1+λ)·(J_ev + J_od)`. -/
theorem sum_good_le {σ t : ℝ} (hσ : 99/100 ≤ σ) (hσ1 : σ ≤ 1) (ht : 0 ≤ t)
    (hL : 25 ≤ Real.log ((d : ℝ) * (t + 2)))
    (𝒳 : Finset (DirichletCharacter ℂ d)) (good : ℂ → Prop) :
    ((∑ χ ∈ 𝒳, ∑ ρ ∈ (zeroFinset χ σ t).filter good,
        analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ)
      ≤ Cloc * (1 + (1 - σ) * Real.log ((d : ℝ) * (t + 2)))
        * (((repIndex σ t 𝒳 good 0).card : ℝ) + (repIndex σ t 𝒳 good 1).card) :=
  sum_good_le_of_localCount ht (fun χ _ _ hγ₀ => localCount_le χ hσ hσ1 ht hL hγ₀)

/-- **Blueprint 7.2(a) + Lemma 7.1 for the full box count** (Theorem M's instance,
`good := True`): `∑_{χ ∈ 𝒳} N(σ,t,χ) ≤ C_loc·(1+λ)·(J_ev + J_od)`. -/
theorem sum_zeroCountBox_le {σ t : ℝ} (hσ : 99/100 ≤ σ) (hσ1 : σ ≤ 1) (ht : 0 ≤ t)
    (hL : 25 ≤ Real.log ((d : ℝ) * (t + 2)))
    (𝒳 : Finset (DirichletCharacter ℂ d)) :
    ((∑ χ ∈ 𝒳, zeroCountBox χ σ t : ℕ) : ℝ)
      ≤ Cloc * (1 + (1 - σ) * Real.log ((d : ℝ) * (t + 2)))
        * (((repIndex σ t 𝒳 (fun _ => True) 0).card : ℝ)
          + (repIndex σ t 𝒳 (fun _ => True) 1).card) := by
  have h := sum_good_le hσ hσ1 ht hL 𝒳 (fun _ => True)
  simp only [Finset.filter_true] at h
  exact h

end

end Representatives
end Carmichael
