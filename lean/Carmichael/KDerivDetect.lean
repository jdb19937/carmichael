/-
Route Z, TZ-LITE File 4: the `k`-th logarithmic-derivative zero detector.

STATUS: **DELIVERED.**  The frozen main statement `kderiv_detection` (§4.2)
is proved, sorry-free and axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`), on top of the five §4.1 definitions at the ADJUDICATED
numerals: cut radius `6η`, `Ndet = ⌈6 + 28800000·η·L⌉₊`, `Mdet = 6·Ndet`,
window dials `1/16` and `16`.  Verified with plain `lake env lean`.

DELIVERED.

§4.1 frozen definitions, byte-identical to the spec modulo one elaboration
annotation (see DELTAS):

* `Ndet`, `Mdet`, `Xone`, `Xtwo`, `primeWindowSum`, with their elementary
  arithmetic (`six_le_Ndet`, `Ndet_pos`, `le_Ndet_cast`, `Ndet_cast_lt`,
  `Mdet_eq`, `Mdet_pos`, `Xone_pos`, `Xtwo_pos`, `Xone_lt_Xtwo`).

§4.2 frozen main statement:

* `kderiv_detection` — byte-identical to the spec.  Proof map (§4.4):
  step 2 `exists_turan_index` → step 3 `norm_LSeries_ge_of_turan` →
  step 4 `norm_LSeries_sub_window_le` + `abel_window` → step 5
  `integral_normSq_div_ge` → the numeric budgets `budget_*`.

The analytic remainder (§4.6 removable-singularity hazard, discharged):

* `exists_logDeriv_remainder` — `g = L′/L − ∑_ρ m_ρ/(·−ρ)` realized as
  `logDeriv h` for the Landau factorization `L = P·h`, hence ANALYTIC on the
  open `13/8`-disk by construction; bounded by `520000·log(q(|τ|+2))` on the
  open `3/2`-disk, the bound being extended from the non-vanishing points to
  the zeros by continuity along `𝓝[≠]`.
* `norm_iteratedDeriv_le_of_bounded_on_disk` — the Cauchy estimate
  `‖g^{(k)}(s₀)‖ ≤ k!·C·2^k` for `dist s₀ (2+iτ) < 1`, i.e. radius `1/2`.
* `iteratedDeriv_sub_inv` — `d^k/dz^k (z−ρ)⁻¹ = (−1)^k k!/(z−ρ)^{k+1}`.

§4.4 step 1, the representation:

* `logMul_iterate`, `abscissa_twist_vonMangoldt_le`, `logDeriv_LFunction_eq`,
  `iteratedDeriv_zeroSum` — the four inputs, then
* `kderiv_representation` —
  `∑_ρ m_ρ/(s₀−ρ)^{k+1} = −(LSeries(log^k·χ·Λ)(s₀) + (−1)^k g^{(k)}(s₀))/k!`
  at every `s₀` of the Landau disk with `Re s₀ > 1`.

§4.4 step 2, the Turán event:

* `sum_range_getD`, `sum_multiset_bind`, `turan_family_power_sum` —
  Turán's max-normalized theorem (`Turan.turan_power_sum_max_lb`) over a
  multiplicity-weighted family with a designated nearest point.
* `mem_zeroDiskFinset_of_near`, `re_lt_one_of_mem_zeroDiskFinset`,
  `exists_turan_index` — the `6η`-family around `1+iτ` (mass `≤ Nz`, the
  hypothesis zero inside, order `≥ 1` via
  `PartialFractions.one_le_ord_of_mem_zeroDiskFinset`, nearest zero by
  `Finset.exists_min_image`) has some `k ∈ [M₀+1, M₀+Nz]` with
  `‖∑ m_ρ/(s₀−ρ)^k‖ ≥ (Nz/(8e(M₀+Nz)))^{Nz}·(2η)^{−k}`.

§4.4 step 3, the far-zero estimates (TZ (4.1)'s `ℓ²` form):

* `div_normSq_le_re_div`, `sum_ord_div_normSq_le` —
  `∑_ρ m_ρ/‖s₀−ρ‖² ≤ (1/η)·(1/η + 2 + 520000·log(q(|τ|+2)))` at
  `s₀ = (1+η)+iτ`.
* `norm_sum_far_le` — the zeros at distance `> r` from `s₀` contribute at most
  `A/r^j` to the order-`(j+2)` pole sum, `A` any bound for the `ℓ²` sum.
* `dist_one_le_norm_sub` — the annulus comparison
  `Re ρ < 1 → dist(ρ, 1+iτ) ≤ ‖s₀ − ρ‖`.
* `norm_LSeries_ge_of_turan` — Turán floor `Q` on the `6η`-family, far
  remainder `≤ Q/8`, Cauchy remainder `≤ Q/8` give
  `‖LSeries(log^{j+1}·χ·Λ)(s₀)‖ ≥ (j+1)!·(3/4)Q`.

§4.6, the general-`k` diagonal bounds:

* `pow_le_factorial_mul_exp` (`x^k ≤ k!e^x`), `log_pow_le_rpow`
  (`(log n)^k ≤ k!·n^v/v^k`), `summable_vonMangoldt_log_pow_rpow`,
* `tsum_vonMangoldt_log_pow_rpow_le` — parametrized:
  `∑ Λ(n)(log n)^k n^{−(1+v+w)} ≤ (k!/v^k)(1/w + 2)`,
* `tsum_vonMangoldt_log_pow_rpow_le'` — sharp:
  `∑ Λ(n)(log n)^k n^{−(1+u)} ≤ k!·e·(k+2)/u^{k+1}` for `0 < u ≤ 1/20`.

Bridging the two sides:

* `norm_term_log_pow_twist_le`, `norm_LSeries_log_pow_le` — the Dirichlet side
  of `kderiv_representation` is bounded by the diagonal sum on `Re s = 1+η`.
* `sum_ord_near_s0_le` — File 3's mass bound transported from disks around
  `1+iτ` to disks around `s₀ = (1+η)+iτ`.

§4.4 step 4, the prime-sum conversion:

* `tsum_nonprime_vonMangoldt_rpow_le` — `∑_{n not prime} Λ(n)n^{−3/4} ≤ 150`,
  by injecting the non-prime support of `Λ` into `ℕ × ℕ` through
  `n ↦ (minFac n, ord_{minFac n} n)` (escape `(0, n)` off the prime powers)
  and the separated majorant `Λ(p)p^{−3/2}·(9/4)(2/3)^a`.
* `tsum_nonprime_log_pow_le` (T1), `tsum_low_log_pow_le` (T2),
  `tsum_high_log_pow_le` (T3) — the three tails of the diagonal
  `Λ(n)(log n)^m n^{−(1+η)}`: prime powers, `n ≤ ⌊X₁⌋₊`, `n > ⌊X₂⌋₊`.
* `norm_LSeries_sub_window_le` — the Dirichlet series minus the weighted
  window sum is at most `T1 + T2 + T3`.
* `sum_Icc_eq_primeWindowSum`, `continuousOn_detKernel`, `abel_window` —
  Abel summation (Mathlib `sum_mul_eq_sub_sub_integral_mul`) with weight
  `φ(t) = (log t)^{j+1}t^{−η}` and kernel `detKernel η j`; the boundary term
  at `X₁` vanishes (`primeWindowSum_eq_zero_of_le`).
* `measurable_primeWindowSum`, `norm_primeWindowSum_le` — the window sum is
  measurable in `u` (a function of `⌊u⌋₊`) and bounded by `e·(log X₂ + 2)`
  below `X₂ ≥ e²⁰`.

§4.4 step 5, the endgame:

* `detKernel`, `hasDerivAt_detWeight`, `abs_detKernel_mul_le` — the kernel
  `ψ(u) = u^{−1−η}(log u)^j((j+1) − η log u)` is `φ′` and satisfies
  `u·|ψ(u)| ≤ 17(j+1)·j!/η^j` on the window.
* `integral_normSq_div_ge` — from `G·C₇ ≤ ‖∫ ψ·S‖`, `u|ψ| ≤ C₇`, `S`
  bounded measurable, pointwise AM–GM at scale `λ = K/G` gives
  `∫ ‖S‖²/u ≥ G²/K` (no Hölder, no Gamma function).

Numeric budgets (each uniform in `k ∈ [6N+1, 7N]`, no `norm_num` on
`k`- or `N`-dependent numerals; `T = 56e ∈ (152, 153)`):

* `nat_le_two_pow`, `nat_mul_pow_le_pow`, `turan_const_bounds`,
  `turan_floor_eq`, `factorial_ge_div_exp_pow` — the shared tools.
* `budget_far` (`3^j ≥ 2N·T^N` from `729 ≥ 4T`, `4^N ≥ 6N`),
  `budget_cauchy` (`(4η)^{j+1} ≤ 1250^{−6N}`),
  `budget_primepow` (`(8η)^{j+1} ≤ 625^{−6N}`),
  `budget_low` (`(8/e)^6 ≥ 2T` against the Stirling floor),
  `budget_high` (`e^{48} ≥ 2·16384·T·64e`),
  `budget_boundary` (`e^{96} ≥ 2·(32e)^7·T·1584e`),
  `budget_endgame` (`e^{36} ≥ 2·T²·16384`, `N ≥ 73984`).
* `ne_one_of_isPrimitive` — primitive characters mod `q ≥ 2` are nontrivial.

DELTAS VS. THE SPEC.

1. `primeWindowSum` carries the binder annotation `fun p : ℕ =>` in its
   `Finset.filter`, without which `X < (p : ℝ)` elaborates `p` at type `ℝ`
   (the pinned-Mathlib binder quirk of §7.4).  The term is otherwise
   character-for-character the spec's.
2. `norm_sum_far_le` (internal, not spec-frozen) is stated for an arbitrary
   predicate `p` with `[DecidablePred p]` and hypothesis
   `∀ ρ ∈ filter p, r < ‖s₀ - ρ‖`: the §4.4 far cut is by
   `¬ dist ρ (1+iτ) ≤ 6η`, whose `Finset.filter` elaborates through
   `Real.decidableLE`, not the `Classical.propDecidable` a
   `Classical`-scoped statement with a variable predicate would bake in.
3. Two Mathlib imports beyond the two campaign files:
   `Mathlib.MeasureTheory.Function.Floor` (`Nat.measurable_floor`) and
   `Mathlib.NumberTheory.AbelSummation` (`sum_mul_eq_sub_sub_integral_mul`).
4. `hW` (`W ≥ e⁵⁰⁰`) is unused: every budget closes from `hηlow` alone
   (`ηL ≥ 1/12`, hence `N ≥ 2400006`).  It stays in the signature as frozen.
5. No other spec statement appears here, so nothing else can deviate.
-/
import Carmichael.SmallDiskZeroCount
import Carmichael.TuranPowerSum
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.AbelSummation

set_option autoImplicit false

open Complex Finset Metric
open ArithmeticFunction (vonMangoldt)
open scoped Classical

namespace Carmichael

noncomputable section

/-! ### §4.1 Frozen definitions -/

/-- Power-sum index count at scale `η`, family scale `L = log W`:
the File-3 mass bound at radius `6η` against `log(q(|τ|+2)) ≤ 2L`,
ceiling-rounded with base 6. -/
noncomputable def Ndet (η L : ℝ) : ℕ := ⌈(6 : ℝ) + 28800000 * η * L⌉₊

/-- Power-sum offset: `k` ranges in `[6·Ndet + 1, 7·Ndet]`. -/
noncomputable def Mdet (η L : ℝ) : ℕ := 6 * Ndet η L

/-- Detector window endpoints. -/
noncomputable def Xone (η L : ℝ) : ℝ := Real.exp ((Mdet η L : ℝ) / (16 * η))
noncomputable def Xtwo (η L : ℝ) : ℝ := Real.exp (16 * (Mdet η L : ℝ) / η)

/-- The prime window sum `∑_{p prime, X < p ≤ u} χ(p)·log p·p^{−1−iτ}`. -/
noncomputable def primeWindowSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (τ X u : ℝ) : ℂ :=
  ∑ p ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun p : ℕ => p.Prime ∧ X < (p : ℝ)),
    χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-(1 : ℂ) - (τ : ℂ) * Complex.I)

/-! ### Elementary arithmetic of the frozen parameters -/

lemma six_le_Ndet (η L : ℝ) (hη : 0 ≤ η) (hL : 0 ≤ L) : 6 ≤ Ndet η L := by
  have h : (6 : ℝ) ≤ 6 + 28800000 * η * L := by nlinarith
  have := Nat.le_ceil ((6 : ℝ) + 28800000 * η * L)
  have h6 : ((6 : ℕ) : ℝ) ≤ (Ndet η L : ℕ) := by
    unfold Ndet
    exact_mod_cast h.trans (Nat.le_ceil _)
  exact_mod_cast h6

lemma Ndet_pos (η L : ℝ) (hη : 0 ≤ η) (hL : 0 ≤ L) : 0 < Ndet η L :=
  lt_of_lt_of_le (by norm_num) (six_le_Ndet η L hη hL)

lemma le_Ndet_cast (η L : ℝ) : (6 : ℝ) + 28800000 * η * L ≤ (Ndet η L : ℝ) :=
  Nat.le_ceil _

lemma Ndet_cast_lt (η L : ℝ) (hη : 0 ≤ η) (hL : 0 ≤ L) :
    (Ndet η L : ℝ) < 7 + 28800000 * η * L := by
  have h : (0:ℝ) ≤ 6 + 28800000 * η * L := by nlinarith
  have := Nat.ceil_lt_add_one (a := (6 : ℝ) + 28800000 * η * L) h
  unfold Ndet
  linarith

lemma Mdet_eq (η L : ℝ) : Mdet η L = 6 * Ndet η L := rfl

lemma Mdet_pos (η L : ℝ) (hη : 0 ≤ η) (hL : 0 ≤ L) : 0 < Mdet η L := by
  have := Ndet_pos η L hη hL
  simpa [Mdet] using Nat.mul_pos (by norm_num : 0 < 6) this

lemma Xone_pos (η L : ℝ) : 0 < Xone η L := Real.exp_pos _
lemma Xtwo_pos (η L : ℝ) : 0 < Xtwo η L := Real.exp_pos _

lemma Xone_lt_Xtwo {η L : ℝ} (hη : 0 < η) (hL : 0 ≤ L) : Xone η L < Xtwo η L := by
  have hM : (0:ℝ) < (Mdet η L : ℝ) := by
    exact_mod_cast Mdet_pos η L hη.le hL
  apply Real.exp_lt_exp.mpr
  rw [div_lt_div_iff₀ (by positivity) hη]
  nlinarith

/-! ### The analytic Landau remainder `g = L′/L − ∑_ρ m_ρ/(·−ρ)` -/

section Remainder

variable {N : ℕ} [NeZero N]

/-- **The Landau remainder is analytic.**  For nontrivial `χ` there is a
function `g`, analytic on the open `13/8`-disk around `2 + it₀`, agreeing with
`L′/L − ∑_{ρ ∈ zeroDiskFinset} m_ρ/(·−ρ)` at every non-zero of `L` in that disk
and bounded by `520000·log(N(|t₀|+2))` on the open `3/2`-disk.

This discharges the removable-singularity hazard of Z7-tzlite §4.6 *by
construction*: `g` is `logDeriv h` for the Landau factorization `L = P·h`
supplied by `PartialFractions.exists_LFunction_factorization`, so no
singularity is ever created and no removal is needed.  The bound is inherited
from `norm_logDeriv_sub_sum_zeroDiskFinset_le` at the non-zeros and extended to
the zeros by continuity (the zeros of `L` are isolated in the disk). -/
theorem exists_logDeriv_remainder {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (t₀ : ℝ) :
    ∃ g : ℂ → ℂ,
      AnalyticOnNhd ℂ g (ball ((2:ℂ) + t₀ * I) (13/8 : ℝ)) ∧
      (∀ s ∈ ball ((2:ℂ) + t₀ * I) (3/2 : ℝ),
          ‖g s‖ ≤ 520000 * Real.log ((N : ℝ) * (|t₀| + 2))) ∧
      (∀ s ∈ ball ((2:ℂ) + t₀ * I) (13/8 : ℝ),
          DirichletCharacter.LFunction χ s ≠ 0 →
            deriv (DirichletCharacter.LFunction χ) s
                / DirichletCharacter.LFunction χ s
              - ∑ ρ ∈ zeroDiskFinset χ t₀,
                  (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
                    / (s - ρ)
              = g s) := by
  classical
  obtain ⟨h, hh_an, hh_fac, hh_ne⟩ := exists_LFunction_factorization hχ t₀
  set c : ℂ := (2:ℂ) + t₀ * I with hcdef
  set L : ℂ → ℂ := DirichletCharacter.LFunction χ with hLdef
  set m : ℂ → ℕ := fun ρ => analyticOrderNatAt L ρ with hmdef
  -- inclusions between the four radii in play
  have hsub_13_74 : ball c (13/8 : ℝ) ⊆ closedBall c (7/4 : ℝ) := fun z hz =>
    closedBall_subset_closedBall (by norm_num : (13/8:ℝ) ≤ 7/4)
      (ball_subset_closedBall hz)
  have hsub_13c : ball c (13/8 : ℝ) ⊆ closedBall c (13/8 : ℝ) :=
    ball_subset_closedBall
  have hsub_32_13 : ball c (3/2 : ℝ) ⊆ ball c (13/8 : ℝ) :=
    ball_subset_ball (by norm_num)
  refine ⟨logDeriv h, ?_, ?_, ?_⟩
  · -- analyticity of `logDeriv h` on the open `13/8`-disk
    intro z hz
    have h1 : AnalyticAt ℂ h z := hh_an z (hsub_13_74 hz)
    have h2 : h z ≠ 0 := hh_ne z (hsub_13c hz)
    simpa [logDeriv] using (h1.deriv.div h1 h2)
  · -- the uniform bound on the open `3/2`-disk
    intro s hs
    -- first the non-zeros, where the Landau expansion applies directly
    have hgood : ∀ z ∈ ball c (3/2 : ℝ), L z ≠ 0 →
        ‖logDeriv h z‖ ≤ 520000 * Real.log ((N : ℝ) * (|t₀| + 2)) := by
      intro z hz hLz
      have hz32 : z ∈ closedBall c (3/2 : ℝ) := ball_subset_closedBall hz
      have hzU : z ∈ closedBall c (7/4 : ℝ) := hsub_13_74 (hsub_32_13 hz)
      have hz13 : z ∈ closedBall c (13/8 : ℝ) := hsub_13c (hsub_32_13 hz)
      have hPz_ne : (∏ ρ ∈ zeroDiskFinset χ t₀, (z - ρ) ^ m ρ) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro ρ hρ
        refine pow_ne_zero _ ?_
        rw [sub_ne_zero]
        intro hzρ
        exact hLz (hzρ ▸ ((mem_zeroDiskFinset hχ).mp hρ).2)
      have hhz_ne : h z ≠ 0 := hh_ne z hz13
      have hPdiff : Differentiable ℂ (fun w => ∏ ρ ∈ zeroDiskFinset χ t₀,
          (w - ρ) ^ m ρ) := by
        have hrw : (fun w => ∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ)
            = ∏ ρ ∈ zeroDiskFinset χ t₀, fun w => (w - ρ) ^ m ρ := by
          funext w; rw [Finset.prod_apply]
        rw [hrw]
        exact Differentiable.finsetProd fun u _ => (differentiable_id.sub_const u).pow _
      have hnb : L =ᶠ[nhds z] fun w =>
          (∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ) * h w := by
        filter_upwards [isOpen_ball.mem_nhds (hsub_32_13 hz)] with w hw
        exact hh_fac w (hsub_13_74 hw)
      have hd1 : deriv L z
          = deriv (fun w => (∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ) * h w) z :=
        hnb.deriv_eq
      have hval : L z = (∏ ρ ∈ zeroDiskFinset χ t₀, (z - ρ) ^ m ρ) * h z :=
        hh_fac z hzU
      have hld : logDeriv (fun w =>
          (∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ) * h w) z
          = logDeriv (fun w => ∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ) z
            + logDeriv h z :=
        logDeriv_mul z hPz_ne hhz_ne (hPdiff z) ((hh_an z hzU).differentiableAt)
      have hPld : logDeriv (fun w => ∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ) z
          = ∑ ρ ∈ zeroDiskFinset χ t₀, (m ρ : ℂ) / (z - ρ) := by
        have h1 : logDeriv (fun w => ∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ) z
            = ∑ ρ ∈ zeroDiskFinset χ t₀,
                logDeriv (fun w => (w - ρ) ^ m ρ) z :=
          logDeriv_prod (f := fun ρ => fun w => (w - ρ) ^ m ρ)
            (fun ρ hρ => by
              refine pow_ne_zero _ ?_
              rw [sub_ne_zero]
              intro hzρ
              exact hLz (hzρ ▸ ((mem_zeroDiskFinset hχ).mp hρ).2))
            (fun ρ _ => ((differentiable_id.sub_const ρ).pow _).differentiableAt)
        rw [h1]
        refine Finset.sum_congr rfl fun ρ hρ => ?_
        have hzρ : z - ρ ≠ 0 := by
          rw [sub_ne_zero]
          intro hzρ
          exact hLz (hzρ ▸ ((mem_zeroDiskFinset hχ).mp hρ).2)
        have h2 : logDeriv (fun w => (w - ρ) ^ m ρ) z
            = (m ρ : ℂ) * logDeriv (fun w => w - ρ) z :=
          logDeriv_fun_pow ((differentiable_id.sub_const ρ).differentiableAt) _
        have h3 : logDeriv (fun w => w - ρ) z = 1 / (z - ρ) := by
          rw [logDeriv_apply, deriv_sub_const, deriv_id'']
        rw [h2, h3]; ring
      have hfinal : deriv L z / L z
          - ∑ ρ ∈ zeroDiskFinset χ t₀, (m ρ : ℂ) / (z - ρ) = logDeriv h z := by
        have hLD : deriv L z / L z = logDeriv (fun w =>
            (∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ) * h w) z := by
          rw [logDeriv_apply, ← hd1, ← hval]
        rw [hLD, hld, hPld]
        ring
      rw [← hfinal]
      exact norm_logDeriv_sub_sum_zeroDiskFinset_le hχ t₀ hz32 hLz
    by_cases hLs : L s = 0
    · -- at a zero: pass to the limit along the punctured neighbourhood
      have hs74 : s ∈ closedBall c (7/4 : ℝ) := hsub_13_74 (hsub_32_13 hs)
      have hLan : AnalyticAt ℂ L s :=
        (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
      have hne : ∀ᶠ z in nhdsWithin s {s}ᶜ, L z ≠ 0 := by
        rcases hLan.eventually_eq_zero_or_eventually_ne_zero with hz | hz
        · exact absurd (analyticOrderAt_eq_top.mpr hz)
            (analyticOrderAt_ne_top_on_disk hχ t₀ hs74)
        · exact hz
      have hballev : ∀ᶠ z in nhdsWithin s {s}ᶜ, z ∈ ball c (3/2 : ℝ) :=
        nhdsWithin_le_nhds (isOpen_ball.mem_nhds hs)
      have hev : ∀ᶠ z in nhdsWithin s {s}ᶜ,
          ‖logDeriv h z‖ ≤ 520000 * Real.log ((N : ℝ) * (|t₀| + 2)) := by
        filter_upwards [hne, hballev] with z hz1 hz2 using hgood z hz2 hz1
      have hcont : ContinuousAt (fun z => ‖logDeriv h z‖) s := by
        have h1 : AnalyticAt ℂ h s := hh_an s hs74
        have h2 : h s ≠ 0 := hh_ne s (hsub_13c (hsub_32_13 hs))
        have : AnalyticAt ℂ (logDeriv h) s := by
          simpa [logDeriv] using (h1.deriv.div h1 h2)
        exact this.continuousAt.norm
      exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) hev
    · exact hgood s hs hLs
  · -- the identity at the non-zeros of the open `13/8`-disk
    intro s hs hLs
    have hsU : s ∈ closedBall c (7/4 : ℝ) := hsub_13_74 hs
    have hs13 : s ∈ closedBall c (13/8 : ℝ) := hsub_13c hs
    have hPs_ne : (∏ ρ ∈ zeroDiskFinset χ t₀, (s - ρ) ^ m ρ) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro ρ hρ
      refine pow_ne_zero _ ?_
      rw [sub_ne_zero]
      intro hsρ
      exact hLs (hsρ ▸ ((mem_zeroDiskFinset hχ).mp hρ).2)
    have hhs_ne : h s ≠ 0 := hh_ne s hs13
    have hPdiff : Differentiable ℂ (fun w => ∏ ρ ∈ zeroDiskFinset χ t₀,
        (w - ρ) ^ m ρ) := by
      have hrw : (fun w => ∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ)
          = ∏ ρ ∈ zeroDiskFinset χ t₀, fun w => (w - ρ) ^ m ρ := by
        funext w; rw [Finset.prod_apply]
      rw [hrw]
      exact Differentiable.finsetProd fun u _ => (differentiable_id.sub_const u).pow _
    have hnb : L =ᶠ[nhds s] fun w =>
        (∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ) * h w := by
      filter_upwards [isOpen_ball.mem_nhds hs] with w hw
      exact hh_fac w (hsub_13_74 hw)
    have hd1 : deriv L s
        = deriv (fun w => (∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ) * h w) s :=
      hnb.deriv_eq
    have hval : L s = (∏ ρ ∈ zeroDiskFinset χ t₀, (s - ρ) ^ m ρ) * h s :=
      hh_fac s hsU
    have hld : logDeriv (fun w =>
        (∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ) * h w) s
        = logDeriv (fun w => ∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ) s
          + logDeriv h s :=
      logDeriv_mul s hPs_ne hhs_ne (hPdiff s) ((hh_an s hsU).differentiableAt)
    have hPld : logDeriv (fun w => ∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ) s
        = ∑ ρ ∈ zeroDiskFinset χ t₀, (m ρ : ℂ) / (s - ρ) := by
      have h1 : logDeriv (fun w => ∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ) s
          = ∑ ρ ∈ zeroDiskFinset χ t₀, logDeriv (fun w => (w - ρ) ^ m ρ) s :=
        logDeriv_prod (f := fun ρ => fun w => (w - ρ) ^ m ρ)
          (fun ρ hρ => by
            refine pow_ne_zero _ ?_
            rw [sub_ne_zero]
            intro hsρ
            exact hLs (hsρ ▸ ((mem_zeroDiskFinset hχ).mp hρ).2))
          (fun ρ _ => ((differentiable_id.sub_const ρ).pow _).differentiableAt)
      rw [h1]
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      have hsρ : s - ρ ≠ 0 := by
        rw [sub_ne_zero]
        intro hsρ
        exact hLs (hsρ ▸ ((mem_zeroDiskFinset hχ).mp hρ).2)
      have h2 : logDeriv (fun w => (w - ρ) ^ m ρ) s
          = (m ρ : ℂ) * logDeriv (fun w => w - ρ) s :=
        logDeriv_fun_pow ((differentiable_id.sub_const ρ).differentiableAt) _
      have h3 : logDeriv (fun w => w - ρ) s = 1 / (s - ρ) := by
        rw [logDeriv_apply, deriv_sub_const, deriv_id'']
      rw [h2, h3]; ring
    have hLD : deriv L s / L s = logDeriv (fun w =>
        (∏ ρ ∈ zeroDiskFinset χ t₀, (w - ρ) ^ m ρ) * h w) s := by
      rw [logDeriv_apply, ← hd1, ← hval]
    rw [hLD, hld, hPld]
    ring

end Remainder

/-! ### Cauchy estimates for the remainder -/

section Cauchy

/-- **Cauchy estimate on radius `1/2`.**  A function analytic on the open
`13/8`-disk around `c` and bounded by `C` on the open `3/2`-disk has
`‖g^{(k)}(s₀)‖ ≤ k!·C·2^k` at every `s₀` with `dist s₀ c < 1`.  This is the
Z7-tzlite §4.4 step-1 error term (`k`-th derivative of the Landau remainder). -/
lemma norm_iteratedDeriv_le_of_bounded_on_disk {g : ℂ → ℂ} {c : ℂ} {C : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball c (13/8 : ℝ)))
    (hb : ∀ s ∈ ball c (3/2 : ℝ), ‖g s‖ ≤ C)
    {s₀ : ℂ} (hs₀ : dist s₀ c < 1) (k : ℕ) :
    ‖iteratedDeriv k g s₀‖ ≤ (k.factorial : ℝ) * C * 2 ^ k := by
  have hsub : closedBall s₀ (1/2 : ℝ) ⊆ ball c (13/8 : ℝ) := by
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_ball]
    calc dist z c ≤ dist z s₀ + dist s₀ c := dist_triangle _ _ _
      _ < 1/2 + 1 := by linarith
      _ ≤ 13/8 := by norm_num
  have hdiff : DiffContOnCl ℂ g (ball s₀ (1/2 : ℝ)) := by
    constructor
    · intro z hz
      exact ((hg z (hsub (ball_subset_closedBall hz))).differentiableAt).differentiableWithinAt
    · intro z hz
      rw [closure_ball s₀ (by norm_num : (1/2:ℝ) ≠ 0)] at hz
      exact ((hg z (hsub hz)).continuousAt).continuousWithinAt
  have hsph : ∀ z ∈ sphere s₀ (1/2 : ℝ), ‖g z‖ ≤ C := by
    intro z hz
    rw [mem_sphere] at hz
    refine hb z ?_
    rw [mem_ball]
    calc dist z c ≤ dist z s₀ + dist s₀ c := dist_triangle _ _ _
      _ < 1/2 + 1 := by rw [hz]; linarith
      _ ≤ 3/2 := by norm_num
  have := norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := s₀) (R := (1/2 : ℝ))
    (C := C) (f := g) k (by norm_num) hdiff hsph
  calc ‖iteratedDeriv k g s₀‖ ≤ (k.factorial : ℝ) * C / (1/2 : ℝ) ^ k := this
    _ = (k.factorial : ℝ) * C * 2 ^ k := by
        rw [div_pow, one_pow]
        field_simp

end Cauchy

/-! ### The `k`-th derivative of a simple pole -/

section PoleDeriv

/-- `d^k/dz^k (z − ρ)⁻¹ = (−1)^k·k!·(z − ρ)^{−(k+1)}`. -/
lemma iteratedDeriv_sub_inv (ρ : ℂ) : ∀ (k : ℕ) {z : ℂ}, z ≠ ρ →
    iteratedDeriv k (fun w => (w - ρ)⁻¹) z
      = (-1) ^ k * (k.factorial : ℂ) / (z - ρ) ^ (k + 1) := by
  intro k
  induction k with
  | zero => intro z hz; simp [iteratedDeriv_zero]
  | succ n ih =>
    intro z hz
    have hz0 : z - ρ ≠ 0 := sub_ne_zero.mpr hz
    have hopen : IsOpen {w : ℂ | w ≠ ρ} := isOpen_ne
    have hev : iteratedDeriv n (fun w => (w - ρ)⁻¹)
        =ᶠ[nhds z] fun w =>
          ((-1) ^ n * (n.factorial : ℂ)) * ((w - ρ) ^ (n + 1))⁻¹ := by
      filter_upwards [hopen.mem_nhds hz] with w hw
      rw [ih hw, div_eq_mul_inv]
    have h1 : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
    have hd : HasDerivAt (fun w : ℂ => (w - ρ) ^ (n + 1))
        (((n : ℂ) + 1) * (z - ρ) ^ n) z := by
      have h2 := h1.pow (n + 1)
      simp only [Nat.add_sub_cancel, mul_one, Nat.cast_add, Nat.cast_one] at h2
      exact h2
    have hne : (z - ρ) ^ (n + 1) ≠ 0 := pow_ne_zero _ hz0
    have hinv : HasDerivAt (fun w : ℂ => ((w - ρ) ^ (n + 1))⁻¹)
        (-(((n : ℂ) + 1) * (z - ρ) ^ n) / ((z - ρ) ^ (n + 1)) ^ 2) z := hd.inv hne
    have hD := hinv.const_mul ((-1 : ℂ) ^ n * (n.factorial : ℂ))
    rw [iteratedDeriv_succ, hev.deriv_eq, hD.deriv]
    have hfac : (((n + 1).factorial : ℕ) : ℂ) = ((n : ℂ) + 1) * (n.factorial : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hsq : ((z - ρ) ^ (n + 1)) ^ 2 = (z - ρ) ^ n * (z - ρ) ^ (n + 2) := by ring
    rw [hfac, hsq]
    have hzn : (z - ρ) ^ n ≠ 0 := pow_ne_zero _ hz0
    have hz2 : (z - ρ) ^ (n + 2) ≠ 0 := pow_ne_zero _ hz0
    field_simp
    ring

end PoleDeriv

/-! ### §4.4 step 1: the `k`-th derivative representation -/

section Representation

variable {N : ℕ} [NeZero N]

/-- Iterating `LSeries.logMul` inserts the factor `(log n)^k`. -/
lemma logMul_iterate (f : ℕ → ℂ) : ∀ (k n : ℕ),
    LSeries.logMul^[k] f n = (Real.log n : ℂ) ^ k * f n := by
  intro k
  induction k with
  | zero => intro n; simp
  | succ m ih =>
    intro n
    rw [Function.iterate_succ_apply']
    show Complex.log (n : ℂ) * (LSeries.logMul^[m] f n) = _
    rw [ih n]
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
    rw [hlog]
    ring

omit [NeZero N] in
/-- Abscissa of absolute convergence of the twisted von Mangoldt series. -/
lemma abscissa_twist_vonMangoldt_le (χ : DirichletCharacter ℂ N) :
    LSeries.abscissaOfAbsConv
        ((fun n : ℕ => χ (n : ZMod N)) * fun n : ℕ => (vonMangoldt n : ℂ))
      ≤ (1 : ℝ) := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1) ?_
  intro y hy
  refine DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ ?_
  rw [Complex.ofReal_re]
  exact hy

/-- `−L′/L = LSeries(χ·Λ)` on the half-plane of absolute convergence. -/
lemma logDeriv_LFunction_eq {χ : DirichletCharacter ℂ N} {s : ℂ} (hs : 1 < s.re) :
    deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
      = -LSeries ((fun n : ℕ => χ (n : ZMod N))
          * fun n : ℕ => (vonMangoldt n : ℂ)) s := by
  have h1 : LSeries ((fun n : ℕ => χ (n : ZMod N))
        * fun n : ℕ => (vonMangoldt n : ℂ)) s
      = -deriv (LSeries (fun n : ℕ => χ (n : ZMod N))) s
        / LSeries (fun n : ℕ => χ (n : ZMod N)) s :=
    DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have h2 : deriv (LSeries (fun n : ℕ => χ (n : ZMod N))) s
      = deriv (DirichletCharacter.LFunction χ) s :=
    (DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs).symm
  have h3 : LSeries (fun n : ℕ => χ (n : ZMod N)) s
      = DirichletCharacter.LFunction χ s :=
    (DirichletCharacter.LFunction_eq_LSeries χ hs).symm
  rw [h1, h2, h3, neg_div, neg_neg]

/-- The `k`-th derivative of the Landau zero sum. -/
lemma iteratedDeriv_zeroSum {χ : DirichletCharacter ℂ N} (τ : ℝ) {s₀ : ℂ}
    (hs₀ : ∀ ρ ∈ zeroDiskFinset χ τ, s₀ ≠ ρ) (k : ℕ) :
    iteratedDeriv k (fun s => ∑ ρ ∈ zeroDiskFinset χ τ,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)) s₀
      = (-1) ^ k * (k.factorial : ℂ) * ∑ ρ ∈ zeroDiskFinset χ τ,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
            / (s₀ - ρ) ^ (k + 1) := by
  classical
  have hinv : ∀ ρ ∈ zeroDiskFinset χ τ,
      ContDiffAt ℂ (k : ℕ∞) (fun s : ℂ => (s - ρ)⁻¹) s₀ := by
    intro ρ hρ
    have h1 : ContDiffAt ℂ (k : ℕ∞) (fun s : ℂ => s - ρ) s₀ :=
      contDiffAt_id.sub contDiffAt_const
    exact h1.inv (sub_ne_zero.mpr (hs₀ ρ hρ))
  have hrw : (fun s : ℂ => ∑ ρ ∈ zeroDiskFinset χ τ,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ))
      = fun s : ℂ => ∑ ρ ∈ zeroDiskFinset χ τ,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((s - ρ)⁻¹) := by
    funext s
    exact Finset.sum_congr rfl fun ρ _ => div_eq_mul_inv _ _
  rw [hrw]
  rw [iteratedDeriv_fun_sum (fun ρ hρ => contDiffAt_const.mul (hinv ρ hρ)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  rw [iteratedDeriv_const_mul
    (c := (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ))
    (f := fun s : ℂ => (s - ρ)⁻¹) (hinv ρ hρ),
    iteratedDeriv_sub_inv ρ k (hs₀ ρ hρ)]
  ring

/-- **§4.4 step 1 (representation).**  At a point `s₀` of the Landau `13/8`-disk
with `Re s₀ > 1`, the zero sum of order `k+1` is the normalized `k`-th
derivative of the twisted von Mangoldt Dirichlet series, corrected by the
`k`-th derivative of the analytic remainder `g`. -/
theorem kderiv_representation {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (τ : ℝ)
    {g : ℂ → ℂ}
    (hgan : AnalyticOnNhd ℂ g (ball ((2:ℂ) + τ * I) (13/8 : ℝ)))
    (hgid : ∀ s ∈ ball ((2:ℂ) + τ * I) (13/8 : ℝ),
        DirichletCharacter.LFunction χ s ≠ 0 →
          deriv (DirichletCharacter.LFunction χ) s
              / DirichletCharacter.LFunction χ s
            - ∑ ρ ∈ zeroDiskFinset χ τ,
                (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
                  / (s - ρ)
            = g s)
    {s₀ : ℂ} (hs₀mem : s₀ ∈ ball ((2:ℂ) + τ * I) (13/8 : ℝ))
    (hs₀re : 1 < s₀.re) (k : ℕ) :
    ∑ ρ ∈ zeroDiskFinset χ τ,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
          / (s₀ - ρ) ^ (k + 1)
      = -(LSeries (fun n : ℕ => (Real.log n : ℂ) ^ k
              * (χ (n : ZMod N) * (vonMangoldt n : ℂ))) s₀
            + (-1) ^ k * iteratedDeriv k g s₀) / (k.factorial : ℂ) := by
  classical
  set f : ℕ → ℂ := (fun n : ℕ => χ (n : ZMod N))
    * fun n : ℕ => (vonMangoldt n : ℂ) with hfdef
  set Zf : ℂ → ℂ := fun s => ∑ ρ ∈ zeroDiskFinset χ τ,
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)
    with hZdef
  have hL0 : ∀ s : ℂ, 1 < s.re → DirichletCharacter.LFunction χ s ≠ 0 := fun s hs =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
  have hne : ∀ ρ ∈ zeroDiskFinset χ τ, s₀ ≠ ρ := by
    intro ρ hρ hcon
    exact hL0 s₀ hs₀re (hcon ▸ ((mem_zeroDiskFinset hχ).mp hρ).2)
  have hV : IsOpen (ball ((2:ℂ) + τ * I) (13/8 : ℝ) ∩ {s : ℂ | 1 < s.re}) :=
    isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)
  have hVmem : s₀ ∈ ball ((2:ℂ) + τ * I) (13/8 : ℝ) ∩ {s : ℂ | 1 < s.re} :=
    ⟨hs₀mem, hs₀re⟩
  have hEqOn : ∀ s ∈ ball ((2:ℂ) + τ * I) (13/8 : ℝ) ∩ {s : ℂ | 1 < s.re},
      LSeries f s = -(Zf s + g s) := by
    rintro s ⟨hs1, hs2⟩
    have h1 := hgid s hs1 (hL0 s hs2)
    rw [logDeriv_LFunction_eq (χ := χ) (s := s) hs2] at h1
    show LSeries f s = -((∑ ρ ∈ zeroDiskFinset χ τ,
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)) + g s)
    linear_combination -h1
  have hev : LSeries f =ᶠ[nhds s₀] fun s => -(Zf s + g s) := by
    filter_upwards [hV.mem_nhds hVmem] with s hs using hEqOn s hs
  have hZcd : ContDiffAt ℂ (k : ℕ∞) Zf s₀ := by
    have hinv : ∀ ρ ∈ zeroDiskFinset χ τ,
        ContDiffAt ℂ (k : ℕ∞) (fun s : ℂ => (s - ρ)⁻¹) s₀ := by
      intro ρ hρ
      exact (contDiffAt_id.sub contDiffAt_const).inv (sub_ne_zero.mpr (hne ρ hρ))
    have hrw : Zf = fun s : ℂ => ∑ ρ ∈ zeroDiskFinset χ τ,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * ((s - ρ)⁻¹) := by
      rw [hZdef]
      funext s
      exact Finset.sum_congr rfl fun ρ _ => div_eq_mul_inv _ _
    rw [hrw]
    exact ContDiffAt.sum fun ρ hρ => contDiffAt_const.mul (hinv ρ hρ)
  have hgcd : ContDiffAt ℂ (k : ℕ∞) g s₀ := (hgan s₀ hs₀mem).contDiffAt
  have hLHS : iteratedDeriv k (LSeries f) s₀
      = (-1) ^ k * LSeries (LSeries.logMul^[k] f) s₀ := by
    refine LSeries_iteratedDeriv k ?_
    refine lt_of_le_of_lt (abscissa_twist_vonMangoldt_le χ) ?_
    exact_mod_cast EReal.coe_lt_coe hs₀re
  have hRHS : iteratedDeriv k (fun s => -(Zf s + g s)) s₀
      = -((-1) ^ k * (k.factorial : ℂ)
          * (∑ ρ ∈ zeroDiskFinset χ τ,
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
                / (s₀ - ρ) ^ (k + 1))
        + iteratedDeriv k g s₀) := by
    have hfun : (fun s => -(Zf s + g s)) = -(Zf + g) := rfl
    rw [hfun, iteratedDeriv_neg, iteratedDeriv_add hZcd hgcd, hZdef,
      iteratedDeriv_zeroSum τ hne k]
  have hkey := hev.iteratedDeriv_eq k
  rw [hLHS, hRHS] at hkey
  have hser : LSeries (LSeries.logMul^[k] f) s₀
      = LSeries (fun n : ℕ => (Real.log n : ℂ) ^ k
          * (χ (n : ZMod N) * (vonMangoldt n : ℂ))) s₀ := by
    congr 1
    funext n
    rw [logMul_iterate f k n]
    rfl
  rw [hser] at hkey
  have hfac : ((k.factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have he : ((-1 : ℂ)) ^ k * ((-1 : ℂ)) ^ k = 1 := by
    rw [← mul_pow]; norm_num
  rw [eq_div_iff hfac]
  linear_combination ((-1 : ℂ)) ^ k * hkey
    - (LSeries (fun n : ℕ => (Real.log n : ℂ) ^ k
          * (χ (n : ZMod N) * (vonMangoldt n : ℂ))) s₀
        + (k.factorial : ℂ) * ∑ ρ ∈ zeroDiskFinset χ τ,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
              / (s₀ - ρ) ^ (k + 1)) * he

end Representation

/-! ### §4.4 step 3: the far-zero estimates -/

section FarZeros

variable {N : ℕ} [NeZero N]

/-- Per-zero comparison: a point with `Re z ≥ η > 0` has
`m/‖z‖² ≤ η⁻¹·Re(m/z)`. -/
lemma div_normSq_le_re_div {m : ℕ} {z : ℂ} {η : ℝ} (hη : 0 < η) (hre : η ≤ z.re) :
    (m : ℝ) / ‖z‖ ^ 2 ≤ (1/η) * ((m : ℂ) / z).re := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hns : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  have hns0 : (0 : ℝ) < ‖z‖ ^ 2 := by
    have : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
    positivity
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
  rw [hns]
  rw [div_le_iff₀ hns0]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hstep : (m : ℝ) * η ≤ (m : ℝ) * z.re := mul_le_mul_of_nonneg_left hre hm
  have hexp : (1/η) * ((m : ℝ) * z.re / ‖z‖ ^ 2) * ‖z‖ ^ 2
      = (1/η) * ((m : ℝ) * z.re) := by
    field_simp
  rw [hexp]
  have hu : (0 : ℝ) < 1/η := by positivity
  have h3 : (1/η) * ((m : ℝ) * η) ≤ (1/η) * ((m : ℝ) * z.re) :=
    mul_le_mul_of_nonneg_left hstep hu.le
  have h4 : (1/η) * ((m : ℝ) * η) = (m : ℝ) := by field_simp
  linarith [h3, h4]

/-- **The `ℓ²` zero sum** at `s₀ = (1+η) + iτ` (TZ's intermediate bound inside
the proof of their (4.1)).  Every zero of the Landau disk has real part `< 1`,
so `Re(s₀ − ρ) > η`, and the partial-fraction bound caps the resulting
`η`-weighted mass. -/
lemma sum_ord_div_normSq_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (τ : ℝ)
    {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1/20) :
    ∑ ρ ∈ zeroDiskFinset χ τ,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
          / ‖(((1 + η : ℝ) : ℂ) + τ * I) - ρ‖ ^ 2
      ≤ (1/η) * (1/η + 2 + 520000 * Real.log ((N : ℝ) * (|τ| + 2))) := by
  classical
  set s₀ : ℂ := ((1 + η : ℝ) : ℂ) + τ * I with hs₀def
  have hs₀re : s₀.re = 1 + η := by rw [hs₀def]; simp
  have hL0 : DirichletCharacter.LFunction χ s₀ ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by rw [hs₀re]; linarith)
  have hmem : s₀ ∈ closedBall ((2 : ℂ) + τ * I) (3/2 : ℝ) := by
    rw [mem_closedBall, Complex.dist_eq]
    have hdiff : s₀ - ((2 : ℂ) + τ * I) = ((1 + η - 2 : ℝ) : ℂ) := by
      rw [hs₀def]; push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  -- every zero of the Landau disk has real part `< 1`
  have hzre : ∀ ρ ∈ zeroDiskFinset χ τ, ρ.re < 1 := by
    intro ρ hρ
    by_contra hcon
    push Not at hcon
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hcon)
      ((mem_zeroDiskFinset hχ).mp hρ).2
  -- termwise comparison
  have hterm : ∀ ρ ∈ zeroDiskFinset χ τ,
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖s₀ - ρ‖ ^ 2
        ≤ (1/η) * (((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
            / (s₀ - ρ)).re) := by
    intro ρ hρ
    refine div_normSq_le_re_div hη0 ?_
    rw [Complex.sub_re, hs₀re]
    linarith [hzre ρ hρ]
  -- the partial-fraction upper bound on the real part
  have hPF : (∑ ρ ∈ zeroDiskFinset χ τ,
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s₀ - ρ)).re
      ≤ 1/η + 2 + 520000 * Real.log ((N : ℝ) * (|τ| + 2)) := by
    have hpf := norm_logDeriv_sub_sum_zeroDiskFinset_le hχ τ hmem hL0
    have hnormLD := norm_logDeriv_le_of_re_eq (χ := χ) hη0 hη hs₀re
    have habs := Complex.abs_re_le_norm
      (deriv (DirichletCharacter.LFunction χ) s₀ / DirichletCharacter.LFunction χ s₀
        - ∑ ρ ∈ zeroDiskFinset χ τ,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s₀ - ρ))
    rw [Complex.sub_re] at habs
    have h1 := abs_le.mp (le_trans habs hpf)
    have h2 := abs_le.mp (Complex.abs_re_le_norm
      (deriv (DirichletCharacter.LFunction χ) s₀
        / DirichletCharacter.LFunction χ s₀))
    linarith [h1.1, h2.2]
  calc ∑ ρ ∈ zeroDiskFinset χ τ,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / ‖s₀ - ρ‖ ^ 2
      ≤ ∑ ρ ∈ zeroDiskFinset χ τ, (1/η) *
          (((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
            / (s₀ - ρ)).re) := Finset.sum_le_sum hterm
    _ = (1/η) * (∑ ρ ∈ zeroDiskFinset χ τ,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
            / (s₀ - ρ)).re := by
        rw [Complex.re_sum, Finset.mul_sum]
    _ ≤ (1/η) * (1/η + 2 + 520000 * Real.log ((N : ℝ) * (|τ| + 2))) := by
        exact mul_le_mul_of_nonneg_left hPF (by positivity)

/-- **The far-zero tail** (§4.4 step 3).  Zeros at distance more than `r` from
`s₀` contribute at most `A/r^j` to the order-`(j+2)` pole sum, where `A` is any
bound for the `ℓ²` zero sum.  The far set may be carved out by any predicate
`p` that forces `r < ‖s₀ - ρ‖`. -/
lemma norm_sum_far_le {χ : DirichletCharacter ℂ N} (τ : ℝ) {s₀ : ℂ}
    {r : ℝ} (hr : 0 < r) (j : ℕ) {A : ℝ} {p : ℂ → Prop} [DecidablePred p]
    (hp : ∀ ρ ∈ (zeroDiskFinset χ τ).filter p, r < ‖s₀ - ρ‖)
    (hA : ∑ ρ ∈ zeroDiskFinset χ τ,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
          / ‖s₀ - ρ‖ ^ 2 ≤ A) :
    ‖∑ ρ ∈ (zeroDiskFinset χ τ).filter p,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
          / (s₀ - ρ) ^ (j + 2)‖ ≤ A / r ^ j := by
  classical
  set K := (zeroDiskFinset χ τ).filter p with hKdef
  have hterm : ∀ ρ ∈ K,
      ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
        / (s₀ - ρ) ^ (j + 2)‖
        ≤ (1 / r ^ j)
          * ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
              / ‖s₀ - ρ‖ ^ 2) := by
    intro ρ hρ
    have hd : r < ‖s₀ - ρ‖ := hp ρ hρ
    rw [hKdef, Finset.mem_filter] at hρ
    have hd0 : (0 : ℝ) < ‖s₀ - ρ‖ := lt_trans hr hd
    rw [norm_div, norm_pow, Complex.norm_natCast]
    have hsplit : ‖s₀ - ρ‖ ^ (j + 2) = ‖s₀ - ρ‖ ^ j * ‖s₀ - ρ‖ ^ 2 := by ring
    rw [hsplit]
    have hrj : r ^ j ≤ ‖s₀ - ρ‖ ^ j := pow_le_pow_left₀ hr.le hd.le j
    have hrj0 : (0 : ℝ) < r ^ j := by positivity
    have hm : (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) :=
      Nat.cast_nonneg _
    rw [div_le_iff₀ (by positivity)]
    have hgoal : (1 / r ^ j)
        * ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
            / ‖s₀ - ρ‖ ^ 2) * (‖s₀ - ρ‖ ^ j * ‖s₀ - ρ‖ ^ 2)
        = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
            * (‖s₀ - ρ‖ ^ j / r ^ j) := by
      field_simp
    rw [hgoal]
    have h1 : (1 : ℝ) ≤ ‖s₀ - ρ‖ ^ j / r ^ j := by
      rw [le_div_iff₀ hrj0]
      linarith
    nlinarith [hm, h1]
  have hnonneg : ∀ ρ ∈ zeroDiskFinset χ τ,
      (0 : ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
        / ‖s₀ - ρ‖ ^ 2 := by
    intro ρ _
    positivity
  calc ‖∑ ρ ∈ K, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
          / (s₀ - ρ) ^ (j + 2)‖
      ≤ ∑ ρ ∈ K, ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
          / (s₀ - ρ) ^ (j + 2)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ K, (1 / r ^ j)
          * ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
              / ‖s₀ - ρ‖ ^ 2) := Finset.sum_le_sum hterm
    _ = (1 / r ^ j) * ∑ ρ ∈ K,
          ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
              / ‖s₀ - ρ‖ ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (1 / r ^ j) * ∑ ρ ∈ zeroDiskFinset χ τ,
          ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
              / ‖s₀ - ρ‖ ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ρ hρ _ => hnonneg ρ hρ)
    _ ≤ (1 / r ^ j) * A := by
        exact mul_le_mul_of_nonneg_left hA (by positivity)
    _ = A / r ^ j := by ring

end FarZeros

/-! ### §4.6: the general-`k` diagonal bound -/

section Diagonal

/-- `x^k ≤ k!·e^x` for `x ≥ 0`: the elementary Stirling floor at a general
point (the `k = x = N` case is `Turan.pow_self_le_factorial_mul_exp`). -/
lemma pow_le_factorial_mul_exp {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    x ^ k ≤ (k.factorial : ℝ) * Real.exp x := by
  have hsum := Real.sum_le_exp_of_nonneg hx (k + 1)
  have hmem : k ∈ Finset.range (k + 1) := Finset.self_mem_range_succ k
  have hnonneg : ∀ i ∈ Finset.range (k + 1), 0 ≤ x ^ i / (i.factorial : ℝ) := by
    intro i _
    have : (0:ℝ) < (i.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos i
    positivity
  have hsingle : x ^ k / (k.factorial : ℝ)
      ≤ ∑ i ∈ Finset.range (k + 1), x ^ i / (i.factorial : ℝ) :=
    Finset.single_le_sum hnonneg hmem
  have hfac : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have := (div_le_iff₀ hfac).mp (le_trans hsingle hsum)
  linarith

/-- `(log n)^k ≤ k!·n^v/v^k` for `n ≥ 1` and `v > 0`. -/
lemma log_pow_le_rpow {v : ℝ} (hv : 0 < v) (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (Real.log n) ^ k ≤ (k.factorial : ℝ) * (n : ℝ) ^ v / v ^ k := by
  have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hlog : (0:ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h1 : (v * Real.log n) ^ k ≤ (k.factorial : ℝ) * Real.exp (v * Real.log n) :=
    pow_le_factorial_mul_exp (by positivity) k
  have h2 : Real.exp (v * Real.log n) = (n : ℝ) ^ v := by
    rw [Real.rpow_def_of_pos hn0, mul_comm]
  rw [h2, mul_pow] at h1
  rw [le_div_iff₀ (by positivity : (0:ℝ) < v ^ k)]
  linarith

/-- **The general-`k` diagonal bound, parametrized form.**  Splitting the
exponent as `1 + u = 1 + v + w` and paying `k!/v^k` for the `(log n)^k` factor,
`∑ Λ(n)(log n)^k n^{−(1+u)} ≤ (k!/v^k)·(1/w + 2)`.  (Z7-tzlite §4.6 asks for
exactly this normalized shape; the caller chooses the split.) -/
lemma tsum_vonMangoldt_log_pow_rpow_le {v w : ℝ} (hv : 0 < v) (hw : 0 < w)
    (hw' : w ≤ 1/20) (k : ℕ) :
    ∑' n : ℕ, vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + (v + w)))
      ≤ (k.factorial : ℝ) / v ^ k * (1/w + 2) := by
  have hvk : (0:ℝ) < v ^ k := by positivity
  have hbase : Summable (fun n : ℕ => vonMangoldt n * (n : ℝ) ^ (-(1 + w))) :=
    Census.summable_vonMangoldt_rpow hw
  have hmaj : Summable (fun n : ℕ => (k.factorial : ℝ) / v ^ k
      * (vonMangoldt n * (n : ℝ) ^ (-(1 + w)))) := hbase.mul_left _
  have hterm : ∀ n : ℕ,
      vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + (v + w)))
        ≤ (k.factorial : ℝ) / v ^ k * (vonMangoldt n * (n : ℝ) ^ (-(1 + w))) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hΛ : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hlp := log_pow_le_rpow hv k hn
    have hsplit : (n : ℝ) ^ (-(1 + (v + w))) * (n : ℝ) ^ v = (n : ℝ) ^ (-(1 + w)) := by
      rw [← Real.rpow_add hn0]
      ring_nf
    have hrp : (0:ℝ) < (n : ℝ) ^ (-(1 + (v + w))) := Real.rpow_pos_of_pos hn0 _
    have hstep : (Real.log n) ^ k * (n : ℝ) ^ (-(1 + (v + w)))
        ≤ (k.factorial : ℝ) / v ^ k * ((n : ℝ) ^ (-(1 + w))) := by
      have := mul_le_mul_of_nonneg_right hlp hrp.le
      calc (Real.log n) ^ k * (n : ℝ) ^ (-(1 + (v + w)))
          ≤ ((k.factorial : ℝ) * (n : ℝ) ^ v / v ^ k)
              * (n : ℝ) ^ (-(1 + (v + w))) := this
        _ = (k.factorial : ℝ) / v ^ k
              * ((n : ℝ) ^ (-(1 + (v + w))) * (n : ℝ) ^ v) := by ring
        _ = (k.factorial : ℝ) / v ^ k * ((n : ℝ) ^ (-(1 + w))) := by rw [hsplit]
    calc vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + (v + w)))
        = vonMangoldt n * ((Real.log n) ^ k * (n : ℝ) ^ (-(1 + (v + w)))) := by ring
      _ ≤ vonMangoldt n * ((k.factorial : ℝ) / v ^ k * ((n : ℝ) ^ (-(1 + w)))) :=
          mul_le_mul_of_nonneg_left hstep hΛ
      _ = (k.factorial : ℝ) / v ^ k * (vonMangoldt n * (n : ℝ) ^ (-(1 + w))) := by
          ring
  have hLsum : Summable (fun n : ℕ =>
      vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + (v + w)))) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) hterm hmaj
    have hΛ : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hlog : (0:ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have : (0:ℝ) ≤ (n : ℝ) ^ (-(1 + (v + w))) :=
      Real.rpow_nonneg (Nat.cast_nonneg n) _
    positivity
  calc ∑' n : ℕ, vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + (v + w)))
      ≤ ∑' n : ℕ, (k.factorial : ℝ) / v ^ k
          * (vonMangoldt n * (n : ℝ) ^ (-(1 + w))) :=
        hLsum.tsum_le_tsum hterm hmaj
    _ = (k.factorial : ℝ) / v ^ k
          * ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + w)) := tsum_mul_left
    _ ≤ (k.factorial : ℝ) / v ^ k * (1/w + 2) := by
        refine mul_le_mul_of_nonneg_left (Census.tsum_vonMangoldt_rpow_le hw hw') ?_
        positivity

/-- **The general-`k` diagonal bound, sharp form** (Z7-tzlite §4.6): for
`0 < u ≤ 1/20`, `∑ Λ(n)(log n)^k n^{−(1+u)} ≤ k!·e·(k+2)/u^{k+1}`.  Obtained
from the parametrized form at the optimal split `v = uk/(k+1)`,
`w = u/(k+1)`; the loss over the true `k!/u^{k+1}` is the factor `e(k+2)`. -/
lemma tsum_vonMangoldt_log_pow_rpow_le' {u : ℝ} (hu : 0 < u) (hu' : u ≤ 1/20)
    (k : ℕ) :
    ∑' n : ℕ, vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + u))
      ≤ (k.factorial : ℝ) * Real.exp 1 * ((k : ℝ) + 2) / u ^ (k + 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : ∑' n : ℕ, vonMangoldt n * (Real.log n) ^ (0:ℕ) * (n : ℝ) ^ (-(1 + u))
        = ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + u)) := by
      refine tsum_congr fun n => ?_
      rw [pow_zero, mul_one]
    rw [h0]
    have hbase := Census.tsum_vonMangoldt_rpow_le hu hu'
    have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have hgoal : 1/u + 2 ≤ (Nat.factorial 0 : ℝ) * Real.exp 1 * ((0:ℕ) + 2) / u ^ (0 + 1) := by
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.cast_zero, zero_add,
        pow_one]
      rw [le_div_iff₀ hu]
      have : (1/u) * u = 1 := by field_simp
      nlinarith [he, hu, hu']
    linarith
  -- the main case `k ≥ 1`
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  set v : ℝ := u * ((k:ℝ)/((k:ℝ)+1)) with hvdef
  set w : ℝ := u / ((k:ℝ)+1) with hwdef
  have hv : (0:ℝ) < v := by rw [hvdef]; positivity
  have hw : (0:ℝ) < w := by rw [hwdef]; positivity
  have hvw : v + w = u := by rw [hvdef, hwdef]; field_simp
  have hw' : w ≤ 1/20 := by
    rw [hwdef]
    have : u / ((k:ℝ)+1) ≤ u := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  have hmain := tsum_vonMangoldt_log_pow_rpow_le hv hw hw' k
  rw [hvw] at hmain
  refine le_trans hmain ?_
  -- numerics: `(1+1/k)^k ≤ e`
  have hc : (((k:ℝ)+1)/(k:ℝ)) ^ k ≤ Real.exp 1 := by
    have h1 : ((k:ℝ)+1)/(k:ℝ) ≤ Real.exp (1/(k:ℝ)) := by
      have h2 := Real.add_one_le_exp (1/(k:ℝ))
      have heq : ((k:ℝ)+1)/(k:ℝ) = 1/(k:ℝ) + 1 := by field_simp; ring
      rw [heq]; linarith
    calc (((k:ℝ)+1)/(k:ℝ)) ^ k ≤ (Real.exp (1/(k:ℝ))) ^ k :=
          pow_le_pow_left₀ (by positivity) h1 k
      _ = Real.exp ((k:ℝ) * (1/(k:ℝ))) := by
          rw [← Real.exp_nat_mul]
      _ = Real.exp 1 := by
          rw [mul_one_div, div_self (ne_of_gt hkpos)]
  have h1v : 1/v = (1/u) * (((k:ℝ)+1)/(k:ℝ)) := by
    rw [hvdef]; field_simp
  have hinv : (1/v) ^ k ≤ (1/u) ^ k * Real.exp 1 := by
    rw [h1v, mul_pow]
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hwval : 1/w + 2 = ((k:ℝ)+1)/u + 2 := by rw [hwdef]; field_simp
  calc (k.factorial : ℝ) / v ^ k * (1/w + 2)
      = (k.factorial : ℝ) * (1/v) ^ k * (((k:ℝ)+1)/u + 2) := by
        rw [hwval, one_div_pow]
        ring
    _ ≤ (k.factorial : ℝ) * ((1/u) ^ k * Real.exp 1) * (((k:ℝ)+1)/u + 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        refine mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = (k.factorial : ℝ) * Real.exp 1 * (((k:ℝ)+1) + 2*u) / u ^ (k+1) := by
        rw [one_div_pow]
        field_simp
        ring
    _ ≤ (k.factorial : ℝ) * Real.exp 1 * ((k:ℝ) + 2) / u ^ (k+1) := by
        have hup : (0:ℝ) < u ^ (k+1) := by positivity
        have hE : (0:ℝ) ≤ (k.factorial : ℝ) * Real.exp 1 := by positivity
        have hnum : (k.factorial : ℝ) * Real.exp 1 * (((k:ℝ)+1) + 2*u)
            ≤ (k.factorial : ℝ) * Real.exp 1 * ((k:ℝ) + 2) :=
          mul_le_mul_of_nonneg_left (by linarith) hE
        exact div_le_div_of_nonneg_right hnum hup.le

end Diagonal

/-! ### Bridging the two sides -/

section Bridge

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- Termwise bound for the `k`-times differentiated twisted series. -/
lemma norm_term_log_pow_twist_le (χ : DirichletCharacter ℂ N) {s : ℂ} {x : ℝ}
    (hre : s.re = x) (k n : ℕ) :
    ‖LSeries.term (fun n : ℕ => (Real.log n : ℂ) ^ k
        * (χ ((n : ZMod N)) * (vonMangoldt n : ℂ))) s n‖
      ≤ vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-x) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, norm_zero,
      show vonMangoldt 0 = 0 from ArithmeticFunction.map_zero]
    simp
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hlog : (0:ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    rw [LSeries.term_of_ne_zero hn, norm_div,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), hre,
      div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlog, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have h1 := DirichletCharacter.norm_le_one χ ((n : ZMod N))
    have h2 : (0:ℝ) ≤ (Real.log n) ^ k := by positivity
    have hΛ : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have h3 : (0:ℝ) ≤ (Real.log n) ^ k * vonMangoldt n
        * (1 - ‖χ ((n : ZMod N))‖) :=
      mul_nonneg (mul_nonneg h2 hΛ) (by linarith)
    nlinarith [h3]

omit [NeZero N] in
/-- **The Dirichlet side of the representation is bounded by the diagonal.**
On the line `Re s = 1 + η`, the `k`-th derivative series is at most the
un-twisted diagonal sum `∑ Λ(n)(log n)^k n^{−(1+η)}`. -/
lemma norm_LSeries_log_pow_le (χ : DirichletCharacter ℂ N) {η : ℝ} (hη : 0 < η)
    {s : ℂ} (hre : s.re = 1 + η) (k : ℕ) :
    ‖LSeries (fun n : ℕ => (Real.log n : ℂ) ^ k
        * (χ ((n : ZMod N)) * (vonMangoldt n : ℂ))) s‖
      ≤ ∑' n : ℕ, vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + η)) := by
  have hmaj : Summable (fun n : ℕ =>
      vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + η/2 + η/2))) := by
    have hv : (0:ℝ) < η/2 := by linarith
    have hw : (0:ℝ) < η/2 := by linarith
    by_cases hsmall : η/2 ≤ 1/20
    · have hbase : Summable (fun n : ℕ => vonMangoldt n * (n : ℝ) ^ (-(1 + η/2))) :=
        Census.summable_vonMangoldt_rpow hw
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
        (hbase.mul_left ((k.factorial : ℝ) / (η/2) ^ k))
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · have hlog : (0:ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
          have h1 : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
          have h2 : (0:ℝ) ≤ (n : ℝ) ^ (-(1 + η/2 + η/2)) :=
            Real.rpow_nonneg (Nat.cast_nonneg n) _
          positivity
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
          have hΛ : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
          have hlp := log_pow_le_rpow hv k hn
          have hsplit : (n : ℝ) ^ (-(1 + η/2 + η/2)) * (n : ℝ) ^ (η/2)
              = (n : ℝ) ^ (-(1 + η/2)) := by
            rw [← Real.rpow_add hn0]
            ring_nf
          have hrp : (0:ℝ) < (n : ℝ) ^ (-(1 + η/2 + η/2)) :=
            Real.rpow_pos_of_pos hn0 _
          have hstep : (Real.log n) ^ k * (n : ℝ) ^ (-(1 + η/2 + η/2))
              ≤ (k.factorial : ℝ) / (η/2) ^ k * ((n : ℝ) ^ (-(1 + η/2))) := by
            calc (Real.log n) ^ k * (n : ℝ) ^ (-(1 + η/2 + η/2))
                ≤ ((k.factorial : ℝ) * (n : ℝ) ^ (η/2) / (η/2) ^ k)
                    * (n : ℝ) ^ (-(1 + η/2 + η/2)) :=
                  mul_le_mul_of_nonneg_right hlp hrp.le
              _ = (k.factorial : ℝ) / (η/2) ^ k
                    * ((n : ℝ) ^ (-(1 + η/2 + η/2)) * (n : ℝ) ^ (η/2)) := by ring
              _ = (k.factorial : ℝ) / (η/2) ^ k * ((n : ℝ) ^ (-(1 + η/2))) := by
                  rw [hsplit]
          calc vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + η/2 + η/2))
              = vonMangoldt n * ((Real.log n) ^ k
                  * (n : ℝ) ^ (-(1 + η/2 + η/2))) := by ring
            _ ≤ vonMangoldt n * ((k.factorial : ℝ) / (η/2) ^ k
                  * ((n : ℝ) ^ (-(1 + η/2)))) := mul_le_mul_of_nonneg_left hstep hΛ
            _ = (k.factorial : ℝ) / (η/2) ^ k
                  * (vonMangoldt n * (n : ℝ) ^ (-(1 + η/2))) := by ring
    · -- `η/2 > 1/20`: use the majorant at exponent `1 + 1/40 + 1/40`
      push Not at hsmall
      have hbase : Summable (fun n : ℕ => vonMangoldt n * (n : ℝ) ^ (-(1 + (1:ℝ)/40))) :=
        Census.summable_vonMangoldt_rpow (by norm_num)
      refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
        (hbase.mul_left ((k.factorial : ℝ) / ((1:ℝ)/40) ^ k))
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · have hlog : (0:ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
          have h1 : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
          have h2 : (0:ℝ) ≤ (n : ℝ) ^ (-(1 + η/2 + η/2)) :=
            Real.rpow_nonneg (Nat.cast_nonneg n) _
          positivity
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
          have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have hΛ : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
          have hlp := log_pow_le_rpow (v := (1:ℝ)/40) (by norm_num) k hn
          have hmono : (n : ℝ) ^ (-(1 + η/2 + η/2)) ≤ (n : ℝ) ^ (-(1 + (1:ℝ)/20)) := by
            refine Real.rpow_le_rpow_of_exponent_le hn1 ?_
            linarith
          have hsplit : (n : ℝ) ^ (-(1 + (1:ℝ)/20)) * (n : ℝ) ^ ((1:ℝ)/40)
              = (n : ℝ) ^ (-(1 + (1:ℝ)/40)) := by
            rw [← Real.rpow_add hn0]
            ring_nf
          have hlogk : (0:ℝ) ≤ (Real.log n) ^ k := by
            have : (0:ℝ) ≤ Real.log n := Real.log_nonneg hn1
            positivity
          have hstep : (Real.log n) ^ k * (n : ℝ) ^ (-(1 + η/2 + η/2))
              ≤ (k.factorial : ℝ) / ((1:ℝ)/40) ^ k * ((n : ℝ) ^ (-(1 + (1:ℝ)/40))) := by
            have h3 : (Real.log n) ^ k * (n : ℝ) ^ (-(1 + η/2 + η/2))
                ≤ (Real.log n) ^ k * (n : ℝ) ^ (-(1 + (1:ℝ)/20)) :=
              mul_le_mul_of_nonneg_left hmono hlogk
            have hrp : (0:ℝ) < (n : ℝ) ^ (-(1 + (1:ℝ)/20)) :=
              Real.rpow_pos_of_pos hn0 _
            calc (Real.log n) ^ k * (n : ℝ) ^ (-(1 + η/2 + η/2))
                ≤ (Real.log n) ^ k * (n : ℝ) ^ (-(1 + (1:ℝ)/20)) := h3
              _ ≤ ((k.factorial : ℝ) * (n : ℝ) ^ ((1:ℝ)/40) / ((1:ℝ)/40) ^ k)
                    * (n : ℝ) ^ (-(1 + (1:ℝ)/20)) :=
                  mul_le_mul_of_nonneg_right hlp hrp.le
              _ = (k.factorial : ℝ) / ((1:ℝ)/40) ^ k
                    * ((n : ℝ) ^ (-(1 + (1:ℝ)/20)) * (n : ℝ) ^ ((1:ℝ)/40)) := by ring
              _ = (k.factorial : ℝ) / ((1:ℝ)/40) ^ k
                    * ((n : ℝ) ^ (-(1 + (1:ℝ)/40))) := by rw [hsplit]
          calc vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + η/2 + η/2))
              = vonMangoldt n * ((Real.log n) ^ k
                  * (n : ℝ) ^ (-(1 + η/2 + η/2))) := by ring
            _ ≤ vonMangoldt n * ((k.factorial : ℝ) / ((1:ℝ)/40) ^ k
                  * ((n : ℝ) ^ (-(1 + (1:ℝ)/40)))) :=
                mul_le_mul_of_nonneg_left hstep hΛ
            _ = (k.factorial : ℝ) / ((1:ℝ)/40) ^ k
                  * (vonMangoldt n * (n : ℝ) ^ (-(1 + (1:ℝ)/40))) := by ring
  have hmaj' : Summable (fun n : ℕ =>
      vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + η))) := by
    have hcongr : (fun n : ℕ =>
        vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + η/2 + η/2)))
        = fun n : ℕ => vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + η)) := by
      funext n
      rw [show (-(1 + η/2 + η/2) : ℝ) = -(1 + η) from by ring]
    rwa [hcongr] at hmaj
  have hterm := norm_term_log_pow_twist_le χ hre k
  have hsummN : Summable (fun n : ℕ => ‖LSeries.term (fun n : ℕ =>
      (Real.log n : ℂ) ^ k * (χ ((n : ZMod N)) * (vonMangoldt n : ℂ))) s n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hterm hmaj'
  calc ‖LSeries (fun n : ℕ => (Real.log n : ℂ) ^ k
        * (χ ((n : ZMod N)) * (vonMangoldt n : ℂ))) s‖
      = ‖∑' n : ℕ, LSeries.term (fun n : ℕ => (Real.log n : ℂ) ^ k
          * (χ ((n : ZMod N)) * (vonMangoldt n : ℂ))) s n‖ := by rw [LSeries]
    _ ≤ ∑' n : ℕ, ‖LSeries.term (fun n : ℕ => (Real.log n : ℂ) ^ k
          * (χ ((n : ZMod N)) * (vonMangoldt n : ℂ))) s n‖ :=
        norm_tsum_le_tsum_norm hsummN
    _ ≤ ∑' n : ℕ, vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + η)) :=
        hsummN.tsum_le_tsum hterm hmaj'

/-- Mass of the zeros within `r` of `s₀ = (1+η) + iτ`, via File 3 at radius
`r + η`. -/
lemma sum_ord_near_s0_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (τ : ℝ)
    {η r : ℝ} (hη0 : 0 < η) (hr0 : 0 < r) (hr : r + η ≤ 1/20) :
    ((∑ ρ ∈ (zeroDiskFinset χ τ).filter
        (fun ρ => ‖(((1 + η : ℝ) : ℂ) + τ * I) - ρ‖ ≤ r),
      analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ)
      ≤ 5 + 2400000 * (r + η) * Real.log ((N : ℝ) * (|τ| + 2)) := by
  classical
  have hsub : (zeroDiskFinset χ τ).filter
      (fun ρ => ‖(((1 + η : ℝ) : ℂ) + τ * I) - ρ‖ ≤ r)
      ⊆ (zeroDiskFinset χ τ).filter
        (fun ρ => dist ρ (1 + τ * Complex.I) ≤ r + η) := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ ⊢
    refine ⟨hρ.1, ?_⟩
    have hstep : dist ρ (1 + (τ : ℂ) * Complex.I)
        ≤ ‖(((1 + η : ℝ) : ℂ) + τ * I) - ρ‖ + η := by
      have hd : dist ρ (1 + (τ : ℂ) * Complex.I)
          = ‖ρ - (1 + (τ : ℂ) * Complex.I)‖ := by rw [Complex.dist_eq]
      rw [hd]
      have hsplit : ρ - (1 + (τ : ℂ) * Complex.I)
          = -((((1 + η : ℝ) : ℂ) + τ * I) - ρ) + ((η : ℝ) : ℂ) := by
        push_cast; ring
      rw [hsplit]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη0]
    linarith [hρ.2]
  have hmono : ((∑ ρ ∈ (zeroDiskFinset χ τ).filter
        (fun ρ => ‖(((1 + η : ℝ) : ℂ) + τ * I) - ρ‖ ≤ r),
      analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ)
      ≤ ((∑ ρ ∈ (zeroDiskFinset χ τ).filter
        (fun ρ => dist ρ (1 + τ * Complex.I) ≤ r + η),
      analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) := by
    exact_mod_cast Finset.sum_le_sum_of_subset hsub
  refine le_trans hmono ?_
  exact sum_ord_smallDisk_le hχ τ (by linarith) hr

end Bridge

/-! ### §4.4 step 2: the Turán power-sum event over the near-zero family -/

section TuranApply

/-- `getD`-padded power sums ignore the padding: for `f 0 = 0` and a range at
least as long as the list, the range sum of `f ∘ getD` is the mapped list sum. -/
lemma sum_range_getD (f : ℂ → ℂ) (hf : f 0 = 0) :
    ∀ (l : List ℂ) {n : ℕ}, l.length ≤ n →
      ∑ i ∈ Finset.range n, f (l.getD i 0) = (l.map f).sum := by
  intro l
  induction l with
  | nil =>
    intro n _
    simp [hf]
  | cons a t ih =>
    intro n hn
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := by
      have : 1 ≤ n := le_trans (by simp) hn
      exact ⟨n - 1, by omega⟩
    rw [Finset.sum_range_succ']
    have hlen : t.length ≤ n' := by
      have := hn
      simp only [List.length_cons] at this
      omega
    have hstep : ∀ i : ℕ, (a :: t).getD (i + 1) 0 = t.getD i 0 := fun i => rfl
    have hzero : (a :: t).getD 0 0 = a := rfl
    simp only [hstep, hzero]
    rw [ih hlen, List.map_cons, List.sum_cons]
    ring

/-- Sums over `Multiset.bind` decompose. -/
lemma sum_multiset_bind {α : Type*} (s : Multiset α) (f : α → Multiset ℂ) :
    (s.bind f).sum = (s.map fun a => (f a).sum).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [ih]

/-- **Turán's second main theorem over a multiplicity-weighted family.**
A finite family `S` of total multiplicity `≤ N` containing a designated point
`ρ₀` of positive multiplicity nearest to `s₀` admits an exponent
`k ∈ [M₀+1, M₀+N]` at which the weighted inverse-power sum is at least
`(N/(8e(M₀+N)))^N · t^k`, for any `0 ≤ t` with `t·‖s₀ − ρ₀‖ ≤ 1`. -/
lemma turan_family_power_sum {S : Finset ℂ} (m : ℂ → ℕ) {s₀ ρ₀ : ℂ}
    {N M₀ : ℕ} (hN : 1 ≤ N) (hmass : ∑ ρ ∈ S, m ρ ≤ N)
    (hρ₀ : ρ₀ ∈ S) (hm₀ : 1 ≤ m ρ₀) (hs₀ : s₀ ≠ ρ₀)
    (hmin : ∀ ρ ∈ S, ‖s₀ - ρ₀‖ ≤ ‖s₀ - ρ‖)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : t * ‖s₀ - ρ₀‖ ≤ 1) :
    ∃ k : ℕ, M₀ + 1 ≤ k ∧ k ≤ M₀ + N ∧
      ((N : ℝ) / (8 * Real.exp 1 * (M₀ + N))) ^ N * t ^ k
        ≤ ‖∑ ρ ∈ S, (m ρ : ℂ) / (s₀ - ρ) ^ k‖ := by
  classical
  set w : ℂ := (s₀ - ρ₀)⁻¹ with hwdef
  set B : Multiset ℂ := S.val.bind fun ρ => Multiset.replicate (m ρ) ((s₀ - ρ)⁻¹)
    with hBdef
  have hwB : w ∈ B := by
    rw [hBdef, Multiset.mem_bind]
    exact ⟨ρ₀, hρ₀, Multiset.mem_replicate.mpr ⟨by omega, rfl⟩⟩
  obtain ⟨B', hB'⟩ := Multiset.exists_cons_of_mem hwB
  set l : List ℂ := w :: B'.toList with hldef
  have hlB : (l : Multiset ℂ) = B := by
    rw [hldef, hB', ← Multiset.cons_coe, Multiset.coe_toList]
  have hcard : Multiset.card B = ∑ ρ ∈ S, m ρ := by
    rw [hBdef, Multiset.card_bind]
    show (S.val.map fun ρ => Multiset.card
      (Multiset.replicate (m ρ) ((s₀ - ρ)⁻¹))).sum = (S.val.map fun ρ => m ρ).sum
    simp only [Multiset.card_replicate]
  have hlen : l.length ≤ N := by
    have h1 : l.length = Multiset.card B := by
      rw [← hlB, Multiset.coe_card]
    omega
  have hwpos : 0 < ‖s₀ - ρ₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs₀)
  have hnormw : ‖w‖ = ‖s₀ - ρ₀‖⁻¹ := by rw [hwdef, norm_inv]
  have hmaxB : ∀ x ∈ B, ‖x‖ ≤ ‖w‖ := by
    intro x hx
    rw [hBdef, Multiset.mem_bind] at hx
    obtain ⟨ρ, hρS, hxr⟩ := hx
    rw [Multiset.eq_of_mem_replicate hxr, norm_inv, hnormw]
    exact (inv_le_inv₀ (lt_of_lt_of_le hwpos (hmin ρ hρS)) hwpos).mpr (hmin ρ hρS)
  set z : Fin N → ℂ := fun i => l.getD i 0 with hzdef
  have hz0 : z ⟨0, hN⟩ = w := rfl
  have hmax : ∀ j, ‖z j‖ ≤ ‖z ⟨0, hN⟩‖ := by
    intro j
    rw [hz0, hzdef]
    simp only
    rcases lt_or_ge (j : ℕ) l.length with hj | hj
    · have hmem : l.getD (j : ℕ) 0 ∈ l := by
        rw [List.getD_eq_getElem l 0 hj]
        exact List.getElem_mem hj
      refine hmaxB _ ?_
      rw [← hlB]
      exact_mod_cast hmem
    · rw [List.getD_eq_default _ _ hj]
      simp
  have htw : t ≤ ‖z ⟨0, hN⟩‖ := by
    rw [hz0, hnormw, ← one_div, le_div_iff₀ hwpos]
    exact ht
  obtain ⟨k, hk1, hk2, hk3⟩ := Turan.turan_power_sum_max_lb hN M₀ z ht0 hmax htw
  have hk0 : k ≠ 0 := by omega
  have hps : ∑ j, z j ^ k = ∑ ρ ∈ S, (m ρ : ℂ) / (s₀ - ρ) ^ k := by
    have h1 : ∑ j, z j ^ k
        = ∑ i ∈ Finset.range N, (fun x : ℂ => x ^ k) (l.getD i 0) :=
      Fin.sum_univ_eq_sum_range (fun i : ℕ => (l.getD i 0) ^ k) N
    rw [h1, sum_range_getD (fun x : ℂ => x ^ k) (zero_pow hk0) l hlen]
    have h2 : (l.map fun x : ℂ => x ^ k).sum
        = ((l : Multiset ℂ).map fun x : ℂ => x ^ k).sum := by
      rw [Multiset.map_coe, Multiset.sum_coe]
    rw [h2, hlB, hBdef, Multiset.map_bind, sum_multiset_bind]
    have h3 : ∀ ρ : ℂ, ((Multiset.replicate (m ρ) ((s₀ - ρ)⁻¹)).map
          fun x : ℂ => x ^ k).sum = (m ρ : ℂ) / (s₀ - ρ) ^ k := by
      intro ρ
      rw [Multiset.map_replicate, Multiset.sum_replicate, nsmul_eq_mul, inv_pow,
        div_eq_mul_inv]
    show (S.val.map fun ρ => ((Multiset.replicate (m ρ) ((s₀ - ρ)⁻¹)).map
        fun x : ℂ => x ^ k).sum).sum = _
    rw [show (S.val.map fun ρ => ((Multiset.replicate (m ρ) ((s₀ - ρ)⁻¹)).map
        fun x : ℂ => x ^ k).sum) = S.val.map fun ρ => (m ρ : ℂ) / (s₀ - ρ) ^ k from
      Multiset.map_congr rfl fun ρ _ => h3 ρ]
    rfl
  exact ⟨k, hk1, hk2, by rwa [hps] at hk3⟩


/-- Zeros left of `Re = 1` recede from `s₀ = (1+η)+iτ` at least as fast as
from `1+iτ`: the annulus comparison of §4.4 step 3. -/
lemma dist_one_le_norm_sub {η τ : ℝ} (hη : 0 ≤ η) {ρ : ℂ} (hρ : ρ.re < 1) :
    dist ρ ((1 : ℂ) + τ * I) ≤ ‖(((1 + η : ℝ) : ℂ) + τ * I) - ρ‖ := by
  have h1 : dist ρ ((1:ℂ) + τ * I) = ‖((1:ℂ) + τ * I) - ρ‖ := by
    rw [Complex.dist_eq, ← norm_neg]
    congr 1
    ring
  rw [h1]
  have e1 : ‖((1:ℂ) + τ * I) - ρ‖ ^ 2
      = (1 - ρ.re) * (1 - ρ.re) + (τ - ρ.im) * (τ - ρ.im) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
  have e2 : ‖(((1 + η : ℝ) : ℂ) + τ * I) - ρ‖ ^ 2
      = (1 + η - ρ.re) * (1 + η - ρ.re) + (τ - ρ.im) * (τ - ρ.im) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
  have hsq : ‖((1:ℂ) + τ * I) - ρ‖ ^ 2 ≤ ‖(((1 + η : ℝ) : ℂ) + τ * I) - ρ‖ ^ 2 := by
    rw [e1, e2]
    nlinarith [mul_nonneg hη (le_of_lt (sub_pos.mpr hρ))]
  have hu := norm_nonneg (((1:ℂ) + τ * I) - ρ)
  have hv := norm_nonneg ((((1 + η : ℝ) : ℂ) + τ * I) - ρ)
  nlinarith [hsq, hu, hv]

end TuranApply

/-! ### §4.4 step 2: the Turán event -/

section Step2

variable {N : ℕ} [NeZero N]

/-- Zeros within `1/2` of `1 + iτ` belong to the Landau disk Finset. -/
lemma mem_zeroDiskFinset_of_near {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {τ : ℝ}
    {ρ : ℂ} (hzero : DirichletCharacter.LFunction χ ρ = 0)
    {r : ℝ} (hr : r ≤ 1/2) (hρ : dist ρ (1 + τ * Complex.I) ≤ r) :
    ρ ∈ zeroDiskFinset χ τ := by
  rw [mem_zeroDiskFinset hχ]
  refine ⟨?_, hzero⟩
  rw [mem_closedBall]
  have h1 : dist ((1:ℂ) + τ * Complex.I) ((2:ℂ) + τ * I) = 1 := by
    rw [Complex.dist_eq]
    have : ((1:ℂ) + τ * Complex.I) - ((2:ℂ) + τ * I) = -1 := by ring
    rw [this, norm_neg, norm_one]
  calc dist ρ ((2:ℂ) + τ * I)
      ≤ dist ρ ((1:ℂ) + τ * Complex.I) + dist ((1:ℂ) + τ * Complex.I) ((2:ℂ) + τ * I) :=
        dist_triangle _ _ _
    _ ≤ r + 1 := by rw [h1]; linarith
    _ ≤ 13/8 := by linarith

/-- Every Landau-disk zero has real part `< 1`. -/
lemma re_lt_one_of_mem_zeroDiskFinset {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {τ : ℝ}
    {ρ : ℂ} (hρ : ρ ∈ zeroDiskFinset χ τ) : ρ.re < 1 := by
  by_contra hcon
  push Not at hcon
  exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hcon)
    ((mem_zeroDiskFinset hχ).mp hρ).2

/-- **§4.4 step 2: the Turán event over the `6η`-family.**  Given a zero within
`η` of `1 + iτ` and a mass bound `Nz ≥ 1` for the `6η`-disk, some exponent
`k ∈ [M₀+1, M₀+Nz]` has a large weighted inverse-power sum at `s₀ = (1+η)+iτ`,
with floor `(Nz/(8e(M₀+Nz)))^{Nz}·(2η)^{−k}`. -/
lemma exists_turan_index {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (τ : ℝ)
    {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1/2) {Nz : ℕ} (hNz : 1 ≤ Nz)
    (hmass : ((∑ ρ ∈ (zeroDiskFinset χ τ).filter
        (fun ρ => dist ρ (1 + τ * Complex.I) ≤ 6 * η),
        analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) ≤ Nz)
    (hzero : ∃ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 ∧
      dist ρ (1 + τ * Complex.I) ≤ η)
    (M₀ : ℕ) :
    ∃ k : ℕ, M₀ + 1 ≤ k ∧ k ≤ M₀ + Nz ∧
      ((Nz : ℝ) / (8 * Real.exp 1 * (M₀ + Nz))) ^ Nz * (1 / (2 * η)) ^ k
        ≤ ‖∑ ρ ∈ (zeroDiskFinset χ τ).filter
            (fun ρ => dist ρ (1 + τ * Complex.I) ≤ 6 * η),
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
              / ((((1 + η : ℝ) : ℂ) + τ * I) - ρ) ^ k‖ := by
  obtain ⟨ρ₁, hρ₁z, hρ₁d⟩ := hzero
  set s₀ : ℂ := ((1 + η : ℝ) : ℂ) + τ * I with hs₀def
  set S := (zeroDiskFinset χ τ).filter
    (fun ρ => dist ρ (1 + τ * Complex.I) ≤ 6 * η) with hSdef
  have hρ₁S : ρ₁ ∈ S := by
    rw [hSdef, Finset.mem_filter]
    refine ⟨mem_zeroDiskFinset_of_near hχ hρ₁z hη hρ₁d, ?_⟩
    linarith
  obtain ⟨ρ₀, hρ₀S, hmin⟩ := Finset.exists_min_image S (fun ρ => ‖s₀ - ρ‖) ⟨ρ₁, hρ₁S⟩
  have hρ₀D : ρ₀ ∈ zeroDiskFinset χ τ := (Finset.mem_filter.mp hρ₀S).1
  have hmassN : ∑ ρ ∈ S, analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ ≤ Nz := by
    exact_mod_cast hmass
  have hm₀ : 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ₀ :=
    one_le_ord_of_mem_zeroDiskFinset hχ hρ₀D
  have hs₀ne : s₀ ≠ ρ₀ := by
    intro h
    have h1 : s₀.re = 1 + η := by rw [hs₀def]; simp
    have h2 := re_lt_one_of_mem_zeroDiskFinset hχ hρ₀D
    rw [← h, h1] at h2
    linarith
  -- the designated zero is within `2η` of `s₀`
  have hnear : ‖s₀ - ρ₁‖ ≤ 2 * η := by
    have hsplit : s₀ - ρ₁ = ((η : ℝ) : ℂ) + (((1:ℂ) + τ * Complex.I) - ρ₁) := by
      rw [hs₀def]; push_cast; ring
    rw [hsplit]
    refine le_trans (norm_add_le _ _) ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη0, ← Complex.dist_eq, dist_comm]
    linarith
  have ht : (1 / (2 * η)) * ‖s₀ - ρ₀‖ ≤ 1 := by
    have h1 : ‖s₀ - ρ₀‖ ≤ 2 * η := le_trans (hmin ρ₁ hρ₁S) hnear
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    exact h1
  exact turan_family_power_sum (fun ρ => analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)
    hNz hmassN hρ₀S hm₀ hs₀ne hmin (by positivity) ht

end Step2

/-! ### Numeric budgets (all seven, at the adjudicated numerals) -/

section Budgets

/-- `N ≤ 2^N` in `ℝ`. -/
lemma nat_le_two_pow (N : ℕ) : (N : ℝ) ≤ 2 ^ N := by
  have := Nat.lt_two_pow_self (n := N)
  exact_mod_cast this.le

/-- `N·a^N ≤ b^N` whenever `2a ≤ b`, `a ≥ 0`. -/
lemma nat_mul_pow_le_pow {a b : ℝ} (N : ℕ) (ha : 0 ≤ a) (hab : 2 * a ≤ b) :
    (N : ℝ) * a ^ N ≤ b ^ N := by
  calc (N : ℝ) * a ^ N ≤ 2 ^ N * a ^ N :=
        mul_le_mul_of_nonneg_right (nat_le_two_pow N) (by positivity)
    _ = (2 * a) ^ N := by rw [mul_pow]
    _ ≤ b ^ N := pow_le_pow_left₀ (by positivity) hab N

/-- The Turán per-zero constant `T = 56e` lies in `(152, 153)`. -/
lemma turan_const_bounds : (152 : ℝ) < 56 * Real.exp 1 ∧ 56 * Real.exp 1 < 153 := by
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.exp_one_lt_d9
  constructor <;> linarith

/-- The frozen floor `Q` as a single fraction. -/
lemma turan_floor_eq {η : ℝ} (hη0 : 0 < η) (N k : ℕ) :
    (1 / (56 * Real.exp 1)) ^ N * (1 / (2 * η)) ^ k / 8
      = 1 / (8 * (56 * Real.exp 1) ^ N * (2 * η) ^ k) := by
  rw [one_div_pow, one_div_pow]
  have h1 : (0:ℝ) < (56 * Real.exp 1) ^ N := by positivity
  have h2 : (0:ℝ) < (2 * η) ^ k := by positivity
  field_simp

/-- Stirling floor: `((j+1)/e)^{j+1} ≤ (j+1)!`. -/
lemma factorial_ge_div_exp_pow (m : ℕ) :
    ((m : ℝ) / Real.exp 1) ^ m ≤ (m.factorial : ℝ) := by
  have h := pow_le_factorial_mul_exp (Nat.cast_nonneg m) m
  have he : Real.exp (m : ℝ) = (Real.exp 1) ^ m := by
    rw [← Real.exp_one_pow]
  rw [he] at h
  rw [div_pow, div_le_iff₀ (by positivity)]
  exact h

/-- **Budget B1 (far zeros).** -/
lemma budget_far {η L A : ℝ} {N k j : ℕ} (hη0 : 0 < η) (hη : η ≤ 1/5000)
    (hL : 0 ≤ L) (hNL : 28800000 * η * L ≤ (N:ℝ) - 6) (hN : (41:ℝ) ≤ N)
    (hk1 : 6 * N + 1 ≤ k) (hkj : k = j + 2)
    (hA : A ≤ (1/η) * (1/η + 2 + 1040000 * L)) :
    A / (6 * η) ^ j ≤ (1 / (56 * Real.exp 1)) ^ N * (1 / (2 * η)) ^ k / 8 := by
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 56 * Real.exp 1 := ⟨_, rfl⟩
  have hT := turan_const_bounds
  rw [← hTdef] at hT
  have hT0 : (0:ℝ) < T := by linarith [hT.1]
  rw [turan_floor_eq hη0, ← hTdef]
  have hTN : (0:ℝ) < T ^ N := by positivity
  have h2η : (0:ℝ) < (2 * η) ^ k := by positivity
  have h6η : (0:ℝ) < (6 * η) ^ j := by positivity
  rw [div_le_div_iff₀ h6η (by positivity)]
  -- reduce to `32·A·η²·T^N ≤ 3^j`
  have hAη : A * η ^ 2 ≤ 1 + 2 * η + 1040000 * η * L := by
    have := mul_le_mul_of_nonneg_right hA (sq_nonneg η)
    calc A * η ^ 2 ≤ (1/η) * (1/η + 2 + 1040000 * L) * η ^ 2 := this
      _ = 1 + 2 * η + 1040000 * η * L := by field_simp
  have hηL : 0 ≤ η * L := by positivity
  have h32 : 32 * (A * η ^ 2) ≤ 2 * (N : ℝ) := by nlinarith
  have hN3 : 3 ≤ N := by
    have : (3:ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hp1 : (3:ℝ) ^ (6 * N) ≤ 3 ^ (j + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hp2 : (3:ℝ) ^ (6 * N) = 729 ^ N := by rw [pow_mul]; norm_num
  have hp3 : (4 * T) ^ N ≤ (729:ℝ) ^ N :=
    pow_le_pow_left₀ (by positivity) (by linarith [hT.2]) N
  have hp4 : (4 * T) ^ N = (4:ℝ) ^ N * T ^ N := mul_pow _ _ _
  have hp5 : (6:ℝ) * N ≤ 4 ^ N := by
    have ha : (N:ℝ) ≤ 2 ^ N := nat_le_two_pow N
    have hb : (8:ℝ) ≤ 2 ^ N := by
      have := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hN3
      norm_num at this
      exact this
    have hc : (4:ℝ) ^ N = 2 ^ N * 2 ^ N := by
      rw [← mul_pow]; norm_num
    rw [hc]
    nlinarith
  have hp6 : (6:ℝ) * N * T ^ N ≤ 3 * 3 ^ j := by
    calc (6:ℝ) * N * T ^ N ≤ 4 ^ N * T ^ N :=
          mul_le_mul_of_nonneg_right hp5 hTN.le
      _ = (4 * T) ^ N := hp4.symm
      _ ≤ 729 ^ N := hp3
      _ = 3 ^ (6 * N) := hp2.symm
      _ ≤ 3 ^ (j + 1) := hp1
      _ = 3 * 3 ^ j := by rw [pow_succ]; ring
  have key : A * 8 * T ^ N * (2 * η) ^ 2 ≤ 3 ^ j := by
    have : A * 8 * T ^ N * (2 * η) ^ 2 = 32 * (A * η ^ 2) * T ^ N := by ring
    rw [this]
    calc 32 * (A * η ^ 2) * T ^ N ≤ 2 * (N:ℝ) * T ^ N :=
          mul_le_mul_of_nonneg_right h32 hTN.le
      _ ≤ 3 ^ j := by linarith
  have hsplit : (2 * η) ^ k = (2 * η) ^ j * (2 * η) ^ 2 := by
    rw [hkj, pow_add]
  have h6 : (6 * η) ^ j = 3 ^ j * (2 * η) ^ j := by
    rw [← mul_pow]; congr 1; ring
  rw [hsplit, h6]
  calc A * (8 * T ^ N * ((2 * η) ^ j * (2 * η) ^ 2))
      = (A * 8 * T ^ N * (2 * η) ^ 2) * (2 * η) ^ j := by ring
    _ ≤ 3 ^ j * (2 * η) ^ j := mul_le_mul_of_nonneg_right key (by positivity)
    _ = 1 * (3 ^ j * (2 * η) ^ j) := by ring

/-- **Budget B2 (Cauchy remainder).** -/
lemma budget_cauchy {η L C : ℝ} {N k j : ℕ} (hη0 : 0 < η) (hη : η ≤ 1/5000)
    (hL : 0 ≤ L) (hNL : 28800000 * η * L ≤ (N:ℝ) - 6)
    (hk1 : 6 * N + 1 ≤ k) (hkj : k = j + 2)
    (hC : C ≤ 1040000 * L) :
    C * 2 ^ (j + 1) ≤ (1 / (56 * Real.exp 1)) ^ N * (1 / (2 * η)) ^ k / 8 := by
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 56 * Real.exp 1 := ⟨_, rfl⟩
  have hT := turan_const_bounds
  rw [← hTdef] at hT
  have hT0 : (0:ℝ) < T := by linarith [hT.1]
  rw [turan_floor_eq hη0, ← hTdef]
  have hTN : (0:ℝ) < T ^ N := by positivity
  rw [le_div_iff₀ (by positivity)]
  have hsplit : (2 * η) ^ k = (2 * η) ^ (j + 1) * (2 * η) := by
    rw [hkj, show j + 2 = (j + 1) + 1 from rfl, pow_succ]
  have hcomb : (2:ℝ) ^ (j + 1) * (2 * η) ^ (j + 1) = (4 * η) ^ (j + 1) := by
    rw [← mul_pow]; congr 1; ring
  have hCη : C * η ≤ (N:ℝ) / 27 := by
    have h1 : C * η ≤ 1040000 * L * η := mul_le_mul_of_nonneg_right hC hη0.le
    have h2 : 27 * (1040000 * L * η) ≤ 28800000 * η * L := by nlinarith [mul_nonneg hL hη0.le]
    linarith
  have hgeom : (4 * η) ^ (j + 1) ≤ (1 / 1250 ^ 6) ^ N := by
    calc (4 * η) ^ (j + 1) ≤ (1 / 1250) ^ (j + 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ (1 / 1250) ^ (6 * N) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = (1 / 1250 ^ 6) ^ N := by rw [pow_mul]; norm_num
  have hmain : (N:ℝ) * (T / 1250 ^ 6) ^ N ≤ 1 := by
    have := nat_mul_pow_le_pow (a := T / 1250 ^ 6) (b := 1) N (by positivity)
      (by rw [mul_div_assoc']; rw [div_le_one (by norm_num)]; linarith [hT.2])
    simpa using this
  calc C * 2 ^ (j + 1) * (8 * T ^ N * (2 * η) ^ k)
      = 16 * (C * η) * ((2:ℝ) ^ (j + 1) * (2 * η) ^ (j + 1)) * T ^ N := by
        rw [hsplit]; ring
    _ = 16 * (C * η) * (4 * η) ^ (j + 1) * T ^ N := by rw [hcomb]
    _ ≤ 16 * ((N:ℝ) / 27) * (1 / 1250 ^ 6) ^ N * T ^ N := by
        gcongr
    _ = (16 / 27) * ((N:ℝ) * (T / 1250 ^ 6) ^ N) := by
        rw [div_pow, one_pow, div_pow]; ring
    _ ≤ (16 / 27) * 1 := by gcongr
    _ ≤ 1 := by norm_num

/-- **Budget B3 (prime powers).** -/
lemma budget_primepow {η : ℝ} {N k j : ℕ} (hη0 : 0 < η) (hη : η ≤ 1/5000)
    (hk1 : 6 * N + 1 ≤ k) (hkj : k = j + 2) :
    150 * 4 ^ (j + 1) ≤ (1 / (56 * Real.exp 1)) ^ N * (1 / (2 * η)) ^ k / 8 := by
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 56 * Real.exp 1 := ⟨_, rfl⟩
  have hT := turan_const_bounds
  rw [← hTdef] at hT
  have hT0 : (0:ℝ) < T := by linarith [hT.1]
  rw [turan_floor_eq hη0, ← hTdef]
  have hTN : (0:ℝ) < T ^ N := by positivity
  rw [le_div_iff₀ (by positivity)]
  have hsplit : (2 * η) ^ k = (2 * η) ^ (j + 1) * (2 * η) := by
    rw [hkj, show j + 2 = (j + 1) + 1 from rfl, pow_succ]
  have hcomb : (4:ℝ) ^ (j + 1) * (2 * η) ^ (j + 1) = (8 * η) ^ (j + 1) := by
    rw [← mul_pow]; congr 1; ring
  have hgeom : (8 * η) ^ (j + 1) ≤ (1 / 625 ^ 6) ^ N := by
    calc (8 * η) ^ (j + 1) ≤ (1 / 625) ^ (j + 1) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ (1 / 625) ^ (6 * N) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = (1 / 625 ^ 6) ^ N := by rw [pow_mul]; norm_num
  have hmain : (T / 625 ^ 6) ^ N ≤ 1 :=
    pow_le_one₀ (by positivity) (by rw [div_le_one (by norm_num)]; linarith [hT.2])
  calc 150 * (4:ℝ) ^ (j + 1) * (8 * T ^ N * (2 * η) ^ k)
      = 2400 * η * ((4:ℝ) ^ (j + 1) * (2 * η) ^ (j + 1)) * T ^ N := by
        rw [hsplit]; ring
    _ = 2400 * η * (8 * η) ^ (j + 1) * T ^ N := by rw [hcomb]
    _ ≤ 2400 * η * (1 / 625 ^ 6) ^ N * T ^ N := by gcongr
    _ = 2400 * η * (T / 625 ^ 6) ^ N := by
        rw [div_pow, one_pow, div_pow]; ring
    _ ≤ 2400 * (1/5000) * 1 := by gcongr
    _ ≤ 1 := by norm_num

/-- **Budget B4 (primes below `X₁`).** -/
lemma budget_low {η : ℝ} {N M k j : ℕ} (hη0 : 0 < η) (hη : η ≤ 1/5000)
    (hN5 : 5 ≤ N) (hM : M = 6 * N)
    (hk1 : 6 * N + 1 ≤ k) (hkj : k = j + 2) :
    ((M:ℝ) / (16 * η)) ^ (j + 1) * (1 / η + 2)
      ≤ ((j + 1).factorial : ℝ)
        * ((1 / (56 * Real.exp 1)) ^ N * (1 / (2 * η)) ^ k / 8) := by
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 56 * Real.exp 1 := ⟨_, rfl⟩
  have hT := turan_const_bounds
  rw [← hTdef] at hT
  have hT0 : (0:ℝ) < T := by linarith [hT.1]
  have hE := Real.exp_one_lt_three
  have hE0 := Real.exp_pos 1
  rw [turan_floor_eq hη0, ← hTdef]
  have hTN : (0:ℝ) < T ^ N := by positivity
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  have hsplit : (2 * η) ^ k = (2 * η) ^ (j + 1) * (2 * η) := by
    rw [hkj, show j + 2 = (j + 1) + 1 from rfl, pow_succ]
  have hcomb : ((M:ℝ) / (16 * η)) ^ (j + 1) * (2 * η) ^ (j + 1) = ((M:ℝ) / 8) ^ (j + 1) := by
    rw [← mul_pow]; congr 1; field_simp; ring
  have hjM : M ≤ j + 1 := by omega
  have hstir : ((M:ℝ) / Real.exp 1) ^ (j + 1) ≤ ((j + 1).factorial : ℝ) := by
    refine le_trans ?_ (factorial_ge_div_exp_pow (j + 1))
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : (M:ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast hjM
    exact div_le_div_of_nonneg_right this hE0.le
  have hME : ((M:ℝ) / Real.exp 1) ^ (j + 1)
      = ((M:ℝ) / 8) ^ (j + 1) * (8 / Real.exp 1) ^ (j + 1) := by
    rw [← mul_pow]; congr 1; field_simp
  have h8E : (2 * T) ^ N ≤ (8 / Real.exp 1) ^ (j + 1) := by
    calc (2 * T) ^ N ≤ ((8 / Real.exp 1) ^ 6) ^ N := by
          refine pow_le_pow_left₀ (by positivity) ?_ N
          rw [div_pow, le_div_iff₀ (by positivity), hTdef]
          have h7 : Real.exp 1 ^ 7 ≤ 3 ^ 7 := pow_le_pow_left₀ hE0.le hE.le 7
          nlinarith [h7]
      _ = (8 / Real.exp 1) ^ (6 * N) := by rw [pow_mul]
      _ ≤ (8 / Real.exp 1) ^ (j + 1) := by
          refine pow_le_pow_right₀ ?_ (by omega)
          rw [le_div_iff₀ hE0]; linarith
  have h2N : (24:ℝ) ≤ 2 ^ N := by
    have := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hN5
    norm_num at this; linarith
  have h24 : 24 * T ^ N ≤ (8 / Real.exp 1) ^ (j + 1) := by
    calc 24 * T ^ N ≤ 2 ^ N * T ^ N := mul_le_mul_of_nonneg_right h2N hTN.le
      _ = (2 * T) ^ N := (mul_pow 2 T N).symm
      _ ≤ _ := h8E
  have hM0 : (0:ℝ) ≤ (M:ℝ) / 8 := by positivity
  calc ((M:ℝ) / (16 * η)) ^ (j + 1) * (1 / η + 2) * (8 * T ^ N * (2 * η) ^ k)
      = (((M:ℝ) / (16 * η)) ^ (j + 1) * (2 * η) ^ (j + 1))
          * ((2 * η) * (1 / η + 2)) * (8 * T ^ N) := by
        rw [hsplit]; ring
    _ = ((M:ℝ) / 8) ^ (j + 1) * (2 + 4 * η) * (8 * T ^ N) := by
        rw [hcomb]; congr 1; congr 1; field_simp; ring
    _ ≤ ((M:ℝ) / 8) ^ (j + 1) * 3 * (8 * T ^ N) := by gcongr; linarith
    _ = ((M:ℝ) / 8) ^ (j + 1) * (24 * T ^ N) := by ring
    _ ≤ ((M:ℝ) / 8) ^ (j + 1) * (8 / Real.exp 1) ^ (j + 1) :=
        mul_le_mul_of_nonneg_left h24 (by positivity)
    _ = ((M:ℝ) / Real.exp 1) ^ (j + 1) := hME.symm
    _ ≤ ((j + 1).factorial : ℝ) := hstir

/-- **Budget B5 (primes above `X₂`).** -/
lemma budget_high {η : ℝ} {N M k j : ℕ} (hη0 : 0 < η)
    (hN1 : 1 ≤ N) (hM : M = 6 * N)
    (hk2 : k ≤ 7 * N) (hkj : k = j + 2) :
    Real.exp (-(8 * (M:ℝ))) * (((j + 1).factorial : ℝ) * Real.exp 1 * ((j:ℝ) + 1 + 2)
        / (η / 2) ^ (j + 2))
      ≤ ((j + 1).factorial : ℝ)
        * ((1 / (56 * Real.exp 1)) ^ N * (1 / (2 * η)) ^ k / 8) := by
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 56 * Real.exp 1 := ⟨_, rfl⟩
  have hT := turan_const_bounds
  rw [← hTdef] at hT
  have hT0 : (0:ℝ) < T := by linarith [hT.1]
  have hE := Real.exp_one_lt_three
  have hE0 := Real.exp_pos 1
  rw [turan_floor_eq hη0, ← hTdef]
  have hTN : (0:ℝ) < T ^ N := by positivity
  have hfac : (0:ℝ) < ((j + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hη2 : (0:ℝ) < (η / 2) ^ (j + 2) := by positivity
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  -- `(2/η)^(j+2)·(2η)^(j+2) = 4^k`
  have hcomb : (2 * η) ^ k / (η / 2) ^ (j + 2) = (4:ℝ) ^ k := by
    rw [hkj, ← div_pow]; congr 1; field_simp; ring
  have hexp : Real.exp (8 * (M:ℝ)) = (Real.exp 48) ^ N := by
    rw [← Real.exp_nat_mul, hM]; push_cast; ring_nf
  have hj3 : (j:ℝ) + 1 + 2 ≤ 8 * N := by
    have hN1' : (1:ℝ) ≤ N := by exact_mod_cast hN1
    have : ((k:ℕ):ℝ) ≤ 7 * N := by exact_mod_cast hk2
    have hk' : (k:ℝ) = j + 2 := by exact_mod_cast hkj
    linarith
  have h4k : (4:ℝ) ^ k ≤ 16384 ^ N := by
    calc (4:ℝ) ^ k ≤ 4 ^ (7 * N) := pow_le_pow_right₀ (by norm_num) hk2
      _ = 16384 ^ N := by rw [pow_mul]; norm_num
  have he48 : (2 * (16384 * T * (64 * Real.exp 1))) ≤ Real.exp 48 := by
    have h1 : Real.exp 48 = (Real.exp 1) ^ 48 := by rw [Real.exp_one_pow]; norm_num
    have h2 : (2.7182818283 : ℝ) ^ 48 ≤ (Real.exp 1) ^ 48 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 48
    rw [h1]
    have h3 : 2 * (16384 * T * (64 * Real.exp 1)) ≤ 2 * (16384 * 153 * (64 * 3)) := by
      gcongr; exact hT.2.le
    have h4 : (2 * (16384 * 153 * (64 * 3)) : ℝ) ≤ (2.7182818283 : ℝ) ^ 48 := by norm_num
    linarith
  have hmain : (N:ℝ) * (16384 * T * (64 * Real.exp 1)) ^ N ≤ (Real.exp 48) ^ N :=
    nat_mul_pow_le_pow N (by positivity) he48
  have h64 : (64 * Real.exp 1) ≤ (64 * Real.exp 1) ^ N := by
    calc (64 * Real.exp 1) = (64 * Real.exp 1) ^ 1 := (pow_one _).symm
      _ ≤ (64 * Real.exp 1) ^ N := pow_le_pow_right₀ (by linarith) hN1
  -- assemble
  have hexpneg : Real.exp (-(8 * (M:ℝ))) = 1 / Real.exp (8 * (M:ℝ)) := by
    rw [Real.exp_neg, one_div]
  rw [hexpneg]
  have hpos48 : (0:ℝ) < Real.exp (8 * (M:ℝ)) := Real.exp_pos _
  have hgoal : 8 * Real.exp 1 * ((j:ℝ) + 1 + 2) * (4:ℝ) ^ k * T ^ N
      ≤ Real.exp (8 * (M:ℝ)) := by
    calc 8 * Real.exp 1 * ((j:ℝ) + 1 + 2) * (4:ℝ) ^ k * T ^ N
        ≤ 8 * Real.exp 1 * (8 * N) * 16384 ^ N * T ^ N := by gcongr
      _ = (N:ℝ) * (16384 * T) ^ N * (64 * Real.exp 1) := by rw [mul_pow 16384 T N]; ring
      _ ≤ (N:ℝ) * (16384 * T) ^ N * (64 * Real.exp 1) ^ N := by gcongr
      _ = (N:ℝ) * (16384 * T * (64 * Real.exp 1)) ^ N := by
          rw [mul_pow (16384 * T) (64 * Real.exp 1) N]; ring
      _ ≤ (Real.exp 48) ^ N := hmain
      _ = Real.exp (8 * (M:ℝ)) := hexp.symm
  calc 1 / Real.exp (8 * (M:ℝ)) * (((j + 1).factorial : ℝ) * Real.exp 1 * ((j:ℝ) + 1 + 2)
        / (η / 2) ^ (j + 2)) * (8 * T ^ N * (2 * η) ^ k)
      = ((j + 1).factorial : ℝ) * (8 * Real.exp 1 * ((j:ℝ) + 1 + 2)
          * ((2 * η) ^ k / (η / 2) ^ (j + 2)) * T ^ N) / Real.exp (8 * (M:ℝ)) := by
        field_simp
    _ = ((j + 1).factorial : ℝ) * (8 * Real.exp 1 * ((j:ℝ) + 1 + 2)
          * (4:ℝ) ^ k * T ^ N) / Real.exp (8 * (M:ℝ)) := by rw [hcomb]
    _ ≤ ((j + 1).factorial : ℝ) * Real.exp (8 * (M:ℝ)) / Real.exp (8 * (M:ℝ)) := by
        gcongr
    _ = ((j + 1).factorial : ℝ) := by field_simp

/-- **Budget B6 (Abel boundary at `X₂`).** -/
lemma budget_boundary {η : ℝ} {N M k j : ℕ} (hη0 : 0 < η) (hη : η ≤ 1/5000)
    (hN1 : 1 ≤ N) (hM : M = 6 * N)
    (hk1 : 6 * N + 1 ≤ k) (hk2 : k ≤ 7 * N) (hkj : k = j + 2) :
    (16 * (M:ℝ) / η) ^ (j + 1) * Real.exp (-(16 * (M:ℝ)))
        * (Real.exp 1 * (16 * (M:ℝ) / η + 2))
      ≤ ((j + 1).factorial : ℝ)
        * ((1 / (56 * Real.exp 1)) ^ N * (1 / (2 * η)) ^ k / 8) := by
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 56 * Real.exp 1 := ⟨_, rfl⟩
  have hT := turan_const_bounds
  rw [← hTdef] at hT
  have hT0 : (0:ℝ) < T := by linarith [hT.1]
  have hE := Real.exp_one_lt_three
  have hE0 := Real.exp_pos 1
  rw [turan_floor_eq hη0, ← hTdef]
  have hTN : (0:ℝ) < T ^ N := by positivity
  have hM1 : (1:ℝ) ≤ M := by
    have : 1 ≤ M := by omega
    exact_mod_cast this
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  have hsplit : (2 * η) ^ k = (2 * η) ^ (j + 1) * (2 * η) := by
    rw [hkj, show j + 2 = (j + 1) + 1 from rfl, pow_succ]
  have hcomb : (16 * (M:ℝ) / η) ^ (j + 1) * (2 * η) ^ (j + 1) = (32 * (M:ℝ)) ^ (j + 1) := by
    rw [← mul_pow]; congr 1; field_simp; ring
  have hjM : M ≤ j + 1 := by omega
  have hj7 : j + 1 ≤ 7 * N := by omega
  have hstir : ((M:ℝ) / Real.exp 1) ^ (j + 1) ≤ ((j + 1).factorial : ℝ) := by
    refine le_trans ?_ (factorial_ge_div_exp_pow (j + 1))
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : (M:ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast hjM
    exact div_le_div_of_nonneg_right this hE0.le
  have hME : ((M:ℝ) / Real.exp 1) ^ (j + 1)
      = (32 * (M:ℝ)) ^ (j + 1) * (1 / (32 * Real.exp 1)) ^ (j + 1) := by
    rw [← mul_pow]; congr 1; field_simp
  have hexp : Real.exp (16 * (M:ℝ)) = (Real.exp 96) ^ N := by
    rw [← Real.exp_nat_mul, hM]; push_cast; ring_nf
  have h32E : (32 * Real.exp 1) ^ (j + 1) ≤ ((32 * Real.exp 1) ^ 7) ^ N := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by linarith) hj7
  have he96 : 2 * ((32 * Real.exp 1) ^ 7 * T * (1584 * Real.exp 1)) ≤ Real.exp 96 := by
    have h1 : Real.exp 96 = (Real.exp 1) ^ 96 := by rw [Real.exp_one_pow]; norm_num
    have h2 : (2.7182818283 : ℝ) ^ 96 ≤ (Real.exp 1) ^ 96 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 96
    rw [h1]
    have h3 : 2 * ((32 * Real.exp 1) ^ 7 * T * (1584 * Real.exp 1))
        ≤ 2 * ((32 * 3) ^ 7 * 153 * (1584 * 3)) := by
      gcongr; linarith [hT.2]
    have h4 : (2 * ((32 * 3) ^ 7 * 153 * (1584 * 3)) : ℝ) ≤ (2.7182818283 : ℝ) ^ 96 := by
      norm_num
    linarith
  have hmain : (N:ℝ) * ((32 * Real.exp 1) ^ 7 * T * (1584 * Real.exp 1)) ^ N
      ≤ (Real.exp 96) ^ N :=
    nat_mul_pow_le_pow N (by positivity) he96
  have h1584 : (1584 * Real.exp 1) ≤ (1584 * Real.exp 1) ^ N := by
    calc (1584 * Real.exp 1) = (1584 * Real.exp 1) ^ 1 := (pow_one _).symm
      _ ≤ (1584 * Real.exp 1) ^ N := pow_le_pow_right₀ (by linarith) hN1
  have hkey : 264 * (M:ℝ) * Real.exp 1 * (32 * Real.exp 1) ^ (j + 1) * T ^ N
      ≤ Real.exp (16 * (M:ℝ)) := by
    calc 264 * (M:ℝ) * Real.exp 1 * (32 * Real.exp 1) ^ (j + 1) * T ^ N
        ≤ 264 * (M:ℝ) * Real.exp 1 * ((32 * Real.exp 1) ^ 7) ^ N * T ^ N := by gcongr
      _ = (N:ℝ) * ((32 * Real.exp 1) ^ 7 * T) ^ N * (1584 * Real.exp 1) := by
          rw [mul_pow, hM]; push_cast; ring
      _ ≤ (N:ℝ) * ((32 * Real.exp 1) ^ 7 * T) ^ N * (1584 * Real.exp 1) ^ N := by gcongr
      _ = (N:ℝ) * ((32 * Real.exp 1) ^ 7 * T * (1584 * Real.exp 1)) ^ N := by
          rw [mul_pow ((32 * Real.exp 1) ^ 7 * T)]; ring
      _ ≤ (Real.exp 96) ^ N := hmain
      _ = Real.exp (16 * (M:ℝ)) := hexp.symm
  have hexpneg : Real.exp (-(16 * (M:ℝ))) = 1 / Real.exp (16 * (M:ℝ)) := by
    rw [Real.exp_neg, one_div]
  have hpos : (0:ℝ) < Real.exp (16 * (M:ℝ)) := Real.exp_pos _
  have h32Epos : (0:ℝ) < (32 * Real.exp 1) ^ (j + 1) := by positivity
  -- reduce
  have hred : 264 * (M:ℝ) * Real.exp 1 * T ^ N / Real.exp (16 * (M:ℝ))
      ≤ (1 / (32 * Real.exp 1)) ^ (j + 1) := by
    rw [one_div_pow, div_le_div_iff₀ hpos h32Epos]
    linarith [hkey]
  rw [hexpneg]
  calc (16 * (M:ℝ) / η) ^ (j + 1) * (1 / Real.exp (16 * (M:ℝ)))
        * (Real.exp 1 * (16 * (M:ℝ) / η + 2)) * (8 * T ^ N * (2 * η) ^ k)
      = ((16 * (M:ℝ) / η) ^ (j + 1) * (2 * η) ^ (j + 1))
          * ((2 * η) * (16 * (M:ℝ) / η + 2)) * (8 * Real.exp 1 * T ^ N)
          / Real.exp (16 * (M:ℝ)) := by
        rw [hsplit]; ring
    _ = (32 * (M:ℝ)) ^ (j + 1) * (32 * M + 4 * η) * (8 * Real.exp 1 * T ^ N)
          / Real.exp (16 * (M:ℝ)) := by
        rw [hcomb]; congr 2; field_simp; ring
    _ ≤ (32 * (M:ℝ)) ^ (j + 1) * (33 * M) * (8 * Real.exp 1 * T ^ N)
          / Real.exp (16 * (M:ℝ)) := by
        gcongr; linarith
    _ = (32 * (M:ℝ)) ^ (j + 1)
          * (264 * (M:ℝ) * Real.exp 1 * T ^ N / Real.exp (16 * (M:ℝ))) := by ring
    _ ≤ (32 * (M:ℝ)) ^ (j + 1) * (1 / (32 * Real.exp 1)) ^ (j + 1) :=
        mul_le_mul_of_nonneg_left hred (by positivity)
    _ = ((M:ℝ) / Real.exp 1) ^ (j + 1) := hME.symm
    _ ≤ ((j + 1).factorial : ℝ) := hstir

/-- **Budget B7 (endgame).**  With `G = Q·η^j/68`, `η³·M·e^{6M}·(η·G²/(16M)) ≥ 1`. -/
lemma budget_endgame {η : ℝ} {N M k j : ℕ} (hη0 : 0 < η)
    (hN : (73984:ℝ) ≤ N) (hM : M = 6 * N)
    (hk2 : k ≤ 7 * N) (hkj : k = j + 2) :
    1 ≤ η ^ 3 * (M:ℝ) * Real.exp (6 * (M:ℝ))
      * (η * ((1 / (56 * Real.exp 1)) ^ N * (1 / (2 * η)) ^ k * η ^ j / 68) ^ 2
          / (16 * (M:ℝ))) := by
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 56 * Real.exp 1 := ⟨_, rfl⟩
  have hT := turan_const_bounds
  rw [← hTdef] at hT
  have hT0 : (0:ℝ) < T := by linarith [hT.1]
  have hE0 := Real.exp_pos 1
  rw [← hTdef]
  have hM0 : (0:ℝ) < M := by
    have : 0 < M := by
      have : (1:ℝ) ≤ N := by linarith
      have : 1 ≤ N := by exact_mod_cast this
      omega
    exact_mod_cast this
  have hTN : (0:ℝ) < T ^ N := by positivity
  -- normalize `G·η²`
  have hG : (1 / T) ^ N * (1 / (2 * η)) ^ k * η ^ j / 68 * η ^ 2
      = (1 / T) ^ N * (1 / 2) ^ k / 68 := by
    rw [hkj, one_div_pow, one_div_pow (2 * η), mul_pow, one_div_pow]
    field_simp
    ring
  have hexp : Real.exp (6 * (M:ℝ)) = (Real.exp 36) ^ N := by
    rw [← Real.exp_nat_mul, hM]; push_cast; ring_nf
  have h4k : (4:ℝ) ^ k ≤ 16384 ^ N := by
    calc (4:ℝ) ^ k ≤ 4 ^ (7 * N) := pow_le_pow_right₀ (by norm_num) hk2
      _ = 16384 ^ N := by rw [pow_mul]; norm_num
  have he36 : 2 * (T ^ 2 * 16384) ≤ Real.exp 36 := by
    have h1 : Real.exp 36 = (Real.exp 1) ^ 36 := by rw [Real.exp_one_pow]; norm_num
    have h2 : (2.7182818283 : ℝ) ^ 36 ≤ (Real.exp 1) ^ 36 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 36
    rw [h1]
    have h3 : 2 * (T ^ 2 * 16384) ≤ 2 * (153 ^ 2 * 16384) := by
      gcongr; exact hT.2.le
    have h4 : (2 * (153 ^ 2 * 16384) : ℝ) ≤ (2.7182818283 : ℝ) ^ 36 := by norm_num
    linarith
  have hmain : (N:ℝ) * (T ^ 2 * 16384) ^ N ≤ (Real.exp 36) ^ N :=
    nat_mul_pow_le_pow N (by positivity) he36
  have hkey : 73984 * (T ^ N) ^ 2 * (4:ℝ) ^ k ≤ Real.exp (6 * (M:ℝ)) := by
    calc 73984 * (T ^ N) ^ 2 * (4:ℝ) ^ k ≤ (N:ℝ) * (T ^ N) ^ 2 * 16384 ^ N := by gcongr
      _ = (N:ℝ) * (T ^ 2 * 16384) ^ N := by
          rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2 N]; ring
      _ ≤ (Real.exp 36) ^ N := hmain
      _ = Real.exp (6 * (M:ℝ)) := hexp.symm
  -- rewrite the goal
  have hexpr : η ^ 3 * (M:ℝ) * Real.exp (6 * (M:ℝ))
      * (η * ((1 / T) ^ N * (1 / (2 * η)) ^ k * η ^ j / 68) ^ 2 / (16 * (M:ℝ)))
      = Real.exp (6 * (M:ℝ)) * ((1 / T) ^ N * (1 / (2 * η)) ^ k * η ^ j / 68 * η ^ 2) ^ 2
          / 16 := by
    field_simp
  rw [hexpr, hG]
  rw [le_div_iff₀ (by norm_num)]
  have h4 : ((1 / T) ^ N * (1 / 2) ^ k / 68) ^ 2
      = 1 / (4624 * (T ^ N) ^ 2 * (4:ℝ) ^ k) := by
    rw [one_div_pow, one_div_pow]
    have h2k : ((2:ℝ) ^ k) ^ 2 = 4 ^ k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    field_simp
    rw [h2k]; ring
  rw [h4]
  have hpos : (0:ℝ) < 4624 * (T ^ N) ^ 2 * (4:ℝ) ^ k := by positivity
  rw [mul_one_div, le_div_iff₀ hpos]
  linarith [hkey]

end Budgets

/-! ### §4.4 step 3: from the Turán floor to the Dirichlet side -/

section Step3

variable {N : ℕ} [NeZero N]

set_option maxHeartbeats 800000 in
/-- **§4.4 step 3: from the Turán floor to the Dirichlet side.**  If the
`6η`-family power sum of order `j+2` is at least `Q`, and the far-zero and
Cauchy remainders are each at most `Q/8`, the `(j+1)`-times differentiated
twisted series at `s₀ = (1+η)+iτ` has norm at least `(j+1)!·(3/4)·Q`. -/
lemma norm_LSeries_ge_of_turan {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (τ : ℝ)
    {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1/20) (j : ℕ) {Q : ℝ}
    (hQ : Q ≤ ‖∑ ρ ∈ (zeroDiskFinset χ τ).filter
        (fun ρ => dist ρ (1 + τ * Complex.I) ≤ 6 * η),
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
          / ((((1 + η : ℝ) : ℂ) + τ * I) - ρ) ^ (j + 2)‖)
    (hfar : (1/η) * (1/η + 2 + 520000 * Real.log ((N:ℝ) * (|τ| + 2))) / (6 * η) ^ j
      ≤ Q / 8)
    (hcauchy : 520000 * Real.log ((N:ℝ) * (|τ| + 2)) * 2 ^ (j + 1) ≤ Q / 8) :
    ((j + 1).factorial : ℝ) * (3/4 * Q)
      ≤ ‖LSeries (fun n : ℕ => (Real.log n : ℂ) ^ (j + 1)
          * (χ (n : ZMod N) * (vonMangoldt n : ℂ))) (((1 + η : ℝ) : ℂ) + τ * I)‖ := by
  classical
  obtain ⟨g, hgan, hgb, hgid⟩ := exists_logDeriv_remainder hχ τ
  set s₀ : ℂ := ((1 + η : ℝ) : ℂ) + τ * I with hs₀def
  have hdist : dist s₀ ((2:ℂ) + τ * I) = 1 - η := by
    rw [Complex.dist_eq, hs₀def]
    have : ((1 + η : ℝ) : ℂ) + τ * I - ((2:ℂ) + τ * I) = ((η - 1 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; ring
  have hs₀mem : s₀ ∈ ball ((2:ℂ) + τ * I) (13/8 : ℝ) := by
    rw [mem_ball, hdist]; linarith
  have hs₀re : 1 < s₀.re := by
    rw [hs₀def]; simp; linarith
  have hrep := kderiv_representation hχ τ hgan hgid hs₀mem hs₀re (j + 1)
  have hcau := norm_iteratedDeriv_le_of_bounded_on_disk hgan hgb
    (by rw [hdist]; linarith) (j + 1)
  obtain ⟨LS, hLS⟩ : ∃ z : ℂ, z = LSeries (fun n : ℕ => (Real.log n : ℂ) ^ (j + 1)
    * (χ (n : ZMod N) * (vonMangoldt n : ℂ))) s₀ := ⟨_, rfl⟩
  obtain ⟨Sall, hSall⟩ : ∃ z : ℂ, z = ∑ ρ ∈ zeroDiskFinset χ τ,
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s₀ - ρ) ^ (j + 2) :=
    ⟨_, rfl⟩
  obtain ⟨Snear, hSnear⟩ : ∃ z : ℂ, z = ∑ ρ ∈ (zeroDiskFinset χ τ).filter
    (fun ρ => dist ρ (1 + τ * Complex.I) ≤ 6 * η),
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s₀ - ρ) ^ (j + 2) :=
    ⟨_, rfl⟩
  obtain ⟨Sfar, hSfar⟩ : ∃ z : ℂ, z = ∑ ρ ∈ (zeroDiskFinset χ τ).filter
    (fun ρ => ¬ dist ρ (1 + τ * Complex.I) ≤ 6 * η),
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s₀ - ρ) ^ (j + 2) :=
    ⟨_, rfl⟩
  rw [← hSnear] at hQ
  rw [← hLS]
  have hsplit : Sall = Snear + Sfar := by
    rw [hSall, hSnear, hSfar]
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hrep' : Sall = -(LS + (-1) ^ (j + 1) * iteratedDeriv (j + 1) g s₀)
      / ((j + 1).factorial : ℂ) := by
    rw [hSall, hLS]; exact hrep
  have hfacC : ((j + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hfac0 : (0:ℝ) < ((j + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hmul : ((j + 1).factorial : ℂ) * Sall
      = -(LS + (-1) ^ (j + 1) * iteratedDeriv (j + 1) g s₀) := by
    rw [hrep', mul_div_cancel₀ _ hfacC]
  have h1 : ((j + 1).factorial : ℝ) * ‖Sall‖
      = ‖LS + (-1) ^ (j + 1) * iteratedDeriv (j + 1) g s₀‖ := by
    rw [← Complex.norm_natCast ((j + 1).factorial), ← norm_mul, hmul, norm_neg]
  have h2 : ‖LS + (-1) ^ (j + 1) * iteratedDeriv (j + 1) g s₀‖
      ≤ ‖LS‖ + ‖iteratedDeriv (j + 1) g s₀‖ := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  -- the far zeros
  have hp : ∀ ρ ∈ (zeroDiskFinset χ τ).filter
      (fun ρ => ¬ dist ρ (1 + τ * Complex.I) ≤ 6 * η), 6 * η < ‖s₀ - ρ‖ := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    have hre := re_lt_one_of_mem_zeroDiskFinset hχ hρ.1
    have := dist_one_le_norm_sub (η := η) (τ := τ) hη0.le hre
    push Not at hρ
    linarith [hρ.2]
  have hfarnorm : ‖Sfar‖
      ≤ (1/η) * (1/η + 2 + 520000 * Real.log ((N:ℝ) * (|τ| + 2))) / (6 * η) ^ j := by
    rw [hSfar]
    exact norm_sum_far_le τ (r := 6 * η) (by positivity) j hp
      (sum_ord_div_normSq_le hχ τ hη0 hη)
  have hnear : ‖Snear‖ ≤ ‖Sall‖ + ‖Sfar‖ := by
    have : Snear = Sall - Sfar := by rw [hsplit]; ring
    rw [this]; exact norm_sub_le _ _
  -- assemble
  have hFnear : ((j + 1).factorial : ℝ) * Q ≤ ((j + 1).factorial : ℝ) * ‖Snear‖ :=
    mul_le_mul_of_nonneg_left hQ hfac0.le
  have hFfar : ((j + 1).factorial : ℝ) * ‖Sfar‖ ≤ ((j + 1).factorial : ℝ) * (Q / 8) :=
    mul_le_mul_of_nonneg_left (le_trans hfarnorm hfar) hfac0.le
  have hFall : ((j + 1).factorial : ℝ) * ‖Snear‖
      ≤ ((j + 1).factorial : ℝ) * (‖Sall‖ + ‖Sfar‖) :=
    mul_le_mul_of_nonneg_left hnear hfac0.le
  have hFg : ((j + 1).factorial : ℝ)
      * (520000 * Real.log ((N:ℝ) * (|τ| + 2)) * 2 ^ (j + 1))
      ≤ ((j + 1).factorial : ℝ) * (Q / 8) :=
    mul_le_mul_of_nonneg_left hcauchy hfac0.le
  have hcau' : ‖iteratedDeriv (j + 1) g s₀‖ ≤ ((j + 1).factorial : ℝ)
      * (520000 * Real.log ((N:ℝ) * (|τ| + 2)) * 2 ^ (j + 1)) := by
    calc ‖iteratedDeriv (j + 1) g s₀‖
        ≤ ((j + 1).factorial : ℝ) * (520000 * Real.log ((N:ℝ) * (|τ| + 2)))
            * 2 ^ (j + 1) := hcau
      _ = _ := by ring
  linarith only [hFnear, hFfar, hFall, hFg, hcau', h1, h2]

end Step3

/-! ### §4.4 step 4: the three tails -/

section Tails

/-- Summability of the `k`-th log-power diagonal at any `u > 0`. -/
lemma summable_vonMangoldt_log_pow_rpow {u : ℝ} (hu : 0 < u) (k : ℕ) :
    Summable (fun n : ℕ => vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + u))) := by
  have hv : 0 < u/2 := by linarith
  have hbase : Summable (fun n : ℕ => vonMangoldt n * (n : ℝ) ^ (-(1 + u/2))) :=
    Census.summable_vonMangoldt_rpow hv
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hbase.mul_left ((k.factorial : ℝ) / (u/2) ^ k))
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hlog : (0:ℝ) ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
      have h1 : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      have h2 : (0:ℝ) ≤ (n : ℝ) ^ (-(1 + u)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
      positivity
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hΛ : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      have hlp := log_pow_le_rpow hv k hn
      have hsplit : (n : ℝ) ^ (-(1 + u)) * (n : ℝ) ^ (u/2) = (n : ℝ) ^ (-(1 + u/2)) := by
        rw [← Real.rpow_add hn0]; ring_nf
      have hrp : (0:ℝ) < (n : ℝ) ^ (-(1 + u)) := Real.rpow_pos_of_pos hn0 _
      calc vonMangoldt n * (Real.log n) ^ k * (n : ℝ) ^ (-(1 + u))
          = vonMangoldt n * ((Real.log n) ^ k * (n : ℝ) ^ (-(1 + u))) := by ring
        _ ≤ vonMangoldt n * (((k.factorial : ℝ) * (n : ℝ) ^ (u/2) / (u/2) ^ k)
              * (n : ℝ) ^ (-(1 + u))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlp hrp.le) hΛ
        _ = (k.factorial : ℝ) / (u/2) ^ k
              * (vonMangoldt n * ((n : ℝ) ^ (-(1 + u)) * (n : ℝ) ^ (u/2))) := by ring
        _ = (k.factorial : ℝ) / (u/2) ^ k
              * (vonMangoldt n * (n : ℝ) ^ (-(1 + u/2))) := by rw [hsplit]

/-- **Prime powers are negligible**: `∑_{n not prime} Λ(n) n^{−3/4} ≤ 150`, with
summability.  The non-prime support of `Λ` is injected into `ℕ × ℕ` via
`n ↦ (minFac n, ord_{minFac n} n)` and dominated by the separated majorant
`Λ(p)p^{−3/2} · (9/4)(2/3)^a`. -/
lemma tsum_nonprime_vonMangoldt_rpow_le :
    Summable (fun n : ℕ => if n.Prime then 0 else vonMangoldt n * (n : ℝ) ^ (-(3/4 : ℝ))) ∧
    ∑' n : ℕ, (if n.Prime then 0 else vonMangoldt n * (n : ℝ) ^ (-(3/4 : ℝ))) ≤ 150 := by
  classical
  set g₁ : ℕ → ℝ := fun p => vonMangoldt p * (p : ℝ) ^ (-(3/2 : ℝ)) with hg₁
  set g₂ : ℕ → ℝ := fun a => (9/4 : ℝ) * (2/3 : ℝ) ^ a with hg₂
  have hg₁nn : ∀ p, 0 ≤ g₁ p := fun p =>
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hg₂nn : ∀ a, 0 ≤ g₂ a := fun a => by positivity
  have hg₁s : Summable g₁ := by
    have := Census.summable_vonMangoldt_rpow (u := 1/2) (by norm_num)
    refine this.congr fun n => ?_
    rw [hg₁]; norm_num
  have hg₁b : ∑' p, g₁ p ≤ 22 := by
    have hbase := Census.tsum_vonMangoldt_rpow_le (u := 1/20) (by norm_num) (by norm_num)
    have hsum20 := Census.summable_vonMangoldt_rpow (u := 1/20) (by norm_num)
    have hle : ∀ p, g₁ p ≤ vonMangoldt p * (p : ℝ) ^ (-(1 + 1/20 : ℝ)) := by
      intro p
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · simp [hg₁]
      · have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp
        refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
        exact Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
    calc ∑' p, g₁ p ≤ ∑' p, vonMangoldt p * (p : ℝ) ^ (-(1 + 1/20 : ℝ)) :=
          hg₁s.tsum_le_tsum hle hsum20
      _ ≤ 1 / (1/20) + 2 := hbase
      _ = 22 := by norm_num
  have hg₂s : Summable g₂ :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hg₂b : ∑' a, g₂ a = 27/4 := by
    rw [hg₂, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  have hgs : Summable (fun x : ℕ × ℕ => g₁ x.1 * g₂ x.2) :=
    hg₁s.mul_of_nonneg hg₂s hg₁nn hg₂nn
  -- the injection
  set ι : ℕ → ℕ × ℕ := fun n =>
    if IsPrimePow n then (n.minFac, n.factorization n.minFac) else (0, n) with hι
  have hinj : Function.Injective ι := by
    intro a b hab
    simp only [hι] at hab
    by_cases ha : IsPrimePow a <;> by_cases hb : IsPrimePow b
    · rw [if_pos ha, if_pos hb, Prod.mk.injEq] at hab
      have h1 := ha.minFac_pow_factorization_eq
      have h2 := hb.minFac_pow_factorization_eq
      rw [← h1, ← h2, hab.2, hab.1]
    · rw [if_pos ha, if_neg hb, Prod.mk.injEq] at hab
      exact absurd hab.1 (Nat.minFac_pos a).ne'
    · rw [if_neg ha, if_pos hb, Prod.mk.injEq] at hab
      exact absurd hab.1.symm (Nat.minFac_pos b).ne'
    · rw [if_neg ha, if_neg hb, Prod.mk.injEq] at hab
      exact hab.2
  -- termwise domination
  have hle : ∀ n, (if n.Prime then 0 else vonMangoldt n * (n : ℝ) ^ (-(3/4 : ℝ)))
      ≤ g₁ (ι n).1 * g₂ (ι n).2 := by
    intro n
    by_cases hp : n.Prime
    · rw [if_pos hp]; exact mul_nonneg (hg₁nn _) (hg₂nn _)
    rw [if_neg hp]
    by_cases hpp : IsPrimePow n
    · obtain ⟨p, a, hpr, ha, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
      have hιv : ι (p ^ a) = (p, a) := by
        simp only [hι, if_pos hpp, hpr.pow_minFac ha.ne', hpr.factorization_pow,
          Finsupp.single_eq_same]
      rw [hιv]
      simp only [hg₁, hg₂]
      rw [ArithmeticFunction.vonMangoldt_apply_pow ha.ne']
      have hΛ : 0 ≤ vonMangoldt p := ArithmeticFunction.vonMangoldt_nonneg
      -- `a ≥ 2`
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := by
        rcases a with _ | _ | b
        · exact absurd ha (lt_irrefl 0)
        · exact absurd (by simpa using hpr : (p ^ (0 + 1)).Prime) hp
        · exact ⟨b, rfl⟩
      have hp0 : (0:ℝ) < p := by exact_mod_cast hpr.pos
      have hp2 : (2:ℝ) ≤ p := by exact_mod_cast hpr.two_le
      set q : ℝ := (p : ℝ) ^ (-(3/4 : ℝ)) with hq
      have hq0 : 0 ≤ q := Real.rpow_nonneg hp0.le _
      have hpow : (((p ^ (b + 2) : ℕ) : ℝ)) ^ (-(3/4 : ℝ)) = q ^ (b + 2) := by
        rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, mul_comm,
          Real.rpow_mul hp0.le, Real.rpow_natCast]
      have hq2 : q ^ 2 = (p : ℝ) ^ (-(3/2 : ℝ)) := by
        rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
      have hq4 : q ^ 4 ≤ (2/3 : ℝ) ^ 4 := by
        have : q ^ 4 = ((p : ℝ) ^ 3)⁻¹ := by
          rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast,
            ← Real.rpow_neg hp0.le]
          norm_num
        rw [this]
        have h8 : (8:ℝ) ≤ (p : ℝ) ^ 3 := by
          have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hp2 3
          norm_num at this; exact this
        calc ((p : ℝ) ^ 3)⁻¹ ≤ (8:ℝ)⁻¹ := inv_anti₀ (by norm_num) h8
          _ ≤ (2/3 : ℝ) ^ 4 := by norm_num
      have hq23 : q ≤ 2/3 := (pow_le_pow_iff_left₀ hq0 (by norm_num) (by norm_num)).mp hq4
      have hqb : q ^ b ≤ (2/3 : ℝ) ^ b := pow_le_pow_left₀ hq0 hq23 b
      rw [hpow]
      calc vonMangoldt p * q ^ (b + 2) = vonMangoldt p * (q ^ 2 * q ^ b) := by ring
        _ ≤ vonMangoldt p * (q ^ 2 * (2/3 : ℝ) ^ b) := by gcongr
        _ = vonMangoldt p * (p : ℝ) ^ (-(3/2 : ℝ)) * (9/4 * (2/3 : ℝ) ^ (b + 2)) := by
            rw [hq2]; ring
    · have : vonMangoldt n = 0 := ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp
      rw [this, zero_mul]; exact mul_nonneg (hg₁nn _) (hg₂nn _)
  have hlhs : Summable (fun n : ℕ =>
      if n.Prime then 0 else vonMangoldt n * (n : ℝ) ^ (-(3/4 : ℝ))) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) hle (hgs.comp_injective hinj)
    split_ifs
    · exact le_rfl
    · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨hlhs, ?_⟩
  calc ∑' n, (if n.Prime then 0 else vonMangoldt n * (n : ℝ) ^ (-(3/4 : ℝ)))
      ≤ ∑' x : ℕ × ℕ, g₁ x.1 * g₂ x.2 :=
        hlhs.tsum_le_tsum_of_inj ι hinj (fun c _ => mul_nonneg (hg₁nn _) (hg₂nn _)) hle hgs
    _ = (∑' p, g₁ p) * (∑' a, g₂ a) := (hg₁s.tsum_mul_tsum hg₂s hgs).symm
    _ ≤ 22 * (27/4) := by
        rw [hg₂b]
        exact mul_le_mul_of_nonneg_right hg₁b (by norm_num)
    _ ≤ 150 := by norm_num

/-- **Tail T1 (prime powers).** -/
lemma tsum_nonprime_log_pow_le {η : ℝ} (hη0 : 0 < η) (m : ℕ) :
    ∑' n : ℕ, (if n.Prime then 0
        else vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η)))
      ≤ 150 * (4 ^ m * (m.factorial : ℝ)) := by
  obtain ⟨hs, hb⟩ := tsum_nonprime_vonMangoldt_rpow_le
  have hpt : ∀ n : ℕ, (if n.Prime then 0
        else vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η)))
      ≤ (4 ^ m * (m.factorial : ℝ))
        * (if n.Prime then 0 else vonMangoldt n * (n : ℝ) ^ (-(3/4 : ℝ))) := by
    intro n
    by_cases hp : n.Prime
    · simp [hp]
    rw [if_neg hp, if_neg hp]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
    have h1 : (Real.log n) ^ m ≤ 4 ^ m * (m.factorial : ℝ) * (n:ℝ) ^ (1/4 : ℝ) := by
      have := pow_le_factorial_mul_exp (x := Real.log n / 4) (by positivity) m
      have he : Real.exp (Real.log n / 4) = (n:ℝ) ^ (1/4 : ℝ) := by
        rw [Real.rpow_def_of_pos hn0]; congr 1; ring
      rw [he, div_pow, div_le_iff₀ (by positivity)] at this
      linarith [this]
    have h2 : (n:ℝ) ^ (-(1 + η)) ≤ (n:ℝ) ^ (-(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    have h3 : (n:ℝ) ^ (1/4 : ℝ) * (n:ℝ) ^ (-(1:ℝ)) = (n:ℝ) ^ (-(3/4 : ℝ)) := by
      rw [← Real.rpow_add hn0]; norm_num
    have hΛ : 0 ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    calc vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η))
        ≤ vonMangoldt n * (4 ^ m * (m.factorial : ℝ) * (n:ℝ) ^ (1/4 : ℝ))
            * (n:ℝ) ^ (-(1:ℝ)) := by gcongr
      _ = (4 ^ m * (m.factorial : ℝ))
            * (vonMangoldt n * ((n:ℝ) ^ (1/4 : ℝ) * (n:ℝ) ^ (-(1:ℝ)))) := by ring
      _ = _ := by rw [h3]
  have hlhs : Summable (fun n : ℕ => if n.Prime then 0
      else vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η))) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) hpt (hs.mul_left _)
    split_ifs
    · exact le_rfl
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
        have h1 := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1+η))
        have h2 : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
        positivity
  calc _ ≤ ∑' n, (4 ^ m * (m.factorial : ℝ))
          * (if n.Prime then 0 else vonMangoldt n * (n : ℝ) ^ (-(3/4 : ℝ))) :=
        hlhs.tsum_le_tsum hpt (hs.mul_left _)
    _ = (4 ^ m * (m.factorial : ℝ))
          * ∑' n, (if n.Prime then 0 else vonMangoldt n * (n : ℝ) ^ (-(3/4 : ℝ))) :=
        tsum_mul_left
    _ ≤ (4 ^ m * (m.factorial : ℝ)) * 150 := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 150 * (4 ^ m * (m.factorial : ℝ)) := by ring

/-- **Tail T2 (below `X`).** -/
lemma tsum_low_log_pow_le {η X : ℝ} (hη0 : 0 < η) (hη : η ≤ 1/20) (hX : 1 ≤ X) (m : ℕ) :
    ∑' n : ℕ, (if n ≤ ⌊X⌋₊ then vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η))
        else 0)
      ≤ (Real.log X) ^ m * (1/η + 2) := by
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hsupp : ∀ n ∉ Finset.Icc 0 ⌊X⌋₊,
      (if n ≤ ⌊X⌋₊ then vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η)) else 0)
        = 0 := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [if_neg]; omega
  rw [tsum_eq_sum hsupp]
  have hpt : ∀ n ∈ Finset.Icc 0 ⌊X⌋₊,
      (if n ≤ ⌊X⌋₊ then vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η)) else 0)
        ≤ (Real.log X) ^ m * (vonMangoldt n * (n : ℝ) ^ (-(1 + η))) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [if_pos hn.2]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn0
    have hnX : (n:ℝ) ≤ X := by
      calc (n:ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast hn.2
        _ ≤ X := Nat.floor_le (by linarith)
    have hlog : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hll : Real.log n ≤ Real.log X := Real.log_le_log (by linarith) hnX
    have hpow : (Real.log n) ^ m ≤ (Real.log X) ^ m := pow_le_pow_left₀ hlog hll m
    have hΛ : 0 ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hr : 0 ≤ (n:ℝ) ^ (-(1 + η)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η))
        ≤ vonMangoldt n * (Real.log X) ^ m * (n : ℝ) ^ (-(1 + η)) := by gcongr
      _ = (Real.log X) ^ m * (vonMangoldt n * (n : ℝ) ^ (-(1 + η))) := by ring
  have hsum := Census.summable_vonMangoldt_rpow hη0
  calc ∑ n ∈ Finset.Icc 0 ⌊X⌋₊,
        (if n ≤ ⌊X⌋₊ then vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η)) else 0)
      ≤ ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, (Real.log X) ^ m * (vonMangoldt n * (n : ℝ) ^ (-(1 + η))) :=
        Finset.sum_le_sum hpt
    _ = (Real.log X) ^ m * ∑ n ∈ Finset.Icc 0 ⌊X⌋₊, vonMangoldt n * (n : ℝ) ^ (-(1 + η)) := by
        rw [Finset.mul_sum]
    _ ≤ (Real.log X) ^ m * ∑' n, vonMangoldt n * (n : ℝ) ^ (-(1 + η)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine hsum.sum_le_tsum _ (fun n _ => ?_)
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ ≤ (Real.log X) ^ m * (1/η + 2) :=
        mul_le_mul_of_nonneg_left (Census.tsum_vonMangoldt_rpow_le hη0 hη) (by positivity)

/-- **Tail T3 (above `X`).** -/
lemma tsum_high_log_pow_le {η X : ℝ} (hη0 : 0 < η) (hη : η ≤ 1/10) (hX : 0 < X) (m : ℕ) :
    ∑' n : ℕ, (if ⌊X⌋₊ < n then vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η))
        else 0)
      ≤ X ^ (-(η/2)) * ((m.factorial : ℝ) * Real.exp 1 * ((m:ℝ) + 2) / (η/2) ^ (m + 1)) := by
  have hv : 0 < η/2 := by linarith
  have hdiag := tsum_vonMangoldt_log_pow_rpow_le' hv (by linarith) m
  have hsum := summable_vonMangoldt_log_pow_rpow hv m
  have hXr : 0 ≤ X ^ (-(η/2)) := Real.rpow_nonneg hX.le _
  have hnn : ∀ n : ℕ, 0 ≤ vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η/2)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
      have h1 := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1+η/2))
      have h2 : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      positivity
  have hpt : ∀ n : ℕ,
      (if ⌊X⌋₊ < n then vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η)) else 0)
        ≤ X ^ (-(η/2)) * (vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η/2))) := by
    intro n
    split_ifs with hlt
    · have hXn : X < n := (Nat.floor_lt hX.le).mp hlt
      have hn0 : (0:ℝ) < n := lt_trans hX hXn
      have hnpos : 0 < n := by exact_mod_cast hn0
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hnpos
      have hsplit : (n:ℝ) ^ (-(1 + η)) = (n:ℝ) ^ (-(η/2)) * (n:ℝ) ^ (-(1 + η/2)) := by
        rw [← Real.rpow_add hn0]; ring_nf
      have hmono : (n:ℝ) ^ (-(η/2)) ≤ X ^ (-(η/2)) := by
        rw [Real.rpow_neg hn0.le, Real.rpow_neg hX.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hX _) (Real.rpow_le_rpow hX.le hXn.le hv.le)
      have hΛ : 0 ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      have hlog : 0 ≤ (Real.log n) ^ m := by
        have : 0 ≤ Real.log n := Real.log_nonneg hn1
        positivity
      have hr : 0 ≤ (n:ℝ) ^ (-(1 + η/2)) := Real.rpow_nonneg hn0.le _
      rw [hsplit]
      calc vonMangoldt n * (Real.log n) ^ m * ((n:ℝ) ^ (-(η/2)) * (n:ℝ) ^ (-(1 + η/2)))
          ≤ vonMangoldt n * (Real.log n) ^ m * (X ^ (-(η/2)) * (n:ℝ) ^ (-(1 + η/2))) := by
            gcongr
        _ = X ^ (-(η/2)) * (vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η/2))) := by
            ring
    · exact mul_nonneg hXr (hnn n)
  have hlhs : Summable (fun n : ℕ =>
      if ⌊X⌋₊ < n then vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η)) else 0) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) hpt (hsum.mul_left _)
    split_ifs
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
        have h1 := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1+η))
        have h2 : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
        positivity
    · exact le_rfl
  calc _ ≤ ∑' n, X ^ (-(η/2)) * (vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η/2))) :=
        hlhs.tsum_le_tsum hpt (hsum.mul_left _)
    _ = X ^ (-(η/2)) * ∑' n, vonMangoldt n * (Real.log n) ^ m * (n : ℝ) ^ (-(1 + η/2)) :=
        tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hdiag hXr

end Tails

/-! ### The window sum: measurability and bounds -/

section Window

variable {q : ℕ}

/-- The prime window sum is measurable in `u` (a function of `⌊u⌋₊`). -/
lemma measurable_primeWindowSum (χ : DirichletCharacter ℂ q) (τ X : ℝ) :
    Measurable (fun u : ℝ => primeWindowSum χ τ X u) := by
  unfold primeWindowSum
  exact (measurable_from_nat (f := fun n : ℕ =>
    ∑ p ∈ (Finset.Icc 1 n).filter (fun p : ℕ => p.Prime ∧ X < (p : ℝ)),
      χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-(1 : ℂ) - (τ : ℂ) * Complex.I))).comp
    Nat.measurable_floor

/-- The window sum vanishes at (and below) the left endpoint. -/
lemma primeWindowSum_eq_zero_of_le (χ : DirichletCharacter ℂ q) (τ : ℝ) {X u : ℝ}
    (hu : u ≤ X) : primeWindowSum χ τ X u = 0 := by
  unfold primeWindowSum
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_filter, Finset.mem_Icc] at hp
  exfalso
  have h1 : (p : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast hp.1.2
  have hu1 : 1 ≤ u := Nat.floor_pos.mp (lt_of_lt_of_le hp.1.1 hp.1.2)
  have h2 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le (by linarith)
  linarith [hp.2.2]

/-- **Uniform bound for the window sum** below `X₂ ≥ e²⁰`:
`‖S(u)‖ ≤ e·(log X₂ + 2)`. -/
lemma norm_primeWindowSum_le (χ : DirichletCharacter ℂ q) (τ X : ℝ) {X₂ u : ℝ}
    (hX₂ : Real.exp 20 ≤ X₂) (hu : u ≤ X₂) :
    ‖primeWindowSum χ τ X u‖ ≤ Real.exp 1 * (Real.log X₂ + 2) := by
  have hX₂pos : 0 < X₂ := lt_of_lt_of_le (Real.exp_pos _) hX₂
  have hlog20 : 20 ≤ Real.log X₂ := by
    have := Real.log_le_log (Real.exp_pos 20) hX₂
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log X₂ := by linarith
  set u₀ : ℝ := 1 / Real.log X₂ with hu₀
  have hu₀pos : 0 < u₀ := by positivity
  have hu₀le : u₀ ≤ 1/20 := by
    rw [hu₀, div_le_div_iff₀ hlogpos (by norm_num)]; linarith
  -- termwise: `‖χ p · log p · p^{-1-iτ}‖ ≤ Λ(p)/p ≤ e·Λ(p)·p^{-(1+u₀)}`
  have hterm : ∀ p ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun p : ℕ => p.Prime ∧ X < (p : ℝ)),
      ‖χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-(1 : ℂ) - (τ : ℂ) * Complex.I)‖
        ≤ Real.exp 1 * (vonMangoldt p * (p : ℝ) ^ (-(1 + u₀))) := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Icc] at hp
    have hp1 : 1 ≤ p := hp.1.1
    have hppos : 0 < p := hp1
    have hpr : (0:ℝ) < p := by exact_mod_cast hppos
    have hp1r : (1:ℝ) ≤ p := by exact_mod_cast hp1
    have hu1 : 1 ≤ u := Nat.floor_pos.mp (lt_of_lt_of_le hp.1.1 hp.1.2)
    have hpX₂ : (p : ℝ) ≤ X₂ := by
      calc (p : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast hp.1.2
        _ ≤ u := Nat.floor_le (by linarith)
        _ ≤ X₂ := hu
    have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1r
    rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hppos, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hlog]
    have hre : (-(1 : ℂ) - (τ : ℂ) * Complex.I).re = -1 := by simp
    rw [hre, ArithmeticFunction.vonMangoldt_apply_prime hp.2.1]
    have hχ := DirichletCharacter.norm_le_one χ (p : ZMod q)
    -- `p^{-1} = p^{-(1+u₀)} · p^{u₀}` and `p^{u₀} ≤ e`
    have hsplit : (p : ℝ) ^ (-1 : ℝ) = (p : ℝ) ^ (-(1 + u₀)) * (p : ℝ) ^ u₀ := by
      rw [← Real.rpow_add hpr]; ring_nf
    have hpu₀ : (p : ℝ) ^ u₀ ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos hpr]
      refine Real.exp_le_exp.mpr ?_
      have hlogp : Real.log p ≤ Real.log X₂ := Real.log_le_log hpr hpX₂
      rw [hu₀]
      calc Real.log p * (1 / Real.log X₂) ≤ Real.log X₂ * (1 / Real.log X₂) := by gcongr
        _ = 1 := by field_simp
    have hr0 : 0 ≤ (p : ℝ) ^ (-(1 + u₀)) := Real.rpow_nonneg hpr.le _
    calc ‖χ (p : ZMod q)‖ * Real.log p * (p : ℝ) ^ (-1 : ℝ)
        ≤ 1 * Real.log p * ((p : ℝ) ^ (-(1 + u₀)) * Real.exp 1) := by
          rw [hsplit]; gcongr
      _ = Real.exp 1 * (Real.log p * (p : ℝ) ^ (-(1 + u₀))) := by ring
  have hsum := Census.summable_vonMangoldt_rpow hu₀pos
  calc ‖primeWindowSum χ τ X u‖
      ≤ ∑ p ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun p : ℕ => p.Prime ∧ X < (p : ℝ)),
          ‖χ p * (Real.log p : ℂ) * (p : ℂ) ^ (-(1 : ℂ) - (τ : ℂ) * Complex.I)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun p : ℕ => p.Prime ∧ X < (p : ℝ)),
          Real.exp 1 * (vonMangoldt p * (p : ℝ) ^ (-(1 + u₀))) := Finset.sum_le_sum hterm
    _ = Real.exp 1 * ∑ p ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun p : ℕ => p.Prime ∧ X < (p : ℝ)),
          vonMangoldt p * (p : ℝ) ^ (-(1 + u₀)) := by rw [Finset.mul_sum]
    _ ≤ Real.exp 1 * ∑' p : ℕ, vonMangoldt p * (p : ℝ) ^ (-(1 + u₀)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
        refine hsum.sum_le_tsum _ (fun p _ => ?_)
        exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    _ ≤ Real.exp 1 * (1 / u₀ + 2) :=
        mul_le_mul_of_nonneg_left (Census.tsum_vonMangoldt_rpow_le hu₀pos hu₀le)
          (Real.exp_pos 1).le
    _ = Real.exp 1 * (Real.log X₂ + 2) := by rw [hu₀]; field_simp

end Window

/-! ### The derivative kernel -/

section Kernel

/-- The derivative kernel `ψ(u) = u^{−1−η}(log u)^j((j+1) − η log u)` of
`φ(u) = (log u)^{j+1}u^{−η}`. -/
noncomputable def detKernel (η : ℝ) (j : ℕ) (u : ℝ) : ℝ :=
  u ^ (-1 - η) * (Real.log u) ^ j * (((j : ℝ) + 1) - η * Real.log u)

lemma hasDerivAt_detWeight {η : ℝ} (j : ℕ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun t : ℝ => (Real.log t) ^ (j + 1) * t ^ (-η)) (detKernel η j u) u := by
  have h1 : HasDerivAt (fun t : ℝ => (Real.log t) ^ (j + 1))
      ((((j + 1 : ℕ) : ℝ)) * (Real.log u) ^ (j + 1 - 1) * u⁻¹) u :=
    (Real.hasDerivAt_log hu.ne').pow (j + 1)
  have h2 : HasDerivAt (fun t : ℝ => t ^ (-η)) ((-η) * u ^ (-η - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inl hu.ne')
  refine (h1.mul h2).congr_deriv ?_
  unfold detKernel
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  have hinv : u⁻¹ = u ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]
  have hsplit : u ^ (-1 - η) = u ^ (-1 : ℝ) * u ^ (-η) := by
    rw [← Real.rpow_add hu]; ring_nf
  have hsplit' : u ^ (-η - 1) = u ^ (-1 : ℝ) * u ^ (-η) := by
    rw [← Real.rpow_add hu]; ring_nf
  rw [hinv, hsplit, hsplit']
  ring

/-- **Kernel bound on the window**: for `1 ≤ u` with `η·log u ≤ 16M ≤ 16(j+1)`,
`u·|ψ(u)| ≤ 17(j+1)·j!/η^j`. -/
lemma abs_detKernel_mul_le {η : ℝ} (hη0 : 0 < η) {j M : ℕ} (hjM : M ≤ j + 1) {u : ℝ}
    (hu1 : 1 ≤ u) (hu : η * Real.log u ≤ 16 * M) :
    |detKernel η j u| * u ≤ 17 * ((j : ℝ) + 1) * (j.factorial : ℝ) / η ^ j := by
  have hu0 : 0 < u := by linarith
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu1
  have hMj : (M : ℝ) ≤ (j : ℝ) + 1 := by exact_mod_cast hjM
  -- `(log u)^j · u^{-η} ≤ j!/η^j`
  have hkey : (Real.log u) ^ j * u ^ (-η) ≤ (j.factorial : ℝ) / η ^ j := by
    have h1 := pow_le_factorial_mul_exp (x := η * Real.log u) (by positivity) j
    have h2 : Real.exp (η * Real.log u) = u ^ η := by
      rw [Real.rpow_def_of_pos hu0, mul_comm]
    rw [h2, mul_pow] at h1
    have hη : 0 < η ^ j := by positivity
    have hpos : 0 < u ^ η := Real.rpow_pos_of_pos hu0 _
    have hneg : u ^ (-η) = (u ^ η)⁻¹ := Real.rpow_neg hu0.le _
    rw [hneg, le_div_iff₀ hη]
    calc (Real.log u) ^ j * (u ^ η)⁻¹ * η ^ j
        = (η ^ j * (Real.log u) ^ j) * (u ^ η)⁻¹ := by ring
      _ ≤ ((j.factorial : ℝ) * u ^ η) * (u ^ η)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (j.factorial : ℝ) := by field_simp
  -- `|(j+1) − η log u| ≤ 17(j+1)`
  have habs : |((j : ℝ) + 1) - η * Real.log u| ≤ 17 * ((j : ℝ) + 1) := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg hη0.le hlog]
  have hsplit : u ^ (-1 - η) * u = u ^ (-η) := by
    have : u ^ (-1 - η) * u = u ^ (-1 - η) * u ^ (1 : ℝ) := by rw [Real.rpow_one]
    rw [this, ← Real.rpow_add hu0]; ring_nf
  have hlogj : 0 ≤ (Real.log u) ^ j := by positivity
  have hupos : 0 ≤ u ^ (-η) := Real.rpow_nonneg hu0.le _
  calc |detKernel η j u| * u
      = (u ^ (-1 - η) * u) * (Real.log u) ^ j * |((j : ℝ) + 1) - η * Real.log u| := by
        unfold detKernel
        rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hu0.le _),
          abs_of_nonneg hlogj]
        ring
    _ = ((Real.log u) ^ j * u ^ (-η)) * |((j : ℝ) + 1) - η * Real.log u| := by
        rw [hsplit]; ring
    _ ≤ ((j.factorial : ℝ) / η ^ j) * (17 * ((j : ℝ) + 1)) := by
        gcongr
    _ = 17 * ((j : ℝ) + 1) * (j.factorial : ℝ) / η ^ j := by ring

end Kernel

/-! ### §4.4 step 5: the endgame -/

section Endgame

/-- **§4.4 step 5 (endgame).**  A measurable window function `S` bounded by `B`
on `[X₁, X₂]`, a kernel with `|ψ(u)|·u ≤ C₇`, and a lower bound `G·C₇` for
`‖∫ ψ·S‖` force the mean square `∫ ‖S‖²/u ≥ G²/K`, `K` any bound for
`log(X₂/X₁)`.  (AM–GM at scale `λ = K/G`; no Hölder needed.) -/
lemma integral_normSq_div_ge {S : ℝ → ℂ} {ψ : ℝ → ℝ} {X₁ X₂ B C₇ G K : ℝ}
    (hX₁ : 0 < X₁) (hX : X₁ ≤ X₂) (hS : Measurable S)
    (hSb : ∀ u ∈ Set.Icc X₁ X₂, ‖S u‖ ≤ B)
    (hψ : ∀ u ∈ Set.Icc X₁ X₂, |ψ u| * u ≤ C₇) (hC₇ : 0 < C₇)
    (hK : Real.log X₂ - Real.log X₁ ≤ K) (hK0 : 0 < K) (hG : 0 < G)
    (hlow : G * C₇ ≤ ‖∫ t in X₁..X₂, (ψ t : ℂ) * S t‖) :
    G ^ 2 / K ≤ ∫ u in X₁..X₂, ‖S u‖ ^ 2 / u := by
  have hX₂ : 0 < X₂ := lt_of_lt_of_le hX₁ hX
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hSb X₁ ⟨le_rfl, hX⟩)
  -- integrability of `‖S‖²/u`
  have hImeas : Measurable (fun u : ℝ => ‖S u‖ ^ 2 / u) :=
    (hS.norm.pow_const 2).div measurable_id
  have hIint : MeasureTheory.IntegrableOn (fun u : ℝ => ‖S u‖ ^ 2 / u) (Set.Ioc X₁ X₂) := by
    refine MeasureTheory.Measure.integrableOn_of_bounded (M := B ^ 2 / X₁)
      measure_Ioc_lt_top.ne hImeas.aestronglyMeasurable ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun u hu => ?_
    have hu1 : X₁ < u := hu.1
    have hu0 : 0 < u := lt_trans hX₁ hu1
    have hSu := hSb u ⟨hu1.le, hu.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖S u‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hSu 2
    calc ‖S u‖ ^ 2 / u ≤ B ^ 2 / u := div_le_div_of_nonneg_right h1 hu0.le
      _ ≤ B ^ 2 / X₁ := div_le_div_of_nonneg_left (by positivity) hX₁ hu1.le
  have hIint' : IntervalIntegrable (fun u : ℝ => ‖S u‖ ^ 2 / u) MeasureTheory.volume X₁ X₂ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mpr hIint
  have hinv : IntervalIntegrable (fun u : ℝ => u⁻¹) MeasureTheory.volume X₁ X₂ := by
    refine intervalIntegral.intervalIntegrable_inv (f := fun x => x) (fun x hx => ?_) continuousOn_id
    rw [Set.uIcc_of_le hX] at hx
    exact ne_of_gt (lt_of_lt_of_le hX₁ hx.1)
  have hinvint : MeasureTheory.IntegrableOn (fun u : ℝ => u⁻¹) (Set.Ioc X₁ X₂) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hX).mp hinv
  -- the scale
  set l : ℝ := K / G with hl
  have hl0 : 0 < l := by positivity
  -- the majorant
  set g : ℝ → ℝ := fun u => C₇ * ((l / 2) * (‖S u‖ ^ 2 / u) + (1 / (2 * l)) * u⁻¹) with hg
  have hgint : MeasureTheory.IntegrableOn g (Set.Ioc X₁ X₂) := by
    rw [hg]
    exact ((hIint.const_mul _).add (hinvint.const_mul _)).const_mul _
  -- pointwise domination on `Ioc`
  have hpt : ∀ u ∈ Set.Ioc X₁ X₂, ‖(ψ u : ℂ) * S u‖ ≤ g u := by
    intro u hu
    have hu0 : 0 < u := lt_trans hX₁ hu.1
    have hψu := hψ u ⟨hu.1.le, hu.2⟩
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hamgm : ‖S u‖ ≤ (l / 2) * ‖S u‖ ^ 2 + 1 / (2 * l) := by
      have h := sq_nonneg (l * ‖S u‖ - 1)
      rw [← sub_nonneg]
      have : (l / 2) * ‖S u‖ ^ 2 + 1 / (2 * l) - ‖S u‖ = (l * ‖S u‖ - 1) ^ 2 / (2 * l) := by
        field_simp; ring
      rw [this]; positivity
    have hψ' : |ψ u| ≤ C₇ / u := by
      rw [le_div_iff₀ hu0]; exact hψu
    calc |ψ u| * ‖S u‖ ≤ (C₇ / u) * ((l / 2) * ‖S u‖ ^ 2 + 1 / (2 * l)) := by
          gcongr
      _ = g u := by rw [hg]; field_simp
  -- integrate
  have hstep1 : ‖∫ t in X₁..X₂, (ψ t : ℂ) * S t‖ ≤ ∫ t in X₁..X₂, ‖(ψ t : ℂ) * S t‖ :=
    intervalIntegral.norm_integral_le_integral_norm hX
  have hstep2 : ∫ t in X₁..X₂, ‖(ψ t : ℂ) * S t‖ ≤ ∫ t in X₁..X₂, g t := by
    rw [intervalIntegral.integral_of_le hX, intervalIntegral.integral_of_le hX]
    refine MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
      hgint ?_
    exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall hpt)
  have hstep3 : ∫ t in X₁..X₂, g t
      = C₇ * ((l / 2) * (∫ u in X₁..X₂, ‖S u‖ ^ 2 / u) + (1 / (2 * l)) * (Real.log X₂ - Real.log X₁)) := by
    rw [hg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hIint'.const_mul _) (hinv.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_inv_of_pos hX₁ hX₂, Real.log_div hX₂.ne' hX₁.ne']
  have hI0 : 0 ≤ ∫ u in X₁..X₂, ‖S u‖ ^ 2 / u := by
    refine intervalIntegral.integral_nonneg hX fun u hu => ?_
    have : 0 < u := lt_of_lt_of_le hX₁ hu.1
    positivity
  -- assemble: `G·C₇ ≤ C₇((l/2)I + K/(2l))`, `l = K/G`
  have hmain : G * C₇ ≤ C₇ * ((l / 2) * (∫ u in X₁..X₂, ‖S u‖ ^ 2 / u) + (1 / (2 * l)) * K) := by
    have := le_trans hlow (le_trans hstep1 hstep2)
    rw [hstep3] at this
    have h2 : C₇ * ((l / 2) * (∫ u in X₁..X₂, ‖S u‖ ^ 2 / u) + (1 / (2 * l)) * (Real.log X₂ - Real.log X₁))
        ≤ C₇ * ((l / 2) * (∫ u in X₁..X₂, ‖S u‖ ^ 2 / u) + (1 / (2 * l)) * K) := by
      gcongr
    exact le_trans this h2
  have hG' : G ≤ (l / 2) * (∫ u in X₁..X₂, ‖S u‖ ^ 2 / u) + (1 / (2 * l)) * K := by
    have hmain' : C₇ * G ≤ C₇ * ((l / 2) * (∫ u in X₁..X₂, ‖S u‖ ^ 2 / u) + (1 / (2 * l)) * K) := by
      linarith [hmain]
    exact le_of_mul_le_mul_left hmain' hC₇
  rw [hl] at hG'
  have hK2 : (1 / (2 * (K / G))) * K = G / 2 := by field_simp
  rw [hK2] at hG'
  have : G / 2 ≤ (K / G / 2) * (∫ u in X₁..X₂, ‖S u‖ ^ 2 / u) := by linarith
  rw [div_le_iff₀ hK0]
  have h3 : (K / G / 2) * (∫ u in X₁..X₂, ‖S u‖ ^ 2 / u) * (2 * G) = K * ∫ u in X₁..X₂, ‖S u‖ ^ 2 / u := by
    field_simp
  nlinarith [this, h3, hG]

end Endgame

/-! ### §4.4 step 4: Abel summation on the window -/

section Abel

variable {q : ℕ}

/-- The Abel partial sums of the window coefficients are the window sums. -/
lemma sum_Icc_eq_primeWindowSum (χ : DirichletCharacter ℂ q) (τ X t : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (if n.Prime ∧ X < (n : ℝ) then
        χ n * (Real.log n : ℂ) * (n : ℂ) ^ (-(1 : ℂ) - (τ : ℂ) * Complex.I) else 0)
      = primeWindowSum χ τ X t := by
  unfold primeWindowSum
  rw [Finset.sum_filter, Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons,
    if_neg (fun h => Nat.not_prime_zero h.1), zero_add]
  have : Finset.Ioc 0 ⌊t⌋₊ = Finset.Icc 1 ⌊t⌋₊ := by
    ext n; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [this]

/-- Continuity of the kernel on a compact window away from `0`. -/
lemma continuousOn_detKernel (η : ℝ) (j : ℕ) {X₁ X₂ : ℝ} (hX₁ : 0 < X₁) :
    ContinuousOn (fun t : ℝ => (detKernel η j t : ℂ)) (Set.Icc X₁ X₂) := by
  have hne : ∀ t ∈ Set.Icc X₁ X₂, t ≠ 0 := fun t ht => ne_of_gt (lt_of_lt_of_le hX₁ ht.1)
  have hlog : ContinuousOn Real.log (Set.Icc X₁ X₂) :=
    Real.continuousOn_log.mono fun t ht => Set.mem_compl_singleton_iff.mpr (hne t ht)
  have hrpow : ContinuousOn (fun t : ℝ => t ^ (-1 - η)) (Set.Icc X₁ X₂) :=
    continuousOn_id.rpow_const fun t ht => Or.inl (hne t ht)
  have hcont : ContinuousOn (fun t : ℝ => detKernel η j t) (Set.Icc X₁ X₂) := by
    unfold detKernel
    exact (hrpow.mul (hlog.pow j)).mul (continuousOn_const.sub (continuousOn_const.mul hlog))
  exact Complex.continuous_ofReal.comp_continuousOn hcont

/-- **Abel summation on the window.**  With `φ(t) = (log t)^{j+1} t^{−η}` and the
window coefficients `c`, the weighted prime sum over `(X₁, X₂]` equals
`φ(X₂)·S(X₂) − ∫_{X₁}^{X₂} ψ(t)·S(t) dt` (the boundary term at `X₁` vanishes). -/
lemma abel_window (χ : DirichletCharacter ℂ q) (τ : ℝ) {η X₁ X₂ : ℝ} (hX₁ : 0 < X₁)
    (hX : X₁ ≤ X₂) (j : ℕ) :
    ∑ n ∈ Finset.Ioc ⌊X₁⌋₊ ⌊X₂⌋₊,
        (((Real.log n) ^ (j + 1) * (n : ℝ) ^ (-η) : ℝ) : ℂ)
          * (if n.Prime ∧ X₁ < (n : ℝ) then
              χ n * (Real.log n : ℂ) * (n : ℂ) ^ (-(1 : ℂ) - (τ : ℂ) * Complex.I) else 0)
      = (((Real.log X₂) ^ (j + 1) * X₂ ^ (-η) : ℝ) : ℂ) * primeWindowSum χ τ X₁ X₂
        - ∫ t in Set.Ioc X₁ X₂, (detKernel η j t : ℂ) * primeWindowSum χ τ X₁ t := by
  have hderiv : ∀ t ∈ Set.Icc X₁ X₂,
      HasDerivAt (fun t : ℝ => (((Real.log t) ^ (j + 1) * t ^ (-η) : ℝ) : ℂ))
        ((detKernel η j t : ℝ) : ℂ) t :=
    fun t ht => (hasDerivAt_detWeight j (lt_of_lt_of_le hX₁ ht.1)).ofReal_comp
  have hdiff : ∀ t ∈ Set.Icc X₁ X₂,
      DifferentiableAt ℝ (fun t : ℝ => (((Real.log t) ^ (j + 1) * t ^ (-η) : ℝ) : ℂ)) t :=
    fun t ht => (hderiv t ht).differentiableAt
  have hint : MeasureTheory.IntegrableOn
      (deriv (fun t : ℝ => (((Real.log t) ^ (j + 1) * t ^ (-η) : ℝ) : ℂ))) (Set.Icc X₁ X₂) := by
    refine ((continuousOn_detKernel η j hX₁).integrableOn_Icc).congr_fun ?_ measurableSet_Icc
    intro t ht
    exact ((hderiv t ht).deriv).symm
  have habel := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => if n.Prime ∧ X₁ < (n : ℝ) then
      χ n * (Real.log n : ℂ) * (n : ℂ) ^ (-(1 : ℂ) - (τ : ℂ) * Complex.I) else 0)
    hX₁.le hX hdiff hint
  rw [sum_Icc_eq_primeWindowSum, sum_Icc_eq_primeWindowSum,
    primeWindowSum_eq_zero_of_le χ τ le_rfl, mul_zero, sub_zero] at habel
  have hcongr : ∫ t in Set.Ioc X₁ X₂,
        deriv (fun t : ℝ => (((Real.log t) ^ (j + 1) * t ^ (-η) : ℝ) : ℂ)) t
          * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (if k.Prime ∧ X₁ < (k : ℝ) then
              χ k * (Real.log k : ℂ) * (k : ℂ) ^ (-(1 : ℂ) - (τ : ℂ) * Complex.I) else 0)
      = ∫ t in Set.Ioc X₁ X₂, (detKernel η j t : ℂ) * primeWindowSum χ τ X₁ t := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [(hderiv t ⟨ht.1.le, ht.2⟩).deriv, sum_Icc_eq_primeWindowSum]
  rw [hcongr] at habel
  exact habel

end Abel

/-! ### §4.4 step 4: the Dirichlet series minus the window sum -/

section Tail

variable {N : ℕ}

/-- **§4.4 step 4: the Dirichlet series minus the window sum.**  The difference
is controlled by the three tails (prime powers, primes below `X₁`, primes
above `X₂`) of the diagonal `D(n) = Λ(n)(log n)^{j+1} n^{−(1+η)}`. -/
lemma norm_LSeries_sub_window_le (χ : DirichletCharacter ℂ N) (τ : ℝ)
    {η X₁ X₂ : ℝ} (hη0 : 0 < η) (hX₁ : 0 ≤ X₁) (j : ℕ) :
    ‖LSeries (fun n : ℕ => (Real.log n : ℂ) ^ (j + 1)
          * (χ (n : ZMod N) * (vonMangoldt n : ℂ))) (((1 + η : ℝ) : ℂ) + τ * I)
      - ∑ n ∈ Finset.Ioc ⌊X₁⌋₊ ⌊X₂⌋₊,
        (((Real.log n) ^ (j + 1) * (n : ℝ) ^ (-η) : ℝ) : ℂ)
          * (if n.Prime ∧ X₁ < (n : ℝ) then
              χ n * (Real.log n : ℂ) * (n : ℂ) ^ (-(1 : ℂ) - (τ : ℂ) * Complex.I) else 0)‖
      ≤ ∑' n : ℕ, (if n.Prime then 0
            else vonMangoldt n * (Real.log n) ^ (j + 1) * (n : ℝ) ^ (-(1 + η)))
        + ∑' n : ℕ, (if n ≤ ⌊X₁⌋₊ then
            vonMangoldt n * (Real.log n) ^ (j + 1) * (n : ℝ) ^ (-(1 + η)) else 0)
        + ∑' n : ℕ, (if ⌊X₂⌋₊ < n then
            vonMangoldt n * (Real.log n) ^ (j + 1) * (n : ℝ) ^ (-(1 + η)) else 0) := by
  classical
  set s₀ : ℂ := ((1 + η : ℝ) : ℂ) + τ * I with hs₀
  set F : ℕ → ℂ := fun n : ℕ => (Real.log n : ℂ) ^ (j + 1)
    * (χ (n : ZMod N) * (vonMangoldt n : ℂ)) with hF
  set D : ℕ → ℝ := fun n => vonMangoldt n * (Real.log n) ^ (j + 1) * (n : ℝ) ^ (-(1 + η))
    with hD
  set P : Finset ℕ := (Finset.Ioc ⌊X₁⌋₊ ⌊X₂⌋₊).filter Nat.Prime with hP
  have hs₀re : s₀.re = 1 + η := by rw [hs₀]; simp
  have hterm : ∀ n, ‖LSeries.term F s₀ n‖ ≤ D n := fun n =>
    norm_term_log_pow_twist_le χ hs₀re (j + 1) n
  have hD0 : ∀ n, 0 ≤ D n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hD]
    · have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
      have h1 := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1+η))
      have h2 : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      rw [hD]; positivity
  have hDsum : Summable D := summable_vonMangoldt_log_pow_rpow hη0 (j + 1)
  have hFsum : Summable (LSeries.term F s₀) := hDsum.of_norm_bounded hterm
  -- the window sum is the sum of the terms over `P`
  have hwin : ∑ n ∈ Finset.Ioc ⌊X₁⌋₊ ⌊X₂⌋₊,
        (((Real.log n) ^ (j + 1) * (n : ℝ) ^ (-η) : ℝ) : ℂ)
          * (if n.Prime ∧ X₁ < (n : ℝ) then
              χ n * (Real.log n : ℂ) * (n : ℂ) ^ (-(1 : ℂ) - (τ : ℂ) * Complex.I) else 0)
      = ∑ n ∈ P, LSeries.term F s₀ n := by
    rw [hP, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Ioc] at hn
    have hX₁n : X₁ < n := (Nat.floor_lt hX₁).mp hn.1
    by_cases hp : n.Prime
    · rw [if_pos ⟨hp, hX₁n⟩, if_pos hp]
      have hn0 : n ≠ 0 := hp.ne_zero
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0
      rw [LSeries.term_of_ne_zero hn0, hF]
      simp only
      rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
      have hc : (((n : ℝ) ^ (-η) : ℝ) : ℂ) = (n : ℂ) ^ (-(η : ℂ)) := by
        rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]; push_cast; ring_nf
      have hmul : (n : ℂ) ^ (-(η : ℂ)) * (n : ℂ) ^ (-(1 : ℂ) - (τ : ℂ) * Complex.I)
          = ((n : ℂ) ^ s₀)⁻¹ := by
        rw [← Complex.cpow_add _ _ hnC, ← Complex.cpow_neg]
        congr 1
        rw [hs₀]; push_cast; ring
      push_cast
      rw [hc, div_eq_mul_inv, ← hmul]
      ring
    · rw [if_neg (fun h => hp h.1), if_neg hp, mul_zero]
  rw [hwin]
  -- write both sides as `tsum`s
  have hPsum : Summable (fun n => if n ∈ P then LSeries.term F s₀ n else 0) :=
    summable_of_ne_finset_zero (s := P) fun n hn => if_neg hn
  have hPeq : ∑ n ∈ P, LSeries.term F s₀ n = ∑' n, (if n ∈ P then LSeries.term F s₀ n else 0) := by
    rw [tsum_eq_sum (s := P) fun n hn => if_neg hn]
    exact Finset.sum_congr rfl fun n hn => (if_pos hn).symm
  rw [hPeq, LSeries, ← hFsum.tsum_sub hPsum]
  have hdiff : ∀ n, LSeries.term F s₀ n - (if n ∈ P then LSeries.term F s₀ n else 0)
      = (if n ∈ P then 0 else LSeries.term F s₀ n) := by
    intro n; split_ifs <;> simp
  simp_rw [hdiff]
  -- the three majorants
  set m₁ : ℕ → ℝ := fun n => if n.Prime then 0 else D n with hm₁
  set m₂ : ℕ → ℝ := fun n => if n ≤ ⌊X₁⌋₊ then D n else 0 with hm₂
  set m₃ : ℕ → ℝ := fun n => if ⌊X₂⌋₊ < n then D n else 0 with hm₃
  have hm₁0 : ∀ n, 0 ≤ m₁ n := fun n => by simp only [hm₁]; split_ifs <;> [exact le_rfl; exact hD0 n]
  have hm₂0 : ∀ n, 0 ≤ m₂ n := fun n => by simp only [hm₂]; split_ifs <;> [exact hD0 n; exact le_rfl]
  have hm₃0 : ∀ n, 0 ≤ m₃ n := fun n => by simp only [hm₃]; split_ifs <;> [exact hD0 n; exact le_rfl]
  have hm₁D : ∀ n, m₁ n ≤ D n := fun n => by simp only [hm₁]; split_ifs <;> [exact hD0 n; exact le_rfl]
  have hm₂D : ∀ n, m₂ n ≤ D n := fun n => by simp only [hm₂]; split_ifs <;> [exact le_rfl; exact hD0 n]
  have hm₃D : ∀ n, m₃ n ≤ D n := fun n => by simp only [hm₃]; split_ifs <;> [exact le_rfl; exact hD0 n]
  have hm₁s : Summable m₁ := Summable.of_nonneg_of_le hm₁0 hm₁D hDsum
  have hm₂s : Summable m₂ := Summable.of_nonneg_of_le hm₂0 hm₂D hDsum
  have hm₃s : Summable m₃ := Summable.of_nonneg_of_le hm₃0 hm₃D hDsum
  have hpt : ∀ n, ‖(if n ∈ P then 0 else LSeries.term F s₀ n)‖ ≤ m₁ n + m₂ n + m₃ n := by
    intro n
    by_cases hnP : n ∈ P
    · rw [if_pos hnP, norm_zero]
      linarith [hm₁0 n, hm₂0 n, hm₃0 n]
    · rw [if_neg hnP]
      refine le_trans (hterm n) ?_
      rw [hm₁, hm₂, hm₃]
      simp only
      by_cases hp : n.Prime
      · by_cases h1 : n ≤ ⌊X₁⌋₊
        · rw [if_pos hp, if_pos h1]; linarith [hm₃0 n]
        · by_cases h2 : ⌊X₂⌋₊ < n
          · rw [if_pos hp, if_neg h1, if_pos h2]; linarith
          · exfalso
            exact hnP (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hp⟩)
      · rw [if_neg hp]; linarith [hm₂0 n, hm₃0 n]
  have hnormsum : Summable (fun n => ‖(if n ∈ P then 0 else LSeries.term F s₀ n)‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hpt ((hm₁s.add hm₂s).add hm₃s)
  calc ‖∑' n, (if n ∈ P then 0 else LSeries.term F s₀ n)‖
      ≤ ∑' n, ‖(if n ∈ P then 0 else LSeries.term F s₀ n)‖ := norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' n, (m₁ n + m₂ n + m₃ n) := hnormsum.tsum_le_tsum hpt ((hm₁s.add hm₂s).add hm₃s)
    _ = ∑' n, m₁ n + ∑' n, m₂ n + ∑' n, m₃ n := by
        rw [(hm₁s.add hm₂s).tsum_add hm₃s, hm₁s.tsum_add hm₂s]

end Tail

/-! ### §4.2 The zero detector -/

section Main

variable {q : ℕ} [NeZero q]

/-- Primitive characters modulo `q ≥ 2` are nontrivial. -/
lemma ne_one_of_isPrimitive {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 2 ≤ q) :
    χ ≠ 1 := by
  intro h
  have h1 := hχ
  rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at h1
  omega

set_option maxHeartbeats 4000000 in
/-- **Zero detection** (TZ Theorem 4.2 shape, lossy constants): a zero of
a nontrivial primitive `χ` within `η` of `1 + iτ` forces the prime window
sums over `(Xone, Xtwo]` to be large in mean square along `du/u`. -/
theorem kderiv_detection {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) (hq : 2 ≤ q) {W τ η : ℝ}
    (hqW : (q : ℝ) ≤ W) (hτW : |τ| + 2 ≤ W) (_hW : Real.exp 500 ≤ W)
    (hη0 : 0 < η) (hηup : η ≤ 1/5000)
    (hηlow : 1 ≤ 12 * η * Real.log W)
    (hzero : ∃ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 ∧
      dist ρ (1 + τ * Complex.I) ≤ η) :
    1 ≤ η ^ 3 * (Mdet η (Real.log W) : ℝ) *
        Real.exp (6 * (Mdet η (Real.log W) : ℝ)) *
        ∫ u in (Xone η (Real.log W))..(Xtwo η (Real.log W)),
          ‖primeWindowSum χ τ (Xone η (Real.log W)) u‖ ^ 2 / u := by
  classical
  have hχ1 : χ ≠ 1 := ne_one_of_isPrimitive hχ hq
  -- the family scale `L = log W`
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log W := ⟨_, rfl⟩
  rw [← hLdef] at hηlow ⊢
  have hηL : 1/12 ≤ η * L := by linarith
  have hL0 : 0 < L := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hη0.le h]
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast (by omega : 1 ≤ q)
  have hτ2 : (2:ℝ) ≤ |τ| + 2 := by linarith [abs_nonneg τ]
  have hW1 : (1:ℝ) ≤ W := le_trans hq1 hqW
  have hlogq : Real.log ((q:ℝ) * (|τ| + 2)) ≤ 2 * L := by
    have h1 : (q:ℝ) * (|τ| + 2) ≤ W * W := mul_le_mul hqW hτW (by linarith) (by linarith)
    have h2 : Real.log ((q:ℝ) * (|τ| + 2)) ≤ Real.log (W * W) :=
      Real.log_le_log (by positivity) h1
    have h3 : Real.log (W * W) = 2 * L := by
      rw [Real.log_mul (ne_of_gt (by linarith)) (ne_of_gt (by linarith)), hLdef]; ring
    linarith
  have hlogq0 : 0 ≤ Real.log ((q:ℝ) * (|τ| + 2)) := Real.log_nonneg (by nlinarith)
  -- the frozen parameters
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = Ndet η L := ⟨_, rfl⟩
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = Mdet η L := ⟨_, rfl⟩
  obtain ⟨X₁, hX₁def⟩ : ∃ X : ℝ, X = Xone η L := ⟨_, rfl⟩
  obtain ⟨X₂, hX₂def⟩ : ∃ X : ℝ, X = Xtwo η L := ⟨_, rfl⟩
  rw [← hMdef, ← hX₁def, ← hX₂def]
  have hM6 : M = 6 * N := by rw [hMdef, hNdef]; rfl
  have hN6 : (6:ℝ) + 28800000 * η * L ≤ N := by rw [hNdef]; exact le_Ndet_cast η L
  have hNlow : (2400006:ℝ) ≤ N := by linarith
  have hNL : 28800000 * η * L ≤ (N:ℝ) - 6 := by linarith
  have hN41 : (41:ℝ) ≤ N := by linarith
  have hN1 : 1 ≤ N := by
    have : (1:ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hN5 : 5 ≤ N := by
    have : (5:ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hM1 : 1 ≤ M := by omega
  have hMr : (6:ℝ) ≤ M := by
    have : 6 ≤ M := by omega
    exact_mod_cast this
  have hX₁eq : X₁ = Real.exp ((M:ℝ) / (16 * η)) := by rw [hX₁def, Xone, hMdef]
  have hX₂eq : X₂ = Real.exp (16 * (M:ℝ) / η) := by rw [hX₂def, Xtwo, hMdef]
  have hX₁pos : 0 < X₁ := by rw [hX₁eq]; exact Real.exp_pos _
  have hX₂pos : 0 < X₂ := by rw [hX₂eq]; exact Real.exp_pos _
  have hX₁ge1 : 1 ≤ X₁ := by
    rw [hX₁eq]; exact Real.one_le_exp (by positivity)
  have hlogX₁ : Real.log X₁ = (M:ℝ) / (16 * η) := by rw [hX₁eq, Real.log_exp]
  have hlogX₂ : Real.log X₂ = 16 * (M:ℝ) / η := by rw [hX₂eq, Real.log_exp]
  have hX₁X₂ : X₁ ≤ X₂ := by
    rw [hX₁eq, hX₂eq]
    refine Real.exp_le_exp.mpr ?_
    rw [div_le_div_iff₀ (by positivity) hη0]
    nlinarith
  have hX₂20 : Real.exp 20 ≤ X₂ := by
    rw [hX₂eq]
    refine Real.exp_le_exp.mpr ?_
    rw [le_div_iff₀ hη0]
    nlinarith
  -- §4.4 step 2: the `6η`-family and the Turán event
  have hmass : ((∑ ρ ∈ (zeroDiskFinset χ τ).filter
      (fun ρ => dist ρ (1 + τ * Complex.I) ≤ 6 * η),
      analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) ≤ N := by
    have h := sum_ord_smallDisk_le hχ1 τ (w := 6 * η) (by positivity) (by linarith)
    calc _ ≤ 5 + 2400000 * (6 * η) * Real.log ((q:ℝ) * (|τ| + 2)) := h
      _ ≤ 5 + 2400000 * (6 * η) * (2 * L) := by gcongr
      _ ≤ N := by linarith [hN6]
  obtain ⟨k, hk1, hk2, hk3⟩ :=
    exists_turan_index hχ1 τ hη0 (by linarith) hN1 hmass hzero M
  have hcoef : ((N:ℝ) / (8 * Real.exp 1 * ((M:ℝ) + N))) = 1 / (56 * Real.exp 1) := by
    rw [hM6]; push_cast
    have hN0 : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hE0 : Real.exp 1 ≠ 0 := (Real.exp_pos 1).ne'
    field_simp
    ring
  rw [hcoef] at hk3
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have hk1' : 6 * N + 1 ≤ j + 2 := by omega
  have hk2' : j + 2 ≤ 7 * N := by omega
  have hjM : M ≤ j + 1 := by omega
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ,
    Q = (1 / (56 * Real.exp 1)) ^ N * (1 / (2 * η)) ^ (j + 2) := ⟨_, rfl⟩
  rw [← hQdef] at hk3
  have hQ0 : 0 < Q := by rw [hQdef]; positivity
  have hfac0 : (0:ℝ) < ((j + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  -- §4.4 step 3: the Dirichlet side is large
  have hfar := budget_far (A := (1/η) * (1/η + 2 + 520000 * Real.log ((q:ℝ) * (|τ| + 2))))
    hη0 hηup hL0.le hNL hN41 hk1' rfl
    (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  have hcauchy := budget_cauchy (C := 520000 * Real.log ((q:ℝ) * (|τ| + 2)))
    hη0 hηup hL0.le hNL hk1' rfl (by linarith)
  rw [← hQdef] at hfar hcauchy
  have hLS := norm_LSeries_ge_of_turan hχ1 τ hη0 (by linarith) j hk3 hfar hcauchy
  -- §4.4 step 4: the three tails
  have hB3 := budget_primepow (N := N) hη0 hηup hk1' rfl
  have hB4 := budget_low hη0 hηup hN5 hM6 hk1' rfl
  have hB5 := budget_high (η := η) hη0 hN1 hM6 hk2' rfl
  have hB6 := budget_boundary hη0 hηup hN1 hM6 hk1' hk2' rfl
  rw [← hQdef] at hB3 hB4 hB5 hB6
  have hT1 : ∑' n : ℕ, (if n.Prime then 0
        else vonMangoldt n * (Real.log n) ^ (j + 1) * (n : ℝ) ^ (-(1 + η)))
      ≤ ((j + 1).factorial : ℝ) * (Q / 8) := by
    refine le_trans (tsum_nonprime_log_pow_le hη0 (j + 1)) ?_
    calc 150 * (4 ^ (j + 1) * ((j + 1).factorial : ℝ))
        = ((j + 1).factorial : ℝ) * (150 * 4 ^ (j + 1)) := by ring
      _ ≤ ((j + 1).factorial : ℝ) * (Q / 8) := mul_le_mul_of_nonneg_left hB3 hfac0.le
  have hT2 : ∑' n : ℕ, (if n ≤ ⌊X₁⌋₊ then
        vonMangoldt n * (Real.log n) ^ (j + 1) * (n : ℝ) ^ (-(1 + η)) else 0)
      ≤ ((j + 1).factorial : ℝ) * (Q / 8) := by
    refine le_trans (tsum_low_log_pow_le hη0 (by linarith) hX₁ge1 (j + 1)) ?_
    rw [hlogX₁]
    exact hB4
  have hX₂pow : X₂ ^ (-(η / 2)) = Real.exp (-(8 * (M:ℝ))) := by
    rw [hX₂eq, ← Real.exp_mul]
    congr 1
    field_simp
    ring
  have hT3 : ∑' n : ℕ, (if ⌊X₂⌋₊ < n then
        vonMangoldt n * (Real.log n) ^ (j + 1) * (n : ℝ) ^ (-(1 + η)) else 0)
      ≤ ((j + 1).factorial : ℝ) * (Q / 8) := by
    refine le_trans (tsum_high_log_pow_le hη0 (by linarith) hX₂pos (j + 1)) ?_
    rw [hX₂pow]
    push_cast
    exact hB5
  have hwin := norm_LSeries_sub_window_le χ τ (X₂ := X₂) hη0 hX₁pos.le j
  -- the window sum is large
  obtain ⟨Dwin, hDwin⟩ : ∃ z : ℂ, z = ∑ n ∈ Finset.Ioc ⌊X₁⌋₊ ⌊X₂⌋₊,
      (((Real.log n) ^ (j + 1) * (n : ℝ) ^ (-η) : ℝ) : ℂ)
        * (if n.Prime ∧ X₁ < (n : ℝ) then
            χ n * (Real.log n : ℂ) * (n : ℂ) ^ (-(1 : ℂ) - (τ : ℂ) * Complex.I) else 0) :=
    ⟨_, rfl⟩
  obtain ⟨LS, hLSdef⟩ : ∃ z : ℂ, z = LSeries (fun n : ℕ => (Real.log n : ℂ) ^ (j + 1)
      * (χ (n : ZMod q) * (vonMangoldt n : ℂ))) (((1 + η : ℝ) : ℂ) + τ * I) := ⟨_, rfl⟩
  rw [← hDwin, ← hLSdef] at hwin
  rw [← hLSdef] at hLS
  have hDwin_lb : ((j + 1).factorial : ℝ) * (3/8 * Q) ≤ ‖Dwin‖ := by
    have h1 := norm_sub_norm_le LS Dwin
    linarith [hwin, hT1, hT2, hT3, hLS]
  -- Abel summation
  have habel := abel_window χ τ (η := η) hX₁pos hX₁X₂ j
  rw [← hDwin] at habel
  obtain ⟨J, hJdef⟩ : ∃ z : ℂ,
      z = ∫ t in Set.Ioc X₁ X₂, (detKernel η j t : ℂ) * primeWindowSum χ τ X₁ t := ⟨_, rfl⟩
  rw [← hJdef] at habel
  -- the boundary term at `X₂`
  have hbdry : ‖(((Real.log X₂) ^ (j + 1) * X₂ ^ (-η) : ℝ) : ℂ) * primeWindowSum χ τ X₁ X₂‖
      ≤ ((j + 1).factorial : ℝ) * (Q / 8) := by
    have hS := norm_primeWindowSum_le χ τ X₁ hX₂20 (le_refl X₂)
    have hφ0 : 0 ≤ (Real.log X₂) ^ (j + 1) * X₂ ^ (-η) := by
      have : 0 ≤ Real.log X₂ := Real.log_nonneg (by linarith [hX₁ge1])
      have := Real.rpow_nonneg hX₂pos.le (-η)
      positivity
    have he : Real.exp (16 * (M:ℝ) / η) ^ (-η) = Real.exp (-(16 * (M:ℝ))) := by
      rw [← Real.exp_mul]; congr 1; field_simp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hφ0]
    calc (Real.log X₂) ^ (j + 1) * X₂ ^ (-η) * ‖primeWindowSum χ τ X₁ X₂‖
        ≤ (Real.log X₂) ^ (j + 1) * X₂ ^ (-η) * (Real.exp 1 * (Real.log X₂ + 2)) :=
          mul_le_mul_of_nonneg_left hS hφ0
      _ = (16 * (M:ℝ) / η) ^ (j + 1) * Real.exp (-(16 * (M:ℝ)))
            * (Real.exp 1 * (16 * (M:ℝ) / η + 2)) := by
          rw [hlogX₂, hX₂eq, he]
      _ ≤ ((j + 1).factorial : ℝ) * (Q / 8) := hB6
  have hJ_lb : ((j + 1).factorial : ℝ) * (1/4 * Q) ≤ ‖J‖ := by
    have h1 : Dwin = (((Real.log X₂) ^ (j + 1) * X₂ ^ (-η) : ℝ) : ℂ)
        * primeWindowSum χ τ X₁ X₂ - J := habel
    have h2 : ‖Dwin‖ ≤ ‖(((Real.log X₂) ^ (j + 1) * X₂ ^ (-η) : ℝ) : ℂ)
        * primeWindowSum χ τ X₁ X₂‖ + ‖J‖ := by
      rw [h1]; exact norm_sub_le _ _
    linarith [hDwin_lb, hbdry]
  -- §4.4 step 5: the endgame
  obtain ⟨C₇, hC₇def⟩ : ∃ c : ℝ, c = 17 * ((j : ℝ) + 1) * (j.factorial : ℝ) / η ^ j := ⟨_, rfl⟩
  have hC₇0 : 0 < C₇ := by rw [hC₇def]; positivity
  obtain ⟨G, hGdef⟩ : ∃ g : ℝ, g = ((j + 1).factorial : ℝ) * Q / (4 * C₇) := ⟨_, rfl⟩
  have hG0 : 0 < G := by rw [hGdef]; positivity
  have hGC : G * C₇ = ((j + 1).factorial : ℝ) * (1/4 * Q) := by
    rw [hGdef]; field_simp
  have hK0 : 0 < 16 * (M:ℝ) / η := by positivity
  have hKlog : Real.log X₂ - Real.log X₁ ≤ 16 * (M:ℝ) / η := by
    rw [hlogX₁, hlogX₂]
    have : 0 ≤ (M:ℝ) / (16 * η) := by positivity
    linarith
  have hSb : ∀ u ∈ Set.Icc X₁ X₂, ‖primeWindowSum χ τ X₁ u‖ ≤ Real.exp 1 * (Real.log X₂ + 2) :=
    fun u hu => norm_primeWindowSum_le χ τ X₁ hX₂20 hu.2
  have hψ : ∀ u ∈ Set.Icc X₁ X₂, |detKernel η j u| * u ≤ C₇ := by
    intro u hu
    rw [hC₇def]
    have hu1 : 1 ≤ u := le_trans hX₁ge1 hu.1
    have hlogu : η * Real.log u ≤ 16 * M := by
      have h1 : Real.log u ≤ Real.log X₂ := Real.log_le_log (by linarith) hu.2
      rw [hlogX₂] at h1
      have h2 : η * Real.log u ≤ η * (16 * (M:ℝ) / η) := mul_le_mul_of_nonneg_left h1 hη0.le
      have h3 : η * (16 * (M:ℝ) / η) = 16 * M := by field_simp
      linarith
    exact abs_detKernel_mul_le hη0 hjM hu1 hlogu
  have hJ' : J = ∫ t in X₁..X₂, (detKernel η j t : ℂ) * primeWindowSum χ τ X₁ t := by
    rw [hJdef, intervalIntegral.integral_of_le hX₁X₂]
  have hlow : G * C₇ ≤ ‖∫ t in X₁..X₂, (detKernel η j t : ℂ) * primeWindowSum χ τ X₁ t‖ := by
    rw [hGC, ← hJ']; exact hJ_lb
  have hI := integral_normSq_div_ge (S := fun u => primeWindowSum χ τ X₁ u)
    (ψ := detKernel η j) hX₁pos hX₁X₂ (measurable_primeWindowSum χ τ X₁) hSb hψ hC₇0
    hKlog hK0 hG0 hlow
  -- the numeric endgame
  have hGeq : G = Q * η ^ j / 68 := by
    rw [hGdef, hC₇def, Nat.factorial_succ]
    push_cast
    have hη : η ^ j ≠ 0 := by positivity
    have hj1 : ((j:ℝ) + 1) ≠ 0 := by positivity
    have hjf : (j.factorial : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  have hB7 := budget_endgame (η := η) (N := N) (M := M) (k := j + 2) (j := j) hη0
    (by linarith) hM6 hk2' rfl
  rw [← hQdef, ← hGeq] at hB7
  have hI' : η * G ^ 2 / (16 * (M:ℝ)) ≤ ∫ u in X₁..X₂, ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u := by
    have : η * G ^ 2 / (16 * (M:ℝ)) = G ^ 2 / (16 * (M:ℝ) / η) := by
      field_simp
    rw [this]
    exact hI
  calc (1:ℝ) ≤ η ^ 3 * (M:ℝ) * Real.exp (6 * (M:ℝ)) * (η * G ^ 2 / (16 * (M:ℝ))) := hB7
    _ ≤ η ^ 3 * (M:ℝ) * Real.exp (6 * (M:ℝ))
          * ∫ u in X₁..X₂, ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u :=
        mul_le_mul_of_nonneg_left hI' (by positivity)

end Main

end

end Carmichael
