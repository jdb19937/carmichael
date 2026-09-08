/-
Route Z, sortie Z4c: Landau partial-fraction expansion of `L′/L`, d-uniform.

MAIN RESULTS (all constants explicit numerals; `N` = the modulus, `χ ≠ 1`):

* `zeroDiskFinset χ t₀ : Finset ℂ` — the distinct zeros of
  `DirichletCharacter.LFunction χ` in the disk `closedBall (2 + it₀) (13/8)`;
  membership characterized by `mem_zeroDiskFinset` (for `χ ≠ 1`).  This is the
  disk-shaped companion of `ZeroCount.zeroFinset`; multiplicities are
  `analyticOrderNatAt (LFunction χ) ρ`, exactly as in the Z4b contract.

* `norm_logDeriv_sub_sum_zeroDiskFinset_le` — **the Landau expansion**: for
  nontrivial `χ mod N`, every `t₀ : ℝ`, and every `s ∈ closedBall (2+it₀) (3/2)`
  with `L(s,χ) ≠ 0`,
    `‖L′/L(s,χ) − ∑_{ρ ∈ zeroDiskFinset χ t₀} ord(ρ)/(s−ρ)‖
       ≤ 520000 · log (N·(|t₀|+2))`.
  Radii: expansion valid on the closed `3/2`-disk, zeros collected from the
  closed `13/8`-disk (the Z4b geometry), all centered `2 + it₀`.

* `exists_good_line` — **good horizontal lines** (the Z5 rectangle-side input):
  for every `T ≥ 2` there is `t₀ ∈ [T, T+1]` with
    `L(σ+it₀, χ) ≠ 0` and `‖L′/L(σ+it₀, χ)‖ ≤ 10⁶·(log(N(T+4)))²`
  for ALL `σ ∈ [1/2, 3]`.  Engine: a zero-spacing pigeonhole
  (`exists_gap_point`) against a census of the zero ordinates of seven
  `13/8`-disks at half-integer grid heights (`exists_grid_cover`), giving
  `|t₀ − Im ρ| ≥ 1/(2(|Γ|+1))` with `|Γ| ≤ 784·log(N(T+4))`; zeros with
  `Re ρ ≤ 7/16` are separated from the segment in the real direction instead.
  NOTE the range `σ ∈ [1/2, 3]`: the segment `σ ∈ [−1/4, 1/2)` of the Z5
  rectangle cannot be reached from the frozen Z4b disk geometry (disks of
  radius `13/8` centered on `Re = 2` stop at `Re = 3/8`); that edge needs the
  functional-equation reflection and must be supplied by Z5 separately.

PROOF SHAPE (Davenport ch. 15, via Borel–Carathéodory — no Hadamard product):
write `L = P·h` with `P(z) = ∏_{ρ ∈ K}(z−ρ)^{m_ρ}` over the `13/8`-disk zeros
`K` (Mathlib `MeromorphicOn.extract_zeros_poles` on `closedBall c (7/4)`, with
the annulus zeros multiplied back into `h`), so `h` is analytic on the closed
`7/4`-disk and zero-free on the closed `13/8`-disk.  On the `7/4`-sphere every
`ρ ∈ K` is `≥ 1/8` away, so `‖h‖ ≤ 15X·8ⁿ` there (`X := N(|t₀|+2)`,
`n := ∑ m_ρ ≤ 112 log X` by Z4b); the maximum principle transports this bound
inside.  At the center `‖h(c)‖ ≥ (1/3)·2⁻ⁿ`.  An analytic logarithm `φ` of `h`
on `ball c (13/8)` is built from a primitive of `h′/h` (Mathlib
`DifferentiableOn.isExactOn_ball`); then `Re(φ−φ(c)) ≤ log(45X) + n·log 16
≤ 325·log X =: M`, Borel–Carathéodory gives `‖φ−φ(c)‖ ≤ 50M` on the
`25/16`-disk, and the Schwarz-lemma derivative bound on `1/16`-balls gives
`‖h′/h‖ = ‖φ′‖ ≤ 1600M ≤ 520000·log X` on the `3/2`-disk.  Finally
`L′/L = ∑_ρ m_ρ/(s−ρ) + h′/h` by `logDeriv_prod`.

Consumed by Z5 (explicit formula); see BVPLAN.md §4 item Z4c.
-/
import Carmichael.LGrowth
import Carmichael.ZeroCount
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Topology.Perfect

namespace Carmichael

open Complex Finset Filter Set Metric
open scoped Topology

/-! ### Elementary helpers -/

section Helpers

/-- `log (45·X) ≤ 7 log X` for `X ≥ 2`. -/
lemma log_fortyfive_mul_le {X : ℝ} (hX : 2 ≤ X) :
    Real.log (45 * X) ≤ 7 * Real.log X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have h1 : Real.log (45 * X) = Real.log 45 + Real.log X :=
    Real.log_mul (by norm_num) (ne_of_gt hX0)
  have h45 : (45 : ℝ) ≤ X ^ 6 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hX 6
    nlinarith
  have h2 : Real.log 45 ≤ Real.log (X ^ 6) := Real.log_le_log (by norm_num) h45
  rw [Real.log_pow] at h2
  push_cast at h2
  linarith

/-- `log 16 ≤ 2.78`. -/
lemma log_sixteen_le : Real.log 16 ≤ 2.78 := by
  have h : (16 : ℝ) = 2 ^ 4 := by norm_num
  rw [h, Real.log_pow]
  have := Real.log_two_lt_d9
  push_cast
  linarith

/-- Every point of a closed ball of positive radius in `ℂ` is an accumulation
point of the ball. -/
lemma accPt_closedBall {c : ℂ} {r : ℝ} (hr : 0 < r) {x : ℂ}
    (hx : x ∈ closedBall c r) : AccPt x (𝓟 (closedBall c r)) := by
  have hnt : (closedBall c r).Nontrivial := by
    refine ⟨c, mem_closedBall_self hr.le, c + r, ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm]
      simp [abs_of_pos hr]
    · intro h
      have h0 : (r : ℂ) = 0 := by linear_combination h.symm
      exact hr.ne' (Complex.ofReal_eq_zero.mp h0)
  have hpre : Preperfect (closedBall c r) :=
    IsPreconnected.preperfect_of_nontrivial hnt
      (convex_closedBall c r).isPreconnected
  exact hpre x hx

/-- Meromorphic functions that are continuous on a set of accumulation points
and agree on a codiscrete-within subset agree everywhere on the set. -/
lemma eq_on_of_meromorphic_of_codiscreteWithin {f g : ℂ → ℂ} {U : Set ℂ}
    (hU : ∀ x ∈ U, AccPt x (𝓟 U))
    (hf : ∀ x ∈ U, MeromorphicAt f x) (hg : ∀ x ∈ U, MeromorphicAt g x)
    (hfc : ∀ x ∈ U, ContinuousAt f x) (hgc : ∀ x ∈ U, ContinuousAt g x)
    (h : f =ᶠ[Filter.codiscreteWithin U] g) : ∀ x ∈ U, f x = g x := by
  intro x hx
  have hev : f =ᶠ[𝓝[≠] x] g :=
    (hf x hx).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      (hg x hx) hx (hU x hx) h
  have h1 : Tendsto f (𝓝[≠] x) (𝓝 (f x)) :=
    ((hfc x hx).tendsto).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto g (𝓝[≠] x) (𝓝 (g x)) :=
    ((hgc x hx).tendsto).mono_left nhdsWithin_le_nhds
  have h3 : Tendsto f (𝓝[≠] x) (𝓝 (g x)) := h2.congr' hev.symm
  exact tendsto_nhds_unique h1 h3

end Helpers

/-! ### The disk zero Finset -/

section ZeroDisk

variable {N : ℕ} [NeZero N]

/-- Zeros of `L(·,χ)` in the closed disk of radius `13/8` around `2 + it₀`
(the Z4b disk geometry). -/
def LZerosDisk (χ : DirichletCharacter ℂ N) (t₀ : ℝ) : Set ℂ :=
  {s ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ) | DirichletCharacter.LFunction χ s = 0}

/-- `L(2,χ) ≠ 0` for every Dirichlet character. -/
lemma LFunction_two_ne_zero (χ : DirichletCharacter ℂ N) :
    DirichletCharacter.LFunction χ 2 ≠ 0 := by
  intro h
  have h13 := one_third_le_norm_LFunction_of_two_le_re χ (s := 2) (by norm_num)
  rw [h, norm_zero] at h13
  linarith

/-- For nontrivial `χ` the disk zero set is finite. -/
lemma finite_LZerosDisk (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (t₀ : ℝ) :
    (LZerosDisk χ t₀).Finite :=
  finite_zeros_inter_compact (DirichletCharacter.differentiable_LFunction hχ)
    (LFunction_two_ne_zero χ) (isCompact_closedBall _ _)

open scoped Classical in
/-- **The nearby-zero Finset for the Landau expansion**: the distinct zeros of
`L(·,χ)` in `closedBall (2+it₀) (13/8)`.  (Junk value `∅` for the principal
character, where the zero set may fail to be recognizably finite.)  Sum over
this Finset with multiplicity weight `analyticOrderNatAt (LFunction χ) ρ`. -/
noncomputable def zeroDiskFinset (χ : DirichletCharacter ℂ N) (t₀ : ℝ) : Finset ℂ :=
  if h : (LZerosDisk χ t₀).Finite then h.toFinset else ∅

lemma mem_zeroDiskFinset {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {t₀ : ℝ} {ρ : ℂ} :
    ρ ∈ zeroDiskFinset χ t₀ ↔
      ρ ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ)
        ∧ DirichletCharacter.LFunction χ ρ = 0 := by
  rw [zeroDiskFinset, dif_pos (finite_LZerosDisk χ hχ t₀), Set.Finite.mem_toFinset]
  rfl

/-- Z4b mass bound for the disk zeros: total multiplicity `≤ 112 log (N(|t₀|+2))`. -/
lemma sum_ord_zeroDiskFinset_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t₀ : ℝ) :
    (∑ ρ ∈ zeroDiskFinset χ t₀,
        analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
      ≤ 112 * Real.log (N * (|t₀| + 2)) :=
  sum_ord_LFunction_disk_le χ hχ t₀
    (fun _ρ hρ => ((mem_zeroDiskFinset hχ).mp hρ).1)

end ZeroDisk

/-! ### Factorization `L = P·h` on the `7/4`-disk -/

section Factorization

variable {N : ℕ} [NeZero N]

/-- `L(·,χ)` has finite vanishing order at every point of the `7/4`-disk
(identity theorem against `‖L(2+it₀,χ)‖ ≥ 1/3`). -/
lemma analyticOrderAt_ne_top_on_disk {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (t₀ : ℝ) {u : ℂ} (hu : u ∈ closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ)) :
    analyticOrderAt (DirichletCharacter.LFunction χ) u ≠ ⊤ := by
  intro htop
  have hA : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ)
      (closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ)) :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hev : DirichletCharacter.LFunction χ =ᶠ[𝓝 u] 0 := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz using hz
  have hEq : Set.EqOn (DirichletCharacter.LFunction χ) 0
      (closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ)) :=
    hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_closedBall _ _).isPreconnected hu hev
  have hc : DirichletCharacter.LFunction χ ((2:ℂ) + t₀ * I) = 0 :=
    hEq (mem_closedBall_self (by norm_num))
  have h13 := one_third_le_norm_LFunction_of_two_le_re χ
    (s := (2:ℂ) + t₀ * I) (by rw [re_center])
  rw [hc, norm_zero] at h13
  linarith

/-- **Factorization.**  For nontrivial `χ` there is `h`, analytic on the closed
`7/4`-disk around `c = 2+it₀`, with
`L(z) = ∏_{ρ ∈ K}(z−ρ)^{m ρ} · h(z)` on that disk and `h ≠ 0` on the closed
`13/8`-subdisk, where `K = zeroDiskFinset χ t₀` and `m = analyticOrderNatAt L`. -/
theorem exists_LFunction_factorization {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (t₀ : ℝ) :
    ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ)) ∧
      (∀ z ∈ closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ),
        DirichletCharacter.LFunction χ z
          = (∏ ρ ∈ zeroDiskFinset χ t₀,
              (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) * h z) ∧
      (∀ z ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ), h z ≠ 0) := by
  classical
  set c : ℂ := (2:ℂ) + t₀ * I with hcdef
  set U : Set ℂ := closedBall c (7/4 : ℝ) with hUdef
  set L : ℂ → ℂ := DirichletCharacter.LFunction χ with hLdef
  set m : ℂ → ℕ := fun ρ => analyticOrderNatAt L ρ with hmdef
  have hL_diff : Differentiable ℂ L := DirichletCharacter.differentiable_LFunction hχ
  have hA : AnalyticOnNhd ℂ L U := fun z _ => hL_diff.analyticAt z
  have hMero : MeromorphicOn L U := hA.meromorphicOn
  have hUc : IsCompact U := isCompact_closedBall c (7/4 : ℝ)
  have hordU : ∀ u ∈ U, analyticOrderAt L u ≠ ⊤ := fun u hu =>
    analyticOrderAt_ne_top_on_disk hχ t₀ hu
  have h₂f : ∀ u : U, meromorphicOrderAt L u ≠ ⊤ := by
    intro u
    rw [(hA u u.2).meromorphicOrderAt_eq, ne_eq, ENat.map_eq_top_iff]
    exact hordU u u.2
  have h₃f : (MeromorphicOn.divisor L U).support.Finite :=
    (MeromorphicOn.divisor L U).finiteSupport hUc
  obtain ⟨g, hg_an, hg_ne, heq⟩ := hMero.extract_zeros_poles h₂f h₃f
  -- divisor values are the analytic orders
  have hDval : ∀ u ∈ U, MeromorphicOn.divisor L U u = (m u : ℤ) := by
    intro u hu
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hA hu,
      ← Nat.cast_analyticOrderNatAt (hordU u hu)]
    rfl
  -- the support Finset
  set Z : Finset ℂ := h₃f.toFinset with hZdef
  have hZsubU : ∀ u ∈ Z, u ∈ U := fun u hu =>
    (MeromorphicOn.divisor L U).supportWithinDomain (h₃f.mem_toFinset.mp hu)
  have hZzero : ∀ u ∈ Z, L u = 0 := by
    intro u hu
    have hne : MeromorphicOn.divisor L U u ≠ 0 := h₃f.mem_toFinset.mp hu
    by_contra hLu
    have h0 : analyticOrderAt L u = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hLu)
    have h1 : m u = 0 := by rw [hmdef]; simp [analyticOrderNatAt, h0]
    rw [hDval u (hZsubU u hu), h1] at hne
    exact hne (by norm_num)
  have hKsubZ : ∀ ρ ∈ zeroDiskFinset χ t₀, ρ ∈ Z := by
    intro ρ hρ
    obtain ⟨hρ13, hρ0⟩ := (mem_zeroDiskFinset hχ).mp hρ
    have hρU : ρ ∈ U := closedBall_subset_closedBall (by norm_num) hρ13
    rw [hZdef, h₃f.mem_toFinset]
    show MeromorphicOn.divisor L U ρ ≠ 0
    rw [hDval ρ hρU]
    have hne0 : analyticOrderAt L ρ ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hL_diff.analyticAt ρ, hρ0⟩
    have h1 : m ρ ≠ 0 := by
      rw [hmdef]
      intro h0
      rcases ENat.toNat_eq_zero.mp h0 with h | h
      · exact hne0 h
      · exact hordU ρ hρU h
    exact_mod_cast h1
  have hZ13 : ∀ u ∈ Z, u ∈ closedBall c (13/8 : ℝ) → u ∈ zeroDiskFinset χ t₀ :=
    fun u hu h13 => (mem_zeroDiskFinset hχ).mpr ⟨h13, hZzero u hu⟩
  -- identify the factorized rational function with a Finset product
  have hPfull : (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor L U u))
      = fun z => ∏ u ∈ Z, (z - u) ^ (m u) := by
    have hsub : (fun u => (· - u) ^ (MeromorphicOn.divisor L U u)).mulSupport ⊆ ↑Z := by
      rw [Function.FactorizedRational.mulSupport]
      intro u hu
      have : MeromorphicOn.divisor L U u ≠ 0 := hu
      simpa [hZdef, h₃f.mem_toFinset] using this
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
    funext z
    rw [Finset.prod_apply]
    refine Finset.prod_congr rfl fun u hu => ?_
    rw [Pi.pow_apply, hDval u (hZsubU u hu), zpow_natCast]
  -- entire product functions
  have hProdDiff : ∀ S : Finset ℂ, Differentiable ℂ (fun z => ∏ u ∈ S, (z - u) ^ (m u)) := by
    intro S
    have hrw : (fun z => ∏ u ∈ S, (z - u) ^ (m u))
        = ∏ u ∈ S, fun z => (z - u) ^ (m u) := by
      funext z; rw [Finset.prod_apply]
    rw [hrw]
    apply Differentiable.finsetProd
    intro u _
    exact (differentiable_id.sub_const u).pow _
  -- pointwise factorization over all of U
  have hfac : ∀ z ∈ U, L z = (∏ u ∈ Z, (z - u) ^ (m u)) * g z := by
    have heq' : L =ᶠ[Filter.codiscreteWithin U]
        fun z => (∏ u ∈ Z, (z - u) ^ (m u)) * g z := by
      filter_upwards [heq] with z hz
      calc L z = ((∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor L U u)) • g) z := hz
        _ = (∏ᶠ u, (· - u) ^ (MeromorphicOn.divisor L U u)) z * g z := by
            simp [Pi.smul_apply']
        _ = (∏ u ∈ Z, (z - u) ^ (m u)) * g z := by rw [hPfull]
    have hUacc : ∀ x ∈ U, AccPt x (𝓟 U) := fun x hx =>
      accPt_closedBall (by norm_num) hx
    exact eq_on_of_meromorphic_of_codiscreteWithin hUacc
      (fun x hx => (hA x hx).meromorphicAt)
      (fun x hx => (((hProdDiff Z).analyticAt x).mul (hg_an x hx)).meromorphicAt)
      (fun x _hx => hL_diff.continuous.continuousAt)
      (fun x hx => ((hProdDiff Z).continuous.continuousAt.mul
        (hg_an x hx).continuousAt))
      heq'
  -- split off the disk zeros
  have hKZ : zeroDiskFinset χ t₀ ⊆ Z := fun ρ hρ => hKsubZ ρ hρ
  refine ⟨fun z => (∏ u ∈ Z \ zeroDiskFinset χ t₀, (z - u) ^ (m u)) * g z, ?_, ?_, ?_⟩
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

end Factorization

/-! ### Analytic logarithm on a disk, via primitives -/

section AnalyticLog

/-- **Analytic logarithm.**  A nonvanishing analytic function on an open disk is
`exp` of a function whose derivative is the logarithmic derivative.  Built from a
primitive of `h′/h` (Morera machinery, `DifferentiableOn.isExactOn_ball`). -/
lemma exists_exp_eq_of_forall_ne_zero {h : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (han : ∀ z ∈ ball c r, AnalyticAt ℂ h z)
    (hne : ∀ z ∈ ball c r, h z ≠ 0) :
    ∃ φ : ℂ → ℂ, (∀ z ∈ ball c r, HasDerivAt φ (deriv h z / h z) z) ∧
      (∀ z ∈ ball c r, Complex.exp (φ z) = h z) := by
  have hcball : c ∈ ball c r := mem_ball_self hr
  have hq_diff : DifferentiableOn ℂ (fun z => deriv h z / h z) (ball c r) := by
    intro z hz
    exact (((han z hz).deriv.differentiableAt).div
      (han z hz).differentiableAt (hne z hz)).differentiableWithinAt
  obtain ⟨F, hFc, hF⟩ := (hq_diff.isExactOn_ball).with_val_at c (Complex.log (h c))
  -- `h · exp (−F)` has zero derivative on the ball
  have hderiv : ∀ z ∈ ball c r,
      HasDerivWithinAt (fun w => h w * Complex.exp (-F w)) 0 (ball c r) z := by
    intro z hz
    have h1 : HasDerivAt h (deriv h z) z := (han z hz).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun w => Complex.exp (-F w))
        (Complex.exp (-F z) * -(deriv h z / h z)) z := ((hF z hz).neg).cexp
    have h3 : HasDerivAt (fun w => h w * Complex.exp (-F w)) 0 z := by
      have h4 := h1.mul h2
      beta_reduce at h4
      have hz0 : h z ≠ 0 := hne z hz
      have hval : deriv h z * Complex.exp (-F z)
          + h z * (Complex.exp (-F z) * -(deriv h z / h z)) = 0 := by
        field_simp
        ring
      rw [hval] at h4
      exact h4
    exact h3.hasDerivWithinAt
  -- hence constant, equal to `h c · exp(−log h c) = 1`
  have hu : ∀ z ∈ ball c r, h z * Complex.exp (-F z) = 1 := by
    intro z hz
    have hkey := (convex_ball c r).norm_image_sub_le_of_norm_hasDerivWithin_le
      hderiv (C := 0) (fun w _ => by simp) hcball hz
    have h0 : h z * Complex.exp (-F z) = h c * Complex.exp (-F c) := by
      have h1 : ‖h z * Complex.exp (-F z) - h c * Complex.exp (-F c)‖ ≤ 0 := by
        simpa using hkey
      have := norm_le_zero_iff.mp h1
      linear_combination this
    rw [h0, hFc, Complex.exp_neg, Complex.exp_log (hne c hcball),
      mul_inv_cancel₀ (hne c hcball)]
  refine ⟨F, hF, fun z hz => ?_⟩
  have h1 := hu z hz
  rw [Complex.exp_neg] at h1
  exact ((mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp h1).symm

end AnalyticLog

/-! ### Borel–Carathéodory + Schwarz: the derivative bound -/

section BCSchwarz

/-- **Logarithmic-derivative bound from `log`-norm bounds.**  If `h` is analytic
and zero-free on `ball c (13/8)` and `log‖h z‖ − log‖h c‖ ≤ M` there, then
`‖h′/h‖ ≤ 1600·M` on `closedBall c (3/2)`.  (Borel–Carathéodory on the full
disk, then the Schwarz-lemma derivative estimate on `1/16`-balls.) -/
lemma norm_logDeriv_le_of_log_norm_bound {h : ℂ → ℂ} {c : ℂ} {M : ℝ} (hM : 0 < M)
    (han : ∀ z ∈ ball c (13/8 : ℝ), AnalyticAt ℂ h z)
    (hne : ∀ z ∈ ball c (13/8 : ℝ), h z ≠ 0)
    (hre : ∀ z ∈ ball c (13/8 : ℝ), Real.log ‖h z‖ - Real.log ‖h c‖ ≤ M)
    {s : ℂ} (hs : s ∈ closedBall c (3/2 : ℝ)) :
    ‖deriv h s / h s‖ ≤ 1600 * M := by
  have hc_ball : c ∈ ball c (13/8 : ℝ) := mem_ball_self (by norm_num)
  obtain ⟨φ, hφd, hφe⟩ := exists_exp_eq_of_forall_ne_zero (by norm_num) han hne
  have hφre : ∀ z ∈ ball c (13/8 : ℝ), (φ z).re = Real.log ‖h z‖ := by
    intro z hz
    have h1 : ‖h z‖ = Real.exp (φ z).re := by rw [← hφe z hz, Complex.norm_exp]
    rw [h1, Real.log_exp]
  -- recenter
  have hmemtrans : ∀ w : ℂ, w ∈ ball (0:ℂ) (13/8 : ℝ) → c + w ∈ ball c (13/8 : ℝ) := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
    exact hw
  have hψderiv : ∀ w ∈ ball (0:ℂ) (13/8 : ℝ),
      HasDerivAt (fun w => φ (c + w) - φ c) (deriv h (c + w) / h (c + w)) w := by
    intro w hw
    have h1 := hφd (c + w) (hmemtrans w hw)
    have h2 : HasDerivAt (fun x : ℂ => c + x) 1 w := (hasDerivAt_id w).const_add c
    have h3 : HasDerivAt (fun x : ℂ => φ (c + x))
        (deriv h (c + w) / h (c + w) * 1) w := h1.comp w h2
    rw [mul_one] at h3
    exact h3.sub_const (φ c)
  have hψdiff : DifferentiableOn ℂ (fun w => φ (c + w) - φ c) (ball (0:ℂ) (13/8 : ℝ)) :=
    fun w hw => ((hψderiv w hw).differentiableAt).differentiableWithinAt
  have hψ0 : (fun w => φ (c + w) - φ c) 0 = 0 := by simp
  have hψre : Set.MapsTo (fun w => φ (c + w) - φ c) (ball (0:ℂ) (13/8 : ℝ))
      {z : ℂ | z.re ≤ M} := by
    intro w hw
    have hz := hmemtrans w hw
    show (φ (c + w) - φ c).re ≤ M
    rw [Complex.sub_re, hφre _ hz, hφre c hc_ball]
    exact hre _ hz
  -- Borel–Carathéodory value bound on the 25/16-disk
  have hBC : ∀ w : ℂ, ‖w‖ ≤ 25/16 → ‖φ (c + w) - φ c‖ ≤ 50 * M := by
    intro w hw
    have hwball : w ∈ ball (0:ℂ) (13/8 : ℝ) := by
      rw [mem_ball, dist_zero_right]
      linarith
    have h1 := Complex.borelCaratheodory_zero hM hψdiff hψre
      (by norm_num : (0:ℝ) < 13/8) hwball hψ0
    have hden : (1/16 : ℝ) ≤ 13/8 - ‖w‖ := by linarith
    calc ‖φ (c + w) - φ c‖ ≤ 2 * M * ‖w‖ / (13/8 - ‖w‖) := by
          simpa using h1
      _ ≤ (2 * M * (25/16)) / (1/16) :=
          div_le_div₀ (by positivity)
            (by nlinarith [norm_nonneg w]) (by norm_num) hden
      _ = 50 * M := by ring
  -- Schwarz derivative bound at `w₀ = s − c`
  have hw₀ : ‖s - c‖ ≤ 3/2 := by
    rw [mem_closedBall, dist_eq_norm] at hs
    exact hs
  have hmaps : Set.MapsTo (fun w => φ (c + w) - φ c) (ball (s - c) (1/16 : ℝ))
      (closedBall ((fun w => φ (c + w) - φ c) (s - c)) (100 * M)) := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    have hwn : ‖w‖ ≤ 25/16 := by
      calc ‖w‖ = ‖(w - (s - c)) + (s - c)‖ := by ring_nf
        _ ≤ ‖w - (s - c)‖ + ‖s - c‖ := norm_add_le _ _
        _ ≤ 25/16 := by linarith
    rw [mem_closedBall, dist_eq_norm]
    calc ‖(φ (c + w) - φ c) - (φ (c + (s - c)) - φ c)‖
        ≤ ‖φ (c + w) - φ c‖ + ‖φ (c + (s - c)) - φ c‖ := norm_sub_le _ _
      _ ≤ 50 * M + 50 * M := add_le_add (hBC w hwn) (hBC (s - c) (by linarith))
      _ = 100 * M := by ring
  have hψdiff' : DifferentiableOn ℂ (fun w => φ (c + w) - φ c)
      (ball (s - c) (1/16 : ℝ)) := by
    apply hψdiff.mono
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    calc ‖w‖ = ‖(w - (s - c)) + (s - c)‖ := by ring_nf
      _ ≤ ‖w - (s - c)‖ + ‖s - c‖ := norm_add_le _ _
      _ < 13/8 := by linarith
  have hSch := Complex.norm_deriv_le_div_of_mapsTo_ball hψdiff' hmaps
    (by norm_num : (0:ℝ) < 1/16)
  have hderiv_eq : deriv (fun w => φ (c + w) - φ c) (s - c) = deriv h s / h s := by
    have h1 := hψderiv (s - c) (by
      rw [mem_ball, dist_zero_right]
      linarith)
    have h2 : c + (s - c) = s := by ring
    rw [h2] at h1
    exact h1.deriv
  rw [hderiv_eq] at hSch
  calc ‖deriv h s / h s‖ ≤ 100 * M / (1/16) := hSch
    _ = 1600 * M := by ring

end BCSchwarz

/-! ### The Landau partial-fraction expansion -/

section Landau

variable {N : ℕ} [NeZero N]

/-- **Z4c main theorem: the Landau partial-fraction expansion of `L′/L`.**
For nontrivial `χ mod N`, every `t₀ : ℝ`, and every `s` in the closed
`3/2`-disk around `2 + it₀` that is not a zero of `L`,
`L′/L(s,χ)` equals `∑_ρ ord(ρ)/(s−ρ)` over the distinct zeros `ρ` of `L(·,χ)`
in the closed `13/8`-disk around `2 + it₀`, up to an error of at most
`520000·log(N(|t₀|+2))`. -/
theorem norm_logDeriv_sub_sum_zeroDiskFinset_le {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (t₀ : ℝ) {s : ℂ}
    (hs : s ∈ closedBall ((2:ℂ) + t₀ * I) (3/2 : ℝ))
    (hLs : DirichletCharacter.LFunction χ s ≠ 0) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
      - ∑ ρ ∈ zeroDiskFinset χ t₀,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖
      ≤ 520000 * Real.log ((N : ℝ) * (|t₀| + 2)) := by
  obtain ⟨h, hh_an, hh_fac, hh_ne⟩ := exists_LFunction_factorization hχ t₀
  set c : ℂ := (2:ℂ) + t₀ * I with hcdef
  set X : ℝ := (N : ℝ) * (|t₀| + 2) with hXdef
  -- numerics
  have hN1 : (1:ℝ) ≤ N := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have ht0 : (0:ℝ) ≤ |t₀| := abs_nonneg t₀
  have hX2 : (2:ℝ) ≤ X := by rw [hXdef]; nlinarith
  have hX0 : (0:ℝ) < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  -- zero mass
  set n : ℕ := ∑ ρ ∈ zeroDiskFinset χ t₀,
      analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ with hndef
  have hn : (n : ℝ) ≤ 112 * Real.log X := by
    have h0 := sum_ord_zeroDiskFinset_le hχ t₀
    rw [hndef]
    push_cast
    exact h0
  -- geometry of `s`
  have hs13 : s ∈ ball c (13/8 : ℝ) := by
    rw [mem_closedBall] at hs
    rw [mem_ball]
    linarith
  have hs13c : s ∈ closedBall c (13/8 : ℝ) := ball_subset_closedBall hs13
  have hsU : s ∈ closedBall c (7/4 : ℝ) :=
    closedBall_subset_closedBall (by norm_num) hs13c
  have hball13_sub : ball c (13/8 : ℝ) ⊆ closedBall c (7/4 : ℝ) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by norm_num))
  -- ‖h‖ on the 7/4-sphere
  have hsphere : ∀ z ∈ sphere c (7/4 : ℝ), ‖h z‖ ≤ 15 * X * 8^n := by
    intro z hz
    have hzU : z ∈ closedBall c (7/4 : ℝ) := sphere_subset_closedBall hz
    have hLz : ‖DirichletCharacter.LFunction χ z‖ ≤ 15 * X := by
      have h1 := norm_LFunction_le_of_one_quarter_le_re χ hχ (disk_re_ge hzU)
      have h2 := disk_norm_le hzU
      rw [hXdef]
      nlinarith
    have hPz : ((1:ℝ)/8)^n ≤ ‖∏ ρ ∈ zeroDiskFinset χ t₀,
        (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ‖ := by
      rw [norm_prod, hndef, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun ρ _ => by positivity) (fun ρ hρ => ?_)
      rw [norm_pow]
      refine pow_le_pow_left₀ (by norm_num) ?_ _
      have hρc : dist ρ c ≤ 13/8 :=
        mem_closedBall.mp ((mem_zeroDiskFinset hχ).mp hρ).1
      have hzc : dist z c = 7/4 := mem_sphere.mp hz
      have htri := dist_triangle z ρ c
      rw [← dist_eq_norm]
      linarith
    have h8n : (0:ℝ) < (1/8:ℝ)^n := by positivity
    have h1 : (1/8:ℝ)^n * ‖h z‖ ≤ 15 * X := by
      calc (1/8:ℝ)^n * ‖h z‖
          ≤ ‖∏ ρ ∈ zeroDiskFinset χ t₀,
              (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ‖ * ‖h z‖ :=
            mul_le_mul_of_nonneg_right hPz (norm_nonneg _)
        _ = ‖DirichletCharacter.LFunction χ z‖ := by rw [hh_fac z hzU, norm_mul]
        _ ≤ 15 * X := hLz
    have h2 : ‖h z‖ ≤ 15 * X / (1/8:ℝ)^n := (le_div_iff₀' h8n).mpr h1
    calc ‖h z‖ ≤ 15 * X / (1/8:ℝ)^n := h2
      _ = 15 * X * 8^n := by
          rw [one_div, inv_pow, div_eq_mul_inv, inv_inv]
  -- maximum principle: same bound on the whole closed 7/4-disk
  have hball_bound : ∀ z ∈ closedBall c (7/4 : ℝ), ‖h z‖ ≤ 15 * X * 8^n := by
    intro z hz
    have hd : DiffContOnCl ℂ h (ball c (7/4 : ℝ)) := by
      refine ⟨fun w hw => (hh_an w (ball_subset_closedBall hw)).differentiableAt.differentiableWithinAt, ?_⟩
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
  have hLc : 1/3 ≤ ‖DirichletCharacter.LFunction χ c‖ :=
    one_third_le_norm_LFunction_of_two_le_re χ (by rw [hcdef, re_center])
  have hPc : ‖∏ ρ ∈ zeroDiskFinset χ t₀,
      (c - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ‖ ≤ 2^n := by
    rw [norm_prod, hndef, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod (fun ρ _ => by positivity) (fun ρ hρ => ?_)
    rw [norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    have hρc : dist ρ c ≤ 13/8 :=
      mem_closedBall.mp ((mem_zeroDiskFinset hχ).mp hρ).1
    rw [← dist_eq_norm, dist_comm]
    linarith
  have hhc : (1/3:ℝ) * (1/2)^n ≤ ‖h c‖ := by
    have heq : ‖DirichletCharacter.LFunction χ c‖
        = ‖∏ ρ ∈ zeroDiskFinset χ t₀,
            (c - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ‖ * ‖h c‖ := by
      rw [hh_fac c hcU, norm_mul]
    have hhalf : ((1/2:ℝ))^n * 2^n = 1 := by
      rw [← mul_pow]
      norm_num
    have h2n : (0:ℝ) < (2:ℝ)^n := by positivity
    have h1 : 1/3 ≤ 2^n * ‖h c‖ := by
      have h2 : ‖∏ ρ ∈ zeroDiskFinset χ t₀,
          (c - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ‖ * ‖h c‖
          ≤ 2^n * ‖h c‖ :=
        mul_le_mul_of_nonneg_right hPc (norm_nonneg _)
      linarith [heq ▸ hLc]
    nlinarith [norm_nonneg (h c), pow_pos (by norm_num : (0:ℝ) < 1/2) n]
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
    have h2 : Real.log ((1/3:ℝ) * (1/2)^n) ≤ Real.log ‖h c‖ :=
      Real.log_le_log (by positivity) hhc
    have h3 : Real.log (15 * X * 8^n)
        = Real.log 15 + Real.log X + n * Real.log 8 := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by norm_num) (ne_of_gt hX0), Real.log_pow]
    have h4 : Real.log ((1/3:ℝ) * (1/2)^n)
        = -Real.log 3 - n * Real.log 2 := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
        one_div, Real.log_inv, one_div, Real.log_inv]
      ring
    have h45 : Real.log 15 + Real.log 3 = Real.log 45 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have h16 : Real.log 8 + Real.log 2 = Real.log 16 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]
      norm_num
    have h6 : Real.log (45 * X) ≤ 7 * Real.log X := log_fortyfive_mul_le hX2
    have h7 : Real.log (45 * X) = Real.log 45 + Real.log X :=
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
  -- differentiability and nonvanishing of the polynomial factor at `s`
  have hPdiff : Differentiable ℂ (fun z => ∏ ρ ∈ zeroDiskFinset χ t₀,
      (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) := by
    have hrw : (fun z => ∏ ρ ∈ zeroDiskFinset χ t₀,
        (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)
        = ∏ ρ ∈ zeroDiskFinset χ t₀,
          fun z => (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ := by
      funext z
      rw [Finset.prod_apply]
    rw [hrw]
    apply Differentiable.finsetProd
    intro u _
    exact (differentiable_id.sub_const u).pow _
  have hPs_ne : (∏ ρ ∈ zeroDiskFinset χ t₀,
      (s - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro ρ hρ
    apply pow_ne_zero
    rw [sub_ne_zero]
    intro hsρ
    exact hLs (hsρ ▸ ((mem_zeroDiskFinset hχ).mp hρ).2)
  have hhs_ne : h s ≠ 0 := hh_ne s hs13c
  have hh_diffAt : DifferentiableAt ℂ h s := (hh_an s hsU).differentiableAt
  -- `L = P·h` near `s`
  have hnb : DirichletCharacter.LFunction χ =ᶠ[𝓝 s]
      fun z => (∏ ρ ∈ zeroDiskFinset χ t₀,
        (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) * h z := by
    filter_upwards [isOpen_ball.mem_nhds hs13] with z hz
    exact hh_fac z (hball13_sub hz)
  have hd1 : deriv (DirichletCharacter.LFunction χ) s
      = deriv (fun z => (∏ ρ ∈ zeroDiskFinset χ t₀,
          (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) * h z) s :=
    hnb.deriv_eq
  have hval : DirichletCharacter.LFunction χ s
      = (∏ ρ ∈ zeroDiskFinset χ t₀,
          (s - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) * h s :=
    hh_fac s hsU
  -- logarithmic-derivative bookkeeping
  have hld : logDeriv (fun z => (∏ ρ ∈ zeroDiskFinset χ t₀,
      (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) * h z) s
      = logDeriv (fun z => ∏ ρ ∈ zeroDiskFinset χ t₀,
          (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) s
        + logDeriv h s :=
    logDeriv_mul s hPs_ne hhs_ne (hPdiff s) hh_diffAt
  have hPld : logDeriv (fun z => ∏ ρ ∈ zeroDiskFinset χ t₀,
      (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) s
      = ∑ ρ ∈ zeroDiskFinset χ t₀,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ) := by
    have h1 : logDeriv (fun z => ∏ ρ ∈ zeroDiskFinset χ t₀,
        (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) s
        = ∑ ρ ∈ zeroDiskFinset χ t₀,
          logDeriv (fun z =>
            (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) s := by
      exact logDeriv_prod
        (f := fun ρ => fun z =>
          (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ)
        (fun ρ hρ => by
          apply pow_ne_zero
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
    have h2 : logDeriv (fun z =>
        (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) s
        = (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
          * logDeriv (fun z => z - ρ) s :=
      logDeriv_fun_pow ((differentiable_id.sub_const ρ).differentiableAt) _
    have h3 : logDeriv (fun z => z - ρ) s = 1 / (s - ρ) := by
      rw [logDeriv_apply, deriv_sub_const, deriv_id'']
    rw [h2, h3]
    ring
  -- assemble the identity `L′/L − ∑ = h′/h`
  have hfinal : deriv (DirichletCharacter.LFunction χ) s
        / DirichletCharacter.LFunction χ s
      - ∑ ρ ∈ zeroDiskFinset χ t₀,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)
      = deriv h s / h s := by
    have hLD : deriv (DirichletCharacter.LFunction χ) s
        / DirichletCharacter.LFunction χ s
        = logDeriv (fun z => (∏ ρ ∈ zeroDiskFinset χ t₀,
            (z - ρ) ^ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) * h z) s := by
      rw [logDeriv_apply, ← hd1, ← hval]
    rw [hLD, hld, hPld, logDeriv_apply]
    ring
  rw [hfinal]
  calc ‖deriv h s / h s‖ ≤ 1600 * (325 * Real.log X) := hbound
    _ = 520000 * Real.log X := by ring

end Landau

/-! ### Good horizontal lines: the zero-spacing pigeonhole -/

section GoodLine

variable {N : ℕ} [NeZero N]

/-- Converse square bound to `norm_le_of_sq_le`. -/
lemma sq_add_sq_le_of_norm_le {z : ℂ} {a : ℝ} (h : ‖z‖ ≤ a) :
    z.re ^ 2 + z.im ^ 2 ≤ a ^ 2 := by
  have h1 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg z]

/-- Members of `zeroDiskFinset` are honest zeros: multiplicity at least one. -/
lemma one_le_ord_of_mem_zeroDiskFinset {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    {t₀ : ℝ} {ρ : ℂ} (hρ : ρ ∈ zeroDiskFinset χ t₀) :
    1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ := by
  obtain ⟨hρ13, hρ0⟩ := (mem_zeroDiskFinset hχ).mp hρ
  have hρU : ρ ∈ closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ) :=
    closedBall_subset_closedBall (by norm_num) hρ13
  have hne0 : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 :=
    analyticOrderAt_ne_zero.mpr
      ⟨(DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ, hρ0⟩
  have hnetop := analyticOrderAt_ne_top_on_disk hχ t₀ hρU
  rw [Nat.one_le_iff_ne_zero, analyticOrderNatAt]
  intro h0
  rcases ENat.toNat_eq_zero.mp h0 with h | h
  · exact hne0 h
  · exact hnetop h

/-- The number of distinct disk zeros is at most `112·log(N(|t₀|+2))`. -/
lemma card_zeroDiskFinset_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (t₀ : ℝ) :
    ((zeroDiskFinset χ t₀).card : ℝ) ≤ 112 * Real.log ((N : ℝ) * (|t₀| + 2)) := by
  have h1 : ((zeroDiskFinset χ t₀).card : ℝ)
      ≤ (∑ ρ ∈ zeroDiskFinset χ t₀,
          analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
    rw [Finset.card_eq_sum_ones]
    push_cast
    exact Finset.sum_le_sum fun ρ hρ => by
      exact_mod_cast one_le_ord_of_mem_zeroDiskFinset hχ hρ
  exact h1.trans (sum_ord_zeroDiskFinset_le hχ t₀)

/-- **Grid cover.**  A genuine zero (with `7/16 < Re ρ < 1`) of the `13/8`-disk at
height `t₀ ∈ [T, T+1]` lies in one of the seven `13/8`-disks at the half-integer
grid heights `T − 1 + j/2`, `j = 0, …, 6`. -/
lemma exists_grid_cover {T t₀ : ℝ} (h1 : T ≤ t₀) (h2 : t₀ ≤ T + 1) {ρ : ℂ}
    (hre : 7/16 < ρ.re) (hre1 : ρ.re < 1)
    (hρ : ρ ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ)) :
    ∃ j ∈ Finset.range 7,
      ρ ∈ closedBall ((2:ℂ) + ((T - 1 + (j:ℝ)/2 : ℝ) : ℂ) * I) (13/8 : ℝ) := by
  -- decode the distance hypothesis
  have hd : (ρ.re - 2)^2 + (ρ.im - t₀)^2 ≤ (13/8:ℝ)^2 := by
    have h3 : ‖ρ - ((2:ℂ) + t₀ * I)‖ ≤ 13/8 := by
      rw [← Complex.dist_eq]
      exact mem_closedBall.mp hρ
    have h4 := sq_add_sq_le_of_norm_le h3
    have hre' : (ρ - ((2:ℂ) + t₀ * I)).re = ρ.re - 2 := by simp
    have him' : (ρ - ((2:ℂ) + t₀ * I)).im = ρ.im - t₀ := by simp
    rw [hre', him'] at h4
    exact h4
  -- helper to conclude membership
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
  · -- below the grid: use `j = 0`
    refine ⟨0, Finset.mem_range.mpr (by norm_num), ?_⟩
    apply hmem
    have h5 : 0 ≤ (T - 1) - ρ.im := by linarith
    have h6 : (T - 1) - ρ.im ≤ t₀ - ρ.im := by linarith
    have h7 : ((T - 1) - ρ.im)^2 ≤ (t₀ - ρ.im)^2 := by nlinarith
    push_cast
    nlinarith [hd, h7]
  rcases le_or_gt (T + 2) ρ.im with hhigh | hin
  · -- above the grid: use `j = 6`
    refine ⟨6, Finset.mem_range.mpr (by norm_num), ?_⟩
    apply hmem
    have h5 : 0 ≤ ρ.im - (T + 2) := by linarith
    have h6 : ρ.im - (T + 2) ≤ ρ.im - t₀ := by linarith
    have h7 : (ρ.im - (T + 2))^2 ≤ (ρ.im - t₀)^2 := by nlinarith
    push_cast
    nlinarith [hd, h7]
  · -- inside `[T−1, T+2]`: nearest half-integer grid point, distance ≤ 1/4
    set x : ℝ := 2 * (ρ.im - (T - 1)) with hxdef
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

/-- **Zero-spacing pigeonhole.**  For any finite set `Γ` of ordinates there is a
point of `[T, T+1]` at distance `≥ 1/(2(|Γ|+1))` from every member of `Γ`. -/
lemma exists_gap_point (Γ : Finset ℝ) (T : ℝ) :
    ∃ t₀ : ℝ, T ≤ t₀ ∧ t₀ ≤ T + 1 ∧
      ∀ γ ∈ Γ, 1/(2*(Γ.card + 1) : ℝ) ≤ |t₀ - γ| := by
  classical
  set k : ℕ := Γ.card with hkdef
  by_contra hcon
  push Not at hcon
  -- every candidate point `T + i/(k+1)` is within `δ` of some ordinate
  have hpick : ∀ i ∈ Finset.range (k + 1), ∃ γ ∈ Γ,
      |T + (i:ℝ)/(k+1) - γ| < 1/(2*((k:ℝ)+1)) := by
    intro i hi
    have hi' : (i : ℝ) ≤ k := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hk1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
    have h1 : T ≤ T + (i:ℝ)/(k+1) := by
      have h1' : (0:ℝ) ≤ (i:ℝ)/(k+1) := by positivity
      linarith
    have h2 : T + (i:ℝ)/(k+1) ≤ T + 1 := by
      have h3 : (i:ℝ)/(k+1) ≤ 1 := by
        rw [div_le_one hk1]
        linarith
      linarith
    obtain ⟨γ, hγΓ, hγ⟩ := hcon (T + (i:ℝ)/(k+1)) h1 h2
    refine ⟨γ, hγΓ, ?_⟩
    have hcast : (1:ℝ)/(2*((Γ.card:ℝ) + 1)) = 1/(2*((k:ℝ)+1)) := by rw [← hkdef]
    rw [← hcast]
    exact hγ
  -- selection function
  set f : ℕ → ℝ := fun j =>
    if h : ∃ γ ∈ Γ, |T + (j:ℝ)/(k+1) - γ| < 1/(2*((k:ℝ)+1)) then h.choose else 0
    with hfdef
  have hsel : ∀ j ∈ Finset.range (k + 1), f j ∈ Γ := by
    intro j hj
    simp only [hfdef, dif_pos (hpick j hj)]
    exact (hpick j hj).choose_spec.1
  have hspec : ∀ j ∈ Finset.range (k + 1),
      |T + (j:ℝ)/(k+1) - f j| < 1/(2*((k:ℝ)+1)) := by
    intro j hj
    simp only [hfdef, dif_pos (hpick j hj)]
    exact (hpick j hj).choose_spec.2
  have hcard : Γ.card < (Finset.range (k + 1)).card := by
    rw [Finset.card_range, hkdef]
    omega
  obtain ⟨i, hi, i', hi', hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hsel
  have h1 := hspec i hi
  have h2 := hspec i' hi'
  rw [heq] at h1
  -- distance between distinct candidates is at least `1/(k+1) = 2δ`
  have hk1 : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hdist : (1:ℝ)/(k+1) ≤ |(T + (i:ℝ)/(k+1)) - (T + (i':ℝ)/(k+1))| := by
    have hd1 : (T + (i:ℝ)/(k+1)) - (T + (i':ℝ)/(k+1)) = ((i:ℝ) - i')/(k+1) := by
      ring
    rw [hd1, abs_div, abs_of_pos hk1, div_le_div_iff_of_pos_right hk1]
    have hne' : (i:ℤ) ≠ (i':ℤ) := by exact_mod_cast hne
    have h3 : (1:ℤ) ≤ |(i:ℤ) - i'| := Int.one_le_abs (sub_ne_zero.mpr hne')
    have h4 : ((1:ℤ):ℝ) ≤ (|((i:ℤ) - i' : ℤ)| : ℝ) := by exact_mod_cast h3
    push_cast at h4 ⊢
    exact h4
  have htri : |(T + (i:ℝ)/(k+1)) - (T + (i':ℝ)/(k+1))|
      ≤ |T + (i:ℝ)/(k+1) - f i'| + |T + (i':ℝ)/(k+1) - f i'| := by
    have h5 : (T + (i:ℝ)/(k+1)) - (T + (i':ℝ)/(k+1))
        = (T + (i:ℝ)/(k+1) - f i') - (T + (i':ℝ)/(k+1) - f i') := by ring
    rw [h5]
    exact abs_sub _ _
  have h6 : (1:ℝ)/(2*((k:ℝ)+1)) + 1/(2*((k:ℝ)+1)) = 1/((k:ℝ)+1) := by
    field_simp
    ring
  have hcombine : |(T + (i:ℝ)/(k+1)) - (T + (i':ℝ)/(k+1))| < 1/((k:ℝ)+1) := by
    calc |(T + (i:ℝ)/(k+1)) - (T + (i':ℝ)/(k+1))|
        ≤ |T + (i:ℝ)/(k+1) - f i'| + |T + (i':ℝ)/(k+1) - f i'| := htri
      _ < 1/(2*((k:ℝ)+1)) + 1/(2*((k:ℝ)+1)) := add_lt_add h1 h2
      _ = 1/((k:ℝ)+1) := h6
  linarith

/-- **Z4c corollary: good horizontal lines.**  For every `T ≥ 2` there is
`t₀ ∈ [T, T+1]` such that for all `σ ∈ [1/2, 3]` the point `s = σ + it₀` is not
a zero of `L(·,χ)` and `‖L′/L(s,χ)‖ ≤ 10⁶·(log(N(T+4)))²`.

The range is `σ ∈ [1/2, 3]`: the segment `σ ∈ [−1/4, 1/2)` of the Z5 rectangle
is outside the reach of the frozen Z4b disk geometry (disks of radius `13/8`
centered on `Re = 2`) and needs the functional-equation reflection; Z5 must
supply that edge separately.  For `σ ≥ 2` one may instead use the trivial
bounds `‖L′‖ ≤ 6`, `‖L‖ ≥ 1/3` from `Carmichael.LGrowth`. -/
theorem exists_good_line {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {T : ℝ}
    (hT : 2 ≤ T) :
    ∃ t₀ : ℝ, T ≤ t₀ ∧ t₀ ≤ T + 1 ∧ ∀ σ : ℝ, 1/2 ≤ σ → σ ≤ 3 →
      DirichletCharacter.LFunction χ (σ + t₀ * I) ≠ 0 ∧
      ‖deriv (DirichletCharacter.LFunction χ) (σ + t₀ * I)
          / DirichletCharacter.LFunction χ (σ + t₀ * I)‖
        ≤ 1000000 * Real.log ((N:ℝ) * (T + 4)) ^ 2 := by
  classical
  -- census: zero ordinates of the seven grid disks
  set W : Finset ℂ := (Finset.range 7).biUnion
    (fun j => zeroDiskFinset χ (T - 1 + (j:ℝ)/2)) with hWdef
  set Γ : Finset ℝ := W.image Complex.im with hΓdef
  have hN1 : (1:ℝ) ≤ N := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hY0 : (0:ℝ) < (N:ℝ) * (T + 4) := by nlinarith
  set logY : ℝ := Real.log ((N:ℝ) * (T + 4)) with hlogYdef
  have hlogY1 : 1 ≤ logY := by
    rw [hlogYdef, Real.le_log_iff_exp_le hY0]
    have hexp := Real.exp_one_lt_d9
    nlinarith
  have hlogY0 : (0:ℝ) < logY := by linarith
  -- census cardinality
  have hcardW : (W.card : ℝ) ≤ 784 * logY := by
    have h1 : W.card ≤ ∑ j ∈ Finset.range 7,
        (zeroDiskFinset χ (T - 1 + (j:ℝ)/2)).card := Finset.card_biUnion_le
    have h2 : ∀ j ∈ Finset.range 7,
        ((zeroDiskFinset χ (T - 1 + (j:ℝ)/2)).card : ℝ) ≤ 112 * logY := by
      intro j hj
      have hj6 : (j:ℝ) ≤ 6 := by
        exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
      have h3 := card_zeroDiskFinset_le hχ (T - 1 + (j:ℝ)/2)
      have habs : |T - 1 + (j:ℝ)/2| = T - 1 + (j:ℝ)/2 :=
        abs_of_nonneg (by linarith)
      have h4 : Real.log ((N:ℝ) * (|T - 1 + (j:ℝ)/2| + 2)) ≤ logY := by
        rw [habs, hlogYdef]
        apply Real.log_le_log (by nlinarith)
        nlinarith
      linarith
    calc (W.card : ℝ)
        ≤ (∑ j ∈ Finset.range 7,
            (zeroDiskFinset χ (T - 1 + (j:ℝ)/2)).card : ℕ) := by exact_mod_cast h1
      _ = ∑ j ∈ Finset.range 7,
            ((zeroDiskFinset χ (T - 1 + (j:ℝ)/2)).card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _j ∈ Finset.range 7, 112 * logY := Finset.sum_le_sum h2
      _ = 784 * logY := by
          rw [Finset.sum_const, Finset.card_range]
          ring
  have hcardΓ : (Γ.card : ℝ) ≤ 784 * logY := by
    have h1 : Γ.card ≤ W.card := by
      rw [hΓdef]
      exact Finset.card_image_le
    calc (Γ.card : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast h1
      _ ≤ 784 * logY := hcardW
  -- the good height
  obtain ⟨t₀, ht₀1, ht₀2, hgap⟩ := exists_gap_point Γ T
  set δ : ℝ := 1/(2*(Γ.card + 1) : ℝ) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  refine ⟨t₀, ht₀1, ht₀2, ?_⟩
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
  -- any genuine disk zero with `Re > 7/16` sits at an ordinate of the census
  have havoid : ∀ ρ ∈ zeroDiskFinset χ t₀, 7/16 < ρ.re → δ ≤ |t₀ - ρ.im| := by
    intro ρ hρ hρre
    obtain ⟨hρball, hρzero⟩ := (mem_zeroDiskFinset hχ).mp hρ
    have hρre1 : ρ.re < 1 := by
      by_contra hge
      push Not at hge
      exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hge hρzero
    obtain ⟨j, hjmem, hjball⟩ := exists_grid_cover ht₀1 ht₀2 hρre hρre1 hρball
    have hρW : ρ ∈ W := by
      rw [hWdef]
      exact Finset.mem_biUnion.mpr
        ⟨j, hjmem, (mem_zeroDiskFinset hχ).mpr ⟨hjball, hρzero⟩⟩
    exact hgap ρ.im (hΓdef ▸ Finset.mem_image_of_mem _ hρW)
  -- nonvanishing on the whole horizontal segment
  have hLs : DirichletCharacter.LFunction χ s ≠ 0 := by
    intro h0
    rcases le_or_gt 1 σ with hge | hlt
    · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
        (by rw [hsre]; exact hge) h0
    · have hs138 : s ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ) :=
        closedBall_subset_closedBall (by norm_num) hs32
      have hsK : s ∈ zeroDiskFinset χ t₀ := (mem_zeroDiskFinset hχ).mpr ⟨hs138, h0⟩
      have h716 : 7/16 < s.re := by rw [hsre]; linarith
      have h1 := havoid s hsK h716
      rw [hsim, sub_self, abs_zero] at h1
      linarith
  -- the Landau expansion at `s`
  have hmain := norm_logDeriv_sub_sum_zeroDiskFinset_le hχ t₀ hs32 hLs
  have hXY : Real.log ((N:ℝ) * (|t₀| + 2)) ≤ logY := by
    have habs : |t₀| = t₀ := abs_of_nonneg (by linarith)
    rw [habs, hlogYdef]
    apply Real.log_le_log (by nlinarith)
    nlinarith
  -- termwise bound on the partial-fraction sum
  have hterm : ∀ ρ ∈ zeroDiskFinset χ t₀,
      ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖
        ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
          * (1624 * logY) := by
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
    have hsρ0 : (0:ℝ) < ‖s - ρ‖ := lt_of_lt_of_le hmin0 hlow
    have hmininv : 1/(min (1/16:ℝ) δ) ≤ 1624 * logY := by
      rcases le_total (1/16:ℝ) δ with hmd | hmd
      · rw [min_eq_left hmd]
        nlinarith
      · rw [min_eq_right hmd, hδdef, one_div_one_div]
        nlinarith
    have hinv : 1/‖s - ρ‖ ≤ 1624 * logY :=
      le_trans (one_div_le_one_div_of_le hmin0 hlow) hmininv
    rw [norm_div, Complex.norm_natCast, div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hinv (Nat.cast_nonneg _)
  -- sum bound
  have hsum : ‖∑ ρ ∈ zeroDiskFinset χ t₀,
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖
      ≤ 112 * logY * (1624 * logY) := by
    have hmass : (∑ ρ ∈ zeroDiskFinset χ t₀,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ≤ 112 * logY := by
      have h1 := sum_ord_zeroDiskFinset_le hχ t₀
      have h2 : (∑ ρ ∈ zeroDiskFinset χ t₀,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))
          = ((∑ ρ ∈ zeroDiskFinset χ t₀,
              analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ) := by
        push_cast
        rfl
      rw [h2]
      calc ((∑ ρ ∈ zeroDiskFinset χ t₀,
          analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ)
          ≤ 112 * Real.log ((N:ℝ) * (|t₀| + 2)) := by exact_mod_cast h1
        _ ≤ 112 * logY := by linarith
    calc ‖∑ ρ ∈ zeroDiskFinset χ t₀,
        (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖
        ≤ ∑ ρ ∈ zeroDiskFinset χ t₀,
          ‖(analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ ρ ∈ zeroDiskFinset χ t₀,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
            * (1624 * logY) := Finset.sum_le_sum hterm
      _ = (∑ ρ ∈ zeroDiskFinset χ t₀,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ))
            * (1624 * logY) := by rw [← Finset.sum_mul]
      _ ≤ 112 * logY * (1624 * logY) := by
          apply mul_le_mul_of_nonneg_right hmass
          positivity
  -- assemble
  refine ⟨hLs, ?_⟩
  calc ‖deriv (DirichletCharacter.LFunction χ) s
        / DirichletCharacter.LFunction χ s‖
      = ‖(deriv (DirichletCharacter.LFunction χ) s
          / DirichletCharacter.LFunction χ s
        - ∑ ρ ∈ zeroDiskFinset χ t₀,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ))
        + ∑ ρ ∈ zeroDiskFinset χ t₀,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖ := by
        congr 1
        ring
    _ ≤ ‖deriv (DirichletCharacter.LFunction χ) s
          / DirichletCharacter.LFunction χ s
        - ∑ ρ ∈ zeroDiskFinset χ t₀,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖
        + ‖∑ ρ ∈ zeroDiskFinset χ t₀,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)‖ :=
        norm_add_le _ _
    _ ≤ 520000 * Real.log ((N:ℝ) * (|t₀| + 2))
        + 112 * logY * (1624 * logY) := add_le_add hmain hsum
    _ ≤ 1000000 * logY ^ 2 := by nlinarith
    _ = 1000000 * Real.log ((N:ℝ) * (T + 4)) ^ 2 := by rw [hlogYdef]

end GoodLine

end Carmichael
