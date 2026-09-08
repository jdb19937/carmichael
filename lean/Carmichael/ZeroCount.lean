/-
Route Z, sortie Z4b: zero counting for Dirichlet L-functions, d-uniform.

DESIGN (consumed by Z4c, Z5, Z9 — read before touching):

* `LZerosBox χ σ T` is the set of zeros of `DirichletCharacter.LFunction χ` in the
  closed box `[σ, 1] × [−T, T]`, with the point `s = 1` excluded.  Excluding `s = 1`
  costs nothing for nontrivial `χ` (where `L(1,χ) ≠ 0`) and makes the definition
  meaningful for the principal character, whose `LFunction` has a pole at `1` and
  carries a junk Lean value there.  `finite_LZerosBox` proves this set is finite for
  EVERY `χ`, `σ`, `T` (no hypotheses), so the Finset below is total.

* `zeroFinset χ σ T : Finset ℂ` — the DISTINCT zeros (via `Set.Finite.toFinset`);
  membership is characterized by `mem_zeroFinset`.

* Multiplicity is `analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ`
  (Mathlib's analytic vanishing order, `.toNat`).  At every `ρ ∈ zeroFinset χ σ T`
  the order is finite and positive.  Zero counts and zero SUMS downstream should be
  written as `∑ ρ ∈ zeroFinset χ σ T, analyticOrderNatAt (LFunction χ) ρ • (…)`;
  this matches Jensen (which counts with multiplicity) and the explicit formula.

* `zeroCountBox χ σ T : ℕ` — total zero count with multiplicity, i.e. the weight-1
  instance of the above.

Deliverables (all constants explicit numerals; `N` = the modulus, arbitrary):

* `sum_analyticOrderNatAt_le` — generic Jensen disk bound: multiplicity mass of any
  finset inside `closedBall c (13/8)` is `≤ 14 log (6M)` for a function analytic on
  `closedBall c (7/4)` with `‖f c‖ ≥ 1/6` and sphere bound `M`.
* `sum_ord_LFunction_disk_le` — the unit-disk count for nontrivial `χ`:
  mass in `closedBall (2 + it₀) (13/8)` is `≤ 112 · log (N·(|t₀|+2))`.
* `sum_ord_etaFun_disk_le` — the same for `ζ`, via the entire-on-`Re > 0` Abel-summed
  Dirichlet eta function `etaFun` with `etaFun = (1 − 2^{1−s}) ζ(s)` off `s = 1`
  (this is the principal-character / option (i) engine; no removable-singularity
  machinery needed).
* `zeroCountBox_le_of_ne_one` — `N(1/2, T, χ) ≤ 1120 · T · log (N (T+2))`, `T ≥ 1`.
* `zeroCountBox_trivChar_le` — the same bound (with `log (T+2)`) for the principal
  character mod `N`, via `L(s,χ₀) = ∏_{p∣N}(1−p^{−s}) · ζ(s)`; at `N = 1` this IS
  the Riemann zeta zero count (`LFunction (1 : DirichletCharacter ℂ 1) = ζ`).
* `sum_zeroCountBox_le` — THE FROZEN Z4b INTERFACE (routez/Z0a-ledger.md §7):
  `∑_{χ mod d} N(1/2, t, χ) ≤ 1120 · t · d · log (d·(t+2))` for `t ≥ 1`, all `d ≥ 1`.
  So `C₁ = 1120`.

Engine: Mathlib's Jensen inequality `AnalyticOnNhd.sum_divisor_le` on disks centered
`2 + it₀` (radii 13/8 < 7/4, staying in `Re ≥ 1/4`), fed by Z4a's growth bounds
(`Carmichael.LGrowth`): `‖L(s,χ)‖ ≤ 5N(2+‖s‖)` on `Re ≥ 1/4` and `‖L‖ ≥ 1/3` on
`Re ≥ 2`.  Box counts follow by covering `[1/2,1] × [−T,T]` with ≤ 5T disks at
integer heights.
-/
import Carmichael.LGrowth
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

namespace Carmichael

open Complex Finset Filter Set Metric
open scoped Topology

/-! ### Elementary helpers -/

section Helpers

/-- Componentwise square bound gives a norm bound. -/
lemma norm_le_of_sq_le {z : ℂ} {a : ℝ} (ha : 0 ≤ a) (h : z.re ^ 2 + z.im ^ 2 ≤ a ^ 2) :
    ‖z‖ ≤ a := by
  have h1 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  nlinarith [norm_nonneg z]

/-- `‖z‖ ≤ |Re z| + |Im z|`. -/
lemma norm_le_abs_re_add_abs_im (z : ℂ) : ‖z‖ ≤ |z.re| + |z.im| := by
  calc ‖z‖ = ‖(z.re : ℂ) + z.im * I‖ := by rw [Complex.re_add_im]
    _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * I‖ := norm_add_le _ _
    _ = |z.re| + |z.im| := by simp

/-- `log (90·X) ≤ 8 log X` for `X ≥ 2`. -/
lemma log_ninety_mul_le {X : ℝ} (hX : 2 ≤ X) : Real.log (90 * X) ≤ 8 * Real.log X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have h1 : Real.log (90 * X) = Real.log 90 + Real.log X :=
    Real.log_mul (by norm_num) (ne_of_gt hX0)
  have h27 : (90 : ℝ) ≤ X ^ 7 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hX 7
    nlinarith
  have h2 : Real.log 90 ≤ Real.log (X ^ 7) := Real.log_le_log (by norm_num) h27
  rw [Real.log_pow] at h2
  have := Real.log_nonneg (by linarith : (1:ℝ) ≤ X)
  push_cast at h2
  linarith

/-- `1/14 ≤ log (14/13)`. -/
lemma one_div_fourteen_le_log : (1 / 14 : ℝ) ≤ Real.log (14 / 13) := by
  have h := Real.log_le_sub_one_of_pos (x := 13 / 14) (by norm_num)
  have h2 : Real.log (14 / 13 : ℝ) = -Real.log (13 / 14) := by
    rw [← Real.log_inv]; norm_num
  linarith

end Helpers

/-! ### Generic zero-counting tools for analytic functions -/

section Generic

/-- Zeros of a not-identically-zero entire function meet any compact set in a finite set. -/
theorem finite_zeros_inter_compact {f : ℂ → ℂ} (hf : Differentiable ℂ f) {w : ℂ}
    (hw : f w ≠ 0) {S : Set ℂ} (hS : IsCompact S) : {s ∈ S | f s = 0}.Finite := by
  have hA : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hcod : f ⁻¹' {0}ᶜ ∈ Filter.codiscrete ℂ := hA.preimage_zero_mem_codiscrete hw
  obtain ⟨hopen, hdiscrete⟩ := mem_codiscrete'.mp hcod
  rw [Set.preimage_compl, compl_compl] at hdiscrete
  rw [Set.preimage_compl] at hopen
  have hzc : IsClosed (f ⁻¹' {0}) := by
    rw [← compl_compl (f ⁻¹' {0})]
    exact hopen.isClosed_compl
  have hset : {s ∈ S | f s = 0} = S ∩ f ⁻¹' {0} := by
    ext s; simp
  rw [hset]
  exact (hS.inter_right hzc).finite (hdiscrete.mono Set.inter_subset_right)

/-- **Jensen bridge.**  If `f` is analytic on `closedBall c (7/4)`, bounded by `M` on the
boundary sphere, and `‖f c‖ ≥ 1/6`, then the total vanishing multiplicity of `f` on any
finset inside `closedBall c (13/8)` is at most `14 · log (6M)`. -/
theorem sum_analyticOrderNatAt_le {f : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hA : AnalyticOnNhd ℂ f (closedBall c (7/4))) (hM : 1 ≤ M)
    (hc : 1/6 ≤ ‖f c‖) (hbd : ∀ z ∈ sphere c (7/4 : ℝ), ‖f z‖ ≤ M)
    {F : Finset ℂ} (hF : ∀ ρ ∈ F, ρ ∈ closedBall c (13/8 : ℝ)) :
    (∑ ρ ∈ F, analyticOrderNatAt f ρ : ℝ) ≤ 14 * Real.log (6 * M) := by
  have habs74 : |(7/4 : ℝ)| = 7/4 := by norm_num
  have habs138 : |(13/8 : ℝ)| = 13/8 := by norm_num
  have hfc : f c ≠ 0 := by
    intro h; rw [h, norm_zero] at hc; linarith
  have hfc0 : (0:ℝ) < ‖f c‖ := lt_of_lt_of_le (by norm_num) hc
  -- finite order everywhere on the big ball
  have hsub : closedBall c (13/8 : ℝ) ⊆ closedBall c (7/4 : ℝ) :=
    closedBall_subset_closedBall (by norm_num)
  have hne_top : ∀ ρ ∈ closedBall c (7/4 : ℝ), analyticOrderAt f ρ ≠ ⊤ := by
    intro ρ hρ htop
    have hev : f =ᶠ[𝓝 ρ] 0 := by
      filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz using hz
    have hEq : Set.EqOn f 0 (closedBall c (7/4 : ℝ)) :=
      hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_closedBall c (7/4 : ℝ)).isPreconnected hρ hev
    exact hfc (hEq (mem_closedBall_self (by norm_num)))
  -- Jensen's inequality
  have hA74 : AnalyticOnNhd ℂ f (closedBall c |(7/4 : ℝ)|) := by rwa [habs74]
  have hbd' : ∀ z ∈ sphere c |(7/4 : ℝ)|, ‖f z‖ ≤ M := by rwa [habs74]
  have J := hA74.sum_divisor_le (r := 13/8) (R := 7/4)
    (by norm_num) (by norm_num) hM hfc hbd'
  rw [habs138] at J
  -- bridge: the finset multiplicity sum is at most the divisor finsum
  have hA138 : AnalyticOnNhd ℂ f (closedBall c (13/8 : ℝ)) := hA.mono hsub
  set D := MeromorphicOn.divisor f (closedBall c (13/8 : ℝ)) with hD
  have hDapply : ∀ ρ ∈ closedBall c (13/8 : ℝ), D ρ = (analyticOrderNatAt f ρ : ℤ) := by
    intro ρ hρ
    rw [hD, MeromorphicOn.AnalyticOnNhd.divisor_apply hA138 hρ,
      ← Nat.cast_analyticOrderNatAt (hne_top ρ (hsub hρ))]
    rfl
  have hDnn : ∀ u : ℂ, 0 ≤ D u := by
    intro u
    by_cases hu : u ∈ closedBall c (13/8 : ℝ)
    · rw [hDapply u hu]; positivity
    · rw [hD, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
  have hsupp := D.finiteSupport (isCompact_closedBall c (13/8 : ℝ))
  have hkey : (∑ ρ ∈ F, (analyticOrderNatAt f ρ : ℤ)) ≤ ∑ᶠ u, D u := by
    have h1 : ∑ᶠ u, D u = ∑ u ∈ F ∪ hsupp.toFinset, D u := by
      apply finsum_eq_sum_of_support_subset
      intro x hx
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe]
      exact Or.inr (hsupp.mem_toFinset.mpr hx)
    have h2 : (∑ ρ ∈ F, (analyticOrderNatAt f ρ : ℤ)) = ∑ ρ ∈ F, D ρ :=
      Finset.sum_congr rfl fun ρ hρ => (hDapply ρ (hF ρ hρ)).symm
    have h3 : ∑ ρ ∈ F, D ρ ≤ ∑ u ∈ F ∪ hsupp.toFinset, D u :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        fun u _ _ => hDnn u
    rw [h2, h1]; exact h3
  -- assemble in ℝ
  have hcast : (∑ ρ ∈ F, analyticOrderNatAt f ρ : ℝ)
      = ((∑ ρ ∈ F, (analyticOrderNatAt f ρ : ℤ)) : ℝ) := by push_cast; rfl
  have hlogpos : (0:ℝ) < Real.log ((7/4) / (13/8)) := by
    have : ((7:ℝ)/4) / (13/8) = 14/13 := by norm_num
    rw [this]; linarith [one_div_fourteen_le_log]
  have hnum : Real.log (M / ‖f c‖) ≤ Real.log (6 * M) := by
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ hfc0]
    nlinarith
  have hden : Real.log (M / ‖f c‖) / Real.log ((7/4) / (13/8)) ≤ 14 * Real.log (6 * M) := by
    rcases le_or_gt (Real.log (M / ‖f c‖)) 0 with hle | hgt
    · have h6M : (0:ℝ) ≤ Real.log (6 * M) :=
        Real.log_nonneg (by nlinarith)
      have : Real.log (M / ‖f c‖) / Real.log ((7/4) / (13/8)) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hle hlogpos.le
      linarith
    · have h1413 : ((7:ℝ)/4) / (13/8) = 14/13 := by norm_num
      have hb : (1/14 : ℝ) ≤ Real.log ((7/4) / (13/8)) := by
        rw [h1413]; exact one_div_fourteen_le_log
      calc Real.log (M / ‖f c‖) / Real.log ((7/4) / (13/8))
          ≤ Real.log (M / ‖f c‖) / (1/14) :=
            div_le_div_of_nonneg_left hgt.le (by norm_num) hb
        _ = 14 * Real.log (M / ‖f c‖) := by ring
        _ ≤ 14 * Real.log (6 * M) := by linarith
  calc (∑ ρ ∈ F, analyticOrderNatAt f ρ : ℝ)
      = ((∑ ρ ∈ F, (analyticOrderNatAt f ρ : ℤ)) : ℝ) := hcast
    _ ≤ ((∑ᶠ u, D u : ℤ) : ℝ) := by exact_mod_cast hkey
    _ ≤ Real.log (M / ‖f c‖) / Real.log ((7/4) / (13/8)) := J
    _ ≤ 14 * Real.log (6 * M) := hden

end Generic

/-! ### The zero box: definition and finiteness -/

section ZeroBox

variable {N : ℕ} [NeZero N]

/-- The closed box `[σ,1] × [−T,T]`. -/
lemma isCompact_box (σ T : ℝ) :
    IsCompact {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T} := by
  have hclosed : IsClosed {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T} := by
    have h1 : IsClosed {s : ℂ | σ ≤ s.re} := isClosed_le continuous_const Complex.continuous_re
    have h2 : IsClosed {s : ℂ | s.re ≤ 1} := isClosed_le Complex.continuous_re continuous_const
    have h3 : IsClosed {s : ℂ | |s.im| ≤ T} :=
      isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const
    have : {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T}
        = {s : ℂ | σ ≤ s.re} ∩ ({s : ℂ | s.re ≤ 1} ∩ {s : ℂ | |s.im| ≤ T}) := by
      ext s; simp
    rw [this]
    exact h1.inter (h2.inter h3)
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0:ℂ) (|σ| + 1 + |T|))
    hclosed ?_
  intro s hs
  obtain ⟨h1, h2, h3⟩ := hs
  simp only [mem_closedBall, dist_zero_right]
  have hre : |s.re| ≤ |σ| + 1 := by
    rcases abs_cases σ with ⟨hσ, _⟩ | ⟨hσ, _⟩ <;> rcases abs_cases s.re with ⟨hr, _⟩ | ⟨hr, _⟩ <;>
      linarith
  have him : |s.im| ≤ |T| := le_trans h3 (le_abs_self T)
  linarith [norm_le_abs_re_add_abs_im s]

/-- Zeros of `L(·,χ)` in the box `[σ,1] × [−T,T]`, excluding the point `1`
(where the principal character's `LFunction` has its pole / junk value). -/
def LZerosBox (χ : DirichletCharacter ℂ N) (σ T : ℝ) : Set ℂ :=
  {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T ∧ s ≠ 1 ∧ DirichletCharacter.LFunction χ s = 0}

/-- The Euler factor `∏_{p ∣ N} (1 − p^{−s})` relating `L(s, χ₀)` to `ζ(s)`. -/
noncomputable def eulerFactor (N : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))

lemma differentiable_eulerFactor (N : ℕ) : Differentiable ℂ (eulerFactor N) := by
  have heq : eulerFactor N = ∏ p ∈ N.primeFactors, fun s : ℂ => (1 - (p : ℂ) ^ (-s)) := by
    funext s
    rw [eulerFactor, Finset.prod_apply]
  rw [heq]
  apply Differentiable.finsetProd
  intro p _
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors ‹p ∈ N.primeFactors›).ne_zero
  exact (differentiable_const 1).sub ((differentiable_id.neg).const_cpow (Or.inl hp0))

lemma eulerFactor_ne_zero {N : ℕ} {s : ℂ} (hs : 0 < s.re) : eulerFactor N s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  have hp0 : (0:ℝ) < (p:ℝ) := by positivity
  have hnorm : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [show ((p:ℕ):ℂ) = ((p:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos hp0]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast hp2.trans_lt' one_lt_two
    · simpa using hs
  intro h
  rw [sub_eq_zero] at h
  rw [← h] at hnorm
  simp at hnorm

/-- The box zero set is finite, for every character (trivial included), every box. -/
theorem finite_LZerosBox (χ : DirichletCharacter ℂ N) (σ T : ℝ) :
    (LZerosBox χ σ T).Finite := by
  have hbox := isCompact_box σ T
  by_cases hχ : χ = 1
  · -- principal character: zeros come from the Euler factor or from ζ
    subst hχ
    have hE : {s ∈ {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T} | eulerFactor N s = 0}.Finite :=
      finite_zeros_inter_compact (differentiable_eulerFactor N)
        (w := 2) (eulerFactor_ne_zero (by norm_num)) hbox
    have hZ : ({s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T} ∩ riemannZetaZeros).Finite :=
      hbox.inter_riemannZetaZeros_finite
    apply (hE.union hZ).subset
    rintro s ⟨h1, h2, h3, h4, h5⟩
    have hLs : eulerFactor N s * riemannZeta s = 0 := by
      rw [eulerFactor, ← DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta h4]
      exact h5
    rcases mul_eq_zero.mp hLs with h | h
    · exact Or.inl ⟨⟨h1, h2, h3⟩, h⟩
    · exact Or.inr ⟨⟨h1, h2, h3⟩, h⟩
  · -- nontrivial character: entire, nonvanishing at 2
    have hL2 : DirichletCharacter.LFunction χ 2 ≠ 0 := by
      intro h
      have := one_third_le_norm_LFunction_of_two_le_re χ (s := 2) (by norm_num)
      rw [h, norm_zero] at this
      linarith
    apply (finite_zeros_inter_compact (DirichletCharacter.differentiable_LFunction hχ)
      hL2 hbox).subset
    rintro s ⟨h1, h2, h3, _, h5⟩
    exact ⟨⟨h1, h2, h3⟩, h5⟩

/-- The Finset of distinct zeros of `L(·,χ)` in the box `[σ,1] × [−T,T]` (minus `s = 1`).
Z4c/Z5 sum over this Finset with multiplicity weight
`analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ`. -/
noncomputable def zeroFinset (χ : DirichletCharacter ℂ N) (σ T : ℝ) : Finset ℂ :=
  (finite_LZerosBox χ σ T).toFinset

@[simp] lemma mem_zeroFinset {χ : DirichletCharacter ℂ N} {σ T : ℝ} {ρ : ℂ} :
    ρ ∈ zeroFinset χ σ T ↔
      σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ ρ ≠ 1 ∧ DirichletCharacter.LFunction χ ρ = 0 := by
  rw [zeroFinset, Set.Finite.mem_toFinset]
  rfl

/-- **The zero count** `N(σ, T, χ)`: number of zeros of `L(·,χ)`, counted with
multiplicity, in the box `[σ,1] × [−T,T]` (excluding `s = 1`). -/
noncomputable def zeroCountBox (χ : DirichletCharacter ℂ N) (σ T : ℝ) : ℕ :=
  ∑ ρ ∈ zeroFinset χ σ T, analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

/-- The count is antitone in the abscissa `σ`. -/
lemma zeroCountBox_mono {χ : DirichletCharacter ℂ N} {σ σ' T : ℝ} (h : σ ≤ σ') :
    zeroCountBox χ σ' T ≤ zeroCountBox χ σ T := by
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  rw [mem_zeroFinset] at hρ ⊢
  exact ⟨le_trans h hρ.1, hρ.2⟩

end ZeroBox

/-! ### The Dirichlet eta function via Abel summation (the ζ engine)

`etaFun` is an everywhere-convergent-on-`Re s > 0` Abel-summed series with
`etaFun s = (1 − 2^{1−s})·ζ(s)` for `Re s > 0`, `s ≠ 1`.  It is the entire-function
stand-in for `ζ` in the Jensen disks: every zero of `ζ` in `Re > 0` is a zero of
`etaFun` of at least the same order, and `etaFun` obeys the same growth/lower bounds
as the nontrivial-character `LFunction`s at modulus `1`. -/

section Eta

/-- Term of the Abel-summed Dirichlet eta series: `A(k)·(k^{−s} − (k+1)^{−s})` where
`A(k) = k % 2` is the partial sum `∑_{1 ≤ j ≤ k} (−1)^{j+1}`. -/
noncomputable def etaTerm (s : ℂ) (k : ℕ) : ℂ :=
  ((k % 2 : ℕ) : ℂ) * (((k : ℕ) : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s))

/-- Abel-summed Dirichlet eta function. -/
noncomputable def etaFun (s : ℂ) : ℂ := ∑' k, etaTerm s k

private lemma norm_etaTerm_le {s : ℂ} (hs : 0 < s.re) (k : ℕ) :
    ‖etaTerm s k‖ ≤ ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [etaTerm, Nat.zero_mod, Nat.cast_zero, zero_mul, norm_zero]
    positivity
  · have h1 : ‖((k % 2 : ℕ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_natCast]
      exact_mod_cast Nat.lt_succ_iff.mp (Nat.mod_lt k (by norm_num))
    calc ‖etaTerm s k‖
        = ‖((k % 2 : ℕ) : ℂ)‖ * ‖((k : ℕ) : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s)‖ :=
          norm_mul _ _
      _ ≤ 1 * (‖s‖ * (k : ℝ) ^ (-s.re - 1)) :=
          mul_le_mul h1 (norm_cpow_sub_cpow_le hs hk) (norm_nonneg _) (by norm_num)
      _ = ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by ring

private lemma summable_norm_etaTerm {s : ℂ} (hs : 0 < s.re) :
    Summable fun k => ‖etaTerm s k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_etaTerm_le hs)
    ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _)

lemma norm_etaFun_le {s : ℂ} (hs : 0 < s.re) : ‖etaFun s‖ ≤ ‖s‖ * (1 + 1 / s.re) := by
  have hsum := summable_norm_etaTerm hs
  calc ‖etaFun s‖ ≤ ∑' k, ‖etaTerm s k‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' k : ℕ, ‖s‖ * (k : ℝ) ^ (-s.re - 1) :=
        hsum.tsum_le_tsum (norm_etaTerm_le hs)
          ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _)
    _ = ‖s‖ * ∑' k : ℕ, (k : ℝ) ^ (-s.re - 1) := tsum_mul_left
    _ ≤ ‖s‖ * (1 + 1 / s.re) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
        exact Real.tsum_le_of_sum_range_le
          (fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _) (sum_range_rpow_le hs)

/-- Numeral growth bound for `etaFun` on `Re s ≥ 1/4` (the modulus-1 analogue of
`norm_LFunction_le_of_one_quarter_le_re`). -/
lemma norm_etaFun_le_of_one_quarter_le_re {s : ℂ} (hs : 1/4 ≤ s.re) :
    ‖etaFun s‖ ≤ 5 * (2 + ‖s‖) := by
  have hs0 : 0 < s.re := lt_of_lt_of_le (by norm_num) hs
  have h1 : 1 + 1 / s.re ≤ 5 := by
    have : 1 / s.re ≤ 4 := by rw [div_le_iff₀ hs0]; linarith
    linarith
  have h2 := norm_etaFun_le hs0
  nlinarith [norm_nonneg s, norm_nonneg (etaFun s)]

private lemma eta_abel {s : ℂ} (hs : s ≠ 0) (M : ℕ) :
    ∑ n ∈ range (M + 1), (-1 : ℂ) ^ (n + 1) * ((n : ℕ) : ℂ) ^ (-s)
      = (∑ k ∈ range M, etaTerm s k) + ((M % 2 : ℕ) : ℂ) * ((M : ℕ) : ℂ) ^ (-s) := by
  induction M with
  | zero =>
      simp [Complex.zero_cpow (neg_ne_zero.mpr hs)]
  | succ M ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (f := etaTerm s)]
      simp only [etaTerm]
      rcases Nat.even_or_odd M with hM | hM
      · have h1 : M % 2 = 0 := Nat.even_iff.mp hM
        have h2 : (M + 1) % 2 = 1 := by omega
        have h3 : (-1 : ℂ) ^ (M + 1 + 1) = 1 :=
          Even.neg_one_pow (Nat.even_iff.mpr (by omega))
        rw [h1, h2, h3]
        push_cast
        ring
      · have h1 : M % 2 = 1 := Nat.odd_iff.mp hM
        have h2 : (M + 1) % 2 = 0 := by omega
        have h3 : (-1 : ℂ) ^ (M + 1 + 1) = -1 :=
          Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))
        rw [h1, h2, h3]
        push_cast
        ring

/-- On `Re s > 1`, the Abel-summed eta function equals `(1 − 2^{1−s}) ζ(s)`. -/
private lemma etaFun_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    etaFun s = (1 - (2:ℂ) ^ ((1:ℂ) - s)) * riemannZeta s := by
  have hs0 : 0 < s.re := by linarith
  have hsne : s ≠ 0 := by
    intro h; rw [h] at hs0; simp at hs0
  -- ζ as a sum of n^{−s}
  have hsummable : Summable (fun n : ℕ => ((n : ℕ) : ℂ) ^ (-s)) := by
    have h := Complex.summable_one_div_nat_cpow.mpr hs
    refine h.congr fun n => ?_
    rw [Complex.cpow_neg, one_div]
  have hzeta : HasSum (fun n : ℕ => ((n : ℕ) : ℂ) ^ (-s)) (riemannZeta s) := by
    have h1 : riemannZeta s = ∑' n : ℕ, ((n : ℕ) : ℂ) ^ (-s) := by
      rw [zeta_eq_tsum_one_div_nat_cpow hs]
      exact tsum_congr fun n => by rw [Complex.cpow_neg, one_div]
    rw [h1]
    exact hsummable.hasSum
  set Z := riemannZeta s with hZ
  set w := (2:ℂ) ^ (-s) with hw
  -- even part
  have heven : HasSum (fun k : ℕ => ((2 * k : ℕ) : ℂ) ^ (-s)) (w * Z) := by
    have h := hzeta.mul_left w
    have heq : (fun k : ℕ => w * ((k : ℕ) : ℂ) ^ (-s))
        = fun k : ℕ => ((2 * k : ℕ) : ℂ) ^ (-s) := by
      funext k
      have hcast : ((2 * k : ℕ) : ℂ) = ((2 : ℕ) : ℂ) * ((k : ℕ) : ℂ) := by push_cast; ring
      rw [hcast, natCast_mul_natCast_cpow]
      norm_num [hw]
    rwa [heq] at h
  -- odd part
  have hoddsummable : Summable (fun k : ℕ => ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
      intro a b h
      simp only at h
      omega
    exact (hsummable.comp_injective hinj).congr fun k => rfl
  have hodd : HasSum (fun k : ℕ => ((2 * k + 1 : ℕ) : ℂ) ^ (-s)) (Z - w * Z) := by
    have h := hoddsummable.hasSum
    have hcomb := HasSum.even_add_odd (f := fun n : ℕ => ((n : ℕ) : ℂ) ^ (-s)) heven h
    have huniq := hzeta.unique hcomb
    have hO : ∑' k : ℕ, ((2 * k + 1 : ℕ) : ℂ) ^ (-s) = Z - w * Z := by
      linear_combination -huniq
    rwa [hO] at h
  -- the alternating series
  have hetasum : HasSum (fun n : ℕ => (-1 : ℂ) ^ (n + 1) * ((n : ℕ) : ℂ) ^ (-s))
      ((1 - 2 * w) * Z) := by
    have he2 : HasSum (fun k : ℕ => (-1 : ℂ) ^ (2 * k + 1) * ((2 * k : ℕ) : ℂ) ^ (-s))
        (-(w * Z)) := by
      have h := heven.neg
      have heq : (fun k : ℕ => -(((2 * k : ℕ) : ℂ) ^ (-s)))
          = fun k : ℕ => (-1 : ℂ) ^ (2 * k + 1) * ((2 * k : ℕ) : ℂ) ^ (-s) := by
        funext k
        have hp : (-1 : ℂ) ^ (2 * k + 1) = -1 := Odd.neg_one_pow ⟨k, by ring⟩
        rw [hp]; ring
      rwa [heq] at h
    have ho2 : HasSum (fun k : ℕ => (-1 : ℂ) ^ (2 * k + 1 + 1) * ((2 * k + 1 : ℕ) : ℂ) ^ (-s))
        (Z - w * Z) := by
      have h := hodd
      have heq : (fun k : ℕ => ((2 * k + 1 : ℕ) : ℂ) ^ (-s))
          = fun k : ℕ => (-1 : ℂ) ^ (2 * k + 1 + 1) * ((2 * k + 1 : ℕ) : ℂ) ^ (-s) := by
        funext k
        have hp : (-1 : ℂ) ^ (2 * k + 1 + 1) = 1 := Even.neg_one_pow ⟨k + 1, by ring⟩
        rw [hp]; ring
      rwa [heq] at h
    have h := HasSum.even_add_odd
      (f := fun n : ℕ => (-1 : ℂ) ^ (n + 1) * ((n : ℕ) : ℂ) ^ (-s)) he2 ho2
    have heq : -(w * Z) + (Z - w * Z) = (1 - 2 * w) * Z := by ring
    rwa [heq] at h
  -- match limits of partial sums
  have h1 : Tendsto (fun M : ℕ => ∑ n ∈ range (M + 1), (-1 : ℂ) ^ (n + 1) * ((n : ℕ) : ℂ) ^ (-s))
      atTop (𝓝 ((1 - 2 * w) * Z)) :=
    (tendsto_add_atTop_iff_nat 1).mpr hetasum.tendsto_sum_nat
  have h2 : Tendsto (fun M : ℕ => (∑ k ∈ range M, etaTerm s k)
      + ((M % 2 : ℕ) : ℂ) * ((M : ℕ) : ℂ) ^ (-s)) atTop (𝓝 ((1 - 2 * w) * Z)) := by
    refine h1.congr fun M => ?_
    exact eta_abel hsne M
  have h3 : Tendsto (fun M : ℕ => ∑ k ∈ range M, etaTerm s k) atTop (𝓝 (etaFun s)) :=
    ((summable_norm_etaTerm hs0).of_norm).hasSum.tendsto_sum_nat
  have h4 : Tendsto (fun M : ℕ => ((M % 2 : ℕ) : ℂ) * ((M : ℕ) : ℂ) ^ (-s)) atTop (𝓝 0) := by
    have hb : ∀ M : ℕ, ‖((M % 2 : ℕ) : ℂ) * ((M : ℕ) : ℂ) ^ (-s)‖ ≤ (M : ℝ) ^ (-s.re) := by
      intro M
      rcases Nat.eq_zero_or_pos M with rfl | hM
      · simp [Complex.zero_cpow (neg_ne_zero.mpr hsne),
          Real.zero_rpow (ne_of_lt (by linarith : -s.re < 0))]
      · rw [norm_mul]
        have hM0 : (0:ℝ) < (M : ℝ) := by exact_mod_cast hM
        have hnn : ‖((M : ℕ) : ℂ) ^ (-s)‖ = (M : ℝ) ^ (-s.re) := by
          rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hM0,
            Complex.neg_re]
        rw [hnn]
        have h1' : ‖((M % 2 : ℕ) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_natCast]
          exact_mod_cast Nat.lt_succ_iff.mp (Nat.mod_lt M (by norm_num))
        nlinarith [Real.rpow_nonneg hM0.le (-s.re)]
    have htend : Tendsto (fun M : ℕ => (M : ℝ) ^ (-s.re)) atTop (𝓝 0) := by
      have hbase : Tendsto (fun x : ℝ => x ^ (-s.re)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hs0
      exact hbase.comp tendsto_natCast_atTop_atTop
    exact squeeze_zero_norm hb htend
  have h5 := h3.add h4
  rw [add_zero] at h5
  have hfinal := tendsto_nhds_unique h2 h5
  have h2pow : (2:ℂ) ^ ((1:ℂ) - s) = 2 * w := by
    rw [hw, show (1:ℂ) - s = 1 + (-s) by ring,
      Complex.cpow_add _ _ (by norm_num : (2:ℂ) ≠ 0), Complex.cpow_one]
  rw [h2pow]
  exact hfinal.symm

private lemma differentiableOn_etaFun :
    DifferentiableOn ℂ etaFun {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hσ : 0 < s₀.re := hs₀
  set r : ℝ := s₀.re / 2 with hr
  have hrpos : 0 < r := by positivity
  suffices h : DifferentiableOn ℂ etaFun (Metric.ball s₀ r) by
    exact (h.differentiableAt (Metric.ball_mem_nhds s₀ hrpos)).differentiableWithinAt
  have hre : ∀ w ∈ Metric.ball s₀ r, r ≤ w.re := by
    intro w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    have h1 : |(w - s₀).re| ≤ ‖w - s₀‖ := Complex.abs_re_le_norm _
    have h2 : |(w - s₀).re| < r := lt_of_le_of_lt h1 hw
    rw [Complex.sub_re, abs_lt] at h2
    linarith [h2.1]
  have hnorm : ∀ w ∈ Metric.ball s₀ r, ‖w‖ ≤ ‖s₀‖ + r := by
    intro w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    calc ‖w‖ = ‖s₀ + (w - s₀)‖ := by ring_nf
      _ ≤ ‖s₀‖ + ‖w - s₀‖ := norm_add_le _ _
      _ ≤ ‖s₀‖ + r := by linarith
  refine differentiableOn_tsum_of_summable_norm
    (u := fun k : ℕ => (‖s₀‖ + r) * (k : ℝ) ^ (-r - 1))
    ?_ ?_ Metric.isOpen_ball ?_
  · exact ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _)
  · intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h0 : (fun s : ℂ => etaTerm s 0) = fun _ => 0 := by
        funext w
        simp [etaTerm]
      rw [h0]
      exact differentiableOn_const 0
    · have hk0 : ((k : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.pos_iff_ne_zero.mp hk
      have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero k
      have hneg : Differentiable ℂ (fun s : ℂ => -s) := differentiable_id.neg
      have hd : Differentiable ℂ (fun s : ℂ => etaTerm s k) := by
        unfold etaTerm
        exact ((hneg.const_cpow (Or.inl hk0)).sub
          (hneg.const_cpow (Or.inl hk1))).const_mul _
      exact hd.differentiableOn
  · intro k w hw
    have hwre : 0 < w.re := lt_of_lt_of_le hrpos (hre w hw)
    calc ‖etaTerm w k‖ ≤ ‖w‖ * (k : ℝ) ^ (-w.re - 1) := norm_etaTerm_le hwre k
      _ ≤ (‖s₀‖ + r) * (k : ℝ) ^ (-r - 1) := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · rw [Nat.cast_zero, Real.zero_rpow (ne_of_lt (by linarith) : -w.re - 1 ≠ 0),
              Real.zero_rpow (ne_of_lt (by linarith) : -r - 1 ≠ 0), mul_zero, mul_zero]
          · have hk1 : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
            have hrw : (k : ℝ) ^ (-w.re - 1) ≤ (k : ℝ) ^ (-r - 1) :=
              Real.rpow_le_rpow_of_exponent_le hk1 (by linarith [hre w hw])
            have h3 : (0:ℝ) ≤ (k : ℝ) ^ (-w.re - 1) := Real.rpow_nonneg (by positivity) _
            have h4 : (0:ℝ) ≤ ‖s₀‖ + r := by positivity
            exact mul_le_mul (hnorm w hw) hrw h3 h4

/-- The right half-plane minus the point `1` is preconnected. -/
lemma isPreconnected_rePos_compl_one :
    IsPreconnected {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  have hA : IsPreconnected ({s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}) :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hB : IsPreconnected ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im < 0}) :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have hC : IsPreconnected ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1}) :=
    ((convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hD : IsPreconnected {s : ℂ | 1 < s.re} := (convex_halfSpace_re_gt 1).isPreconnected
  have hCA : IsPreconnected (({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1})
      ∪ ({s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im})) := by
    apply IsPreconnected.union ((1/2 : ℂ) + (1/2) * I) _ _ hC hA
    · exact ⟨by simp, by simp; norm_num⟩
    · exact ⟨by simp, by simp⟩
  have hCAB : IsPreconnected ((({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1})
      ∪ ({s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}))
      ∪ ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im < 0})) := by
    apply IsPreconnected.union ((1/2 : ℂ) - (1/2) * I) _ _ hCA hB
    · apply Set.mem_union_left
      exact ⟨by simp, by simp; norm_num⟩
    · exact ⟨by simp, by simp⟩
  have hAll : IsPreconnected (((({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1})
      ∪ ({s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}))
      ∪ ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im < 0})) ∪ {s : ℂ | 1 < s.re}) := by
    apply IsPreconnected.union ((2 : ℂ) + I) _ _ hCAB hD
    · apply Set.mem_union_left
      apply Set.mem_union_right
      exact ⟨by simp, by simp⟩
    · show (1:ℝ) < ((2:ℂ) + I).re
      simp
  have hset : {s : ℂ | 0 < s.re ∧ s ≠ 1}
      = ((({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.re < 1})
        ∪ ({s : ℂ | 0 < s.re} ∩ {s : ℂ | 0 < s.im}))
        ∪ ({s : ℂ | 0 < s.re} ∩ {s : ℂ | s.im < 0})) ∪ {s : ℂ | 1 < s.re} := by
    ext s
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_trichotomy s.im 0 with him | him | him
      · exact Or.inl (Or.inr ⟨h1, him⟩)
      · rcases lt_trichotomy s.re 1 with hre | hre | hre
        · exact Or.inl (Or.inl (Or.inl ⟨h1, hre⟩))
        · exact absurd (Complex.ext hre him) h2
        · exact Or.inr hre
      · exact Or.inl (Or.inl (Or.inr ⟨h1, him⟩))
    · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | h1)
      · exact ⟨h1, fun h => by rw [h] at h2; simp at h2⟩
      · exact ⟨h1, fun h => by rw [h] at h2; simp at h2⟩
      · exact ⟨h1, fun h => by rw [h] at h2; simp at h2⟩
      · exact ⟨by linarith, fun h => by rw [h] at h1; simp at h1⟩
  rw [hset]
  exact hAll

/-- `etaFun = (1 − 2^{1−s}) ζ(s)` on the right half-plane minus `1`. -/
lemma etaFun_eqOn :
    Set.EqOn etaFun (fun s => (1 - (2:ℂ) ^ ((1:ℂ) - s)) * riemannZeta s)
      {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  have hopen0 : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hopen : IsOpen {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
    have h2 : IsOpen {s : ℂ | s ≠ 1} := isOpen_compl_singleton
    have hset : {s : ℂ | 0 < s.re ∧ s ≠ 1} = {s : ℂ | 0 < s.re} ∩ {s : ℂ | s ≠ 1} := rfl
    rw [hset]
    exact hopen0.inter h2
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ) (z₀ := (2:ℂ))
    ?_ ?_ isPreconnected_rePos_compl_one ?_ ?_
  · exact (differentiableOn_etaFun.analyticOnNhd hopen0).mono (fun s hs => hs.1)
  · apply DifferentiableOn.analyticOnNhd _ hopen
    intro s hs
    have h1 : DifferentiableAt ℂ (fun s : ℂ => 1 - (2:ℂ) ^ ((1:ℂ) - s)) s := by
      have h := ((differentiable_const (1:ℂ)).sub differentiable_id).const_cpow
        (Or.inl (by norm_num : (2:ℂ) ≠ 0))
      exact (differentiableAt_const 1).sub (h s)
    exact (h1.mul (differentiableAt_riemannZeta hs.2)).differentiableWithinAt
  · constructor
    · show (0:ℝ) < (2:ℂ).re
      norm_num
    · norm_num
  · have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2:ℂ) := by
      have ho : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
      apply ho.mem_nhds
      show (1:ℝ) < (2:ℂ).re
      norm_num
    filter_upwards [hmem] with z hz
    exact etaFun_eq_of_one_lt_re hz

lemma etaFun_two_ne_zero : etaFun 2 ≠ 0 := by
  have h2 : (1:ℝ) < (2:ℂ).re := by norm_num
  rw [etaFun_eq_of_one_lt_re h2]
  apply mul_ne_zero
  · have h : (1:ℂ) - 2 = -1 := by norm_num
    rw [h, Complex.cpow_neg_one]
    norm_num
  · intro h
    have h13 := one_third_le_norm_LFunction_of_two_le_re (N := 1)
      (1 : DirichletCharacter ℂ 1) (s := 2) (by norm_num)
    rw [DirichletCharacter.LFunction_modOne_eq, h, norm_zero] at h13
    linarith

lemma analyticOrderAt_etaFun_ne_top {ρ : ℂ} (hρ : 0 < ρ.re) :
    analyticOrderAt etaFun ρ ≠ ⊤ := by
  intro htop
  have hopen0 : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hA : AnalyticOnNhd ℂ etaFun {s : ℂ | 0 < s.re} :=
    differentiableOn_etaFun.analyticOnNhd hopen0
  have hev : etaFun =ᶠ[𝓝 ρ] 0 := by
    filter_upwards [analyticOrderAt_eq_top.mp htop] with z hz using hz
  have hEq : Set.EqOn etaFun 0 {s : ℂ | 0 < s.re} :=
    hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_halfSpace_re_gt 0).isPreconnected hρ hev
  have h2mem : (2:ℂ) ∈ {s : ℂ | 0 < s.re} := by
    show (0:ℝ) < (2:ℂ).re
    norm_num
  exact etaFun_two_ne_zero (hEq h2mem)

/-- Local factorization of the order of `etaFun`: near any `ρ` with `Re ρ > 0`, `ρ ≠ 1`,
`etaFun = (1 − 2^{1−s})·ζ`, so the orders add. -/
private lemma analyticOrderAt_etaFun_decomp {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ ≠ 1) :
    analyticOrderAt etaFun ρ
      = analyticOrderAt (fun s : ℂ => 1 - (2:ℂ) ^ ((1:ℂ) - s)) ρ
        + analyticOrderAt riemannZeta ρ := by
  have hopen : IsOpen {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
    have h1 : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : IsOpen {s : ℂ | s ≠ 1} := isOpen_compl_singleton
    exact h1.inter h2
  have hmem : ρ ∈ {s : ℂ | 0 < s.re ∧ s ≠ 1} := ⟨hρ, hρ1⟩
  have hev : etaFun =ᶠ[𝓝 ρ] fun s => (1 - (2:ℂ) ^ ((1:ℂ) - s)) * riemannZeta s := by
    filter_upwards [hopen.mem_nhds hmem] with z hz
    exact etaFun_eqOn hz
  have hfac : AnalyticAt ℂ (fun s : ℂ => 1 - (2:ℂ) ^ ((1:ℂ) - s)) ρ := by
    have h : Differentiable ℂ (fun s : ℂ => 1 - (2:ℂ) ^ ((1:ℂ) - s)) :=
      (differentiable_const 1).sub
        (((differentiable_const (1:ℂ)).sub differentiable_id).const_cpow
          (Or.inl (by norm_num : (2:ℂ) ≠ 0)))
    exact h.analyticAt ρ
  have hζ : AnalyticAt ℂ riemannZeta ρ := by
    have hopen1 : IsOpen {s : ℂ | s ≠ 1} := isOpen_compl_singleton
    have hd : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun z hz =>
      (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact hd.analyticAt (hopen1.mem_nhds hρ1)
  rw [analyticOrderAt_congr hev]
  have hprod : (fun s : ℂ => (1 - (2:ℂ) ^ ((1:ℂ) - s)) * riemannZeta s)
      = (fun s : ℂ => 1 - (2:ℂ) ^ ((1:ℂ) - s)) * riemannZeta := rfl
  rw [hprod]
  exact analyticOrderAt_mul hfac hζ

/-- `ζ` has finite vanishing order at every point of `Re > 0` minus `1`. -/
lemma analyticOrderAt_zeta_ne_top {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  intro htop
  have hd := analyticOrderAt_etaFun_decomp hρ hρ1
  rw [htop, add_top] at hd
  exact analyticOrderAt_etaFun_ne_top hρ hd

/-- Every zero of `ζ` in `Re > 0` (minus `1`) is a zero of `etaFun` of at least
the same order. -/
lemma analyticOrderNatAt_zeta_le_etaFun {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ ≠ 1) :
    analyticOrderNatAt riemannZeta ρ ≤ analyticOrderNatAt etaFun ρ := by
  have hle : analyticOrderAt riemannZeta ρ ≤ analyticOrderAt etaFun ρ := by
    rw [analyticOrderAt_etaFun_decomp hρ hρ1]
    exact le_add_self
  exact ENat.toNat_le_toNat hle (analyticOrderAt_etaFun_ne_top hρ)

end Eta

/-! ### The Jensen disks at `2 + it₀` -/

section Disks

/-- Points of the radius-`7/4` disk around `2 + it₀` have `Re ≥ 1/4`. -/
lemma disk_re_ge {t₀ : ℝ} {z : ℂ} (hz : z ∈ closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ)) :
    1/4 ≤ z.re := by
  rw [mem_closedBall, Complex.dist_eq] at hz
  have h := Complex.abs_re_le_norm (z - ((2:ℂ) + t₀ * I))
  have hre : (z - ((2:ℂ) + t₀ * I)).re = z.re - 2 := by simp
  rw [hre] at h
  have := abs_le.mp (le_trans h hz)
  linarith [this.1]

lemma norm_center_le (t₀ : ℝ) : ‖(2:ℂ) + t₀ * I‖ ≤ 2 + |t₀| := by
  calc ‖(2:ℂ) + t₀ * I‖ ≤ ‖(2:ℂ)‖ + ‖(t₀:ℂ) * I‖ := norm_add_le _ _
    _ = 2 + |t₀| := by simp

lemma disk_norm_le {t₀ : ℝ} {z : ℂ} (hz : z ∈ closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ)) :
    ‖z‖ ≤ |t₀| + 15/4 := by
  rw [mem_closedBall, Complex.dist_eq] at hz
  calc ‖z‖ = ‖(z - ((2:ℂ) + t₀ * I)) + ((2:ℂ) + t₀ * I)‖ := by ring_nf
    _ ≤ ‖z - ((2:ℂ) + t₀ * I)‖ + ‖(2:ℂ) + t₀ * I‖ := norm_add_le _ _
    _ ≤ 7/4 + (2 + |t₀|) := add_le_add hz (norm_center_le t₀)
    _ = |t₀| + 15/4 := by ring

lemma re_center (t₀ : ℝ) : ((2:ℂ) + t₀ * I).re = 2 := by simp

/-- **Unit-disk zero count for nontrivial characters.**  The total vanishing
multiplicity of `L(·,χ)` on any finset inside the disk `‖s − (2+it₀)‖ ≤ 13/8` is at
most `112 · log (N (|t₀|+2))`. -/
theorem sum_ord_LFunction_disk_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (t₀ : ℝ) {F : Finset ℂ}
    (hF : ∀ ρ ∈ F, ρ ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ)) :
    (∑ ρ ∈ F, analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
      ≤ 112 * Real.log (N * (|t₀| + 2)) := by
  have hN1 : (1:ℝ) ≤ N := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have ht0 : (0:ℝ) ≤ |t₀| := abs_nonneg t₀
  have hX2 : (2:ℝ) ≤ N * (|t₀| + 2) := by nlinarith
  have hA : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ)
      (closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ)) :=
    fun z _ => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have hM : (1:ℝ) ≤ 15 * N * (|t₀| + 2) := by nlinarith
  have hlow : 1/6 ≤ ‖DirichletCharacter.LFunction χ ((2:ℂ) + t₀ * I)‖ := by
    have h13 := one_third_le_norm_LFunction_of_two_le_re χ
      (s := (2:ℂ) + t₀ * I) (by rw [re_center])
    linarith
  have hbd : ∀ z ∈ sphere ((2:ℂ) + t₀ * I) (7/4 : ℝ),
      ‖DirichletCharacter.LFunction χ z‖ ≤ 15 * N * (|t₀| + 2) := by
    intro z hz
    have hz' : z ∈ closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ) := sphere_subset_closedBall hz
    have h1 := norm_LFunction_le_of_one_quarter_le_re χ hχ (disk_re_ge hz')
    have h2 := disk_norm_le hz'
    nlinarith
  have key := sum_analyticOrderNatAt_le hA hM hlow hbd hF
  have hlog : Real.log (6 * (15 * N * (|t₀| + 2))) ≤ 8 * Real.log (N * (|t₀| + 2)) := by
    have h : (6:ℝ) * (15 * N * (|t₀| + 2)) = 90 * (N * (|t₀| + 2)) := by ring
    rw [h]
    exact log_ninety_mul_le hX2
  linarith

/-- **Unit-disk zero count for `etaFun`** (hence for `ζ`, with multiplicity). -/
theorem sum_ord_etaFun_disk_le (t₀ : ℝ) {F : Finset ℂ}
    (hF : ∀ ρ ∈ F, ρ ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ)) :
    (∑ ρ ∈ F, analyticOrderNatAt etaFun ρ : ℝ) ≤ 112 * Real.log (|t₀| + 2) := by
  have ht0 : (0:ℝ) ≤ |t₀| := abs_nonneg t₀
  have hX2 : (2:ℝ) ≤ |t₀| + 2 := by linarith
  have hopen0 : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hA : AnalyticOnNhd ℂ etaFun (closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ)) := by
    apply (differentiableOn_etaFun.analyticOnNhd hopen0).mono
    intro z hz
    have := disk_re_ge hz
    show (0:ℝ) < z.re
    linarith
  have hM : (1:ℝ) ≤ 15 * (|t₀| + 2) := by nlinarith
  have hlow : 1/6 ≤ ‖etaFun ((2:ℂ) + t₀ * I)‖ := by
    have hre1 : (1:ℝ) < ((2:ℂ) + t₀ * I).re := by rw [re_center]; norm_num
    rw [etaFun_eq_of_one_lt_re hre1, norm_mul]
    have hζ : 1/3 ≤ ‖riemannZeta ((2:ℂ) + t₀ * I)‖ := by
      have h13 := one_third_le_norm_LFunction_of_two_le_re (N := 1)
        (1 : DirichletCharacter ℂ 1) (s := (2:ℂ) + t₀ * I) (by rw [re_center])
      rwa [DirichletCharacter.LFunction_modOne_eq] at h13
    have hfac : 1/2 ≤ ‖1 - (2:ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀ * I))‖ := by
      have hnorm : ‖(2:ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀ * I))‖ = 1/2 := by
        have hb : (2:ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀ * I))
            = ((2:ℝ):ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀ * I)) := by norm_num
        have hre : ((1:ℂ) - ((2:ℂ) + t₀ * I)).re = -1 := by
          simp
          norm_num
        rw [hb, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2), hre,
          Real.rpow_neg_one]
        norm_num
      calc (1/2 : ℝ) = ‖(1:ℂ)‖ - 1/2 := by simp; norm_num
        _ = ‖(1:ℂ)‖ - ‖(2:ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀ * I))‖ := by rw [hnorm]
        _ ≤ ‖1 - (2:ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀ * I))‖ := norm_sub_norm_le _ _
    nlinarith [norm_nonneg (1 - (2:ℂ) ^ ((1:ℂ) - ((2:ℂ) + t₀ * I))),
      norm_nonneg (riemannZeta ((2:ℂ) + t₀ * I))]
  have hbd : ∀ z ∈ sphere ((2:ℂ) + t₀ * I) (7/4 : ℝ), ‖etaFun z‖ ≤ 15 * (|t₀| + 2) := by
    intro z hz
    have hz' : z ∈ closedBall ((2:ℂ) + t₀ * I) (7/4 : ℝ) := sphere_subset_closedBall hz
    have h1 := norm_etaFun_le_of_one_quarter_le_re (disk_re_ge hz')
    have h2 := disk_norm_le hz'
    nlinarith
  have key := sum_analyticOrderNatAt_le hA hM hlow hbd hF
  have hlog : Real.log (6 * (15 * (|t₀| + 2))) ≤ 8 * Real.log (|t₀| + 2) := by
    have h : (6:ℝ) * (15 * (|t₀| + 2)) = 90 * (|t₀| + 2) := by ring
    rw [h]
    exact log_ninety_mul_le hX2
  linarith

end Disks

/-! ### Box counts: covering `[1/2,1] × [−T,T]` by unit disks at integer heights -/

section BoxCount

private lemma round_mem_Icc {T : ℝ} (_hT : 1 ≤ T) {γ : ℝ} (hγ : |γ| ≤ T) :
    round γ ∈ Finset.Icc (-⌈T⌉) ⌈T⌉ := by
  have h1 : |γ - round γ| ≤ 1/2 := abs_sub_round γ
  have h2 : |(round γ : ℝ)| ≤ T + 1/2 := by
    have h0 : (round γ : ℝ) = γ - (γ - round γ) := by ring
    rw [h0]
    calc |γ - (γ - (round γ : ℝ))| ≤ |γ| + |γ - (round γ : ℝ)| := abs_sub _ _
      _ ≤ T + 1/2 := add_le_add hγ h1
  have hceil : T ≤ (⌈T⌉ : ℝ) := Int.le_ceil T
  rw [Finset.mem_Icc]
  constructor
  · have hlow : -(T + 1/2) ≤ (round γ : ℝ) := neg_le_of_abs_le h2
    have hlt : (-(⌈T⌉ : ℝ)) - 1 < (round γ : ℝ) := by linarith
    have hz : -⌈T⌉ - 1 < round γ := by exact_mod_cast hlt
    omega
  · have hup : (round γ : ℝ) ≤ T + 1/2 := le_of_abs_le h2
    have hlt : (round γ : ℝ) < (⌈T⌉ : ℝ) + 1 := by linarith
    have hz : round γ < ⌈T⌉ + 1 := by exact_mod_cast hlt
    omega

private lemma mem_fiber_ball {ρ : ℂ} (h1 : 1/2 ≤ ρ.re) (h2 : ρ.re ≤ 1) :
    ρ ∈ closedBall ((2:ℂ) + (round ρ.im : ℝ) * I) (13/8 : ℝ) := by
  rw [mem_closedBall, Complex.dist_eq]
  apply norm_le_of_sq_le (by norm_num)
  have hre : (ρ - ((2:ℂ) + (round ρ.im : ℝ) * I)).re = ρ.re - 2 := by simp
  have him : (ρ - ((2:ℂ) + (round ρ.im : ℝ) * I)).im = ρ.im - round ρ.im := by simp
  rw [hre, him]
  have ha : |ρ.im - round ρ.im| ≤ 1/2 := abs_sub_round ρ.im
  have hb : (ρ.im - (round ρ.im : ℝ)) ^ 2 ≤ (1/2) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ha 2
  nlinarith

/-- Generic box count from a disk bound: if every radius-`13/8` disk at height `t₀`
carries multiplicity mass `≤ 112 log (A(|t₀|+2))`, then the box `[1/2,1] × [−T,T]`
carries mass `≤ 1120 · T · log (A(T+2))`. -/
private lemma box_count_core {f : ℂ → ℂ} {A : ℝ} (hA : 1 ≤ A)
    (hdisk : ∀ t₀ : ℝ, ∀ F : Finset ℂ,
      (∀ ρ ∈ F, ρ ∈ closedBall ((2:ℂ) + t₀ * I) (13/8 : ℝ)) →
      (∑ ρ ∈ F, analyticOrderNatAt f ρ : ℝ) ≤ 112 * Real.log (A * (|t₀| + 2)))
    {T : ℝ} (hT : 1 ≤ T) {G : Finset ℂ}
    (hG : ∀ ρ ∈ G, 1/2 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T) :
    (∑ ρ ∈ G, analyticOrderNatAt f ρ : ℝ) ≤ 1120 * T * Real.log (A * (T + 2)) := by
  have hT0 : (0:ℝ) < T := by linarith
  have hA2 : (2:ℝ) ≤ A * (T + 2) := by nlinarith
  have hlogpos : (0:ℝ) ≤ Real.log (A * (T + 2)) := Real.log_nonneg (by linarith)
  have hmaps : ∀ ρ ∈ G, round ρ.im ∈ Finset.Icc (-⌈T⌉) ⌈T⌉ := fun ρ hρ =>
    round_mem_Icc hT (hG ρ hρ).2.2
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps
    (fun ρ => (analyticOrderNatAt f ρ : ℝ))
  rw [← hfib]
  have hfiber : ∀ k ∈ Finset.Icc (-⌈T⌉) ⌈T⌉,
      (∑ ρ ∈ G.filter (fun ρ => round ρ.im = k), (analyticOrderNatAt f ρ : ℝ))
        ≤ 224 * Real.log (A * (T + 2)) := by
    intro k hk
    have hin : ∀ ρ ∈ G.filter (fun ρ => round ρ.im = k),
        ρ ∈ closedBall ((2:ℂ) + (k : ℝ) * I) (13/8 : ℝ) := by
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      have hmem := mem_fiber_ball (hG ρ hρ.1).1 (hG ρ hρ.1).2.1
      rwa [hρ.2] at hmem
    have hd := hdisk (k : ℝ) _ hin
    have hkT : |(k : ℝ)| ≤ T + 1 := by
      rw [Finset.mem_Icc] at hk
      have hu : (k : ℝ) ≤ (⌈T⌉ : ℝ) := by exact_mod_cast hk.2
      have hl : (-(⌈T⌉ : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hk.1
      have hc : (⌈T⌉ : ℝ) < T + 1 := Int.ceil_lt_add_one T
      rw [abs_le]
      constructor <;> linarith
    have harg0 : (0:ℝ) < A * (|(k : ℝ)| + 2) := by
      nlinarith [abs_nonneg (k : ℝ)]
    have hlog1 : Real.log (A * (|(k : ℝ)| + 2)) ≤ Real.log (2 * (A * (T + 2))) := by
      apply Real.log_le_log harg0
      nlinarith [abs_nonneg (k : ℝ)]
    have hlog2 : Real.log (2 * (A * (T + 2))) = Real.log 2 + Real.log (A * (T + 2)) :=
      Real.log_mul (by norm_num) (by nlinarith)
    have hlog3 : Real.log 2 ≤ Real.log (A * (T + 2)) :=
      Real.log_le_log (by norm_num) hA2
    linarith
  calc ∑ k ∈ Finset.Icc (-⌈T⌉) ⌈T⌉,
        ∑ ρ ∈ G.filter (fun ρ => round ρ.im = k), (analyticOrderNatAt f ρ : ℝ)
      ≤ ∑ _k ∈ Finset.Icc (-⌈T⌉) ⌈T⌉, (224 * Real.log (A * (T + 2))) :=
        Finset.sum_le_sum hfiber
    _ = ((Finset.Icc (-⌈T⌉) ⌈T⌉).card : ℝ) * (224 * Real.log (A * (T + 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (5 * T) * (224 * Real.log (A * (T + 2))) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        -- card (Icc (−⌈T⌉) ⌈T⌉) = 2⌈T⌉ + 1 ≤ 2(T+1)+1 ≤ 5T
        have hnn : (0:ℤ) ≤ 2 * ⌈T⌉ + 1 := by
          have : (1:ℤ) ≤ ⌈T⌉ := by exact_mod_cast (le_trans hT (Int.le_ceil T) : (1:ℝ) ≤ ⌈T⌉)
          omega
        have hcardeq : (Finset.Icc (-⌈T⌉) ⌈T⌉).card = (2 * ⌈T⌉ + 1).toNat := by
          rw [Int.card_Icc]
          congr 1
          ring
        have h0 : ((2 * ⌈T⌉ + 1).toNat : ℤ) = 2 * ⌈T⌉ + 1 := Int.toNat_of_nonneg hnn
        have h2 : ((2 * ⌈T⌉ + 1).toNat : ℝ) = 2 * (⌈T⌉ : ℝ) + 1 := by
          exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h0
        rw [hcardeq, h2]
        have hc : (⌈T⌉ : ℝ) < T + 1 := Int.ceil_lt_add_one T
        linarith
    _ = 1120 * T * Real.log (A * (T + 2)) := by ring

/-- **Box zero count, nontrivial characters** (`C₂ = 1120`):
`N(1/2, T, χ) ≤ 1120 · T · log (N (T+2))` for `T ≥ 1`. -/
theorem zeroCountBox_le_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {T : ℝ} (hT : 1 ≤ T) :
    (zeroCountBox χ (1/2) T : ℝ) ≤ 1120 * T * Real.log (N * (T + 2)) := by
  have hN1 : (1:ℝ) ≤ N := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hcast : (zeroCountBox χ (1/2) T : ℝ)
      = ∑ ρ ∈ zeroFinset χ (1/2) T,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
    rw [zeroCountBox]
    push_cast
    rfl
  rw [hcast]
  refine box_count_core hN1 (fun t₀ F hF => sum_ord_LFunction_disk_le χ hχ t₀ hF) hT ?_
  intro ρ hρ
  rw [mem_zeroFinset] at hρ
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1⟩

/-! ### The principal character: reduction to `ζ` via the eta function -/

/-- Local factorization of the order of the principal `L`-function:
`L(·,χ₀) = eulerFactor N · ζ` away from `1`, so the orders add. -/
private lemma analyticOrderAt_trivChar_decomp {N : ℕ} [NeZero N] {ρ : ℂ} (hρ1 : ρ ≠ 1) :
    analyticOrderAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)) ρ
      = analyticOrderAt (eulerFactor N) ρ + analyticOrderAt riemannZeta ρ := by
  have hopen : IsOpen {s : ℂ | s ≠ 1} := isOpen_compl_singleton
  have hev : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)
      =ᶠ[𝓝 ρ] fun s => eulerFactor N s * riemannZeta s := by
    filter_upwards [hopen.mem_nhds hρ1] with z hz
    have h := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := N) hz
    simpa [eulerFactor, DirichletCharacter.LFunctionTrivChar] using h
  have hE : AnalyticAt ℂ (eulerFactor N) ρ := (differentiable_eulerFactor N).analyticAt ρ
  have hζ : AnalyticAt ℂ riemannZeta ρ := by
    have hd : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun z hz =>
      (differentiableAt_riemannZeta hz).differentiableWithinAt
    exact hd.analyticAt (hopen.mem_nhds hρ1)
  rw [analyticOrderAt_congr hev]
  have hprod : (fun s : ℂ => eulerFactor N s * riemannZeta s)
      = eulerFactor N * riemannZeta := rfl
  rw [hprod]
  exact analyticOrderAt_mul hE hζ

/-- At `Re > 0`, `s ≠ 1`, the vanishing order of the principal `L`-function mod `N`
equals that of `ζ` (the Euler factor does not vanish there). -/
lemma analyticOrderNatAt_trivChar_eq {N : ℕ} [NeZero N] {ρ : ℂ}
    (hρ : 0 < ρ.re) (hρ1 : ρ ≠ 1) :
    analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N)) ρ
      = analyticOrderNatAt riemannZeta ρ := by
  have hE : AnalyticAt ℂ (eulerFactor N) ρ := (differentiable_eulerFactor N).analyticAt ρ
  have hE0 : analyticOrderAt (eulerFactor N) ρ = 0 :=
    hE.analyticOrderAt_eq_zero.mpr (eulerFactor_ne_zero hρ)
  rw [analyticOrderNatAt, analyticOrderNatAt, analyticOrderAt_trivChar_decomp hρ1, hE0,
    zero_add]

/-- Every `L(·,χ)` has finite vanishing order at every point of `Re > 0` minus `1`
(this includes the principal character). -/
lemma analyticOrderAt_LFunction_ne_top {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ ≠ 1) :
    analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
  by_cases hχ : χ = 1
  · subst hχ
    rw [analyticOrderAt_trivChar_decomp hρ1, ne_eq, ENat.add_eq_top]
    rintro (h | h)
    · have hEfun : eulerFactor N ≠ 0 := by
        intro h0
        have h2 : eulerFactor N 2 ≠ 0 := eulerFactor_ne_zero (by norm_num : (0:ℝ) < (2:ℂ).re)
        rw [h0] at h2
        exact h2 rfl
      have := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ
        (fun z => (differentiable_eulerFactor N).analyticAt z)).mp h
      exact hEfun this
    · exact analyticOrderAt_zeta_ne_top hρ hρ1 h
  · intro h
    have hLfun := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ
      (fun z => (DirichletCharacter.differentiable_LFunction hχ).analyticAt z)).mp h
    have hL2 : DirichletCharacter.LFunction χ 2 ≠ 0 := by
      intro h0
      have h13 := one_third_le_norm_LFunction_of_two_le_re χ (s := 2) (by norm_num)
      rw [h0, norm_zero] at h13
      linarith
    rw [hLfun] at hL2
    exact hL2 rfl

/-- Each member of `zeroFinset χ σ T` (with `σ > 0`) is a zero of positive, finite
multiplicity: `analyticOrderNatAt (LFunction χ) ρ ≥ 1`.  Z4c/Z5 may therefore treat
`zeroFinset`/`analyticOrderNatAt` as an honest multiplicity-weighted zero list. -/
lemma one_le_analyticOrderNatAt_of_mem_zeroFinset {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {σ T : ℝ} (hσ : 0 < σ) {ρ : ℂ}
    (hρ : ρ ∈ zeroFinset χ σ T) :
    1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ := by
  rw [mem_zeroFinset] at hρ
  obtain ⟨h1, _, _, h4, h5⟩ := hρ
  have hρre : 0 < ρ.re := lt_of_lt_of_le hσ h1
  have hAt : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ := by
    have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {s : ℂ | s ≠ 1} :=
      fun z hz => (DirichletCharacter.differentiableAt_LFunction χ z
        (Or.inl hz)).differentiableWithinAt
    exact hd.analyticAt (isOpen_compl_singleton.mem_nhds h4)
  have hne0 : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hAt, h5⟩
  have hnetop := analyticOrderAt_LFunction_ne_top χ hρre h4
  rw [Nat.one_le_iff_ne_zero, analyticOrderNatAt]
  intro h0
  rcases ENat.toNat_eq_zero.mp h0 with h | h
  · exact hne0 h
  · exact hnetop h

/-- **Riemann zeta box count** (the `d = 1` principal character IS `ζ`):
`N_ζ(1/2, T) ≤ 1120 · T · log (T+2)` for `T ≥ 1`, zeros counted with multiplicity. -/
theorem zeroCountBox_one_le {T : ℝ} (hT : 1 ≤ T) :
    (zeroCountBox (1 : DirichletCharacter ℂ 1) (1/2) T : ℝ)
      ≤ 1120 * T * Real.log (T + 2) := by
  have hcast : (zeroCountBox (1 : DirichletCharacter ℂ 1) (1/2) T : ℝ)
      = ∑ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T,
          (analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ρ : ℝ) := by
    rw [zeroCountBox]
    push_cast
    rfl
  rw [hcast]
  have hstep : ∀ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T,
      (analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ρ : ℝ)
        ≤ (analyticOrderNatAt etaFun ρ : ℝ) := by
    intro ρ hρ
    rw [mem_zeroFinset] at hρ
    have hρre : 0 < ρ.re := by linarith [hρ.1]
    have hord : analyticOrderNatAt (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1)) ρ
        = analyticOrderNatAt riemannZeta ρ := by
      rw [DirichletCharacter.LFunction_modOne_eq]
    rw [hord]
    exact_mod_cast analyticOrderNatAt_zeta_le_etaFun hρre hρ.2.2.2.1
  have hbound : (∑ ρ ∈ zeroFinset (1 : DirichletCharacter ℂ 1) (1/2) T,
      (analyticOrderNatAt etaFun ρ : ℝ)) ≤ 1120 * T * Real.log (1 * (T + 2)) := by
    refine box_count_core le_rfl (fun t₀ F hF => ?_) hT ?_
    · have h := sum_ord_etaFun_disk_le t₀ hF
      rw [one_mul]
      exact h
    · intro ρ hρ
      rw [mem_zeroFinset] at hρ
      exact ⟨hρ.1, hρ.2.1, hρ.2.2.1⟩
  rw [one_mul] at hbound
  exact le_trans (Finset.sum_le_sum hstep) hbound

/-- The principal character's box count equals the `ζ` box count (any `σ > 0`). -/
lemma zeroCountBox_trivChar_eq (N : ℕ) [NeZero N] {σ T : ℝ} (hσ : 0 < σ) :
    zeroCountBox (1 : DirichletCharacter ℂ N) σ T
      = zeroCountBox (1 : DirichletCharacter ℂ 1) σ T := by
  have hsets : zeroFinset (1 : DirichletCharacter ℂ N) σ T
      = zeroFinset (1 : DirichletCharacter ℂ 1) σ T := by
    ext ρ
    rw [mem_zeroFinset, mem_zeroFinset]
    constructor
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, h2, h3, h4, ?_⟩
      rw [DirichletCharacter.LFunction_modOne_eq]
      have hρre : 0 < ρ.re := lt_of_lt_of_le hσ h1
      have hfact : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) ρ
          = (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-ρ))) * riemannZeta ρ :=
        DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := N) h4
      rw [hfact] at h5
      rcases mul_eq_zero.mp h5 with h | h
      · exact absurd h (by simpa [eulerFactor] using eulerFactor_ne_zero (N := N) hρre)
      · exact h
    · rintro ⟨h1, h2, h3, h4, h5⟩
      refine ⟨h1, h2, h3, h4, ?_⟩
      rw [DirichletCharacter.LFunction_modOne_eq] at h5
      have hfact : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) ρ
          = (∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-ρ))) * riemannZeta ρ :=
        DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := N) h4
      rw [hfact, h5, mul_zero]
  rw [zeroCountBox, zeroCountBox, hsets]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [mem_zeroFinset] at hρ
  have hρre : 0 < ρ.re := lt_of_lt_of_le hσ hρ.1
  rw [analyticOrderNatAt_trivChar_eq hρre hρ.2.2.2.1,
    DirichletCharacter.LFunction_modOne_eq]

/-- **Box zero count, principal character.** -/
theorem zeroCountBox_trivChar_le {N : ℕ} [NeZero N] {T : ℝ} (hT : 1 ≤ T) :
    (zeroCountBox (1 : DirichletCharacter ℂ N) (1/2) T : ℝ)
      ≤ 1120 * T * Real.log (T + 2) := by
  rw [zeroCountBox_trivChar_eq N (by norm_num : (0:ℝ) < 1/2)]
  exact zeroCountBox_one_le hT

end BoxCount

/-! ### The frozen Z4b interface -/

section Interface

/-- **THE FROZEN Z4b INTERFACE** (routez/Z0a-ledger.md §7, with `C₁ = 1120`):
`N(1/2, t, d) = ∑_{χ mod d} N(1/2, t, χ) ≤ 1120 · t · d · log (d (t+2))` for `t ≥ 1`,
`d ≥ 1`, all characters (principal included), zeros counted with multiplicity. -/
theorem sum_zeroCountBox_le (d : ℕ) [NeZero d] {t : ℝ} (ht : 1 ≤ t) :
    ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ (1/2) t : ℝ)
      ≤ 1120 * t * d * Real.log (d * (t + 2)) := by
  have hd1 : (1:ℝ) ≤ d := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have ht2 : (0:ℝ) < t + 2 := by linarith
  have hlogpos : (0:ℝ) ≤ Real.log (d * (t + 2)) := Real.log_nonneg (by nlinarith)
  have hper : ∀ χ : DirichletCharacter ℂ d,
      (zeroCountBox χ (1/2) t : ℝ) ≤ 1120 * t * Real.log (d * (t + 2)) := by
    intro χ
    by_cases hχ : χ = 1
    · subst hχ
      calc (zeroCountBox (1 : DirichletCharacter ℂ d) (1/2) t : ℝ)
          ≤ 1120 * t * Real.log (t + 2) := zeroCountBox_trivChar_le ht
        _ ≤ 1120 * t * Real.log (d * (t + 2)) := by
            have h1 : Real.log (t + 2) ≤ Real.log (d * (t + 2)) :=
              Real.log_le_log (by linarith) (by nlinarith)
            nlinarith
    · exact zeroCountBox_le_of_ne_one χ hχ ht
  have hcard : ((Finset.univ : Finset (DirichletCharacter ℂ d)).card : ℝ) ≤ d := by
    have h1 : Nat.card (DirichletCharacter ℂ d) = d.totient :=
      DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
    have h2 : (Finset.univ : Finset (DirichletCharacter ℂ d)).card = d.totient := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h1]
    rw [h2]
    exact_mod_cast Nat.totient_le d
  have hconst : (0:ℝ) ≤ 1120 * t * Real.log (d * (t + 2)) := by
    have h0 : (0:ℝ) ≤ 1120 * t := by linarith
    exact mul_nonneg h0 hlogpos
  calc ∑ χ : DirichletCharacter ℂ d, (zeroCountBox χ (1/2) t : ℝ)
      ≤ ∑ _χ : DirichletCharacter ℂ d, (1120 * t * Real.log (d * (t + 2))) :=
        Finset.sum_le_sum fun χ _ => hper χ
    _ = ((Finset.univ : Finset (DirichletCharacter ℂ d)).card : ℝ)
        * (1120 * t * Real.log (d * (t + 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d : ℝ) * (1120 * t * Real.log (d * (t + 2))) :=
        mul_le_mul_of_nonneg_right hcard hconst
    _ = 1120 * t * d * Real.log (d * (t + 2)) := by ring

end Interface

end Carmichael