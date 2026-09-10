/-
Route Z, sortie Z4a′-corollaries: the I1 scope closure
(routez/Z0b-density.md §2 I1, §12.1 last paragraph, §9).

No `sorry`, no `axiom`, no `native_decide` in this file.
`#print axioms` on every theorem below: [propext, Classical.choice, Quot.sound].

The delivered `LConvexity.norm_LFunction_le_convexity'` covers only primitive
nontrivial characters.  The Z0b machine consumes I1 for ALL `χ mod d`
(Lemmas 4.2, 6.3) and for `ζ` (§9, Theorem Z band (c) at `d = 1`).  This file
delivers the missing corollaries:

1. `norm_LFunction_le_convexity_nonprincipal` — every non-principal `χ mod N`
   (imprimitive included), with the frozen extra factor `2^{ω(N)}`:
   `‖L(s,χ)‖ ≤ 100000·2^{ω(N)}·(N(|t|+2))^{max((1−σ)/2,0)}·log(N(|t|+3))`
   on `1/200 ≤ σ ≤ 2`.  Route: Mathlib `DirichletCharacter.LFunction_changeLevel`
   (the Euler-factor identity `L(s,χ) = L(s,χ*)·∏_{p∣N}(1−χ*(p)p^{−s})` exists
   in the pin — nothing had to be built), each factor `≤ 2` for `σ ≥ 0`.
2. `two_pow_card_primeFactors_le_rpow` — the I9(d) divisor bound in the form
   the I1 corollaries consume: `2^{ω(m)} ≤ C_τ·m^{ε/8}` with `ε = 1/100`
   (frozen master parameter), i.e. exponent `1/800`; `C_τ = 2^{2^{800}}`.
   Only the `2^{ω}` form is consumed anywhere (Z0b §2 I1 block, Lemmas 4.2,
   6.3); the `τ(m)` phrasing of I9(d) is not needed and not delivered.
3. `norm_riemannZeta_le_convexity` — the ζ variant with the pole term:
   `‖ζ(s)‖ ≤ 200000·(|t|+2)^{max((1−σ)/2,0)}·log(|t|+3) + 200000/‖s−1‖`
   on `1/200 ≤ σ ≤ 2` (no `s ≠ 1` hypothesis: at `s = 1` Mathlib's value
   `(γ − log(4π))/2` satisfies the bound trivially).  Route: the pin's entire
   completion `riemannZeta₀ = ζ − 1/(s−1)`; strip growth from the elementary
   representation `ζ₀(s) = 1/2 − s(s+1)∫_1^∞ Ψ(t)t^{−s−2}dt` with
   `Ψ(t) = (fract t)(fract t − 1)/2 ∈ [−1/8, 0]` (proved on `Re s > 1` via
   Mathlib `LSeries_eq_mul_integral'` + integration by parts, extended to
   `Re s > −1/2` by the identity theorem on the convex half-plane); left edge
   from `riemannZeta_one_sub` + the delivered `norm_Gamma_one_sub_mul_sin_interp`;
   Phragmén–Lindelöf main interpolation mirroring `norm_LFunction_le_convexity'`.
4. `norm_LFunctionTrivChar_le_convexity` — the principal case,
   `‖L(s,χ₀)‖ ≤ 200000·2^{ω(N)}·((N(|t|+2))^{max}·log(N(|t|+3)) + 1/‖s−1‖)`
   for `s ≠ 1`, via `LFunctionTrivChar_eq_mul_riemannZeta`.
5. `norm_LFunction_le_convexity_all` — the single citable lemma over all
   `χ mod N` (hypothesis `χ ≠ 1 ∨ s ≠ 1`), constant `200000`:
   `‖L(s,χ)‖ ≤ 200000·2^{ω(N)}·((N(|t|+2))^{max((1−σ)/2,0)}·log(N(|t|+3)) + 1/‖s−1‖)`.

Also delivered en route: `norm_riemannZeta₀_le` (uniform strip growth
`‖ζ₀(z)‖ ≤ 1/2 + ‖z‖‖z+1‖/4` on `Re z ≥ −1/2`) and
`norm_riemannZeta₀_le_convexity` (the pole-free PL bound for `ζ₀`, constant
`200000`), plus `norm_LFunction_le_convexity_nonprincipal'` (divisor bound
folded: constant `100000·C_τ`, extra factor `N^{1/800}`).

DEVIATIONS (reported, none silent):
* I9(d) is delivered in the `2^{ω(m)} ≤ C_τ m^{1/800}` form with the explicit
  `C_τ = 2^{2^{800}}`; the `τ(m)` phrasing of Z0b §2 is not delivered — every
  consumer (the §2 I1 block, Lemmas 4.2, 6.3, §11.1 row 4) consumes only the
  `2^{ω(d)}` factor, and `2^{ω} ≤ τ` anyway.
* The ζ variant and its consumers use `C_cx = 200000`; the delivered primitive
  lemma keeps its `C_cx = 100000`.  I1 requires only an absolute constant; all
  SHAPES (d-exponent `max((1−σ)/2,0)`, single log, `2^{ω(d)}` packaging, pole
  term `C/|s−1|`) are exactly the frozen ones.
* The ζ variant needs no `s ≠ 1` hypothesis (strictly stronger than frozen):
  Mathlib's `ζ(1) = (γ − log 4π)/2` satisfies the bound outright.

MATHLIB NOTES FOUND EN ROUTE:
* `DirichletCharacter.LFunction_changeLevel` + `changeLevel_primitiveCharacter`
  give the imprimitive Euler-factor identity — nothing had to be built.
* `riemannZeta₀` (entire completion of `ζ − 1/(s−1)`) and
  `differentiable_riemannZeta₀` are in the pin (`Harmonic/ZetaAsymp`), as is
  `riemannZeta_one`.
* The fract topology lemmas (`tendsto_fract_left'`, `continuousAt_fract`,
  `measurable_fract`) are root-level, NOT in the `Int` namespace.
* `LSeries_eq_mul_integral'` (`LSeries/SumCoeff`) gives `ζ(s) = s∫⌊t⌋t^{−s−1}`
  for free; the sawtooth integration by parts and the analytic continuation of
  `∫Ψ(t)t^{−s−2}` (via `hasDerivAt_integral_of_dominated_loc_of_deriv_le` and
  `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` on the convex half-plane
  `Re > −1`) are built here.
* `squeeze_zero_norm'` names its bound function `a`, not `g`.
* `Finset.card_filter_add_card_filter_not` (not `filter_card_add_filter_neg_…`).
* `Real.finsetProd_rpow` (deprecated alias `finset_prod_rpow`).
* Keep `2^800` unevaluated: `maxRecDepth 8000` and never `norm_num`/`omega`
  near the literal (the "exponent exceeds threshold" warning is intended).
-/
import Carmichael.LConvexity
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.Algebra.Order.Floor

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

namespace Carmichael

open Complex Finset Filter Set
open scoped Real Topology

/-! ### The Euler-factor product bound -/

section EulerFactors

/-- Each Euler factor `1 − c·p^{−s}` with `‖c‖ ≤ 1` has norm `≤ 2` for `Re s ≥ 0`;
the product over the prime factors of `N` is `≤ 2^{ω(N)}`. -/
lemma norm_prod_euler_factors_le {N : ℕ} {s : ℂ} (hσ : 0 ≤ s.re) (c : ℕ → ℂ)
    (hc : ∀ p ∈ N.primeFactors, ‖c p‖ ≤ 1) :
    ‖∏ p ∈ N.primeFactors, (1 - c p * (p : ℂ) ^ (-s))‖ ≤ 2 ^ N.primeFactors.card := by
  rw [norm_prod]
  have hterm : ∀ p ∈ N.primeFactors, ‖1 - c p * (p : ℂ) ^ (-s)‖ ≤ 2 := by
    intro p hp
    have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
    have hp0 : 0 < p := by omega
    have hcpow : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
      rw [Complex.norm_natCast_cpow_of_pos hp0, Complex.neg_re]
    have hple : (p : ℝ) ^ (-s.re) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast Nat.one_le_of_lt hp2
      · linarith
    calc ‖1 - c p * (p : ℂ) ^ (-s)‖ ≤ ‖(1 : ℂ)‖ + ‖c p * (p : ℂ) ^ (-s)‖ :=
          norm_sub_le _ _
      _ = 1 + ‖c p‖ * ‖(p : ℂ) ^ (-s)‖ := by rw [norm_one, norm_mul]
      _ ≤ 1 + 1 * 1 := by
          have h1 := hc p hp
          have h2 : ‖c p‖ * ‖(p : ℂ) ^ (-s)‖ ≤ 1 * 1 := by
            apply mul_le_mul h1 _ (norm_nonneg _) zero_le_one
            rw [hcpow]
            exact hple
          linarith
      _ = 2 := by norm_num
  calc ∏ p ∈ N.primeFactors, ‖1 - c p * (p : ℂ) ^ (-s)‖
      ≤ ∏ _p ∈ N.primeFactors, (2 : ℝ) :=
        Finset.prod_le_prod (fun p _ => norm_nonneg _) hterm
    _ = 2 ^ N.primeFactors.card := Finset.prod_const 2

end EulerFactors

/-! ### The I9(d) divisor bound, `2^{ω}` form, exponent `ε/8 = 1/800` -/

section DivisorBound

/-- `2 ≤ p^{1/800}` for `p ≥ 2^{800}`. -/
private lemma two_le_rpow_inv_800 {p : ℕ} (hp : 2 ^ 800 ≤ p) :
    (2 : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / 800) := by
  have hcast : ((2 : ℝ)) ^ (800 : ℕ) ≤ (p : ℝ) := by
    exact_mod_cast hp
  have hbase : ((2 : ℝ) ^ (800 : ℕ)) ^ ((1 : ℝ) / 800) = 2 := by
    rw [← Real.rpow_natCast (2 : ℝ) 800, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  calc (2 : ℝ) = ((2 : ℝ) ^ (800 : ℕ)) ^ ((1 : ℝ) / 800) := hbase.symm
    _ ≤ (p : ℝ) ^ ((1 : ℝ) / 800) :=
        Real.rpow_le_rpow (by positivity) hcast (by norm_num)

/-- **I9(d), `2^{ω}` form (frozen: `ε/8 = 1/800` at `ε = 1/100`).**
`2^{ω(m)} ≤ C_τ·m^{1/800}` with the explicit `C_τ = 2^{2^{800}}`. -/
lemma two_pow_card_primeFactors_le_rpow {m : ℕ} (hm : m ≠ 0) :
    (2 : ℝ) ^ m.primeFactors.card
      ≤ (2 : ℝ) ^ (2 ^ 800 : ℕ) * (m : ℝ) ^ ((1 : ℝ) / 800) := by
  classical
  set S := m.primeFactors with hS
  set Sb := S.filter (fun p => 2 ^ 800 ≤ p) with hSb
  set Ss := S.filter (fun p => ¬ 2 ^ 800 ≤ p) with hSs
  have hcard : Sb.card + Ss.card = S.card := by
    rw [hSs, hSb]
    exact Finset.card_filter_add_card_filter_not (fun p => 2 ^ 800 ≤ p)
  -- small primes: at most 2^800 of them
  have hsmall : Ss.card ≤ 2 ^ 800 := by
    have hsub : Ss ⊆ Finset.range (2 ^ 800) := by
      intro p hp
      rw [hSs, Finset.mem_filter] at hp
      exact Finset.mem_range.mpr (not_le.mp hp.2)
    calc Ss.card ≤ (Finset.range (2 ^ 800)).card := Finset.card_le_card hsub
      _ = 2 ^ 800 := Finset.card_range _
  have hsmallpow : (2 : ℝ) ^ Ss.card ≤ (2 : ℝ) ^ (2 ^ 800 : ℕ) :=
    pow_le_pow_right₀ (by norm_num) hsmall
  -- large primes: 2 ≤ p^{1/800} termwise
  have hbigpow : (2 : ℝ) ^ Sb.card ≤ (m : ℝ) ^ ((1 : ℝ) / 800) := by
    have hterm : (2 : ℝ) ^ Sb.card ≤ ∏ p ∈ Sb, (p : ℝ) ^ ((1 : ℝ) / 800) := by
      rw [← Finset.prod_const (2 : ℝ)]
      apply Finset.prod_le_prod (fun p _ => by norm_num)
      intro p hp
      rw [hSb, Finset.mem_filter] at hp
      exact two_le_rpow_inv_800 hp.2
    have hprodrw : ∏ p ∈ Sb, (p : ℝ) ^ ((1 : ℝ) / 800)
        = ((∏ p ∈ Sb, p : ℕ) : ℝ) ^ ((1 : ℝ) / 800) := by
      rw [Nat.cast_prod]
      exact (Real.finsetProd_rpow Sb _ (fun p _ => by positivity) _)
    have hdvd : (∏ p ∈ Sb, p) ∣ m := by
      have h1 : (∏ p ∈ Sb, p) ∣ ∏ p ∈ S, p :=
        Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
      exact h1.trans (Nat.prod_primeFactors_dvd m)
    have hle : ((∏ p ∈ Sb, p : ℕ) : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd
    calc (2 : ℝ) ^ Sb.card ≤ ∏ p ∈ Sb, (p : ℝ) ^ ((1 : ℝ) / 800) := hterm
      _ = ((∏ p ∈ Sb, p : ℕ) : ℝ) ^ ((1 : ℝ) / 800) := hprodrw
      _ ≤ (m : ℝ) ^ ((1 : ℝ) / 800) :=
          Real.rpow_le_rpow (by positivity) hle (by norm_num)
  calc (2 : ℝ) ^ S.card = (2 : ℝ) ^ Ss.card * (2 : ℝ) ^ Sb.card := by
        rw [← pow_add, add_comm, hcard]
    _ ≤ (2 : ℝ) ^ (2 ^ 800 : ℕ) * (m : ℝ) ^ ((1 : ℝ) / 800) := by
        apply mul_le_mul hsmallpow hbigpow (by positivity) (by positivity)

end DivisorBound

/-! ### The imprimitive non-principal corollary -/

section Imprimitive

variable {N : ℕ} [NeZero N]

/-- The Euler-factor identity for a non-principal character in terms of its
primitive character (Mathlib `LFunction_changeLevel` + `changeLevel_primitiveCharacter`). -/
lemma LFunction_eq_primitive_mul_prod {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (s : ℂ) :
    have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    DirichletCharacter.LFunction χ s
      = DirichletCharacter.LFunction χ.primitiveCharacter s *
          ∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h, DirichletCharacter.changeLevel_one]
  have h := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level
    χ.primitiveCharacter (Or.inl hχ') (s := s)
  rwa [χ.changeLevel_primitiveCharacter] at h

/-- **I1, imprimitive non-principal corollary (frozen shape, §12.1).**
For every non-principal `χ mod N` and `1/200 ≤ σ ≤ 2`:
`‖L(s,χ)‖ ≤ 100000·2^{ω(N)}·(N(|t|+2))^{max((1−σ)/2,0)}·log(N(|t|+3))`. -/
theorem norm_LFunction_le_convexity_nonprincipal {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {s : ℂ} (hσ1 : 1/200 ≤ s.re) (hσ2 : s.re ≤ 2) :
    ‖DirichletCharacter.LFunction χ s‖
      ≤ 100000 * 2 ^ N.primeFactors.card
          * ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
          * Real.log ((N:ℝ) * (|s.im| + 3)) := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hχ' : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h, DirichletCharacter.changeLevel_one]
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hNpos
  have habs : (0:ℝ) ≤ |s.im| := abs_nonneg _
  -- conductor facts
  have hdN : (χ.conductor : ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.le_of_dvd hNpos χ.conductor_dvd_level
  have hd1 : (1:ℝ) ≤ (χ.conductor : ℝ) := by
    have := Nat.pos_of_ne_zero χ.conductor_ne_zero
    exact_mod_cast this
  -- the primitive convexity bound at the conductor
  have hprim := norm_LFunction_le_convexity' χ.primitiveCharacter_isPrimitive hχ' hσ1 hσ2
  -- monotonicity of the two D-parts in the modulus
  have hmax0 : (0:ℝ) ≤ max ((1 - s.re)/2) 0 := le_max_right _ _
  have hbase2 : (0:ℝ) < (χ.conductor : ℝ) * (|s.im| + 2) := by positivity
  have hbase2' : (χ.conductor : ℝ) * (|s.im| + 2) ≤ (N:ℝ) * (|s.im| + 2) := by
    apply mul_le_mul_of_nonneg_right hdN (by linarith)
  have hDpow : ((χ.conductor : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
      ≤ ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0) :=
    Real.rpow_le_rpow hbase2.le hbase2' hmax0
  have hlog : Real.log ((χ.conductor : ℝ) * (|s.im| + 3))
      ≤ Real.log ((N:ℝ) * (|s.im| + 3)) := by
    apply Real.log_le_log (by positivity)
    apply mul_le_mul_of_nonneg_right hdN (by linarith)
  have hlog0 : (0:ℝ) ≤ Real.log ((χ.conductor : ℝ) * (|s.im| + 3)) := by
    apply Real.log_nonneg
    nlinarith
  have hDpow0 : (0:ℝ) ≤ ((χ.conductor : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0) :=
    Real.rpow_nonneg hbase2.le _
  have hDpowN0 : (0:ℝ) ≤ ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0) :=
    Real.rpow_nonneg (by positivity) _
  have hlogN0 : (0:ℝ) ≤ Real.log ((N:ℝ) * (|s.im| + 3)) := hlog0.trans hlog
  -- primitive bound relaxed to modulus N
  have hprimN : ‖DirichletCharacter.LFunction χ.primitiveCharacter s‖
      ≤ 100000 * ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
          * Real.log ((N:ℝ) * (|s.im| + 3)) := by
    calc ‖DirichletCharacter.LFunction χ.primitiveCharacter s‖
        ≤ 100000 * ((χ.conductor : ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
            * Real.log ((χ.conductor : ℝ) * (|s.im| + 3)) := hprim
      _ ≤ 100000 * ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
            * Real.log ((N:ℝ) * (|s.im| + 3)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hDpow (by norm_num)
          · exact hlog
          · exact hlog0
          · positivity
  -- Euler factors
  have hprod : ‖∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s))‖
      ≤ 2 ^ N.primeFactors.card := by
    apply norm_prod_euler_factors_le (by linarith : (0:ℝ) ≤ s.re)
    intro p _
    exact χ.primitiveCharacter.norm_le_one _
  -- assemble
  rw [LFunction_eq_primitive_mul_prod hχ s, norm_mul]
  calc ‖DirichletCharacter.LFunction χ.primitiveCharacter s‖ *
      ‖∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s))‖
      ≤ (100000 * ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
          * Real.log ((N:ℝ) * (|s.im| + 3))) * 2 ^ N.primeFactors.card := by
        apply mul_le_mul hprimN hprod (norm_nonneg _) (by positivity)
    _ = 100000 * 2 ^ N.primeFactors.card
          * ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
          * Real.log ((N:ℝ) * (|s.im| + 3)) := by ring

/-- The imprimitive non-principal corollary with the divisor bound folded in:
`‖L(s,χ)‖ ≤ 100000·C_τ·N^{1/800}·(N(|t|+2))^{max((1−σ)/2,0)}·log(N(|t|+3))`,
`C_τ = 2^{2^{800}}` (I9(d) at `ε/8 = 1/800`). -/
theorem norm_LFunction_le_convexity_nonprincipal' {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {s : ℂ} (hσ1 : 1/200 ≤ s.re) (hσ2 : s.re ≤ 2) :
    ‖DirichletCharacter.LFunction χ s‖
      ≤ 100000 * (2 : ℝ) ^ (2 ^ 800 : ℕ) * (N:ℝ) ^ ((1:ℝ)/800)
          * ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
          * Real.log ((N:ℝ) * (|s.im| + 3)) := by
  have h := norm_LFunction_le_convexity_nonprincipal hχ hσ1 hσ2
  have hτ := two_pow_card_primeFactors_le_rpow (NeZero.ne N)
  have hDpow0 : (0:ℝ) ≤ ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0) :=
    Real.rpow_nonneg (by positivity) _
  have hlog0 : (0:ℝ) ≤ Real.log ((N:ℝ) * (|s.im| + 3)) := by
    apply Real.log_nonneg
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    nlinarith [abs_nonneg s.im]
  calc ‖DirichletCharacter.LFunction χ s‖
      ≤ 100000 * 2 ^ N.primeFactors.card
          * ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
          * Real.log ((N:ℝ) * (|s.im| + 3)) := h
    _ ≤ 100000 * ((2 : ℝ) ^ (2 ^ 800 : ℕ) * (N:ℝ) ^ ((1:ℝ)/800))
          * ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
          * Real.log ((N:ℝ) * (|s.im| + 3)) := by
        apply mul_le_mul_of_nonneg_right _ hlog0
        apply mul_le_mul_of_nonneg_right _ hDpow0
        apply mul_le_mul_of_nonneg_left hτ (by norm_num)
    _ = 100000 * (2 : ℝ) ^ (2 ^ 800 : ℕ) * (N:ℝ) ^ ((1:ℝ)/800)
          * ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
          * Real.log ((N:ℝ) * (|s.im| + 3)) := by simp only [mul_assoc]

end Imprimitive

/-! ### The sawtooth antiderivative and the `ζ₀` integral representation

`ψ(t) := fract t − 1/2` has the continuous antiderivative
`Ψ(t) := ((fract t)² − fract t)/2` with `Ψ = 0` at integers and `|Ψ| ≤ 1/8`.
Euler–Maclaurin at first order gives, for `Re s > 1`,
`ζ(s) = s/(s−1) − 1/2 − s(s+1)·∫_1^∞ Ψ(t)t^{−s−2}dt`; the right side minus the
pole is analytic on `Re s > −1`, so the identity theorem extends
`ζ₀(s) = 1/2 − s(s+1)·K(s)` to all of `Re s > −1`, whence the uniform strip
growth bound `‖ζ₀(z)‖ ≤ 1/2 + ‖z‖‖z+1‖/4` on `Re z ≥ −1/2`. -/

section ZetaRep

open MeasureTheory intervalIntegral

/-- The centered sawtooth `ψ(t) = fract t − 1/2`. -/
private noncomputable def saw (t : ℝ) : ℝ := Int.fract t - 1/2

/-- The quadratic `q(y) = (y² − y)/2`. -/
private noncomputable def qpoly (y : ℝ) : ℝ := (y^2 - y)/2

/-- The sawtooth antiderivative `Ψ(t) = ((fract t)² − fract t)/2`. -/
private noncomputable def sawInt (t : ℝ) : ℝ := qpoly (Int.fract t)

private lemma abs_saw_le (t : ℝ) : |saw t| ≤ 1/2 := by
  have h1 := Int.fract_nonneg t
  have h2 := Int.fract_lt_one t
  rw [saw, abs_le]
  constructor <;> nlinarith

private lemma abs_sawInt_le (t : ℝ) : |sawInt t| ≤ 1/8 := by
  have h1 := Int.fract_nonneg t
  have h2 := Int.fract_lt_one t
  rw [sawInt, qpoly, abs_le]
  constructor <;> nlinarith [sq_nonneg (Int.fract t - 1/2)]

private lemma sawInt_intCast (n : ℤ) : sawInt (n : ℝ) = 0 := by
  rw [sawInt, Int.fract_intCast, qpoly]
  norm_num

private lemma continuous_qpoly : Continuous qpoly := by
  unfold qpoly
  fun_prop

private lemma continuous_sawInt : Continuous sawInt := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne ((⌊x⌋ : ℤ) : ℝ) x with hx | hx
  · -- integer point: left and right limits both `qpoly` of `1` resp. `0`, i.e. `0`
    set n : ℤ := ⌊x⌋ with hn
    have hleft : Tendsto sawInt (𝓝[<] ((n : ℤ) : ℝ)) (𝓝 0) := by
      have h1 : Tendsto Int.fract (𝓝[<] ((n : ℤ) : ℝ)) (𝓝 1) := tendsto_fract_left' n
      have h2 := (continuous_qpoly.tendsto 1).comp h1
      have h3 : qpoly 1 = 0 := by rw [qpoly]; norm_num
      rw [h3] at h2
      exact h2.congr (fun y => rfl)
    have hright : Tendsto sawInt (𝓝[≥] ((n : ℤ) : ℝ)) (𝓝 0) := by
      have h1 : Tendsto Int.fract (𝓝[≥] ((n : ℤ) : ℝ)) (𝓝 0) := tendsto_fract_right' n
      have h2 := (continuous_qpoly.tendsto 0).comp h1
      have h3 : qpoly 0 = 0 := by rw [qpoly]; norm_num
      rw [h3] at h2
      exact h2.congr (fun y => rfl)
    have hcomb : Tendsto sawInt (𝓝 ((n : ℤ) : ℝ)) (𝓝 0) := by
      rw [← nhdsLT_sup_nhdsGE ((n : ℤ) : ℝ)]
      exact hleft.sup hright
    rw [← hx]
    show Tendsto sawInt (𝓝 ((n : ℤ) : ℝ)) (𝓝 (sawInt ((n : ℤ) : ℝ)))
    rw [sawInt_intCast n]
    exact hcomb
  · -- non-integer point: `fract` is continuous there
    have h1 : ContinuousAt Int.fract x := continuousAt_fract (Ne.symm hx)
    exact continuous_qpoly.continuousAt.comp h1

/-- Right-derivative of `Ψ` at every point `x`: within `Ioi x`, `Ψ` has
derivative `ψ x`.  (Uniform over integers and non-integers: to the right of
`x`, eventually `⌊t⌋ = ⌊x⌋`.) -/
private lemma hasDerivWithinAt_sawInt (x : ℝ) :
    HasDerivWithinAt sawInt (saw x) (Ioi x) x := by
  set n : ℤ := ⌊x⌋ with hn
  set q : ℝ → ℝ := fun t => ((t - (n : ℝ))^2 - (t - (n : ℝ)))/2 with hq
  -- derivative of the polynomial model
  have hqd : HasDerivAt q (x - (n : ℝ) - 1/2) x := by
    rw [hq]
    have h1 : HasDerivAt (fun t : ℝ => t - (n : ℝ)) 1 x := (hasDerivAt_id x).sub_const _
    have h3 := ((h1.pow 2).sub h1).div_const 2
    have hv : ((2:ℕ) * (x - (n : ℝ)) ^ 1 * 1 - 1) / 2 = x - (n : ℝ) - 1/2 := by
      push_cast
      ring
    rw [← hv]
    exact h3
  -- `sawInt` agrees with the polynomial model on the right of `x`
  have hev : sawInt =ᶠ[𝓝[>] x] q := by
    have hmem : Iio ((n : ℝ) + 1) ∈ 𝓝[>] x :=
      nhdsWithin_le_nhds (Iio_mem_nhds (Int.lt_floor_add_one x))
    filter_upwards [hmem, self_mem_nhdsWithin] with t ht1 ht2
    have hfloor : ⌊t⌋ = n := by
      rw [Int.floor_eq_iff]
      exact ⟨le_trans (Int.floor_le x) (le_of_lt ht2), by exact_mod_cast ht1⟩
    rw [sawInt, qpoly, ← Int.self_sub_floor, hfloor, hq]
  have hx0 : sawInt x = q x := by
    rw [sawInt, qpoly, ← Int.self_sub_floor, ← hn, hq]
  have hval : saw x = x - (n : ℝ) - 1/2 := by
    rw [saw, ← Int.self_sub_floor, ← hn]
  rw [hval]
  exact (hqd.hasDerivWithinAt).congr_of_eventuallyEq hev hx0

/-! #### Integrability of the two integrands -/

private lemma aestronglyMeasurable_cpow_Ioi (c : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ c)
      (volume.restrict (Ioi (1:ℝ))) := by
  apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioi
  intro t ht
  have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht
  rcases eq_or_ne c 0 with rfl | hc
  · simp only [Complex.cpow_zero]
    exact continuousWithinAt_const
  · exact ((hasDerivAt_ofReal_cpow_const ht0.ne' hc).differentiableAt.continuousAt).continuousWithinAt

private lemma norm_ofReal_mul_cpow {f : ℝ → ℝ} {t : ℝ} (ht : 0 < t) (c : ℂ) :
    ‖((f t : ℝ) : ℂ) * (t : ℂ) ^ c‖ = |f t| * t ^ c.re := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos ht]

private lemma aestronglyMeasurable_saw_mul (c : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => ((saw t : ℝ) : ℂ) * (t : ℂ) ^ c)
      (volume.restrict (Ioi (1:ℝ))) := by
  apply AEStronglyMeasurable.mul _ (aestronglyMeasurable_cpow_Ioi c)
  apply Measurable.aestronglyMeasurable
  apply Complex.measurable_ofReal.comp
  exact (measurable_fract.sub measurable_const)

private lemma aestronglyMeasurable_sawInt_mul (c : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => ((sawInt t : ℝ) : ℂ) * (t : ℂ) ^ c)
      (volume.restrict (Ioi (1:ℝ))) := by
  apply AEStronglyMeasurable.mul _ (aestronglyMeasurable_cpow_Ioi c)
  exact (Complex.continuous_ofReal.comp continuous_sawInt).aestronglyMeasurable

private lemma integrableOn_saw_mul {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => ((saw t : ℝ) : ℂ) * (t : ℂ) ^ (-s-1)) (Ioi 1) := by
  apply Integrable.mono' ((integrableOn_Ioi_rpow_of_lt
    (by linarith : -s.re - 1 < -1) zero_lt_one).const_mul (1/2 : ℝ))
    (aestronglyMeasurable_saw_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht
  rw [norm_ofReal_mul_cpow ht0]
  have hre : (-s-1).re = -s.re - 1 := by
    simp [Complex.sub_re, Complex.neg_re]
  rw [hre]
  apply mul_le_mul_of_nonneg_right (abs_saw_le t) (Real.rpow_nonneg ht0.le _)

private lemma integrableOn_sawInt_mul {s : ℂ} (hs : -1 < s.re) :
    IntegrableOn (fun t : ℝ => ((sawInt t : ℝ) : ℂ) * (t : ℂ) ^ (-s-2)) (Ioi 1) := by
  apply Integrable.mono' ((integrableOn_Ioi_rpow_of_lt
    (by linarith : -s.re - 2 < -1) zero_lt_one).const_mul (1/8 : ℝ))
    (aestronglyMeasurable_sawInt_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht
  rw [norm_ofReal_mul_cpow ht0]
  have hre : (-s-2).re = -s.re - 2 := by
    simp [Complex.sub_re, Complex.neg_re]
  rw [hre]
  apply mul_le_mul_of_nonneg_right (abs_sawInt_le t) (Real.rpow_nonneg ht0.le _)

/-! #### Identity A: Euler–Maclaurin at first order, `Re s > 1` -/

/-- For `Re s > 1`:
`ζ(s) = s/(s−1) − 1/2 − s·∫_1^∞ ψ(t)t^{−s−1}dt` (via Mathlib
`LSeries_eq_mul_integral'` at `f = 1`). -/
private lemma zeta_eq_sub_saw_integral {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = s/(s-1) - 1/2
      - s * ∫ t in Ioi (1:ℝ), ((saw t : ℝ) : ℂ) * (t : ℂ) ^ (-s-1) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := by linear_combination h
    rw [this] at hs
    simp at hs
  -- the Mathlib integral representation of `LSeries 1`
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, ‖(1 : ℕ → ℂ) k‖) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    apply Asymptotics.isBigO_of_le atTop
    intro n
    have h1 : ∑ k ∈ Icc 1 n, ‖(1 : ℕ → ℂ) k‖ = (n : ℝ) := by
      simp [Nat.card_Icc]
    rw [h1, Real.rpow_one]
  have base := LSeries_eq_mul_integral' (1 : ℕ → ℂ) (by norm_num : (0:ℝ) ≤ 1) hs hO
  rw [← LSeries_one_eq_riemannZeta hs, base]
  -- rewrite the integrand pointwise on `Ioi 1`
  have hptwise : ∀ t ∈ Ioi (1:ℝ),
      (∑ k ∈ Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) * (t : ℂ) ^ (-(s+1))
        = (t : ℂ) ^ (-s) - (1/2 : ℂ) * (t : ℂ) ^ (-s-1)
            - ((saw t : ℝ) : ℂ) * (t : ℂ) ^ (-s-1) := by
    intro t ht
    have ht1 : (1:ℝ) < t := ht
    have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht1
    have htC : (t : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt ht0
    have hsum2 : (∑ k ∈ Icc 1 ⌊t⌋₊, (1 : ℕ → ℂ) k) = ((⌊t⌋₊ : ℕ) : ℂ) := by
      simp [Nat.card_Icc]
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) = t - Int.fract t := by
      have h1 : ((⌊t⌋₊ : ℕ) : ℤ) = ⌊t⌋ := Int.natCast_floor_eq_floor (le_of_lt ht0)
      have h2 : ((⌊t⌋₊ : ℕ) : ℝ) = ((⌊t⌋ : ℤ) : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h1
      rw [h2, ← Int.self_sub_fract]
    have hflC : ((⌊t⌋₊ : ℕ) : ℂ) = (t : ℂ) - (1/2 : ℂ) - ((saw t : ℝ) : ℂ) := by
      have h3 : ((⌊t⌋₊ : ℕ) : ℂ) = (((⌊t⌋₊ : ℕ) : ℝ) : ℂ) := by push_cast; ring
      rw [h3, hfl, saw]
      push_cast
      ring
    have hexp : -(s+1) = -s-1 := by ring
    have hcpow : (t : ℂ) * (t : ℂ) ^ (-s-1) = (t : ℂ) ^ (-s) := by
      have h4 : (t : ℂ) ^ (-s) = (t : ℂ) ^ (-s-1) * (t : ℂ) ^ (1:ℂ) := by
        rw [← Complex.cpow_add _ _ htC]
        congr 1
        ring
      rw [h4, Complex.cpow_one]
      exact mul_comm ((t : ℂ)) ((t : ℂ) ^ (-s-1))
    rw [hsum2, hexp, hflC]
    calc ((t : ℂ) - 1/2 - ((saw t : ℝ) : ℂ)) * (t : ℂ) ^ (-s-1)
        = (t : ℂ) * (t : ℂ) ^ (-s-1) - (1/2 : ℂ) * (t : ℂ) ^ (-s-1)
            - ((saw t : ℝ) : ℂ) * (t : ℂ) ^ (-s-1) := by ring
      _ = (t : ℂ) ^ (-s) - (1/2 : ℂ) * (t : ℂ) ^ (-s-1)
            - ((saw t : ℝ) : ℂ) * (t : ℂ) ^ (-s-1) := by rw [hcpow]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hptwise]
  -- split the integral
  have hI1 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Ioi 1) :=
    integrableOn_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith) zero_lt_one
  have hI2 : IntegrableOn (fun t : ℝ => (1/2 : ℂ) * (t : ℂ) ^ (-s-1)) (Ioi 1) := by
    apply Integrable.const_mul
    exact integrableOn_Ioi_cpow_of_lt
      (by simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]; linarith) zero_lt_one
  have hI3 : IntegrableOn (fun t : ℝ => ((saw t : ℝ) : ℂ) * (t : ℂ) ^ (-s-1)) (Ioi 1) :=
    integrableOn_saw_mul (by linarith)
  have hsubint : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (-s) - (1/2 : ℂ) * (x : ℂ) ^ (-s-1)) (Ioi 1) := hI1.sub hI2
  have hsplit1 : (∫ x in Ioi (1:ℝ),
        ((x : ℂ) ^ (-s) - (1/2 : ℂ) * (x : ℂ) ^ (-s-1) - ((saw x : ℝ) : ℂ) * (x : ℂ) ^ (-s-1)))
      = (∫ x in Ioi (1:ℝ), ((x : ℂ) ^ (-s) - (1/2 : ℂ) * (x : ℂ) ^ (-s-1)))
        - ∫ x in Ioi (1:ℝ), ((saw x : ℝ) : ℂ) * (x : ℂ) ^ (-s-1) :=
    MeasureTheory.integral_sub hsubint hI3
  have hsplit2 : (∫ x in Ioi (1:ℝ), ((x : ℂ) ^ (-s) - (1/2 : ℂ) * (x : ℂ) ^ (-s-1)))
      = (∫ x in Ioi (1:ℝ), (x : ℂ) ^ (-s))
        - ∫ x in Ioi (1:ℝ), (1/2 : ℂ) * (x : ℂ) ^ (-s-1) :=
    MeasureTheory.integral_sub hI1 hI2
  rw [hsplit1, hsplit2, MeasureTheory.integral_const_mul]
  -- evaluate the two explicit integrals
  have hval1 : (∫ t in Ioi (1:ℝ), (t : ℂ) ^ (-s)) = 1/(s-1) := by
    rw [integral_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith) zero_lt_one]
    rw [Complex.ofReal_one, Complex.one_cpow]
    have h5 : -s + 1 ≠ 0 := by
      intro h
      apply hs1
      linear_combination -h
    field_simp
    ring
  have hval2 : (∫ t in Ioi (1:ℝ), (t : ℂ) ^ (-s-1)) = 1/s := by
    rw [integral_Ioi_cpow_of_lt
      (by simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]; linarith) zero_lt_one]
    rw [Complex.ofReal_one, Complex.one_cpow]
    have h6 : -s - 1 + 1 = -s := by ring
    rw [h6]
    field_simp
  rw [hval1, hval2]
  field_simp

/-! #### Identity B: integration by parts, `Re s > 1` -/

/-- For `Re s > 1`:
`∫_1^∞ ψ(t)t^{−s−1}dt = (s+1)·∫_1^∞ Ψ(t)t^{−s−2}dt`
(FTC with right-derivatives on `[1,T]`, then `T → ∞`). -/
private lemma saw_integral_eq_sawInt {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Ioi (1:ℝ), ((saw t : ℝ) : ℂ) * (t : ℂ) ^ (-s-1))
      = (s+1) * ∫ t in Ioi (1:ℝ), ((sawInt t : ℝ) : ℂ) * (t : ℂ) ^ (-s-2) := by
  set g : ℝ → ℂ := fun t => ((sawInt t : ℝ) : ℂ) * (t : ℂ) ^ (-s-1) with hg
  set g' : ℝ → ℂ := fun t => ((saw t : ℝ) : ℂ) * (t : ℂ) ^ (-s-1)
    + ((sawInt t : ℝ) : ℂ) * ((-s-1) * (t : ℂ) ^ (-s-2)) with hg'
  have hr0 : (-s-1 : ℂ) ≠ 0 := by
    intro h
    have : (-s-1 : ℂ).re = 0 := by rw [h]; simp
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re] at this
    linarith
  -- integrability of `g'` on the ray
  have hIoi : IntegrableOn g' (Ioi (1:ℝ)) := by
    apply MeasureTheory.Integrable.add
    · exact integrableOn_saw_mul (by linarith)
    · have h7 : IntegrableOn
          (fun t : ℝ => (-s-1) * (((sawInt t : ℝ) : ℂ) * (t : ℂ) ^ (-s-2)))
          (Ioi (1:ℝ)) := (integrableOn_sawInt_mul (by linarith)).const_mul _
      apply h7.congr_fun _ measurableSet_Ioi
      intro t _
      ring
  -- FTC on [1, T]
  have hFTC : ∀ T : ℝ, 1 ≤ T → (∫ t in (1:ℝ)..T, g' t) = g T := by
    intro T hT
    have hcont : ContinuousOn g (Icc 1 T) := by
      apply ContinuousOn.mul
      · exact (Complex.continuous_ofReal.comp continuous_sawInt).continuousOn
      · intro t ht
        have ht0 : (0:ℝ) < t := lt_of_lt_of_le zero_lt_one ht.1
        exact ((hasDerivAt_ofReal_cpow_const ht0.ne' hr0).differentiableAt.continuousAt).continuousWithinAt
    have hderiv : ∀ t ∈ Ioo (1:ℝ) T, HasDerivWithinAt g (g' t) (Ioi t) t := by
      intro t ht
      have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht.1
      have h1 : HasDerivWithinAt (fun u : ℝ => ((sawInt u : ℝ) : ℂ)) ((saw t : ℝ) : ℂ)
          (Ioi t) t := (hasDerivWithinAt_sawInt t).ofReal_comp
      have h2 : HasDerivWithinAt (fun u : ℝ => (u : ℂ) ^ (-s-1))
          ((-s-1) * (t : ℂ) ^ (-s-2)) (Ioi t) t := by
        have h3 := (hasDerivAt_ofReal_cpow_const ht0.ne' hr0).hasDerivWithinAt
          (s := Ioi t)
        have h4 : (-s-1-1 : ℂ) = -s-2 := by ring
        rwa [h4] at h3
      exact h1.mul h2
    have hint : IntervalIntegrable g' MeasureTheory.volume 1 T := by
      apply MeasureTheory.IntegrableOn.intervalIntegrable
      rw [uIcc_of_le hT]
      apply hIoi.mono_set_ae
      rw [MeasureTheory.ae_le_set]
      have h8 : Icc (1:ℝ) T \ Ioi 1 ⊆ {1} := by
        intro x hx
        have h8a : (1:ℝ) ≤ x := hx.1.1
        have h8b : ¬ (1:ℝ) < x := hx.2
        have h8c : x = 1 := le_antisymm (not_lt.mp h8b) h8a
        simp [h8c]
      exact MeasureTheory.measure_mono_null h8 (MeasureTheory.measure_singleton 1)
    have h9 := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hT hcont hderiv hint
    rw [h9]
    have h10 : g 1 = 0 := by
      rw [hg]
      have h11 : sawInt (1:ℝ) = 0 := by
        have := sawInt_intCast 1
        simpa using this
      simp [h11]
    rw [h10, sub_zero]
  -- `T → ∞`: the boundary term vanishes
  have hglim : Tendsto (fun T : ℝ => g T) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun T => (1/8 : ℝ) * T ^ (-s.re - 1))
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
      have hT0 : (0:ℝ) < T := lt_of_lt_of_le zero_lt_one hT
      rw [hg]
      have h12 := norm_ofReal_mul_cpow (f := sawInt) hT0 (-s-1)
      simp only [] at h12 ⊢
      rw [h12]
      have hre : (-s-1 : ℂ).re = -s.re - 1 := by
        simp [Complex.sub_re, Complex.neg_re]
      rw [hre]
      exact mul_le_mul_of_nonneg_right (abs_sawInt_le T) (Real.rpow_nonneg hT0.le _)
    · have h13 : Tendsto (fun T : ℝ => T ^ (-(s.re + 1))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by linarith)
      have h14 := h13.const_mul (1/8 : ℝ)
      rw [mul_zero] at h14
      apply h14.congr
      intro T
      congr 1
      ring_nf
  -- combine the two limits
  have hlim1 : Tendsto (fun T : ℝ => ∫ t in (1:ℝ)..T, g' t) atTop
      (𝓝 (∫ t in Ioi (1:ℝ), g' t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 1 hIoi tendsto_id
  have hlim2 : Tendsto (fun T : ℝ => ∫ t in (1:ℝ)..T, g' t) atTop (𝓝 0) := by
    apply hglim.congr'
    filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    exact (hFTC T hT).symm
  have hzero : (∫ t in Ioi (1:ℝ), g' t) = 0 := tendsto_nhds_unique hlim1 hlim2
  -- split the vanishing integral
  have hsplit : (∫ t in Ioi (1:ℝ), g' t)
      = (∫ t in Ioi (1:ℝ), ((saw t : ℝ) : ℂ) * (t : ℂ) ^ (-s-1))
        + (-s-1) * ∫ t in Ioi (1:ℝ), ((sawInt t : ℝ) : ℂ) * (t : ℂ) ^ (-s-2) := by
    rw [hg']
    rw [MeasureTheory.integral_add (integrableOn_saw_mul (by linarith)) _]
    · congr 1
      have h15 : (fun t : ℝ => ((sawInt t : ℝ) : ℂ) * ((-s-1) * (t : ℂ) ^ (-s-2)))
          = fun t : ℝ => (-s-1) * (((sawInt t : ℝ) : ℂ) * (t : ℂ) ^ (-s-2)) := by
        funext t
        ring
      rw [h15, MeasureTheory.integral_const_mul]
    · have h7 : IntegrableOn
          (fun t : ℝ => (-s-1) * (((sawInt t : ℝ) : ℂ) * (t : ℂ) ^ (-s-2)))
          (Ioi (1:ℝ)) := (integrableOn_sawInt_mul (by linarith)).const_mul _
      apply h7.congr_fun _ measurableSet_Ioi
      intro t _
      ring
  rw [hsplit] at hzero
  linear_combination hzero

/-! #### The representation extends to `Re s > −1` and gives the strip growth bound -/

/-- `K(s) = ∫_1^∞ Ψ(t)t^{−s−2}dt`. -/
private noncomputable def Kint (s : ℂ) : ℂ :=
  ∫ t in Ioi (1:ℝ), ((sawInt t : ℝ) : ℂ) * (t : ℂ) ^ (-s-2)

private lemma differentiableAt_Kint {s₀ : ℂ} (hs₀ : -1 < s₀.re) :
    DifferentiableAt ℂ Kint s₀ := by
  set r : ℝ := (s₀.re + 1)/2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  set ρ : ℝ := s₀.re - r with hρ
  have hρ1 : -1 < ρ := by rw [hρ, hr]; linarith
  set δ : ℝ := (ρ + 1)/2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hexp : δ - ρ - 2 < -1 := by rw [hδ]; linarith
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (z : ℂ) (t : ℝ) => ((sawInt t : ℝ) : ℂ) * (t : ℂ) ^ (-z-2))
    (F' := fun (z : ℂ) (t : ℝ) =>
      ((sawInt t : ℝ) : ℂ) * (-((Real.log t : ℝ) : ℂ) * (t : ℂ) ^ (-z-2)))
    (μ := MeasureTheory.volume.restrict (Ioi (1:ℝ)))
    (x₀ := s₀)
    (bound := fun t => (1/(8*δ)) * t ^ (δ - ρ - 2))
    (s := Metric.ball s₀ r)
    (Metric.ball_mem_nhds s₀ hr0)
    (Eventually.of_forall (fun z => aestronglyMeasurable_sawInt_mul _))
    (integrableOn_sawInt_mul hs₀)
    ?_ ?_ ?_ ?_
  · exact key.2.differentiableAt
  · -- measurability of `F' s₀`
    apply AEStronglyMeasurable.mul
      ((Complex.continuous_ofReal.comp continuous_sawInt).aestronglyMeasurable)
    apply AEStronglyMeasurable.mul
    · exact ((Complex.measurable_ofReal.comp Real.measurable_log).neg).aestronglyMeasurable
    · exact aestronglyMeasurable_cpow_Ioi _
  · -- uniform bound on the ball
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have ht1 : (1:ℝ) < t := ht
    have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht1
    have hzre : ρ ≤ z.re := by
      have h1 : |z.re - s₀.re| ≤ ‖z - s₀‖ := by
        rw [show z.re - s₀.re = (z - s₀).re from by simp [Complex.sub_re]]
        exact Complex.abs_re_le_norm _
      have h2 : ‖z - s₀‖ < r := by
        rw [← dist_eq_norm]
        exact Metric.mem_ball.mp hz
      have h3 := abs_le.mp (le_of_lt (lt_of_le_of_lt h1 h2))
      rw [hρ]
      linarith [h3.1]
    have hlogpos : (0:ℝ) ≤ Real.log t := Real.log_nonneg ht1.le
    have hnorm : ‖((sawInt t : ℝ) : ℂ) * (-((Real.log t : ℝ) : ℂ) * (t : ℂ) ^ (-z-2))‖
        = |sawInt t| * (Real.log t * t ^ ((-z-2).re)) := by
      rw [norm_mul, norm_mul, norm_neg, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ht0,
        abs_of_nonneg hlogpos]
    rw [hnorm]
    have hre2 : (-z-2 : ℂ).re = -z.re - 2 := by
      simp [Complex.sub_re, Complex.neg_re]
    rw [hre2]
    have hb1 : t ^ (-z.re - 2) ≤ t ^ (-ρ - 2) :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
    have hb2 : Real.log t ≤ t ^ δ / δ := by
      have h4 : Real.log (t ^ δ) ≤ t ^ δ - 1 :=
        Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht0 _)
      rw [Real.log_rpow ht0] at h4
      have h5 : δ * Real.log t ≤ t ^ δ := by linarith
      rw [le_div_iff₀ hδ0, mul_comm]
      exact h5
    calc |sawInt t| * (Real.log t * t ^ (-z.re - 2))
        ≤ (1/8) * (Real.log t * t ^ (-z.re - 2)) := by
          apply mul_le_mul_of_nonneg_right (abs_sawInt_le t)
          exact mul_nonneg hlogpos (Real.rpow_nonneg ht0.le _)
      _ ≤ (1/8) * ((t ^ δ / δ) * t ^ (-ρ - 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply mul_le_mul hb2 hb1 (Real.rpow_nonneg ht0.le _)
          positivity
      _ = (1/(8*δ)) * t ^ (δ - ρ - 2) := by
          rw [show δ - ρ - 2 = δ + (-ρ - 2) from by ring, Real.rpow_add ht0]
          field_simp
  · -- the bound is integrable
    exact (integrableOn_Ioi_rpow_of_lt hexp zero_lt_one).const_mul _
  · -- differentiability in the parameter, for each `t > 1`
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    intro z _
    have ht1 : (1:ℝ) < t := ht
    have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht1
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht0
    have h1 : HasDerivAt (fun w : ℂ => -w-2) (-1) z := by
      have := ((hasDerivAt_id z).neg).sub_const (2:ℂ)
      simpa using this
    have h2 : HasDerivAt (fun w : ℂ => (t : ℂ) ^ w)
        ((t : ℂ) ^ (-z-2) * Complex.log (t : ℂ) * 1) (-z-2) :=
      (hasDerivAt_id (-z-2)).const_cpow (Or.inl htC)
    have h3 := (h2.comp z h1)
    have h4 := h3.const_mul ((sawInt t : ℝ) : ℂ)
    have hlog : Complex.log ((t : ℝ) : ℂ) = ((Real.log t : ℝ) : ℂ) :=
      (Complex.ofReal_log ht0.le).symm
    have h5 : HasDerivAt (fun w : ℂ => ((sawInt t : ℝ) : ℂ) * (t : ℂ) ^ (-w-2))
        (((sawInt t : ℝ) : ℂ) * ((t : ℂ) ^ (-z-2) * Complex.log ((t : ℝ) : ℂ) * 1 * -1))
        z := h4
    rw [hlog] at h5
    have hval : ((sawInt t : ℝ) : ℂ) * ((t : ℂ) ^ (-z-2) * ((Real.log t : ℝ) : ℂ) * 1 * -1)
        = ((sawInt t : ℝ) : ℂ) * (-((Real.log t : ℝ) : ℂ) * (t : ℂ) ^ (-z-2)) := by
      ring
    rw [hval] at h5
    exact h5

private lemma zeta0_eq_Kint {s : ℂ} (hs : -1 < s.re) :
    riemannZeta₀ s = 1/2 - s*(s+1)*Kint s := by
  set U : Set ℂ := {z : ℂ | -1 < z.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt (-1)).isPreconnected
  have h2U : (2:ℂ) ∈ U := by
    show (-1:ℝ) < (2:ℂ).re
    norm_num
  have hf : AnalyticOnNhd ℂ riemannZeta₀ U :=
    DifferentiableOn.analyticOnNhd differentiable_riemannZeta₀.differentiableOn hUopen
  have hg : AnalyticOnNhd ℂ (fun z => 1/2 - z*(z+1)*Kint z) U := by
    apply DifferentiableOn.analyticOnNhd _ hUopen
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.const_sub
    exact (differentiableAt_id.mul (differentiableAt_id.add_const 1)).mul
      (differentiableAt_Kint hz)
  have hev : riemannZeta₀ =ᶠ[𝓝 (2:ℂ)] (fun z => 1/2 - z*(z+1)*Kint z) := by
    have hopen2 : {z : ℂ | 1 < z.re} ∈ 𝓝 (2:ℂ) := by
      apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      norm_num
    filter_upwards [hopen2] with z hz
    have hz1 : z ≠ 1 := by
      intro h
      have h1 : (1:ℝ) < (1:ℂ).re := by rw [← h]; exact hz
      rw [Complex.one_re] at h1
      linarith
    have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
    have hzeta0 : riemannZeta₀ z = riemannZeta z - (z-1)⁻¹ := by
      rw [riemannZeta_eq_inv_sub_add hz1]
      ring
    rw [hzeta0, zeta_eq_sub_saw_integral hz, saw_integral_eq_sawInt hz]
    simp only [Kint]
    field_simp
    ring
  exact (hf.eqOn_of_preconnected_of_eventuallyEq hg hUpre h2U hev) hs

/-- **Uniform strip growth of `ζ₀`** (the elementary Euler–Maclaurin bound):
`‖ζ₀(z)‖ ≤ 1/2 + ‖z‖·‖z+1‖/4` for `Re z ≥ −1/2` — including `z = 1`. -/
lemma norm_riemannZeta₀_le {z : ℂ} (hz : -(1/2:ℝ) ≤ z.re) :
    ‖riemannZeta₀ z‖ ≤ 1/2 + ‖z‖ * ‖z+1‖ / 4 := by
  have h1 : -1 < z.re := by linarith
  rw [zeta0_eq_Kint h1]
  have hK : ‖Kint z‖ ≤ 1/4 := by
    have hb : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Ioi (1:ℝ))),
        ‖((sawInt t : ℝ) : ℂ) * (t : ℂ) ^ (-z-2)‖ ≤ (1/8) * t ^ (-(3/2) : ℝ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : (1:ℝ) < t := ht
      have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht1
      rw [norm_ofReal_mul_cpow ht0]
      have hre2 : (-z-2 : ℂ).re = -z.re - 2 := by
        simp [Complex.sub_re, Complex.neg_re]
      rw [hre2]
      have hb1 : t ^ (-z.re - 2) ≤ t ^ (-(3/2) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
      calc |sawInt t| * t ^ (-z.re - 2)
          ≤ (1/8) * t ^ (-z.re - 2) :=
            mul_le_mul_of_nonneg_right (abs_sawInt_le t) (Real.rpow_nonneg ht0.le _)
        _ ≤ (1/8) * t ^ (-(3/2) : ℝ) := by
            apply mul_le_mul_of_nonneg_left hb1 (by norm_num)
    have hint : MeasureTheory.Integrable (fun t : ℝ => (1/8 : ℝ) * t ^ (-(3/2) : ℝ))
        (MeasureTheory.volume.restrict (Ioi (1:ℝ))) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).const_mul _
    have h2 := MeasureTheory.norm_integral_le_of_norm_le hint hb
    have h3 : (∫ t in Ioi (1:ℝ), (1/8 : ℝ) * t ^ (-(3/2) : ℝ)) = 1/4 := by
      rw [MeasureTheory.integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) zero_lt_one]
      norm_num
    rw [Kint]
    calc ‖∫ t in Ioi (1:ℝ), ((sawInt t : ℝ) : ℂ) * (t : ℂ) ^ (-z-2)‖
        ≤ ∫ t in Ioi (1:ℝ), (1/8 : ℝ) * t ^ (-(3/2) : ℝ) := h2
      _ = 1/4 := h3
  have hhalf : ‖(1/2 : ℂ)‖ = 1/2 := by
    rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) from by norm_num, Complex.norm_real]
    norm_num
  calc ‖(1/2 : ℂ) - z*(z+1)*Kint z‖
      ≤ ‖(1/2 : ℂ)‖ + ‖z*(z+1)*Kint z‖ := norm_sub_le _ _
    _ = 1/2 + ‖z‖ * ‖z+1‖ * ‖Kint z‖ := by
        rw [hhalf, norm_mul, norm_mul]
    _ ≤ 1/2 + ‖z‖ * ‖z+1‖ * (1/4) := by
        have h4 : ‖z‖ * ‖z+1‖ * ‖Kint z‖ ≤ ‖z‖ * ‖z+1‖ * (1/4) :=
          mul_le_mul_of_nonneg_left hK (by positivity)
        linarith
    _ = 1/2 + ‖z‖ * ‖z+1‖ / 4 := by ring

end ZetaRep

/-! ### Helpers for the ζ Phragmén–Lindelöf (recreated: private in `LConvexity`) -/

section ZetaHelpers

private lemma exp_one_le_three : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le

private lemma exp_four_le : Real.exp 4 ≤ 81 := by
  have h1 : Real.exp 1 ≤ 3 := exp_one_le_three
  have h0 : (0:ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have h2 : Real.exp 1 * Real.exp 1 ≤ 9 := by nlinarith
  have h02 : (0:ℝ) ≤ Real.exp 1 * Real.exp 1 := by positivity
  have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  calc Real.exp 4 = Real.exp 1 * Real.exp 1 * (Real.exp 1 * Real.exp 1) := h4
    _ ≤ 9 * 9 := mul_le_mul h2 h2 h02 (by norm_num)
    _ = 81 := by norm_num

/-- `(1+|v|)·e^{−v²} ≤ 3`. -/
private lemma one_add_abs_mul_exp_neg_sq_le (v : ℝ) : (1 + |v|) * Real.exp (-v ^ 2) ≤ 3 := by
  have h1 : 1 + |v| ≤ Real.exp |v| := by
    have := Real.add_one_le_exp |v|; linarith
  have h2 : (1 + |v|) * Real.exp (-v ^ 2) ≤ Real.exp |v| * Real.exp (-v ^ 2) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have h3 : Real.exp |v| * Real.exp (-v ^ 2) = Real.exp (|v| + -v ^ 2) := by
    rw [← Real.exp_add]
  have h4 : |v| + -v ^ 2 ≤ 1 := by
    nlinarith [sq_abs v, sq_nonneg (|v| - 1/2)]
  calc (1 + |v|) * Real.exp (-v ^ 2) ≤ Real.exp (|v| + -v ^ 2) := by rw [← h3]; exact h2
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr h4
    _ ≤ 3 := exp_one_le_three

/-- Modulus of the Gaussian normalizer. -/
private lemma norm_exp_sq_sub (z w : ℂ) :
    ‖Complex.exp ((z - w) ^ 2)‖ = Real.exp ((z.re - w.re) ^ 2 - (z.im - w.im) ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  rw [sq, Complex.mul_re, Complex.sub_re, Complex.sub_im]
  ring

/-- Modulus of the power normalizer. -/
private lemma norm_exp_mul_ofReal (u : ℂ) (c : ℝ) :
    ‖Complex.exp (u * (c : ℂ))‖ = Real.exp (u.re * c) := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

/-- `2+|y| ≤ (2+|y₀|)·(1+|y−y₀|)`. -/
private lemma two_add_abs_le (y y₀ : ℝ) : 2 + |y| ≤ (2 + |y₀|) * (1 + |y - y₀|) := by
  have hy : y = y₀ + (y - y₀) := by ring
  have h1 : |y| ≤ |y₀| + |y - y₀| := by
    calc |y| = |y₀ + (y - y₀)| := by rw [← hy]
      _ ≤ |y₀| + |y - y₀| := abs_add_le _ _
  nlinarith [abs_nonneg y₀, abs_nonneg (y - y₀),
    mul_nonneg (abs_nonneg y₀) (abs_nonneg (y - y₀))]

/-- Cubic-in-`|Im|` bounds satisfy the double-exponential Phragmén–Lindelöf
growth condition (with `c = 1`). -/
private lemma isBigO_double_exp {P : ℝ} (hP : 1 ≤ P) {f : ℂ → ℂ} {S : Set ℂ}
    (hf : ∀ z ∈ S, ‖f z‖ ≤ P * (4 + |z.im|) ^ 3) :
    f =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 S]
      (fun z : ℂ => Real.exp ((Real.log P + 12) * Real.exp |z.im|)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  rw [Filter.eventually_inf_principal]
  apply Filter.Eventually.of_forall
  intro z hz
  rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine (hf z hz).trans ?_
  have hu0 : (0:ℝ) ≤ |z.im| := abs_nonneg _
  have hP0 : (0:ℝ) < P := by linarith
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg hP
  have h4u : (0:ℝ) < 4 + |z.im| := by linarith
  have hlog : Real.log (4 + |z.im|) ≤ 3 + |z.im| := by
    have := Real.log_le_sub_one_of_pos h4u
    linarith
  have hexpu : 1 ≤ Real.exp |z.im| := Real.one_le_exp hu0
  have huexp : |z.im| ≤ Real.exp |z.im| := by
    have := Real.add_one_le_exp |z.im|
    linarith
  have heq : P * (4 + |z.im|) ^ 3
      = Real.exp (Real.log P + 3 * Real.log (4 + |z.im|)) := by
    rw [Real.exp_add, Real.exp_log hP0]
    congr 1
    rw [show (3:ℝ) * Real.log (4 + |z.im|) = ((3:ℕ) : ℝ) * Real.log (4 + |z.im|) from
      by norm_num, ← Real.log_pow, Real.exp_log (by positivity)]
  rw [heq]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hlogP (sub_nonneg.mpr hexpu)]

end ZetaHelpers

/-! ### The ζ edges -/

section ZetaEdges

/-- Right edge for `ζ`: the mod-1 Dirichlet series bound. -/
private lemma norm_zeta_le_of_one_lt_re {z : ℂ} (hz : 1 < z.re) :
    ‖riemannZeta z‖ ≤ 1 + 1 / (z.re - 1) := by
  have h := norm_LFunction_le_of_one_lt_re (N := 1) (1 : DirichletCharacter ℂ 1) hz
  rwa [DirichletCharacter.LFunction_modOne_eq] at h

/-- Left edge for `ζ`: functional equation + the delivered interpolated Γ-factor
bound.  For `−1/2 ≤ Re z < 0`:
`‖ζ(z)‖ ≤ 12·(1+1/(−Re z))·(2+|Im z|)^{1/2−Re z}`. -/
private lemma norm_zeta_le_left_edge {z : ℂ} (h1 : -(1/2:ℝ) ≤ z.re) (h2 : z.re < 0) :
    ‖riemannZeta z‖ ≤ 12 * (1 + 1/(-z.re)) * (2 + |z.im|) ^ ((1:ℝ)/2 - z.re) := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at h2
    simp at h2
  -- functional equation at `s := 1 − z`
  have hs1 : ∀ n : ℕ, (1 - z : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    linarith
  have hs2 : (1 - z : ℂ) ≠ 1 := by
    intro h
    apply hz0
    linear_combination -h
  have hFE := riemannZeta_one_sub hs1 hs2
  have hz' : (1 : ℂ) - (1 - z) = z := by ring
  rw [hz'] at hFE
  -- rewrite the trigonometric factor
  have hcos : Complex.cos (↑π * (1 - z) / 2) = Complex.sin (↑π * (z + (0:ℝ)) / 2) := by
    rw [show (↑π * (1 - z) / 2 : ℂ) = ↑π/2 - ↑π * (z + (0:ℝ))/2 from by push_cast; ring]
    exact Complex.cos_pi_div_two_sub _
  rw [hcos] at hFE
  -- take norms
  rw [hFE]
  have hnorm : ‖(2 : ℂ) * (2 * ↑π) ^ (-(1 - z)) * Complex.Gamma (1 - z) *
      Complex.sin (↑π * (z + (0:ℝ)) / 2) * riemannZeta (1 - z)‖
      = 2 * ‖(2 * (π:ℂ)) ^ (-(1 - z))‖ *
          ‖Complex.Gamma (1 - z) * Complex.sin (↑π * (z + (0:ℝ)) / 2)‖ *
          ‖riemannZeta (1 - z)‖ := by
    simp only [norm_mul, Complex.norm_ofNat]
    ring
  rw [hnorm]
  -- the three factors
  have hpi0 : (0:ℝ) < 2 * π := by positivity
  have h2pi : ‖(2 * (π:ℂ)) ^ (-(1 - z))‖ ≤ 1/6 := by
    have hbase : (2 * (π:ℂ)) = (((2 * π : ℝ)) : ℂ) := by push_cast; ring
    rw [hbase, Complex.norm_cpow_eq_rpow_re_of_pos hpi0]
    have hre : (-(1 - z)).re = z.re - 1 := by
      simp [Complex.sub_re]
    rw [hre]
    have hexple : z.re - 1 ≤ -1 := by linarith
    have h6pi : (6:ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
    calc (2*π) ^ (z.re - 1) ≤ (2*π) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hexple
      _ = 1/(2*π) := by
          rw [Real.rpow_neg_one]
          ring
      _ ≤ 1/6 := by
          apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) h6pi
  have hΓ := norm_Gamma_one_sub_mul_sin_interp (0:ℝ) h1 h2.le
  have hζ : ‖riemannZeta (1 - z)‖ ≤ 1 + 1/(-z.re) := by
    have hre1 : (1:ℝ) < (1 - z).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have h := norm_zeta_le_of_one_lt_re hre1
    have hre2 : (1 - z).re - 1 = -z.re := by
      simp [Complex.sub_re, Complex.one_re]
    rwa [hre2] at h
  -- assemble
  have hq0 : (0:ℝ) ≤ (2 + |z.im|) ^ ((1:ℝ)/2 - z.re) :=
    Real.rpow_nonneg (by linarith [abs_nonneg z.im]) _
  have hL0 : (0:ℝ) ≤ 1 + 1/(-z.re) := by
    have : (0:ℝ) < -z.re := by linarith
    positivity
  calc 2 * ‖(2 * (π:ℂ)) ^ (-(1 - z))‖ *
      ‖Complex.Gamma (1 - z) * Complex.sin (↑π * (z + (0:ℝ)) / 2)‖ *
      ‖riemannZeta (1 - z)‖
      ≤ 2 * (1/6) * (34 * (2 + |z.im|) ^ ((1:ℝ)/2 - z.re)) * (1 + 1/(-z.re)) := by
        apply mul_le_mul _ hζ (norm_nonneg _) (by positivity)
        apply mul_le_mul _ hΓ (norm_nonneg _) (by positivity)
        apply mul_le_mul_of_nonneg_left h2pi (by norm_num)
    _ = (34/3) * (1 + 1/(-z.re)) * (2 + |z.im|) ^ ((1:ℝ)/2 - z.re) := by ring
    _ ≤ 12 * (1 + 1/(-z.re)) * (2 + |z.im|) ^ ((1:ℝ)/2 - z.re) := by
        apply mul_le_mul_of_nonneg_right _ hq0
        apply mul_le_mul_of_nonneg_right (by norm_num) hL0

end ZetaEdges

/-! ### The ζ convexity bound -/

section ZetaConvexity

/-- **Phragmén–Lindelöf for `ζ₀`** (the entire completion `ζ(s) − 1/(s−1)`):
for `1/200 ≤ σ ≤ 2`,
`‖ζ₀(s)‖ ≤ 200000·(|t|+2)^{max((1−σ)/2,0)}·log(|t|+3)`. -/
theorem norm_riemannZeta₀_le_convexity {s : ℂ}
    (hσ1 : 1/200 ≤ s.re) (hσ2 : s.re ≤ 2) :
    ‖riemannZeta₀ s‖
      ≤ 200000 * (|s.im| + 2) ^ (max ((1 - s.re)/2) 0) * Real.log (|s.im| + 3) := by
  set D : ℝ := |s.im| + 2 with hDdef
  set M : ℝ := |s.im| + 3 with hMdef
  have habs : (0:ℝ) ≤ |s.im| := abs_nonneg _
  have hD1 : (1:ℝ) ≤ D := by rw [hDdef]; linarith
  have hD0 : (0:ℝ) < D := by linarith
  have hM3 : (3:ℝ) ≤ M := by rw [hMdef]; linarith
  have hM0 : (0:ℝ) < M := by linarith
  have hDM : D ≤ M := by rw [hDdef, hMdef]; linarith
  have hlogM1 : (1:ℝ) ≤ Real.log M := by
    rw [Real.le_log_iff_exp_le hM0]
    linarith [exp_one_le_three]
  set L : ℝ := 1 + Real.log M with hLdef
  have hL2 : (2:ℝ) ≤ L := by rw [hLdef]; linarith
  have hL0 : (0:ℝ) < L := by linarith
  have h1L0 : (0:ℝ) < 1 + L := by linarith
  have hiL : (1:ℝ)/L ≤ 1/2 := by
    rw [div_le_iff₀ hL0]
    linarith
  have hiL0 : (0:ℝ) < 1/L := by positivity
  have hlogD : Real.log D ≤ L := by
    have h := Real.log_le_log hD0 hDM
    rw [hLdef]
    linarith
  have hD3 : D ^ ((1:ℝ)/L) ≤ 3 := by
    rw [Real.rpow_def_of_pos hD0]
    calc Real.exp (Real.log D * (1/L)) ≤ Real.exp 1 := by
          apply Real.exp_le_exp.mpr
          rw [mul_one_div, div_le_one hL0]
          exact hlogD
      _ ≤ 3 := exp_one_le_three
  have hmaxE0 : (0:ℝ) ≤ max ((1 - s.re)/2) 0 := le_max_right _ _
  have hDmax0 : (0:ℝ) ≤ D ^ (max ((1 - s.re)/2) 0) := Real.rpow_nonneg hD0.le _
  have hDmax1 : (1:ℝ) ≤ D ^ (max ((1 - s.re)/2) 0) := Real.one_le_rpow hD1 hmaxE0
  set σR : ℝ := 1 + 1/L with hσRdef
  have hσR1 : 1 < σR := by rw [hσRdef]; linarith
  have hσR32 : σR ≤ 3/2 := by rw [hσRdef]; linarith
  set σL : ℝ := -(1/L) with hσLdef
  have hσLhalf : -(1/2 : ℝ) ≤ σL := by rw [hσLdef]; linarith
  have hσL0 : σL < 0 := by rw [hσLdef]; linarith
  set W : ℝ := σR - σL with hWdef
  have hW : W = 1 + 2/L := by
    rw [hWdef, hσRdef, hσLdef]
    ring
  have hiL2 : (2:ℝ)/L ≤ 1 := by
    rw [div_le_iff₀ hL0]
    linarith
  have hW1 : 1 ≤ W := by
    have h2L0 : (0:ℝ) < 2/L := div_pos two_pos hL0
    rw [hW]
    linarith
  have hW2 : W ≤ 2 := by rw [hW]; linarith
  have hW0 : (0:ℝ) < W := by linarith
  have h1L3logM : 1 + L ≤ 3 * Real.log M := by rw [hLdef]; linarith
  -- pole-part bounds used on both edges
  have hpole : ∀ z : ℂ, z.re ≠ 1 → riemannZeta₀ z = riemannZeta z - (z-1)⁻¹ := by
    intro z hz
    have hz1 : z ≠ 1 := by
      intro h
      apply hz
      rw [h, Complex.one_re]
    rw [riemannZeta_eq_inv_sub_add hz1]
    ring
  rcases le_or_gt s.re σR with hcase | hcase
  · -- Phragmén–Lindelöf branch: `1/200 ≤ σ ≤ σR`
    set b : ℝ := 117 * D ^ ((1:ℝ)/2) with hbdef
    have hDhalf1 : (1:ℝ) ≤ D ^ ((1:ℝ)/2) := Real.one_le_rpow hD1 (by norm_num)
    have hDhalf0 : (0:ℝ) < D ^ ((1:ℝ)/2) := by linarith
    have hb1 : (1:ℝ) ≤ b := by rw [hbdef]; nlinarith
    have hb0 : (0:ℝ) < b := by linarith
    set c : ℝ := Real.log b / W with hcdef
    have hc0 : (0:ℝ) ≤ c := div_nonneg (Real.log_nonneg hb1) hW0.le
    set K : ℂ → ℂ := fun z =>
      riemannZeta₀ z * Complex.exp ((z - s) ^ 2) *
        Complex.exp ((z - (σR : ℂ)) * (c : ℂ)) with hKdef
    have hnormK : ∀ z : ℂ, ‖K z‖ = ‖riemannZeta₀ z‖ *
        Real.exp ((z.re - s.re) ^ 2 - (z.im - s.im) ^ 2) *
        Real.exp ((z.re - σR) * c) := by
      intro z
      rw [hKdef]
      simp only []
      rw [norm_mul, norm_mul, norm_exp_sq_sub, norm_exp_mul_ofReal,
        Complex.sub_re, Complex.ofReal_re]
    -- right boundary
    have hright : ∀ z : ℂ, z.re = σR → ‖K z‖ ≤ 162 * (1 + L) := by
      intro z hz
      rw [hnormK z, hz, sub_self, zero_mul, Real.exp_zero, mul_one]
      have hζ0z : ‖riemannZeta₀ z‖ ≤ 1 + 2*L := by
        rw [hpole z (by rw [hz]; linarith)]
        have hζz : ‖riemannZeta z‖ ≤ 1 + L := by
          have h := norm_zeta_le_of_one_lt_re (z := z) (by rw [hz]; exact hσR1)
          rw [hz, show σR - 1 = 1/L from by rw [hσRdef]; ring, one_div_one_div] at h
          exact h
        have hinv : ‖(z-1)⁻¹‖ ≤ L := by
          rw [norm_inv]
          have hre : (z-1).re = 1/L := by
            rw [Complex.sub_re, Complex.one_re, hz, hσRdef]
            ring
          have hn : 1/L ≤ ‖z-1‖ := by
            calc 1/L = (z-1).re := hre.symm
              _ ≤ |(z-1).re| := le_abs_self _
              _ ≤ ‖z-1‖ := Complex.abs_re_le_norm _
          have hn0 : (0:ℝ) < ‖z-1‖ := lt_of_lt_of_le hiL0 hn
          rw [inv_le_comm₀ hn0 hL0] at *
          · calc L⁻¹ = 1/L := (one_div L).symm
              _ ≤ ‖z-1‖ := hn
        calc ‖riemannZeta z - (z-1)⁻¹‖ ≤ ‖riemannZeta z‖ + ‖(z-1)⁻¹‖ := norm_sub_le _ _
          _ ≤ (1 + L) + L := add_le_add hζz hinv
          _ = 1 + 2*L := by ring
      have hgauss : Real.exp ((σR - s.re) ^ 2 - (z.im - s.im) ^ 2) ≤ 81 := by
        calc Real.exp ((σR - s.re) ^ 2 - (z.im - s.im) ^ 2) ≤ Real.exp 4 := by
              apply Real.exp_le_exp.mpr
              nlinarith [sq_nonneg (z.im - s.im)]
          _ ≤ 81 := exp_four_le
      calc ‖riemannZeta₀ z‖ * Real.exp ((σR - s.re) ^ 2 - (z.im - s.im) ^ 2)
          ≤ (1 + 2*L) * 81 := by
            apply mul_le_mul hζ0z hgauss (Real.exp_pos _).le
            linarith
        _ ≤ 162 * (1 + L) := by nlinarith
    -- left boundary
    have hcancel : 117 * D ^ ((1:ℝ)/2) * b⁻¹ = 1 := by
      rw [← hbdef]
      exact mul_inv_cancel₀ hb0.ne'
    have hleft : ∀ z : ℂ, z.re = σL → ‖K z‖ ≤ 162 * (1 + L) := by
      intro z hz
      rw [hnormK z, hz]
      have hnorm2 : Real.exp ((σL - σR) * c) = b⁻¹ := by
        have h1 : (σL - σR) * c = -Real.log b := by
          rw [hcdef, show σL - σR = -W from by rw [hWdef]; ring]
          field_simp
        rw [h1, Real.exp_neg, Real.exp_log hb0]
      rw [hnorm2]
      -- the ζ₀ bound with base split
      have hζ0b : ‖riemannZeta₀ z‖
          ≤ 13 * (1 + L) * (D ^ ((1:ℝ)/2) * D ^ ((1:ℝ)/L) * (1 + |z.im - s.im|)) := by
        have hq1 : (1:ℝ) ≤ (2 + |z.im|) ^ ((1:ℝ)/2 - σL) := by
          apply Real.one_le_rpow (by linarith [abs_nonneg z.im])
          rw [hσLdef]
          linarith [hiL0]
        have hζz : ‖riemannZeta z‖ ≤ 12 * (1 + L) * (2 + |z.im|) ^ ((1:ℝ)/2 - σL) := by
          have h := norm_zeta_le_left_edge (z := z)
            (by rw [hz]; exact hσLhalf) (by rw [hz]; exact hσL0)
          rw [hz, show 1 + 1/(-σL) = 1 + L from by
            rw [hσLdef, neg_neg, one_div_one_div, hLdef]] at h
          exact h
        have hinv : ‖(z-1)⁻¹‖ ≤ 1 := by
          rw [norm_inv]
          have hre : (z-1).re = σL - 1 := by
            rw [Complex.sub_re, Complex.one_re, hz]
          have hn : (1:ℝ) ≤ ‖z-1‖ := by
            calc (1:ℝ) ≤ 1 - σL := by linarith
              _ = |(z-1).re| := by
                  rw [hre, abs_of_nonpos (by linarith)]
                  ring
              _ ≤ ‖z-1‖ := Complex.abs_re_le_norm _
          exact inv_le_one_of_one_le₀ hn
        have hζ0z : ‖riemannZeta₀ z‖ ≤ 13 * (1 + L) * (2 + |z.im|) ^ ((1:ℝ)/2 - σL) := by
          rw [hpole z (by rw [hz]; linarith)]
          calc ‖riemannZeta z - (z-1)⁻¹‖ ≤ ‖riemannZeta z‖ + ‖(z-1)⁻¹‖ := norm_sub_le _ _
            _ ≤ 12 * (1 + L) * (2 + |z.im|) ^ ((1:ℝ)/2 - σL) + 1 := add_le_add hζz hinv
            _ ≤ 12 * (1 + L) * (2 + |z.im|) ^ ((1:ℝ)/2 - σL)
                + (1 + L) * (2 + |z.im|) ^ ((1:ℝ)/2 - σL) := by
                nlinarith [hq1, h1L0]
            _ = 13 * (1 + L) * (2 + |z.im|) ^ ((1:ℝ)/2 - σL) := by ring
        have hE : (1:ℝ)/2 - σL = 1/2 + 1/L := by rw [hσLdef]; ring
        have hbase : (2 + |z.im|) ^ ((1:ℝ)/2 - σL)
            ≤ D ^ ((1:ℝ)/2) * D ^ ((1:ℝ)/L) * (1 + |z.im - s.im|) := by
          have hstep1 : 2 + |z.im| ≤ D * (1 + |z.im - s.im|) := by
            calc 2 + |z.im| ≤ (2 + |s.im|) * (1 + |z.im - s.im|) := two_add_abs_le z.im s.im
              _ = D * (1 + |z.im - s.im|) := by rw [hDdef]; ring
          have hexp0 : (0:ℝ) ≤ (1:ℝ)/2 - σL := by rw [hE]; positivity
          have hexple : (1:ℝ)/2 - σL ≤ 1 := by rw [hE]; linarith
          calc (2 + |z.im|) ^ ((1:ℝ)/2 - σL)
              ≤ (D * (1 + |z.im - s.im|)) ^ ((1:ℝ)/2 - σL) :=
                Real.rpow_le_rpow (by positivity) hstep1 hexp0
            _ = D ^ ((1:ℝ)/2 - σL) * (1 + |z.im - s.im|) ^ ((1:ℝ)/2 - σL) :=
                Real.mul_rpow hD0.le (by positivity)
            _ ≤ D ^ ((1:ℝ)/2 - σL) * (1 + |z.im - s.im|) := by
                have h1v : (1:ℝ) ≤ 1 + |z.im - s.im| := by
                  linarith [abs_nonneg (z.im - s.im)]
                have h2v : (1 + |z.im - s.im|) ^ ((1:ℝ)/2 - σL)
                    ≤ (1 + |z.im - s.im|) ^ (1:ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le h1v hexple
                rw [Real.rpow_one] at h2v
                exact mul_le_mul_of_nonneg_left h2v (Real.rpow_nonneg hD0.le _)
            _ = D ^ ((1:ℝ)/2) * D ^ ((1:ℝ)/L) * (1 + |z.im - s.im|) := by
                rw [hE, Real.rpow_add hD0]
        calc ‖riemannZeta₀ z‖
            ≤ 13 * (1 + L) * ((2 + |z.im|) ^ ((1:ℝ)/2 - σL)) := hζ0z
          _ ≤ 13 * (1 + L) * (D ^ ((1:ℝ)/2) * D ^ ((1:ℝ)/L) * (1 + |z.im - s.im|)) := by
              apply mul_le_mul_of_nonneg_left hbase
              nlinarith
      have hgauss : Real.exp ((σL - s.re) ^ 2 - (z.im - s.im) ^ 2)
          ≤ 81 * Real.exp (-(z.im - s.im) ^ 2) := by
        rw [show (σL - s.re) ^ 2 - (z.im - s.im) ^ 2
            = (σL - s.re) ^ 2 + -(z.im - s.im) ^ 2 from by ring, Real.exp_add]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        calc Real.exp ((σL - s.re) ^ 2) ≤ Real.exp 4 := by
              apply Real.exp_le_exp.mpr
              nlinarith
          _ ≤ 81 := exp_four_le
      have hA0 : (0:ℝ) ≤ 13 * 81 * (1 + L) * D ^ ((1:ℝ)/2) := by
        nlinarith
      calc ‖riemannZeta₀ z‖ *
          Real.exp ((σL - s.re) ^ 2 - (z.im - s.im) ^ 2) * b⁻¹
          ≤ (13 * (1 + L) * (D ^ ((1:ℝ)/2) * D ^ ((1:ℝ)/L) * (1 + |z.im - s.im|))) *
              (81 * Real.exp (-(z.im - s.im) ^ 2)) * b⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hb0.le)
            apply mul_le_mul hζ0b hgauss (Real.exp_pos _).le
            have h0a : (0:ℝ) ≤ D ^ ((1:ℝ)/L) := Real.rpow_nonneg hD0.le _
            have h0b : (0:ℝ) ≤ 1 + |z.im - s.im| := by
              linarith [abs_nonneg (z.im - s.im)]
            nlinarith [hDhalf0.le, mul_nonneg (mul_nonneg hDhalf0.le h0a) h0b]
        _ = 13 * 81 * (1 + L) * D ^ ((1:ℝ)/2) * (D ^ ((1:ℝ)/L)) *
              ((1 + |z.im - s.im|) * Real.exp (-(z.im - s.im) ^ 2)) * b⁻¹ := by ring
        _ ≤ 13 * 81 * (1 + L) * D ^ ((1:ℝ)/2) * 3 * 3 * b⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hb0.le)
            apply mul_le_mul (mul_le_mul_of_nonneg_left hD3 hA0)
              (one_add_abs_mul_exp_neg_sq_le _) (by positivity)
            nlinarith
        _ = 81 * (1 + L) * (117 * D ^ ((1:ℝ)/2) * b⁻¹) := by ring
        _ = 81 * (1 + L) := by rw [hcancel, mul_one]
        _ ≤ 162 * (1 + L) := by nlinarith
    -- growth condition
    have hgrowth : ∀ z ∈ Complex.re ⁻¹' (Set.Ioo σL σR),
        ‖K z‖ ≤ (81 : ℝ) * (4 + |z.im|) ^ 3 := by
      intro z hz
      have hz1 : σL < z.re := hz.1
      have hz2 : z.re < σR := hz.2
      rw [hnormK z]
      have hζ0z : ‖riemannZeta₀ z‖ ≤ (4 + |z.im|) ^ 3 := by
        have h := norm_riemannZeta₀_le (z := z) (by linarith)
        have hz3 : ‖z‖ ≤ 4 + |z.im| := by
          have h1 := Complex.norm_le_abs_re_add_abs_im z
          have h2 : |z.re| ≤ 2 := by
            rw [abs_le]
            constructor <;> linarith
          linarith
        have hz4 : ‖z+1‖ ≤ 4 + |z.im| := by
          have h1 := Complex.norm_le_abs_re_add_abs_im (z+1)
          have h2 : |(z+1).re| ≤ 3 := by
            rw [Complex.add_re, Complex.one_re, abs_le]
            constructor <;> linarith
          have h3 : (z+1).im = z.im := by
            rw [Complex.add_im, Complex.one_im, add_zero]
          rw [h3] at h1
          linarith
        have h4u : (0:ℝ) < 4 + |z.im| := by positivity
        have hsq : ‖z‖ * ‖z+1‖ ≤ (4 + |z.im|)^2 := by
          calc ‖z‖ * ‖z+1‖ ≤ (4 + |z.im|) * (4 + |z.im|) :=
                mul_le_mul hz3 hz4 (norm_nonneg _) h4u.le
            _ = (4 + |z.im|)^2 := (sq _).symm
        have hcube : (4 + |z.im|)^2 ≤ (4 + |z.im|)^3 := by
          have h1 : (1:ℝ) ≤ 4 + |z.im| := by linarith [abs_nonneg z.im]
          calc (4 + |z.im|)^2 = (4 + |z.im|)^2 * 1 := (mul_one _).symm
            _ ≤ (4 + |z.im|)^2 * (4 + |z.im|) := by nlinarith
            _ = (4 + |z.im|)^3 := by ring
        calc ‖riemannZeta₀ z‖ ≤ 1/2 + ‖z‖ * ‖z+1‖ / 4 := h
          _ ≤ 1/2 + (4 + |z.im|)^2 / 4 := by linarith
          _ ≤ (4 + |z.im|)^2 := by nlinarith [sq_nonneg (4 + |z.im|), h4u]
          _ ≤ (4 + |z.im|)^3 := hcube
      have hgauss : Real.exp ((z.re - s.re) ^ 2 - (z.im - s.im) ^ 2) ≤ 81 := by
        calc Real.exp ((z.re - s.re) ^ 2 - (z.im - s.im) ^ 2) ≤ Real.exp 4 := by
              apply Real.exp_le_exp.mpr
              nlinarith [sq_nonneg (z.im - s.im)]
          _ ≤ 81 := exp_four_le
      have hnorm1 : Real.exp ((z.re - σR) * c) ≤ 1 := by
        rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
        apply Real.exp_le_exp.mpr
        exact mul_nonpos_iff.mpr (Or.inr ⟨by linarith, hc0⟩)
      calc ‖riemannZeta₀ z‖ *
          Real.exp ((z.re - s.re) ^ 2 - (z.im - s.im) ^ 2) *
          Real.exp ((z.re - σR) * c)
          ≤ ((4 + |z.im|) ^ 3) * 81 * 1 := by
            apply mul_le_mul _ hnorm1 (Real.exp_pos _).le (by positivity)
            exact mul_le_mul hζ0z hgauss (Real.exp_pos _).le (by positivity)
        _ = 81 * (4 + |z.im|) ^ 3 := by ring
    -- Phragmén–Lindelöf
    have main : ‖K s‖ ≤ 162 * (1 + L) := by
      apply PhragmenLindelof.vertical_strip (a := σL) (b := σR) (C := 162 * (1 + L))
      · have hKd : Differentiable ℂ K := by
          apply Differentiable.mul
          · apply Differentiable.mul
            · exact differentiable_riemannZeta₀
            · apply Complex.differentiable_exp.comp
              fun_prop
          · apply Complex.differentiable_exp.comp
            fun_prop
        exact hKd.diffContOnCl
      · refine ⟨1, ?_, Real.log 81 + 12, ?_⟩
        · rw [← hWdef, lt_div_iff₀ hW0]
          nlinarith [Real.pi_gt_three]
        · simpa only [one_mul] using isBigO_double_exp (by norm_num : (1:ℝ) ≤ 81) hgrowth
      · exact hleft
      · exact hright
      · linarith
      · exact hcase
    -- unwind at `s`
    have hKs : ‖K s‖ = ‖riemannZeta₀ s‖ * Real.exp ((s.re - σR) * c) := by
      rw [hnormK s, show (s.re - s.re) ^ 2 - (s.im - s.im) ^ 2 = 0 from by ring,
        Real.exp_zero, mul_one]
    have hζ0s : ‖riemannZeta₀ s‖ = ‖K s‖ * Real.exp ((σR - s.re) * c) := by
      rw [hKs, mul_assoc, ← Real.exp_add,
        show (s.re - σR) * c + (σR - s.re) * c = 0 from by ring,
        Real.exp_zero, mul_one]
    set θ : ℝ := (σR - s.re) / W with hθdef
    have hθ0 : (0:ℝ) ≤ θ := div_nonneg (by linarith) hW0.le
    have hθ1 : θ ≤ 1 := by
      rw [hθdef, div_le_one hW0]
      linarith
    have hbθ : Real.exp ((σR - s.re) * c) = b ^ θ := by
      rw [Real.rpow_def_of_pos hb0]
      congr 1
      rw [hcdef, hθdef]
      ring
    have hθhalf : θ/2 ≤ max ((1 - s.re)/2) 0 + 1/L := by
      have hexpand : θ/2 = (σR - s.re) / (W * 2) := by
        rw [hθdef, div_div]
      rcases le_total s.re 1 with hσle | hσge
      · rw [max_eq_left (by linarith : (0:ℝ) ≤ (1 - s.re)/2), hexpand,
          div_le_iff₀ (by linarith : (0:ℝ) < W * 2), hσRdef, hW]
        nlinarith [mul_nonneg hiL0.le (by linarith : (0:ℝ) ≤ 1 - s.re),
          sq_nonneg (1/L)]
      · rw [max_eq_right (by linarith : (1 - s.re)/2 ≤ 0), zero_add, hexpand,
          div_le_iff₀ (by linarith : (0:ℝ) < W * 2), hσRdef, hW]
        nlinarith [sq_nonneg (1/L)]
    have hbθle : b ^ θ ≤ 351 * D ^ (max ((1 - s.re)/2) 0) := by
      have h117 : (117:ℝ) ^ θ ≤ 117 := by
        calc (117:ℝ) ^ θ ≤ (117:ℝ) ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
          _ = 117 := Real.rpow_one _
      have hsplit : b ^ θ = 117 ^ θ * (D ^ ((1:ℝ)/2)) ^ θ := by
        rw [hbdef, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hD0.le _)]
      have hDθ : (D ^ ((1:ℝ)/2)) ^ θ = D ^ (θ/2) := by
        rw [← Real.rpow_mul hD0.le]
        congr 1
        ring
      calc b ^ θ = 117 ^ θ * (D ^ ((1:ℝ)/2)) ^ θ := hsplit
        _ ≤ 117 * D ^ (θ/2) := by
            rw [hDθ]
            exact mul_le_mul_of_nonneg_right h117 (Real.rpow_nonneg hD0.le _)
        _ ≤ 117 * D ^ (max ((1 - s.re)/2) 0 + 1/L) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact Real.rpow_le_rpow_of_exponent_le hD1 hθhalf
        _ = 117 * (D ^ (max ((1 - s.re)/2) 0) * D ^ ((1:ℝ)/L)) := by
            rw [Real.rpow_add hD0]
        _ ≤ 117 * (D ^ (max ((1 - s.re)/2) 0) * 3) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_left hD3 hDmax0
        _ = 351 * D ^ (max ((1 - s.re)/2) 0) := by ring
    calc ‖riemannZeta₀ s‖
        = ‖K s‖ * Real.exp ((σR - s.re) * c) := hζ0s
      _ ≤ (162 * (1 + L)) * (351 * D ^ (max ((1 - s.re)/2) 0)) := by
          apply mul_le_mul main _ (Real.exp_pos _).le (by positivity)
          rw [hbθ]
          exact hbθle
      _ = 56862 * (1 + L) * D ^ (max ((1 - s.re)/2) 0) := by ring
      _ ≤ 56862 * (3 * Real.log M) * D ^ (max ((1 - s.re)/2) 0) := by
          apply mul_le_mul_of_nonneg_right _ hDmax0
          apply mul_le_mul_of_nonneg_left h1L3logM (by norm_num)
      _ = 170586 * D ^ (max ((1 - s.re)/2) 0) * Real.log M := by ring
      _ ≤ 200000 * D ^ (max ((1 - s.re)/2) 0) * Real.log M := by
          nlinarith [mul_nonneg hDmax0 (by linarith : (0:ℝ) ≤ Real.log M)]
  · -- direct branch: `σR < σ ≤ 2`
    have hσgt1 : 1 < s.re := lt_trans hσR1 hcase
    have hζ0s : ‖riemannZeta₀ s‖ ≤ 1 + 2*L := by
      rw [hpole s (by linarith)]
      have hζs : ‖riemannZeta s‖ ≤ 1 + L := by
        have h := norm_zeta_le_of_one_lt_re hσgt1
        have h2 : 1/(s.re - 1) ≤ L := by
          rw [div_le_iff₀ (by linarith : (0:ℝ) < s.re - 1)]
          have h3 : 1/L ≤ s.re - 1 := by
            have h4 : σR - 1 = 1/L := by rw [hσRdef]; ring
            linarith
          calc (1:ℝ) = L * (1/L) := by field_simp
            _ ≤ L * (s.re - 1) := mul_le_mul_of_nonneg_left h3 hL0.le
        linarith
      have hinv : ‖(s-1)⁻¹‖ ≤ L := by
        rw [norm_inv]
        have hre : 1/L ≤ (s-1).re := by
          rw [Complex.sub_re, Complex.one_re]
          have h4 : σR - 1 = 1/L := by rw [hσRdef]; ring
          linarith
        have hn : 1/L ≤ ‖s-1‖ := by
          calc 1/L ≤ (s-1).re := hre
            _ ≤ |(s-1).re| := le_abs_self _
            _ ≤ ‖s-1‖ := Complex.abs_re_le_norm _
        have hn0 : (0:ℝ) < ‖s-1‖ := lt_of_lt_of_le hiL0 hn
        rw [inv_le_comm₀ hn0 hL0]
        calc L⁻¹ = 1/L := (one_div L).symm
          _ ≤ ‖s-1‖ := hn
      calc ‖riemannZeta s - (s-1)⁻¹‖ ≤ ‖riemannZeta s‖ + ‖(s-1)⁻¹‖ := norm_sub_le _ _
        _ ≤ (1 + L) + L := add_le_add hζs hinv
        _ = 1 + 2*L := by ring
    have hlogm0 : (0:ℝ) ≤ Real.log M := by linarith
    calc ‖riemannZeta₀ s‖ ≤ 1 + 2*L := hζ0s
      _ ≤ 6 * Real.log M := by rw [hLdef]; linarith
      _ ≤ 200000 * (D ^ (max ((1 - s.re)/2) 0) * Real.log M) := by nlinarith
      _ = 200000 * D ^ (max ((1 - s.re)/2) 0) * Real.log M := by ring

/-- **I1, ζ variant (frozen shape, Z0b §2 and §12.1).**  For `1/200 ≤ σ ≤ 2`:
`‖ζ(s)‖ ≤ C_cx·(|t|+2)^{max((1−σ)/2,0)}·log(|t|+3) + C_cx/‖s−1‖` with
`C_cx = 200000`.  No `s ≠ 1` hypothesis: at `s = 1` Mathlib's value
`ζ(1) = (γ − log 4π)/2` satisfies the bound outright. -/
theorem norm_riemannZeta_le_convexity {s : ℂ} (hσ1 : 1/200 ≤ s.re) (hσ2 : s.re ≤ 2) :
    ‖riemannZeta s‖
      ≤ 200000 * (|s.im| + 2) ^ (max ((1 - s.re)/2) 0) * Real.log (|s.im| + 3)
        + 200000 / ‖s - 1‖ := by
  rcases eq_or_ne s 1 with rfl | hs1
  · -- the point `s = 1`
    have hLHS : ‖riemannZeta 1‖ ≤ 8 := by
      have hlogC : Complex.log (4 * (π:ℂ)) = ((Real.log (4*π) : ℝ) : ℂ) := by
        rw [show (4 * (π:ℂ)) = ((4*π : ℝ) : ℂ) from by push_cast; ring]
        exact (Complex.ofReal_log (by positivity)).symm
      rw [riemannZeta_one, hlogC, ← Complex.ofReal_sub, norm_div, Complex.norm_real,
        Real.norm_eq_abs]
      have hγu : Real.eulerMascheroniConstant < 2/3 :=
        Real.eulerMascheroniConstant_lt_two_thirds
      have hγl : (1:ℝ)/2 < Real.eulerMascheroniConstant :=
        Real.one_half_lt_eulerMascheroniConstant
      have hπ4 : π ≤ 4 := Real.pi_le_four
      have hπ3 : 3 < π := Real.pi_gt_three
      have hl0 : (0:ℝ) ≤ Real.log (4*π) := Real.log_nonneg (by nlinarith)
      have hlu : Real.log (4*π) ≤ 15 := by
        have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4*π by positivity)
        nlinarith
      have habs8 : |Real.eulerMascheroniConstant - Real.log (4*π)| ≤ 16 := by
        rw [abs_le]
        constructor <;> nlinarith
      have h2 : ‖(2:ℂ)‖ = 2 := by norm_num
      rw [h2]
      linarith
    have hRHS : (8:ℝ) ≤ 200000 * (|(1:ℂ).im| + 2) ^ (max ((1 - (1:ℂ).re)/2) 0)
        * Real.log (|(1:ℂ).im| + 3) + 200000 / ‖(1:ℂ) - 1‖ := by
      simp only [Complex.one_im, Complex.one_re, abs_zero, zero_add]
      have hmax : max ((1 - (1:ℝ))/2) 0 = 0 := by norm_num
      rw [hmax, Real.rpow_zero, sub_self, norm_zero, div_zero, add_zero, mul_one]
      have hlog : (1:ℝ) ≤ Real.log 3 := by
        rw [Real.le_log_iff_exp_le (by norm_num)]
        linarith [exp_one_le_three]
      linarith
    linarith [hLHS, hRHS]
  · -- `s ≠ 1`: split off the pole
    have hd := norm_riemannZeta₀_le_convexity hσ1 hσ2
    have hs10 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hn0 : (0:ℝ) < ‖s - 1‖ := norm_pos_iff.mpr hs10
    calc ‖riemannZeta s‖ = ‖(s-1)⁻¹ + riemannZeta₀ s‖ := by
          rw [← riemannZeta_eq_inv_sub_add hs1]
      _ ≤ ‖(s-1)⁻¹‖ + ‖riemannZeta₀ s‖ := norm_add_le _ _
      _ = 1/‖s-1‖ + ‖riemannZeta₀ s‖ := by rw [norm_inv, one_div]
      _ ≤ 200000/‖s-1‖ + 200000 * (|s.im| + 2) ^ (max ((1 - s.re)/2) 0)
            * Real.log (|s.im| + 3) := by
          apply add_le_add _ hd
          gcongr
          norm_num
      _ = 200000 * (|s.im| + 2) ^ (max ((1 - s.re)/2) 0) * Real.log (|s.im| + 3)
            + 200000 / ‖s-1‖ := by ring

end ZetaConvexity

/-! ### The principal case and the master lemma -/

section Principal

variable {N : ℕ} [NeZero N]

/-- **I1, principal corollary (frozen shape, §2/§12.1).**  For the principal
character mod `N` and `s ≠ 1`, `1/200 ≤ σ ≤ 2`:
`‖L(s,χ₀)‖ ≤ 200000·2^{ω(N)}·((N(|t|+2))^{max((1−σ)/2,0)}·log(N(|t|+3)) + 1/‖s−1‖)`
(the ζ variant times the Euler-factor bound `∏_{p∣N}‖1−p^{−s}‖ ≤ 2^{ω(N)}`). -/
theorem norm_LFunctionTrivChar_le_convexity {s : ℂ} (hs : s ≠ 1)
    (hσ1 : 1/200 ≤ s.re) (hσ2 : s.re ≤ 2) :
    ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) s‖
      ≤ 200000 * 2 ^ N.primeFactors.card *
          (((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
              * Real.log ((N:ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have habs : (0:ℝ) ≤ |s.im| := abs_nonneg _
  -- the factorization
  have hfac := DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta (N := N) hs
  have hLerw : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) s
      = (∏ p ∈ N.primeFactors, (1 - (p:ℂ) ^ (-s))) * riemannZeta s := hfac
  rw [hLerw, norm_mul]
  -- the Euler-factor bound
  have hprod : ‖∏ p ∈ N.primeFactors, (1 - (p:ℂ) ^ (-s))‖ ≤ 2 ^ N.primeFactors.card := by
    have hcongr : (∏ p ∈ N.primeFactors, (1 - (p:ℂ) ^ (-s)))
        = ∏ p ∈ N.primeFactors, (1 - (1:ℂ) * (p:ℂ) ^ (-s)) := by
      apply Finset.prod_congr rfl
      intro p _
      rw [one_mul]
    rw [hcongr]
    apply norm_prod_euler_factors_le (by linarith : (0:ℝ) ≤ s.re)
    intro p _
    rw [norm_one]
  -- the ζ bound relaxed to modulus N
  have hmax0 : (0:ℝ) ≤ max ((1 - s.re)/2) 0 := le_max_right _ _
  have hDle : (|s.im| + 2) ^ (max ((1 - s.re)/2) 0)
      ≤ ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0) := by
    apply Real.rpow_le_rpow (by linarith) _ hmax0
    nlinarith
  have hlogle : Real.log (|s.im| + 3) ≤ Real.log ((N:ℝ) * (|s.im| + 3)) := by
    apply Real.log_le_log (by linarith)
    nlinarith
  have hlog0 : (0:ℝ) ≤ Real.log (|s.im| + 3) := by
    apply Real.log_nonneg
    linarith
  have hDpow0 : (0:ℝ) ≤ (|s.im| + 2) ^ (max ((1 - s.re)/2) 0) :=
    Real.rpow_nonneg (by linarith) _
  have hζ : ‖riemannZeta s‖
      ≤ 200000 * (((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
          * Real.log ((N:ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖) := by
    have h := norm_riemannZeta_le_convexity hσ1 hσ2
    have hmono : 200000 * (|s.im| + 2) ^ (max ((1 - s.re)/2) 0) * Real.log (|s.im| + 3)
        ≤ 200000 * (((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
            * Real.log ((N:ℝ) * (|s.im| + 3))) := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply mul_le_mul hDle hlogle hlog0 (Real.rpow_nonneg (by nlinarith) _)
    have hpole : (200000:ℝ) / ‖s - 1‖ = 200000 * (1 / ‖s - 1‖) := by ring
    calc ‖riemannZeta s‖
        ≤ 200000 * (|s.im| + 2) ^ (max ((1 - s.re)/2) 0) * Real.log (|s.im| + 3)
          + 200000 / ‖s - 1‖ := h
      _ ≤ 200000 * (((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
            * Real.log ((N:ℝ) * (|s.im| + 3))) + 200000 * (1 / ‖s - 1‖) := by
          rw [← hpole]
          exact add_le_add hmono le_rfl
      _ = 200000 * (((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
            * Real.log ((N:ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖) := by ring
  -- assemble
  have hRHS0 : (0:ℝ) ≤ ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
      * Real.log ((N:ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖ := by
    apply add_nonneg
    · exact mul_nonneg (Real.rpow_nonneg (by nlinarith) _) (hlog0.trans hlogle)
    · positivity
  calc ‖∏ p ∈ N.primeFactors, (1 - (p:ℂ) ^ (-s))‖ * ‖riemannZeta s‖
      ≤ (2 ^ N.primeFactors.card : ℝ) *
          (200000 * (((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
              * Real.log ((N:ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖)) := by
        apply mul_le_mul hprod hζ (norm_nonneg _) (by positivity)
    _ = 200000 * 2 ^ N.primeFactors.card *
          (((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
              * Real.log ((N:ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖) := by ring

/-- **I1, master form: one citable lemma for ALL `χ mod N`** (Z0b §12.1:
"state these as corollaries so the consumers (Lemmas 4.2, 6.3) can cite one
lemma").  For every Dirichlet character `χ mod N`, every `s` with
`χ ≠ 1 ∨ s ≠ 1` and `1/200 ≤ σ ≤ 2`:
`‖L(s,χ)‖ ≤ 200000·2^{ω(N)}·((N(|t|+2))^{max((1−σ)/2,0)}·log(N(|t|+3)) + 1/‖s−1‖)`. -/
theorem norm_LFunction_le_convexity_all (χ : DirichletCharacter ℂ N) {s : ℂ}
    (h : χ ≠ 1 ∨ s ≠ 1) (hσ1 : 1/200 ≤ s.re) (hσ2 : s.re ≤ 2) :
    ‖DirichletCharacter.LFunction χ s‖
      ≤ 200000 * 2 ^ N.primeFactors.card *
          (((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
              * Real.log ((N:ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖) := by
  rcases eq_or_ne χ 1 with rfl | hχ
  · exact norm_LFunctionTrivChar_le_convexity
      (h.resolve_left (fun h' => h' rfl)) hσ1 hσ2
  · have hnp := norm_LFunction_le_convexity_nonprincipal hχ hσ1 hσ2
    have hN1 : (1:ℝ) ≤ (N:ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have habs : (0:ℝ) ≤ |s.im| := abs_nonneg _
    have hpow0 : (0:ℝ) ≤ ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0) :=
      Real.rpow_nonneg (by nlinarith) _
    have hlog0 : (0:ℝ) ≤ Real.log ((N:ℝ) * (|s.im| + 3)) := by
      apply Real.log_nonneg
      nlinarith
    have hpole0 : (0:ℝ) ≤ 1 / ‖s - 1‖ := by positivity
    have h2ω : (0:ℝ) ≤ (2:ℝ) ^ N.primeFactors.card := by positivity
    calc ‖DirichletCharacter.LFunction χ s‖
        ≤ 100000 * 2 ^ N.primeFactors.card
            * ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
            * Real.log ((N:ℝ) * (|s.im| + 3)) := hnp
      _ ≤ 200000 * 2 ^ N.primeFactors.card *
            (((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
                * Real.log ((N:ℝ) * (|s.im| + 3)) + 1 / ‖s - 1‖) := by
          nlinarith [mul_nonneg (mul_nonneg h2ω hpow0) hlog0,
            mul_nonneg h2ω hpole0]

end Principal

end Carmichael
