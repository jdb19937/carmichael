/-
Route Z, sortie Z6c: the pre-sifted zero detector.
Blueprint: routez/Z0b-density.md §1 (parameters), §3 (pseudocharacter toolkit),
§4 (zero detector), §12.3 (frozen statement).

DELIVERED (fully proved, no sorry/axioms):

* §1 parameters as `rpow` definitions: `calL, Rpar, M0par, z1par, z2par, Xpar,
  ellpar, Lambda0`.
* Barban–Vehov weights `bvLam` (λ_δ) and `bvA` (a(n) = ∑_{δ∣n} λ_δ), with
  `abs_bvLam_le_one`, `bvLam_eq_moebius` (δ ≤ z₁), `bvLam_eq_zero` (δ ≥ z₂),
  `bvA_one` (a(1) = 1) and the VANISHING PROPERTY `bvA_eq_zero` (a(n) = 0 for
  1 < n ≤ z₁).
* Pseudocharacters: `fmp` (f = μ·φ), `psi` (ψ_r(n) = f((r,n))), `Pfun` (P(n)),
  `Rset`, `P1` (P(1)).
* Blueprint Lemma 3.2 (`psi_mul_psi_eq_sum_hBV`): ψ_r ψ_{r'}(n) = ∑_{δ∣n} h(δ;r,r')
  with `hBV` the blueprint's h (supported on squarefree δ).
* Blueprint Lemma 3.3(a) (`sum_hBV_div_eq`, EXACT ORTHOGONALITY):
  ∑_δ h(δ;r,r')/δ = φ(r) if r = r', else 0.  This is the engine of §6.
* Blueprint Lemma 3.3(b) (`sum_abs_hBV_le`): ∑_δ |h(δ;r,r')| ≤ ∏_{p∣r}(p+1)·∏_{p∣r'}(p+1).
* Blueprint Lemma 3.1 (`LSeries_bvA_psi_eq_LFunction_mul_Mr`, twisted-L
  factorisation): for Re s > 1, ∑ a(n)ψ_r(n)χ(n)n^{−s} = L(s,χ)·M_r(s,χ),
  with `Mr` in the blueprint's finite product form (via `eulerT`, `tOf`).
* Blueprint Lemma 3.4(c) (`norm_Mr_le`): ‖M_r(s,χ)‖ ≤ z₂·r³ for Re s ≥ 0;
  summed form `sum_inv_mul_norm_Mr_le`.
* Blueprint Lemma 3.4(d) (`norm_Mr_one_principal_le`): ‖M_r(1,χ₀)‖ ≤ (φ(r)/r)(1+log z₂);
  summed form `sum_inv_mul_norm_Mr_one_le`.
* §1 window `Wwin` (Γ-smoothed double window W(n)) with positivity `Wwin_pos`;
  majorant `bMaj` (b_n); detector coefficients `cDet` and the detector `Fdet`
  (F = ∑_{n>z₁} a(n)P(n)e^{−n/X}χ(n)n^{−ρ}), with summability `summable_fdetTerm`.
* Blueprint Lemma 4.3 (`norm_Epole_le`, pole term small at height ≥ Λ₀), proved
  from the Γ-decay hypothesis I8(b) and the I9(c) hypothesis.
* Blueprint Proposition 4.4 = THE FROZEN Z6c STATEMENT (`detector_lower_bound`):
  ‖F(ρ,χ)‖ ≥ (ε/4)·(φ(d)/d)·log D at any zero ρ in the detection range.

DELTAS vs the §12.3 frozen forms (all documented at the statements):

1. HYPOTHESIS-IZED (argument `hdet : DetectionEstimate …` of
   `detector_lower_bound`): the combined content of blueprint Lemmas 4.1+4.2
   (Mellin rectangle shift of the detection identity plus the contour-term
   bound under threshold (T1)).  Reason: the contour shift consumes I1 = Z4a′
   (convexity bound, sortie still OPEN) and the Mellin/rectangle residue
   machinery.  `DetectionEstimate` states exactly the 4.1+4.2 conclusion:
   ‖F(ρ,χ) + e^{−1/X}·P(1) − E_pole(ρ,χ)‖ ≤ P(1)/8 at every detected zero,
   with `Epole` the DEFINED pole term of Lemma 4.1.  Lemma 4.3 (pole bound)
   IS proved here, so only 4.1+4.2 remain open.
2. HYPOTHESIS-IZED interface inputs (open sorties): I8(b) (Γ-decay, argument
   `hGamma`), I9(b) (P(1) ≥ (ε/2)(φ(d)/d)·log D, argument `hP1`), I9(c)
   (Φ_R bound, argument `hPhi`).
3. Threshold: `200 ≤ log D` where the blueprint's D₀ clause (v) says
   `100 ≤ log D` (the extra room absorbs Lemma 3.4(d)'s constant exactly;
   the blueprint's D₀ is far larger anyway via clauses (i)–(ii)).
4. `Mr` is indexed by `Finset.Icc 1 ⌊z₂⌋₊` (the blueprint's `δ ≤ z₂`; λ_δ
   vanishes for δ > z₂, so the forms agree).  Lemma 3.3 sums over
   `(r·r').divisors` (the blueprint's unrestricted ∑_δ; `hBV` vanishes off
   squarefree divisors of `r·r'`, so the forms agree).
5. In `Lambda0`, the blueprint constant C₆ = log(32e·C_Γ′/ε) at ε = 1/100 is
   passed as the explicit value `Real.log (3200 * Real.exp 1 * CΓ')`.

These feed Z6d (the density theorem §§5–10); see routez/Z0b-density.md §12.
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Squarefree

set_option autoImplicit false

namespace Carmichael
namespace Detector

open Finset ArithmeticFunction
open scoped Real ArithmeticFunction.Moebius

/-! ### §1 master parameters (blueprint table), as functions of `D` -/

/-- `𝓛 = log D`. -/
noncomputable def calL (D : ℝ) : ℝ := Real.log D

/-- Pseudocharacter modulus cut `R = D^ε`, `ε = 1/100`. -/
noncomputable def Rpar (D : ℝ) : ℝ := D ^ (1/100 : ℝ)

/-- Bottom of the lower window, `M₀ = D^{3/5}`. -/
noncomputable def M0par (D : ℝ) : ℝ := D ^ (3/5 : ℝ)

/-- Barban–Vehov lower cut `z₁ = D^{31/50}`. -/
noncomputable def z1par (D : ℝ) : ℝ := D ^ (31/50 : ℝ)

/-- Barban–Vehov upper cut `z₂ = D^{63/100}`. -/
noncomputable def z2par (D : ℝ) : ℝ := D ^ (63/100 : ℝ)

/-- Detector length `X = D^{6/5}`. -/
noncomputable def Xpar (D : ℝ) : ℝ := D ^ (6/5 : ℝ)

/-- Window width `ℓ = ε·𝓛 = log D^ε`. -/
noncomputable def ellpar (D : ℝ) : ℝ := (1/100) * Real.log D

/-- Blueprint Lemma 4.3 pole-suppression height
`Λ₀(σ) = log 𝓛 + (6/5)·λ + C₆`, `λ = (1−σ)·𝓛`; the constant `C₆` is passed
explicitly (header delta 5: `C₆ = log(3200·e·C_Γ′)`). -/
noncomputable def Lambda0 (D σ C6 : ℝ) : ℝ :=
  Real.log (Real.log D) + (6/5) * ((1 - σ) * Real.log D) + C6

/-! ### Elementary helpers -/

lemma posLog_of_le_one {x : ℝ} (h0 : 0 ≤ x) (hx : x ≤ 1) : Real.posLog x = 0 := by
  simp only [Real.posLog, max_eq_left_iff]
  exact Real.log_nonpos h0 hx

lemma posLog_of_one_le {x : ℝ} (hx : 1 ≤ x) : Real.posLog x = Real.log x := by
  simp only [Real.posLog, max_eq_right_iff]
  exact Real.log_nonneg hx

/-- `log⁺(x·c) ≤ log⁺ x + log c` for `0 ≤ x`, `1 ≤ c`. -/
lemma posLog_mul_le {x c : ℝ} (hx : 0 ≤ x) (hc : 1 ≤ c) :
    Real.posLog (x * c) ≤ Real.posLog x + Real.log c := by
  rcases le_or_gt (x * c) 1 with h | h
  · rw [posLog_of_le_one (by positivity) h]
    exact add_nonneg Real.posLog_nonneg (Real.log_nonneg hc)
  · have hx0 : 0 < x := by
      rcases hx.lt_or_eq with h0 | h0
      · exact h0
      · exfalso; rw [← h0, zero_mul] at h; exact absurd h (by norm_num)
    rw [posLog_of_one_le h.le, Real.log_mul (ne_of_gt hx0) (by linarith)]
    have hlx : Real.log x ≤ Real.posLog x := by
      simp only [Real.posLog]
      exact le_max_right _ _
    linarith

/-- A finite product of distinct primes is squarefree. -/
lemma squarefree_prod_primes {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  have h0 : (∏ p ∈ S, p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => (hS p hp).ne_zero
  rw [Nat.squarefree_iff_factorization_le_one h0]
  intro q
  rw [Nat.factorization_prod fun p hp => (hS p hp).ne_zero, Finset.sum_apply']
  calc ∑ p ∈ S, p.factorization q = ∑ p ∈ S, if p = q then 1 else 0 := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [(hS p hp).factorization, Finsupp.single_apply]
      _ ≤ 1 := by rw [Finset.sum_ite_eq']; split <;> simp

/-- A squarefree divisor of `n` divides the radical `∏_{p∣n} p`. -/
lemma sf_dvd_radical {δ n : ℕ} (hδ : Squarefree δ) (hdvd : δ ∣ n) (hn : n ≠ 0) :
    δ ∣ ∏ p ∈ n.primeFactors, p := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hδ]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Nat.primeFactors_mono hdvd hn)

/-- Master subset-sum tool: a divisor sum of a summand supported on squarefree
numbers and multiplicative-by-construction there (`δ ↦ ∏_{p∣δ} g(p)`) factors as
an Euler product over the primes of `n`, for ANY `n ≠ 0`.  Powers all of §3. -/
lemma sum_divisors_ite_squarefree_prod {R : Type*} [CommSemiring R] {n : ℕ} (hn : n ≠ 0)
    (gp : ℕ → R) :
    ∑ δ ∈ n.divisors, (if Squarefree δ then ∏ p ∈ δ.primeFactors, gp p else 0)
      = ∏ p ∈ n.primeFactors, (1 + gp p) := by
  classical
  have hprimes : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hsf : Squarefree (∏ p ∈ n.primeFactors, p) := squarefree_prod_primes hprimes
  have hdvd : (∏ p ∈ n.primeFactors, p) ∣ n := Nat.prod_primeFactors_dvd n
  have hpf : (∏ p ∈ n.primeFactors, p).primeFactors = n.primeFactors :=
    Nat.primeFactors_prod hprimes
  have h1 : ∑ δ ∈ n.divisors, (if Squarefree δ then ∏ p ∈ δ.primeFactors, gp p else 0)
      = ∑ δ ∈ (∏ p ∈ n.primeFactors, p).divisors,
          (if Squarefree δ then ∏ p ∈ δ.primeFactors, gp p else 0) := by
    refine (Finset.sum_subset (Nat.divisors_subset_of_dvd hn hdvd) ?_).symm
    intro δ hδ hδ'
    rw [if_neg]
    intro hsfδ
    exact hδ' (Nat.mem_divisors.mpr
      ⟨sf_dvd_radical hsfδ (Nat.mem_divisors.mp hδ).1 hn, hsf.ne_zero⟩)
  have h2 : ∀ δ ∈ (∏ p ∈ n.primeFactors, p).divisors,
      (if Squarefree δ then ∏ p ∈ δ.primeFactors, gp p else 0)
        = ArithmeticFunction.prodPrimeFactors gp δ := by
    intro δ hδ
    have hδsf : Squarefree δ :=
      Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hδ).1 hsf
    rw [if_pos hδsf, ← ArithmeticFunction.prodPrimeFactors_apply hδsf.ne_zero]
  rw [h1, Finset.sum_congr rfl h2,
    ← ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
      (ArithmeticFunction.IsMultiplicative.prodPrimeFactors gp) hsf, hpf]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [ArithmeticFunction.prodPrimeFactors_apply hp'.ne_zero, hp'.primeFactors,
    Finset.prod_singleton]

/-! ### Barban–Vehov weights (blueprint §1) -/

/-- The Barban–Vehov weight
`λ_δ = μ(δ)·(log⁺(z₂/δ) − log⁺(z₁/δ))/log(z₂/z₁)`. -/
noncomputable def bvLam (z1 z2 : ℝ) (δ : ℕ) : ℝ :=
  (μ δ : ℝ) * (Real.posLog (z2 / δ) - Real.posLog (z1 / δ)) / Real.log (z2 / z1)

/-- `a(n) = ∑_{δ ∣ n} λ_δ`. -/
noncomputable def bvA (z1 z2 : ℝ) (n : ℕ) : ℝ := ∑ δ ∈ n.divisors, bvLam z1 z2 δ

lemma bvLam_eq_moebius {z1 z2 : ℝ} (hz1 : 1 ≤ z1) (hz12 : z1 < z2) {δ : ℕ}
    (hδ0 : δ ≠ 0) (hδ : (δ : ℝ) ≤ z1) : bvLam z1 z2 δ = (μ δ : ℝ) := by
  have hδ1 : (1 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hδ0
  have hδpos : (0 : ℝ) < δ := by linarith
  have h1 : (1 : ℝ) ≤ z1 / δ := (one_le_div hδpos).mpr hδ
  have h2 : (1 : ℝ) ≤ z2 / δ := (one_le_div hδpos).mpr (by linarith)
  have hne : Real.log z2 - Real.log z1 ≠ 0 :=
    sub_ne_zero.mpr (ne_of_gt (Real.log_lt_log (by linarith) hz12))
  have hz1' : z1 ≠ 0 := by linarith
  have hz2' : z2 ≠ 0 := by linarith
  rw [bvLam, posLog_of_one_le h2, posLog_of_one_le h1,
    Real.log_div hz2' (ne_of_gt hδpos),
    Real.log_div hz1' (ne_of_gt hδpos),
    Real.log_div hz2' hz1']
  have hsimp : Real.log z2 - Real.log δ - (Real.log z1 - Real.log δ)
      = Real.log z2 - Real.log z1 := by ring
  rw [hsimp]
  field_simp

lemma bvLam_eq_zero {z1 z2 : ℝ} (hz1 : 0 < z1) (hz12 : z1 ≤ z2) {δ : ℕ}
    (hδ : z2 ≤ (δ : ℝ)) : bvLam z1 z2 δ = 0 := by
  have hδpos : (0 : ℝ) < δ := lt_of_lt_of_le (lt_of_lt_of_le hz1 hz12) hδ
  have h1 : z1 / δ ≤ 1 := (div_le_one hδpos).mpr (le_trans hz12 hδ)
  have h2 : z2 / δ ≤ 1 := (div_le_one hδpos).mpr hδ
  rw [bvLam, posLog_of_le_one (div_nonneg hz1.le hδpos.le) h1,
    posLog_of_le_one (div_nonneg (by linarith) hδpos.le) h2]
  simp

lemma abs_bvLam_le_one {z1 z2 : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2) (δ : ℕ) :
    |bvLam z1 z2 δ| ≤ 1 := by
  rcases Nat.eq_zero_or_pos δ with rfl | hδpos
  · simp [bvLam]
  have hδR : (0 : ℝ) < δ := by exact_mod_cast hδpos
  have hlogpos : 0 < Real.log (z2 / z1) := Real.log_pos ((one_lt_div hz1).mpr hz12)
  have hz1' : z1 ≠ 0 := ne_of_gt hz1
  have hδ' : (δ : ℝ) ≠ 0 := ne_of_gt hδR
  have hmono : Real.posLog (z1 / δ) ≤ Real.posLog (z2 / δ) :=
    Real.posLog_le_posLog (div_nonneg hz1.le hδR.le) (by gcongr)
  have hupper : Real.posLog (z2 / δ) ≤ Real.posLog (z1 / δ) + Real.log (z2 / z1) := by
    have h : z2 / (δ : ℝ) = z1 / δ * (z2 / z1) := by
      field_simp
    rw [h]
    exact posLog_mul_le (div_nonneg hz1.le hδR.le) (le_of_lt ((one_lt_div hz1).mpr hz12))
  rw [bvLam, abs_div, abs_of_pos hlogpos, div_le_one hlogpos, abs_mul]
  have h1 : |(μ δ : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have h2 : |Real.posLog (z2 / δ) - Real.posLog (z1 / δ)| ≤ Real.log (z2 / z1) := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  calc |(μ δ : ℝ)| * |Real.posLog (z2 / δ) - Real.posLog (z1 / δ)|
      ≤ 1 * Real.log (z2 / z1) := mul_le_mul h1 h2 (abs_nonneg _) one_pos.le
    _ = Real.log (z2 / z1) := one_mul _

lemma bvA_one {z1 z2 : ℝ} (hz1 : 1 ≤ z1) (hz12 : z1 < z2) : bvA z1 z2 1 = 1 := by
  rw [bvA, Nat.divisors_one, Finset.sum_singleton,
    bvLam_eq_moebius hz1 hz12 one_ne_zero (by exact_mod_cast hz1)]
  simp

/-- The Barban–Vehov VANISHING PROPERTY: `a(n) = 0` for `1 < n ≤ z₁`. -/
lemma bvA_eq_zero {z1 z2 : ℝ} (hz1 : 1 ≤ z1) (hz12 : z1 < z2) {n : ℕ} (hn1 : 1 < n)
    (hn : (n : ℝ) ≤ z1) : bvA z1 z2 n = 0 := by
  have hn0 : n ≠ 0 := by omega
  have h1 : ∀ δ ∈ n.divisors, bvLam z1 z2 δ = (μ δ : ℝ) := by
    intro δ hδ
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hδ
    have hδ0 : δ ≠ 0 := by
      rintro rfl
      exact hn0 (Nat.eq_zero_of_zero_dvd hdvd)
    refine bvLam_eq_moebius hz1 hz12 hδ0 ?_
    calc (δ : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_dvd (by omega) hdvd
      _ ≤ z1 := hn
  rw [bvA, Finset.sum_congr rfl h1]
  have h2 : (∑ δ ∈ n.divisors, μ δ) = (0 : ℤ) := by
    have h := (ArithmeticFunction.coe_mul_zeta_apply (f := μ) (x := n)).symm
    rwa [ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply_ne (show n ≠ 1 by omega)] at h
  rw [← Int.cast_sum, h2, Int.cast_zero]

/-! ### Pseudocharacters `f = μ·φ`, `ψ_r`, `P` (blueprint §1, §3) -/

/-- `f(n) = μ(n)·φ(n)`. -/
noncomputable def fmp (n : ℕ) : ℝ := (μ n : ℝ) * (n.totient : ℝ)

/-- `ψ_r(n) = f((r,n))`. -/
noncomputable def psi (r n : ℕ) : ℝ := fmp (Nat.gcd r n)

@[simp] lemma fmp_one : fmp 1 = 1 := by simp [fmp]

lemma fmp_prime {p : ℕ} (hp : p.Prime) : fmp p = -((p : ℝ) - 1) := by
  rw [fmp, ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp,
    Nat.cast_sub hp.one_lt.le]
  push_cast
  ring

/-- `φ` as a real-valued arithmetic function. -/
noncomputable def phiA : ArithmeticFunction ℝ := ⟨fun n => (n.totient : ℝ), by simp⟩

lemma phiA_apply (n : ℕ) : phiA n = (n.totient : ℝ) := rfl

lemma phiA_mult : phiA.IsMultiplicative := by
  refine ⟨by simp [phiA_apply], fun {m n} h => ?_⟩
  simp only [phiA_apply]
  rw [Nat.totient_mul h]
  push_cast
  ring

/-- `f = μ·φ` as an arithmetic function (pointwise product). -/
noncomputable def fmpA : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul (μ : ArithmeticFunction ℝ) phiA

lemma fmpA_apply (n : ℕ) : fmpA n = fmp n := by
  simp [fmpA, fmp, ArithmeticFunction.pmul_apply, ArithmeticFunction.intCoe_apply, phiA_apply]

lemma fmpA_mult : fmpA.IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.intCast.pmul phiA_mult

lemma fmp_mul_coprime {a b : ℕ} (h : a.Coprime b) : fmp (a * b) = fmp a * fmp b := by
  rw [← fmpA_apply, ← fmpA_apply, ← fmpA_apply]
  exact fmpA_mult.map_mul_of_coprime h

lemma fmp_prod_primeFactors {m : ℕ} (hm : Squarefree m) :
    fmp m = ∏ p ∈ m.primeFactors, fmp p := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hm]
  rw [← fmpA_apply,
    ArithmeticFunction.IsMultiplicative.map_prod_of_subset_primeFactors fmpA_mult m _
      Finset.Subset.rfl]
  exact Finset.prod_congr rfl fun p _ => fmpA_apply p

/-- For squarefree `r`: `φ(r) = ∏_{p ∣ r} (p − 1)` (real form). -/
lemma totient_squarefree_prod {r : ℕ} (hr : Squarefree r) :
    (r.totient : ℝ) = ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := by
  conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hr]
  rw [← phiA_apply,
    ArithmeticFunction.IsMultiplicative.map_prod_of_subset_primeFactors phiA_mult r _
      Finset.Subset.rfl]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hp' := Nat.prime_of_mem_primeFactors hp
  rw [phiA_apply, Nat.totient_prime hp', Nat.cast_sub hp'.one_lt.le, Nat.cast_one]

lemma abs_fmp_le_totient (n : ℕ) : |fmp n| ≤ (n.totient : ℝ) := by
  rw [fmp, abs_mul]
  have h1 : |(μ n : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc |(μ n : ℝ)| * |(n.totient : ℝ)| ≤ 1 * |(n.totient : ℝ)| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = (n.totient : ℝ) := by rw [one_mul, abs_of_nonneg (by positivity)]

lemma abs_psi_le {r : ℕ} (hr : r ≠ 0) (n : ℕ) : |psi r n| ≤ (r : ℝ) := by
  refine (abs_fmp_le_totient _).trans ?_
  have h1 : (Nat.gcd r n).totient ≤ Nat.gcd r n := Nat.totient_le _
  have h2 : Nat.gcd r n ≤ r := Nat.gcd_le_left n (Nat.pos_of_ne_zero hr)
  exact_mod_cast h1.trans h2

open scoped Classical in
/-- The pseudocharacter index set: squarefree `r ≤ R` coprime to the modulus. -/
noncomputable def Rset (N : ℕ) (R : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊R⌋₊).filter fun r => Squarefree r ∧ r.Coprime N

/-- `P(n) = ∑'_{r ≤ R} μ²(r)/r · ψ_r(n)`. -/
noncomputable def Pfun (N : ℕ) (R : ℝ) (n : ℕ) : ℝ := ∑ r ∈ Rset N R, psi r n / r

/-- `P(1) = ∑'_{r ≤ R} μ²(r)/r`. -/
noncomputable def P1 (N : ℕ) (R : ℝ) : ℝ := ∑ r ∈ Rset N R, (r : ℝ)⁻¹

lemma mem_Rset {N : ℕ} {R : ℝ} {r : ℕ} :
    r ∈ Rset N R ↔ (1 ≤ r ∧ r ≤ ⌊R⌋₊) ∧ Squarefree r ∧ r.Coprime N := by
  classical
  simp [Rset, Finset.mem_filter, Finset.mem_Icc]

lemma Pfun_one (N : ℕ) (R : ℝ) : Pfun N R 1 = P1 N R := by
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [psi, Nat.gcd_one_right, fmp_one, one_div]

lemma P1_nonneg (N : ℕ) (R : ℝ) : 0 ≤ P1 N R :=
  Finset.sum_nonneg fun r _ => by positivity

lemma card_Rset_le (N : ℕ) (R : ℝ) : (Rset N R).card ≤ ⌊R⌋₊ := by
  classical
  calc (Rset N R).card ≤ (Finset.Icc 1 ⌊R⌋₊).card := Finset.card_filter_le _ _
    _ = ⌊R⌋₊ := by rw [Nat.card_Icc]; omega

lemma abs_Pfun_le (N : ℕ) (R : ℝ) (n : ℕ) : |Pfun N R n| ≤ (⌊R⌋₊ : ℝ) := by
  calc |Pfun N R n| ≤ ∑ r ∈ Rset N R, |psi r n / r| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ Rset N R, 1 := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hr1 : 1 ≤ r := (mem_Rset.mp hr).1.1
        have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
        rw [abs_div, abs_of_pos hrR, div_le_one hrR]
        exact abs_psi_le (by omega) n
    _ = (Rset N R).card := by simp
    _ ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast card_Rset_le N R

/-! ### Blueprint Lemmas 3.2 and 3.3: the `h`-expansion and EXACT orthogonality -/

/-- Per-prime value of the `h(·; r,r')` kernel: `(value of ψ_r·ψ_{r'} at p) − 1`. -/
noncomputable def hPrime (r r' p : ℕ) : ℝ :=
  (if p ∣ r then fmp p else 1) * (if p ∣ r' then fmp p else 1) - 1

/-- Blueprint `h(δ; r, r')`: supported on squarefree `δ`, multiplicative there,
with value `∏_{p ∣ δ} hPrime p`.  (On squarefree `δ` this matches the
blueprint's two-product display; `hPrime p = 0` for `p ∤ r·r'` enforces the
support condition `δ ∣ rad(r·r')`.) -/
noncomputable def hBV (r r' δ : ℕ) : ℝ :=
  if Squarefree δ then ∏ p ∈ δ.primeFactors, hPrime r r' p else 0

lemma psi_eq_prod {r n : ℕ} (hr : Squarefree r) (hn : n ≠ 0) :
    psi r n = ∏ p ∈ n.primeFactors, (if p ∣ r then fmp p else 1) := by
  classical
  have hgcd_sf : Squarefree (Nat.gcd r n) :=
    Squarefree.squarefree_of_dvd (Nat.gcd_dvd_left r n) hr
  have hset : n.primeFactors.filter (fun p => p ∣ r) = r.primeFactors ∩ n.primeFactors := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_inter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, hpn, -⟩, hpr⟩
      exact ⟨⟨hp, hpr, hr.ne_zero⟩, hp, hpn, hn⟩
    · rintro ⟨⟨hp, hpr, -⟩, -, hpn, -⟩
      exact ⟨⟨hp, hpn, hn⟩, hpr⟩
  rw [psi, fmp_prod_primeFactors hgcd_sf, Nat.primeFactors_gcd hr.ne_zero hn, ← hset,
    Finset.prod_filter]

/-- **Blueprint Lemma 3.2** (product expansion; Jutila Lemma 2):
`ψ_r(n)·ψ_{r'}(n) = ∑_{δ ∣ n} h(δ; r, r')`. -/
theorem psi_mul_psi_eq_sum_hBV {r r' n : ℕ} (hr : Squarefree r) (hr' : Squarefree r')
    (hn : n ≠ 0) :
    psi r n * psi r' n = ∑ δ ∈ n.divisors, hBV r r' δ := by
  simp only [hBV]
  rw [sum_divisors_ite_squarefree_prod hn (hPrime r r'), psi_eq_prod hr hn,
    psi_eq_prod hr' hn, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => by rw [hPrime]; ring

/-- **Blueprint Lemma 3.3(a)** (EXACT ORTHOGONALITY; Jutila Lemma 3):
`∑_δ h(δ; r, r')/δ = φ(r)` if `r = r'`, and `= 0` otherwise.  The sum may be
taken over the divisors of `r·r'` since `h` vanishes elsewhere.  This exactness
(`f(p) − 1 = −p` kills `1 + (f(p)−1)/p`) is the engine of blueprint §6. -/
theorem sum_hBV_div_eq {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    ∑ δ ∈ (r * r').divisors, hBV r r' δ / δ
      = if r = r' then (r.totient : ℝ) else 0 := by
  classical
  have hr0 : r ≠ 0 := hr.ne_zero
  have hr'0 : r' ≠ 0 := hr'.ne_zero
  have hrr'0 : r * r' ≠ 0 := mul_ne_zero hr0 hr'0
  have hterm : ∀ δ ∈ (r * r').divisors, hBV r r' δ / δ
      = if Squarefree δ then ∏ p ∈ δ.primeFactors, (hPrime r r' p / p) else 0 := by
    intro δ hδ
    rw [hBV]
    split_ifs with hsf
    · rw [Finset.prod_div_distrib]
      congr 1
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsf]
    · exact zero_div _
  rw [Finset.sum_congr rfl hterm, sum_divisors_ite_squarefree_prod hrr'0,
    Nat.primeFactors_mul hr0 hr'0]
  by_cases heq : r = r'
  · subst heq
    rw [if_pos rfl, Finset.union_self, totient_squarefree_prod hr]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hpr : p ∣ r := Nat.dvd_of_mem_primeFactors hp
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.ne_zero
    rw [hPrime, if_pos hpr, fmp_prime hp']
    field_simp
    ring
  · rw [if_neg heq]
    have hne : r.primeFactors ≠ r'.primeFactors := by
      intro h
      apply heq
      rw [← Nat.prod_primeFactors_of_squarefree hr, ← Nat.prod_primeFactors_of_squarefree hr', h]
    obtain ⟨p, hp⟩ := Finset.symmDiff_nonempty.mpr hne
    rw [Finset.mem_symmDiff] at hp
    have hzero : ∀ q ∈ r.primeFactors ∪ r'.primeFactors,
        (q ∈ r.primeFactors ∧ q ∉ r'.primeFactors) ∨
          (q ∈ r'.primeFactors ∧ q ∉ r.primeFactors) →
        1 + hPrime r r' q / q = 0 := by
      intro q _ hq
      have hq' : q.Prime := by
        rcases hq with ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact Nat.prime_of_mem_primeFactors h1
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq'.ne_zero
      rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hqr : q ∣ r := Nat.dvd_of_mem_primeFactors h1
        have hqr' : ¬ q ∣ r' := fun hd => h2 (Nat.mem_primeFactors.mpr ⟨hq', hd, hr'0⟩)
        rw [hPrime, if_pos hqr, if_neg hqr', fmp_prime hq', mul_one]
        field_simp
        ring
      · have hqr' : q ∣ r' := Nat.dvd_of_mem_primeFactors h1
        have hqr : ¬ q ∣ r := fun hd => h2 (Nat.mem_primeFactors.mpr ⟨hq', hd, hr0⟩)
        rw [hPrime, if_neg hqr, if_pos hqr', fmp_prime hq', one_mul]
        field_simp
        ring
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Finset.prod_eq_zero (Finset.mem_union_left _ h1)
        (hzero p (Finset.mem_union_left _ h1) (Or.inl ⟨h1, h2⟩))
    · exact Finset.prod_eq_zero (Finset.mem_union_right _ h1)
        (hzero p (Finset.mem_union_right _ h1) (Or.inr ⟨h1, h2⟩))

/-- **Blueprint Lemma 3.3(b)** (`h`-mass): `∑_δ |h(δ;r,r')| ≤ ∏_{p∣r}(p+1)·∏_{p∣r'}(p+1)`. -/
theorem sum_abs_hBV_le {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    ∑ δ ∈ (r * r').divisors, |hBV r r' δ|
      ≤ (∏ p ∈ r.primeFactors, ((p : ℝ) + 1)) * ∏ p ∈ r'.primeFactors, ((p : ℝ) + 1) := by
  classical
  have hr0 : r ≠ 0 := hr.ne_zero
  have hr'0 : r' ≠ 0 := hr'.ne_zero
  have hrr'0 : r * r' ≠ 0 := mul_ne_zero hr0 hr'0
  have habs : ∀ δ, |hBV r r' δ|
      = if Squarefree δ then ∏ p ∈ δ.primeFactors, |hPrime r r' p| else 0 := by
    intro δ
    rw [hBV, apply_ite abs, abs_zero, Finset.abs_prod]
  rw [Finset.sum_congr rfl fun δ _ => habs δ, sum_divisors_ite_squarefree_prod hrr'0,
    Nat.primeFactors_mul hr0 hr'0]
  have hsub : r.primeFactors ∩ r'.primeFactors ⊆ r.primeFactors ∪ r'.primeFactors :=
    Finset.inter_subset_union
  have hUI : ∀ p ∈ (r.primeFactors ∪ r'.primeFactors) \ (r.primeFactors ∩ r'.primeFactors),
      1 + |hPrime r r' p| = (p : ℝ) + 1 := by
    intro p hp
    rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter, not_and_or] at hp
    obtain ⟨hmem, hnot⟩ := hp
    have hp' : p.Prime := by
      rcases hmem with h | h <;> exact Nat.prime_of_mem_primeFactors h
    have hval : hPrime r r' p = -(p : ℝ) := by
      rcases hmem with h | h
      · have hpr : p ∣ r := Nat.dvd_of_mem_primeFactors h
        have hpr' : ¬ p ∣ r' := by
          intro hd
          rcases hnot with hn | hn
          · exact hn (Nat.mem_primeFactors.mpr ⟨hp', hpr, hr0⟩)
          · exact hn (Nat.mem_primeFactors.mpr ⟨hp', hd, hr'0⟩)
        rw [hPrime, if_pos hpr, if_neg hpr', fmp_prime hp', mul_one]
        ring
      · have hpr' : p ∣ r' := Nat.dvd_of_mem_primeFactors h
        have hpr : ¬ p ∣ r := by
          intro hd
          rcases hnot with hn | hn
          · exact hn (Nat.mem_primeFactors.mpr ⟨hp', hd, hr0⟩)
          · exact hn (Nat.mem_primeFactors.mpr ⟨hp', hpr', hr'0⟩)
        rw [hPrime, if_neg hpr, if_pos hpr', fmp_prime hp', one_mul]
        ring
    rw [hval, abs_neg, abs_of_nonneg (by positivity)]
    ring
  have hI : ∀ p ∈ r.primeFactors ∩ r'.primeFactors,
      1 + |hPrime r r' p| ≤ ((p : ℝ) + 1) * ((p : ℝ) + 1) := by
    intro p hp
    rw [Finset.mem_inter] at hp
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp.1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
    have hpr : p ∣ r := Nat.dvd_of_mem_primeFactors hp.1
    have hpr' : p ∣ r' := Nat.dvd_of_mem_primeFactors hp.2
    have hval : hPrime r r' p = ((p : ℝ) - 1) ^ 2 - 1 := by
      rw [hPrime, if_pos hpr, if_pos hpr', fmp_prime hp']
      ring
    rw [hval, abs_of_nonneg (by nlinarith)]
    nlinarith
  calc ∏ p ∈ r.primeFactors ∪ r'.primeFactors, (1 + |hPrime r r' p|)
      = (∏ p ∈ (r.primeFactors ∪ r'.primeFactors) \ (r.primeFactors ∩ r'.primeFactors),
          (1 + |hPrime r r' p|))
        * ∏ p ∈ r.primeFactors ∩ r'.primeFactors, (1 + |hPrime r r' p|) :=
        (Finset.prod_sdiff hsub).symm
    _ ≤ (∏ p ∈ (r.primeFactors ∪ r'.primeFactors) \ (r.primeFactors ∩ r'.primeFactors),
          ((p : ℝ) + 1))
        * ∏ p ∈ r.primeFactors ∩ r'.primeFactors, (((p : ℝ) + 1) * ((p : ℝ) + 1)) := by
        exact mul_le_mul (le_of_eq (Finset.prod_congr rfl hUI))
          (Finset.prod_le_prod (fun p _ => by positivity) hI)
          (Finset.prod_nonneg fun p _ => by positivity)
          (Finset.prod_nonneg fun p _ => by positivity)
    _ = ((∏ p ∈ (r.primeFactors ∪ r'.primeFactors) \ (r.primeFactors ∩ r'.primeFactors),
          ((p : ℝ) + 1))
        * ∏ p ∈ r.primeFactors ∩ r'.primeFactors, ((p : ℝ) + 1))
        * ∏ p ∈ r.primeFactors ∩ r'.primeFactors, ((p : ℝ) + 1) := by
        rw [Finset.prod_mul_distrib]
        ring
    _ = ((∏ p ∈ r.primeFactors ∪ r'.primeFactors, ((p : ℝ) + 1))
        * ∏ p ∈ r.primeFactors ∩ r'.primeFactors, ((p : ℝ) + 1)) := by
        rw [Finset.prod_sdiff hsub]
    _ = _ := Finset.prod_union_inter

/-! ### Blueprint Lemma 3.1: the twisted-`L` factorisation (Jutila Lemma 1)

Strategy: `ψ_t(m) = ∑_{e ∣ m} G_t(e)` with the finitely supported kernel
`Gker`, so `χ·ψ_t = (χ·G_t) ⍟ χ` (Dirichlet convolution) and the inner
L-series factors as `eulerT · L(s,χ)`.  The outer `δ`-sum is a finite
combination of point-mass convolutions.  All identities below at `Re s > 1`. -/

/-- `t(δ; r) = ∏_{p ∣ r, p ∤ δ} p`. -/
noncomputable def tOf (δ r : ℕ) : ℕ :=
  ∏ p ∈ r.primeFactors.filter (fun p => ¬ p ∣ δ), p

lemma tOf_primes {δ r : ℕ} :
    ∀ p ∈ r.primeFactors.filter (fun p => ¬ p ∣ δ), p.Prime :=
  fun _ hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma squarefree_tOf (δ r : ℕ) : Squarefree (tOf δ r) :=
  squarefree_prod_primes tOf_primes

lemma tOf_ne_zero (δ r : ℕ) : tOf δ r ≠ 0 := (squarefree_tOf δ r).ne_zero

lemma tOf_dvd (δ : ℕ) {r : ℕ} (hr : Squarefree r) : tOf δ r ∣ r := by
  conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hr]
  exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)

lemma tOf_primeFactors (δ r : ℕ) :
    (tOf δ r).primeFactors = r.primeFactors.filter (fun p => ¬ p ∣ δ) :=
  Nat.primeFactors_prod tOf_primes

lemma coprime_tOf_left (δ r : ℕ) : Nat.Coprime δ (tOf δ r) := by
  refine Nat.Coprime.prod_right fun p hp => ?_
  obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
  exact (((Nat.prime_of_mem_primeFactors hp1).coprime_iff_not_dvd).mpr hp2).symm

/-- The two gcd factors in the splitting `(r, δm) = (r,δ)·(t(δ;r), m)` are coprime. -/
lemma coprime_gcd_gcd_tOf (r δ m : ℕ) :
    (Nat.gcd r δ).Coprime (Nat.gcd (tOf δ r) m) :=
  Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left _ _)
    (Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_right r δ) (coprime_tOf_left δ r))

/-- Gcd splitting along `n = δ·m`: `(r, δm) = (r, δ)·(t(δ;r), m)` for squarefree `r`. -/
lemma gcd_mul_split {r : ℕ} (hr : Squarefree r) {δ m : ℕ} (hδ : δ ≠ 0) (hm : m ≠ 0) :
    Nat.gcd r (δ * m) = Nat.gcd r δ * Nat.gcd (tOf δ r) m := by
  have hcop := coprime_gcd_gcd_tOf r δ m
  have h1 : Squarefree (Nat.gcd r (δ * m)) :=
    Squarefree.squarefree_of_dvd (Nat.gcd_dvd_left _ _) hr
  have hgl : Squarefree (Nat.gcd r δ) :=
    Squarefree.squarefree_of_dvd (Nat.gcd_dvd_left _ _) hr
  have hgr : Squarefree (Nat.gcd (tOf δ r) m) :=
    Squarefree.squarefree_of_dvd (Nat.gcd_dvd_left _ _) (squarefree_tOf δ r)
  have h2 : Squarefree (Nat.gcd r δ * Nat.gcd (tOf δ r) m) :=
    (Nat.squarefree_mul hcop).mpr ⟨hgl, hgr⟩
  have hpf : (Nat.gcd r (δ * m)).primeFactors
      = (Nat.gcd r δ * Nat.gcd (tOf δ r) m).primeFactors := by
    rw [Nat.primeFactors_gcd hr.ne_zero (mul_ne_zero hδ hm), Nat.primeFactors_mul hδ hm,
      Nat.Coprime.primeFactors_mul hcop, Nat.primeFactors_gcd hr.ne_zero hδ,
      Nat.primeFactors_gcd (tOf_ne_zero δ r) hm, tOf_primeFactors]
    ext p
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hpr, hpδ | hpm⟩
      · exact Or.inl ⟨hpr, hpδ⟩
      · by_cases hdvd : p ∣ δ
        · exact Or.inl ⟨hpr, Nat.mem_primeFactors.mpr
            ⟨Nat.prime_of_mem_primeFactors hpr, hdvd, hδ⟩⟩
        · exact Or.inr ⟨⟨hpr, hdvd⟩, hpm⟩
    · rintro (⟨hpr, hpδ⟩ | ⟨⟨hpr, -⟩, hpm⟩)
      · exact ⟨hpr, Or.inl hpδ⟩
      · exact ⟨hpr, Or.inr hpm⟩
  calc Nat.gcd r (δ * m) = ∏ p ∈ (Nat.gcd r (δ * m)).primeFactors, p :=
        (Nat.prod_primeFactors_of_squarefree h1).symm
    _ = ∏ p ∈ (Nat.gcd r δ * Nat.gcd (tOf δ r) m).primeFactors, p := by rw [hpf]
    _ = Nat.gcd r δ * Nat.gcd (tOf δ r) m := Nat.prod_primeFactors_of_squarefree h2

/-- `ψ_r(δ·m) = f((r,δ))·ψ_{t(δ;r)}(m)` (blueprint Lemma 3.1, first display). -/
lemma psi_mul_split {r : ℕ} (hr : Squarefree r) {δ m : ℕ} (hδ : δ ≠ 0) (hm : m ≠ 0) :
    psi r (δ * m) = fmp (Nat.gcd r δ) * psi (tOf δ r) m := by
  rw [psi, psi, gcd_mul_split hr hδ hm, fmp_mul_coprime (coprime_gcd_gcd_tOf r δ m)]

/-- The finite Möbius-inverted kernel `G_t(e)`: for `e ∣ t` (with `t`
squarefree), `∏_{p ∣ e} (f(p) − 1)`; zero otherwise. -/
noncomputable def Gker (t e : ℕ) : ℝ :=
  if e ∣ t then ∏ p ∈ e.primeFactors, (fmp p - 1) else 0

/-- `ψ_t(m) = ∑_{e ∣ m} G_t(e)` for squarefree `t`. -/
lemma psi_eq_sum_Gker {t m : ℕ} (ht : Squarefree t) (hm : m ≠ 0) :
    psi t m = ∑ e ∈ m.divisors, Gker t e := by
  classical
  have hg : Nat.gcd t m ∣ m := Nat.gcd_dvd_right t m
  have hg_sf : Squarefree (Nat.gcd t m) :=
    Squarefree.squarefree_of_dvd (Nat.gcd_dvd_left t m) ht
  have hg0 : Nat.gcd t m ≠ 0 := Nat.gcd_ne_zero_left ht.ne_zero
  have hstep1 : ∀ e ∈ m.divisors, Gker t e
      = if e ∣ Nat.gcd t m then ∏ p ∈ e.primeFactors, (fmp p - 1) else 0 := by
    intro e he
    have hem : e ∣ m := (Nat.mem_divisors.mp he).1
    rw [Gker]
    by_cases h : e ∣ t
    · rw [if_pos h, if_pos (Nat.dvd_gcd h hem)]
    · rw [if_neg h, if_neg (fun hc => h (hc.trans (Nat.gcd_dvd_left t m)))]
  symm
  calc ∑ e ∈ m.divisors, Gker t e
      = ∑ e ∈ m.divisors, if e ∣ Nat.gcd t m then ∏ p ∈ e.primeFactors, (fmp p - 1) else 0 :=
        Finset.sum_congr rfl hstep1
    _ = ∑ e ∈ m.divisors.filter (fun e => e ∣ Nat.gcd t m),
          ∏ p ∈ e.primeFactors, (fmp p - 1) := (Finset.sum_filter _ _).symm
    _ = ∑ e ∈ (Nat.gcd t m).divisors, ∏ p ∈ e.primeFactors, (fmp p - 1) := by
        rw [Nat.divisors_filter_dvd_of_dvd hm hg]
    _ = ∑ e ∈ (Nat.gcd t m).divisors,
          if Squarefree e then ∏ p ∈ e.primeFactors, (fmp p - 1) else 0 :=
        Finset.sum_congr rfl fun e he =>
          (if_pos (Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp he).1 hg_sf)).symm
    _ = ∏ p ∈ (Nat.gcd t m).primeFactors, (1 + (fmp p - 1)) :=
        sum_divisors_ite_squarefree_prod hg0 _
    _ = ∏ p ∈ (Nat.gcd t m).primeFactors, fmp p :=
        Finset.prod_congr rfl fun p _ => by ring
    _ = psi t m := by rw [psi, fmp_prod_primeFactors hg_sf]

section LSeriesFactorisation

variable {N : ℕ} [NeZero N]

/-- The finite Euler factor `∏_{p ∣ t} (1 + (f(p) − 1)·χ(p)·p^{−s})`. -/
noncomputable def eulerT (χ : DirichletCharacter ℂ N) (s : ℂ) (t : ℕ) : ℂ :=
  ∏ p ∈ t.primeFactors, (1 + ((fmp p - 1 : ℝ) : ℂ) * χ p * (p : ℂ) ^ (-s))

/-- Casting a product of naturals through `cpow` distributes over the factors. -/
lemma natCast_prod_cpow (S : Finset ℕ) (w : ℂ) :
    ((∏ p ∈ S, p : ℕ) : ℂ) ^ w = ∏ p ∈ S, ((p : ℕ) : ℂ) ^ w := by
  classical
  induction S using Finset.cons_induction with
  | empty => simp
  | cons a S ha ih =>
      rw [Finset.prod_cons, Finset.prod_cons, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, ih]

lemma Gker_char_term_eq_zero {t : ℕ} (ht : t ≠ 0) (χ : DirichletCharacter ℂ N) (s : ℂ) :
    ∀ e ∉ t.divisors,
      LSeries.term (fun e => ((Gker t e : ℝ) : ℂ) * χ e) s e = 0 := by
  intro e he
  rcases eq_or_ne e 0 with rfl | he0
  · exact LSeries.term_zero _ _
  · rw [LSeries.term_of_ne_zero he0]
    have h : ¬ e ∣ t := fun hd => he (Nat.mem_divisors.mpr ⟨hd, ht⟩)
    rw [Gker, if_neg h]
    simp

lemma LSeriesSummable_Gker_char {t : ℕ} (ht : t ≠ 0) (χ : DirichletCharacter ℂ N) (s : ℂ) :
    LSeriesSummable (fun e => ((Gker t e : ℝ) : ℂ) * χ e) s :=
  summable_of_ne_finset_zero (Gker_char_term_eq_zero ht χ s)

/-- The L-series of the twisted kernel is the finite Euler factor. -/
lemma LSeries_Gker_char {t : ℕ} (ht : Squarefree t) (χ : DirichletCharacter ℂ N) (s : ℂ) :
    LSeries (fun e => ((Gker t e : ℝ) : ℂ) * χ e) s = eulerT χ s t := by
  classical
  rw [LSeries, tsum_eq_sum (Gker_char_term_eq_zero ht.ne_zero χ s)]
  have hterm : ∀ e ∈ t.divisors,
      LSeries.term (fun e => ((Gker t e : ℝ) : ℂ) * χ e) s e
        = if Squarefree e then
            ∏ p ∈ e.primeFactors, (((fmp p - 1 : ℝ) : ℂ) * χ p * (p : ℂ) ^ (-s))
          else 0 := by
    intro e he
    obtain ⟨het, ht0⟩ := Nat.mem_divisors.mp he
    have he0 : e ≠ 0 := by
      rintro rfl
      exact ht0 (Nat.eq_zero_of_zero_dvd het)
    have hesf : Squarefree e := Squarefree.squarefree_of_dvd het ht
    have hχ : χ (e : ℕ) = ∏ p ∈ e.primeFactors, χ p := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hesf]
      rw [Nat.cast_prod, map_prod]
    have hpow : ((e : ℕ) : ℂ) ^ (-s) = ∏ p ∈ e.primeFactors, ((p : ℕ) : ℂ) ^ (-s) := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hesf]
      exact natCast_prod_cpow _ _
    rw [LSeries.term_of_ne_zero he0, if_pos hesf, Gker, if_pos het, div_eq_mul_inv,
      ← Complex.cpow_neg, hχ, hpow, Complex.ofReal_prod, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl hterm, sum_divisors_ite_squarefree_prod ht.ne_zero _, eulerT]

lemma LSeriesSummable_char_psi {t : ℕ} (ht : t ≠ 0) (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (fun k => χ k * ((psi t k : ℝ) : ℂ)) s := by
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := (t : ℝ)) (fun n _ => ?_) hs
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖χ (n : ZMod N)‖ * |psi t n| ≤ 1 * (t : ℝ) :=
        mul_le_mul (χ.norm_le_one _) (abs_psi_le ht n) (abs_nonneg _) one_pos.le
    _ = (t : ℝ) := one_mul _

/-- Step A of blueprint Lemma 3.1: the inner twisted series factorises,
`∑_k χ(k)ψ_t(k) k^{−s} = eulerT(t)·L(s,χ)` for `Re s > 1`. -/
lemma LSeries_char_psi_eq {t : ℕ} (ht : Squarefree t) (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (fun k => χ k * ((psi t k : ℝ) : ℂ)) s = eulerT χ s t * χ.LFunction s := by
  have hχsum : LSeriesSummable (fun n : ℕ => (χ n : ℂ)) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs
  have hconv : LSeries (fun k => χ k * ((psi t k : ℝ) : ℂ)) s
      = LSeries (LSeries.convolution (fun e => ((Gker t e : ℝ) : ℂ) * χ e) (fun n : ℕ => (χ n : ℂ))) s := by
    refine LSeries_congr (fun {n} hn => ?_) s
    simp only [LSeries.convolution_def]
    rw [Nat.sum_divisorsAntidiagonal (fun a b => (((Gker t a : ℝ) : ℂ) * χ a) * χ b)]
    have h1 : ∀ a ∈ n.divisors,
        (((Gker t a : ℝ) : ℂ) * χ a) * χ ((n / a : ℕ)) = ((Gker t a : ℝ) : ℂ) * χ n := by
      intro a ha
      have hdvd := (Nat.mem_divisors.mp ha).1
      rw [mul_assoc]
      congr 1
      rw [← map_mul, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
    rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, psi_eq_sum_Gker ht hn]
    push_cast
    ring
  rw [hconv, LSeries_convolution' (LSeriesSummable_Gker_char ht.ne_zero χ s) hχsum,
    LSeries_Gker_char ht χ s, DirichletCharacter.LFunction_eq_LSeries χ hs]

lemma LSeriesSummable_pointMass (δ : ℕ) (c : ℂ) (s : ℂ) :
    LSeriesSummable (fun m => if m = δ then c else 0) s := by
  refine summable_of_ne_finset_zero (s := {δ}) fun m hm => ?_
  have hmδ : m ≠ δ := by simpa using hm
  rcases eq_or_ne m 0 with rfl | h0
  · exact LSeries.term_zero _ _
  · rw [LSeries.term_of_ne_zero h0, if_neg hmδ, zero_div]

lemma LSeries_pointMass {δ : ℕ} (hδ : δ ≠ 0) (c : ℂ) (s : ℂ) :
    LSeries (fun m => if m = δ then c else 0) s = c * (δ : ℂ) ^ (-s) := by
  rw [LSeries, tsum_eq_single δ ?_]
  · rw [LSeries.term_of_ne_zero hδ, if_pos rfl, Complex.cpow_neg, div_eq_mul_inv]
  · intro m hmδ
    rcases eq_or_ne m 0 with rfl | h0
    · exact LSeries.term_zero _ _
    · rw [LSeries.term_of_ne_zero h0, if_neg hmδ, zero_div]

lemma pointMass_convolution {δ : ℕ} (c : ℂ) (G : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    (LSeries.convolution (fun m => if m = δ then c else 0) G) n
      = if δ ∣ n then c * G (n / δ) else 0 := by
  classical
  simp only [LSeries.convolution_def]
  rw [Nat.sum_divisorsAntidiagonal (fun a b => (if a = δ then c else 0) * G b)]
  have h1 : ∀ a ∈ n.divisors,
      (if a = δ then c else 0) * G (n / a) = if a = δ then c * G (n / a) else 0 := by
    intro a _
    split <;> simp
  rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' n.divisors δ (fun a => c * G (n / a))]
  by_cases h : δ ∣ n
  · rw [if_pos (Nat.mem_divisors.mpr ⟨h, hn⟩), if_pos h]
  · rw [if_neg (fun hc => h (Nat.mem_divisors.mp hc).1), if_neg h]

/-- Blueprint `M_r(s, χ)`: the finite mollifier
`∑_{δ ≤ z₂} λ_δ·f((r,δ))·χ(δ)·δ^{−s}·∏_{p ∣ t(δ;r)}(1 + (f(p)−1)χ(p)p^{−s})`. -/
noncomputable def Mr (χ : DirichletCharacter ℂ N) (z1 z2 : ℝ) (r : ℕ) (s : ℂ) : ℂ :=
  ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊,
    ((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ) * χ δ * (δ : ℂ) ^ (-s)
      * eulerT χ s (tOf δ r)

/-- Step B of blueprint Lemma 3.1 (pointwise): the coefficient
`a(n)·ψ_r(n)·χ(n)` is a finite combination of point-mass convolutions. -/
lemma bvA_psi_char_eq_sum {r : ℕ} (hr : Squarefree r) {z1 z2 : ℝ} (hz1 : 0 < z1)
    (hz12 : z1 ≤ z2) (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : n ≠ 0) :
    ((bvA z1 z2 n * psi r n : ℝ) : ℂ) * χ n
      = ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊, ((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ)
          * (LSeries.convolution (fun m => if m = δ then χ δ else 0)
              (fun k => χ k * ((psi (tOf δ r) k : ℝ) : ℂ))) n := by
  classical
  have hz2 : 0 ≤ z2 := le_trans hz1.le hz12
  -- rewrite each convolution summand
  have hstep : ∀ δ ∈ Finset.Icc 1 ⌊z2⌋₊,
      ((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ)
        * (LSeries.convolution (fun m => if m = δ then χ δ else 0)
            (fun k => χ k * ((psi (tOf δ r) k : ℝ) : ℂ))) n
      = if δ ∣ n then ((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ) * χ n
          * ((psi (tOf δ r) (n / δ) : ℝ) : ℂ) else 0 := by
    intro δ hδ
    rw [pointMass_convolution (χ δ) _ hn]
    by_cases h : δ ∣ n
    · rw [if_pos h, if_pos h]
      have hmul : χ (δ : ℕ) * χ ((n / δ : ℕ)) = χ n := by
        rw [← map_mul, ← Nat.cast_mul, Nat.mul_div_cancel' h]
      rw [← hmul]
      ring
    · rw [if_neg h, if_neg h, mul_zero]
  rw [Finset.sum_congr rfl hstep]
  -- the divisor-sum form of the left side
  have hre : (bvA z1 z2 n * psi r n : ℝ)
      = ∑ δ ∈ n.divisors, bvLam z1 z2 δ * fmp (Nat.gcd r δ) * psi (tOf δ r) (n / δ) := by
    rw [bvA, Finset.sum_mul]
    refine Finset.sum_congr rfl fun δ hδ => ?_
    have hdvd := (Nat.mem_divisors.mp hδ).1
    have hδ0 : δ ≠ 0 := by
      rintro rfl
      exact hn (Nat.eq_zero_of_zero_dvd hdvd)
    have hm0 : n / δ ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero hδ0)
      omega
    have hsplit : psi r n = fmp (Nat.gcd r δ) * psi (tOf δ r) (n / δ) := by
      conv_lhs => rw [show n = δ * (n / δ) from (Nat.mul_div_cancel' hdvd).symm]
      exact psi_mul_split hr hδ0 hm0
    rw [hsplit]
    ring
  -- assemble: both sides equal the sum over `n.divisors ∩ Icc 1 ⌊z₂⌋₊`
  have hLHS : ((bvA z1 z2 n * psi r n : ℝ) : ℂ) * χ n
      = ∑ δ ∈ n.divisors, ((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ) * χ n
          * ((psi (tOf δ r) (n / δ) : ℝ) : ℂ) := by
    rw [hre]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun δ _ => by ring
  rw [hLHS]
  -- restrict the divisor sum to δ ≤ ⌊z₂⌋₊ (the tail has λ_δ = 0)
  have htail : ∀ δ ∈ n.divisors, δ ∉ n.divisors ∩ Finset.Icc 1 ⌊z2⌋₊ →
      ((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ) * χ n
        * ((psi (tOf δ r) (n / δ) : ℝ) : ℂ) = 0 := by
    intro δ hδ hδ'
    have hδ1 : 1 ≤ δ := Nat.pos_of_mem_divisors hδ
    have hgt : ⌊z2⌋₊ < δ := by
      by_contra hle
      exact hδ' (Finset.mem_inter.mpr ⟨hδ, Finset.mem_Icc.mpr ⟨hδ1, by omega⟩⟩)
    have hz2δ : z2 ≤ (δ : ℝ) := le_of_lt ((Nat.floor_lt hz2).mp hgt)
    rw [bvLam_eq_zero hz1 hz12 hz2δ]
    simp
  have hleft : ∑ δ ∈ n.divisors, ((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ) * χ n
      * ((psi (tOf δ r) (n / δ) : ℝ) : ℂ)
    = ∑ δ ∈ n.divisors ∩ Finset.Icc 1 ⌊z2⌋₊,
        ((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ) * χ n
          * ((psi (tOf δ r) (n / δ) : ℝ) : ℂ) :=
    (Finset.sum_subset Finset.inter_subset_left htail).symm
  -- restrict the Icc sum to divisors (the rest vanish by the `if`)
  have hright : ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊,
      (if δ ∣ n then ((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ) * χ n
        * ((psi (tOf δ r) (n / δ) : ℝ) : ℂ) else 0)
    = ∑ δ ∈ n.divisors ∩ Finset.Icc 1 ⌊z2⌋₊,
        ((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ) * χ n
          * ((psi (tOf δ r) (n / δ) : ℝ) : ℂ) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun δ _ => rfl
    ext δ
    simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h3, hn⟩, h1, h2⟩
    · rintro ⟨⟨h1, -⟩, h2, h3⟩
      exact ⟨⟨h2, h3⟩, h1⟩
  rw [hleft, hright]

/-- **Blueprint Lemma 3.1** (twisted-`L` factorisation; Jutila Lemma 1): for
`Re s > 1` and squarefree `r`,
`∑_n a(n)·ψ_r(n)·χ(n)·n^{−s} = L(s,χ)·M_r(s,χ)`.
(`M_r` is entire — a finite sum of finite products — so this identity is the
`Re s > 1` anchor of the analytic continuation used in blueprint Lemma 4.1.) -/
theorem LSeries_bvA_psi_eq_LFunction_mul_Mr {r : ℕ} (hr : Squarefree r) {z1 z2 : ℝ}
    (hz1 : 0 < z1) (hz12 : z1 ≤ z2) (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((bvA z1 z2 n * psi r n : ℝ) : ℂ) * χ n) s
      = χ.LFunction s * Mr χ z1 z2 r s := by
  classical
  have hterm : ∀ n : ℕ,
      LSeries.term (fun n => ((bvA z1 z2 n * psi r n : ℝ) : ℂ) * χ n) s n
        = ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊, ((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ)
            * LSeries.term (LSeries.convolution (fun m => if m = δ then χ δ else 0)
                (fun k => χ k * ((psi (tOf δ r) k : ℝ) : ℂ))) s n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, bvA_psi_char_eq_sum hr hz1 hz12 χ hn, Finset.sum_div]
      refine Finset.sum_congr rfl fun δ _ => ?_
      rw [LSeries.term_of_ne_zero hn, mul_div_assoc]
  have hsummand : ∀ δ ∈ Finset.Icc 1 ⌊z2⌋₊,
      Summable (fun n => ((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ)
        * LSeries.term (LSeries.convolution (fun m => if m = δ then χ δ else 0)
            (fun k => χ k * ((psi (tOf δ r) k : ℝ) : ℂ))) s n) := by
    intro δ _
    exact ((LSeriesSummable_pointMass δ (χ δ) s).convolution
      (LSeriesSummable_char_psi (tOf_ne_zero δ r) χ hs)).mul_left _
  rw [LSeries, tsum_congr hterm, Summable.tsum_finsetSum hsummand]
  have hpiece : ∀ δ ∈ Finset.Icc 1 ⌊z2⌋₊,
      (∑' n, ((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ)
        * LSeries.term (LSeries.convolution (fun m => if m = δ then χ δ else 0)
            (fun k => χ k * ((psi (tOf δ r) k : ℝ) : ℂ))) s n)
      = ((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ)
          * (χ δ * (δ : ℂ) ^ (-s) * (eulerT χ s (tOf δ r) * χ.LFunction s)) := by
    intro δ hδ
    have hδ0 : δ ≠ 0 := by
      have := (Finset.mem_Icc.mp hδ).1
      omega
    rw [tsum_mul_left]
    congr 1
    calc ∑' n, LSeries.term (LSeries.convolution (fun m => if m = δ then χ δ else 0)
            (fun k => χ k * ((psi (tOf δ r) k : ℝ) : ℂ))) s n
        = LSeries (LSeries.convolution (fun m => if m = δ then χ δ else 0)
            (fun k => χ k * ((psi (tOf δ r) k : ℝ) : ℂ))) s := rfl
      _ = LSeries (fun m => if m = δ then χ δ else 0) s
            * LSeries (fun k => χ k * ((psi (tOf δ r) k : ℝ) : ℂ)) s :=
          LSeries_convolution' (LSeriesSummable_pointMass δ (χ δ) s)
            (LSeriesSummable_char_psi (tOf_ne_zero δ r) χ hs)
      _ = χ δ * (δ : ℂ) ^ (-s) * (eulerT χ s (tOf δ r) * χ.LFunction s) := by
          rw [LSeries_pointMass hδ0 (χ δ) s, LSeries_char_psi_eq (squarefree_tOf δ r) χ hs]
  rw [Finset.sum_congr rfl hpiece, Mr, Finset.mul_sum]
  exact Finset.sum_congr rfl fun δ _ => by ring

/-! ### Blueprint Lemma 3.4(c),(d): size bounds for `M_r` -/

lemma norm_eulerT_le (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 ≤ s.re) (t : ℕ) :
    ‖eulerT χ s t‖ ≤ ∏ p ∈ t.primeFactors, ((p : ℝ) + 1) := by
  rw [eulerT]
  refine (Finset.norm_prod_le _ _).trans
    (Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p hp => ?_)
  have hp' := Nat.prime_of_mem_primeFactors hp
  have hfactor : ‖((fmp p - 1 : ℝ) : ℂ) * χ p * (p : ℂ) ^ (-s)‖ ≤ (p : ℝ) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |fmp p - 1| = (p : ℝ) := by
      rw [fmp_prime hp', show -((p : ℝ) - 1) - 1 = -(p : ℝ) from by ring, abs_neg,
        abs_of_nonneg (by positivity)]
    have h2 : ‖χ (p : ZMod N)‖ ≤ 1 := χ.norm_le_one _
    have h3 : ‖((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos hp'.pos]
      refine Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp'.one_lt.le) ?_
      simp [hs]
    rw [h1]
    calc (p : ℝ) * ‖χ (p : ZMod N)‖ * ‖((p : ℕ) : ℂ) ^ (-s)‖
        ≤ (p : ℝ) * 1 * 1 := by gcongr <;> positivity
      _ = (p : ℝ) := by ring
  calc ‖1 + ((fmp p - 1 : ℝ) : ℂ) * χ p * (p : ℂ) ^ (-s)‖
      ≤ ‖(1 : ℂ)‖ + ‖((fmp p - 1 : ℝ) : ℂ) * χ p * (p : ℂ) ^ (-s)‖ := norm_add_le _ _
    _ ≤ 1 + (p : ℝ) := by rw [norm_one]; linarith
    _ = (p : ℝ) + 1 := by ring

lemma prod_primeFactors_add_one_le {r : ℕ} (hr : Squarefree r) :
    ∏ p ∈ r.primeFactors, ((p : ℝ) + 1) ≤ (r : ℝ) ^ 2 := by
  have h4 : ∏ p ∈ r.primeFactors, (p : ℝ) = (r : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hr]
  calc ∏ p ∈ r.primeFactors, ((p : ℝ) + 1)
      ≤ ∏ p ∈ r.primeFactors, (2 * (p : ℝ)) := by
        refine Finset.prod_le_prod (fun p _ => by positivity) fun p hp => ?_
        have h : (1 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le
        linarith
    _ = (∏ p ∈ r.primeFactors, (2 : ℝ)) * ∏ p ∈ r.primeFactors, (p : ℝ) :=
        Finset.prod_mul_distrib
    _ ≤ (∏ p ∈ r.primeFactors, (p : ℝ)) * ∏ p ∈ r.primeFactors, (p : ℝ) := by
        refine mul_le_mul_of_nonneg_right
          (Finset.prod_le_prod (fun p _ => by norm_num) fun p hp => ?_)
          (Finset.prod_nonneg fun p _ => by positivity)
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    _ = (r : ℝ) ^ 2 := by rw [h4]; ring

/-- **Blueprint Lemma 3.4(c)** (crude mollifier bound): `‖M_r(s,χ)‖ ≤ z₂·r³`
for `Re s ≥ 0`. -/
theorem norm_Mr_le {r : ℕ} (hr : Squarefree r) {z1 z2 : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2)
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖Mr χ z1 z2 r s‖ ≤ z2 * (r : ℝ) ^ 3 := by
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr.ne_zero
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hz2 : 0 ≤ z2 := by linarith
  have hterm : ∀ δ ∈ Finset.Icc 1 ⌊z2⌋₊,
      ‖((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ) * χ δ * (δ : ℂ) ^ (-s)
          * eulerT χ s (tOf δ r)‖ ≤ (r : ℝ) ^ 3 := by
    intro δ hδ
    have hδ1 : 1 ≤ δ := (Finset.mem_Icc.mp hδ).1
    have h1 : ‖((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ)‖ ≤ (r : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
      calc |bvLam z1 z2 δ| * |fmp (Nat.gcd r δ)| ≤ 1 * (r : ℝ) :=
            mul_le_mul (abs_bvLam_le_one hz1 hz12 δ) (abs_psi_le hr.ne_zero δ)
              (abs_nonneg _) one_pos.le
        _ = (r : ℝ) := one_mul _
    have h2 : ‖χ ((δ : ℕ) : ZMod N)‖ ≤ 1 := χ.norm_le_one _
    have h3 : ‖((δ : ℕ) : ℂ) ^ (-s)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hδ1) (by simp [hs])
    have h4 : ‖eulerT χ s (tOf δ r)‖ ≤ (r : ℝ) ^ 2 := by
      refine (norm_eulerT_le χ hs _).trans (le_trans ?_ (prod_primeFactors_add_one_le hr))
      have hsubset : (tOf δ r).primeFactors ⊆ r.primeFactors := by
        rw [tOf_primeFactors]
        exact Finset.filter_subset _ _
      have hone : (1 : ℝ) ≤ ∏ p ∈ r.primeFactors \ (tOf δ r).primeFactors, ((p : ℝ) + 1) := by
        calc (1 : ℝ) = ∏ _p ∈ r.primeFactors \ (tOf δ r).primeFactors, (1 : ℝ) :=
              Finset.prod_const_one.symm
          _ ≤ ∏ p ∈ r.primeFactors \ (tOf δ r).primeFactors, ((p : ℝ) + 1) := by
              refine Finset.prod_le_prod (fun p _ => zero_le_one) fun p hp => ?_
              have h : (1 : ℝ) ≤ (p : ℝ) := by
                exact_mod_cast
                  (Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1).one_lt.le
              linarith
      calc ∏ p ∈ (tOf δ r).primeFactors, ((p : ℝ) + 1)
          ≤ (∏ p ∈ r.primeFactors \ (tOf δ r).primeFactors, ((p : ℝ) + 1))
            * ∏ p ∈ (tOf δ r).primeFactors, ((p : ℝ) + 1) :=
            le_mul_of_one_le_left (Finset.prod_nonneg fun p _ => by positivity) hone
        _ = ∏ p ∈ r.primeFactors, ((p : ℝ) + 1) := Finset.prod_sdiff hsubset
    rw [norm_mul, norm_mul, norm_mul]
    calc ‖((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ)‖ * ‖χ ((δ : ℕ) : ZMod N)‖
          * ‖((δ : ℕ) : ℂ) ^ (-s)‖ * ‖eulerT χ s (tOf δ r)‖
        ≤ (r : ℝ) * 1 * 1 * (r : ℝ) ^ 2 := by
          refine mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by linarith))
            h3 (norm_nonneg _) (by positivity)) h4 (norm_nonneg _) (by positivity)
      _ = (r : ℝ) ^ 3 := by ring
  calc ‖Mr χ z1 z2 r s‖
      ≤ ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊,
          ‖((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ) * χ δ * (δ : ℂ) ^ (-s)
            * eulerT χ s (tOf δ r)‖ := norm_sum_le _ _
    _ ≤ ∑ _δ ∈ Finset.Icc 1 ⌊z2⌋₊, (r : ℝ) ^ 3 := Finset.sum_le_sum hterm
    _ = (⌊z2⌋₊ : ℝ) * (r : ℝ) ^ 3 := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        norm_num
    _ ≤ z2 * (r : ℝ) ^ 3 := by
        refine mul_le_mul_of_nonneg_right (Nat.floor_le hz2) (by positivity)

/-- Summed form of Lemma 3.4(c): `∑'_{r ≤ R} r⁻¹·‖M_r(s,χ)‖ ≤ z₂·R³`. -/
theorem sum_inv_mul_norm_Mr_le (χ : DirichletCharacter ℂ N) {z1 z2 R : ℝ}
    (hz1 : 0 < z1) (hz12 : z1 < z2) {s : ℂ} (hs : 0 ≤ s.re) (hR : 1 ≤ R) :
    ∑ r ∈ Rset N R, (r : ℝ)⁻¹ * ‖Mr χ z1 z2 r s‖ ≤ z2 * R ^ 3 := by
  have hz2 : 0 ≤ z2 := by linarith
  have hstep : ∀ r ∈ Rset N R, (r : ℝ)⁻¹ * ‖Mr χ z1 z2 r s‖ ≤ z2 * R ^ 2 := by
    intro r hrs
    obtain ⟨⟨hr1, hrfloor⟩, hrsf, -⟩ := mem_Rset.mp hrs
    have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have hrne : (r : ℝ) ≠ 0 := by linarith
    have hrleR : (r : ℝ) ≤ R := by
      calc (r : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast hrfloor
        _ ≤ R := Nat.floor_le (by linarith)
    calc (r : ℝ)⁻¹ * ‖Mr χ z1 z2 r s‖
        ≤ (r : ℝ)⁻¹ * (z2 * (r : ℝ) ^ 3) :=
          mul_le_mul_of_nonneg_left (norm_Mr_le hrsf hz1 hz12 χ hs) (by positivity)
      _ = z2 * (r : ℝ) ^ 2 := by field_simp
      _ ≤ z2 * R ^ 2 := by gcongr
  calc ∑ r ∈ Rset N R, (r : ℝ)⁻¹ * ‖Mr χ z1 z2 r s‖
      ≤ ∑ _r ∈ Rset N R, z2 * R ^ 2 := Finset.sum_le_sum hstep
    _ = ((Rset N R).card : ℝ) * (z2 * R ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ R * (z2 * R ^ 2) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        calc ((Rset N R).card : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast card_Rset_le N R
          _ ≤ R := Nat.floor_le (by linarith)
    _ = z2 * R ^ 3 := by ring

/-- Harmonic bound: `∑_{1 ≤ k ≤ K} 1/k ≤ 1 + log K`. -/
lemma sum_Icc_inv_le (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, ((k : ℝ))⁻¹ ≤ 1 + Real.log K := by
  have h1 : ∑ k ∈ Finset.Icc 1 K, ((k : ℝ))⁻¹ = ((harmonic K : ℚ) : ℝ) := by
    induction K with
    | zero => simp [harmonic_zero]
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih, harmonic_succ]
        push_cast
        ring
  rw [h1]
  exact harmonic_le_one_add_log K

/-- Reciprocal sum over multiples of `r` in `[1, M]`, against `log z₂`. -/
lemma sum_inv_multiples_le {r M : ℕ} (hr : 1 ≤ r) {z2 : ℝ} (hM : (M : ℝ) ≤ z2)
    (hz2 : 1 ≤ z2) :
    ∑ δ ∈ (Finset.Icc 1 M).filter (fun δ => r ∣ δ), ((δ : ℝ))⁻¹
      ≤ (r : ℝ)⁻¹ * (1 + Real.log z2) := by
  classical
  have hr0 : r ≠ 0 := by omega
  have hreindex : ∑ δ ∈ (Finset.Icc 1 M).filter (fun δ => r ∣ δ), ((δ : ℝ))⁻¹
      = ∑ k ∈ Finset.Icc 1 (M / r), ((r * k : ℕ) : ℝ)⁻¹ := by
    refine Finset.sum_nbij' (i := fun δ => δ / r) (j := fun k => r * k) ?_ ?_ ?_ ?_ ?_
    · intro δ hδ
      obtain ⟨hδI, hdvd⟩ := Finset.mem_filter.mp hδ
      obtain ⟨hδ1, hδM⟩ := Finset.mem_Icc.mp hδI
      refine Finset.mem_Icc.mpr ⟨?_, Nat.div_le_div_right hδM⟩
      rw [Nat.one_le_div_iff (by omega)]
      exact Nat.le_of_dvd (by omega) hdvd
    · intro k hk
      obtain ⟨hk1, hkM⟩ := Finset.mem_Icc.mp hk
      have hkr : k * r ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < r)).mp hkM
      have hrk : r * k ≤ M := by rwa [Nat.mul_comm r k]
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, hrk⟩, dvd_mul_right r k⟩
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · intro δ hδ
      exact Nat.mul_div_cancel' (Finset.mem_filter.mp hδ).2
    · intro k _
      exact Nat.mul_div_cancel_left k (by omega)
    · intro δ hδ
      rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hδ).2]
  rw [hreindex]
  have hsplit : ∑ k ∈ Finset.Icc 1 (M / r), ((r * k : ℕ) : ℝ)⁻¹
      = (r : ℝ)⁻¹ * ∑ k ∈ Finset.Icc 1 (M / r), ((k : ℝ))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    rw [mul_inv]
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (sum_Icc_inv_le (M / r)).trans ?_
  have hlog : Real.log (M / r : ℕ) ≤ Real.log z2 := by
    rcases Nat.eq_zero_or_pos (M / r) with h0 | hpos
    · rw [h0]
      simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg hz2
    · refine Real.log_le_log (by exact_mod_cast hpos) ?_
      calc ((M / r : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast Nat.div_le_self M r
        _ ≤ z2 := hM
  linarith

/-- **Blueprint Lemma 3.4(d)**: at `s = 1` and the principal character,
`‖M_r(1, χ₀)‖ ≤ (φ(r)/r)·(1 + log z₂)` (squarefree `r` coprime to the modulus;
only `δ` divisible by `r` survive, since the Euler factor at `s = 1` vanishes
at every prime of `t(δ;r)`). -/
theorem norm_Mr_one_principal_le {r : ℕ} (hr : Squarefree r) (hrN : r.Coprime N)
    {z1 z2 : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2) (hz2 : 1 ≤ z2) :
    ‖Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1‖
      ≤ ((r.totient : ℝ) / r) * (1 + Real.log z2) := by
  classical
  have hr1 : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr.ne_zero
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have heuler0 : ∀ δ : ℕ, ¬ r ∣ δ →
      eulerT (1 : DirichletCharacter ℂ N) 1 (tOf δ r) = 0 := by
    intro δ hnd
    have hex : ∃ p ∈ r.primeFactors, ¬ p ∣ δ := by
      by_contra hcon
      push Not at hcon
      apply hnd
      calc r = ∏ p ∈ r.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hr).symm
        _ ∣ δ := Finset.prod_primes_dvd δ
            (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) hcon
    obtain ⟨p, hpr, hpδ⟩ := hex
    have hp' := Nat.prime_of_mem_primeFactors hpr
    refine Finset.prod_eq_zero (i := p) ?_ ?_
    · rw [tOf_primeFactors, Finset.mem_filter]
      exact ⟨hpr, hpδ⟩
    · have hpN : IsUnit ((p : ℕ) : ZMod N) := by
        rw [ZMod.isUnit_iff_coprime]
        exact Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hpr) hrN
      rw [MulChar.one_apply hpN, fmp_prime hp',
        show ((-((p : ℝ) - 1) - 1 : ℝ) : ℂ) = -((p : ℕ) : ℂ) from by push_cast; ring]
      have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hp'.ne_zero
      rw [Complex.cpow_neg_one]
      field_simp
      norm_num
  have htOf_one : ∀ δ : ℕ, r ∣ δ → tOf δ r = 1 := by
    intro δ hdvd
    rw [tOf]
    have hempty : r.primeFactors.filter (fun p => ¬ p ∣ δ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp
      simp only [not_not]
      exact (Nat.dvd_of_mem_primeFactors hp).trans hdvd
    rw [hempty, Finset.prod_empty]
  have hterm : ∀ δ ∈ Finset.Icc 1 ⌊z2⌋₊,
      ‖((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ) * (1 : DirichletCharacter ℂ N) δ
          * (δ : ℂ) ^ (-(1 : ℂ)) * eulerT (1 : DirichletCharacter ℂ N) 1 (tOf δ r)‖
        ≤ if r ∣ δ then (r.totient : ℝ) * ((δ : ℝ))⁻¹ else 0 := by
    intro δ hδ
    have hδ1 : 1 ≤ δ := (Finset.mem_Icc.mp hδ).1
    by_cases h : r ∣ δ
    · rw [if_pos h, htOf_one δ h,
        show eulerT (1 : DirichletCharacter ℂ N) 1 1 = 1 from by simp [eulerT], mul_one,
        Nat.gcd_eq_left h, norm_mul, norm_mul]
      have h1 : ‖((bvLam z1 z2 δ * fmp r : ℝ) : ℂ)‖ ≤ (r.totient : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
        calc |bvLam z1 z2 δ| * |fmp r| ≤ 1 * (r.totient : ℝ) :=
              mul_le_mul (abs_bvLam_le_one hz1 hz12 δ) (abs_fmp_le_totient r)
                (abs_nonneg _) one_pos.le
          _ = (r.totient : ℝ) := one_mul _
      have h2 : ‖(1 : DirichletCharacter ℂ N) ((δ : ℕ) : ZMod N)‖ ≤ 1 :=
        (1 : DirichletCharacter ℂ N).norm_le_one _
      have h3 : ‖((δ : ℕ) : ℂ) ^ (-(1 : ℂ))‖ = ((δ : ℝ))⁻¹ := by
        rw [Complex.norm_natCast_cpow_of_pos (by omega)]
        norm_num [Real.rpow_neg_one]
      rw [h3]
      calc ‖((bvLam z1 z2 δ * fmp r : ℝ) : ℂ)‖ * ‖(1 : DirichletCharacter ℂ N) ((δ:ℕ) : ZMod N)‖
            * ((δ : ℝ))⁻¹
          ≤ (r.totient : ℝ) * 1 * ((δ : ℝ))⁻¹ := by
            refine mul_le_mul_of_nonneg_right
              (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) (by positivity)
        _ = (r.totient : ℝ) * ((δ : ℝ))⁻¹ := by ring
    · rw [if_neg h, heuler0 δ h, mul_zero, norm_zero]
  calc ‖Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1‖
      ≤ ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊,
          ‖((bvLam z1 z2 δ * fmp (Nat.gcd r δ) : ℝ) : ℂ) * (1 : DirichletCharacter ℂ N) δ
            * (δ : ℂ) ^ (-(1 : ℂ)) * eulerT (1 : DirichletCharacter ℂ N) 1 (tOf δ r)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ δ ∈ Finset.Icc 1 ⌊z2⌋₊, (if r ∣ δ then (r.totient : ℝ) * ((δ : ℝ))⁻¹ else 0) :=
        Finset.sum_le_sum hterm
    _ = (r.totient : ℝ) * ∑ δ ∈ (Finset.Icc 1 ⌊z2⌋₊).filter (fun δ => r ∣ δ), ((δ : ℝ))⁻¹ := by
        rw [← Finset.sum_filter, Finset.mul_sum]
    _ ≤ (r.totient : ℝ) * ((r : ℝ)⁻¹ * (1 + Real.log z2)) := by
        refine mul_le_mul_of_nonneg_left
          (sum_inv_multiples_le hr1 (Nat.floor_le (by linarith)) hz2) (by positivity)
    _ = ((r.totient : ℝ) / r) * (1 + Real.log z2) := by ring

/-- Summed form of Lemma 3.4(d):
`∑'_{r ≤ R} r⁻¹·‖M_r(1,χ₀)‖ ≤ Φ_R·(1 + log z₂)` with `Φ_R = ∑' φ(r)/r²`. -/
theorem sum_inv_mul_norm_Mr_one_le {z1 z2 : ℝ} (R : ℝ)
    (hz1 : 0 < z1) (hz12 : z1 < z2) (hz2 : 1 ≤ z2) :
    ∑ r ∈ Rset N R, (r : ℝ)⁻¹ * ‖Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1‖
      ≤ (∑ r ∈ Rset N R, (r.totient : ℝ) / (r : ℝ) ^ 2) * (1 + Real.log z2) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun r hrs => ?_
  obtain ⟨⟨hr1, -⟩, hrsf, hrcop⟩ := mem_Rset.mp hrs
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  calc (r : ℝ)⁻¹ * ‖Mr (1 : DirichletCharacter ℂ N) z1 z2 r 1‖
      ≤ (r : ℝ)⁻¹ * (((r.totient : ℝ) / r) * (1 + Real.log z2)) :=
        mul_le_mul_of_nonneg_left (norm_Mr_one_principal_le hrsf hrcop hz1 hz12 hz2)
          (by positivity)
    _ = (r.totient : ℝ) / (r : ℝ) ^ 2 * (1 + Real.log z2) := by
        field_simp

end LSeriesFactorisation

/-! ### §1 window, majorant, and detector coefficients -/

/-- The Γ-smoothed averaged double-exponential window `W(n)` (blueprint §1):
`W(n) = avg_{η ∈ [log X, log X + ℓ]} e^{−n/e^η} − avg_{ξ ∈ [log M₀, log M₀ + ℓ]} e^{−n/e^ξ}`. -/
noncomputable def Wwin (M0 X ell : ℝ) (n : ℕ) : ℝ :=
  (1 / ell) * (∫ η in Real.log X..(Real.log X + ell), Real.exp (-(n : ℝ) / Real.exp η))
    - (1 / ell) * (∫ ξ in Real.log M0..(Real.log M0 + ell), Real.exp (-(n : ℝ) / Real.exp ξ))

lemma continuous_windowIntegrand (n : ℕ) :
    Continuous fun η : ℝ => Real.exp (-(n : ℝ) / Real.exp η) :=
  Real.continuous_exp.comp
    (continuous_const.div Real.continuous_exp fun x => (Real.exp_pos x).ne')

/-- Window sandwich, lower half: `W(n) ≥ e^{−n/X} − e^{−n/(M₀e^ℓ)}`. -/
lemma exp_sub_exp_le_Wwin {M0 X ell : ℝ} (hM0 : 0 < M0) (hX : 0 < X) (hell : 0 < ell)
    (n : ℕ) :
    Real.exp (-(n : ℝ) / X) - Real.exp (-(n : ℝ) / (M0 * Real.exp ell)) ≤ Wwin M0 X ell n := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun η : ℝ => Real.exp (-(n : ℝ) / Real.exp η))
      MeasureTheory.volume a b := fun a b => (continuous_windowIntegrand n).intervalIntegrable a b
  have h1 : ell * Real.exp (-(n : ℝ) / X)
      ≤ ∫ η in Real.log X..(Real.log X + ell), Real.exp (-(n : ℝ) / Real.exp η) := by
    have hmono : ∀ η ∈ Set.Icc (Real.log X) (Real.log X + ell),
        Real.exp (-(n : ℝ) / X) ≤ Real.exp (-(n : ℝ) / Real.exp η) := by
      intro η hη
      have hXη : X ≤ Real.exp η := by
        calc X = Real.exp (Real.log X) := (Real.exp_log hX).symm
          _ ≤ Real.exp η := Real.exp_le_exp.mpr hη.1
      refine Real.exp_le_exp.mpr ?_
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (by positivity) hX hXη
    calc ell * Real.exp (-(n : ℝ) / X)
        = ∫ _η in Real.log X..(Real.log X + ell), Real.exp (-(n : ℝ) / X) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
      _ ≤ _ := intervalIntegral.integral_mono_on (by linarith)
            (intervalIntegrable_const) (hint _ _) hmono
  have h2 : (∫ ξ in Real.log M0..(Real.log M0 + ell), Real.exp (-(n : ℝ) / Real.exp ξ))
      ≤ ell * Real.exp (-(n : ℝ) / (M0 * Real.exp ell)) := by
    have hmono : ∀ ξ ∈ Set.Icc (Real.log M0) (Real.log M0 + ell),
        Real.exp (-(n : ℝ) / Real.exp ξ) ≤ Real.exp (-(n : ℝ) / (M0 * Real.exp ell)) := by
      intro ξ hξ
      have hMξ : Real.exp ξ ≤ M0 * Real.exp ell := by
        calc Real.exp ξ ≤ Real.exp (Real.log M0 + ell) := Real.exp_le_exp.mpr hξ.2
          _ = M0 * Real.exp ell := by rw [Real.exp_add, Real.exp_log hM0]
      refine Real.exp_le_exp.mpr ?_
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (by positivity) (Real.exp_pos ξ) hMξ
    calc (∫ ξ in Real.log M0..(Real.log M0 + ell), Real.exp (-(n : ℝ) / Real.exp ξ))
        ≤ ∫ _ξ in Real.log M0..(Real.log M0 + ell),
            Real.exp (-(n : ℝ) / (M0 * Real.exp ell)) :=
          intervalIntegral.integral_mono_on (by linarith) (hint _ _)
            (intervalIntegrable_const) hmono
      _ = ell * Real.exp (-(n : ℝ) / (M0 * Real.exp ell)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
          ring
  rw [Wwin, sub_le_sub_iff]
  have e1 : Real.exp (-(n : ℝ) / X) ≤ (1 / ell)
      * ∫ η in Real.log X..(Real.log X + ell), Real.exp (-(n : ℝ) / Real.exp η) := by
    calc Real.exp (-(n : ℝ) / X) = (1 / ell) * (ell * Real.exp (-(n : ℝ) / X)) := by
          field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  have e2 : (1 / ell)
      * (∫ ξ in Real.log M0..(Real.log M0 + ell), Real.exp (-(n : ℝ) / Real.exp ξ))
      ≤ Real.exp (-(n : ℝ) / (M0 * Real.exp ell)) := by
    calc (1 / ell) * (∫ ξ in Real.log M0..(Real.log M0 + ell),
            Real.exp (-(n : ℝ) / Real.exp ξ))
        ≤ (1 / ell) * (ell * Real.exp (-(n : ℝ) / (M0 * Real.exp ell))) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = Real.exp (-(n : ℝ) / (M0 * Real.exp ell)) := by field_simp
  linarith

/-- Window positivity: `W(n) > 0` for `n ≥ 1` when `M₀e^ℓ < X`. -/
lemma Wwin_pos {M0 X ell : ℝ} (hM0 : 0 < M0) (hell : 0 < ell)
    (hlt : M0 * Real.exp ell < X) {n : ℕ} (hn : 1 ≤ n) : 0 < Wwin M0 X ell n := by
  have hX : 0 < X := lt_trans (by positivity) hlt
  refine lt_of_lt_of_le ?_ (exp_sub_exp_le_Wwin hM0 hX hell n)
  rw [sub_pos]
  refine Real.exp_lt_exp.mpr ?_
  rw [neg_div, neg_div, neg_lt_neg_iff]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  exact div_lt_div_of_pos_left hnpos (by positivity) hlt

/-- The Halász majorant `b_n = n⁻¹·P(n)²·W(n)` (blueprint §1). -/
noncomputable def bMaj (N : ℕ) (R M0 X ell : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * (Pfun N R n) ^ 2 * Wwin M0 X ell n

/-- Detector coefficients `c_n = a(n)·P(n)·e^{−n/X}·n^{−σ}` for `n > z₁`, else `0`
(blueprint §1). -/
noncomputable def cDet (N : ℕ) (z1 z2 R X σ : ℝ) (n : ℕ) : ℝ :=
  if z1 < (n : ℝ) then
    bvA z1 z2 n * Pfun N R n * Real.exp (-(n : ℝ) / X) * (n : ℝ) ^ (-σ)
  else 0

/-- The zero detector
`F(ρ, χ) = ∑_{n > z₁} a(n)·P(n)·e^{−n/X}·χ(n)·n^{−ρ}` (blueprint §1/§12.3). -/
noncomputable def Fdet {N : ℕ} (χ : DirichletCharacter ℂ N) (z1 z2 R X : ℝ) (ρ : ℂ) : ℂ :=
  ∑' n : ℕ, if z1 < (n : ℝ) then
    ((bvA z1 z2 n * Pfun N R n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-ρ)
  else 0

lemma abs_bvA_le {z1 z2 : ℝ} (hz1 : 0 < z1) (hz12 : z1 < z2) (n : ℕ) :
    |bvA z1 z2 n| ≤ (n : ℝ) := by
  calc |bvA z1 z2 n| ≤ ∑ δ ∈ n.divisors, |bvLam z1 z2 δ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _δ ∈ n.divisors, 1 :=
        Finset.sum_le_sum fun δ _ => abs_bvLam_le_one hz1 hz12 δ
    _ = (n.divisors.card : ℝ) := by simp
    _ ≤ (n : ℝ) := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · have hsub : n.divisors ⊆ Finset.Icc 1 n := fun d hd =>
            Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
              Nat.le_of_dvd hn (Nat.mem_divisors.mp hd).1⟩
          have hcard := Finset.card_le_card hsub
          rw [Nat.card_Icc, Nat.add_sub_cancel] at hcard
          exact_mod_cast hcard

set_option maxHeartbeats 4000000 in
/-- The detector series converges absolutely (exponential cutoff). -/
lemma summable_fdetTerm {N : ℕ} (χ : DirichletCharacter ℂ N) {z1 z2 R X : ℝ}
    (hz1 : 0 < z1) (hz12 : z1 < z2) (hX : 0 < X) {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    Summable (fun n : ℕ => if z1 < (n : ℝ) then
      ((bvA z1 z2 n * Pfun N R n * Real.exp (-(n : ℝ) / X) : ℝ) : ℂ) * χ n * (n : ℂ) ^ (-ρ)
    else 0) := by
  have hq1 : |Real.exp (-1 / X)| < 1 := by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff, neg_div]
    have h0 : (0 : ℝ) < 1 / X := one_div_pos.mpr hX
    linarith
  have hsum : Summable (fun n : ℕ => (⌊R⌋₊ : ℝ) * ((n : ℝ) ^ (1 : ℕ)
      * Real.exp (-1 / X) ^ n)) :=
    (summable_pow_mul_geometric_of_norm_lt_one 1 (by rwa [Real.norm_eq_abs])).mul_left _
  refine Summable.of_norm_bounded hsum ?_
  intro n
  by_cases h : z1 < (n : ℝ)
  · rw [if_pos h]
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | h1
      · rw [Nat.cast_zero] at h
        linarith
      · exact h1
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |bvA z1 z2 n * Pfun N R n * Real.exp (-(n : ℝ) / X)|
        ≤ (n : ℝ) * (⌊R⌋₊ : ℝ) * Real.exp (-1 / X) ^ n := by
      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
      have hexp : Real.exp (-(n : ℝ) / X) = Real.exp (-1 / X) ^ n := by
        rw [← Real.exp_nat_mul]
        congr 1
        field_simp
      rw [hexp]
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (Real.exp_pos _).le n)
      exact mul_le_mul (abs_bvA_le hz1 hz12 n) (abs_Pfun_le N R n) (abs_nonneg _)
        (Nat.cast_nonneg n)
    have h2 : ‖χ ((n : ℕ) : ZMod N)‖ ≤ 1 := χ.norm_le_one _
    have h3 : ‖((n : ℕ) : ℂ) ^ (-ρ)‖ ≤ 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (by omega)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1) (by simp [hρ])
    calc |bvA z1 z2 n * Pfun N R n * Real.exp (-(n : ℝ) / X)| * ‖χ ((n : ℕ) : ZMod N)‖
          * ‖((n : ℕ) : ℂ) ^ (-ρ)‖
        ≤ ((n : ℝ) * (⌊R⌋₊ : ℝ) * Real.exp (-1 / X) ^ n) * 1 * 1 := by
          have hb0 : (0 : ℝ) ≤ (n : ℝ) * (⌊R⌋₊ : ℝ) * Real.exp (-1 / X) ^ n :=
            mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg _))
              (pow_nonneg (Real.exp_pos _).le n)
          exact mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hb0) h3 (norm_nonneg _)
            (mul_nonneg hb0 zero_le_one)
      _ = (⌊R⌋₊ : ℝ) * ((n : ℝ) ^ (1 : ℕ) * Real.exp (-1 / X) ^ n) := by ring
  · rw [if_neg h, norm_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (pow_nonneg (Real.exp_pos _).le _))

/-! ### Blueprint Lemma 4.3 and Proposition 4.4 (the frozen Z6c statement) -/

open scoped Classical in
/-- The pole term `E_pole(ρ, χ)` of blueprint Lemma 4.1: present only for the
principal character.
`E_pole(ρ,χ₀) = Γ(1−ρ)·X^{1−ρ}·(φ(d)/d)·∑'_{r ≤ R} r⁻¹·M_r(1,χ₀)`. -/
noncomputable def Epole {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 R X : ℝ) (ρ : ℂ) : ℂ :=
  if χ = 1 then
    Complex.Gamma (1 - ρ) * (X : ℂ) ^ ((1 : ℂ) - ρ) * ((N.totient : ℂ) / N)
      * ∑ r ∈ Rset N R, ((r : ℂ))⁻¹ * Mr χ z1 z2 r 1
  else 0

lemma Epole_eq_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (z1 z2 R X : ℝ) (ρ : ℂ) : Epole χ z1 z2 R X ρ = 0 := by
  rw [Epole, if_neg hχ]

set_option maxHeartbeats 2000000 in
/-- **Blueprint Lemma 4.3** (pole term small at height `≥ Λ₀`).  Consumes the
hypothesis-ized I8(b) (`hGamma`), I9(b) (`hP1`), I9(c) (`hPhi`); see header
deltas 2–3 (threshold `200 ≤ log D`; `C₆ = log(3200·e·C_Γ′)`). -/
theorem norm_Epole_le {N : ℕ} [NeZero N] {D σ : ℝ} (hD1 : 1 < D)
    (hL : 200 ≤ Real.log D) (hσ1 : σ ≤ 1)
    {CΓ' : ℝ} (hCΓ' : 1 ≤ CΓ')
    (hGamma : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1/2 ≤ |z.im| →
      ‖Complex.Gamma z‖ ≤ CΓ' * Real.exp (-|z.im|))
    (hP1 : (1/200) * ((N.totient : ℝ) / N) * Real.log D ≤ P1 N (Rpar D))
    (hPhi : ∑ r ∈ Rset N (Rpar D), (r.totient : ℝ) / (r : ℝ) ^ 2
      ≤ π ^ 2 / 6 * ((N.totient : ℝ) / N) * (1 + Real.log (Rpar D)))
    {ρ : ℂ} (hβ : σ ≤ ρ.re) (hβ1 : ρ.re ≤ 1) (hσ0 : 0 ≤ σ)
    (hγ : Lambda0 D σ (Real.log (3200 * Real.exp 1 * CΓ')) ≤ |ρ.im|) :
    ‖Epole (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖
      ≤ P1 N (Rpar D) / 8 := by
  have hD0 : (0 : ℝ) < D := by linarith
  set L := Real.log D with hLdef
  have hL0 : (0 : ℝ) < L := by rw [hLdef]; linarith
  set lam := (1 - σ) * L with hlamdef
  have hlam0 : 0 ≤ lam := by
    rw [hlamdef]
    have : 0 ≤ 1 - σ := by linarith
    positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  have hφ0 : (0 : ℝ) ≤ (N.totient : ℝ) / N := by positivity
  have hφ1 : (N.totient : ℝ) / N ≤ 1 := by
    rw [div_le_one hNpos]
    exact_mod_cast Nat.totient_le N
  -- parameter facts
  have hz1pos : 0 < z1par D := Real.rpow_pos_of_pos hD0 _
  have hz12 : z1par D < z2par D := by
    rw [z1par, z2par]
    exact Real.rpow_lt_rpow_of_exponent_lt hD1 (by norm_num)
  have hz2ge1 : 1 ≤ z2par D := by
    rw [z2par]
    calc (1 : ℝ) = D ^ (0 : ℝ) := (Real.rpow_zero D).symm
      _ ≤ D ^ (63/100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by norm_num)
  have hlogR : Real.log (Rpar D) = L / 100 := by
    rw [Rpar, Real.log_rpow hD0]
    ring
  have hlogz2 : Real.log (z2par D) = 63 / 100 * L := by
    rw [z2par, Real.log_rpow hD0]
  -- Γ factor
  have hΓ : ‖Complex.Gamma (1 - ρ)‖ ≤ CΓ' * Real.exp (-|ρ.im|) := by
    have him : |(1 - ρ).im| = |ρ.im| := by
      simp [Complex.sub_im, Complex.one_im]
    have hC6pos : (0 : ℝ) ≤ Real.log (3200 * Real.exp 1 * CΓ') := by
      refine Real.log_nonneg ?_
      have := Real.exp_pos (1 : ℝ)
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    have hloglog : (1 : ℝ) ≤ Real.log L := by
      rw [Real.le_log_iff_exp_le hL0]
      have := Real.exp_one_lt_d9
      linarith
    have him2 : 1/2 ≤ |ρ.im| := by
      have h1 : Real.log (Real.log D) + (6/5) * ((1 - σ) * Real.log D)
          + Real.log (3200 * Real.exp 1 * CΓ') ≤ |ρ.im| := hγ
      have h2 : 0 ≤ (6/5) * ((1 - σ) * Real.log D) := by
        rw [← hLdef]
        rw [show (6/5) * ((1 - σ) * L) = (6/5) * lam from by rw [hlamdef]]
        positivity
      rw [← hLdef] at h1
      linarith
    have := hGamma (1 - ρ) (by simp [Complex.sub_re]; linarith)
      (by simp [Complex.sub_re]; linarith) (by rwa [him])
    rwa [him] at this
  -- X factor
  have hXpos : 0 < Xpar D := Real.rpow_pos_of_pos hD0 _
  have hXnorm : ‖((Xpar D : ℝ) : ℂ) ^ ((1 : ℂ) - ρ)‖ ≤ Real.exp (6/5 * lam) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    have hre : ((1 : ℂ) - ρ).re = 1 - ρ.re := by simp [Complex.sub_re]
    rw [hre]
    have hX1 : 1 ≤ Xpar D := by
      rw [Xpar]
      calc (1 : ℝ) = D ^ (0 : ℝ) := (Real.rpow_zero D).symm
        _ ≤ D ^ (6/5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by norm_num)
    calc Xpar D ^ (1 - ρ.re) ≤ Xpar D ^ (1 - σ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = Real.exp (6/5 * lam) := by
          rw [Xpar, ← Real.rpow_mul hD0.le, Real.rpow_def_of_pos hD0]
          congr 1
          rw [hlamdef, ← hLdef]
          ring
  -- the M_r sum, via 3.4(d)-summed and I9(c)
  have hMr : ‖∑ r ∈ Rset N (Rpar D),
        ((r : ℂ))⁻¹ * Mr (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) r 1‖
      ≤ π ^ 2 / 6 * ((N.totient : ℝ) / N) * (1 + L / 100) * (1 + 63/100 * L) := by
    calc ‖∑ r ∈ Rset N (Rpar D),
          ((r : ℂ))⁻¹ * Mr (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) r 1‖
        ≤ ∑ r ∈ Rset N (Rpar D),
            (r : ℝ)⁻¹ * ‖Mr (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) r 1‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun r _ => ?_))
          rw [norm_mul, norm_inv, Complex.norm_natCast]
      _ ≤ (∑ r ∈ Rset N (Rpar D), (r.totient : ℝ) / (r : ℝ) ^ 2)
            * (1 + Real.log (z2par D)) :=
          sum_inv_mul_norm_Mr_one_le (Rpar D) hz1pos hz12 hz2ge1
      _ ≤ (π ^ 2 / 6 * ((N.totient : ℝ) / N) * (1 + Real.log (Rpar D)))
            * (1 + Real.log (z2par D)) := by
          refine mul_le_mul_of_nonneg_right hPhi ?_
          rw [hlogz2]
          positivity
      _ = π ^ 2 / 6 * ((N.totient : ℝ) / N) * (1 + L / 100) * (1 + 63/100 * L) := by
          rw [hlogR, hlogz2]
  -- exponential suppression from |γ| ≥ Λ₀
  have hexpγ : Real.exp (-|ρ.im|)
      ≤ (L * Real.exp (6/5 * lam) * (3200 * Real.exp 1 * CΓ'))⁻¹ := by
    have hpos : (0 : ℝ) < 3200 * Real.exp 1 * CΓ' := by
      have := Real.exp_pos (1 : ℝ)
      nlinarith
    have hΛ : Real.exp (Lambda0 D σ (Real.log (3200 * Real.exp 1 * CΓ')))
        = L * Real.exp (6/5 * lam) * (3200 * Real.exp 1 * CΓ') := by
      rw [Lambda0, Real.exp_add, Real.exp_add, ← hLdef, Real.exp_log hL0,
        Real.exp_log hpos]
    calc Real.exp (-|ρ.im|) = (Real.exp |ρ.im|)⁻¹ := Real.exp_neg _
      _ ≤ (Real.exp (Lambda0 D σ (Real.log (3200 * Real.exp 1 * CΓ'))))⁻¹ := by
          gcongr
      _ = _ := by rw [hΛ]
  -- numeric core
  have hπ : π ^ 2 ≤ 16 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  have he1 : (1 : ℝ) ≤ Real.exp 1 := by nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hCΓ'0 : (0 : ℝ) < CΓ' := by linarith
  have hEpos : (0 : ℝ) < Real.exp (6/5 * lam) := Real.exp_pos _
  have hnum : CΓ' * (L * Real.exp (6/5 * lam) * (3200 * Real.exp 1 * CΓ'))⁻¹
      * Real.exp (6/5 * lam) * (π ^ 2 / 6 * (1 + L / 100) * (1 + 63/100 * L))
      ≤ L / 1600 := by
    have hA : π ^ 2 / 6 * (1 + L / 100) * (1 + 63/100 * L) ≤ 2 * L ^ 2 := by
      nlinarith [hπ, Real.pi_pos, hL]
    have heq : CΓ' * (L * Real.exp (6/5 * lam) * (3200 * Real.exp 1 * CΓ'))⁻¹
        * Real.exp (6/5 * lam) * (π ^ 2 / 6 * (1 + L / 100) * (1 + 63/100 * L))
        = (π ^ 2 / 6 * (1 + L / 100) * (1 + 63/100 * L)) / (3200 * Real.exp 1 * L) := by
      field_simp
    rw [heq]
    calc (π ^ 2 / 6 * (1 + L / 100) * (1 + 63/100 * L)) / (3200 * Real.exp 1 * L)
        ≤ (2 * L ^ 2) / (3200 * 1 * L) := by
          refine div_le_div₀ (by positivity) hA (by positivity) ?_
          nlinarith
      _ = L / 1600 := by
          field_simp
          ring
  -- assemble
  rw [Epole, if_pos rfl, norm_mul, norm_mul, norm_mul]
  have hφnorm : ‖((N.totient : ℂ) / N)‖ = (N.totient : ℝ) / N := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
  rw [hφnorm]
  have h0b1 : (0 : ℝ) ≤ CΓ' * Real.exp (-|ρ.im|) := by positivity
  have h0b2 : (0 : ℝ) ≤ CΓ' * Real.exp (-|ρ.im|) * Real.exp (6/5 * lam) := by positivity
  have h0b3 : (0 : ℝ) ≤ CΓ' * Real.exp (-|ρ.im|) * Real.exp (6/5 * lam)
      * ((N.totient : ℝ) / N) := by positivity
  have hstep1 : ‖Complex.Gamma (1 - ρ)‖ * ‖((Xpar D : ℝ) : ℂ) ^ ((1 : ℂ) - ρ)‖
      * ((N.totient : ℝ) / N)
      * ‖∑ r ∈ Rset N (Rpar D),
          ((r : ℂ))⁻¹ * Mr (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) r 1‖
      ≤ CΓ' * Real.exp (-|ρ.im|) * Real.exp (6/5 * lam) * ((N.totient : ℝ) / N)
        * (π ^ 2 / 6 * ((N.totient : ℝ) / N) * (1 + L / 100) * (1 + 63/100 * L)) :=
    mul_le_mul
      (mul_le_mul
        (mul_le_mul hΓ hXnorm (norm_nonneg _) h0b1)
        le_rfl hφ0 h0b2)
      hMr (norm_nonneg _) h0b3
  refine hstep1.trans ?_
  have hstep2 : CΓ' * Real.exp (-|ρ.im|) * Real.exp (6/5 * lam) * ((N.totient : ℝ) / N)
      * (π ^ 2 / 6 * ((N.totient : ℝ) / N) * (1 + L / 100) * (1 + 63/100 * L))
      ≤ ((N.totient : ℝ) / N)
        * (CΓ' * (L * Real.exp (6/5 * lam) * (3200 * Real.exp 1 * CΓ'))⁻¹
          * Real.exp (6/5 * lam) * (π ^ 2 / 6 * (1 + L / 100) * (1 + 63/100 * L))) := by
    have hu : (0 : ℝ) ≤ 1 + L / 100 := by positivity
    have hv : (0 : ℝ) ≤ 1 + 63/100 * L := by positivity
    have hE2 : π ^ 2 / 6 * ((N.totient : ℝ) / N) * (1 + L / 100) * (1 + 63/100 * L)
        ≤ π ^ 2 / 6 * (1 + L / 100) * (1 + 63/100 * L) := by
      have h1 : π ^ 2 / 6 * ((N.totient : ℝ) / N) ≤ π ^ 2 / 6 := by
        calc π ^ 2 / 6 * ((N.totient : ℝ) / N) ≤ π ^ 2 / 6 * 1 :=
              mul_le_mul_of_nonneg_left hφ1 (by positivity)
          _ = π ^ 2 / 6 := mul_one _
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hu) hv
    have hB : CΓ' * Real.exp (-|ρ.im|)
        ≤ CΓ' * (L * Real.exp (6/5 * lam) * (3200 * Real.exp 1 * CΓ'))⁻¹ :=
      mul_le_mul_of_nonneg_left hexpγ (by linarith)
    calc CΓ' * Real.exp (-|ρ.im|) * Real.exp (6/5 * lam) * ((N.totient : ℝ) / N)
        * (π ^ 2 / 6 * ((N.totient : ℝ) / N) * (1 + L / 100) * (1 + 63/100 * L))
        = ((N.totient : ℝ) / N) * (CΓ' * Real.exp (-|ρ.im|) * Real.exp (6/5 * lam)
          * (π ^ 2 / 6 * ((N.totient : ℝ) / N) * (1 + L / 100) * (1 + 63/100 * L))) := by
          ring
      _ ≤ ((N.totient : ℝ) / N)
          * (CΓ' * (L * Real.exp (6/5 * lam) * (3200 * Real.exp 1 * CΓ'))⁻¹
            * Real.exp (6/5 * lam) * (π ^ 2 / 6 * (1 + L / 100) * (1 + 63/100 * L))) := by
          refine mul_le_mul_of_nonneg_left ?_ hφ0
          refine mul_le_mul (mul_le_mul_of_nonneg_right hB hEpos.le) hE2 ?_ ?_
          · positivity
          · have hinv : (0 : ℝ) ≤ (L * Real.exp (6/5 * lam)
              * (3200 * Real.exp 1 * CΓ'))⁻¹ := by positivity
            positivity
  refine hstep2.trans ?_
  calc ((N.totient : ℝ) / N)
      * (CΓ' * (L * Real.exp (6/5 * lam) * (3200 * Real.exp 1 * CΓ'))⁻¹
        * Real.exp (6/5 * lam) * (π ^ 2 / 6 * (1 + L / 100) * (1 + 63/100 * L)))
      ≤ ((N.totient : ℝ) / N) * (L / 1600) := mul_le_mul_of_nonneg_left hnum hφ0
    _ ≤ P1 N (Rpar D) / 8 := by linarith only [hP1]

/-- The combined content of blueprint Lemmas 4.1 (detection identity: Mellin
rectangle shift; the residue at `w = 0` is `L(ρ,χ)·M_r(ρ,χ) = 0` BECAUSE `ρ`
is a zero) and 4.2 (contour term `≤ P(1)/8` under threshold (T1)),
hypothesis-ized pending sortie Z4a′ (convexity input I1); header delta 1:
`‖F(ρ,χ) + e^{−1/X}·P(1) − E_pole(ρ,χ)‖ ≤ P(1)/8` at the detected zero `ρ`. -/
def DetectionEstimate {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (z1 z2 R X : ℝ) (ρ : ℂ) : Prop :=
  ‖Fdet χ z1 z2 R X ρ + ((Real.exp (-1 / X) * P1 N R : ℝ) : ℂ)
      - Epole χ z1 z2 R X ρ‖ ≤ P1 N R / 8

/-- **Blueprint Proposition 4.4 = the frozen Z6c statement** (routez
Z0b-density.md §12.3): at every detected zero,
`‖F(ρ,χ)‖ ≥ (ε/4)·(φ(d)/d)·log D` with `ε = 1/100`, i.e. constant `1/400`.
Hypotheses: `hdet` = Lemmas 4.1+4.2 (header delta 1), `hGamma` = I8(b),
`hP1` = I9(b), `hPhi` = I9(c); the `χ = χ₀` clause `hγ` carries Lemma 4.3's
height condition `|γ| ≥ Λ₀(σ)`. -/
theorem detector_lower_bound {N : ℕ} [NeZero N] {D σ : ℝ} (hD1 : 1 < D)
    (hL : 200 ≤ Real.log D) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    {CΓ' : ℝ} (hCΓ' : 1 ≤ CΓ')
    (hGamma : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1/2 ≤ |z.im| →
      ‖Complex.Gamma z‖ ≤ CΓ' * Real.exp (-|z.im|))
    {χ : DirichletCharacter ℂ N}
    (hP1 : (1/200) * ((N.totient : ℝ) / N) * Real.log D ≤ P1 N (Rpar D))
    (hPhi : ∑ r ∈ Rset N (Rpar D), (r.totient : ℝ) / (r : ℝ) ^ 2
      ≤ π ^ 2 / 6 * ((N.totient : ℝ) / N) * (1 + Real.log (Rpar D)))
    {ρ : ℂ} (hβ : σ ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hγ : χ = 1 → Lambda0 D σ (Real.log (3200 * Real.exp 1 * CΓ')) ≤ |ρ.im|)
    (hdet : DetectionEstimate χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ) :
    (1/400) * ((N.totient : ℝ) / N) * Real.log D
      ≤ ‖Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖ := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hP0 : 0 ≤ P1 N (Rpar D) := P1_nonneg N (Rpar D)
  -- pole bound: Lemma 4.3 when χ = χ₀, trivial otherwise
  have hEp : ‖Epole χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖
      ≤ P1 N (Rpar D) / 8 := by
    by_cases h1 : χ = 1
    · subst h1
      exact norm_Epole_le hD1 hL hσ1 hCΓ' hGamma hP1 hPhi hβ hβ1 hσ0 (hγ rfl)
    · rw [Epole_eq_zero h1, norm_zero]
      linarith only [hP0]
  -- the detection estimate, unfolded
  have hdet' : ‖Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ
      + ((Real.exp (-1 / Xpar D) * P1 N (Rpar D) : ℝ) : ℂ)
      - Epole χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖
      ≤ P1 N (Rpar D) / 8 := hdet
  -- `e^{−1/X} ≥ 3/4` (blueprint: `D ≥ D₀` makes `X` huge)
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
  have hXpos : (0 : ℝ) < Xpar D := by linarith
  have hexp : (3/4 : ℝ) ≤ Real.exp (-1 / Xpar D) := by
    have h1 : -1 / Xpar D + 1 ≤ Real.exp (-1 / Xpar D) :=
      Real.add_one_le_exp _
    have h2 : 1 / Xpar D ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) hX4
    have h3 : -1 / Xpar D = -(1 / Xpar D) := by ring
    linarith
  -- norm of the main (n = 1) term
  have hc : ‖((Real.exp (-1 / Xpar D) * P1 N (Rpar D) : ℝ) : ℂ)‖
      = Real.exp (-1 / Xpar D) * P1 N (Rpar D) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg (Real.exp_pos _).le hP0
  -- triangle inequality: `‖c‖ ≤ ‖F + c − E‖ + ‖F‖ + ‖E‖`
  set F := Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ with hFdef
  set E := Epole χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ with hEdef
  set c := ((Real.exp (-1 / Xpar D) * P1 N (Rpar D) : ℝ) : ℂ) with hcdef
  have htri : ‖c‖ ≤ ‖F + c - E‖ + ‖F‖ + ‖E‖ := by
    calc ‖c‖ = ‖((F + c - E) - F) + E‖ := by
          rw [show ((F + c - E) - F) + E = c from by ring]
      _ ≤ ‖(F + c - E) - F‖ + ‖E‖ := norm_add_le _ _
      _ ≤ (‖F + c - E‖ + ‖F‖) + ‖E‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
  -- assemble: `‖F‖ ≥ (3/4 − 1/8 − 1/8)·P(1) = P(1)/2 ≥ (1/400)·(φ/N)·log D`
  have h34 : (3/4 : ℝ) * P1 N (Rpar D)
      ≤ Real.exp (-1 / Xpar D) * P1 N (Rpar D) :=
    mul_le_mul_of_nonneg_right hexp hP0
  linarith only [htri, hc, h34, hdet', hEp, hP1]

end Detector
end Carmichael
