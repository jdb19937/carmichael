/-
Route Z, sortie Z6b: large-values estimates for character-twisted Dirichlet
polynomials (Halász–Montgomery duality + Huxley-type combination), single
modulus, building on the mean value theorem of sortie Z6a
(`Carmichael.MeanValue`).

Setup. A *spaced family* is a finite index set `s` with maps
`chi : ι → DirichletCharacter ℂ d`, `pt : ι → ℝ`, such that any two indices
carrying the SAME character have `1 ≤ |pt r - pt r'|`, and every index is a
*large value*: `V ≤ ‖∑_{n ∈ Icc 1 N} a n · χᵣ(n) · exp((-log n · tᵣ)·I)‖`.
Write `R := s.card`, `G := ∑_{n ∈ Icc 1 N} ‖a n‖²`.

Main results (all fully explicit, no `sorry`, no new axioms):

* `mean_value_chars_discrete_family` — the grouped discrete mean value
  theorem: point sets may depend on the character,
    `∑_χ ∑_{r ∈ R(χ)} ‖∑ₙ aₙ χ(n) e^{-ir log n}‖²
       ≤ 200 (N + d(T+1)) ∑ₙ (1 + log²n) ‖aₙ‖²`.

* **LV1** `large_values_mean` :
    `R·V² ≤ 300 · (1 + log N)² · (N + dT) · G`
  (mean-value/Halász count; C₁ = 300, k₁ = 2, log base `1 + log N`).

* **LV2** `large_values_dual` (duality/bilinear form step) : for a family of
  diameter `Θ` (`|pt r - pt r'| ≤ Θ`, `2 ≤ Θ`),
    `R·V² ≤ 100 · (1 + log(2 + dΘN))² · (N + R·(d·Θ)) · G`.
  ACHIEVED EXPONENTS, stated honestly: the off-diagonal Gram entry is bounded
  by `d·Θ·polylog` — the exponent of `d` is **1** (from the trivial
  complete-period bound `|∑_{period} χ| = 0`, partial period `≤ d`; the
  pinned Mathlib has no Pólya–Vinogradov, which would give `d^{1/2}`), and
  the `Θ`-dependence is **linear** (partial summation; the classical `Θ^{1/2}`
  needs van der Corput second-derivative estimates, not available).
  So the second term is `R·d·Θ`, NOT the classical `R·√(dΘN)`.

* **LV3** `large_values_huxley` :
    `R ≤ 300 · (1 + log N)² · ( G·N/V² + G²·N·(d·T)/V⁴ )`.
  ACHIEVED SHAPE, flagged loudly for the Z0a-ledger keeper: with the
  linear-in-`Θ` off-diagonal of LV2, the Huxley subdivision optimum is block
  length `Θ ≍ V²/(dG·polylog)`, giving `G²·N·(dT)/V⁴` — the same bound that
  LV1 + `V² ≤ NG` (Cauchy–Schwarz) already yields, which is how it is proved
  here. The canonical Huxley second term `G³·N·(dT)/V⁶` (d-exponent 1,
  N-exponent 1, V-exponent 6) requires the off-diagonal `√(dΘ)·polylog`,
  i.e. Pólya–Vinogradov + van der Corput; with only the trivial bounds the
  subdivision reproduces exactly the `G²(dT)/V⁴` form and adds nothing.
  Ledger impact (computed, not verified downstream): balancing
  `N^{2-2σ}` against `N^{3-4σ}(dT)` gives density coefficient
  `A(σ) = 2/(2σ-1)`, which on `σ ∈ [39/50, 1]` is `≤ 25/7 ≈ 3.571 < 9/2`,
  under the ledger's wall (`2/(2σ-1) ≤ 9/2 ⟺ σ ≥ 13/18 = 0.7222`).
  `large_values_huxley_canonical` recovers the literal `G³N(dT)/V⁶` shape
  under the extra hypothesis `V² ≤ G` (usually FALSE downstream, where
  `V² ≈ N^{2σ} > N ≈ G`; included only for shape-compatibility).

All bounds use the exponential form `exp((-log n * t) * I)` of Z6a.
-/
import Carmichael.MeanValue

namespace Carmichael
namespace LargeValues

open Complex MeasureTheory Finset intervalIntegral Filter Carmichael.MeanValue
open scoped Real ComplexConjugate Classical

/-! ### Elementary complex-exponential estimates -/

/-- `‖e^{iθ} − 1‖ ≤ |θ|`. -/
lemma norm_exp_I_sub_one_le (θ : ℝ) :
    ‖Complex.exp ((θ : ℝ) * Complex.I) - 1‖ ≤ |θ| := by
  have h : Complex.exp ((θ : ℝ) * Complex.I) - 1
      = ((Real.cos θ - 1 : ℝ) : ℂ) + (Real.sin θ : ℝ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast
    ring
  rw [h, Complex.norm_add_mul_I]
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h2 := Real.cos_two_mul_eq_one_sub (θ / 2)
    rwa [show 2 * (θ / 2) = θ by ring] at h2
  have hs : Real.sin (θ / 2) ^ 2 ≤ (θ / 2) ^ 2 := by
    calc Real.sin (θ / 2) ^ 2 = |Real.sin (θ / 2)| ^ 2 := (sq_abs _).symm
      _ ≤ |θ / 2| ^ 2 := pow_le_pow_left₀ (abs_nonneg _) Real.abs_sin_le_abs 2
      _ = (θ / 2) ^ 2 := sq_abs _
  have hpyth := Real.sin_sq_add_cos_sq θ
  calc Real.sqrt ((Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2)
      ≤ Real.sqrt (θ ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = |θ| := Real.sqrt_sq_eq_abs θ

/-- `‖e^{ia} − e^{ib}‖ ≤ |a − b|`. -/
lemma norm_exp_sub_exp_le (a b : ℝ) :
    ‖Complex.exp ((a : ℝ) * Complex.I) - Complex.exp ((b : ℝ) * Complex.I)‖
      ≤ |a - b| := by
  have h : Complex.exp ((a : ℝ) * Complex.I) - Complex.exp ((b : ℝ) * Complex.I)
      = Complex.exp ((b : ℝ) * Complex.I)
          * (Complex.exp (((a - b : ℝ)) * Complex.I) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [h, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact norm_exp_I_sub_one_le (a - b)

/-- Increment bound for the twist `n ↦ e^{-iθ log n}`:
`‖e^{-iθ log x} − e^{-iθ log y}‖ ≤ |θ| (log y − log x)` for `0 < x ≤ y`. -/
lemma norm_exp_log_sub_le {x y : ℝ} (θ : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    ‖Complex.exp ((-Real.log x * θ : ℝ) * Complex.I)
        - Complex.exp ((-Real.log y * θ : ℝ) * Complex.I)‖
      ≤ |θ| * (Real.log y - Real.log x) := by
  have hlog : Real.log x ≤ Real.log y := Real.log_le_log hx hxy
  calc ‖Complex.exp ((-Real.log x * θ : ℝ) * Complex.I)
        - Complex.exp ((-Real.log y * θ : ℝ) * Complex.I)‖
      ≤ |(-Real.log x * θ) - (-Real.log y * θ)| := norm_exp_sub_exp_le _ _
    _ = |θ| * |Real.log y - Real.log x| := by
        rw [show (-Real.log x * θ) - (-Real.log y * θ)
            = θ * (Real.log y - Real.log x) by ring, abs_mul]
    _ = |θ| * (Real.log y - Real.log x) := by
        rw [abs_of_nonneg (show (0 : ℝ) ≤ Real.log y - Real.log x by linarith)]

/-! ### The harmonic sum and separated reciprocal sums -/

/-- `∑_{e ≤ M} 1/e ≤ 1 + log M`. -/
lemma harmonic_sum_le (M : ℕ) :
    (∑ e ∈ Finset.Icc 1 M, (1 : ℝ) / e) ≤ 1 + Real.log M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · norm_num
    · rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
      have hM1 : (0 : ℝ) < M := by exact_mod_cast hM
      have hstep : (1 : ℝ) / (M + 1) ≤ Real.log (M + 1) - Real.log M := by
        have h1 : (0 : ℝ) < (M : ℝ) / (M + 1) := by positivity
        have h2 := Real.log_le_sub_one_of_pos h1
        rw [Real.log_div hM1.ne' (by positivity : ((M : ℝ) + 1) ≠ 0)] at h2
        have h3 : (M : ℝ) / (M + 1) - 1 = -(1 / (M + 1)) := by
          field_simp
          ring
        rw [h3] at h2
        linarith
      have hcast : ((M + 1 : ℕ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      linarith

/-- Reciprocal sum over 1-separated values in `[1, Θ]`:
`∑ 1/vᵢ ≤ 1 + log Θ`. -/
lemma sum_inv_sep_le {ι : Type*} (s : Finset ι) (v : ι → ℝ) (Θ : ℝ) (hΘ1 : 1 ≤ Θ)
    (h1 : ∀ i ∈ s, 1 ≤ v i) (hΘ : ∀ i ∈ s, v i ≤ Θ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ |v i - v j|) :
    (∑ i ∈ s, 1 / v i) ≤ 1 + Real.log Θ := by
  set K : ℕ := ⌊Θ⌋₊ with hK
  have hK1 : 1 ≤ K := Nat.le_floor (by exact_mod_cast hΘ1)
  have hKΘ : (K : ℝ) ≤ Θ := Nat.floor_le (by linarith)
  set φ : ι → ℕ := fun i => ⌊v i⌋₊ with hφ
  have hφ1 : ∀ i ∈ s, 1 ≤ φ i := fun i hi => Nat.le_floor (by exact_mod_cast h1 i hi)
  have hφK : ∀ i ∈ s, φ i ≤ K := fun i hi => Nat.floor_le_floor (hΘ i hi)
  have hφle : ∀ i ∈ s, (φ i : ℝ) ≤ v i := fun i hi =>
    Nat.floor_le (by linarith [h1 i hi])
  have hφlt : ∀ i ∈ s, v i < (φ i : ℝ) + 1 := fun i hi =>
    Nat.lt_floor_add_one (v i)
  have hinj : ∀ i ∈ s, ∀ j ∈ s, φ i = φ j → i = j := by
    intro i hi j hj hij
    by_contra hne
    have h1' := hsep i hi j hj hne
    have hle_i := hφle i hi
    have hlt_i := hφlt i hi
    have hle_j := hφle j hj
    have hlt_j := hφlt j hj
    rw [hij] at hle_i hlt_i
    rcases abs_cases (v i - v j) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h1' <;> linarith
  have hterm : ∀ i ∈ s, 1 / v i ≤ 1 / (φ i : ℝ) := by
    intro i hi
    have h0 : (0 : ℝ) < (φ i : ℝ) := by
      have := hφ1 i hi
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
    exact one_div_le_one_div_of_le h0 (hφle i hi)
  calc (∑ i ∈ s, 1 / v i) ≤ ∑ i ∈ s, 1 / (φ i : ℝ) := Finset.sum_le_sum hterm
    _ = ∑ k ∈ s.image φ, 1 / (k : ℝ) := by rw [Finset.sum_image hinj]
    _ ≤ ∑ k ∈ Finset.Icc 1 K, 1 / (k : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => by positivity)
        intro k hk
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hk
        exact Finset.mem_Icc.2 ⟨hφ1 i hi, hφK i hi⟩
    _ ≤ 1 + Real.log K := harmonic_sum_le K
    _ ≤ 1 + Real.log Θ := by
        have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
        linarith [Real.log_le_log hK0 hKΘ]

/-- The two-sided version: 1-separated values `θ i` with `1 ≤ |θ i| ≤ Θ`. -/
lemma sum_inv_abs_sep_le {ι : Type*} (s : Finset ι) (θ : ι → ℝ) (Θ : ℝ) (hΘ1 : 1 ≤ Θ)
    (h1 : ∀ i ∈ s, 1 ≤ |θ i|) (hΘ : ∀ i ∈ s, |θ i| ≤ Θ)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 1 ≤ |θ i - θ j|) :
    (∑ i ∈ s, 1 / |θ i|) ≤ 2 * (1 + Real.log Θ) := by
  have hsplit := Finset.sum_filter_add_sum_filter_not s (fun i => 0 < θ i)
    (fun i => 1 / |θ i|)
  have habs : ∀ i ∈ s, ∀ j ∈ s, (0 < θ i ↔ 0 < θ j) → i ≠ j →
      1 ≤ abs (abs (θ i) - abs (θ j)) := by
    intro i hi j hj hsgn hne
    have h := hsep i hi j hj hne
    have hi1 := h1 i hi
    have hj1 := h1 j hj
    rcases lt_or_ge 0 (θ i) with hip | hin
    · have hjp := hsgn.1 hip
      rw [abs_of_pos hip, abs_of_pos hjp]
      exact h
    · have hjn : ¬ (0 < θ j) := fun hjp => absurd (hsgn.2 hjp) (not_lt.2 hin)
      push Not at hjn
      rw [abs_of_nonpos hin, abs_of_nonpos hjn]
      rw [show -θ i - -θ j = -(θ i - θ j) by ring, abs_neg]
      exact h
  have hpos : (∑ i ∈ s.filter (fun i => 0 < θ i), 1 / |θ i|)
      ≤ 1 + Real.log Θ := by
    refine sum_inv_sep_le _ (fun i => |θ i|) Θ hΘ1
      (fun i hi => h1 i (Finset.mem_filter.1 hi).1)
      (fun i hi => hΘ i (Finset.mem_filter.1 hi).1) ?_
    intro i hi j hj hne
    obtain ⟨hi', hip⟩ := Finset.mem_filter.1 hi
    obtain ⟨hj', hjp⟩ := Finset.mem_filter.1 hj
    exact habs i hi' j hj' (iff_of_true hip hjp) hne
  have hneg : (∑ i ∈ s.filter (fun i => ¬ 0 < θ i), 1 / |θ i|)
      ≤ 1 + Real.log Θ := by
    refine sum_inv_sep_le _ (fun i => |θ i|) Θ hΘ1
      (fun i hi => h1 i (Finset.mem_filter.1 hi).1)
      (fun i hi => hΘ i (Finset.mem_filter.1 hi).1) ?_
    intro i hi j hj hne
    obtain ⟨hi', hip⟩ := Finset.mem_filter.1 hi
    obtain ⟨hj', hjp⟩ := Finset.mem_filter.1 hj
    exact habs i hi' j hj' (iff_of_false hip hjp) hne
  linarith [hsplit.symm.le, hsplit.le, hpos, hneg]

/-! ### The grouped discrete mean value theorem

Z6a's `mean_value_chars_discrete` uses one point set for all characters; the
large-values setup needs a point set *per character*. The Sobolev step is
per-character anyway, so we extract it (proof copied from Z6a) and re-run the
summation over characters. -/

set_option maxHeartbeats 1000000 in
/-- Per-character Sobolev window bound: for 1-separated points in `[-T, T]`,
`∑_r ‖S(r)‖² ≤ 2∫_{-(T+1)}^{T+1} ‖S‖² + ∫_{-(T+1)}^{T+1} ‖S′‖²`. -/
lemma per_char_sobolev (d : ℕ) [NeZero d] (T : ℝ) (hT0 : 0 < T) (N : ℕ) (a : ℕ → ℂ)
    (χ : DirichletCharacter ℂ d) (R : Finset ℝ)
    (hRT : ∀ r ∈ R, |r| ≤ T)
    (hsep : ∀ r ∈ R, ∀ r' ∈ R, r ≠ r' → 1 ≤ |r - r'|) :
    (∑ r ∈ R, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * r : ℝ) * Complex.I)‖ ^ 2)
      ≤ 2 * (∫ t in (-(T + 1))..(T + 1), ‖∑ n ∈ Finset.Icc 1 N,
            a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2)
        + ∫ t in (-(T + 1))..(T + 1), ‖∑ n ∈ Finset.Icc 1 N,
            (a n * ((-Real.log n : ℝ) : ℂ) * Complex.I) * χ (n : ZMod d) *
              Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2 := by
  set S : ℝ → ℂ := fun t => ∑ n ∈ Finset.Icc 1 N,
    a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I) with hSdef
  set S' : ℝ → ℂ := fun t => ∑ n ∈ Finset.Icc 1 N,
    (a n * ((-Real.log n : ℝ) : ℂ) * Complex.I) * χ (n : ZMod d) *
      Complex.exp ((-Real.log n * t : ℝ) * Complex.I) with hS'def
  have hScont : Continuous S := by
    rw [hSdef]
    refine continuous_finsetSum _ fun n _ => continuous_const.mul ?_
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
        continuous_const)
  have hS'cont : Continuous S' := by
    rw [hS'def]
    refine continuous_finsetSum _ fun n _ => continuous_const.mul ?_
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
        continuous_const)
  have hSsq : Continuous fun u : ℝ => ‖S u‖ ^ 2 := by fun_prop
  have hS'sq : Continuous fun u : ℝ => ‖S' u‖ ^ 2 := by fun_prop
  have hderiv : ∀ t : ℝ, HasDerivAt S (S' t) t := by
    intro t
    simp only [hSdef, hS'def]
    refine HasDerivAt.fun_sum fun n _ => ?_
    have h0 := (hasDerivAt_exp_mul_I (-Real.log n) t).const_mul (a n * χ (n : ZMod d))
    have hrw : a n * ((-Real.log n : ℝ) : ℂ) * Complex.I * χ (n : ZMod d) *
        Complex.exp ((-Real.log n * t : ℝ) * Complex.I)
        = a n * χ (n : ZMod d) * (((-Real.log n : ℝ) : ℂ) * Complex.I *
            Complex.exp ((-Real.log n * t : ℝ) * Complex.I)) := by ring
    rw [hrw]
    exact h0
  have hFd : ∀ t : ℝ, HasDerivAt (fun u => ‖S u‖ ^ 2)
      ((S' t * conj (S t) + S t * conj (S' t)).re) t := by
    intro t
    have hconjS : HasDerivAt (fun u => conj (S u)) (conj (S' t)) t :=
      HasDerivAt.star (hderiv t)
    have h1 : HasDerivAt (fun u => S u * conj (S u))
        (S' t * conj (S t) + S t * conj (S' t)) t := (hderiv t).mul hconjS
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
    have h3 : (fun u => (S u * conj (S u)).re) = fun u => ‖S u‖ ^ 2 := by
      funext u
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    rw [← h3]
    exact h2
  set D : ℝ → ℝ := fun t => (S' t * conj (S t) + S t * conj (S' t)).re with hDdef
  have hDcont : Continuous D := by
    rw [hDdef]
    exact Complex.continuous_re.comp
      (((hS'cont.mul (continuous_star.comp hScont)).add
        (hScont.mul (continuous_star.comp hS'cont))))
  have hDbound : ∀ u : ℝ, |D u| ≤ ‖S u‖ ^ 2 + ‖S' u‖ ^ 2 := by
    intro u
    rw [hDdef]
    calc |(S' u * conj (S u) + S u * conj (S' u)).re|
        ≤ ‖S' u * conj (S u) + S u * conj (S' u)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖S' u * conj (S u)‖ + ‖S u * conj (S' u)‖ := norm_add_le _ _
      _ = ‖S' u‖ * ‖S u‖ + ‖S u‖ * ‖S' u‖ := by
          rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
      _ ≤ ‖S u‖ ^ 2 + ‖S' u‖ ^ 2 := by nlinarith [sq_nonneg (‖S u‖ - ‖S' u‖)]
  have hpoint : ∀ r ∈ R, ‖S r‖ ^ 2
      ≤ ∫ u in (r - 1/2)..(r + 1/2), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2) := by
    intro r _
    have hCr : ∀ v ∈ Set.Icc (r - 1/2) (r + 1/2),
        ‖S r‖ ^ 2 ≤ ‖S v‖ ^ 2 + ∫ u in (r - 1/2)..(r + 1/2), |D u| := by
      intro v hv
      have hftc : (∫ u in v..r, D u) = ‖S r‖ ^ 2 - ‖S v‖ ^ 2 :=
        integral_eq_sub_of_hasDerivAt (fun u _ => hFd u) (hDcont.intervalIntegrable _ _)
      have habs1 : |∫ u in v..r, D u| ≤ |(∫ u in v..r, |D u|)| := by
        have := intervalIntegral.norm_integral_le_abs_integral_norm
          (f := D) (a := v) (b := r) (μ := volume)
        simpa [Real.norm_eq_abs] using this
      have habs2 : |(∫ u in v..r, |D u|)| ≤ ∫ u in (r - 1/2)..(r + 1/2), |D u| := by
        have hsub : Set.uIoc v r ⊆ Set.uIoc (r - 1/2) (r + 1/2) := by
          rw [Set.uIoc_of_le (by linarith : r - 1/2 ≤ r + 1/2), Set.uIoc]
          refine Set.Ioc_subset_Ioc ?_ ?_
          · exact le_min hv.1 (by linarith)
          · exact max_le hv.2 (by linarith)
        have h5 := intervalIntegral.abs_integral_mono_interval hsub
          (Eventually.of_forall fun u => abs_nonneg (D u))
          (hDcont.abs.intervalIntegrable (μ := volume) _ _)
        refine h5.trans (le_of_eq (abs_of_nonneg ?_))
        exact intervalIntegral.integral_nonneg (by linarith) fun u _ => abs_nonneg _
      have := habs1.trans habs2
      have h4 : ‖S r‖ ^ 2 - ‖S v‖ ^ 2 ≤ |∫ u in v..r, D u| := by
        rw [hftc] at *
        exact le_abs_self _
      linarith [h4.trans this]
    have hlen : (∫ v in (r - 1/2)..(r + 1/2), ‖S r‖ ^ 2) = ‖S r‖ ^ 2 := by
      rw [intervalIntegral.integral_const]
      norm_num
    have hmono : (∫ v in (r - 1/2)..(r + 1/2), ‖S r‖ ^ 2)
        ≤ ∫ v in (r - 1/2)..(r + 1/2),
            (‖S v‖ ^ 2 + ∫ u in (r - 1/2)..(r + 1/2), |D u|) := by
      refine integral_mono_on (by linarith) (intervalIntegrable_const)
        ((hSsq.add continuous_const).intervalIntegrable _ _) hCr
    have hsplit : (∫ v in (r - 1/2)..(r + 1/2),
          (‖S v‖ ^ 2 + ∫ u in (r - 1/2)..(r + 1/2), |D u|))
        = (∫ v in (r - 1/2)..(r + 1/2), ‖S v‖ ^ 2)
          + ∫ u in (r - 1/2)..(r + 1/2), |D u| := by
      rw [intervalIntegral.integral_add (hSsq.intervalIntegrable _ _)
        intervalIntegrable_const, intervalIntegral.integral_const]
      norm_num
    have hDle : (∫ u in (r - 1/2)..(r + 1/2), |D u|)
        ≤ ∫ u in (r - 1/2)..(r + 1/2), (‖S u‖ ^ 2 + ‖S' u‖ ^ 2) := by
      refine integral_mono_on (by linarith) (hDcont.abs.intervalIntegrable _ _)
        ((by fun_prop : Continuous fun u : ℝ => ‖S u‖ ^ 2 + ‖S' u‖ ^ 2).intervalIntegrable _ _)
        fun u _ => hDbound u
    have hfin : (∫ u in (r - 1/2)..(r + 1/2), (‖S u‖ ^ 2 + (‖S u‖ ^ 2 + ‖S' u‖ ^ 2)))
        = ∫ u in (r - 1/2)..(r + 1/2), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2) := by
      refine intervalIntegral.integral_congr fun u _ => ?_
      ring
    have hSS' : Continuous fun u : ℝ => ‖S u‖ ^ 2 + ‖S' u‖ ^ 2 := by fun_prop
    have hcomb : (∫ v in (r - 1/2)..(r + 1/2), ‖S v‖ ^ 2)
          + (∫ u in (r - 1/2)..(r + 1/2), (‖S u‖ ^ 2 + ‖S' u‖ ^ 2))
        = ∫ u in (r - 1/2)..(r + 1/2), (‖S u‖ ^ 2 + (‖S u‖ ^ 2 + ‖S' u‖ ^ 2)) := by
      rw [intervalIntegral.integral_add (hSsq.intervalIntegrable _ _)
        (hSS'.intervalIntegrable _ _)]
    calc ‖S r‖ ^ 2 = ∫ v in (r - 1/2)..(r + 1/2), ‖S r‖ ^ 2 := hlen.symm
      _ ≤ (∫ v in (r - 1/2)..(r + 1/2), ‖S v‖ ^ 2)
          + ∫ u in (r - 1/2)..(r + 1/2), |D u| := hmono.trans (le_of_eq hsplit)
      _ ≤ (∫ v in (r - 1/2)..(r + 1/2), ‖S v‖ ^ 2)
          + ∫ u in (r - 1/2)..(r + 1/2), (‖S u‖ ^ 2 + ‖S' u‖ ^ 2) := by linarith
      _ = ∫ u in (r - 1/2)..(r + 1/2), (‖S u‖ ^ 2 + (‖S u‖ ^ 2 + ‖S' u‖ ^ 2)) := hcomb
      _ = ∫ u in (r - 1/2)..(r + 1/2), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2) := hfin
  have hh : Continuous fun u : ℝ => 2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2 :=
    (continuous_const.mul hSsq).add hS'sq
  have hh0 : ∀ u : ℝ, 0 ≤ 2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2 := fun u => by positivity
  have hsum_r : (∑ r ∈ R, ∫ u in (r - 1/2)..(r + 1/2), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2))
      ≤ ∫ u in (-(T + 1))..(T + 1), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2) := by
    have hIoc : ∀ r ∈ R, (∫ u in (r - 1/2)..(r + 1/2), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2))
        = ∫ u in Set.Ioc (r - 1/2) (r + 1/2), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2) :=
      fun r _ => integral_of_le (by linarith)
    rw [Finset.sum_congr rfl hIoc]
    have hdisj : Set.Pairwise ↑R
        (Function.onFun Disjoint fun r : ℝ => Set.Ioc (r - 1/2) (r + 1/2)) := by
      intro r hr r' hr' hne
      have hsep' := hsep r hr r' hr' hne
      simp only [Function.onFun]
      rw [Set.Ioc_disjoint_Ioc]
      rcases abs_cases (r - r') with ⟨h1, _⟩ | ⟨h1, _⟩
      · calc min (r + 1/2) (r' + 1/2) ≤ r' + 1/2 := min_le_right _ _
          _ ≤ r - 1/2 := by linarith
          _ ≤ max (r - 1/2) (r' - 1/2) := le_max_left _ _
      · calc min (r + 1/2) (r' + 1/2) ≤ r + 1/2 := min_le_left _ _
          _ ≤ r' - 1/2 := by linarith
          _ ≤ max (r - 1/2) (r' - 1/2) := le_max_right _ _
    rw [← MeasureTheory.integral_biUnion_finset R (fun r _ => measurableSet_Ioc) hdisj
      (fun r _ => hh.integrableOn_Ioc)]
    rw [integral_of_le (by linarith : -(T + 1) ≤ T + 1)]
    refine setIntegral_mono_set hh.integrableOn_Ioc
      (Eventually.of_forall fun u => hh0 u) ?_
    refine LE.le.eventuallyLE ?_
    refine Set.iUnion₂_subset fun r hr => ?_
    have hrT := abs_le.1 (hRT r hr)
    exact Set.Ioc_subset_Ioc (by linarith [hrT.1]) (by linarith [hrT.2])
  have hsplit2 : (∫ u in (-(T + 1))..(T + 1), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2))
      = 2 * (∫ u in (-(T + 1))..(T + 1), ‖S u‖ ^ 2)
        + ∫ u in (-(T + 1))..(T + 1), ‖S' u‖ ^ 2 := by
    rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous fun u : ℝ => 2 * ‖S u‖ ^ 2).intervalIntegrable _ _)
      (hS'sq.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul]
  calc (∑ r ∈ R, ‖S r‖ ^ 2)
      ≤ ∑ r ∈ R, ∫ u in (r - 1/2)..(r + 1/2), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2) :=
        Finset.sum_le_sum hpoint
    _ ≤ ∫ u in (-(T + 1))..(T + 1), (2 * ‖S u‖ ^ 2 + ‖S' u‖ ^ 2) := hsum_r
    _ = 2 * (∫ u in (-(T + 1))..(T + 1), ‖S u‖ ^ 2)
          + ∫ u in (-(T + 1))..(T + 1), ‖S' u‖ ^ 2 := hsplit2

set_option maxHeartbeats 2000000 in
/-- **Grouped discrete mean value theorem.** Point sets may depend on the
character: for 1-separated points `R(χ) ⊆ [-T, T]` per character,

  `∑_χ ∑_{r ∈ R(χ)} ‖∑ₙ aₙ χ(n) e^{-ir log n}‖²
      ≤ 200 (N + d(T+1)) ∑ₙ (1 + log² n) ‖aₙ‖²`. -/
theorem mean_value_chars_discrete_family (d : ℕ) (hd : 0 < d) (T : ℝ) (hT : 2 ≤ T)
    (N : ℕ) (a : ℕ → ℂ) (Rfam : DirichletCharacter ℂ d → Finset ℝ)
    (hRT : ∀ χ, ∀ r ∈ Rfam χ, |r| ≤ T)
    (hsep : ∀ χ, ∀ r ∈ Rfam χ, ∀ r' ∈ Rfam χ, r ≠ r' → 1 ≤ |r - r'|) :
    (∑ χ : DirichletCharacter ℂ d, ∑ r ∈ Rfam χ, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * r : ℝ) * Complex.I)‖ ^ 2)
      ≤ 200 * ((N : ℝ) + d * (T + 1)) *
          ∑ n ∈ Finset.Icc 1 N, (1 + Real.log n ^ 2) * ‖a n‖ ^ 2 := by
  have : NeZero d := ⟨hd.ne'⟩
  have hT0 : (0 : ℝ) < T := by linarith
  have hT1 : (2 : ℝ) ≤ T + 1 := by linarith
  have hper : ∀ χ : DirichletCharacter ℂ d,
      (∑ r ∈ Rfam χ, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * r : ℝ) * Complex.I)‖ ^ 2)
      ≤ 2 * (∫ t in (-(T + 1))..(T + 1), ‖∑ n ∈ Finset.Icc 1 N,
            a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2)
        + ∫ t in (-(T + 1))..(T + 1), ‖∑ n ∈ Finset.Icc 1 N,
            (a n * ((-Real.log n : ℝ) : ℂ) * Complex.I) * χ (n : ZMod d) *
              Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2 :=
    fun χ => per_char_sobolev d T hT0 N a χ (Rfam χ) (hRT χ) (hsep χ)
  have hMV1 := mean_value_chars d hd (T + 1) hT1 N a
  have hMV2 := mean_value_chars d hd (T + 1) hT1 N
    (fun n => a n * ((-Real.log n : ℝ) : ℂ) * Complex.I)
  have hnorm2 : (∑ n ∈ Finset.Icc 1 N, ‖a n * ((-Real.log n : ℝ) : ℂ) * Complex.I‖ ^ 2)
      = ∑ n ∈ Finset.Icc 1 N, Real.log n ^ 2 * ‖a n‖ ^ 2 := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  rw [hnorm2] at hMV2
  have hC0 : (0 : ℝ) ≤ (N : ℝ) + d * (T + 1) := by positivity
  have hA0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  have hB0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, Real.log n ^ 2 * ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  have hexpand : (∑ n ∈ Finset.Icc 1 N, (1 + Real.log n ^ 2) * ‖a n‖ ^ 2)
      = (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)
        + ∑ n ∈ Finset.Icc 1 N, Real.log n ^ 2 * ‖a n‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  calc (∑ χ : DirichletCharacter ℂ d, ∑ r ∈ Rfam χ, ‖∑ n ∈ Finset.Icc 1 N,
        a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * r : ℝ) * Complex.I)‖ ^ 2)
      ≤ ∑ χ : DirichletCharacter ℂ d,
          (2 * (∫ t in (-(T + 1))..(T + 1), ‖∑ n ∈ Finset.Icc 1 N,
              a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2)
            + ∫ t in (-(T + 1))..(T + 1), ‖∑ n ∈ Finset.Icc 1 N,
                (a n * ((-Real.log n : ℝ) : ℂ) * Complex.I) * χ (n : ZMod d) *
                  Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2) :=
        Finset.sum_le_sum fun χ _ => hper χ
    _ = 2 * (∑ χ : DirichletCharacter ℂ d, ∫ t in (-(T + 1))..(T + 1),
            ‖∑ n ∈ Finset.Icc 1 N,
              a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2)
        + ∑ χ : DirichletCharacter ℂ d, ∫ t in (-(T + 1))..(T + 1),
            ‖∑ n ∈ Finset.Icc 1 N,
              (a n * ((-Real.log n : ℝ) : ℂ) * Complex.I) * χ (n : ZMod d) *
                Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 2 * (100 * ((N : ℝ) + d * (T + 1)) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)
        + 100 * ((N : ℝ) + d * (T + 1)) *
            ∑ n ∈ Finset.Icc 1 N, Real.log n ^ 2 * ‖a n‖ ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hMV1 (by norm_num)) hMV2
    _ ≤ 200 * ((N : ℝ) + d * (T + 1)) *
          ∑ n ∈ Finset.Icc 1 N, (1 + Real.log n ^ 2) * ‖a n‖ ^ 2 := by
        rw [hexpand]
        nlinarith [mul_nonneg hC0 hB0, mul_nonneg hC0 hA0]

/-! ### LV1: the mean-value large-values count -/

/-- **LV1 (mean-value/Halász count).** For a spaced family (1-separation only
among equal characters) of large values in `[-T, T]`,

  `R · V² ≤ 300 · (1 + log N)² · (N + d·T) · G`.

Explicit constants: `C₁ = 300`, `k₁ = 2`. -/
theorem large_values_mean {ι : Type*} (d : ℕ) (hd : 0 < d) (T : ℝ) (hT : 2 ≤ T)
    (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) (V : ℝ) (hV : 0 ≤ V)
    (s : Finset ι) (chi : ι → DirichletCharacter ℂ d) (pt : ι → ℝ)
    (hpt : ∀ r ∈ s, |pt r| ≤ T)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → chi r = chi r' → 1 ≤ |pt r - pt r'|)
    (hlarge : ∀ r ∈ s, V ≤ ‖∑ n ∈ Finset.Icc 1 N,
        a n * (chi r) (n : ZMod d) * Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I)‖) :
    (s.card : ℝ) * V ^ 2 ≤ 300 * (1 + Real.log N) ^ 2 * ((N : ℝ) + d * T) *
      ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have : NeZero d := ⟨hd.ne'⟩
  set Rfam : DirichletCharacter ℂ d → Finset ℝ :=
    fun χ => (s.filter fun r => chi r = χ).image pt with hRfam
  -- fibers: `pt` is injective on each fiber
  have hinj : ∀ χ : DirichletCharacter ℂ d, ∀ r ∈ s.filter (fun r => chi r = χ),
      ∀ r' ∈ s.filter (fun r => chi r = χ), pt r = pt r' → r = r' := by
    intro χ r hr r' hr' hpteq
    obtain ⟨hrs, hrχ⟩ := Finset.mem_filter.1 hr
    obtain ⟨hr's, hr'χ⟩ := Finset.mem_filter.1 hr'
    by_contra hne
    have h1 := hsep r hrs r' hr's hne (hrχ.trans hr'χ.symm)
    rw [hpteq, sub_self, abs_zero] at h1
    linarith
  -- regroup the family sum by character
  have hgroup : (∑ r ∈ s, ‖∑ n ∈ Finset.Icc 1 N,
        a n * (chi r) (n : ZMod d) *
          Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I)‖ ^ 2)
      = ∑ χ : DirichletCharacter ℂ d, ∑ t ∈ Rfam χ, ‖∑ n ∈ Finset.Icc 1 N,
          a n * χ (n : ZMod d) * Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2 := by
    rw [← Finset.sum_fiberwise s chi (fun r => ‖∑ n ∈ Finset.Icc 1 N,
      a n * (chi r) (n : ZMod d) *
        Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I)‖ ^ 2)]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [hRfam, Finset.sum_image (hinj χ)]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [(Finset.mem_filter.1 hr).2]
  -- hypotheses for the grouped MVT
  have hRT' : ∀ χ : DirichletCharacter ℂ d, ∀ t ∈ Rfam χ, |t| ≤ T := by
    intro χ t ht
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 ht
    exact hpt r (Finset.mem_filter.1 hr).1
  have hsep' : ∀ χ : DirichletCharacter ℂ d, ∀ t ∈ Rfam χ, ∀ t' ∈ Rfam χ,
      t ≠ t' → 1 ≤ |t - t'| := by
    intro χ t ht t' ht' hne
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 ht
    obtain ⟨r', hr', rfl⟩ := Finset.mem_image.1 ht'
    obtain ⟨hrs, hrχ⟩ := Finset.mem_filter.1 hr
    obtain ⟨hr's, hr'χ⟩ := Finset.mem_filter.1 hr'
    exact hsep r hrs r' hr's (fun h => hne (by rw [h])) (hrχ.trans hr'χ.symm)
  -- count against the grouped MVT
  have hcount : (s.card : ℝ) * V ^ 2 ≤ ∑ r ∈ s, ‖∑ n ∈ Finset.Icc 1 N,
      a n * (chi r) (n : ZMod d) *
        Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I)‖ ^ 2 := by
    calc (s.card : ℝ) * V ^ 2 = ∑ _r ∈ s, V ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun r hr => pow_le_pow_left₀ hV (hlarge r hr) 2
  have hMVT := mean_value_chars_discrete_family d hd T hT N a Rfam hRT' hsep'
  -- weight comparison: `1 + log² n ≤ (1 + log N)²` on `[1, N]`
  have hwt : (∑ n ∈ Finset.Icc 1 N, (1 + Real.log n ^ 2) * ‖a n‖ ^ 2)
      ≤ (1 + Real.log N) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.1 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlogn : Real.log n ≤ Real.log N :=
      Real.log_le_log hn0 (by exact_mod_cast hnN)
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hfac : 1 + Real.log n ^ 2 ≤ (1 + Real.log N) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hfac (by positivity)
  -- size comparison: `N + d(T+1) ≤ (3/2)(N + dT)`
  have hsz : (N : ℝ) + d * (T + 1) ≤ 3 / 2 * ((N : ℝ) + d * T) := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hW0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, (1 + Real.log n ^ 2) * ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  have hG0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  have hL0 : (0 : ℝ) ≤ (1 + Real.log N) ^ 2 := sq_nonneg _
  have hNT0 : (0 : ℝ) ≤ (N : ℝ) + d * T := by positivity
  calc (s.card : ℝ) * V ^ 2
      ≤ ∑ r ∈ s, ‖∑ n ∈ Finset.Icc 1 N,
          a n * (chi r) (n : ZMod d) *
            Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I)‖ ^ 2 := hcount
    _ = ∑ χ : DirichletCharacter ℂ d, ∑ t ∈ Rfam χ, ‖∑ n ∈ Finset.Icc 1 N,
          a n * χ (n : ZMod d) *
            Complex.exp ((-Real.log n * t : ℝ) * Complex.I)‖ ^ 2 := hgroup
    _ ≤ 200 * ((N : ℝ) + d * (T + 1)) *
          ∑ n ∈ Finset.Icc 1 N, (1 + Real.log n ^ 2) * ‖a n‖ ^ 2 := hMVT
    _ ≤ 200 * (3 / 2 * ((N : ℝ) + d * T)) *
          ∑ n ∈ Finset.Icc 1 N, (1 + Real.log n ^ 2) * ‖a n‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ hW0
        exact mul_le_mul_of_nonneg_left hsz (by norm_num)
    _ = 300 * ((N : ℝ) + d * T) *
          ∑ n ∈ Finset.Icc 1 N, (1 + Real.log n ^ 2) * ‖a n‖ ^ 2 := by ring
    _ ≤ 300 * ((N : ℝ) + d * T) *
          ((1 + Real.log N) ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hwt (by positivity)
    _ = 300 * (1 + Real.log N) ^ 2 * ((N : ℝ) + d * T) *
          ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by ring

/-! ### Character sums: the trivial complete-period bound

The pinned Mathlib has no Pólya–Vinogradov; sortie Z4a confirmed this. We use
the trivial bound: a nontrivial character sums to `0` over a complete period,
so every partial sum has norm `≤ d`. -/

/-- Conjugation of a Dirichlet character value is the (complex) inverse —
on non-units both sides are `0`. -/
lemma conj_char_eq_cinv {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (y : ZMod d) :
    conj (χ y) = (χ y)⁻¹ := by
  by_cases hy : IsUnit y
  · have hnorm : ‖χ y‖ = 1 := by
      have h2 := χ.unit_norm_eq_one hy.unit
      rwa [IsUnit.unit_spec] at h2
    exact (Complex.inv_eq_conj hnorm).symm
  · rw [χ.map_nonunit hy]
    simp

/-- `χ(y) · conj(χ'(y)) = (χ · χ'⁻¹)(y)` pointwise. -/
lemma char_mul_conj_eq {d : ℕ} [NeZero d] (χ χ' : DirichletCharacter ℂ d) (y : ZMod d) :
    χ y * conj (χ' y) = (χ * χ'⁻¹) y := by
  rw [MulChar.mul_apply, MulChar.inv_apply_eq_inv', conj_char_eq_cinv]

/-- Orthogonality over the period: `∑_{x mod d} χ(x) conj(χ'(x)) = 0` for
distinct characters. -/
lemma sum_univ_char_mul_conj {d : ℕ} [NeZero d] {χ χ' : DirichletCharacter ℂ d}
    (h : χ ≠ χ') : (∑ x : ZMod d, χ x * conj (χ' x)) = 0 := by
  have h1 : (χ * χ'⁻¹) ≠ 1 := fun hc => h (by rwa [mul_inv_eq_one] at hc)
  calc (∑ x : ZMod d, χ x * conj (χ' x)) = ∑ x : ZMod d, (χ * χ'⁻¹) x :=
        Finset.sum_congr rfl fun x _ => char_mul_conj_eq χ χ' x
    _ = 0 := MulChar.sum_eq_zero_of_ne_one h1

/-- `Icc 1 N = Ioc 0 N` in `ℕ`. -/
lemma Icc_one_eq_Ioc_zero (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_Ioc]
  omega

/-- A block of `d` consecutive integers covers each residue mod `d` once. -/
lemma sum_block_zmod {d : ℕ} [NeZero d] (g : ZMod d → ℂ) (k : ℕ) :
    (∑ n ∈ Finset.Ioc k (k + d), g (n : ZMod d)) = ∑ x : ZMod d, g x := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have h1 : Finset.Ioc k (k + d) = Finset.Ico (k + 1) (k + 1 + d) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ico]
    omega
  rw [h1, Finset.sum_Ico_eq_sum_range]
  have h2 : k + 1 + d - (k + 1) = d := by omega
  rw [h2]
  have h3 : ∀ j ∈ Finset.range d, g ((k + 1 + j : ℕ) : ZMod d)
      = g ((k + 1 : ℕ) + (j : ZMod d)) := by
    intro j _
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl h3]
  have h4 : (∑ j ∈ Finset.range d, g (((k + 1 : ℕ) : ZMod d) + (j : ZMod d)))
      = ∑ x : ZMod d, g (((k + 1 : ℕ) : ZMod d) + x) := by
    refine Finset.sum_nbij' (fun j => ((j : ℕ) : ZMod d)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
    · intro j _
      exact Finset.mem_univ _
    · intro x _
      exact Finset.mem_range.2 (ZMod.val_lt x)
    · intro j hj
      exact ZMod.val_cast_of_lt (Finset.mem_range.1 hj)
    · intro x _
      exact ZMod.natCast_rightInverse x
    · intro j _
      rfl
  rw [h4]
  exact Fintype.sum_equiv (Equiv.addLeft (((k + 1 : ℕ) : ZMod d))) _ _ fun x => rfl

/-- Trivial partial-sum bound: if `g : ZMod d → ℂ` has zero mean and values of
norm `≤ 1`, then every partial sum `∑_{0 < n ≤ u} g(n mod d)` has norm `≤ d`. -/
lemma partial_sum_zmod_le {d : ℕ} [NeZero d] (g : ZMod d → ℂ)
    (hg0 : (∑ x : ZMod d, g x) = 0) (hg1 : ∀ x, ‖g x‖ ≤ 1) :
    ∀ u : ℕ, ‖∑ n ∈ Finset.Ioc 0 u, g (n : ZMod d)‖ ≤ d := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  intro u
  induction u using Nat.strong_induction_on with
  | _ u ih =>
    by_cases hu : u ≤ d
    · calc ‖∑ n ∈ Finset.Ioc 0 u, g (n : ZMod d)‖
          ≤ ∑ n ∈ Finset.Ioc 0 u, ‖g (n : ZMod d)‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Ioc 0 u, (1 : ℝ) := Finset.sum_le_sum fun n _ => hg1 _
        _ = ((Finset.Ioc 0 u).card : ℝ) := by rw [Finset.sum_const]; simp
        _ ≤ d := by
            rw [Nat.card_Ioc]
            exact_mod_cast hu
    · push Not at hu
      have hsplit : (∑ n ∈ Finset.Ioc 0 (u - d), g (n : ZMod d))
            + ∑ n ∈ Finset.Ioc (u - d) u, g (n : ZMod d)
          = ∑ n ∈ Finset.Ioc 0 u, g (n : ZMod d) :=
        Finset.sum_Ioc_consecutive _ (by omega) (by omega)
      have hblock : (∑ n ∈ Finset.Ioc (u - d) u, g (n : ZMod d)) = 0 := by
        have h1 : u = u - d + d := by omega
        rw [show Finset.Ioc (u - d) u = Finset.Ioc (u - d) (u - d + d) by rw [← h1]]
        rw [sum_block_zmod g (u - d)]
        exact hg0
      have h2 : (∑ n ∈ Finset.Ioc 0 u, g (n : ZMod d))
          = ∑ n ∈ Finset.Ioc 0 (u - d), g (n : ZMod d) := by
        rw [← hsplit, hblock, add_zero]
      rw [h2]
      exact ih (u - d) (by omega)

/-! ### Discrete Abel summation and the twisted nonprincipal sum -/

/-- Discrete summation by parts on `[1, N]`. -/
lemma abel_summation_Icc (f w : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, f n * w n)
      = (∑ n ∈ Finset.Icc 1 N, f n) * w N
        + ∑ k ∈ Finset.Icc 1 (N - 1),
            (∑ n ∈ Finset.Icc 1 k, f n) * (w k - w (k + 1)) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN1 ih =>
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    have hm : m + 1 + 1 - 1 = m + 1 := by omega
    have hm' : m + 1 - 1 = m := by omega
    rw [hm] at *
    rw [hm'] at ih
    have hstep1 : (∑ n ∈ Finset.Icc 1 (m + 1 + 1), f n * w n)
        = (∑ n ∈ Finset.Icc 1 (m + 1), f n * w n) + f (m + 1 + 1) * w (m + 1 + 1) :=
      Finset.sum_Icc_succ_top (by omega) _
    have hstep2 : (∑ n ∈ Finset.Icc 1 (m + 1 + 1), f n)
        = (∑ n ∈ Finset.Icc 1 (m + 1), f n) + f (m + 1 + 1) :=
      Finset.sum_Icc_succ_top (by omega) f
    have hstep3 : (∑ k ∈ Finset.Icc 1 (m + 1),
          (∑ n ∈ Finset.Icc 1 k, f n) * (w k - w (k + 1)))
        = (∑ k ∈ Finset.Icc 1 m, (∑ n ∈ Finset.Icc 1 k, f n) * (w k - w (k + 1)))
          + (∑ n ∈ Finset.Icc 1 (m + 1), f n) * (w (m + 1) - w (m + 1 + 1)) :=
      Finset.sum_Icc_succ_top (by omega) _
    rw [hstep1, hstep2, hstep3, ih]
    ring

/-- Telescoping: `∑_{1 ≤ k ≤ N-1} (log(k+1) − log k) = log N`. -/
lemma telescope_log_sum (N : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.Icc 1 (N - 1), (Real.log ((k : ℝ) + 1) - Real.log k))
      = Real.log N := by
  have h1 : Finset.Icc 1 (N - 1) = Finset.Ico 1 N := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [h1, Finset.sum_Ico_eq_sum_range]
  have h2 : ∀ j ∈ Finset.range (N - 1),
      (Real.log (((1 + j : ℕ) : ℝ) + 1) - Real.log ((1 + j : ℕ) : ℝ))
      = Real.log ((1 + (j + 1) : ℕ) : ℝ) - Real.log ((1 + j : ℕ) : ℝ) := by
    intro j _
    have h3 : ((1 + j : ℕ) : ℝ) + 1 = ((1 + (j + 1) : ℕ) : ℝ) := by push_cast; ring
    rw [h3]
  rw [Finset.sum_congr rfl h2,
    Finset.sum_range_sub (f := fun j => Real.log ((1 + j : ℕ) : ℝ))]
  rw [show 1 + (N - 1) = N by omega]
  norm_num

/-- **Nonprincipal twisted character sum, trivial bound**: for `χ ≠ χ'`,
`‖∑_{n ≤ N} χ(n) conj(χ'(n)) e^{-iθ log n}‖ ≤ d (1 + |θ| log N)`.
(The classical Pólya–Vinogradov `√d log d` is not in the pinned Mathlib;
this is the complete-period bound plus partial summation.) -/
lemma nonprincipal_twisted_sum_le {d : ℕ} [NeZero d] {χ χ' : DirichletCharacter ℂ d}
    (h : χ ≠ χ') (θ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d) * conj (χ' (n : ZMod d)) *
        Complex.exp ((-Real.log n * θ : ℝ) * Complex.I)‖
      ≤ d * (1 + |θ| * Real.log N) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  set g : ZMod d → ℂ := fun x => χ x * conj (χ' x) with hg
  set f : ℕ → ℂ := fun n => g (n : ZMod d) with hf
  set w : ℕ → ℂ := fun n => Complex.exp ((-Real.log n * θ : ℝ) * Complex.I) with hw
  have hg1 : ∀ x, ‖g x‖ ≤ 1 := by
    intro x
    rw [hg]
    calc ‖χ x * conj (χ' x)‖ = ‖χ x‖ * ‖χ' x‖ := by
          rw [norm_mul, Complex.norm_conj]
      _ ≤ 1 * 1 := mul_le_mul (χ.norm_le_one x) (χ'.norm_le_one x)
          (norm_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  have hpartial : ∀ k : ℕ, ‖∑ n ∈ Finset.Icc 1 k, f n‖ ≤ d := by
    intro k
    rw [Icc_one_eq_Ioc_zero]
    exact partial_sum_zmod_le g (sum_univ_char_mul_conj h) hg1 k
  have hwnorm : ∀ k : ℕ, ‖w k‖ = 1 := fun k => Complex.norm_exp_ofReal_mul_I _
  have hincr : ∀ k : ℕ, 1 ≤ k →
      ‖w k - w (k + 1)‖ ≤ |θ| * (Real.log ((k : ℝ) + 1) - Real.log k) := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have h1 := norm_exp_log_sub_le (x := (k : ℝ)) (y := (k : ℝ) + 1) θ hk0 (by linarith)
    rw [hw]
    have h2 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    simpa [h2] using h1
  calc ‖∑ n ∈ Finset.Icc 1 N, f n * w n‖
      = ‖(∑ n ∈ Finset.Icc 1 N, f n) * w N
          + ∑ k ∈ Finset.Icc 1 (N - 1), (∑ n ∈ Finset.Icc 1 k, f n) * (w k - w (k + 1))‖ := by
        rw [abel_summation_Icc f w N hN]
    _ ≤ ‖(∑ n ∈ Finset.Icc 1 N, f n) * w N‖
        + ‖∑ k ∈ Finset.Icc 1 (N - 1), (∑ n ∈ Finset.Icc 1 k, f n) * (w k - w (k + 1))‖ :=
        norm_add_le _ _
    _ ≤ (d : ℝ) + ∑ k ∈ Finset.Icc 1 (N - 1),
          (d : ℝ) * (|θ| * (Real.log ((k : ℝ) + 1) - Real.log k)) := by
        refine add_le_add ?_ ?_
        · rw [norm_mul, hwnorm N, mul_one]
          exact hpartial N
        · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
          obtain ⟨hk1, _⟩ := Finset.mem_Icc.1 hk
          rw [norm_mul]
          exact mul_le_mul (hpartial k) (hincr k hk1) (norm_nonneg _)
            (by positivity)
    _ = (d : ℝ) + (d : ℝ) * |θ| *
          ∑ k ∈ Finset.Icc 1 (N - 1), (Real.log ((k : ℝ) + 1) - Real.log k) := by
        rw [Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = (d : ℝ) + (d : ℝ) * |θ| * Real.log N := by rw [telescope_log_sum N hN]
    _ = d * (1 + |θ| * Real.log N) := by ring

/-! ### The oscillatory sum `∑ n^{-iθ}`: integral comparison -/

/-- The twist as a function of a real variable. -/
noncomputable def exptwist (θ : ℝ) : ℝ → ℂ := fun u =>
  Complex.exp ((-Real.log u * θ : ℝ) * Complex.I)

lemma continuousOn_exptwist (θ : ℝ) :
    ContinuousOn (exptwist θ) {u : ℝ | u ≠ 0} := by
  unfold exptwist
  refine Complex.continuous_exp.comp_continuousOn ?_
  refine ContinuousOn.mul ?_ continuousOn_const
  refine Complex.continuous_ofReal.comp_continuousOn ?_
  exact (Real.continuousOn_log.neg.mul continuousOn_const)

lemma exptwist_intervalIntegrable (θ : ℝ) {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) :
    IntervalIntegrable (exptwist θ) volume x y := by
  refine ContinuousOn.intervalIntegrable ((continuousOn_exptwist θ).mono ?_)
  rw [Set.uIcc_of_le hxy]
  intro u hu
  have h1 := (Set.mem_Icc.1 hu).1
  show u ≠ 0
  intro h0
  rw [h0] at h1
  linarith

lemma norm_exptwist (θ : ℝ) (u : ℝ) : ‖exptwist θ u‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The primitive of the twist: `F(u) = u · e^{-iθ log u} / (1 - iθ)` has
derivative `e^{-iθ log u}` for `u > 0`. -/
lemma hasDerivAt_exptwist_primitive (θ : ℝ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun v : ℝ => (v : ℂ) * exptwist θ v / (1 - (θ : ℂ) * Complex.I))
      (exptwist θ u) u := by
  have hc : (1 : ℂ) - (θ : ℂ) * Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
  have hlog := Real.hasDerivAt_log hu.ne'
  have h1 : HasDerivAt (fun v : ℝ => -Real.log v * θ) (-u⁻¹ * θ) u :=
    hlog.neg.mul_const θ
  have h2 : HasDerivAt (fun v : ℝ => ((-Real.log v * θ : ℝ) : ℂ))
      (((-u⁻¹ * θ : ℝ) : ℂ)) u :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u h1
  have h3 : HasDerivAt (fun v : ℝ => ((-Real.log v * θ : ℝ) : ℂ) * Complex.I)
      (((-u⁻¹ * θ : ℝ) : ℂ) * Complex.I) u := h2.mul_const Complex.I
  have h4 : HasDerivAt (exptwist θ)
      (exptwist θ u * (((-u⁻¹ * θ : ℝ) : ℂ) * Complex.I)) u := h3.cexp
  have h5 := HasDerivAt.ofReal_comp (hasDerivAt_id u)
  have h6 := (h5.mul h4).div_const ((1 : ℂ) - (θ : ℂ) * Complex.I)
  simp only [id_eq, Complex.ofReal_one, one_mul] at h6
  have hu' : ((u : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hDeq : exptwist θ u + ((u : ℝ) : ℂ) *
        (exptwist θ u * (((-u⁻¹ * θ : ℝ) : ℂ) * Complex.I))
      = exptwist θ u * ((1 : ℂ) - (θ : ℂ) * Complex.I) := by
    push_cast
    field_simp
    ring
  rw [hDeq, mul_div_assoc, div_self hc, mul_one] at h6
  exact h6

/-- **Oscillatory partial-sum bound.** For `1 ≤ |θ|`,
`‖∑_{m ≤ M} e^{-iθ log m}‖ ≤ (M+2)/|θ| + |θ| log(M+1)`. -/
lemma exp_twist_partial_sum_le (θ : ℝ) (hθ : 1 ≤ |θ|) (M : ℕ) :
    ‖∑ m ∈ Finset.Icc 1 M, Complex.exp ((-Real.log m * θ : ℝ) * Complex.I)‖
      ≤ ((M : ℝ) + 2) / |θ| + |θ| * Real.log ((M : ℝ) + 1) := by
  have hθ0 : (0 : ℝ) < |θ| := by linarith
  set f : ℝ → ℂ := exptwist θ with hf
  set F : ℝ → ℂ := fun v : ℝ => (v : ℂ) * exptwist θ v / (1 - (θ : ℂ) * Complex.I)
    with hF
  -- norm of the constant `1 - iθ` dominates `|θ|`
  have hcnorm : |θ| ≤ ‖(1 : ℂ) - (θ : ℂ) * Complex.I‖ := by
    have h1 : (1 : ℂ) - (θ : ℂ) * Complex.I
        = ((1 : ℝ) : ℂ) + ((-θ : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h1, Complex.norm_add_mul_I]
    calc |θ| = Real.sqrt (θ ^ 2) := (Real.sqrt_sq_eq_abs θ).symm
      _ ≤ Real.sqrt ((1 : ℝ) ^ 2 + (-θ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
  have hFnorm : ∀ u : ℝ, 0 ≤ u → ‖F u‖ ≤ u / |θ| := by
    intro u hu
    have hc0 : (0 : ℝ) < ‖(1 : ℂ) - (θ : ℂ) * Complex.I‖ := lt_of_lt_of_le hθ0 hcnorm
    have h1 : ‖F u‖ = u / ‖(1 : ℂ) - (θ : ℂ) * Complex.I‖ := by
      simp only [hF]
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_exptwist,
        mul_one, abs_of_nonneg hu]
    rw [h1, div_le_div_iff₀ hc0 hθ0]
    nlinarith
  -- FTC on [1, M+1]
  have hM1 : (1 : ℝ) ≤ (M : ℝ) + 1 := by
    have := (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
    linarith
  have hFTC : (∫ u in (1 : ℝ)..((M : ℝ) + 1), f u) = F ((M : ℝ) + 1) - F 1 := by
    refine integral_eq_sub_of_hasDerivAt (fun u hu => ?_)
      (exptwist_intervalIntegrable θ le_rfl hM1)
    rw [Set.uIcc_of_le hM1] at hu
    exact hasDerivAt_exptwist_primitive θ (by linarith [(Set.mem_Icc.1 hu).1])
  -- split the integral over adjacent unit intervals
  have hadj : (∑ k ∈ Finset.range M,
        ∫ u in (((k : ℕ) : ℝ) + 1)..(((k + 1 : ℕ) : ℝ) + 1), f u)
      = ∫ u in (1 : ℝ)..((M : ℝ) + 1), f u := by
    have h1 := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => ((k : ℝ) + 1)) (n := M) (f := f) (μ := volume) ?_
    · have h2 : (((0 : ℕ) : ℝ) + 1) = (1 : ℝ) := by norm_num
      rw [h2] at h1
      exact h1
    · intro k _
      refine exptwist_intervalIntegrable θ ?_ ?_
      · have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
        linarith
      · push_cast
        linarith
  -- rewrite the adjacent-intervals sum over `Icc 1 M`
  have hreindex : (∑ m ∈ Finset.Icc 1 M, ∫ u in ((m : ℝ))..((m : ℝ) + 1), f u)
      = ∑ k ∈ Finset.range M,
          ∫ u in (((k : ℕ) : ℝ) + 1)..(((k + 1 : ℕ) : ℝ) + 1), f u := by
    have h1 : Finset.Icc 1 M = Finset.Ico 1 (M + 1) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [h1, Finset.sum_Ico_eq_sum_range]
    have h2 : M + 1 - 1 = M := by omega
    rw [h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : ((1 + k : ℕ) : ℝ) = ((k : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e1]
    have e3 : (((k : ℕ) : ℝ) + 1) + 1 = ((k + 1 : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e3]
  -- the sum-vs-integral decomposition
  have hdecomp : (∑ m ∈ Finset.Icc 1 M,
        Complex.exp ((-Real.log m * θ : ℝ) * Complex.I))
      = (∫ u in (1 : ℝ)..((M : ℝ) + 1), f u)
        + ∑ m ∈ Finset.Icc 1 M,
            (Complex.exp ((-Real.log m * θ : ℝ) * Complex.I)
              - ∫ u in ((m : ℝ))..((m : ℝ) + 1), f u) := by
    rw [Finset.sum_sub_distrib, hreindex, hadj]
    ring
  -- per-term error bound
  have hterm : ∀ m ∈ Finset.Icc 1 M,
      ‖Complex.exp ((-Real.log m * θ : ℝ) * Complex.I)
          - ∫ u in ((m : ℝ))..((m : ℝ) + 1), f u‖
        ≤ |θ| * (Real.log ((m : ℝ) + 1) - Real.log m) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hii := exptwist_intervalIntegrable θ hmR (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)
    have hconst : (∫ _u in ((m : ℝ))..((m : ℝ) + 1),
        Complex.exp ((-Real.log m * θ : ℝ) * Complex.I))
        = Complex.exp ((-Real.log m * θ : ℝ) * Complex.I) := by
      rw [intervalIntegral.integral_const]
      simp
    have hsub : Complex.exp ((-Real.log m * θ : ℝ) * Complex.I)
          - (∫ u in ((m : ℝ))..((m : ℝ) + 1), f u)
        = ∫ u in ((m : ℝ))..((m : ℝ) + 1),
            (Complex.exp ((-Real.log m * θ : ℝ) * Complex.I) - f u) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hii, hconst]
    rw [hsub]
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (m : ℝ)) (b := (m : ℝ) + 1)
      (C := |θ| * (Real.log ((m : ℝ) + 1) - Real.log m))
      (f := fun u => Complex.exp ((-Real.log m * θ : ℝ) * Complex.I) - f u) ?_
    · calc ‖∫ u in ((m : ℝ))..((m : ℝ) + 1),
            (Complex.exp ((-Real.log m * θ : ℝ) * Complex.I) - f u)‖
          ≤ |θ| * (Real.log ((m : ℝ) + 1) - Real.log m) * |(m : ℝ) + 1 - m| := hbound
        _ = |θ| * (Real.log ((m : ℝ) + 1) - Real.log m) := by
            rw [show (m : ℝ) + 1 - m = 1 by ring, abs_one, mul_one]
    · intro u hu
      rw [Set.uIoc_of_le (by linarith : (m : ℝ) ≤ (m : ℝ) + 1)] at hu
      obtain ⟨hu1, hu2⟩ := Set.mem_Ioc.1 hu
      have hu0 : (0 : ℝ) < u := by linarith
      calc ‖Complex.exp ((-Real.log m * θ : ℝ) * Complex.I) - f u‖
          ≤ |θ| * (Real.log u - Real.log m) :=
            norm_exp_log_sub_le θ hm0 hu1.le
        _ ≤ |θ| * (Real.log ((m : ℝ) + 1) - Real.log m) := by
            have := Real.log_le_log hu0 hu2
            have h0 : (0 : ℝ) ≤ |θ| := abs_nonneg θ
            nlinarith
  -- telescoping the per-term bounds
  have htel : (∑ m ∈ Finset.Icc 1 M, |θ| * (Real.log ((m : ℝ) + 1) - Real.log m))
      = |θ| * Real.log ((M : ℝ) + 1) := by
    rw [← Finset.mul_sum]
    congr 1
    have h1 := telescope_log_sum (M + 1) (by omega)
    have h2 : M + 1 - 1 = M := by omega
    rw [h2] at h1
    rw [h1]
    push_cast
    ring
  -- assemble
  calc ‖∑ m ∈ Finset.Icc 1 M, Complex.exp ((-Real.log m * θ : ℝ) * Complex.I)‖
      = ‖(∫ u in (1 : ℝ)..((M : ℝ) + 1), f u)
          + ∑ m ∈ Finset.Icc 1 M,
              (Complex.exp ((-Real.log m * θ : ℝ) * Complex.I)
                - ∫ u in ((m : ℝ))..((m : ℝ) + 1), f u)‖ := by rw [← hdecomp]
    _ ≤ ‖∫ u in (1 : ℝ)..((M : ℝ) + 1), f u‖
        + ‖∑ m ∈ Finset.Icc 1 M,
            (Complex.exp ((-Real.log m * θ : ℝ) * Complex.I)
              - ∫ u in ((m : ℝ))..((m : ℝ) + 1), f u)‖ := norm_add_le _ _
    _ ≤ (((M : ℝ) + 1) / |θ| + 1 / |θ|)
        + ∑ m ∈ Finset.Icc 1 M, |θ| * (Real.log ((m : ℝ) + 1) - Real.log m) := by
        refine add_le_add ?_ ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm))
        rw [hFTC]
        calc ‖F ((M : ℝ) + 1) - F 1‖ ≤ ‖F ((M : ℝ) + 1)‖ + ‖F 1‖ := norm_sub_le _ _
          _ ≤ ((M : ℝ) + 1) / |θ| + 1 / |θ| :=
              add_le_add (hFnorm _ (by positivity)) (hFnorm 1 zero_le_one)
    _ = ((M : ℝ) + 2) / |θ| + |θ| * Real.log ((M : ℝ) + 1) := by
        rw [htel]
        ring

/-! ### The principal-character twisted sum, via Möbius over divisors -/

/-- `∑_{e ∣ m} μ(e) = [m = 1]`. -/
lemma moebius_sum_divisors (m : ℕ) :
    (∑ e ∈ m.divisors, ArithmeticFunction.moebius e) = if m = 1 then 1 else 0 := by
  have h1 := ArithmeticFunction.coe_mul_zeta_apply
    (f := ArithmeticFunction.moebius) (x := m)
  rw [ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply] at h1
  exact h1.symm

/-- Multiplicativity of the twist over a product of positive integers. -/
lemma exptwist_nat_mul (θ : ℝ) {e m : ℕ} (he : 1 ≤ e) (hm : 1 ≤ m) :
    Complex.exp ((-Real.log ((e * m : ℕ) : ℝ) * θ : ℝ) * Complex.I)
      = Complex.exp ((-Real.log e * θ : ℝ) * Complex.I) *
        Complex.exp ((-Real.log m * θ : ℝ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  have he0 : ((e : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < e := by exact_mod_cast he
    linarith
  have hm0 : ((m : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    linarith
  rw [Nat.cast_mul, Real.log_mul he0 hm0]
  push_cast
  ring

/-- Divisors sit inside `[1, d]`. -/
lemma divisors_subset_Icc (d : ℕ) : d.divisors ⊆ Finset.Icc 1 d := by
  intro e he
  exact Finset.mem_Icc.2 ⟨Nat.pos_of_mem_divisors he, Nat.divisor_le he⟩

set_option maxHeartbeats 2000000 in
/-- **Principal twisted sum bound** (the same-character off-diagonal): for
`1 ≤ |θ|`,

  `‖∑_{n ≤ N, (n,d)=1} e^{-iθ log n}‖
      ≤ (N(1 + log d) + 2d)/|θ| + d·|θ|·log(N+1)`.

Möbius over the divisors of `d` + the oscillatory bound
`exp_twist_partial_sum_le` on each subprogression. -/
lemma principal_twisted_sum_le (d : ℕ) [NeZero d] (θ : ℝ) (hθ : 1 ≤ |θ|) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, (if IsUnit ((n : ZMod d)) then (1 : ℂ) else 0) *
        Complex.exp ((-Real.log n * θ : ℝ) * Complex.I)‖
      ≤ ((N : ℝ) * (1 + Real.log d) + 2 * d) / |θ|
        + d * |θ| * Real.log ((N : ℝ) + 1) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hθ0 : (0 : ℝ) < |θ| := by linarith
  set w : ℕ → ℂ := fun n => Complex.exp ((-Real.log n * θ : ℝ) * Complex.I) with hw
  -- Step 1: Möbius expansion of the coprimality indicator
  have hind : ∀ n ∈ Finset.Icc 1 N, (if IsUnit ((n : ZMod d)) then (1 : ℂ) else 0)
      = ∑ e ∈ d.divisors, (if e ∣ n then ((ArithmeticFunction.moebius e : ℤ) : ℂ) else 0) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have hset : d.divisors.filter (fun e => e ∣ n) = (Nat.gcd n d).divisors := by
      ext e
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hed, _⟩, hen⟩
        refine ⟨⟨hen, hed⟩, fun hg => ?_⟩
        exact NeZero.ne d (Nat.eq_zero_of_gcd_eq_zero_right hg)
      · rintro ⟨⟨hen, hed⟩, _⟩
        exact ⟨⟨hed, NeZero.ne d⟩, hen⟩
    calc (if IsUnit ((n : ZMod d)) then (1 : ℂ) else 0)
        = (if Nat.gcd n d = 1 then (1 : ℂ) else 0) := by
          by_cases h : Nat.Coprime n d
          · rw [if_pos ((ZMod.isUnit_iff_coprime n d).2 h), if_pos h]
          · rw [if_neg (fun hu => h ((ZMod.isUnit_iff_coprime n d).1 hu)), if_neg h]
      _ = ((if Nat.gcd n d = 1 then (1 : ℤ) else 0 : ℤ) : ℂ) := by
          split_ifs <;> simp
      _ = ((∑ e ∈ (Nat.gcd n d).divisors, ArithmeticFunction.moebius e : ℤ) : ℂ) := by
          rw [moebius_sum_divisors]
      _ = ∑ e ∈ (Nat.gcd n d).divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) := by
          push_cast
          rfl
      _ = ∑ e ∈ d.divisors.filter (fun e => e ∣ n),
            ((ArithmeticFunction.moebius e : ℤ) : ℂ) := by rw [hset]
      _ = ∑ e ∈ d.divisors,
            (if e ∣ n then ((ArithmeticFunction.moebius e : ℤ) : ℂ) else 0) :=
          Finset.sum_filter _ _
  -- Step 2: swap the sums
  have hswap : (∑ n ∈ Finset.Icc 1 N, (if IsUnit ((n : ZMod d)) then (1 : ℂ) else 0) * w n)
      = ∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => e ∣ n), w n := by
    calc (∑ n ∈ Finset.Icc 1 N, (if IsUnit ((n : ZMod d)) then (1 : ℂ) else 0) * w n)
        = ∑ n ∈ Finset.Icc 1 N, ∑ e ∈ d.divisors,
            (if e ∣ n then ((ArithmeticFunction.moebius e : ℤ) : ℂ) else 0) * w n := by
          refine Finset.sum_congr rfl fun n hn => ?_
          rw [hind n hn, Finset.sum_mul]
      _ = ∑ e ∈ d.divisors, ∑ n ∈ Finset.Icc 1 N,
            (if e ∣ n then ((ArithmeticFunction.moebius e : ℤ) : ℂ) else 0) * w n :=
          Finset.sum_comm
      _ = ∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
            ∑ n ∈ (Finset.Icc 1 N).filter (fun n => e ∣ n), w n := by
          refine Finset.sum_congr rfl fun e _ => ?_
          rw [Finset.mul_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun n _ => ?_
          split_ifs <;> simp
  -- Step 3: reindex each subprogression and bound it
  have hinner : ∀ e ∈ d.divisors,
      ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => e ∣ n), w n‖
        ≤ ((N : ℝ) / e + 2) / |θ| + |θ| * Real.log ((N : ℝ) + 1) := by
    intro e hediv
    have he1 : 1 ≤ e := Nat.pos_of_mem_divisors hediv
    have he0 : (0 : ℝ) < e := by exact_mod_cast he1
    have hreidx : (∑ n ∈ (Finset.Icc 1 N).filter (fun n => e ∣ n), w n)
        = ∑ m ∈ Finset.Icc 1 (N / e), w (e * m) := by
      refine Finset.sum_nbij' (fun n => n / e) (fun m => e * m) ?_ ?_ ?_ ?_ ?_
      · intro n hn
        obtain ⟨hn', hdvd⟩ := Finset.mem_filter.1 hn
        obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.1 hn'
        refine Finset.mem_Icc.2 ⟨?_, Nat.div_le_div_right hnN⟩
        rw [Nat.one_le_div_iff he1]
        exact Nat.le_of_dvd (by omega) hdvd
      · intro m hm
        obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.1 hm
        refine Finset.mem_filter.2
          ⟨Finset.mem_Icc.2 ⟨Nat.mul_pos he1 hm1, ?_⟩, dvd_mul_right e m⟩
        calc e * m = m * e := mul_comm e m
          _ ≤ N := (Nat.le_div_iff_mul_le he1).1 hmN
      · intro n hn
        exact Nat.mul_div_cancel' (Finset.mem_filter.1 hn).2
      · intro m _
        exact Nat.mul_div_cancel_left m he1
      · intro n hn
        rw [Nat.mul_div_cancel' (Finset.mem_filter.1 hn).2]
    rw [hreidx]
    have hsplit : (∑ m ∈ Finset.Icc 1 (N / e), w (e * m))
        = Complex.exp ((-Real.log e * θ : ℝ) * Complex.I) *
            ∑ m ∈ Finset.Icc 1 (N / e), w m := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
      rw [hw]
      exact exptwist_nat_mul θ he1 hm1
    rw [hsplit, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hbound := exp_twist_partial_sum_le θ hθ (N / e)
    have hND : ((N / e : ℕ) : ℝ) ≤ (N : ℝ) / e := Nat.cast_div_le
    have hlogND : Real.log (((N / e : ℕ) : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) := by
      have h1 : ((N / e : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast Nat.div_le_self N e
      have h2 : (0 : ℝ) < ((N / e : ℕ) : ℝ) + 1 := by positivity
      exact Real.log_le_log h2 (by linarith)
    calc ‖∑ m ∈ Finset.Icc 1 (N / e), w m‖
        ≤ (((N / e : ℕ) : ℝ) + 2) / |θ| + |θ| * Real.log (((N / e : ℕ) : ℝ) + 1) :=
          hbound
      _ ≤ ((N : ℝ) / e + 2) / |θ| + |θ| * Real.log ((N : ℝ) + 1) := by
          refine add_le_add ?_ ?_
          · gcongr
          · exact mul_le_mul_of_nonneg_left hlogND (abs_nonneg θ)
  -- Step 4: sum over divisors
  have hmu : ∀ e : ℕ, ‖((ArithmeticFunction.moebius e : ℤ) : ℂ)‖ ≤ 1 := by
    intro e
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hcard : ((d.divisors).card : ℝ) ≤ d := by
    have h1 := Finset.card_le_card (divisors_subset_Icc d)
    rw [Nat.card_Icc] at h1
    exact_mod_cast le_trans h1 (by omega)
  have hharm : (∑ e ∈ d.divisors, (N : ℝ) / e)
      ≤ (N : ℝ) * (1 + Real.log d) := by
    have h1 : (∑ e ∈ d.divisors, (N : ℝ) / e)
        = (N : ℝ) * ∑ e ∈ d.divisors, (1 : ℝ) / e := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      ring
    rw [h1]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg N)
    calc (∑ e ∈ d.divisors, (1 : ℝ) / e)
        ≤ ∑ e ∈ Finset.Icc 1 d, (1 : ℝ) / e := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (divisors_subset_Icc d)
            fun e _ _ => by positivity
      _ ≤ 1 + Real.log d := harmonic_sum_le d
  calc ‖∑ n ∈ Finset.Icc 1 N, (if IsUnit ((n : ZMod d)) then (1 : ℂ) else 0) * w n‖
      = ‖∑ e ∈ d.divisors, ((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => e ∣ n), w n‖ := by rw [hswap]
    _ ≤ ∑ e ∈ d.divisors, ‖((ArithmeticFunction.moebius e : ℤ) : ℂ) *
          ∑ n ∈ (Finset.Icc 1 N).filter (fun n => e ∣ n), w n‖ := norm_sum_le _ _
    _ ≤ ∑ e ∈ d.divisors, (((N : ℝ) / e + 2) / |θ| + |θ| * Real.log ((N : ℝ) + 1)) := by
        refine Finset.sum_le_sum fun e he => ?_
        rw [norm_mul]
        calc ‖((ArithmeticFunction.moebius e : ℤ) : ℂ)‖ *
              ‖∑ n ∈ (Finset.Icc 1 N).filter (fun n => e ∣ n), w n‖
            ≤ 1 * (((N : ℝ) / e + 2) / |θ| + |θ| * Real.log ((N : ℝ) + 1)) :=
              mul_le_mul (hmu e) (hinner e he) (norm_nonneg _) zero_le_one
          _ = ((N : ℝ) / e + 2) / |θ| + |θ| * Real.log ((N : ℝ) + 1) := one_mul _
    _ = (∑ e ∈ d.divisors, ((N : ℝ) / e + 2)) / |θ|
        + ((d.divisors).card : ℝ) * (|θ| * Real.log ((N : ℝ) + 1)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_div]
    _ ≤ ((N : ℝ) * (1 + Real.log d) + 2 * d) / |θ|
        + d * (|θ| * Real.log ((N : ℝ) + 1)) := by
        have hnum : (∑ e ∈ d.divisors, ((N : ℝ) / e + 2))
            ≤ (N : ℝ) * (1 + Real.log d) + 2 * d := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          linarith [hharm, hcard]
        refine add_le_add ?_ ?_
        · exact div_le_div_of_nonneg_right hnum hθ0.le
        · refine mul_le_mul_of_nonneg_right hcard ?_
          have h1 : (0 : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
            Real.log_nonneg (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])
          positivity
    _ = ((N : ℝ) * (1 + Real.log d) + 2 * d) / |θ|
        + d * |θ| * Real.log ((N : ℝ) + 1) := by ring

/-! ### Gram-matrix entries for the duality step -/

/-- `e^{ixt} · conj(e^{ixu}) = e^{ix(t−u)}` (same frequency, two times). -/
lemma exp_mul_conj_exp_time (x t u : ℝ) :
    Complex.exp ((x * t : ℝ) * Complex.I) * conj (Complex.exp ((x * u : ℝ) * Complex.I))
      = Complex.exp ((x * (t - u) : ℝ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `conj(e^{iy}) = e^{-iy}`. -/
lemma conj_exp_ofReal_mul_I (y : ℝ) :
    conj (Complex.exp ((y : ℝ) * Complex.I)) = Complex.exp (((-y : ℝ)) * Complex.I) := by
  rw [← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Trivial entry bound: every Gram entry has norm at most `N`. -/
lemma gram_entry_le {d : ℕ} [NeZero d] (χ χ' : DirichletCharacter ℂ d) (θ : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d) * conj (χ' (n : ZMod d)) *
        Complex.exp ((-Real.log n * θ : ℝ) * Complex.I)‖ ≤ N := by
  calc ‖∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d) * conj (χ' (n : ZMod d)) *
        Complex.exp ((-Real.log n * θ : ℝ) * Complex.I)‖
      ≤ ∑ n ∈ Finset.Icc 1 N, ‖χ (n : ZMod d) * conj (χ' (n : ZMod d)) *
          Complex.exp ((-Real.log n * θ : ℝ) * Complex.I)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) := by
        refine Finset.sum_le_sum fun n _ => ?_
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, mul_one]
        exact mul_le_one₀ (χ.norm_le_one _) (norm_nonneg _) (χ'.norm_le_one _)
    _ = N := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring

/-- Same-character entries reduce to the unit-restricted oscillatory sum. -/
lemma gram_entry_same_char {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d) (θ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, χ (n : ZMod d) * conj (χ (n : ZMod d)) *
        Complex.exp ((-Real.log n * θ : ℝ) * Complex.I))
      = ∑ n ∈ Finset.Icc 1 N, (if IsUnit ((n : ZMod d)) then (1 : ℂ) else 0) *
          Complex.exp ((-Real.log n * θ : ℝ) * Complex.I) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  by_cases hy : IsUnit ((n : ZMod d))
  · rw [if_pos hy, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    have hnorm : ‖χ ((n : ZMod d))‖ = 1 := by
      have h2 := χ.unit_norm_eq_one hy.unit
      rwa [IsUnit.unit_spec] at h2
    rw [hnorm]
    norm_num
  · rw [if_neg hy, χ.map_nonunit hy, zero_mul]

set_option maxHeartbeats 2000000 in
/-- **Gram row-sum bound.** For a spaced family of diameter `Θ`, each row of
the Gram matrix has `ℓ¹`-norm at most `12 L² (N + R·dΘ)`,
`L := 1 + log(2 + dΘN)`. The `d·Θ` (both exponents 1) is the honest cost of
the trivial character-sum bound and partial summation; see the file header. -/
lemma gram_row_sum_le {ι : Type*} (d : ℕ) [NeZero d] (N : ℕ) (hN : 1 ≤ N)
    (Θ : ℝ) (hΘ : 2 ≤ Θ)
    (s : Finset ι) (chi : ι → DirichletCharacter ℂ d) (pt : ι → ℝ)
    (hdiam : ∀ r ∈ s, ∀ r' ∈ s, |pt r - pt r'| ≤ Θ)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → chi r = chi r' → 1 ≤ |pt r - pt r'|)
    (hR1 : (1 : ℝ) ≤ s.card) (r : ι) (hr : r ∈ s) :
    (∑ r' ∈ s, ‖∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
        Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖)
      ≤ 12 * (1 + Real.log (2 + d * Θ * N)) ^ 2 *
          ((N : ℝ) + (s.card : ℝ) * ((d : ℝ) * Θ)) := by
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  set L : ℝ := 1 + Real.log (2 + d * Θ * N) with hL
  set R : ℝ := (s.card : ℝ) with hRdef
  set Kf : ι → ℝ := fun r' => ‖∑ n ∈ Finset.Icc 1 N,
    (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
      Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖ with hKf
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hΘ0 : (0 : ℝ) < Θ := by linarith
  have hdN : (1 : ℝ) ≤ (d : ℝ) * N := by nlinarith
  have hΘN1 : (1 : ℝ) ≤ Θ * (N : ℝ) := by nlinarith
  have hdΘN : Θ ≤ (d : ℝ) * Θ * N := by
    nlinarith [mul_nonneg hΘ0.le (sub_nonneg.2 hdN)]
  have hd_le : (d : ℝ) ≤ (d : ℝ) * Θ * N := by
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ (d : ℝ)) (sub_nonneg.2 hΘN1)]
  have hN_le : (N : ℝ) + 1 ≤ 2 + (d : ℝ) * Θ * N := by
    have hdΘ2 : (2 : ℝ) ≤ (d : ℝ) * Θ := by nlinarith
    nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      (sub_nonneg.2 (by linarith : (1 : ℝ) ≤ (d : ℝ) * Θ))]
  have harg1 : (1 : ℝ) ≤ 2 + (d : ℝ) * Θ * N := by linarith
  have hlogarg0 : 0 ≤ Real.log (2 + (d : ℝ) * Θ * N) := Real.log_nonneg harg1
  have hL1 : 1 ≤ L := by rw [hL]; linarith
  have hL0 : 0 < L := by linarith
  have hlogd : 1 + Real.log d ≤ L := by
    have h1 : (d : ℝ) ≤ 2 + (d : ℝ) * Θ * N := by linarith
    have h2 := Real.log_le_log (by linarith : (0 : ℝ) < d) h1
    rw [hL]; linarith
  have hlogN1 : Real.log ((N : ℝ) + 1) ≤ L := by
    have h2 := Real.log_le_log (by linarith : (0 : ℝ) < (N : ℝ) + 1) hN_le
    rw [hL]; linarith
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlogN : Real.log N ≤ L := by
    have h1 := Real.log_le_log (by linarith : (0 : ℝ) < N)
      (by linarith : (N : ℝ) ≤ (N : ℝ) + 1)
    linarith
  have hlogΘ : 1 + Real.log Θ ≤ L := by
    have h1 : Θ ≤ 2 + (d : ℝ) * Θ * N := by linarith
    have h2 := Real.log_le_log hΘ0 h1
    rw [hL]; linarith
  have hlogd0 : 0 ≤ Real.log d := Real.log_nonneg hd1
  have hlogΘ0 : 0 ≤ Real.log Θ := Real.log_nonneg (by linarith)
  -- the diagonal entry
  have hdiag : Kf r ≤ N := by
    rw [hKf]
    exact gram_entry_le (chi r) (chi r) (pt r - pt r) N
  -- same-character off-diagonal entries
  have hsame : ∀ r' ∈ (s.erase r).filter (fun r' => chi r' = chi r),
      Kf r' ≤ ((N : ℝ) * (1 + Real.log d) + 2 * d) * (1 / |pt r - pt r'|)
        + (d : ℝ) * Θ * L := by
    intro r' hr'
    obtain ⟨hr'e, hchi⟩ := Finset.mem_filter.1 hr'
    have hr's : r' ∈ s := Finset.mem_of_mem_erase hr'e
    have hne : r ≠ r' := (Finset.ne_of_mem_erase hr'e).symm
    have hsep' : 1 ≤ |pt r - pt r'| := hsep r hr r' hr's hne hchi.symm
    have hdiam' : |pt r - pt r'| ≤ Θ := hdiam r hr r' hr's
    have h1 : Kf r' = ‖∑ n ∈ Finset.Icc 1 N,
        (if IsUnit ((n : ZMod d)) then (1 : ℂ) else 0) *
          Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖ := by
      rw [hKf]
      simp only [hchi]
      rw [gram_entry_same_char (chi r) (pt r - pt r') N]
    rw [h1]
    have h2 := principal_twisted_sum_le d (pt r - pt r') hsep' N
    have h3 : ((N : ℝ) * (1 + Real.log d) + 2 * d) / |pt r - pt r'|
        = ((N : ℝ) * (1 + Real.log d) + 2 * d) * (1 / |pt r - pt r'|) := by
      rw [mul_one_div]
    have h4 : (d : ℝ) * |pt r - pt r'| * Real.log ((N : ℝ) + 1) ≤ (d : ℝ) * Θ * L := by
      have h5 : |pt r - pt r'| * Real.log ((N : ℝ) + 1) ≤ Θ * L := by
        refine mul_le_mul hdiam' hlogN1 (Real.log_nonneg (by linarith)) (by linarith)
      calc (d : ℝ) * |pt r - pt r'| * Real.log ((N : ℝ) + 1)
          = (d : ℝ) * (|pt r - pt r'| * Real.log ((N : ℝ) + 1)) := by ring
        _ ≤ (d : ℝ) * (Θ * L) := by
            exact mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = (d : ℝ) * Θ * L := by ring
    rw [h3] at h2
    linarith [h2]
  -- different-character entries
  have hdiff : ∀ r' ∈ (s.erase r).filter (fun r' => ¬ chi r' = chi r),
      Kf r' ≤ 2 * ((d : ℝ) * Θ * L) := by
    intro r' hr'
    obtain ⟨hr'e, hchi⟩ := Finset.mem_filter.1 hr'
    have hr's : r' ∈ s := Finset.mem_of_mem_erase hr'e
    have hne : chi r ≠ chi r' := fun h => hchi h.symm
    have hdiam' : |pt r - pt r'| ≤ Θ := hdiam r hr r' hr's
    have h1 := nonprincipal_twisted_sum_le hne (pt r - pt r') N hN
    have h2 : |pt r - pt r'| * Real.log N ≤ Θ * L :=
      mul_le_mul hdiam' hlogN hlogN0 (by linarith)
    have h3 : (1 : ℝ) ≤ Θ * L := by nlinarith
    have h4 : (1 : ℝ) + |pt r - pt r'| * Real.log N ≤ 2 * (Θ * L) := by linarith
    rw [hKf]
    calc ‖∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
          Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖
        ≤ (d : ℝ) * (1 + |pt r - pt r'| * Real.log N) := h1
      _ ≤ (d : ℝ) * (2 * (Θ * L)) := mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = 2 * ((d : ℝ) * Θ * L) := by ring
  -- sum of the same-character entries
  have hsame_sum : (∑ r' ∈ (s.erase r).filter (fun r' => chi r' = chi r), Kf r')
      ≤ ((N : ℝ) * L + 2 * d) * (4 * L) + R * ((d : ℝ) * Θ * L) := by
    have hinv : (∑ r' ∈ (s.erase r).filter (fun r' => chi r' = chi r),
          1 / |pt r - pt r'|) ≤ 2 * (1 + Real.log Θ) := by
      refine sum_inv_abs_sep_le _ (fun r' => pt r - pt r') Θ (by linarith) ?_ ?_ ?_
      · intro i hi
        obtain ⟨hie, hichi⟩ := Finset.mem_filter.1 hi
        exact hsep r hr i (Finset.mem_of_mem_erase hie)
          (Finset.ne_of_mem_erase hie).symm hichi.symm
      · intro i hi
        obtain ⟨hie, _⟩ := Finset.mem_filter.1 hi
        exact hdiam r hr i (Finset.mem_of_mem_erase hie)
      · intro i hi j hj hij
        obtain ⟨hie, hichi⟩ := Finset.mem_filter.1 hi
        obtain ⟨hje, hjchi⟩ := Finset.mem_filter.1 hj
        have h1 := hsep i (Finset.mem_of_mem_erase hie) j (Finset.mem_of_mem_erase hje)
          hij (hichi.trans hjchi.symm)
        rw [show pt r - pt i - (pt r - pt j) = -(pt i - pt j) by ring, abs_neg]
        exact h1
    have hcard : (((s.erase r).filter (fun r' => chi r' = chi r)).card : ℝ) ≤ R := by
      rw [hRdef]
      exact_mod_cast Finset.card_le_card
        ((Finset.filter_subset _ _).trans (Finset.erase_subset r s))
    have hA0 : (0 : ℝ) ≤ (N : ℝ) * (1 + Real.log d) + 2 * d := by positivity
    calc (∑ r' ∈ (s.erase r).filter (fun r' => chi r' = chi r), Kf r')
        ≤ ∑ r' ∈ (s.erase r).filter (fun r' => chi r' = chi r),
            (((N : ℝ) * (1 + Real.log d) + 2 * d) * (1 / |pt r - pt r'|)
              + (d : ℝ) * Θ * L) := Finset.sum_le_sum hsame
      _ = ((N : ℝ) * (1 + Real.log d) + 2 * d) *
            (∑ r' ∈ (s.erase r).filter (fun r' => chi r' = chi r), 1 / |pt r - pt r'|)
          + (((s.erase r).filter (fun r' => chi r' = chi r)).card : ℝ) *
              ((d : ℝ) * Θ * L) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((N : ℝ) * (1 + Real.log d) + 2 * d) * (2 * (1 + Real.log Θ))
          + R * ((d : ℝ) * Θ * L) := by
          refine add_le_add (mul_le_mul_of_nonneg_left hinv hA0)
            (mul_le_mul_of_nonneg_right hcard (by positivity))
      _ ≤ ((N : ℝ) * L + 2 * d) * (4 * L) + R * ((d : ℝ) * Θ * L) := by
          have h1 : (N : ℝ) * (1 + Real.log d) + 2 * d ≤ (N : ℝ) * L + 2 * d := by
            nlinarith [mul_le_mul_of_nonneg_left hlogd
              (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
          have h2 : 2 * (1 + Real.log Θ) ≤ 4 * L := by linarith [hL0.le]
          have hc0 : (0 : ℝ) ≤ 2 * (1 + Real.log Θ) := by linarith
          have hb0 : (0 : ℝ) ≤ (N : ℝ) * L + 2 * d := by
            nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) hL0.le]
          exact add_le_add (mul_le_mul h1 h2 hc0 hb0) le_rfl
  -- sum of the different-character entries
  have hdiff_sum : (∑ r' ∈ (s.erase r).filter (fun r' => ¬ chi r' = chi r), Kf r')
      ≤ R * (2 * ((d : ℝ) * Θ * L)) := by
    have hcard : (((s.erase r).filter (fun r' => ¬ chi r' = chi r)).card : ℝ) ≤ R := by
      rw [hRdef]
      exact_mod_cast Finset.card_le_card
        ((Finset.filter_subset _ _).trans (Finset.erase_subset r s))
    calc (∑ r' ∈ (s.erase r).filter (fun r' => ¬ chi r' = chi r), Kf r')
        ≤ ∑ _r' ∈ (s.erase r).filter (fun r' => ¬ chi r' = chi r),
            2 * ((d : ℝ) * Θ * L) := Finset.sum_le_sum hdiff
      _ = (((s.erase r).filter (fun r' => ¬ chi r' = chi r)).card : ℝ) *
            (2 * ((d : ℝ) * Θ * L)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ R * (2 * ((d : ℝ) * Θ * L)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
  -- assemble the row
  have hsplit : (∑ r' ∈ s, Kf r') = Kf r + ∑ r' ∈ s.erase r, Kf r' :=
    (Finset.add_sum_erase s Kf hr).symm
  have hsplit2 : (∑ r' ∈ s.erase r, Kf r')
      = (∑ r' ∈ (s.erase r).filter (fun r' => chi r' = chi r), Kf r')
        + ∑ r' ∈ (s.erase r).filter (fun r' => ¬ chi r' = chi r), Kf r' :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hrow : (∑ r' ∈ s, Kf r')
      ≤ (N : ℝ) + (((N : ℝ) * L + 2 * d) * (4 * L) + R * ((d : ℝ) * Θ * L))
        + R * (2 * ((d : ℝ) * Θ * L)) := by
    rw [hsplit, hsplit2]
    linarith [hdiag, hsame_sum, hdiff_sum]
  -- final arithmetic: everything fits under `12 L² (N + R d Θ)`
  have g1 : (2 : ℝ) ≤ Θ * L := by
    have := mul_le_mul hΘ hL1 zero_le_one (by linarith : (0 : ℝ) ≤ Θ)
    linarith
  have hL2 : (1 : ℝ) ≤ L ^ 2 := by
    nlinarith [mul_le_mul hL1 hL1 zero_le_one (by linarith : (0 : ℝ) ≤ L)]
  have hLL : L ≤ L ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hL1 hL0.le]
  have f1 : (N : ℝ) ≤ (N : ℝ) * L ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hL2 (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have f2 : 8 * (d : ℝ) * L ≤ 4 * (R * ((d : ℝ) * Θ)) * L ^ 2 := by
    have h4dL0 : (0 : ℝ) ≤ 4 * (d : ℝ) * L :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg d)) hL0.le
    have h1 : 8 * (d : ℝ) * L ≤ 4 * ((d : ℝ) * Θ * L) * L := by
      nlinarith [mul_le_mul_of_nonneg_left g1 h4dL0]
    have h2 : 4 * ((d : ℝ) * Θ * L) * L ≤ 4 * (R * ((d : ℝ) * Θ)) * L ^ 2 := by
      have h3 : (0 : ℝ) ≤ 4 * ((d : ℝ) * Θ) * L ^ 2 := by positivity
      nlinarith [mul_nonneg (sub_nonneg.2 hR1) h3]
    linarith
  have f3 : 3 * (R * ((d : ℝ) * Θ)) * L ≤ 3 * (R * ((d : ℝ) * Θ)) * L ^ 2 := by
    have h1 : (0 : ℝ) ≤ 3 * (R * ((d : ℝ) * Θ)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hLL h1]
  calc (∑ r' ∈ s, Kf r')
      ≤ (N : ℝ) + (((N : ℝ) * L + 2 * d) * (4 * L) + R * ((d : ℝ) * Θ * L))
        + R * (2 * ((d : ℝ) * Θ * L)) := hrow
    _ = (N : ℝ) + 4 * (N : ℝ) * L ^ 2 + 8 * (d : ℝ) * L
        + 3 * (R * ((d : ℝ) * Θ)) * L := by ring
    _ ≤ (N : ℝ) * L ^ 2 + 4 * (N : ℝ) * L ^ 2 + 4 * (R * ((d : ℝ) * Θ)) * L ^ 2
        + 3 * (R * ((d : ℝ) * Θ)) * L ^ 2 := by linarith [f1, f2, f3]
    _ ≤ 12 * L ^ 2 * ((N : ℝ) + R * ((d : ℝ) * Θ)) := by
        have hX0 : (0 : ℝ) ≤ (N : ℝ) * L ^ 2 := by positivity
        have hY0 : (0 : ℝ) ≤ R * ((d : ℝ) * Θ) * L ^ 2 := by positivity
        nlinarith [hX0, hY0]

set_option maxHeartbeats 4000000 in
/-- **LV2 (Halász–Montgomery duality step), achieved variant.** For a spaced
family of diameter `Θ` (`2 ≤ Θ`) of `V`-large values,

  `R·V² ≤ 100 · (1 + log(2 + dΘN))² · (N + R·(d·Θ)) · G`.

EXPONENT REPORT: the off-diagonal term is `R·d·Θ` — `d`-exponent **1**
(trivial complete-period character-sum bound; no Pólya–Vinogradov in the
pinned Mathlib, which would give `d^{1/2}`), `Θ`-exponent **1** (partial
summation; van der Corput would give `Θ^{1/2}`). The classical target shape
`N + R·√(dΘN)` is NOT achieved; do not consume this expecting `√`. -/
theorem large_values_dual {ι : Type*} (d : ℕ) (hd : 0 < d) (N : ℕ) (hN : 1 ≤ N)
    (a : ℕ → ℂ) (V : ℝ) (hV : 0 < V) (Θ : ℝ) (hΘ : 2 ≤ Θ)
    (s : Finset ι) (chi : ι → DirichletCharacter ℂ d) (pt : ι → ℝ)
    (hdiam : ∀ r ∈ s, ∀ r' ∈ s, |pt r - pt r'| ≤ Θ)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → chi r = chi r' → 1 ≤ |pt r - pt r'|)
    (hlarge : ∀ r ∈ s, V ≤ ‖∑ n ∈ Finset.Icc 1 N,
        a n * (chi r) (n : ZMod d) *
          Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I)‖) :
    (s.card : ℝ) * V ^ 2 ≤
      100 * (1 + Real.log (2 + d * Θ * N)) ^ 2 *
        ((N : ℝ) + (s.card : ℝ) * ((d : ℝ) * Θ)) *
        ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
  have : NeZero d := ⟨hd.ne'⟩
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hG0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  have hprod0 : (0 : ℝ) ≤ (d : ℝ) * Θ * N := by positivity
  have hL1 : (1 : ℝ) ≤ 1 + Real.log (2 + d * Θ * N) := by
    have h1 : (0 : ℝ) ≤ Real.log (2 + d * Θ * N) :=
      Real.log_nonneg (by linarith)
    linarith
  rcases Finset.eq_empty_or_nonempty s with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero, zero_mul, add_zero]
    have h2 : (0 : ℝ) ≤ (1 + Real.log (2 + d * Θ * N)) ^ 2 := sq_nonneg _
    have h3 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    positivity
  have hR1 : (1 : ℝ) ≤ s.card := by
    have h1 := Finset.card_pos.2 hne
    exact_mod_cast h1
  -- the Dirichlet polynomials, the dual vector, and their key identities
  set S : ι → ℂ := fun r => ∑ n ∈ Finset.Icc 1 N,
    a n * (chi r) (n : ZMod d) *
      Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I) with hSdef
  set B : ℕ → ℂ := fun n => ∑ r ∈ s,
    conj (S r) * (chi r) (n : ZMod d) *
      Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I) with hBdef
  have hSr : ∀ r : ι, S r = ∑ n ∈ Finset.Icc 1 N,
      a n * (chi r) (n : ZMod d) *
        Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I) := fun r => by rw [hSdef]
  have hBr : ∀ n : ℕ, B n = ∑ r ∈ s,
      conj (S r) * (chi r) (n : ZMod d) *
        Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I) := fun n => by rw [hBdef]
  have hlargeS : ∀ r ∈ s, V ≤ ‖S r‖ := by
    intro r hr
    rw [hSr r]
    exact hlarge r hr
  have hSig0 : (0 : ℝ) ≤ ∑ r ∈ s, ‖S r‖ ^ 2 :=
    Finset.sum_nonneg fun r _ => by positivity
  -- Step A: the count against the energy
  have hRV : (s.card : ℝ) * V ^ 2 ≤ ∑ r ∈ s, ‖S r‖ ^ 2 := by
    calc (s.card : ℝ) * V ^ 2 = ∑ _r ∈ s, V ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ r ∈ s, ‖S r‖ ^ 2 :=
          Finset.sum_le_sum fun r hr => pow_le_pow_left₀ hV.le (hlargeS r hr) 2
  -- Step B: the duality identity  Σ = ∑ₙ aₙ Bₙ
  have hBsum : (∑ n ∈ Finset.Icc 1 N, a n * B n) = ∑ r ∈ s, conj (S r) * S r := by
    calc (∑ n ∈ Finset.Icc 1 N, a n * B n)
        = ∑ n ∈ Finset.Icc 1 N, ∑ r ∈ s,
            a n * (conj (S r) * (chi r) (n : ZMod d) *
              Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I)) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hBr n, Finset.mul_sum]
      _ = ∑ r ∈ s, ∑ n ∈ Finset.Icc 1 N,
            a n * (conj (S r) * (chi r) (n : ZMod d) *
              Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I)) := Finset.sum_comm
      _ = ∑ r ∈ s, conj (S r) * ∑ n ∈ Finset.Icc 1 N,
            a n * (chi r) (n : ZMod d) *
              Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I) := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
      _ = ∑ r ∈ s, conj (S r) * S r := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [← hSr r]
  -- Step C: Cauchy–Schwarz in `n`
  set H : ℝ := ∑ n ∈ Finset.Icc 1 N, ‖B n‖ ^ 2 with hHdef
  have hnorm_eq : (∑ r ∈ s, ‖S r‖ ^ 2) = ‖∑ n ∈ Finset.Icc 1 N, a n * B n‖ := by
    have hc : (((∑ r ∈ s, ‖S r‖ ^ 2 : ℝ)) : ℂ) = ∑ n ∈ Finset.Icc 1 N, a n * B n := by
      rw [hBsum]
      push_cast
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [mul_comm, Complex.mul_conj']
    calc (∑ r ∈ s, ‖S r‖ ^ 2)
        = ‖(((∑ r ∈ s, ‖S r‖ ^ 2 : ℝ)) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hSig0]
      _ = ‖∑ n ∈ Finset.Icc 1 N, a n * B n‖ := by rw [hc]
  have hCS : (∑ r ∈ s, ‖S r‖ ^ 2) ^ 2
      ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * H := by
    have h2 : ‖∑ n ∈ Finset.Icc 1 N, a n * B n‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ * ‖B n‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun n _ => norm_mul _ _
    have h3 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N)
      (fun n => ‖a n‖) (fun n => ‖B n‖)
    calc (∑ r ∈ s, ‖S r‖ ^ 2) ^ 2
        = ‖∑ n ∈ Finset.Icc 1 N, a n * B n‖ ^ 2 := by rw [hnorm_eq]
      _ ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖ * ‖B n‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) *
            ∑ n ∈ Finset.Icc 1 N, ‖B n‖ ^ 2 := h3
      _ = (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * H := by rw [hHdef]
  -- Step D: expand `H` over the Gram matrix
  have hterm : ∀ (z w χv χv' : ℂ) (n : ℕ) (t t' : ℝ),
      (z * χv * Complex.exp ((-Real.log n * t : ℝ) * Complex.I)) *
        conj (conj w * χv' * Complex.exp ((-Real.log n * t' : ℝ) * Complex.I))
      = z * w * (χv * conj χv' *
          Complex.exp ((-Real.log n * (t - t') : ℝ) * Complex.I)) := by
    intro z w χv χv' n t t'
    rw [map_mul, map_mul, Complex.conj_conj]
    rw [← exp_mul_conj_exp_time (-Real.log n) t t']
    ring
  have hHexp : ((H : ℝ) : ℂ) = ∑ r ∈ s, ∑ r' ∈ s, conj (S r) * S r' *
      ∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
        Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I) := by
    calc ((H : ℝ) : ℂ)
        = ∑ n ∈ Finset.Icc 1 N, B n * conj (B n) := by
          rw [hHdef]
          push_cast
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Complex.mul_conj']
      _ = ∑ n ∈ Finset.Icc 1 N, ∑ r ∈ s, ∑ r' ∈ s,
            conj (S r) * S r' * ((chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
              Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [hBr n, map_sum, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
          exact hterm (conj (S r)) (S r') ((chi r) (n : ZMod d)) ((chi r') (n : ZMod d))
            n (pt r) (pt r')
      _ = ∑ r ∈ s, ∑ n ∈ Finset.Icc 1 N, ∑ r' ∈ s,
            conj (S r) * S r' * ((chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
              Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)) :=
          Finset.sum_comm
      _ = ∑ r ∈ s, ∑ r' ∈ s, ∑ n ∈ Finset.Icc 1 N,
            conj (S r) * S r' * ((chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
              Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)) := by
          exact Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ r ∈ s, ∑ r' ∈ s, conj (S r) * S r' *
            ∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
              Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I) := by
          refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
          exact (Finset.mul_sum _ _ _).symm
  -- Step E: the Gram rows control `H`
  set Lam : ℝ := 12 * (1 + Real.log (2 + d * Θ * N)) ^ 2 *
    ((N : ℝ) + (s.card : ℝ) * ((d : ℝ) * Θ)) with hLamdef
  have hrow : ∀ r ∈ s, (∑ r' ∈ s, ‖∑ n ∈ Finset.Icc 1 N,
      (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
        Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖) ≤ Lam := by
    intro r hr
    rw [hLamdef]
    exact gram_row_sum_le d N hN Θ hΘ s chi pt hdiam hsep hR1 r hr
  have hsymm : ∀ r ∈ s, ∀ r' ∈ s,
      ‖∑ n ∈ Finset.Icc 1 N, (chi r') (n : ZMod d) * conj ((chi r) (n : ZMod d)) *
        Complex.exp ((-Real.log n * (pt r' - pt r) : ℝ) * Complex.I)‖
      = ‖∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
        Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖ := by
    intro r _ r' _
    have h1 : (∑ n ∈ Finset.Icc 1 N, (chi r') (n : ZMod d) * conj ((chi r) (n : ZMod d)) *
        Complex.exp ((-Real.log n * (pt r' - pt r) : ℝ) * Complex.I))
        = conj (∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
            Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_mul, map_mul, Complex.conj_conj, conj_exp_ofReal_mul_I]
      have h2 : ((-(-Real.log n * (pt r - pt r')) : ℝ) : ℂ)
          = ((-Real.log n * (pt r' - pt r) : ℝ) : ℂ) := by push_cast; ring
      rw [h2]
      ring
    rw [h1, Complex.norm_conj]
  have hHle : H ≤ (∑ r ∈ s, ‖S r‖ ^ 2) * Lam := by
    have h5 : H ≤ ‖((H : ℝ) : ℂ)‖ := by
      calc H = (((H : ℝ) : ℂ)).re := (Complex.ofReal_re H).symm
        _ ≤ ‖((H : ℝ) : ℂ)‖ := Complex.re_le_norm _
    have h7 : ‖((H : ℝ) : ℂ)‖ ≤ ∑ r ∈ s, ∑ r' ∈ s, ‖S r‖ * ‖S r'‖ *
        ‖∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
          Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖ := by
      rw [hHexp]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r' _ => le_of_eq ?_)
      rw [norm_mul, norm_mul, Complex.norm_conj]
    have h8 : (∑ r ∈ s, ∑ r' ∈ s, ‖S r‖ * ‖S r'‖ *
        ‖∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
          Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖)
        ≤ ∑ r ∈ s, ∑ r' ∈ s, (‖S r‖ ^ 2 + ‖S r'‖ ^ 2) / 2 *
            ‖∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
              Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖ := by
      refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun r' _ => ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      nlinarith [sq_nonneg (‖S r‖ - ‖S r'‖)]
    have hA : (∑ r ∈ s, ∑ r' ∈ s, ‖S r‖ ^ 2 *
        ‖∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
          Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖)
        ≤ (∑ r ∈ s, ‖S r‖ ^ 2) * Lam := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun r hr => ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hrow r hr) (by positivity)
    have hB : (∑ r ∈ s, ∑ r' ∈ s, ‖S r'‖ ^ 2 *
        ‖∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
          Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖)
        ≤ (∑ r ∈ s, ‖S r‖ ^ 2) * Lam := by
      rw [Finset.sum_comm]
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun r' hr' => ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc (∑ r ∈ s, ‖∑ n ∈ Finset.Icc 1 N,
            (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
              Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖)
          = ∑ r ∈ s, ‖∑ n ∈ Finset.Icc 1 N,
              (chi r') (n : ZMod d) * conj ((chi r) (n : ZMod d)) *
                Complex.exp ((-Real.log n * (pt r' - pt r) : ℝ) * Complex.I)‖ :=
            Finset.sum_congr rfl fun r hr => (hsymm r hr r' hr').symm
        _ ≤ Lam := hrow r' hr'
    calc H ≤ ‖((H : ℝ) : ℂ)‖ := h5
      _ ≤ ∑ r ∈ s, ∑ r' ∈ s, ‖S r‖ * ‖S r'‖ *
          ‖∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
            Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖ := h7
      _ ≤ ∑ r ∈ s, ∑ r' ∈ s, (‖S r‖ ^ 2 + ‖S r'‖ ^ 2) / 2 *
          ‖∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
            Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖ := h8
      _ = (∑ r ∈ s, ∑ r' ∈ s, ‖S r‖ ^ 2 *
            ‖∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
              Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖) / 2
          + (∑ r ∈ s, ∑ r' ∈ s, ‖S r'‖ ^ 2 *
            ‖∑ n ∈ Finset.Icc 1 N, (chi r) (n : ZMod d) * conj ((chi r') (n : ZMod d)) *
              Complex.exp ((-Real.log n * (pt r - pt r') : ℝ) * Complex.I)‖) / 2 := by
          rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun r' _ => ?_
          ring
      _ ≤ (∑ r ∈ s, ‖S r‖ ^ 2) * Lam / 2 + (∑ r ∈ s, ‖S r‖ ^ 2) * Lam / 2 := by
          refine add_le_add ?_ ?_ <;> exact div_le_div_of_nonneg_right (by assumption)
            (by norm_num)
      _ = (∑ r ∈ s, ‖S r‖ ^ 2) * Lam := by ring
  -- Step G: cancel one factor of Σ and conclude
  have hSigpos : (0 : ℝ) < ∑ r ∈ s, ‖S r‖ ^ 2 := by
    have h1 : (0 : ℝ) < V ^ 2 := by positivity
    nlinarith [hRV, mul_nonneg (sub_nonneg.2 hR1) (sq_nonneg V)]
  have hSigLam : (∑ r ∈ s, ‖S r‖ ^ 2)
      ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * Lam := by
    have h11 : (∑ r ∈ s, ‖S r‖ ^ 2) * (∑ r ∈ s, ‖S r‖ ^ 2)
        ≤ ((∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * Lam) * (∑ r ∈ s, ‖S r‖ ^ 2) := by
      calc (∑ r ∈ s, ‖S r‖ ^ 2) * (∑ r ∈ s, ‖S r‖ ^ 2)
          = (∑ r ∈ s, ‖S r‖ ^ 2) ^ 2 := by ring
        _ ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * H := hCS
        _ ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * ((∑ r ∈ s, ‖S r‖ ^ 2) * Lam) :=
            mul_le_mul_of_nonneg_left hHle hG0
        _ = ((∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * Lam) * (∑ r ∈ s, ‖S r‖ ^ 2) := by ring
    exact le_of_mul_le_mul_right h11 hSigpos
  have hLamfac0 : (0 : ℝ) ≤ (1 + Real.log (2 + d * Θ * N)) ^ 2 *
      ((N : ℝ) + (s.card : ℝ) * ((d : ℝ) * Θ)) *
        ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
    have h1 : (0 : ℝ) ≤ (N : ℝ) + (s.card : ℝ) * ((d : ℝ) * Θ) := by positivity
    exact mul_nonneg (mul_nonneg (sq_nonneg _) h1) hG0
  calc (s.card : ℝ) * V ^ 2 ≤ ∑ r ∈ s, ‖S r‖ ^ 2 := hRV
    _ ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * Lam := hSigLam
    _ = 12 * (1 + Real.log (2 + d * Θ * N)) ^ 2 *
          ((N : ℝ) + (s.card : ℝ) * ((d : ℝ) * Θ)) *
          ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by rw [hLamdef]; ring
    _ ≤ 100 * (1 + Real.log (2 + d * Θ * N)) ^ 2 *
          ((N : ℝ) + (s.card : ℝ) * ((d : ℝ) * Θ)) *
          ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by nlinarith [hLamfac0]

/-! ### LV3: the Huxley-type combined bound (achieved shape) -/

/-- **LV3 (Huxley-type large-values bound), ACHIEVED SHAPE — read carefully.**

  `R ≤ 300 · (1 + log N)² · ( G·N/V² + G²·N·(d·T)/V⁴ )`.

EXPONENT REPORT for the Z0a-ledger keeper: the second term is
`G²·N·(dT)/V⁴` — `d`-exponent **1** (as required), `N`-exponent **1** (as
required), but `G`-exponent **2** and `V`-exponent **4** instead of the
canonical Huxley `G³·N·(dT)/V⁶`. Reason: with the linear-in-`Θ`
off-diagonal of `large_values_dual` (no Pólya–Vinogradov, no van der
Corput), the optimal Huxley block length is `Θ ≍ V²/(dG·polylog)` and the
subdivision computation returns exactly this `G²/V⁴` form — identically what
LV1 + the Cauchy–Schwarz bound `V² ≤ N·G` give directly, which is the proof
used here. The subdivision buys nothing until the off-diagonal improves to
`√(dΘ)`. Ledger impact (Z0a §3.2): balancing `N^{2−2σ}` against
`N^{3−4σ}(dT)` yields density coefficient `A(σ) = 2/(2σ−1)`, which on
`σ ∈ [39/50, 1]` is at most `25/7 ≈ 3.571 < 9/2` — inside the ledger's wall
(`2/(2σ−1) ≤ 9/2` if and only if `σ ≥ 13/18`). In the regime `V² ≥ G`
(the operative one downstream) this bound is moreover *stronger* than the
canonical `G³/V⁶` form. -/
theorem large_values_huxley {ι : Type*} (d : ℕ) (hd : 0 < d) (T : ℝ) (hT : 2 ≤ T)
    (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) (V : ℝ) (hV : 0 < V)
    (s : Finset ι) (chi : ι → DirichletCharacter ℂ d) (pt : ι → ℝ)
    (hpt : ∀ r ∈ s, |pt r| ≤ T)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → chi r = chi r' → 1 ≤ |pt r - pt r'|)
    (hlarge : ∀ r ∈ s, V ≤ ‖∑ n ∈ Finset.Icc 1 N,
        a n * (chi r) (n : ZMod d) *
          Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I)‖) :
    (s.card : ℝ) ≤ 300 * (1 + Real.log N) ^ 2 *
      ((∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * N / V ^ 2
        + (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ^ 2 * N * ((d : ℝ) * T) / V ^ 4) := by
  have hG0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  have hL₀1 : (1 : ℝ) ≤ 1 + Real.log N := by
    have := Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ N)
    linarith
  have hV4 : (0 : ℝ) < V ^ 4 := by positivity
  rcases Finset.eq_empty_or_nonempty s with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  -- the trivial Cauchy–Schwarz bound `V² ≤ N·G`
  obtain ⟨r₀, hr₀⟩ := hne
  have hVNG : V ^ 2 ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
    have h1 := hlarge r₀ hr₀
    have h2 : ‖∑ n ∈ Finset.Icc 1 N, a n * (chi r₀) (n : ZMod d) *
        Complex.exp ((-Real.log n * pt r₀ : ℝ) * Complex.I)‖
        ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
      rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      calc ‖a n‖ * ‖(chi r₀) (n : ZMod d)‖ ≤ ‖a n‖ * 1 :=
            mul_le_mul_of_nonneg_left ((chi r₀).norm_le_one _) (norm_nonneg _)
        _ = ‖a n‖ := mul_one _
    have h3 : (∑ n ∈ Finset.Icc 1 N, ‖a n‖) ^ 2
        ≤ (N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 := by
      have h4 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 N)
        (fun _ => (1 : ℝ)) (fun n => ‖a n‖)
      simp only [one_mul, one_pow] at h4
      have h5 : (∑ _n ∈ Finset.Icc 1 N, (1 : ℝ)) = (N : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
        push_cast
        ring
      rwa [h5] at h4
    have h6 : V ^ 2 ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖) ^ 2 :=
      pow_le_pow_left₀ hV.le (h1.trans h2) 2
    linarith
  have hLV1 := large_values_mean d hd T hT N hN a V hV.le s chi pt hpt hsep hlarge
  -- multiplied-out form
  have hmul : (s.card : ℝ) * V ^ 4 ≤ 300 * (1 + Real.log N) ^ 2 *
      ((∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * N * V ^ 2
        + (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ^ 2 * N * ((d : ℝ) * T)) := by
    have h7 : (d : ℝ) * T * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * V ^ 2
        ≤ (d : ℝ) * T * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) *
            ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hVNG (by positivity)
    have h8 : (0 : ℝ) ≤ 300 * (1 + Real.log N) ^ 2 := by positivity
    calc (s.card : ℝ) * V ^ 4 = ((s.card : ℝ) * V ^ 2) * V ^ 2 := by ring
      _ ≤ (300 * (1 + Real.log N) ^ 2 * ((N : ℝ) + d * T) *
            ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * V ^ 2 :=
          mul_le_mul_of_nonneg_right hLV1 (sq_nonneg V)
      _ = 300 * (1 + Real.log N) ^ 2 *
            ((∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * N * V ^ 2)
          + 300 * (1 + Real.log N) ^ 2 *
            ((d : ℝ) * T * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * V ^ 2) := by ring
      _ ≤ 300 * (1 + Real.log N) ^ 2 *
            ((∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * N * V ^ 2)
          + 300 * (1 + Real.log N) ^ 2 *
            ((d : ℝ) * T * (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) *
              ((N : ℝ) * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2)) := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left h7 h8)
      _ = 300 * (1 + Real.log N) ^ 2 *
            ((∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * N * V ^ 2
              + (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ^ 2 * N * ((d : ℝ) * T)) := by ring
  have hle : (s.card : ℝ) ≤ (300 * (1 + Real.log N) ^ 2 *
      ((∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * N * V ^ 2
        + (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ^ 2 * N * ((d : ℝ) * T))) / V ^ 4 := by
    rw [le_div_iff₀ hV4]
    exact hmul
  refine hle.trans (le_of_eq ?_)
  field_simp

/-- The literal canonical Huxley shape `G·N/V² + G³·N·(dT)/V⁶`, recovered
under the EXTRA hypothesis `V² ≤ G`. WARNING: downstream zero-detection
typically has `V² ≈ N^{2σ} > N ≈ G`, so this hypothesis usually FAILS there;
`large_values_huxley` is the operative statement. Included only for
shape-compatibility with BVPLAN §4 (Z6b). -/
theorem large_values_huxley_canonical {ι : Type*} (d : ℕ) (hd : 0 < d) (T : ℝ)
    (hT : 2 ≤ T) (N : ℕ) (hN : 1 ≤ N) (a : ℕ → ℂ) (V : ℝ) (hV : 0 < V)
    (s : Finset ι) (chi : ι → DirichletCharacter ℂ d) (pt : ι → ℝ)
    (hpt : ∀ r ∈ s, |pt r| ≤ T)
    (hsep : ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → chi r = chi r' → 1 ≤ |pt r - pt r'|)
    (hlarge : ∀ r ∈ s, V ≤ ‖∑ n ∈ Finset.Icc 1 N,
        a n * (chi r) (n : ZMod d) *
          Complex.exp ((-Real.log n * pt r : ℝ) * Complex.I)‖)
    (hVG : V ^ 2 ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) :
    (s.card : ℝ) ≤ 300 * (1 + Real.log N) ^ 2 *
      ((∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) * N / V ^ 2
        + (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ^ 3 * N * ((d : ℝ) * T) / V ^ 6) := by
  have hG0 : (0 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => by positivity
  refine (large_values_huxley d hd T hT N hN a V hV s chi pt hpt hsep hlarge).trans ?_
  have h2 : (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ^ 2 * N * ((d : ℝ) * T) / V ^ 4
      ≤ (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ^ 3 * N * ((d : ℝ) * T) / V ^ 6 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤
        (∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2) ^ 2 * N * ((d : ℝ) * T) * V ^ 4)
      (sub_nonneg.2 hVG)]
  have h3 : (0 : ℝ) ≤ 300 * (1 + Real.log N) ^ 2 := by positivity
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl h2) h3

end LargeValues
end Carmichael

