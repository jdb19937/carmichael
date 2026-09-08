/-
Route Z, sortie Z4a: growth bounds for Dirichlet L-functions, d-uniform.

Deliverables (all constants explicit numerals, `d = N` the modulus):

* `norm_LFunction_le_of_re_pos` — for nontrivial `χ mod N` and `0 < Re s`,
  `‖L(s,χ)‖ ≤ N·‖s‖·(1 + 1/Re s)`.  Engine: Abel summation of `∑ χ(n) n^{−s}`
  against the trivial period bound `‖∑_{k<n} χ(k)‖ ≤ N`, giving an everywhere-
  convergent series on `Re s > 0` that agrees with `LSeries` on `Re s > 1`,
  hence with the entire `LFunction` on `Re s > 0` by analytic continuation.
* `norm_LFunction_le_of_one_quarter_le_re` — the numeral form
  `‖L(s,χ)‖ ≤ 5·N·(2 + ‖s‖)` on `Re s ≥ 1/4`.
* `norm_LFunction_le_left_strip` — for primitive nontrivial `χ` and
  `−1/2 ≤ Re s ≤ 1/2`, `‖L(s,χ)‖ ≤ 18·N³·(2 + ‖s‖)²`.  Engine: the functional
  equation `IsPrimitive.completedLFunction_one_sub` plus the Deligne-factor
  reflection formulas `inv_Gammaℝ_one_sub` / `inv_Gammaℝ_two_sub`, which reduce
  everything to the strip bound `‖Γ(1−s)·sin(π(s+a)/2)‖ ≤ 3(2+‖s‖)`.  The
  latter is proved by Phragmén–Lindelöf on the strip `−1/2 ≤ Re s ≤ 1/2`,
  using the exact modulus `‖Γ(1/2+it)‖² = π/cosh(πt)` on the boundary lines
  (no Stirling needed).
* `norm_LFunction_le_of_neg_half_le_re` — combined polynomial bound
  `‖L(s,χ)‖ ≤ 18·(N·(2+‖s‖))³` on all of `Re s ≥ −1/2` (primitive nontrivial χ).
* `one_third_le_norm_LFunction_of_two_le_re` — `‖L(s,χ)‖ ≥ 1/3` on `Re s ≥ 2`
  (any χ), and `norm_deriv_LFunction_le_of_two_le_re` — `‖L′(s,χ)‖ ≤ 6` there.

These feed Z4b (Jensen zero counts) and Z4c (Landau partial fractions);
see routez/Z0a-ledger.md §7 and BVPLAN.md §4.
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace Carmichael

open Complex Finset Filter Set
open scoped Real Topology

/-! ### Elementary real and Γ-function estimates -/

section RealLemmas

/-- `e^{|x|} ≤ 2 cosh x`. -/
lemma exp_abs_le_two_mul_cosh (x : ℝ) : Real.exp |x| ≤ 2 * Real.cosh x := by
  rcases abs_cases x with ⟨h, _⟩ | ⟨h, _⟩ <;>
    rw [h, Real.cosh_eq] <;>
    [linarith [(Real.exp_pos (-x)).le]; linarith [(Real.exp_pos x).le]]

/-- Complex sine grows at most like `e^{|Im z|}`. -/
lemma norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin_eq]
  calc ‖Complex.sin z.re * Complex.cosh z.im + Complex.cos z.re * Complex.sinh z.im * I‖
      ≤ ‖Complex.sin z.re * Complex.cosh z.im‖ +
        ‖Complex.cos z.re * Complex.sinh z.im * I‖ := norm_add_le _ _
    _ = ‖((Real.sin z.re * Real.cosh z.im : ℝ) : ℂ)‖ +
        ‖((Real.cos z.re * Real.sinh z.im : ℝ) : ℂ) * I‖ := by
        rw [← Complex.ofReal_sin, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
          ← Complex.ofReal_sinh, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    _ = |Real.sin z.re * Real.cosh z.im| + |Real.cos z.re * Real.sinh z.im| := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
    _ = |Real.sin z.re| * |Real.cosh z.im| + |Real.cos z.re| * |Real.sinh z.im| := by
        rw [abs_mul, abs_mul]
    _ ≤ 1 * Real.cosh |z.im| + 1 * Real.sinh |z.im| := by
        rw [abs_of_pos (Real.cosh_pos _)]
        gcongr
        · exact Real.abs_sin_le_one _
        · rw [Real.cosh_abs]
        · exact Real.abs_cos_le_one _
        · rw [Real.abs_sinh]
    _ = Real.exp |z.im| := by rw [one_mul, one_mul, Real.cosh_add_sinh]

/-- Trivial bound for the Euler integral: `‖Γ(z)‖ ≤ Γ(Re z)` on `Re z > 0`. -/
lemma norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz, Complex.GammaIntegral]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
    Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re, Complex.one_re]

/-- `Γ(x) ≤ 2` on `[1,2]`, from `t^{x−1} ≤ 1 + t` under the Euler integral. -/
lemma Real_Gamma_le_two {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) : Real.Gamma x ≤ 2 := by
  have hint1 : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (-t) * t ^ ((1:ℝ) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent one_pos
  have hint2 : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (-t) * t ^ ((2:ℝ) - 1)) (Ioi 0) :=
    Real.GammaIntegral_convergent two_pos
  have hx0 : 0 < x := by linarith
  rw [Real.Gamma_eq_integral hx0]
  have step : ∫ t in Ioi (0:ℝ), Real.exp (-t) * t ^ (x - 1) ≤
      ∫ t in Ioi (0:ℝ), (Real.exp (-t) * t ^ ((1:ℝ) - 1) +
        Real.exp (-t) * t ^ ((2:ℝ) - 1)) := by
    refine MeasureTheory.setIntegral_mono_on (Real.GammaIntegral_convergent hx0)
      (hint1.add hint2) measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) < t := ht
    have hbound : t ^ (x - 1) ≤ t ^ ((1:ℝ) - 1) + t ^ ((2:ℝ) - 1) := by
      rcases le_or_gt t 1 with h | h
      · have : t ^ (x - 1) ≤ (1:ℝ) := Real.rpow_le_one ht0.le h (by linarith)
        have h0 : t ^ ((1:ℝ) - 1) = 1 := by norm_num
        have h1' : (0:ℝ) ≤ t ^ ((2:ℝ) - 1) := Real.rpow_nonneg ht0.le _
        linarith
      · have : t ^ (x - 1) ≤ t ^ ((2:ℝ) - 1) :=
          Real.rpow_le_rpow_of_exponent_le h.le (by linarith)
        have h1' : (0:ℝ) ≤ t ^ ((1:ℝ) - 1) := Real.rpow_nonneg ht0.le _
        linarith
    have := mul_le_mul_of_nonneg_left hbound (Real.exp_nonneg (-t))
    linarith [this]
  calc ∫ t in Ioi (0:ℝ), Real.exp (-t) * t ^ (x - 1)
      ≤ ∫ t in Ioi (0:ℝ), (Real.exp (-t) * t ^ ((1:ℝ) - 1) +
          Real.exp (-t) * t ^ ((2:ℝ) - 1)) := step
    _ = (∫ t in Ioi (0:ℝ), Real.exp (-t) * t ^ ((1:ℝ) - 1)) +
        ∫ t in Ioi (0:ℝ), Real.exp (-t) * t ^ ((2:ℝ) - 1) :=
      MeasureTheory.integral_add hint1 hint2
    _ = Real.Gamma 1 + Real.Gamma 2 := by
      rw [← Real.Gamma_eq_integral one_pos, ← Real.Gamma_eq_integral two_pos]
    _ = 2 := by rw [Real.Gamma_one, Real.Gamma_two]; norm_num

/-- `Γ(x) ≤ 4` on `[1/2, 3/2]`. -/
lemma Real_Gamma_le_four {x : ℝ} (h1 : 1/2 ≤ x) (h2 : x ≤ 3/2) : Real.Gamma x ≤ 4 := by
  rcases le_or_gt 1 x with h | h
  · linarith [Real_Gamma_le_two h (by linarith)]
  · have hx0 : 0 < x := by linarith
    have hΓ1 : Real.Gamma (x + 1) ≤ 2 := Real_Gamma_le_two (by linarith) (by linarith)
    have hΓ2 : Real.Gamma (x + 1) = x * Real.Gamma x := Real.Gamma_add_one hx0.ne'
    have hpos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx0
    nlinarith

/-- Mean-value inequality `σ (x+1)^{−σ−1} ≤ x^{−σ} − (x+1)^{−σ}` for `x ≥ 1`. -/
lemma rpow_mvt {σ : ℝ} (hσ : 0 < σ) {x : ℝ} (hx : 1 ≤ x) :
    σ * (x + 1) ^ (-σ - 1) ≤ x ^ (-σ) - (x + 1) ^ (-σ) := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
  have hderiv : ∀ y ∈ Ioo x (x + 1),
      HasDerivAt (fun y : ℝ => -(y ^ (-σ))) (σ * y ^ (-σ - 1)) y := by
    intro y hy
    have hy0 : y ≠ 0 := by nlinarith [hy.1]
    have h0 := (Real.hasDerivAt_rpow_const (p := -σ) (x := y) (Or.inl hy0)).neg
    rw [show -(-σ * y ^ (-σ - 1)) = σ * y ^ (-σ - 1) from by ring] at h0
    exact h0
  have hcont : ContinuousOn (fun y : ℝ => -(y ^ (-σ))) (Icc x (x + 1)) := by
    intro y hy
    have hy0 : y ≠ 0 := by nlinarith [hy.1]
    exact ((Real.hasDerivAt_rpow_const (p := -σ) (Or.inl hy0)).neg).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (fun y : ℝ => -(y ^ (-σ)))
    (fun y => σ * y ^ (-σ - 1)) (by linarith : x < x + 1) hcont hderiv
  have hcx : 0 < c := lt_trans hx0 hc.1
  have hmono : (x + 1) ^ (-σ - 1) ≤ c ^ (-σ - 1) :=
    Real.rpow_le_rpow_of_nonpos hcx hc.2.le (by linarith)
  have heq : σ * c ^ (-σ - 1) = x ^ (-σ) - (x + 1) ^ (-σ) := by
    rw [hc']
    have : x + 1 - x = 1 := by ring
    rw [this, div_one]
    ring
  nlinarith [hmono, hσ.le]

private lemma sum_range_rpow_aux {σ : ℝ} (hσ : 0 < σ) (K : ℕ) :
    σ * ∑ k ∈ range (K + 2), (k : ℝ) ^ (-σ - 1) ≤ σ + 1 - ((K : ℝ) + 1) ^ (-σ) := by
  induction K with
  | zero =>
      have h0 : ((0:ℕ) : ℝ) ^ (-σ - 1) = 0 := by
        rw [Nat.cast_zero]; exact Real.zero_rpow (ne_of_lt (by linarith))
      have h1 : ((1:ℕ) : ℝ) ^ (-σ - 1) = 1 := by rw [Nat.cast_one]; exact Real.one_rpow _
      rw [show (0:ℕ) + 2 = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one, h0, h1]
      norm_num [Real.one_rpow]
  | succ K ih =>
      rw [show K + 1 + 2 = (K + 2) + 1 from rfl, Finset.sum_range_succ, mul_add]
      have hmvt := rpow_mvt hσ (x := (K : ℝ) + 1)
        (by have := Nat.cast_nonneg (α := ℝ) K; linarith)
      have hcast : ((K + 2 : ℕ) : ℝ) = ((K : ℝ) + 1) + 1 := by push_cast; ring
      have hcast2 : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
      rw [hcast, hcast2]
      linarith

/-- `∑_{k<K} k^{−σ−1} ≤ 1 + 1/σ` for `σ > 0` (the `k = 0` term vanishes). -/
lemma sum_range_rpow_le {σ : ℝ} (hσ : 0 < σ) (K : ℕ) :
    ∑ k ∈ range K, (k : ℝ) ^ (-σ - 1) ≤ 1 + 1 / σ := by
  have hmono : ∑ k ∈ range K, (k : ℝ) ^ (-σ - 1) ≤
      ∑ k ∈ range (K + 2), (k : ℝ) ^ (-σ - 1) := by
    have hsub : range K ⊆ range (K + 2) := fun x hx =>
      Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega)
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun k _ _ => Real.rpow_nonneg (Nat.cast_nonneg k) _
  have haux := sum_range_rpow_aux hσ K
  have hpow : (0:ℝ) ≤ ((K : ℝ) + 1) ^ (-σ) := Real.rpow_nonneg (by positivity) _
  have h2 : σ * ∑ k ∈ range (K + 2), (k : ℝ) ^ (-σ - 1) ≤ σ + 1 := by linarith
  have h3 : σ * ∑ k ∈ range K, (k : ℝ) ^ (-σ - 1) ≤ σ + 1 :=
    le_trans (mul_le_mul_of_nonneg_left hmono hσ.le) h2
  have h4 : ∑ k ∈ range K, (k : ℝ) ^ (-σ - 1) ≤ (σ + 1) / σ :=
    (le_div_iff₀' hσ).mpr h3
  calc ∑ k ∈ range K, (k : ℝ) ^ (-σ - 1) ≤ (σ + 1) / σ := h4
    _ = 1 + 1 / σ := by rw [add_div, div_self hσ.ne']

/-- Complex mean-value bound: `‖k^{−s} − (k+1)^{−s}‖ ≤ ‖s‖ k^{−Re s − 1}` for `k ≥ 1`. -/
lemma norm_cpow_sub_cpow_le {s : ℂ} (hs : 0 < s.re) {k : ℕ} (hk : 1 ≤ k) :
    ‖((k : ℕ) : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
  have hk0 : (0:ℝ) < (k : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hsne : -s ≠ 0 := by
    simp only [ne_eq, neg_eq_zero]
    intro h; rw [h] at hs; simp at hs
  have hIcc : Convex ℝ (Icc (k:ℝ) ((k:ℝ) + 1)) := convex_Icc _ _
  have hderiv : ∀ y ∈ Icc (k:ℝ) ((k:ℝ) + 1),
      HasDerivWithinAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ (-s))
        ((-s) * ((y : ℝ) : ℂ) ^ (-s - 1)) (Icc (k:ℝ) ((k:ℝ) + 1)) y := by
    intro y hy
    have hy0 : y ≠ 0 := by have := hy.1; nlinarith
    exact (hasDerivAt_ofReal_cpow_const hy0 hsne).hasDerivWithinAt
  have hbound : ∀ y ∈ Icc (k:ℝ) ((k:ℝ) + 1),
      ‖(-s) * ((y : ℝ) : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
    intro y hy
    have hy0 : (0:ℝ) < y := lt_of_lt_of_le hk0 hy.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
    gcongr ‖s‖ * ?_
    exact Real.rpow_le_rpow_of_nonpos hk0 hy.1 (by linarith)
  have hx : (k:ℝ) ∈ Icc (k:ℝ) ((k:ℝ) + 1) := ⟨le_refl _, by linarith⟩
  have hy : (k:ℝ) + 1 ∈ Icc (k:ℝ) ((k:ℝ) + 1) := ⟨by linarith, le_refl _⟩
  have key := hIcc.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound hx hy
  have hcast : (((k:ℝ) + 1 : ℝ) : ℂ) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
  have hcast2 : (((k:ℝ) : ℝ) : ℂ) = ((k : ℕ) : ℂ) := by push_cast; ring
  calc ‖((k : ℕ) : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s)‖
      = ‖(((k:ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((k:ℝ) : ℝ) : ℂ) ^ (-s)‖ := by
        rw [hcast, hcast2, norm_sub_rev]
    _ ≤ ‖s‖ * (k : ℝ) ^ (-s.re - 1) * ‖((k:ℝ) + 1) - (k:ℝ)‖ := key
    _ = ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by norm_num

end RealLemmas

/-! ### Character sums: the trivial period bound -/

section CharSum

variable {N : ℕ} [NeZero N]

/-- Running sum `∑_{k < n} χ(k)` of a Dirichlet character. -/
noncomputable def charSum (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  ∑ k ∈ range n, χ (k : ZMod N)

private lemma sum_range_zmod (φ : ZMod N → ℂ) :
    ∑ j ∈ range N, φ ((j : ℕ) : ZMod N) = ∑ x : ZMod N, φ x := by
  refine Finset.sum_nbij' (i := fun j => ((j : ℕ) : ZMod N)) (j := fun x => x.val)
    (fun a _ => Finset.mem_univ _)
    (fun x _ => Finset.mem_range.mpr (ZMod.val_lt x))
    (fun a ha => ?_) (fun x _ => ZMod.natCast_zmod_val x) (fun a _ => rfl)
  have := Finset.mem_range.mp ha
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt this]

private lemma charSum_add_period (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (n : ℕ) :
    charSum χ (n + N) = charSum χ n := by
  unfold charSum
  have hcast : ∀ j : ℕ, ((n + j : ℕ) : ZMod N) = ((n : ℕ) : ZMod N) + ((j : ℕ) : ZMod N) := by
    intro j; push_cast; ring
  have htail : ∑ i ∈ Finset.Ico n (n + N), χ ((i : ℕ) : ZMod N) = 0 := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    have h1 : ∑ j ∈ range N, χ ((n + j : ℕ) : ZMod N)
        = ∑ x : ZMod N, χ (((n : ℕ) : ZMod N) + x) := by
      rw [← sum_range_zmod (fun x => χ (((n : ℕ) : ZMod N) + x))]
      exact Finset.sum_congr rfl fun j _ => by rw [hcast]
    have h2 : ∑ x : ZMod N, χ (((n : ℕ) : ZMod N) + x) = ∑ x : ZMod N, χ x :=
      Fintype.sum_equiv (Equiv.addLeft ((n : ℕ) : ZMod N)) _ _ fun x => rfl
    rw [h1, h2, χ.sum_eq_zero_of_ne_one hχ]
  have hsplit : ∑ k ∈ range (n + N), χ ((k : ℕ) : ZMod N)
      = (∑ k ∈ range n, χ ((k : ℕ) : ZMod N))
        + ∑ i ∈ Finset.Ico n (n + N), χ ((i : ℕ) : ZMod N) := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le n) (Nat.le_add_right n N)).symm
  rw [hsplit, htail, add_zero]

private lemma charSum_mod (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (n : ℕ) :
    charSum χ n = charSum χ (n % N) := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases lt_or_ge n N with h | h
    · rw [Nat.mod_eq_of_lt h]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + N := ⟨n - N, by omega⟩
      rw [charSum_add_period χ hχ, ih m (by omega), Nat.add_mod_right]

/-- Trivial period bound: partial sums of a nontrivial character are bounded by the modulus. -/
lemma norm_charSum_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (n : ℕ) :
    ‖charSum χ n‖ ≤ N := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  rw [charSum_mod χ hχ]
  calc ‖∑ k ∈ range (n % N), χ ((k : ℕ) : ZMod N)‖
      ≤ ∑ k ∈ range (n % N), ‖χ ((k : ℕ) : ZMod N)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ range (n % N), (1:ℝ) := Finset.sum_le_sum fun k _ => χ.norm_le_one _
    _ = (n % N : ℕ) := by simp
    _ ≤ N := by exact_mod_cast (Nat.mod_lt n hN).le

private lemma char_zero_val (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    χ ((0 : ℕ) : ZMod N) = 0 := by
  have hN1 : N ≠ 1 := fun h => hχ (χ.level_one' h)
  have hN : 1 < N := by
    have := NeZero.ne N; omega
  have : Fact (1 < N) := ⟨hN⟩
  have : ¬IsUnit ((0 : ℕ) : ZMod N) := by
    rw [Nat.cast_zero]
    exact not_isUnit_zero
  exact χ.map_nonunit this

end CharSum

/-! ### Abel-summation continuation of the L-series -/

section Abel

variable {N : ℕ} [NeZero N]

/-- Term of the Abel-summed series for `L(s,χ)`. -/
noncomputable def Aterm (χ : DirichletCharacter ℂ N) (s : ℂ) (k : ℕ) : ℂ :=
  charSum χ (k + 1) * (((k : ℕ) : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s))

/-- Abel-summed series; agrees with `LFunction χ` on `Re s > 0` for nontrivial `χ`. -/
noncomputable def Afun (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  ∑' k, Aterm χ s k

omit [NeZero N] in
private lemma abel_identity (χ : DirichletCharacter ℂ N) (s : ℂ) (M : ℕ) :
    ∑ k ∈ range (M + 1), χ ((k : ℕ) : ZMod N) * ((k : ℕ) : ℂ) ^ (-s)
      = (∑ k ∈ range M, Aterm χ s k) + charSum χ (M + 1) * ((M : ℕ) : ℂ) ^ (-s) := by
  induction M with
  | zero => simp [Aterm, charSum]
  | succ M ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ (f := Aterm χ s)]
      have hcs : charSum χ (M + 2) = charSum χ (M + 1) + χ ((M + 1 : ℕ) : ZMod N) := by
        unfold charSum; rw [Finset.sum_range_succ]
      rw [Aterm, hcs]
      ring

private lemma norm_Aterm_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) (k : ℕ) :
    ‖Aterm χ s k‖ ≤ (N : ℝ) * ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 : charSum χ 1 = 0 := by
      unfold charSum; rw [Finset.sum_range_one, char_zero_val χ hχ]
    rw [Aterm, h0, zero_mul, norm_zero, Nat.cast_zero,
      Real.zero_rpow (ne_of_lt (by linarith) : -s.re - 1 ≠ 0), mul_zero]
  · rw [Aterm, norm_mul]
    have h1 := norm_charSum_le χ hχ (k + 1)
    have h2 := norm_cpow_sub_cpow_le hs hk
    calc ‖charSum χ (k + 1)‖ * ‖((k : ℕ) : ℂ) ^ (-s) - ((k + 1 : ℕ) : ℂ) ^ (-s)‖
        ≤ (N : ℝ) * (‖s‖ * (k : ℝ) ^ (-s.re - 1)) := by
          exact mul_le_mul h1 h2 (norm_nonneg _) (Nat.cast_nonneg N)
      _ = (N : ℝ) * ‖s‖ * (k : ℝ) ^ (-s.re - 1) := by ring

private lemma summable_majorant {s : ℂ} (hs : 0 < s.re) (c : ℝ) :
    Summable fun k : ℕ => c * (k : ℝ) ^ (-s.re - 1) :=
  (Real.summable_nat_rpow.mpr (by linarith)).mul_left c

private lemma summable_norm_Aterm (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) : Summable fun k => ‖Aterm χ s k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_Aterm_le χ hχ hs)
    (summable_majorant hs _)

private lemma norm_Afun_le (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) : ‖Afun χ s‖ ≤ (N : ℝ) * ‖s‖ * (1 + 1 / s.re) := by
  have hsum := summable_norm_Aterm χ hχ hs
  calc ‖Afun χ s‖ ≤ ∑' k, ‖Aterm χ s k‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' k : ℕ, (N : ℝ) * ‖s‖ * (k : ℝ) ^ (-s.re - 1) :=
        hsum.tsum_le_tsum (norm_Aterm_le χ hχ hs) (summable_majorant hs _)
    _ = (N : ℝ) * ‖s‖ * ∑' k : ℕ, (k : ℝ) ^ (-s.re - 1) := tsum_mul_left
    _ ≤ (N : ℝ) * ‖s‖ * (1 + 1 / s.re) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ (N:ℝ) * ‖s‖)
        exact Real.tsum_le_of_sum_range_le
          (fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _) (sum_range_rpow_le hs)

private lemma LSeries_eq_Afun (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 < s.re) : LSeries (χ ·) s = Afun χ s := by
  have hs0 : 0 < s.re := lt_trans one_pos hs
  have hsne : s ≠ 0 := fun h => by rw [h] at hs0; simp at hs0
  have hsum : LSeriesSummable (χ ·) s := χ.LSeriesSummable_of_one_lt_re hs
  have hterm : ∀ k : ℕ, LSeries.term (χ ·) s k = χ ((k : ℕ) : ZMod N) * ((k : ℕ) : ℂ) ^ (-s) := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · rw [LSeries.term_zero]
      have h0 : ((0:ℕ) : ℂ) = 0 := Nat.cast_zero
      rw [h0, Complex.zero_cpow (neg_ne_zero.mpr hsne), mul_zero]
    · rw [LSeries.term_of_ne_zero hk, Complex.cpow_neg, div_eq_mul_inv]
  have h1 : Tendsto (fun M => ∑ k ∈ range M, LSeries.term (χ ·) s k) atTop
      (𝓝 (LSeries (χ ·) s)) := hsum.hasSum.tendsto_sum_nat
  have h2 : Tendsto (fun M => ∑ k ∈ range (M + 1), χ ((k : ℕ) : ZMod N) * ((k : ℕ) : ℂ) ^ (-s))
      atTop (𝓝 (LSeries (χ ·) s)) := by
    have := (tendsto_add_atTop_iff_nat 1).mpr h1
    refine this.congr fun M => Finset.sum_congr rfl fun k _ => hterm k
  have h3 : Tendsto (fun M => (∑ k ∈ range M, Aterm χ s k) +
      charSum χ (M + 1) * ((M : ℕ) : ℂ) ^ (-s)) atTop (𝓝 (LSeries (χ ·) s)) := by
    refine h2.congr fun M => ?_
    exact abel_identity χ s M
  have h4 : Tendsto (fun M => ∑ k ∈ range M, Aterm χ s k) atTop (𝓝 (Afun χ s)) :=
    ((summable_norm_Aterm χ hχ hs0).of_norm).hasSum.tendsto_sum_nat
  have h5 : Tendsto (fun M => charSum χ (M + 1) * ((M : ℕ) : ℂ) ^ (-s)) atTop (𝓝 0) := by
    have hb : ∀ M : ℕ, ‖charSum χ (M + 1) * ((M : ℕ) : ℂ) ^ (-s)‖
        ≤ (N : ℝ) * (M : ℝ) ^ (-s.re) := by
      intro M
      rcases Nat.eq_zero_or_pos M with rfl | hM
      · have h0 : ((0:ℕ) : ℂ) = 0 := Nat.cast_zero
        rw [h0, Complex.zero_cpow (neg_ne_zero.mpr hsne), mul_zero, norm_zero,
          Nat.cast_zero, Real.zero_rpow (ne_of_lt (by linarith) : -s.re ≠ 0), mul_zero]
      · rw [norm_mul]
        have hM0 : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM
        have hnn : ‖((M : ℕ) : ℂ) ^ (-s)‖ = (M : ℝ) ^ (-s.re) := by
          rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hM0, Complex.neg_re]
        rw [hnn]
        exact mul_le_mul_of_nonneg_right (norm_charSum_le χ hχ (M + 1))
          (Real.rpow_nonneg hM0.le _)
    have htend : Tendsto (fun M : ℕ => (N : ℝ) * (M : ℝ) ^ (-s.re)) atTop (𝓝 0) := by
      have hbase : Tendsto (fun x : ℝ => x ^ (-s.re)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hs0
      have := (hbase.comp tendsto_natCast_atTop_atTop).const_mul (N : ℝ)
      simpa using this
    exact squeeze_zero_norm hb htend
  have := h4.add h5
  rw [add_zero] at this
  exact tendsto_nhds_unique h3 this

private lemma differentiableOn_Afun (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ (Afun χ) {s : ℂ | 0 < s.re} := by
  intro s₀ hs₀
  have hσ : 0 < s₀.re := hs₀
  set r : ℝ := s₀.re / 2 with hr
  have hrpos : 0 < r := by positivity
  suffices h : DifferentiableOn ℂ (Afun χ) (Metric.ball s₀ r) by
    exact (h.differentiableAt (Metric.ball_mem_nhds s₀ hrpos)).differentiableWithinAt
  have hre : ∀ w ∈ Metric.ball s₀ r, r ≤ w.re := by
    intro w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    have h1 : |(w - s₀).re| ≤ ‖w - s₀‖ := Complex.abs_re_le_norm _
    have h2 : |(w - s₀).re| < r := lt_of_le_of_lt h1 hw
    rw [Complex.sub_re, abs_lt] at h2
    have := h2.1
    linarith [h2.1]
  have hnorm : ∀ w ∈ Metric.ball s₀ r, ‖w‖ ≤ ‖s₀‖ + r := by
    intro w hw
    rw [Metric.mem_ball, Complex.dist_eq] at hw
    calc ‖w‖ = ‖s₀ + (w - s₀)‖ := by ring_nf
      _ ≤ ‖s₀‖ + ‖w - s₀‖ := norm_add_le _ _
      _ ≤ ‖s₀‖ + r := by linarith
  refine differentiableOn_tsum_of_summable_norm
    (u := fun k : ℕ => (N : ℝ) * (‖s₀‖ + r) * (k : ℝ) ^ (-r - 1))
    ?_ ?_ Metric.isOpen_ball ?_
  · exact ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _)
  · intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have h0 : (fun s : ℂ => Aterm χ s 0) = fun _ => 0 := by
        funext w
        have : charSum χ 1 = 0 := by
          unfold charSum; rw [Finset.sum_range_one, char_zero_val χ hχ]
        rw [Aterm, this, zero_mul]
      rw [h0]
      exact differentiableOn_const 0
    · have hk0 : ((k : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.pos_iff_ne_zero.mp hk
      have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero k
      have hneg : Differentiable ℂ (fun s : ℂ => -s) := differentiable_id.neg
      have hd : Differentiable ℂ (fun s : ℂ => Aterm χ s k) := by
        unfold Aterm
        exact ((hneg.const_cpow (Or.inl hk0)).sub
          (hneg.const_cpow (Or.inl hk1))).const_mul _
      exact hd.differentiableOn
  · intro k w hw
    have hwre : 0 < w.re := lt_of_lt_of_le hrpos (hre w hw)
    calc ‖Aterm χ w k‖ ≤ (N : ℝ) * ‖w‖ * (k : ℝ) ^ (-w.re - 1) := norm_Aterm_le χ hχ hwre k
      _ ≤ (N : ℝ) * (‖s₀‖ + r) * (k : ℝ) ^ (-r - 1) := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · rw [Nat.cast_zero, Real.zero_rpow (ne_of_lt (by linarith) : -w.re - 1 ≠ 0),
              Real.zero_rpow (ne_of_lt (by linarith) : -r - 1 ≠ 0), mul_zero, mul_zero]
          · have hk1 : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
            have hrw : (k : ℝ) ^ (-w.re - 1) ≤ (k : ℝ) ^ (-r - 1) :=
              Real.rpow_le_rpow_of_exponent_le hk1 (by linarith [hre w hw])
            have h1 : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
            have h2 : ‖w‖ ≤ ‖s₀‖ + r := hnorm w hw
            have h3 : (0:ℝ) ≤ (k : ℝ) ^ (-w.re - 1) := Real.rpow_nonneg (by positivity) _
            have h4 : (0:ℝ) ≤ ‖s₀‖ + r := by positivity
            calc (N : ℝ) * ‖w‖ * (k : ℝ) ^ (-w.re - 1)
                = (N : ℝ) * (‖w‖ * (k : ℝ) ^ (-w.re - 1)) := by ring
              _ ≤ (N : ℝ) * ((‖s₀‖ + r) * (k : ℝ) ^ (-r - 1)) :=
                  mul_le_mul_of_nonneg_left (mul_le_mul h2 hrw h3 h4) h1
              _ = (N : ℝ) * (‖s₀‖ + r) * (k : ℝ) ^ (-r - 1) := by ring

private lemma LFunction_eqOn_Afun (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    Set.EqOn (DirichletCharacter.LFunction χ) (Afun χ) {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := by
    have : {s : ℂ | 0 < s.re} = Complex.re ⁻¹' (Set.Ioi 0) := rfl
    rw [this]
    exact isOpen_Ioi.preimage Complex.continuous_re
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (𝕜 := ℂ)
    (f := DirichletCharacter.LFunction χ) (g := Afun χ) (z₀ := (2 : ℂ)) ?_ ?_ ?_ ?_ ?_
  · exact ((DirichletCharacter.differentiable_LFunction hχ).differentiableOn).analyticOnNhd hopen
  · exact (differentiableOn_Afun χ hχ).analyticOnNhd hopen
  · exact (convex_halfSpace_re_gt 0).isPreconnected
  · show (0:ℝ) < (2:ℂ).re
    norm_num
  · have hmem : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) := by
      have : IsOpen {s : ℂ | 1 < s.re} := by
        have : {s : ℂ | 1 < s.re} = Complex.re ⁻¹' (Set.Ioi 1) := rfl
        rw [this]
        exact isOpen_Ioi.preimage Complex.continuous_re
      refine this.mem_nhds ?_
      show (1:ℝ) < (2:ℂ).re
      norm_num
    filter_upwards [hmem] with z hz
    rw [DirichletCharacter.LFunction_eq_LSeries χ hz, LSeries_eq_Afun χ hχ hz]

/-- **Z4a upper bound, general form.** For nontrivial `χ mod N` and `Re s > 0`,
`‖L(s,χ)‖ ≤ N·‖s‖·(1 + 1/Re s)`. -/
theorem norm_LFunction_le_of_re_pos (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {s : ℂ}
    (hs : 0 < s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ (N : ℝ) * ‖s‖ * (1 + 1 / s.re) := by
  rw [LFunction_eqOn_Afun χ hχ (by exact hs : s ∈ {s : ℂ | 0 < s.re})]
  exact norm_Afun_le χ hχ hs

/-- **Z4a upper bound, right half-plane numeral form.** For nontrivial `χ mod N` and
`Re s ≥ 1/4`, `‖L(s,χ)‖ ≤ 5·N·(2 + ‖s‖)`. -/
theorem norm_LFunction_le_of_one_quarter_le_re (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1/4 ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 5 * (N : ℝ) * (2 + ‖s‖) := by
  have hs0 : 0 < s.re := lt_of_lt_of_le (by norm_num) hs
  have h1 : 1 + 1 / s.re ≤ 5 := by
    have : 1 / s.re ≤ 4 := by
      rw [div_le_iff₀ hs0]; linarith
    linarith
  have hN0 : (0:ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  calc ‖DirichletCharacter.LFunction χ s‖ ≤ (N : ℝ) * ‖s‖ * (1 + 1 / s.re) :=
        norm_LFunction_le_of_re_pos χ hχ hs0
    _ ≤ (N : ℝ) * (2 + ‖s‖) * 5 := by
        have hb : (0:ℝ) ≤ 1 + 1 / s.re := by positivity
        have hs2 : ‖s‖ ≤ 2 + ‖s‖ := by linarith [norm_nonneg s]
        nlinarith [norm_nonneg s, mul_nonneg hN0 (norm_nonneg s)]
    _ = 5 * (N : ℝ) * (2 + ‖s‖) := by ring

end Abel

/-! ### Lower bound and `L′` bound at `Re s ≥ 2` -/

section TwoLine

variable {N : ℕ} [NeZero N]

private lemma sum_inv_sq_tail_le (K : ℕ) :
    ∑ j ∈ range K, (((j : ℝ) + 2) ^ 2)⁻¹ ≤ 2/3 - ((K : ℝ) + 3/2)⁻¹ := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [Finset.sum_range_succ]
      have h1 : (0:ℝ) < (K : ℝ) + 3/2 := by positivity
      have h2 : (0:ℝ) < (K : ℝ) + 5/2 := by positivity
      have h3 : (0:ℝ) < ((K : ℝ) + 2) ^ 2 := by positivity
      have key : (((K : ℝ) + 2) ^ 2)⁻¹ ≤ ((K : ℝ) + 3/2)⁻¹ - ((K : ℝ) + 5/2)⁻¹ := by
        have heq : ((K : ℝ) + 3/2)⁻¹ - ((K : ℝ) + 5/2)⁻¹
            = (((K : ℝ) + 3/2) * ((K : ℝ) + 5/2))⁻¹ := by
          field_simp
          ring
        rw [heq]
        gcongr
        nlinarith
      have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have : ((K : ℝ) + 1) + 3/2 = (K : ℝ) + 5/2 := by ring
      rw [this]
      linarith

private lemma summable_inv_sq_shift :
    Summable fun j : ℕ => (((j : ℝ) + 2) ^ 2)⁻¹ := by
  have h := (Real.summable_nat_rpow (p := (-2:ℝ))).mpr (by norm_num)
  have h2 := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ ((-2):ℝ)) 2).mpr h
  refine h2.congr fun j => ?_
  have hj : (0:ℝ) < (j : ℝ) + 2 := by positivity
  have hcast : ((j + 2 : ℕ) : ℝ) = (j : ℝ) + 2 := by push_cast; ring
  rw [hcast, Real.rpow_neg hj.le, Real.rpow_two]

/-- **Z4a lower bound at `Re s ≥ 2`.** `‖L(s,χ)‖ ≥ 1/3` for every Dirichlet character. -/
theorem one_third_le_norm_LFunction_of_two_le_re (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 2 ≤ s.re) : 1/3 ≤ ‖DirichletCharacter.LFunction χ s‖ := by
  have hs1 : 1 < s.re := by linarith
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs1]
  have hsum : LSeriesSummable (χ ·) s := χ.LSeriesSummable_of_one_lt_re hs1
  have hsum1 : Summable fun n => LSeries.term (χ ·) s (n + 1) :=
    (summable_nat_add_iff 1).mpr hsum
  have hsum2 : Summable fun n => LSeries.term (χ ·) s (n + 2) := by
    have := (summable_nat_add_iff 2).mpr hsum
    exact this
  have hsplit : LSeries (χ ·) s = LSeries.term (χ ·) s 0 + (LSeries.term (χ ·) s 1 +
      ∑' n, LSeries.term (χ ·) s (n + 2)) := by
    rw [LSeries, hsum.tsum_eq_zero_add, hsum1.tsum_eq_zero_add]
  have hterm0 : LSeries.term (χ ·) s 0 = 0 := LSeries.term_zero _ _
  have hterm1 : LSeries.term (χ ·) s 1 = 1 := by
    rw [LSeries.term_of_ne_zero one_ne_zero]
    norm_num
  have htail : ‖∑' n, LSeries.term (χ ·) s (n + 2)‖ ≤ 2/3 := by
    have hbound : ∀ n : ℕ, ‖LSeries.term (χ ·) s (n + 2)‖ ≤ (((n : ℝ) + 2) ^ 2)⁻¹ := by
      intro n
      rw [LSeries.term_of_ne_zero (by omega : n + 2 ≠ 0), norm_div]
      have hpos : (0:ℝ) < ((n + 2 : ℕ) : ℝ) := by positivity
      have hnorm : ‖((n + 2 : ℕ) : ℂ) ^ s‖ = ((n + 2 : ℕ) : ℝ) ^ s.re := by
        rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
      rw [hnorm]
      have hchi : ‖χ (((n + 2 : ℕ)) : ZMod N)‖ ≤ 1 := χ.norm_le_one _
      have hden : (((n : ℝ) + 2) ^ 2) ≤ ((n + 2 : ℕ) : ℝ) ^ s.re := by
        have hcast : ((n + 2 : ℕ) : ℝ) = (n : ℝ) + 2 := by push_cast; ring
        rw [hcast]
        calc ((n : ℝ) + 2) ^ 2 = ((n : ℝ) + 2) ^ ((2:ℕ) : ℝ) := by
              rw [Real.rpow_natCast]
          _ ≤ ((n : ℝ) + 2) ^ s.re := by
              apply Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) n])
              exact_mod_cast hs
      have hden0 : (0:ℝ) < ((n : ℝ) + 2) ^ 2 := by positivity
      calc ‖χ (((n + 2 : ℕ)) : ZMod N)‖ / ((n + 2 : ℕ) : ℝ) ^ s.re
          ≤ 1 / (((n : ℝ) + 2) ^ 2) := div_le_div₀ zero_le_one hchi hden0 hden
        _ = (((n : ℝ) + 2) ^ 2)⁻¹ := one_div _
    have hsumnorm : Summable fun n => ‖LSeries.term (χ ·) s (n + 2)‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound summable_inv_sq_shift
    calc ‖∑' n, LSeries.term (χ ·) s (n + 2)‖ ≤ ∑' n, ‖LSeries.term (χ ·) s (n + 2)‖ :=
          norm_tsum_le_tsum_norm hsumnorm
      _ ≤ ∑' n : ℕ, (((n : ℝ) + 2) ^ 2)⁻¹ :=
          hsumnorm.tsum_le_tsum hbound summable_inv_sq_shift
      _ ≤ 2/3 := by
          apply Real.tsum_le_of_sum_range_le (fun n => by positivity)
          intro K
          have := sum_inv_sq_tail_le K
          have h0 : (0:ℝ) < ((K : ℝ) + 3/2)⁻¹ := by positivity
          linarith
  rw [hsplit, hterm0, hterm1, zero_add]
  set R := ∑' n, LSeries.term (χ ·) s (n + 2)
  have := norm_add_le (1 + R) (-R)
  simp only [add_neg_cancel_right, norm_neg] at this
  have h1 : ‖(1:ℂ)‖ = 1 := norm_one
  rw [h1] at this
  linarith

/-- **Z4a `L′` bound at `Re s ≥ 2`.** `‖L′(s,χ)‖ ≤ 6`, uniformly in the modulus. -/
theorem norm_deriv_LFunction_le_of_two_le_re (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 2 ≤ s.re) : ‖deriv (DirichletCharacter.LFunction χ) s‖ ≤ 6 := by
  have hs1 : 1 < s.re := by linarith
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs1]
  have habs : LSeries.abscissaOfAbsConv (χ ·) < s.re := by
    have h1 : LSeries.abscissaOfAbsConv (χ ·) ≤ (1:ℝ) := by
      apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
      intro y hy
      exact χ.LSeriesSummable_of_one_lt_re (by exact_mod_cast hy)
    calc LSeries.abscissaOfAbsConv (χ ·) ≤ ((1:ℝ) : EReal) := h1
      _ < (s.re : EReal) := by exact_mod_cast hs1
  rw [LSeries_deriv habs, norm_neg]
  have hsum : LSeriesSummable (LSeries.logMul (χ ·)) s := LSeriesSummable_logMul_of_lt_re habs
  have hbound : ∀ n : ℕ, ‖LSeries.term (LSeries.logMul (χ ·)) s n‖
      ≤ 2 * (n : ℝ) ^ (-(1/2 : ℝ) - 1) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [LSeries.term_zero, norm_zero, Nat.cast_zero,
        Real.zero_rpow (by norm_num : -(1/2:ℝ) - 1 ≠ 0), mul_zero]
    · have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      rw [LSeries.term_of_ne_zero (Nat.pos_iff_ne_zero.mp hn), norm_div]
      have hnorm : ‖((n : ℕ) : ℂ) ^ s‖ = (n : ℝ) ^ s.re := by
        rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      rw [hnorm]
      have hlog : ‖LSeries.logMul (χ ·) n‖ ≤ Real.log n := by
        rw [LSeries.logMul]
        rw [norm_mul]
        have h1 : ‖Complex.log ((n : ℕ) : ℂ)‖ = Real.log n := by
          rw [← Complex.ofReal_natCast, ← Complex.ofReal_log hn0.le, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hn1)]
        rw [h1]
        have := χ.norm_le_one (((n : ℕ)) : ZMod N)
        nlinarith [Real.log_nonneg hn1]
      have hlog2 : Real.log n ≤ 2 * (n : ℝ) ^ (1/2 : ℝ) := by
        have hsq : (0:ℝ) < (n : ℝ) ^ (1/2 : ℝ) := Real.rpow_pos_of_pos hn0 _
        have h1 : Real.log ((n : ℝ) ^ (1/2 : ℝ)) = (1/2) * Real.log n :=
          Real.log_rpow hn0 _
        have h2 : Real.log ((n : ℝ) ^ (1/2 : ℝ)) ≤ (n : ℝ) ^ (1/2 : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos hsq
        linarith
      have hden : (n : ℝ) ^ ((2:ℕ) : ℝ) ≤ (n : ℝ) ^ s.re := by
        apply Real.rpow_le_rpow_of_exponent_le hn1
        exact_mod_cast hs
      have hden' : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ s.re := by
        convert hden using 2
        norm_num
      calc ‖LSeries.logMul (χ ·) n‖ / (n : ℝ) ^ s.re
          ≤ (2 * (n : ℝ) ^ (1/2 : ℝ)) / (n : ℝ) ^ (2 : ℝ) := by
            exact div_le_div₀ (by positivity) (hlog.trans hlog2) (by positivity) hden'
        _ = 2 * (n : ℝ) ^ (-(1/2 : ℝ) - 1) := by
            rw [mul_div_assoc, ← Real.rpow_sub hn0]
            norm_num
  have hsumnorm : Summable fun n => ‖LSeries.term (LSeries.logMul (χ ·)) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
      ((Real.summable_nat_rpow.mpr (by norm_num)).mul_left 2)
  calc ‖LSeries (LSeries.logMul (χ ·)) s‖ ≤ ∑' n, ‖LSeries.term (LSeries.logMul (χ ·)) s n‖ :=
        norm_tsum_le_tsum_norm hsumnorm
    _ ≤ ∑' n : ℕ, 2 * (n : ℝ) ^ (-(1/2 : ℝ) - 1) :=
        hsumnorm.tsum_le_tsum hbound
          ((Real.summable_nat_rpow.mpr (by norm_num)).mul_left 2)
    _ ≤ 6 := by
        have h := Real.tsum_le_of_sum_range_le
          (f := fun n : ℕ => 2 * (n : ℝ) ^ (-(1/2 : ℝ) - 1))
          (fun n => by positivity) (c := 2 * (1 + 1/(1/2 : ℝ))) ?_
        · calc ∑' n : ℕ, 2 * (n : ℝ) ^ (-(1/2 : ℝ) - 1) ≤ 2 * (1 + 1/(1/2 : ℝ)) := h
            _ = 6 := by norm_num
        · intro K
          rw [← Finset.mul_sum]
          have := sum_range_rpow_le (σ := (1/2 : ℝ)) (by norm_num) K
          linarith

end TwoLine

/-! ### The Phragmén–Lindelöf strip bound for `Γ(1−s)·sin(π(s+a)/2)` -/

section PLStrip

/-- Exact modulus of Γ on the critical line of the reflection formula:
`‖Γ(w)‖² = π / cosh(π·Im w)` when `Re w = 1/2`. -/
lemma norm_Gamma_sq_of_re_half {w : ℂ} (hw : w.re = 1/2) :
    ‖Complex.Gamma w‖ ^ 2 = π / Real.cosh (π * w.im) := by
  have hconj : (starRingEnd ℂ) w = 1 - w := by
    apply Complex.ext
    · simp [hw]; norm_num
    · simp
  have h1 : Complex.Gamma w * Complex.Gamma (1 - w) = ↑π / Complex.sin (↑π * w) :=
    Complex.Gamma_mul_Gamma_one_sub w
  rw [← hconj, Complex.Gamma_conj] at h1
  have hsin : Complex.sin (↑π * w) = ↑(Real.cosh (π * w.im)) := by
    have hw' : (↑π * w) = ↑(π/2) + ↑(π * w.im) * I := by
      apply Complex.ext
      · simp [Complex.mul_re, hw]; ring
      · simp [Complex.mul_im, hw]
    rw [hw', Complex.sin_add]
    have h2 : Complex.sin ↑(π/2) = 1 := by
      rw [← Complex.ofReal_sin, Real.sin_pi_div_two, Complex.ofReal_one]
    have h3 : Complex.cos ↑(π/2) = 0 := by
      rw [← Complex.ofReal_cos, Real.cos_pi_div_two, Complex.ofReal_zero]
    rw [h2, h3, Complex.cos_mul_I, Complex.ofReal_cosh]
    ring
  rw [hsin] at h1
  have h2 : Complex.Gamma w * (starRingEnd ℂ) (Complex.Gamma w)
      = ↑(‖Complex.Gamma w‖ ^ 2) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h2, ← Complex.ofReal_div] at h1
  exact_mod_cast h1

private lemma im_pi_mul (a : ℝ) (z : ℂ) : (↑π * (z + ↑a) / 2).im = π * z.im / 2 := by
  have h : ↑π * (z + ↑a) / 2 = ↑(π/2) * (z + ↑a) := by
    push_cast; ring
  rw [h, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
    Complex.ofReal_im, add_zero, zero_mul, add_zero]
  ring

private lemma norm_sin_pi_mul_le (a : ℝ) (z : ℂ) :
    ‖Complex.sin (↑π * (z + ↑a) / 2)‖ ≤ Real.exp (π * |z.im| / 2) := by
  refine (norm_sin_le_exp _).trans (le_of_eq ?_)
  rw [im_pi_mul, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (by norm_num : (0:ℝ) < 2)]

/-- **Phragmén–Lindelöf strip bound**: on `−1/2 ≤ Re s ≤ 1/2`,
`‖Γ(1−s)·sin(π(s+a)/2)‖ ≤ 3(2+‖s‖)` for every real shift `a`. -/
lemma norm_Gamma_one_sub_mul_sin_le (a : ℝ) {s : ℂ}
    (h1 : -(1/2 : ℝ) ≤ s.re) (h2 : s.re ≤ 1/2) :
    ‖Complex.Gamma (1 - s) * Complex.sin (↑π * (s + ↑a) / 2)‖ ≤ 3 * (2 + ‖s‖) := by
  set F : ℂ → ℂ :=
    fun z => Complex.Gamma (1 - z) * Complex.sin (↑π * (z + ↑a) / 2) / (2 - z) with hF
  have hden_ne : ∀ z : ℂ, z.re < 1 → (2 : ℂ) - z ≠ 0 := by
    intro z hz h
    have : ((2:ℂ) - z).re = 0 := by rw [h]; simp
    rw [Complex.sub_re] at this
    norm_num at this
    linarith [this]
  have hden_ge : ∀ z : ℂ, z.re ≤ 1/2 → (3/2 : ℝ) ≤ ‖(2:ℂ) - z‖ := by
    intro z hz
    have h1' : ((2:ℂ) - z).re = 2 - z.re := by simp
    calc (3/2 : ℝ) ≤ 2 - z.re := by linarith
      _ ≤ |((2:ℂ) - z).re| := by rw [h1']; exact le_abs_self _
      _ ≤ ‖(2:ℂ) - z‖ := Complex.abs_re_le_norm _
  have hΓbound : ∀ z : ℂ, -(1/2 : ℝ) ≤ z.re → z.re ≤ 1/2 →
      ‖Complex.Gamma (1 - z)‖ ≤ 4 := by
    intro z hza hzb
    have hre : (1 - z : ℂ).re = 1 - z.re := by simp
    have hpos : 0 < (1 - z : ℂ).re := by rw [hre]; linarith
    refine (norm_Gamma_le_Gamma_re hpos).trans ?_
    rw [hre]
    exact Real_Gamma_le_four (by linarith) (by linarith)
  -- Main Phragmén–Lindelöf estimate on the strip
  have main : ‖F s‖ ≤ 3 := by
    apply PhragmenLindelof.vertical_strip (a := -(1/2 : ℝ)) (b := (1/2 : ℝ)) (C := 3)
    -- differentiability
    · have hdiff : DifferentiableOn ℂ F {z : ℂ | z.re < 1} := by
        intro z hz
        have hz1 : z.re < 1 := hz
        have hΓ : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (1 - w)) z := by
          have hne : ∀ m : ℕ, 1 - z ≠ -m := by
            intro m h
            have := congrArg Complex.re h
            simp at this
            have hm : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg m
            linarith
          exact (Complex.differentiableAt_Gamma _ hne).comp z (by fun_prop)
        have hsin : DifferentiableAt ℂ (fun w : ℂ => Complex.sin (↑π * (w + ↑a) / 2)) z := by
          apply Complex.differentiable_sin.differentiableAt.comp
          fun_prop
        exact ((hΓ.mul hsin).div (by fun_prop) (hden_ne z hz1)).differentiableWithinAt
      apply DifferentiableOn.diffContOnCl
      refine hdiff.mono ?_
      have hsub : closure (Complex.re ⁻¹' (Set.Ioo (-(1/2:ℝ)) (1/2)))
          ⊆ Complex.re ⁻¹' (Set.Icc (-(1/2:ℝ)) (1/2)) :=
        closure_minimal (Set.preimage_mono Set.Ioo_subset_Icc_self)
          (isClosed_Icc.preimage Complex.continuous_re)
      refine hsub.trans ?_
      intro z hz
      have := hz.2
      show z.re < 1
      linarith
    -- growth condition
    · refine ⟨π/2, ?_, 5, ?_⟩
      · rw [show (1/2 : ℝ) - -(1/2) = 1 by norm_num, div_one]
        linarith [Real.pi_pos]
      · rw [Asymptotics.isBigO_iff]
        refine ⟨1, ?_⟩
        rw [Filter.eventually_inf_principal]
        apply Filter.Eventually.of_forall
        intro z hz
        have hz1 : -(1/2:ℝ) < z.re := hz.1
        have hz2 : z.re < 1/2 := hz.2
        have hFle : ‖F z‖ ≤ 3 * Real.exp (π/2 * |z.im|) := by
          rw [hF]
          simp only []
          rw [norm_div, norm_mul]
          have hd := hden_ge z hz2.le
          have hnum : ‖Complex.Gamma (1 - z)‖ * ‖Complex.sin (↑π * (z + ↑a) / 2)‖
              ≤ 4 * Real.exp (π/2 * |z.im|) := by
            have h1' := hΓbound z hz1.le hz2.le
            have h2' := norm_sin_pi_mul_le a z
            have h3' : Real.exp (π * |z.im| / 2) = Real.exp (π/2 * |z.im|) := by ring_nf
            rw [h3'] at h2'
            nlinarith [norm_nonneg (Complex.Gamma (1 - z)),
              norm_nonneg (Complex.sin (↑π * (z + ↑a) / 2)), Real.exp_pos (π/2 * |z.im|)]
          rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hd)]
          nlinarith [Real.exp_pos (π/2 * |z.im|)]
        have hexp : 3 * Real.exp (π/2 * |z.im|) ≤
            Real.exp (5 * Real.exp (π/2 * |z.im|)) := by
          set y := Real.exp (π/2 * |z.im|) with hy
          have hy1 : 1 ≤ y := Real.one_le_exp (by positivity)
          have h3 : (3:ℝ) ≤ Real.exp 2 := by
            have := Real.add_one_le_exp (2:ℝ)
            linarith
          calc 3 * y ≤ Real.exp 2 * y := by nlinarith
            _ = Real.exp (2 + π/2 * |z.im|) := by
                rw [Real.exp_add, hy]
            _ ≤ Real.exp (5 * y) := by
                apply Real.exp_le_exp.mpr
                have h5 := Real.add_one_le_exp (π/2 * |z.im|)
                rw [← hy] at h5
                linarith [hy1]
        rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact hFle.trans hexp
    -- boundary line Re z = −1/2
    · intro z hz
      set t := z.im with ht
      have h1z : (1 : ℂ) - z = ((1/2 : ℂ) + (-t : ℝ) * I) + 1 := by
        apply Complex.ext
        · simp [hz]; norm_num
        · simp [ht]
      have hw : ((1/2 : ℂ) + (-t : ℝ) * I).re = 1/2 := by simp
      have hwne : (1/2 : ℂ) + (-t : ℝ) * I ≠ 0 := by
        intro h
        have := congrArg Complex.re h
        rw [hw] at this
        norm_num at this
      have hΓrec : Complex.Gamma (1 - z)
          = ((1/2 : ℂ) + (-t : ℝ) * I) * Complex.Gamma ((1/2 : ℂ) + (-t : ℝ) * I) := by
        rw [h1z, Complex.Gamma_add_one _ hwne]
      have hΓsq : ‖Complex.Gamma ((1/2 : ℂ) + (-t : ℝ) * I)‖ ^ 2
          = π / Real.cosh (π * t) := by
        rw [norm_Gamma_sq_of_re_half hw]
        have him : ((1/2 : ℂ) + (-t : ℝ) * I).im = -t := by simp
        rw [him, mul_neg, Real.cosh_neg]
      have hwsq : ‖(1/2 : ℂ) + (-t : ℝ) * I‖ ^ 2 = 1/4 + t^2 := by
        rw [← Complex.normSq_eq_norm_sq]
        rw [show (1/2 : ℂ) + (-t : ℝ) * I = ((1/2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I by push_cast; rfl]
        rw [Complex.normSq_add_mul_I]
        ring
      have hdsq : ‖(2:ℂ) - z‖ ^ 2 = 25/4 + t^2 := by
        rw [← Complex.normSq_eq_norm_sq]
        have : (2:ℂ) - z = ((5/2 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by
          apply Complex.ext
          · simp [hz]; norm_num
          · simp [ht]
        rw [this, Complex.normSq_add_mul_I]
        ring
      have hsin := norm_sin_pi_mul_le a z
      have hcosh := exp_abs_le_two_mul_cosh (π * t)
      have habs : |π * t| = π * |t| := by
        rw [abs_mul, abs_of_pos Real.pi_pos]
      rw [habs] at hcosh
      have hcoshpos : 0 < Real.cosh (π * t) := Real.cosh_pos _
      have hsinexp : ‖Complex.sin (↑π * (z + ↑a) / 2)‖ ^ 2 ≤ Real.exp (π * |t|) := by
        have h := hsin
        have h2 : Real.exp (π * |t| / 2) ^ 2 = Real.exp (π * |t|) := by
          rw [sq, ← Real.exp_add]
          congr 1
          ring
        nlinarith [norm_nonneg (Complex.sin (↑π * (z + ↑a) / 2)), Real.exp_pos (π * |t| / 2)]
      -- squared bound
      rw [hF]
      simp only []
      rw [norm_div, norm_mul, hΓrec, norm_mul]
      rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) (hden_ge z (by rw [hz]; norm_num)))]
      have hsq : (‖(1/2 : ℂ) + (-t : ℝ) * I‖ * ‖Complex.Gamma ((1/2 : ℂ) + (-t : ℝ) * I)‖ *
          ‖Complex.sin (↑π * (z + ↑a) / 2)‖) ^ 2 ≤ (3 * ‖(2:ℂ) - z‖) ^ 2 := by
        have expand : (‖(1/2 : ℂ) + (-t : ℝ) * I‖ * ‖Complex.Gamma ((1/2 : ℂ) + (-t : ℝ) * I)‖ *
            ‖Complex.sin (↑π * (z + ↑a) / 2)‖) ^ 2
            = (1/4 + t^2) * (π / Real.cosh (π * t)) *
              ‖Complex.sin (↑π * (z + ↑a) / 2)‖ ^ 2 := by
          rw [mul_pow, mul_pow, hwsq, hΓsq]
        rw [expand, mul_pow, hdsq]
        have hπ4 : π ≤ 4 := Real.pi_le_four
        have hcosh' : Real.exp (π * |t|) / Real.cosh (π * t) ≤ 2 := by
          rw [div_le_iff₀ hcoshpos]; linarith
        have hkey : (π / Real.cosh (π * t)) * ‖Complex.sin (↑π * (z + ↑a) / 2)‖ ^ 2 ≤ 2 * π := by
          have h1' : (π / Real.cosh (π * t)) * ‖Complex.sin (↑π * (z + ↑a) / 2)‖ ^ 2
              ≤ (π / Real.cosh (π * t)) * Real.exp (π * |t|) := by
            apply mul_le_mul_of_nonneg_left hsinexp (by positivity)
          have h2' : (π / Real.cosh (π * t)) * Real.exp (π * |t|)
              = π * (Real.exp (π * |t|) / Real.cosh (π * t)) := by ring
          rw [h2'] at h1'
          have h3' : π * (Real.exp (π * |t|) / Real.cosh (π * t)) ≤ π * 2 :=
            mul_le_mul_of_nonneg_left hcosh' Real.pi_pos.le
          linarith
        have hsinsq : 0 ≤ ‖Complex.sin (↑π * (z + ↑a) / 2)‖ ^ 2 := sq_nonneg _
        nlinarith [Real.pi_pos, sq_nonneg t]
      have h3z : (0:ℝ) ≤ 3 * ‖(2:ℂ) - z‖ := by positivity
      nlinarith [hsq, norm_nonneg ((1/2 : ℂ) + (-t : ℝ) * I),
        norm_nonneg (Complex.Gamma ((1/2 : ℂ) + (-t : ℝ) * I)),
        norm_nonneg (Complex.sin (↑π * (z + ↑a) / 2)),
        mul_nonneg (mul_nonneg (norm_nonneg ((1/2 : ℂ) + (-t : ℝ) * I))
          (norm_nonneg (Complex.Gamma ((1/2 : ℂ) + (-t : ℝ) * I))))
          (norm_nonneg (Complex.sin (↑π * (z + ↑a) / 2)))]
    -- boundary line Re z = 1/2
    · intro z hz
      set t := z.im with ht
      have h1z : ((1 : ℂ) - z).re = 1/2 := by simp [hz]; norm_num
      have hΓsq : ‖Complex.Gamma (1 - z)‖ ^ 2 = π / Real.cosh (π * t) := by
        rw [norm_Gamma_sq_of_re_half h1z]
        have him : ((1:ℂ) - z).im = -t := by simp [ht]
        rw [him, mul_neg, Real.cosh_neg]
      have hsin := norm_sin_pi_mul_le a z
      have hcosh := exp_abs_le_two_mul_cosh (π * t)
      have habs : |π * t| = π * |t| := by rw [abs_mul, abs_of_pos Real.pi_pos]
      rw [habs] at hcosh
      have hcoshpos : 0 < Real.cosh (π * t) := Real.cosh_pos _
      have hsinexp : ‖Complex.sin (↑π * (z + ↑a) / 2)‖ ^ 2 ≤ Real.exp (π * |t|) := by
        have h2 : Real.exp (π * |t| / 2) ^ 2 = Real.exp (π * |t|) := by
          rw [sq, ← Real.exp_add]
          congr 1
          ring
        nlinarith [norm_nonneg (Complex.sin (↑π * (z + ↑a) / 2)), Real.exp_pos (π * |t| / 2)]
      rw [hF]
      simp only []
      rw [norm_div, norm_mul]
      rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) (hden_ge z (by rw [hz])))]
      have hd := hden_ge z (by rw [hz])
      have hsq : (‖Complex.Gamma (1 - z)‖ * ‖Complex.sin (↑π * (z + ↑a) / 2)‖) ^ 2
          ≤ 2 * π := by
        rw [mul_pow, hΓsq]
        have hπ4 : π ≤ 4 := Real.pi_le_four
        have h1' : (π / Real.cosh (π * t)) * ‖Complex.sin (↑π * (z + ↑a) / 2)‖ ^ 2
            ≤ (π / Real.cosh (π * t)) * Real.exp (π * |t|) :=
          mul_le_mul_of_nonneg_left hsinexp (by positivity)
        have hcosh' : Real.exp (π * |t|) / Real.cosh (π * t) ≤ 2 := by
          rw [div_le_iff₀ hcoshpos]; linarith
        have h2' : (π / Real.cosh (π * t)) * Real.exp (π * |t|)
            = π * (Real.exp (π * |t|) / Real.cosh (π * t)) := by ring
        rw [h2'] at h1'
        have h3' : π * (Real.exp (π * |t|) / Real.cosh (π * t)) ≤ π * 2 :=
          mul_le_mul_of_nonneg_left hcosh' Real.pi_pos.le
        linarith
      have hπ4 : π ≤ 4 := Real.pi_le_four
      nlinarith [norm_nonneg (Complex.Gamma (1 - z)),
        norm_nonneg (Complex.sin (↑π * (z + ↑a) / 2)),
        mul_nonneg (norm_nonneg (Complex.Gamma (1 - z)))
          (norm_nonneg (Complex.sin (↑π * (z + ↑a) / 2))), Real.pi_pos]
    · exact h1
    · exact h2
  -- unfold F
  have hne : (2:ℂ) - s ≠ 0 := hden_ne s (by linarith)
  have hFs : ‖Complex.Gamma (1 - s) * Complex.sin (↑π * (s + ↑a) / 2)‖
      = ‖F s‖ * ‖(2:ℂ) - s‖ := by
    rw [hF]
    simp only []
    rw [norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hne)]
  rw [hFs]
  have hle : ‖(2:ℂ) - s‖ ≤ 2 + ‖s‖ := by
    calc ‖(2:ℂ) - s‖ ≤ ‖(2:ℂ)‖ + ‖s‖ := norm_sub_le _ _
      _ = 2 + ‖s‖ := by norm_num
  calc ‖F s‖ * ‖(2:ℂ) - s‖ ≤ 3 * ‖(2:ℂ) - s‖ :=
        mul_le_mul_of_nonneg_right main (norm_nonneg _)
    _ ≤ 3 * (2 + ‖s‖) := by linarith

end PLStrip

/-! ### The left strip via the functional equation -/

section LeftStrip

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
private lemma inv_mul_neg_one (χ : DirichletCharacter ℂ N) :
    χ (-1) * χ⁻¹ (-1) = 1 := by
  have h : (χ * χ⁻¹) (-1) = 1 := by
    rw [mul_inv_cancel]
    exact MulChar.one_apply isUnit_one.neg
  rwa [MulChar.mul_apply] at h

omit [NeZero N] in
private lemma even_inv {χ : DirichletCharacter ℂ N} (h : χ.Even) : (χ⁻¹).Even := by
  have := inv_mul_neg_one χ
  rw [h] at this
  rwa [one_mul] at this

omit [NeZero N] in
private lemma odd_inv {χ : DirichletCharacter ℂ N} (h : χ.Odd) : (χ⁻¹).Odd := by
  have hmul := inv_mul_neg_one χ
  rw [h] at hmul
  show χ⁻¹ (-1) = -1
  linear_combination -hmul

private lemma norm_gaussSum_le (χ : DirichletCharacter ℂ N) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ N := by
  rw [gaussSum]
  calc ‖∑ a : ZMod N, χ a * ZMod.stdAddChar a‖
      ≤ ∑ a : ZMod N, ‖χ a * ZMod.stdAddChar a‖ := norm_sum_le _ _
    _ ≤ ∑ _a : ZMod N, (1:ℝ) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rw [norm_mul]
        have h1 := χ.norm_le_one x
        have h2 : ‖ZMod.stdAddChar (N := N) x‖ = 1 := by
          rw [ZMod.stdAddChar_apply]
          exact Circle.norm_coe _
        rw [h2, mul_one]
        exact h1
    _ = N := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card]
        simp

private lemma norm_rootNumber_le (χ : DirichletCharacter ℂ N) :
    ‖DirichletCharacter.rootNumber χ‖ ≤ N := by
  classical
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  rw [DirichletCharacter.rootNumber]
  rw [norm_div, norm_div]
  have hI : ‖(I : ℂ) ^ (if χ.Even then 0 else 1)‖ = 1 := by
    rw [norm_pow, Complex.norm_I, one_pow]
  have hNhalf : ‖((N : ℂ)) ^ ((1:ℂ)/2)‖ = (N:ℝ) ^ ((1:ℝ)/2) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    norm_num
  have h1 : (1:ℝ) ≤ (N:ℝ) ^ ((1:ℝ)/2) := Real.one_le_rpow hN1 (by norm_num)
  rw [hI, div_one, hNhalf]
  calc ‖gaussSum χ ZMod.stdAddChar‖ / (N:ℝ) ^ ((1:ℝ)/2)
      ≤ ‖gaussSum χ ZMod.stdAddChar‖ / 1 := by
        apply div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) h1
    _ = ‖gaussSum χ ZMod.stdAddChar‖ := div_one _
    _ ≤ N := norm_gaussSum_le χ

private lemma one_sub_ne_neg_nat {s : ℂ} (hs : s.re ≤ 1/2) :
    ∀ n : ℕ, (1:ℂ) - s ≠ -n := by
  intro n h
  have := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at this
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  linarith

/-- Functional-equation identity for even primitive nontrivial characters, valid on
`Re s ≤ 1/2` (both sides vanish at the trivial zero `s = 0`). -/
private lemma LFunction_left_even {χ : DirichletCharacter ℂ N} (hχp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (hE : χ.Even) {s : ℂ} (hs : s.re ≤ 1/2) :
    DirichletCharacter.LFunction χ s
      = (N:ℂ) ^ ((1:ℂ)/2 - s) * DirichletCharacter.rootNumber χ *
        (Complex.Gammaℂ (1 - s) * Complex.sin (↑π * s / 2)) *
        DirichletCharacter.LFunction χ⁻¹ (1 - s) := by
  have hN : N ≠ 1 := fun h => hχ (χ.level_one' h)
  have hre1s : 0 < (1 - s : ℂ).re := by
    rw [Complex.sub_re, Complex.one_re]; linarith
  have hEinv : (χ⁻¹).Even := even_inv hE
  have hΓne : Complex.Gammaℝ (1 - s) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre1s
  -- Λ(χ⁻¹, 1−s) = L(χ⁻¹, 1−s) · Γℝ(1−s)
  have hΛinv : DirichletCharacter.completedLFunction χ⁻¹ (1 - s)
      = DirichletCharacter.LFunction χ⁻¹ (1 - s) * Complex.Gammaℝ (1 - s) := by
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inr hN)
    rw [hEinv.gammaFactor_def] at h
    rw [h, div_mul_cancel₀ _ hΓne]
  -- Functional equation
  have hFE : DirichletCharacter.completedLFunction χ s
      = (N:ℂ) ^ ((1:ℂ)/2 - s) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ (1 - s) := by
    have h := hχp.completedLFunction_one_sub (1 - s)
    rw [sub_sub_cancel] at h
    rw [show ((1:ℂ) - s - 1/2) = (1:ℂ)/2 - s from by ring] at h
    exact h
  -- Reflection formula for the Deligne factor
  have hrefl : (Complex.Gammaℝ s)⁻¹
      = Complex.Gammaℂ (1 - s) * Complex.sin (↑π * s / 2) * (Complex.Gammaℝ (1 - s))⁻¹ := by
    have h := Complex.inv_Gammaℝ_one_sub (s := 1 - s) (one_sub_ne_neg_nat hs)
    rw [sub_sub_cancel] at h
    rw [h]
    congr 2
    rw [show ↑π * (1 - s) / 2 = ↑π/2 - ↑π * s / 2 from by ring, Complex.cos_pi_div_two_sub]
  -- assemble
  have hL : DirichletCharacter.LFunction χ s
      = DirichletCharacter.completedLFunction χ s * (Complex.Gammaℝ s)⁻¹ := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN),
      hE.gammaFactor_def, div_eq_mul_inv]
  rw [hL, hFE, hΛinv, hrefl]
  field_simp

/-- Functional-equation identity for odd primitive characters, valid on `Re s ≤ 1/2`. -/
private lemma LFunction_left_odd {χ : DirichletCharacter ℂ N} (hχp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (hO : χ.Odd) {s : ℂ} (hs : s.re ≤ 1/2) :
    DirichletCharacter.LFunction χ s
      = (N:ℂ) ^ ((1:ℂ)/2 - s) * DirichletCharacter.rootNumber χ *
        (Complex.Gammaℂ (1 - s) * Complex.cos (↑π * s / 2)) *
        DirichletCharacter.LFunction χ⁻¹ (1 - s) := by
  have hN : N ≠ 1 := fun h => hχ (χ.level_one' h)
  have hre2s : 0 < ((1 - s : ℂ) + 1).re := by
    rw [Complex.add_re, Complex.sub_re, Complex.one_re]; linarith
  have hOinv : (χ⁻¹).Odd := odd_inv hO
  have hΓne : Complex.Gammaℝ ((1 - s) + 1) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre2s
  have hΛinv : DirichletCharacter.completedLFunction χ⁻¹ (1 - s)
      = DirichletCharacter.LFunction χ⁻¹ (1 - s) * Complex.Gammaℝ ((1 - s) + 1) := by
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inr hN)
    rw [hOinv.gammaFactor_def] at h
    rw [h, div_mul_cancel₀ _ hΓne]
  have hFE : DirichletCharacter.completedLFunction χ s
      = (N:ℂ) ^ ((1:ℂ)/2 - s) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ (1 - s) := by
    have h := hχp.completedLFunction_one_sub (1 - s)
    rw [sub_sub_cancel] at h
    rw [show ((1:ℂ) - s - 1/2) = (1:ℂ)/2 - s from by ring] at h
    exact h
  have hrefl : (Complex.Gammaℝ (s + 1))⁻¹
      = Complex.Gammaℂ (1 - s) * Complex.cos (↑π * s / 2) * (Complex.Gammaℝ ((1 - s) + 1))⁻¹ := by
    have h := Complex.inv_Gammaℝ_two_sub (s := 1 - s) (one_sub_ne_neg_nat hs)
    rw [show (2:ℂ) - (1 - s) = s + 1 from by ring] at h
    rw [h]
    congr 2
    rw [show ↑π * (1 - s) / 2 = ↑π/2 - ↑π * s / 2 from by ring, Complex.sin_pi_div_two_sub]
  have hL : DirichletCharacter.LFunction χ s
      = DirichletCharacter.completedLFunction χ s * (Complex.Gammaℝ (s + 1))⁻¹ := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN),
      hO.gammaFactor_def, div_eq_mul_inv]
  rw [hL, hFE, hΛinv, hrefl]
  field_simp

private lemma norm_GammaC_mul_trig_le {s : ℂ} (h1 : -(1/2 : ℝ) ≤ s.re) (h2 : s.re ≤ 1/2)
    {T : ℂ} (hT : T = Complex.sin (↑π * s / 2) ∨ T = Complex.cos (↑π * s / 2)) :
    ‖Complex.Gammaℂ (1 - s) * T‖ ≤ 6 * (2 + ‖s‖) := by
  have hstrip : ‖Complex.Gamma (1 - s) * T‖ ≤ 3 * (2 + ‖s‖) := by
    rcases hT with rfl | rfl
    · have := norm_Gamma_one_sub_mul_sin_le 0 h1 h2
      rw [show ((0:ℝ):ℂ) = 0 from by norm_num, add_zero] at this
      exact this
    · have := norm_Gamma_one_sub_mul_sin_le 1 h1 h2
      rw [show ↑π * (s + ((1:ℝ):ℂ)) / 2 = ↑π/2 - -(↑π * s / 2) from by push_cast; ring,
        Complex.sin_pi_div_two_sub, Complex.cos_neg] at this
      exact this
  have hpow : ‖((2:ℂ) * ↑π) ^ (-(1 - s))‖ ≤ 1 := by
    rw [show ((2:ℂ) * ↑π) = (((2 * π : ℝ)):ℂ) from by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    apply Real.rpow_le_one_of_one_le_of_nonpos
    · nlinarith [Real.two_le_pi]
    · rw [Complex.neg_re, Complex.sub_re, Complex.one_re]
      linarith
  have hexpand : Complex.Gammaℂ (1 - s) * T
      = 2 * (((2:ℂ) * ↑π) ^ (-(1 - s))) * (Complex.Gamma (1 - s) * T) := by
    rw [Complex.Gammaℂ_def]
    ring
  rw [hexpand, norm_mul, norm_mul]
  have h2' : ‖(2:ℂ)‖ = 2 := by norm_num
  rw [h2']
  calc 2 * ‖((2:ℂ) * ↑π) ^ (-(1 - s))‖ * ‖Complex.Gamma (1 - s) * T‖
      ≤ 2 * 1 * (3 * (2 + ‖s‖)) := by
        apply mul_le_mul
        · apply mul_le_mul_of_nonneg_left hpow (by norm_num)
        · exact hstrip
        · exact norm_nonneg _
        · norm_num
    _ = 6 * (2 + ‖s‖) := by ring

/-- **Z4a left-strip bound.** For primitive nontrivial `χ mod N` and
`−1/2 ≤ Re s ≤ 1/2`, `‖L(s,χ)‖ ≤ 18·N³·(2+‖s‖)²`. -/
theorem norm_LFunction_le_left_strip {χ : DirichletCharacter ℂ N} (hχp : χ.IsPrimitive)
    (hχ : χ ≠ 1) {s : ℂ} (h1 : -(1/2 : ℝ) ≤ s.re) (h2 : s.re ≤ 1/2) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 18 * (N:ℝ)^3 * (2 + ‖s‖)^2 := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  -- bound on N^(1/2 − s)
  have hb1 : ‖(N:ℂ) ^ ((1:ℂ)/2 - s)‖ ≤ (N:ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    calc (N:ℝ) ^ ((1:ℂ)/2 - s).re ≤ (N:ℝ) ^ (1:ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hN1
          rw [Complex.sub_re]
          norm_num
          linarith
      _ = (N:ℝ) := Real.rpow_one _
  have hb2 := norm_rootNumber_le χ
  -- bound on L(χ⁻¹, 1−s)
  have hb4 : ‖DirichletCharacter.LFunction χ⁻¹ (1 - s)‖ ≤ 3 * (N:ℝ) * (2 + ‖s‖) := by
    have hinv1 : χ⁻¹ ≠ 1 := fun h => hχ (inv_eq_one.mp h)
    have hre : 0 < (1 - s : ℂ).re := by
      rw [Complex.sub_re, Complex.one_re]; linarith
    have hre' : (1 - s : ℂ).re = 1 - s.re := by
      rw [Complex.sub_re, Complex.one_re]
    have h := norm_LFunction_le_of_re_pos χ⁻¹ hinv1 hre
    have hfrac : 1 + 1 / (1 - s : ℂ).re ≤ 3 := by
      rw [hre']
      have hpos : (0:ℝ) < 1 - s.re := by linarith
      have : 1 / (1 - s.re) ≤ 2 := by
        rw [div_le_iff₀ hpos]; linarith
      linarith
    have hnorm1s : ‖(1 - s : ℂ)‖ ≤ 2 + ‖s‖ := by
      calc ‖(1 - s : ℂ)‖ ≤ ‖(1:ℂ)‖ + ‖s‖ := norm_sub_le _ _
        _ = 1 + ‖s‖ := by rw [norm_one]
        _ ≤ 2 + ‖s‖ := by linarith
    calc ‖DirichletCharacter.LFunction χ⁻¹ (1 - s)‖
        ≤ (N:ℝ) * ‖(1 - s : ℂ)‖ * (1 + 1 / (1 - s : ℂ).re) := h
      _ ≤ (N:ℝ) * (2 + ‖s‖) * 3 := by
          have hfr0 : (0:ℝ) ≤ 1 + 1 / (1 - s : ℂ).re := by
            rw [hre']
            have : (0:ℝ) < 1 - s.re := by linarith
            positivity
          have := mul_le_mul (mul_le_mul_of_nonneg_left hnorm1s hNpos.le) hfrac hfr0
            (by positivity : (0:ℝ) ≤ (N:ℝ) * (2 + ‖s‖))
          linarith [this]
      _ = 3 * (N:ℝ) * (2 + ‖s‖) := by ring
  have hfinal : ∀ T : ℂ, (T = Complex.sin (↑π * s / 2) ∨ T = Complex.cos (↑π * s / 2)) →
      ‖(N:ℂ) ^ ((1:ℂ)/2 - s) * DirichletCharacter.rootNumber χ *
        (Complex.Gammaℂ (1 - s) * T) * DirichletCharacter.LFunction χ⁻¹ (1 - s)‖
      ≤ 18 * (N:ℝ)^3 * (2 + ‖s‖)^2 := by
    intro T hT
    have hb3 := norm_GammaC_mul_trig_le h1 h2 hT
    rw [norm_mul, norm_mul, norm_mul]
    have hnn : (0:ℝ) ≤ 2 + ‖s‖ := by positivity
    calc ‖(N:ℂ) ^ ((1:ℂ)/2 - s)‖ * ‖DirichletCharacter.rootNumber χ‖ *
        ‖Complex.Gammaℂ (1 - s) * T‖ * ‖DirichletCharacter.LFunction χ⁻¹ (1 - s)‖
        ≤ (N:ℝ) * (N:ℝ) * (6 * (2 + ‖s‖)) * (3 * (N:ℝ) * (2 + ‖s‖)) := by
          gcongr
      _ = 18 * (N:ℝ)^3 * (2 + ‖s‖)^2 := by ring
  rcases χ.even_or_odd with hE | hO
  · rw [LFunction_left_even hχp hχ hE h2]
    exact hfinal _ (Or.inl rfl)
  · rw [LFunction_left_odd hχp hχ hO h2]
    exact hfinal _ (Or.inr rfl)

/-- **Z4a combined polynomial growth bound.** For primitive nontrivial `χ mod N` and
`Re s ≥ −1/2`, `‖L(s,χ)‖ ≤ 18·(N·(2+‖s‖))³`. -/
theorem norm_LFunction_le_of_neg_half_le_re {χ : DirichletCharacter ℂ N}
    (hχp : χ.IsPrimitive) (hχ : χ ≠ 1) {s : ℂ} (hs : -(1/2 : ℝ) ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ ≤ 18 * ((N:ℝ) * (2 + ‖s‖))^3 := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  have hb : (1:ℝ) ≤ 2 + ‖s‖ := by linarith [norm_nonneg s]
  have hbN : (1:ℝ) ≤ (N:ℝ) * (2 + ‖s‖) := by nlinarith
  have hN0 : (0:ℝ) ≤ (N:ℝ) := by linarith
  have hb0 : (0:ℝ) ≤ 2 + ‖s‖ := by linarith
  rcases le_or_gt s.re (1/2) with h | h
  · have hstrip := norm_LFunction_le_left_strip hχp hχ hs h
    calc ‖DirichletCharacter.LFunction χ s‖ ≤ 18 * (N:ℝ)^3 * (2 + ‖s‖)^2 := hstrip
      _ ≤ 18 * (N:ℝ)^3 * (2 + ‖s‖)^3 := by
          have hle : (2 + ‖s‖)^2 ≤ (2 + ‖s‖)^3 := pow_le_pow_right₀ hb (by norm_num)
          have hN3 : (0:ℝ) ≤ (N:ℝ)^3 := by positivity
          nlinarith
      _ = 18 * ((N:ℝ) * (2 + ‖s‖))^3 := by rw [mul_pow]; ring
  · have h4 : (1/4 : ℝ) ≤ s.re := by linarith
    have hq := norm_LFunction_le_of_one_quarter_le_re χ hχ h4
    have hx1 : (1:ℝ) ≤ ((N:ℝ) * (2 + ‖s‖))^2 := one_le_pow₀ hbN
    have hx0 : (0:ℝ) ≤ (N:ℝ) * (2 + ‖s‖) := by linarith
    calc ‖DirichletCharacter.LFunction χ s‖ ≤ 5 * (N:ℝ) * (2 + ‖s‖) := hq
      _ = 5 * ((N:ℝ) * (2 + ‖s‖)) := by ring
      _ ≤ 18 * (((N:ℝ) * (2 + ‖s‖)) * ((N:ℝ) * (2 + ‖s‖))^2) := by nlinarith
      _ = 18 * ((N:ℝ) * (2 + ‖s‖))^3 := by ring

end LeftStrip

end Carmichael
