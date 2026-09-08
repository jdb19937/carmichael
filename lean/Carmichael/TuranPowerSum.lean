/-
Route Z, TZ-LITE File 1: Turán power-sum lower bounds.

DELIVERED (Part 1, first main theorem):

* `turan_power_sum_lb` — for `z : Fin N → ℂ` with `t ≤ ‖z j‖` for every `j`
  (`0 ≤ t`), some exponent `k ∈ [M+1, M+N]` satisfies
    `(N / (8·e·(M+N)))^N · t^k ≤ ‖∑ j, z j ^ k‖`.
* `turan_power_sum_min` — the same with `t := ‖z ⟨0, hN⟩‖` and the
  min-normalised hypothesis `hmin`.

DELIVERED (Part 2, second main theorem — the frozen Z7-tzlite §1.1
interface, byte-identical statements):

* `turan_power_sum_max` — under `hmax : ∀ j, ‖z j‖ ≤ ‖z ⟨0, hN⟩‖`, some
  exponent `k ∈ [M+1, M+N]` satisfies
    `(N / (8·e·(M+N)))^N · ‖z ⟨0, hN⟩‖^k ≤ ‖∑ j, z j ^ k‖`.
* `turan_power_sum_max_lb` — the same against any lower bound `t` on the
  largest modulus (`0 ≤ t ≤ ‖z ⟨0, hN⟩‖`), with `t^k` on the left.

The literal `z 0` of §1.1 does not elaborate for a variable `N` (no
`NeZero N` instance); §1.4 pre-authorises the `⟨0, hN⟩` spelling.

PROOF (Part 1: classical generating-function/Bézout proof of the first main
theorem).  Normalise `θ := ‖z ⟨0,hN⟩‖ > 0` and put `y j := θ / z j`, so
`‖y j‖ ≤ 1`.  With `ω := ∏ j (1 - y j X)` and `v := ∏ j ∑_{r≤M} (y j X)^r`
one has `ω · v = ∏ j (1 - (y j X)^{M+1}) ≡ 1 (mod X^{M+1})`.  Truncating
`v` to degree `M` gives `u` with `ω·u ≡ 1 (mod X^{M+1})` and
`deg (ω·u) ≤ M+N`, so `R := 1 - ω·u` is supported on `[M+1, M+N]` and
`R (z j / θ) = 1` for every `j` (as `ω` kills `1 / y j`).  Summing over `j`
turns `N` into a linear combination of the window power sums with total
coefficient mass `‖ω‖₁‖u‖₁ ≤ C(2N,N)·C(M+N,N) ≤ (8e(M+N)/N)^N`.

The proof of Part 2 (van der Poorten's interpolation argument over a
Chebyshev-selected circle) is described in the Part 2 section header below.
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Topology.Algebra.Polynomial

set_option autoImplicit false

open Finset Polynomial

namespace Carmichael

namespace Turan

noncomputable section

/-! ### The multiset-coefficient counting function -/

/-- `mch n k` is the number of ways of writing `k` as an ordered sum of `n`
non-negative integers, i.e. `Nat.choose (k + n - 1) k`, spelled so as to
avoid truncated subtraction. -/
def mch : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | (n + 1), k => (k + n).choose k

@[simp] lemma mch_zero (k : ℕ) : mch 0 k = if k = 0 then 1 else 0 := rfl

@[simp] lemma mch_succ (n k : ℕ) : mch (n + 1) k = (k + n).choose k := rfl

/-- Hockey-stick: partial sums of `mch n ·` are `mch (n+1) ·`. -/
lemma sum_range_mch (n k : ℕ) :
    ∑ i ∈ Finset.range (k + 1), mch n i = mch (n + 1) k := by
  cases n with
  | zero =>
      have hz : ∀ i : ℕ, mch 0 i = if i = 0 then 1 else 0 := fun _ => rfl
      simp only [hz, mch_succ, Nat.add_zero, Nat.choose_self]
      rw [Finset.sum_ite_eq' (Finset.range (k + 1)) 0 (fun _ => 1)]
      simp
  | succ n =>
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          simp only [mch_succ]
          have h := Nat.choose_succ_succ' (k + n + 1) k
          have e1 : k + (n + 1) = k + n + 1 := by ring
          have e2 : k + 1 + n = k + n + 1 := by ring
          have e3 : k + 1 + (n + 1) = k + n + 1 + 1 := by ring
          rw [e1, e2, e3, h]

/-! ### The `ℓ¹` coefficient norm on `ℂ[X]` -/

/-- Coefficientwise absolute value of a complex polynomial. -/
def absP (p : ℂ[X]) : ℝ[X] :=
  ∑ i ∈ p.support, Polynomial.C ‖p.coeff i‖ * Polynomial.X ^ i

lemma absP_coeff (p : ℂ[X]) (k : ℕ) : (absP p).coeff k = ‖p.coeff k‖ := by
  classical
  simp only [absP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (p.support) k (fun i => ‖p.coeff i‖)]
  by_cases hk : k ∈ p.support
  · simp [hk]
  · simp [hk, Polynomial.notMem_support_iff.mp hk]

lemma absP_natDegree_le (p : ℂ[X]) : (absP p).natDegree ≤ p.natDegree := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  rw [absP_coeff]
  simp [Polynomial.coeff_eq_zero_of_natDegree_lt hn]

/-- `ℓ¹` norm of the coefficient sequence. -/
def l1 (p : ℂ[X]) : ℝ := (absP p).eval 1

lemma l1_eq_sum_range {p : ℂ[X]} {n : ℕ} (hn : p.natDegree < n) :
    l1 p = ∑ i ∈ Finset.range n, ‖p.coeff i‖ := by
  have hd : (absP p).natDegree < n := lt_of_le_of_lt (absP_natDegree_le p) hn
  rw [l1, Polynomial.eval_eq_sum_range' hd]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [absP_coeff, one_pow, mul_one]

lemma l1_nonneg (p : ℂ[X]) : 0 ≤ l1 p := by
  rw [l1_eq_sum_range (Nat.lt_succ_self p.natDegree)]
  exact Finset.sum_nonneg fun i _ => norm_nonneg _

lemma l1_mul_le (p q : ℂ[X]) : l1 (p * q) ≤ l1 p * l1 q := by
  set n := p.natDegree + q.natDegree + 1 with hn
  have hpq : (p * q).natDegree < n := by
    have := Polynomial.natDegree_mul_le (p := p) (q := q)
    omega
  have hp : p.natDegree < n := by omega
  have hq : q.natDegree < n := by omega
  rw [l1_eq_sum_range hpq, l1_eq_sum_range hp, l1_eq_sum_range hq]
  set f : ℕ → ℝ := fun i => ‖p.coeff i‖ with hf
  set g : ℕ → ℝ := fun i => ‖q.coeff i‖ with hg
  have hf0 : ∀ i, 0 ≤ f i := fun i => norm_nonneg _
  have hg0 : ∀ i, 0 ≤ g i := fun i => norm_nonneg _
  -- coefficientwise domination by the nonnegative convolution
  have key : ∀ k, ‖(p * q).coeff k‖
      ≤ ∑ i ∈ Finset.range (k + 1), f i * g (k - i) := by
    intro k
    rw [Polynomial.coeff_mul]
    refine le_trans (norm_sum_le _ _) ?_
    refine le_of_eq ?_
    rw [← Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
      (fun x : ℕ × ℕ => f x.1 * g x.2) k]
    exact Finset.sum_congr rfl fun x _ => norm_mul _ _
  refine le_trans (Finset.sum_le_sum fun k _ => key k) ?_
  -- swap the order of summation
  have hswap : ∑ k ∈ Finset.range n, ∑ i ∈ Finset.range (k + 1), f i * g (k - i)
      = ∑ i ∈ Finset.range n, ∑ k ∈ Finset.Ico i n, f i * g (k - i) := by
    refine Finset.sum_comm' ?_
    intro k i
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hswap, Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro i _
  have hreindex : ∑ k ∈ Finset.Ico i n, f i * g (k - i)
      = ∑ j ∈ Finset.range (n - i), f i * g j := by
    rw [Finset.sum_Ico_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => by simp
  rw [hreindex, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (hf0 i)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => hg0 j)
  intro x hx
  simp only [Finset.mem_range] at hx ⊢
  omega

/-! ### Coefficient bound for products of unit-coefficient polynomials -/

/-- If every factor has all coefficients of norm at most `1`, the `k`-th
coefficient of a product of `n` factors is at most `mch n k` in norm. -/
lemma coeff_prod_le {ι : Type*} (p : ι → ℂ[X])
    (hp : ∀ i : ι, ∀ r : ℕ, ‖(p i).coeff r‖ ≤ 1) (s : Finset ι) (k : ℕ) :
    ‖(∏ i ∈ s, p i).coeff k‖ ≤ (mch s.card k : ℝ) := by
  classical
  induction s using Finset.cons_induction generalizing k with
  | empty =>
      simp only [Finset.prod_empty, Finset.card_empty, mch_zero]
      rcases eq_or_ne k 0 with rfl | hk
      · simp
      · simp [Polynomial.coeff_one, hk]
  | cons a t ha ih =>
      rw [Finset.prod_cons, Polynomial.coeff_mul, Finset.card_cons]
      refine le_trans (norm_sum_le _ _) ?_
      have hterm : ∀ x ∈ Finset.antidiagonal k,
          ‖(p a).coeff x.1 * (∏ i ∈ t, p i).coeff x.2‖ ≤ (mch t.card x.2 : ℝ) := by
        intro x _
        rw [norm_mul]
        have h1 := hp a x.1
        have h2 := ih (k := x.2)
        nlinarith [norm_nonneg ((p a).coeff x.1),
          norm_nonneg ((∏ i ∈ t, p i).coeff x.2),
          Nat.cast_nonneg (α := ℝ) (mch t.card x.2)]
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk
        (fun x : ℕ × ℕ => (mch t.card x.2 : ℝ)) k]
      have hrefl := Finset.sum_range_reflect (fun j => (mch t.card j : ℝ)) (k + 1)
      simp only [Nat.add_sub_cancel] at hrefl
      rw [hrefl, ← Nat.cast_sum, sum_range_mch]

/-! ### The window polynomial -/

section Construction

variable {N : ℕ}

/-- One linear factor `1 - c·X`. -/
def linF (c : ℂ) : ℂ[X] := 1 - Polynomial.C c * Polynomial.X

/-- One truncated geometric factor `∑_{r ≤ M} (c·X)^r`. -/
def geoF (c : ℂ) (M : ℕ) : ℂ[X] :=
  ∑ r ∈ Finset.range (M + 1), (Polynomial.C c * Polynomial.X) ^ r

lemma coeff_linF (c : ℂ) (r : ℕ) :
    (linF c).coeff r = (if r = 0 then (1 : ℂ) else 0) - c * (if r = 1 then 1 else 0) := by
  simp only [linF, Polynomial.coeff_sub, Polynomial.coeff_one,
    Polynomial.coeff_C_mul, Polynomial.coeff_X]
  rcases eq_or_ne r 1 with rfl | h
  · simp
  · simp [h, Ne.symm h]

lemma norm_coeff_linF_le {c : ℂ} (hc : ‖c‖ ≤ 1) (r : ℕ) : ‖(linF c).coeff r‖ ≤ 1 := by
  rw [coeff_linF]
  rcases eq_or_ne r 0 with rfl | h0
  · norm_num
  · rcases eq_or_ne r 1 with rfl | h1
    · simpa using hc
    · simp [h0, h1]

lemma coeff_geoF (c : ℂ) (M r : ℕ) :
    (geoF c M).coeff r = if r ≤ M then c ^ r else 0 := by
  have hpow : ∀ i : ℕ, (Polynomial.C c * Polynomial.X) ^ i
      = Polynomial.C (c ^ i) * Polynomial.X ^ i := by
    intro i; rw [mul_pow, Polynomial.C_pow]
  simp only [geoF, hpow, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (M + 1)) r (fun i => c ^ i)]
  simp [Finset.mem_range]

lemma norm_coeff_geoF_le {c : ℂ} (hc : ‖c‖ ≤ 1) (M r : ℕ) :
    ‖(geoF c M).coeff r‖ ≤ 1 := by
  rw [coeff_geoF]
  by_cases h : r ≤ M
  · simp only [h, if_true, norm_pow]
    exact pow_le_one₀ (norm_nonneg c) hc
  · simp [h]

/-- `ω = ∏ⱼ (1 - yⱼ X)`. -/
def om (y : Fin N → ℂ) : ℂ[X] := ∏ j, linF (y j)

/-- `v = ∏ⱼ ∑_{r ≤ M} (yⱼ X)^r`, the truncated inverse before truncation. -/
def gv (y : Fin N → ℂ) (M : ℕ) : ℂ[X] := ∏ j, geoF (y j) M

/-- `u`, the degree-`≤ M` truncation of `gv`. -/
def uu (y : Fin N → ℂ) (M : ℕ) : ℂ[X] :=
  ∑ r ∈ Finset.range (M + 1), Polynomial.C ((gv y M).coeff r) * Polynomial.X ^ r

lemma coeff_uu (y : Fin N → ℂ) (M r : ℕ) :
    (uu y M).coeff r = if r ≤ M then (gv y M).coeff r else 0 := by
  simp only [uu, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (M + 1)) r (fun i => (gv y M).coeff i)]
  simp [Finset.mem_range]

lemma natDegree_om_le (y : Fin N → ℂ) : (om y).natDegree ≤ N := by
  refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
  calc ∑ j : Fin N, (linF (y j)).natDegree ≤ ∑ _j : Fin N, 1 := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
        intro n hn
        rw [coeff_linF]
        have h0 : n ≠ 0 := by omega
        have h1 : n ≠ 1 := by omega
        simp [h0, h1]
    _ = N := by simp

lemma natDegree_uu_le (y : Fin N → ℂ) (M : ℕ) : (uu y M).natDegree ≤ M := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr ?_
  intro n hn
  rw [coeff_uu]
  simp [Nat.not_le.mpr hn]

/-! #### The Bézout identity `ω·u ≡ 1 (mod X^{M+1})` -/

lemma om_mul_gv (y : Fin N → ℂ) (M : ℕ) :
    om y * gv y M = ∏ j, (1 - (Polynomial.C (y j) * Polynomial.X) ^ (M + 1)) := by
  rw [om, gv, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro j _
  set x := Polynomial.C (y j) * Polynomial.X with hx
  have h := geom_sum_mul x (M + 1)
  have hrw : linF (y j) * geoF (y j) M
      = -((∑ i ∈ Finset.range (M + 1), x ^ i) * (x - 1)) := by
    rw [linF, geoF, ← hx]; ring
  rw [hrw, h]; ring

lemma coeff_prod_shift (y : Fin N → ℂ) (M : ℕ) (s : Finset (Fin N)) (k : ℕ)
    (hk : k ≤ M) :
    (∏ j ∈ s, (1 - (Polynomial.C (y j) * Polynomial.X) ^ (M + 1))).coeff k
      = if k = 0 then 1 else 0 := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      rcases eq_or_ne k 0 with rfl | h
      · simp
      · simp [Polynomial.coeff_one, h]
  | cons a t ha ih =>
      rw [Finset.prod_cons]
      set P := ∏ j ∈ t, (1 - (Polynomial.C (y j) * Polynomial.X) ^ (M + 1)) with hP
      have hQ : (Polynomial.C (y a) * Polynomial.X) ^ (M + 1)
          = Polynomial.C (y a ^ (M + 1)) * Polynomial.X ^ (M + 1) := by
        rw [mul_pow, Polynomial.C_pow]
      have hsplit : (1 - (Polynomial.C (y a) * Polynomial.X) ^ (M + 1)) * P
          = P - Polynomial.C (y a ^ (M + 1)) * (P * Polynomial.X ^ (M + 1)) := by
        rw [hQ]; ring
      rw [hsplit, Polynomial.coeff_sub, Polynomial.coeff_C_mul,
        Polynomial.coeff_mul_X_pow']
      rw [if_neg (by omega : ¬ (M + 1 ≤ k))]
      simpa using ih

lemma coeff_om_mul_uu_low (y : Fin N → ℂ) (M k : ℕ) (hk : k ≤ M) :
    (om y * uu y M).coeff k = if k = 0 then 1 else 0 := by
  have hswap : (om y * uu y M).coeff k = (om y * gv y M).coeff k := by
    rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
    refine Finset.sum_congr rfl ?_
    intro x hx
    rw [Finset.mem_antidiagonal] at hx
    rw [coeff_uu, if_pos (by omega : x.2 ≤ M)]
  rw [hswap, om_mul_gv, coeff_prod_shift y M Finset.univ k hk]

/-! #### Evaluation and `ℓ¹` bounds -/

lemma eval_om_eq_zero (y : Fin N → ℂ) (j : Fin N) (hj : y j ≠ 0) :
    (om y).eval (1 / y j) = 0 := by
  rw [om, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
  simp only [linF, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  rw [mul_one_div, div_self hj, sub_self]



lemma l1_om_le (y : Fin N → ℂ) (hy : ∀ j, ‖y j‖ ≤ 1) :
    l1 (om y) ≤ (mch (N + 1) N : ℝ) := by
  rw [l1_eq_sum_range (Nat.lt_succ_of_le (natDegree_om_le y))]
  have hb : ∀ i ∈ Finset.range (N + 1), ‖(om y).coeff i‖ ≤ (mch N i : ℝ) := by
    intro i _
    have := coeff_prod_le (fun j : Fin N => linF (y j))
      (fun j r => norm_coeff_linF_le (hy j) r) Finset.univ i
    simpa [om] using this
  refine le_trans (Finset.sum_le_sum hb) ?_
  rw [← Nat.cast_sum, sum_range_mch]

lemma l1_uu_le (y : Fin N → ℂ) (M : ℕ) (hy : ∀ j, ‖y j‖ ≤ 1) :
    l1 (uu y M) ≤ (mch (N + 1) M : ℝ) := by
  rw [l1_eq_sum_range (Nat.lt_succ_of_le (natDegree_uu_le y M))]
  have hb : ∀ i ∈ Finset.range (M + 1), ‖(uu y M).coeff i‖ ≤ (mch N i : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [coeff_uu, if_pos (by omega : i ≤ M)]
    have := coeff_prod_le (fun j : Fin N => geoF (y j) M)
      (fun j r => norm_coeff_geoF_le (hy j) M r) Finset.univ i
    simpa [gv] using this
  refine le_trans (Finset.sum_le_sum hb) ?_
  rw [← Nat.cast_sum, sum_range_mch]

/-! #### Numeric bound on the total coefficient mass -/

lemma pow_self_le_factorial_mul_exp (N : ℕ) :
    ((N : ℝ)) ^ N ≤ (N.factorial : ℝ) * Real.exp N := by
  have hsum := Real.sum_le_exp_of_nonneg (x := (N : ℝ)) (Nat.cast_nonneg N) (N + 1)
  have hmem : N ∈ Finset.range (N + 1) := Finset.self_mem_range_succ N
  have hsingle : (N : ℝ) ^ N / (N.factorial : ℝ)
      ≤ ∑ i ∈ Finset.range (N + 1), (N : ℝ) ^ i / (i.factorial : ℝ) := by
    refine Finset.single_le_sum (f := fun i => (N : ℝ) ^ i / (i.factorial : ℝ)) ?_ hmem
    intro i _
    positivity
  have hfac : (0 : ℝ) < (N.factorial : ℝ) := by
    exact_mod_cast N.factorial_pos
  have := le_trans hsingle hsum
  rw [div_le_iff₀ hfac] at this
  linarith [this]

lemma mch_mul_mch_le (N M : ℕ) (hN : 1 ≤ N) :
    (mch (N + 1) N : ℝ) * (mch (N + 1) M : ℝ)
      ≤ (4 * Real.exp 1 * ((M : ℝ) + N) / N) ^ N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hfac : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast N.factorial_pos
  -- the central binomial factor
  have h1 : (mch (N + 1) N : ℝ) ≤ (4 : ℝ) ^ N := by
    rw [mch_succ]
    have := Nat.choose_le_two_pow (N + N) N
    have hc : (((N + N).choose N : ℕ) : ℝ) ≤ ((2 ^ (N + N) : ℕ) : ℝ) := by
      exact_mod_cast this
    refine le_trans hc ?_
    push_cast
    rw [show N + N = 2 * N by ring, pow_mul]
    norm_num
  -- the window binomial factor
  have h2 : (mch (N + 1) M : ℝ) ≤ ((M : ℝ) + N) ^ N / (N.factorial : ℝ) := by
    rw [mch_succ]
    have hsymm : (M + N).choose M = (M + N).choose N := by
      have h := Nat.choose_symm (n := M + N) (k := N) (by omega)
      simpa using h
    rw [hsymm]
    have := Nat.choose_le_pow_div (α := ℝ) N (M + N)
    push_cast at this
    exact this
  have h1' : (0 : ℝ) ≤ (mch (N + 1) N : ℝ) := by positivity
  have h2' : (0 : ℝ) ≤ (mch (N + 1) M : ℝ) := by positivity
  have hstep : (mch (N + 1) N : ℝ) * (mch (N + 1) M : ℝ)
      ≤ (4 : ℝ) ^ N * (((M : ℝ) + N) ^ N / (N.factorial : ℝ)) :=
    mul_le_mul h1 h2 h2' (by positivity)
  refine le_trans hstep ?_
  -- replace `1/N!` by `exp N / N^N`
  have hfl := pow_self_le_factorial_mul_exp N
  have hinvfac : (1 : ℝ) / (N.factorial : ℝ) ≤ Real.exp N / (N : ℝ) ^ N := by
    rw [div_le_div_iff₀ hfac (by positivity)]
    linarith [hfl]
  have hMN : (0 : ℝ) ≤ ((M : ℝ) + N) ^ N := by positivity
  have hcalc : (4 : ℝ) ^ N * (((M : ℝ) + N) ^ N / (N.factorial : ℝ))
      ≤ (4 : ℝ) ^ N * (((M : ℝ) + N) ^ N * (Real.exp N / (N : ℝ) ^ N)) := by
    have : ((M : ℝ) + N) ^ N / (N.factorial : ℝ)
        = ((M : ℝ) + N) ^ N * (1 / (N.factorial : ℝ)) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinvfac hMN) (by positivity)
  refine le_trans hcalc (le_of_eq ?_)
  have hexp : Real.exp (N : ℝ) = Real.exp 1 ^ N := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hexp, div_pow, mul_pow, mul_pow]
  field_simp

end Construction

/-! ### The Turán power-sum lower bound -/

/-- **Turán's first main theorem, `8e` form, lower-bound version.**  If every
`z j` has modulus at least `t ≥ 0`, then some exponent `k` in the window
`[M+1, M+N]` satisfies `(N/(8e(M+N)))^N · t^k ≤ ‖∑ j, z j ^ k‖`.

This is the form §4 wants directly: there `t := 1/(3η)`, with no reindexing
of the zero list needed. -/
theorem turan_power_sum_lb {N : ℕ} (hN : 1 ≤ N) (M : ℕ) (z : Fin N → ℂ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht : ∀ j, t ≤ ‖z j‖) :
    ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (8 * Real.exp 1 * (M + N))) ^ N * t ^ k
        ≤ ‖∑ j, z j ^ k‖ := by
  classical
  set c : ℝ := (N : ℝ) / (8 * Real.exp 1 * ((M : ℝ) + N)) with hcdef
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hMN : (0 : ℝ) < (M : ℝ) + N := by positivity
  have hcpos : 0 < c := by rw [hcdef]; positivity
  rcases eq_or_lt_of_le ht0 with hzero | htpos
  · refine ⟨M + 1, le_refl _, by omega, ?_⟩
    rw [← hzero, zero_pow (by omega : M + 1 ≠ 0), mul_zero]
    exact norm_nonneg _
  -- main case: `t > 0`
  by_contra hcon
  have hall : ∀ k, M + 1 ≤ k → k ≤ M + N → ‖∑ j, z j ^ k‖ ≤ c ^ N * t ^ k := by
    intro k h1 h2
    by_contra h3
    exact hcon ⟨k, h1, h2, le_of_lt (not_le.mp h3)⟩
  have hzne : ∀ j, z j ≠ 0 := by
    intro j hj
    have h := ht j
    rw [hj, norm_zero] at h
    exact absurd h (not_le.mpr htpos)
  -- normalised roots
  set y : Fin N → ℂ := fun j => (t : ℂ) / z j with hydef
  have hynorm : ∀ j, ‖y j‖ ≤ 1 := by
    intro j
    have hzp : 0 < ‖z j‖ := lt_of_lt_of_le htpos (ht j)
    rw [hydef]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_pos htpos, div_le_one hzp]
    exact ht j
  have hy0 : ∀ j, y j ≠ 0 := by
    intro j
    rw [hydef]
    simp only [ne_eq, div_eq_zero_iff, not_or]
    refine ⟨?_, hzne j⟩
    exact_mod_cast ne_of_gt htpos
  have hinv : ∀ j, 1 / y j = z j / (t : ℂ) := by
    intro j; rw [hydef]; simp
  -- the window polynomial
  set W : ℂ[X] := om y * uu y M with hWdef
  have hWdeg : W.natDegree < M + N + 1 := by
    have h1 : W.natDegree ≤ (om y).natDegree + (uu y M).natDegree := by
      rw [hWdef]; exact Polynomial.natDegree_mul_le
    have h2 := natDegree_om_le y
    have h3 := natDegree_uu_le y M
    omega
  have hev : ∀ j, W.eval (z j / (t : ℂ)) = 0 := by
    intro j
    rw [hWdef, Polynomial.eval_mul, ← hinv j, eval_om_eq_zero y j (hy0 j), zero_mul]
  -- `W` reproduces `-1` at every normalised root, using only window exponents
  have hwin : ∀ j, ∑ i ∈ Finset.Ico (M + 1) (M + N + 1),
      W.coeff i * (z j / (t : ℂ)) ^ i = -1 := by
    intro j
    have he := Polynomial.eval_eq_sum_range' hWdeg (z j / (t : ℂ))
    rw [hev j] at he
    have hsplit : ∑ i ∈ Finset.range (M + N + 1), W.coeff i * (z j / (t : ℂ)) ^ i
        = (∑ i ∈ Finset.range (M + 1), W.coeff i * (z j / (t : ℂ)) ^ i)
          + ∑ i ∈ Finset.Ico (M + 1) (M + N + 1), W.coeff i * (z j / (t : ℂ)) ^ i := by
      rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.sum_Ico_consecutive _ (Nat.zero_le _) (by omega)]
    have hfirst : ∑ i ∈ Finset.range (M + 1), W.coeff i * (z j / (t : ℂ)) ^ i = 1 := by
      have hc : ∀ i ∈ Finset.range (M + 1), W.coeff i * (z j / (t : ℂ)) ^ i
          = (if i = 0 then (1 : ℂ) else 0) * (z j / (t : ℂ)) ^ i := by
        intro i hi
        rw [hWdef, coeff_om_mul_uu_low y M i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
      rw [Finset.sum_congr rfl hc]
      simp
    rw [hsplit, hfirst] at he
    linear_combination -he
  -- sum over the roots
  have hterm : ∀ i : ℕ, ∑ j, W.coeff i * (z j / (t : ℂ)) ^ i
      = W.coeff i * (∑ j, z j ^ i) / (t : ℂ) ^ i := by
    intro i
    have h : ∀ j : Fin N, W.coeff i * (z j / (t : ℂ)) ^ i
        = (W.coeff i * z j ^ i) * ((t : ℂ) ^ i)⁻¹ := by
      intro j; rw [div_pow]; ring
    rw [Finset.sum_congr rfl (fun j _ => h j), ← Finset.sum_mul, ← Finset.mul_sum,
      ← div_eq_mul_inv]
  have hsum : ∑ i ∈ Finset.Ico (M + 1) (M + N + 1),
      W.coeff i * (∑ j, z j ^ i) / (t : ℂ) ^ i = -(N : ℂ) := by
    have h1 : ∑ j : Fin N, ∑ i ∈ Finset.Ico (M + 1) (M + N + 1),
        W.coeff i * (z j / (t : ℂ)) ^ i = ∑ _j : Fin N, (-1 : ℂ) :=
      Finset.sum_congr rfl (fun j _ => hwin j)
    rw [Finset.sum_comm] at h1
    rw [Finset.sum_congr rfl (fun i _ => (hterm i).symm)]
    rw [h1]
    simp
  -- take norms and use the window hypothesis
  have hNle : (N : ℝ) ≤ (∑ i ∈ Finset.Ico (M + 1) (M + N + 1), ‖W.coeff i‖) * c ^ N := by
    have h1 : (N : ℝ) = ‖(-(N : ℂ))‖ := by simp
    rw [h1, ← hsum, Finset.sum_mul]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum ?_
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hpow : (0 : ℝ) < t ^ i := pow_pos htpos i
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos htpos, div_le_iff₀ hpow]
    calc ‖W.coeff i‖ * ‖∑ j, z j ^ i‖
        ≤ ‖W.coeff i‖ * (c ^ N * t ^ i) :=
          mul_le_mul_of_nonneg_left (hall i hi.1 (by omega)) (norm_nonneg _)
      _ = ‖W.coeff i‖ * c ^ N * t ^ i := by ring
  -- bound the coefficient mass
  have hAle : ∑ i ∈ Finset.Ico (M + 1) (M + N + 1), ‖W.coeff i‖ ≤ l1 W := by
    rw [l1_eq_sum_range hWdeg]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => norm_nonneg _)
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact Finset.mem_range.mpr (by omega)
  have hl1 : l1 W ≤ (mch (N + 1) N : ℝ) * (mch (N + 1) M : ℝ) := by
    refine le_trans (l1_mul_le _ _) ?_
    exact mul_le_mul (l1_om_le y hynorm) (l1_uu_le y M hynorm) (l1_nonneg _)
      (by positivity)
  have hmass := le_trans hAle hl1
  have hBound := mch_mul_mch_le N M hN
  have hchain : (N : ℝ) ≤ (4 * Real.exp 1 * ((M : ℝ) + N) / N) ^ N * c ^ N := by
    refine le_trans hNle ?_
    exact mul_le_mul_of_nonneg_right (le_trans hmass hBound) (by positivity)
  -- the numerical contradiction
  have hprod : (4 * Real.exp 1 * ((M : ℝ) + N) / N) * c = 1 / 2 := by
    rw [hcdef]
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    field_simp
    ring
  have hhalf : (4 * Real.exp 1 * ((M : ℝ) + N) / N) ^ N * c ^ N = (1 / 2 : ℝ) ^ N := by
    rw [← mul_pow, hprod]
  rw [hhalf] at hchain
  have hle : ((1 : ℝ) / 2) ^ N ≤ (1 / 2 : ℝ) ^ 1 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
  have h1N : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [pow_one] at hle
  linarith [hchain, hle, h1N]

/-- **Turán's first main theorem, `8e` form, min-normalised.**  Conclusion,
window and constant are those of Z7-tzlite §1.1; the hypothesis is the
min-normalisation `hmin` in place of §1.1's `hmax` (see the module docstring
— this is the delta reported for re-freeze under spec §7.3). -/
theorem turan_power_sum_min {N : ℕ} (hN : 1 ≤ N) (M : ℕ) (z : Fin N → ℂ)
    (hmin : ∀ j, ‖z ⟨0, hN⟩‖ ≤ ‖z j‖) :
    ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (8 * Real.exp 1 * (M + N))) ^ N * ‖z ⟨0, hN⟩‖ ^ k
        ≤ ‖∑ j, z j ^ k‖ :=
  turan_power_sum_lb hN M z (norm_nonneg _) hmin

end

end Turan

end Carmichael

/-! ## Part 2: Turán's second main theorem, max-normalised (Z7-tzlite §1.1)

Deliverables: `turan_power_sum_max` and `turan_power_sum_max_lb`, byte-compatible
with the frozen contract.

Route (adjudicated, Z7-tzlite §1.3): van der Poorten's interpolation proof of the
second main theorem, with two repairs.  Makai's circle lemma is replaced by the
Chebyshev equioscillation bound (`Polynomial.Chebyshev.coeff_le_of_forall_abs_le_one`
gives the sharp constant `2·(δ/4)^n`, which the `8e` budget requires — the
finite-difference variant of the crib, at constant `δ/(2e)`, does not fit the
frozen constant).  Van der Poorten's unproved "a fortiori" prefix estimate is
repaired by ordering the Newton nodes by decreasing `| ‖z j − 1‖ − R |` and using
the sorted-prefix inequality `(∏_{h<N} f)^i ≤ (∏_{h<i} f)^N`.

Skeleton, for `z : Fin N → ℂ` with `z 0 = 1` and `‖z j‖ ≤ 1` (`N ≥ 2`):

* `δ := (N−1)/(M+N)`; Chebyshev selection gives `R ∈ (0, δ]` with
  `∏_j |R − ‖z j − 1‖| ≥ 2 (δ/4)^N`, so the circle `|ζ−1| = R` avoids every
  `z j` and the origin, and every sorted prefix has
  `∏_{h≤i} |R − d_h| ≥ (δ/4)^{i+1}`.
* `b i := (2πi)⁻¹ ∮_{|ζ−1|=R} dζ / (ζ^{M+1}·(ζ−ν 0)⋯(ζ−ν i))`, `ν` the sorted
  enumeration; the Newton polynomial `P := ∑_i b i·∏_{h<i}(X − ν h)` (degree `< N`)
  takes the value `ν j^{−(M+1)}` at nodes inside the circle and `0` outside
  (telescoping identity + Cauchy integral formula resp. Cauchy–Goursat).
* `T := P·X^{M+1}` is supported on exponents `[M+1, M+N]` and
  `∑_j T(z j) = #\{j : z j inside\} ≥ 1` (the designated entry `z 0 = 1` is inside).
* `ℓ¹` estimate: `l1 P ≤ (32/7)·(1−δ)^{−(M+1)}·(8/δ)^{N−1}`.
* Endgame: `(32/7)·(1−δ)^{−(M+1)}·(8/δ)^{N−1}·(N/(8e(M+N)))^N ≤ 4/7 < 1`, so some
  window power sum defeats any putative uniform bound `c^N` — Turán's second main
  theorem with constant `(N/(8e(M+N)))^N`.
-/

namespace Carmichael

namespace Turan

noncomputable section

/-! ### The Chebyshev equioscillation bound on an interval -/

/-- A monic real polynomial of degree `n ≥ 1` has absolute value at least
`2·(δ/4)^n` somewhere on `[0, δ]` (the Chebyshev min–max bound). -/
lemma exists_abs_eval_ge {n : ℕ} (hn : 1 ≤ n) {p : ℝ[X]} (hp : p.Monic)
    (hdeg : p.natDegree = n) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R ∈ Set.Icc (0 : ℝ) δ, 2 * (δ / 4) ^ n ≤ |p.eval R| := by
  obtain ⟨R, hRmem, hRmax⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := δ)).exists_isMaxOn
      (Set.nonempty_Icc.mpr hδ.le) (p.continuous.abs.continuousOn)
  refine ⟨R, hRmem, ?_⟩
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  -- `A := |p.eval R| > 0` since `p` has finitely many roots
  have hp0 : p ≠ 0 := hp.ne_zero
  have hApos : 0 < |p.eval R| := by
    obtain ⟨x, hx⟩ := ((Set.Icc_infinite hδ).sdiff
      (p.finite_setOfPred_isRoot hp0)).nonempty
    have hx2 : ¬ p.IsRoot x := hx.2
    calc (0 : ℝ) < |p.eval x| := abs_pos.mpr hx2
      _ ≤ |p.eval R| := isMaxOn_iff.mp hRmax x hx.1
  set A : ℝ := |p.eval R| with hA
  -- rescale to `[-1, 1]`
  set q : ℝ[X] := p.comp (Polynomial.C (δ/2) * Polynomial.X + Polynomial.C (δ/2)) with hq
  have hlin_deg : (Polynomial.C (δ/2) * Polynomial.X + Polynomial.C (δ/2)).natDegree = 1 :=
    Polynomial.natDegree_linear (ne_of_gt hδ2)
  have hqdeg : q.natDegree = n := by
    rw [hq, Polynomial.natDegree_comp, hlin_deg, hdeg, mul_one]
  have hqcoeff : q.coeff n = (δ/2) ^ n := by
    have h1 : q.leadingCoeff = (δ/2) ^ n := by
      rw [hq, Polynomial.leadingCoeff_comp (by rw [hlin_deg]; exact one_ne_zero),
        hp.leadingCoeff, one_mul, Polynomial.leadingCoeff_linear (ne_of_gt hδ2), hdeg]
    rwa [Polynomial.leadingCoeff, hqdeg] at h1
  have hqval : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |q.eval y| ≤ A := by
    intro y hy
    rw [hq, Polynomial.eval_comp]
    have harg : (Polynomial.C (δ/2) * Polynomial.X + Polynomial.C (δ/2)).eval y
        = δ/2 * y + δ/2 := by simp
    rw [harg]
    refine isMaxOn_iff.mp hRmax _ ⟨?_, ?_⟩
    · nlinarith [hy.1]
    · nlinarith [hy.2]
  -- apply the Chebyshev coefficient bound to `A⁻¹ • q`
  set P : ℝ[X] := Polynomial.C A⁻¹ * q with hP
  have hPnat : P.natDegree ≤ n := by
    rw [hP]
    exact le_trans (Polynomial.natDegree_C_mul_le _ _) (le_of_eq hqdeg)
  have hPdeg : P.degree ≤ (n : ℕ) :=
    le_trans Polynomial.degree_le_natDegree (by exact_mod_cast hPnat)
  have hPbnd : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |P.eval x| ≤ 1 := by
    intro y hy
    rw [hP, Polynomial.eval_mul, Polynomial.eval_C, abs_mul, abs_inv, abs_of_pos hApos]
    calc A⁻¹ * |q.eval y| ≤ A⁻¹ * A :=
          mul_le_mul_of_nonneg_left (hqval y hy) (inv_nonneg.mpr hApos.le)
      _ = 1 := inv_mul_cancel₀ hApos.ne'
  have hcoeff := Polynomial.Chebyshev.coeff_le_of_forall_abs_le_one hPdeg hPbnd
  have hPc : P.coeff n = A⁻¹ * (δ/2) ^ n := by
    rw [hP, Polynomial.coeff_C_mul, hqcoeff]
  rw [hPc] at hcoeff
  -- conclude: `2 (δ/4)^n · 2^(n-1) = (δ/2)^n ≤ A · 2^(n-1)`
  have h3 : (δ/2) ^ n ≤ A * 2 ^ (n - 1) := by
    have h4 := mul_le_mul_of_nonneg_left hcoeff hApos.le
    rwa [← mul_assoc, mul_inv_cancel₀ hApos.ne', one_mul] at h4
  have h2n : (2 : ℝ) * (δ/4) ^ n * 2 ^ (n - 1) = (δ/2) ^ n := by
    have e1 : ((4 : ℝ)) ^ n = 2 ^ n * 2 ^ n := by
      rw [← mul_pow]; norm_num
    have e2 : (2 : ℝ) * 2 ^ (n - 1) = 2 ^ n := by
      rw [← pow_succ', Nat.sub_add_cancel hn]
    calc (2 : ℝ) * (δ/4) ^ n * 2 ^ (n - 1)
        = (2 * 2 ^ (n - 1)) * (δ ^ n / (2 ^ n * 2 ^ n)) := by rw [div_pow, e1]; ring
      _ = 2 ^ n * (δ ^ n / (2 ^ n * 2 ^ n)) := by rw [e2]
      _ = (2 ^ n * δ ^ n) / (2 ^ n * 2 ^ n) := by rw [mul_div_assoc']
      _ = δ ^ n / 2 ^ n := mul_div_mul_left _ _ (by positivity)
      _ = (δ/2) ^ n := (div_pow δ 2 n).symm
  have h5 : (0 : ℝ) < 2 ^ (n - 1) := by positivity
  have h6 : 2 * (δ/4) ^ n * 2 ^ (n - 1) ≤ A * 2 ^ (n - 1) := by
    rw [h2n]; exact h3
  exact le_of_mul_le_mul_right h6 h5

/-- Chebyshev node selection for the circle radius: some `R ∈ [0, δ]` keeps the
distance product `∏_{h<n} |R − d h|` at least `2·(δ/4)^n`. -/
lemma exists_cheb_radius {n : ℕ} (hn : 1 ≤ n) (d : ℕ → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ R ∈ Set.Icc (0 : ℝ) δ,
      2 * (δ / 4) ^ n ≤ ∏ h ∈ Finset.range n, |R - d h| := by
  have hmon : ∀ h ∈ Finset.range n, (Polynomial.X - Polynomial.C (d h)).Monic :=
    fun h _ => Polynomial.monic_X_sub_C (d h)
  have hp : (∏ h ∈ Finset.range n, (Polynomial.X - Polynomial.C (d h))).Monic :=
    Polynomial.monic_prod_of_monic _ _ hmon
  have hdeg : (∏ h ∈ Finset.range n, (Polynomial.X - Polynomial.C (d h))).natDegree = n := by
    rw [Polynomial.natDegree_prod_of_monic _ _ hmon]
    simp
  obtain ⟨R, hR, hval⟩ := exists_abs_eval_ge hn hp hdeg hδ
  refine ⟨R, hR, ?_⟩
  calc 2 * (δ/4) ^ n
      ≤ |(∏ h ∈ Finset.range n, (Polynomial.X - Polynomial.C (d h))).eval R| := hval
    _ = ∏ h ∈ Finset.range n, |R - d h| := by
        rw [Polynomial.eval_prod, Finset.abs_prod]
        exact Finset.prod_congr rfl fun h _ => by simp

/-! ### The sorted-prefix inequality -/

/-- For an antitone positive tuple, every prefix product dominates the geometric
mean: `(∏_{h<n} f)^i ≤ (∏_{h<i} f)^n`. -/
lemma prod_range_pow_le_prod_prefix_pow (f : ℕ → ℝ) {n : ℕ}
    (hpos : ∀ h, h < n → 0 < f h)
    (hanti : ∀ h h', h ≤ h' → h' < n → f h' ≤ f h)
    {i : ℕ} (hi : i ≤ n) :
    (∏ h ∈ Finset.range n, f h) ^ i ≤ (∏ h ∈ Finset.range i, f h) ^ n := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  set c : ℝ := f (i - 1) with hc
  have hi1 : i - 1 < n := by omega
  have hcpos : 0 < c := hpos _ hi1
  have hA : 0 < ∏ h ∈ Finset.range i, f h :=
    Finset.prod_pos fun h hh => hpos h (by
      have := Finset.mem_range.mp hh; omega)
  have hB0 : 0 < ∏ h ∈ Finset.Ico i n, f h :=
    Finset.prod_pos fun h hh => hpos h (Finset.mem_Ico.mp hh).2
  have hsplit : (∏ h ∈ Finset.range i, f h) * ∏ h ∈ Finset.Ico i n, f h
      = ∏ h ∈ Finset.range n, f h := Finset.prod_range_mul_prod_Ico f hi
  have hBle : ∏ h ∈ Finset.Ico i n, f h ≤ c ^ (n - i) := by
    calc ∏ h ∈ Finset.Ico i n, f h ≤ ∏ _h ∈ Finset.Ico i n, c := by
          refine Finset.prod_le_prod (fun h hh => (hpos h (Finset.mem_Ico.mp hh).2).le) ?_
          intro h hh
          have hh' := Finset.mem_Ico.mp hh
          exact hanti (i - 1) h (by omega) hh'.2
      _ = c ^ (n - i) := by rw [Finset.prod_const, Nat.card_Ico]
  have hAge : c ^ i ≤ ∏ h ∈ Finset.range i, f h := by
    calc c ^ i = ∏ _h ∈ Finset.range i, c := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ h ∈ Finset.range i, f h := by
          refine Finset.prod_le_prod (fun _ _ => hcpos.le) ?_
          intro h hh
          have hhi := Finset.mem_range.mp hh
          exact hanti h (i - 1) (by omega) hi1
  have key : (∏ h ∈ Finset.Ico i n, f h) ^ i ≤ (∏ h ∈ Finset.range i, f h) ^ (n - i) := by
    calc (∏ h ∈ Finset.Ico i n, f h) ^ i ≤ (c ^ (n - i)) ^ i :=
          pow_le_pow_left₀ hB0.le hBle i
      _ = (c ^ i) ^ (n - i) := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (∏ h ∈ Finset.range i, f h) ^ (n - i) :=
          pow_le_pow_left₀ (by positivity) hAge _
  calc (∏ h ∈ Finset.range n, f h) ^ i
      = ((∏ h ∈ Finset.range i, f h) * ∏ h ∈ Finset.Ico i n, f h) ^ i := by rw [hsplit]
    _ = (∏ h ∈ Finset.range i, f h) ^ i * (∏ h ∈ Finset.Ico i n, f h) ^ i := mul_pow _ _ _
    _ ≤ (∏ h ∈ Finset.range i, f h) ^ i * (∏ h ∈ Finset.range i, f h) ^ (n - i) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (∏ h ∈ Finset.range i, f h) ^ n := by
        rw [← pow_add, Nat.add_sub_cancel' hi]

/-! ### Additions to the `ℓ¹` layer -/

lemma l1_zero : l1 (0 : ℂ[X]) = 0 := by
  rw [l1_eq_sum_range (n := 1) (by simp)]
  simp

lemma l1_one : l1 (1 : ℂ[X]) = 1 := by
  rw [l1_eq_sum_range (n := 1) (by simp)]
  simp

lemma l1_add_le (p q : ℂ[X]) : l1 (p + q) ≤ l1 p + l1 q := by
  set n := max p.natDegree q.natDegree + 1 with hn
  have h1 : (p + q).natDegree < n :=
    Nat.lt_succ_of_le (le_trans (Polynomial.natDegree_add_le p q) le_rfl)
  have h2 : p.natDegree < n := Nat.lt_succ_of_le (le_max_left _ _)
  have h3 : q.natDegree < n := Nat.lt_succ_of_le (le_max_right _ _)
  rw [l1_eq_sum_range h1, l1_eq_sum_range h2, l1_eq_sum_range h3, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Polynomial.coeff_add]
  exact norm_add_le _ _

lemma l1_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℂ[X]) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp [l1_zero]
  | cons a t ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      calc l1 (f a + ∑ i ∈ t, f i) ≤ l1 (f a) + l1 (∑ i ∈ t, f i) := l1_add_le _ _
        _ ≤ l1 (f a) + ∑ i ∈ t, l1 (f i) := by linarith [ih]

lemma l1_C_mul_le (a : ℂ) (p : ℂ[X]) : l1 (Polynomial.C a * p) ≤ ‖a‖ * l1 p := by
  have h1 : (Polynomial.C a * p).natDegree < p.natDegree + 1 :=
    Nat.lt_succ_of_le (Polynomial.natDegree_C_mul_le a p)
  rw [l1_eq_sum_range h1, l1_eq_sum_range (Nat.lt_succ_self p.natDegree), Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Polynomial.coeff_C_mul, norm_mul]

lemma l1_X_sub_C (a : ℂ) : l1 (Polynomial.X - Polynomial.C a) = 1 + ‖a‖ := by
  have h : (Polynomial.X - Polynomial.C a).natDegree < 2 := by
    rw [Polynomial.natDegree_X_sub_C]; omega
  rw [l1_eq_sum_range h, Finset.sum_range_succ, Finset.sum_range_one]
  have h0 : (Polynomial.X - Polynomial.C a).coeff 0 = -a := by simp
  have h1 : (Polynomial.X - Polynomial.C a).coeff 1 = 1 := by simp
  rw [h0, h1, norm_neg, norm_one]
  ring

lemma l1_prod_X_sub_C_le (ν : ℕ → ℂ) (i : ℕ) :
    l1 (∏ h ∈ Finset.range i, (Polynomial.X - Polynomial.C (ν h)))
      ≤ ∏ h ∈ Finset.range i, (1 + ‖ν h‖) := by
  induction i with
  | zero => simp [l1_one]
  | succ i ih =>
      rw [Finset.prod_range_succ, Finset.prod_range_succ]
      refine le_trans (l1_mul_le _ _) ?_
      rw [l1_X_sub_C]
      refine mul_le_mul ih le_rfl (by positivity) ?_
      exact Finset.prod_nonneg fun _ _ => by positivity

/-! ### The contour-integral interpolant -/

section Contour

open Metric

/-- Telescoping identity for the Newton kernel, multiplied through by `ζ − x`. -/
lemma newton_telescope (N : ℕ) (ν : ℕ → ℂ) (x ζ : ℂ)
    (hζ : ∀ h, h < N → ζ - ν h ≠ 0) :
    (∑ i ∈ Finset.range N,
        (∏ h ∈ Finset.range i, (x - ν h)) * (∏ h ∈ Finset.range (i+1), (ζ - ν h))⁻¹)
      * (ζ - x)
      = 1 - (∏ h ∈ Finset.range N, (x - ν h)) * (∏ h ∈ Finset.range N, (ζ - ν h))⁻¹ := by
  have key : ∀ i ∈ Finset.range N,
      ((∏ h ∈ Finset.range i, (x - ν h)) * (∏ h ∈ Finset.range (i+1), (ζ - ν h))⁻¹) * (ζ - x)
        = (∏ h ∈ Finset.range i, (x - ν h)) * (∏ h ∈ Finset.range i, (ζ - ν h))⁻¹
          - (∏ h ∈ Finset.range (i+1), (x - ν h)) * (∏ h ∈ Finset.range (i+1), (ζ - ν h))⁻¹ := by
    intro i hi
    have hiN : i < N := Finset.mem_range.mp hi
    have hzi : ζ - ν i ≠ 0 := hζ i hiN
    have hB : (∏ h ∈ Finset.range i, (ζ - ν h)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun h hh => hζ h (lt_trans (Finset.mem_range.mp hh) hiN)
    rw [Finset.prod_range_succ (fun h => x - ν h), Finset.prod_range_succ (fun h => ζ - ν h),
      mul_inv]
    field_simp
    ring
  rw [Finset.sum_mul, Finset.sum_congr rfl key,
    Finset.sum_range_sub' (fun i => (∏ h ∈ Finset.range i, (x - ν h)) *
      (∏ h ∈ Finset.range i, (ζ - ν h))⁻¹)]
  simp

lemma norm_ge_of_mem_sphere {R : ℝ} {ζ : ℂ} (hζ : ζ ∈ sphere (1 : ℂ) R) :
    1 - R ≤ ‖ζ‖ := by
  rw [mem_sphere_iff_norm] at hζ
  have h := abs_norm_sub_norm_le ζ (1 : ℂ)
  rw [hζ, norm_one] at h
  have := (abs_le.mp h).1
  linarith

lemma dist_node_le_of_mem_sphere {R : ℝ} {ζ w : ℂ} (hζ : ζ ∈ sphere (1 : ℂ) R) :
    |R - ‖w - 1‖| ≤ ‖ζ - w‖ := by
  rw [mem_sphere_iff_norm] at hζ
  have h := abs_norm_sub_norm_le (ζ - 1) (w - 1)
  rw [hζ] at h
  have he : ζ - 1 - (w - 1) = ζ - w := by ring
  rwa [he] at h

/-- The van der Poorten interpolant: a polynomial of degree `< N` that takes the
value `(ν j)^{-(M+1)}` at every node inside the circle `|ζ − 1| = R` and `0` at
every node outside, with the contour bound on its `ℓ¹` mass. -/
theorem exists_window_interpolant (M N : ℕ) (hN : 0 < N) (ν : ℕ → ℂ) {R : ℝ}
    (hR0 : 0 < R) (hR1 : R < 1) (hoff : ∀ h, h < N → ‖ν h - 1‖ ≠ R) :
    ∃ P : ℂ[X], P.natDegree < N ∧
      (∀ j, j < N → P.eval (ν j) = if ‖ν j - 1‖ < R then ((ν j) ^ (M+1))⁻¹ else 0) ∧
      l1 P ≤ ∑ i ∈ Finset.range N,
        R / ((1 - R) ^ (M+1) * ∏ h ∈ Finset.range (i+1), |R - ‖ν h - 1‖|) *
          ∏ h ∈ Finset.range i, (1 + ‖ν h‖) := by
  classical
  have h1R : (0 : ℝ) < 1 - R := by linarith
  have hfacpos : ∀ h, h < N → 0 < |R - ‖ν h - 1‖| := fun h hh =>
    abs_pos.mpr (sub_ne_zero.mpr fun hEq => hoff h hh hEq.symm)
  have hprodpos : ∀ i, i < N → 0 < ∏ h ∈ Finset.range (i+1), |R - ‖ν h - 1‖| := by
    intro i hi
    exact Finset.prod_pos fun h hh => hfacpos h
      (lt_of_lt_of_le (Finset.mem_range.mp hh) (Nat.succ_le_of_lt hi))
  set F : ℕ → ℂ → ℂ :=
    fun i ζ => ((ζ ^ (M+1)) * ∏ h ∈ Finset.range (i+1), (ζ - ν h))⁻¹ with hF
  have hsz : ∀ ζ ∈ sphere (1 : ℂ) R, ζ ≠ 0 := by
    intro ζ hζ h0
    have := norm_ge_of_mem_sphere hζ
    rw [h0, norm_zero] at this
    linarith
  have hsnode : ∀ ζ ∈ sphere (1 : ℂ) R, ∀ h, h < N → ζ - ν h ≠ 0 := by
    intro ζ hζ h hh h0
    have h1 := dist_node_le_of_mem_sphere (w := ν h) hζ
    have h2 := hfacpos h hh
    rw [h0, norm_zero] at h1
    linarith
  have hden : ∀ i, i < N → ∀ ζ ∈ sphere (1 : ℂ) R,
      (ζ ^ (M+1)) * ∏ h ∈ Finset.range (i+1), (ζ - ν h) ≠ 0 := by
    intro i hi ζ hζ
    refine mul_ne_zero (pow_ne_zero _ (hsz ζ hζ)) ?_
    exact Finset.prod_ne_zero_iff.mpr fun h hh => hsnode ζ hζ h
      (lt_of_lt_of_le (Finset.mem_range.mp hh) (Nat.succ_le_of_lt hi))
  have hFcont : ∀ i, i < N → ContinuousOn (F i) (sphere (1 : ℂ) R) := by
    intro i hi
    refine ContinuousOn.inv₀ ?_ (hden i hi)
    exact ((continuous_pow (M+1)).mul
      (continuous_finsetProd _ fun h _ => continuous_id.sub continuous_const)).continuousOn
  have hFint : ∀ i, i < N → CircleIntegrable (F i) 1 R := fun i hi =>
    (hFcont i hi).circleIntegrable hR0.le
  set b : ℕ → ℂ :=
    fun i => (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∮ ζ in C(1, R), F i ζ with hb
  set P : ℂ[X] := ∑ i ∈ Finset.range N,
    Polynomial.C (b i) * ∏ h ∈ Finset.range i, (Polynomial.X - Polynomial.C (ν h)) with hP
  -- degree bound
  have hPdeg : P.natDegree < N := by
    have hle : P.natDegree ≤ N - 1 := by
      rw [hP]
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      have hstep : (∏ h ∈ Finset.range i,
          (Polynomial.X - Polynomial.C (ν h))).natDegree ≤ i := by
        refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
        rw [Finset.sum_congr rfl (fun h _ => Polynomial.natDegree_X_sub_C (ν h))]
        simp
      have hiN := Finset.mem_range.mp hi
      exact le_trans hstep (by omega)
    omega
  -- norm bound on the Newton coefficients
  have hbnd : ∀ i, i < N →
      ‖b i‖ ≤ R / ((1 - R) ^ (M+1) * ∏ h ∈ Finset.range (i+1), |R - ‖ν h - 1‖|) := by
    intro i hi
    set D : ℝ := (1 - R) ^ (M+1) * ∏ h ∈ Finset.range (i+1), |R - ‖ν h - 1‖| with hD
    have hDpos : 0 < D := mul_pos (pow_pos h1R _) (hprodpos i hi)
    have hpt : ∀ ζ ∈ sphere (1 : ℂ) R, ‖F i ζ‖ ≤ D⁻¹ := by
      intro ζ hζ
      simp only [hF]
      rw [norm_inv, norm_mul, norm_pow]
      refine inv_anti₀ hDpos ?_
      rw [hD]
      have hp1 : (1 - R) ^ (M+1) ≤ ‖ζ‖ ^ (M+1) :=
        pow_le_pow_left₀ h1R.le (norm_ge_of_mem_sphere hζ) _
      have hp2 : ∏ h ∈ Finset.range (i+1), |R - ‖ν h - 1‖|
          ≤ ∏ h ∈ Finset.range (i+1), ‖ζ - ν h‖ :=
        Finset.prod_le_prod (fun h _ => abs_nonneg _)
          (fun h _ => dist_node_le_of_mem_sphere hζ)
      have hnp : ‖∏ h ∈ Finset.range (i+1), (ζ - ν h)‖
          = ∏ h ∈ Finset.range (i+1), ‖ζ - ν h‖ := norm_prod _ _
      rw [hnp]
      exact mul_le_mul hp1 hp2 (Finset.prod_nonneg fun _ _ => abs_nonneg _)
        (by positivity)
    have hnorm := circleIntegral.norm_integral_le_of_norm_le_const hR0.le hpt
    have h2pi : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
      rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      norm_num
    have hπpos : (0 : ℝ) < 2 * Real.pi := by positivity
    calc ‖b i‖ = ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * ‖∮ ζ in C(1, R), F i ζ‖ := by
          rw [hb]; exact norm_mul _ _
      _ ≤ ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ * (2 * Real.pi * R * D⁻¹) := by
          refine mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = (2 * Real.pi)⁻¹ * (2 * Real.pi * R * D⁻¹) := by rw [norm_inv, h2pi]
      _ = ((2 * Real.pi)⁻¹ * (2 * Real.pi)) * (R * D⁻¹) := by ring
      _ = R * D⁻¹ := by rw [inv_mul_cancel₀ (ne_of_gt hπpos), one_mul]
      _ = R / D := (div_eq_mul_inv R D).symm
  -- value matching at the nodes
  have hval : ∀ j, j < N →
      P.eval (ν j) = if ‖ν j - 1‖ < R then ((ν j) ^ (M+1))⁻¹ else 0 := by
    intro j hj
    have hev : P.eval (ν j)
        = ∑ i ∈ Finset.range N, b i * ∏ h ∈ Finset.range i, (ν j - ν h) := by
      rw [hP, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
      congr 1
      exact Finset.prod_congr rfl fun h _ => by simp
    have hintKF : ∀ i ∈ Finset.range N, CircleIntegrable
        (fun ζ => (∏ h ∈ Finset.range i, (ν j - ν h)) * F i ζ) 1 R := by
      intro i hi
      exact (continuousOn_const.mul (hFcont i (Finset.mem_range.mp hi))).circleIntegrable
        hR0.le
    have hswap : ∑ i ∈ Finset.range N, b i * ∏ h ∈ Finset.range i, (ν j - ν h)
        = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
          ∮ ζ in C(1, R), ∑ i ∈ Finset.range N,
            (∏ h ∈ Finset.range i, (ν j - ν h)) * F i ζ := by
      rw [circleIntegral.integral_fun_sum hintKF, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [circleIntegral.integral_const_mul]
      simp only [hb]
      ring
    have hpt : Set.EqOn
        (fun ζ => ∑ i ∈ Finset.range N, (∏ h ∈ Finset.range i, (ν j - ν h)) * F i ζ)
        (fun ζ => (ζ - ν j)⁻¹ * ((ζ ^ (M+1) : ℂ))⁻¹)
        (sphere (1 : ℂ) R) := by
      intro ζ hζ
      simp only
      have hnodes : ∀ h, h < N → ζ - ν h ≠ 0 := hsnode ζ hζ
      have hζj : ζ - ν j ≠ 0 := hnodes j hj
      have htel := newton_telescope N ν (ν j) ζ hnodes
      have hΦ : (∏ h ∈ Finset.range N, (ν j - ν h)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.mpr hj) (sub_self _)
      rw [hΦ, zero_mul, sub_zero] at htel
      set S : ℂ := ∑ i ∈ Finset.range N,
        (∏ h ∈ Finset.range i, (ν j - ν h)) * (∏ h ∈ Finset.range (i+1), (ζ - ν h))⁻¹
        with hS
      have hSeq : S = (ζ - ν j)⁻¹ := by
        calc S = S * ((ζ - ν j) * (ζ - ν j)⁻¹) := by
              rw [mul_inv_cancel₀ hζj, mul_one]
          _ = (S * (ζ - ν j)) * (ζ - ν j)⁻¹ := by ring
          _ = 1 * (ζ - ν j)⁻¹ := by rw [htel]
          _ = (ζ - ν j)⁻¹ := one_mul _
      have hexp : ∑ i ∈ Finset.range N, (∏ h ∈ Finset.range i, (ν j - ν h)) * F i ζ
          = ((ζ ^ (M+1) : ℂ))⁻¹ * S := by
        rw [hS, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [hF]
        rw [mul_inv]
        ring
      rw [hexp, hSeq]
      ring
    rw [hev, hswap, circleIntegral.integral_congr hR0.le hpt]
    rcases lt_or_gt_of_ne (hoff j hj) with hin | hout
    · -- node inside the circle: Cauchy integral formula
      rw [if_pos hin]
      have hball : ν j ∈ ball (1 : ℂ) R := by
        rw [mem_ball, dist_eq_norm]; exact hin
      have hcont : ContinuousOn (fun ζ : ℂ => ((ζ ^ (M+1) : ℂ))⁻¹)
          (closedBall (1 : ℂ) R) := by
        refine ContinuousOn.inv₀ (continuous_pow (M+1)).continuousOn ?_
        intro ζ hζ
        refine pow_ne_zero _ ?_
        intro h0
        rw [mem_closedBall, dist_eq_norm, h0, zero_sub, norm_neg, norm_one] at hζ
        linarith
      have hdiff : ∀ x ∈ ball (1 : ℂ) R \ (∅ : Set ℂ), DifferentiableAt ℂ
          (fun ζ : ℂ => ((ζ ^ (M+1) : ℂ))⁻¹) x := by
        intro x hx
        have hx0 : x ≠ 0 := by
          intro h0
          have hx1 := hx.1
          rw [mem_ball, dist_eq_norm, h0, zero_sub, norm_neg, norm_one] at hx1
          linarith
        exact (differentiableAt_pow (M+1)).inv (pow_ne_zero _ hx0)
      have hcau := Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        Set.countable_empty hball hcont hdiff
      simp only [smul_eq_mul] at hcau
      exact hcau
    · -- node outside the circle: Cauchy–Goursat
      rw [if_neg (not_lt.mpr hout.le)]
      have hne : ∀ ζ : ℂ, ζ ∈ closedBall (1 : ℂ) R → (ζ - ν j ≠ 0 ∧ ζ ≠ 0) := by
        intro ζ hζ
        rw [mem_closedBall, dist_eq_norm] at hζ
        constructor
        · intro h0
          have h1 : ζ = ν j := sub_eq_zero.mp h0
          rw [h1] at hζ
          linarith
        · intro h0
          rw [h0, zero_sub, norm_neg, norm_one] at hζ
          linarith
      have hcont : ContinuousOn (fun ζ : ℂ => (ζ - ν j)⁻¹ * ((ζ ^ (M+1) : ℂ))⁻¹)
          (closedBall (1 : ℂ) R) := by
        refine ContinuousOn.mul ?_ ?_
        · exact ContinuousOn.inv₀ (continuous_id.sub continuous_const).continuousOn
            fun ζ hζ => (hne ζ hζ).1
        · exact ContinuousOn.inv₀ (continuous_pow (M+1)).continuousOn
            fun ζ hζ => pow_ne_zero _ (hne ζ hζ).2
      have hdiff : ∀ x ∈ ball (1 : ℂ) R \ (∅ : Set ℂ), DifferentiableAt ℂ
          (fun ζ : ℂ => (ζ - ν j)⁻¹ * ((ζ ^ (M+1) : ℂ))⁻¹) x := by
        intro x hx
        have hx1 := hne x (ball_subset_closedBall hx.1)
        have hd0 : DifferentiableAt ℂ (fun ζ : ℂ => ζ - ν j) x :=
          differentiableAt_id.sub_const _
        have hd1 : DifferentiableAt ℂ (fun ζ : ℂ => (ζ - ν j)⁻¹) x := hd0.inv hx1.1
        have hd2 : DifferentiableAt ℂ (fun ζ : ℂ => ((ζ ^ (M+1) : ℂ))⁻¹) x :=
          (differentiableAt_pow (M+1)).inv (pow_ne_zero _ hx1.2)
        exact hd1.mul hd2
      have hzero := Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
        hR0.le Set.countable_empty hcont hdiff
      rw [hzero, mul_zero]
  -- ℓ¹ bound
  have hl1 : l1 P ≤ ∑ i ∈ Finset.range N,
      R / ((1 - R) ^ (M+1) * ∏ h ∈ Finset.range (i+1), |R - ‖ν h - 1‖|) *
        ∏ h ∈ Finset.range i, (1 + ‖ν h‖) := by
    rw [hP]
    refine le_trans (l1_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
    refine le_trans (l1_C_mul_le _ _) ?_
    refine mul_le_mul (hbnd i (Finset.mem_range.mp hi)) (l1_prod_X_sub_C_le ν i)
      (l1_nonneg _) ?_
    exact div_nonneg hR0.le (mul_nonneg (pow_nonneg h1R.le _)
      (Finset.prod_nonneg fun _ _ => abs_nonneg _))
  exact ⟨P, hPdeg, hval, hl1⟩

end Contour

/-! ### Endgame numerics -/

section Endgame

/-- `(1 + x/(m+1))^(m+1) ≤ exp x` for `x ≥ 0`. -/
lemma one_add_div_pow_le_exp {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    (1 + x / ((m : ℝ) + 1)) ^ (m + 1) ≤ Real.exp x := by
  have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have h2 : 1 + x / ((m : ℝ) + 1) ≤ Real.exp (x / ((m : ℝ) + 1)) := by
    have := Real.add_one_le_exp (x / ((m : ℝ) + 1))
    linarith
  have h3 : (0 : ℝ) ≤ 1 + x / ((m : ℝ) + 1) := by positivity
  calc (1 + x / ((m : ℝ) + 1)) ^ (m + 1)
      ≤ (Real.exp (x / ((m : ℝ) + 1))) ^ (m + 1) := pow_le_pow_left₀ h3 h2 _
    _ = Real.exp x := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        field_simp

/-- The endgame estimate: with `δ = (N−1)/(M+N)`,
`(32/7)·((M+N)/(M+1))^{M+1}·(8/δ)^{N−1}·(N/(8e(M+N)))^N ≤ 4/7`. -/
lemma endgame_bound (M N : ℕ) (hN2 : 2 ≤ N) :
    (32/7 : ℝ) * (((M : ℝ) + N) / ((M : ℝ) + 1)) ^ (M + 1)
      * (8 / (((N : ℝ) - 1) / ((M : ℝ) + N))) ^ (N - 1)
      * ((N : ℝ) / (8 * Real.exp 1 * ((M : ℝ) + N))) ^ N ≤ 4/7 := by
  have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hn1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hMN : (0 : ℝ) < (M : ℝ) + N := by linarith
  have hM1 : (0 : ℝ) < (M : ℝ) + 1 := by linarith
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hK : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  -- Step 1: `((M+N)/(M+1))^(M+1) ≤ exp (N−1)`
  have h1 : (((M : ℝ) + N) / ((M : ℝ) + 1)) ^ (M + 1) ≤ Real.exp ((N : ℝ) - 1) := by
    have harg : ((M : ℝ) + N) / ((M : ℝ) + 1) = 1 + ((N : ℝ) - 1) / ((M : ℝ) + 1) := by
      field_simp
      ring
    rw [harg]
    exact one_add_div_pow_le_exp (by linarith) M
  -- Step 2: `(N/(N−1))^(N−1) ≤ e`
  have hpow1 : ((N : ℝ) / ((N : ℝ) - 1)) ^ (N - 1) ≤ Real.exp 1 := by
    have hNn1 : (N : ℝ) / ((N : ℝ) - 1) = 1 + 1 / ((N : ℝ) - 1) := by
      field_simp
      ring
    have h2 : 1 + 1 / ((N : ℝ) - 1) ≤ Real.exp (1 / ((N : ℝ) - 1)) := by
      have := Real.add_one_le_exp (1 / ((N : ℝ) - 1))
      linarith
    rw [hNn1]
    calc (1 + 1 / ((N : ℝ) - 1)) ^ (N - 1)
        ≤ (Real.exp (1 / ((N : ℝ) - 1))) ^ (N - 1) :=
          pow_le_pow_left₀ (by positivity) h2 _
      _ = Real.exp (((N - 1 : ℕ) : ℝ) * (1 / ((N : ℝ) - 1))) := (Real.exp_nat_mul _ _).symm
      _ = Real.exp 1 := by
          rw [hK]
          congr 1
          field_simp
  -- Step 3: combine the two `(N−1)`-power blocks
  have hcombo : (8 / (((N : ℝ) - 1) / ((M : ℝ) + N)))
      * ((N : ℝ) / (8 * Real.exp 1 * ((M : ℝ) + N)))
      = (N : ℝ) / (Real.exp 1 * ((N : ℝ) - 1)) := by
    field_simp
  have hexpK : Real.exp ((N : ℝ) - 1) = Real.exp 1 ^ (N - 1) := by
    rw [← Real.exp_nat_mul, hK, mul_one]
  have hsplitmid : ((N : ℝ) / (Real.exp 1 * ((N : ℝ) - 1))) ^ (N - 1)
      = ((N : ℝ) / ((N : ℝ) - 1)) ^ (N - 1) * (Real.exp 1 ^ (N - 1))⁻¹ := by
    rw [show (N : ℝ) / (Real.exp 1 * ((N : ℝ) - 1))
        = ((N : ℝ) / ((N : ℝ) - 1)) / Real.exp 1 by field_simp]
    rw [div_pow, div_eq_mul_inv]
  have hmid : ((N : ℝ) / (Real.exp 1 * ((N : ℝ) - 1))) ^ (N - 1) * Real.exp ((N : ℝ) - 1)
      ≤ Real.exp 1 := by
    rw [hsplitmid, hexpK]
    have hEK : (0 : ℝ) < Real.exp 1 ^ (N - 1) := by positivity
    calc ((N : ℝ) / ((N : ℝ) - 1)) ^ (N - 1) * (Real.exp 1 ^ (N - 1))⁻¹ * Real.exp 1 ^ (N - 1)
        = ((N : ℝ) / ((N : ℝ) - 1)) ^ (N - 1) := by
          rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hEK), mul_one]
      _ ≤ Real.exp 1 := hpow1
  -- Step 4: assemble
  set c : ℝ := (N : ℝ) / (8 * Real.exp 1 * ((M : ℝ) + N)) with hc
  set B : ℝ := 8 / (((N : ℝ) - 1) / ((M : ℝ) + N)) with hB
  set A : ℝ := (((M : ℝ) + N) / ((M : ℝ) + 1)) ^ (M + 1) with hA
  have hc0 : 0 < c := by rw [hc]; positivity
  have hB0 : 0 < B := by
    rw [hB]
    exact div_pos (by norm_num) (div_pos hn1 hMN)
  have hA0 : 0 < A := by rw [hA]; positivity
  have hcsplit : c ^ N = c * c ^ (N - 1) := by
    conv_lhs => rw [show N = 1 + (N - 1) by omega]
    rw [pow_add, pow_one]
  have hBc : B * c = (N : ℝ) / (Real.exp 1 * ((N : ℝ) - 1)) := hcombo
  have hre : (32/7 : ℝ) * A * B ^ (N - 1) * c ^ N
      = (32/7) * c * (((B * c) ^ (N - 1)) * A) := by
    rw [hcsplit, mul_pow]
    ring
  rw [hre, hBc]
  have hstep1 : ((N : ℝ) / (Real.exp 1 * ((N : ℝ) - 1))) ^ (N - 1) * A
      ≤ ((N : ℝ) / (Real.exp 1 * ((N : ℝ) - 1))) ^ (N - 1) * Real.exp ((N : ℝ) - 1) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have hstep2 : (32/7 : ℝ) * c * (((N : ℝ) / (Real.exp 1 * ((N : ℝ) - 1))) ^ (N - 1) * A)
      ≤ (32/7) * c * Real.exp 1 := by
    refine mul_le_mul_of_nonneg_left (le_trans hstep1 hmid) ?_
    positivity
  refine le_trans hstep2 ?_
  -- `(32/7)·(N/(8e(M+N)))·e = (4N)/(7(M+N)) ≤ 4/7`
  have hfin : (32/7 : ℝ) * c * Real.exp 1 = 4 * (N : ℝ) / (7 * ((M : ℝ) + N)) := by
    rw [hc]
    field_simp
    ring
  rw [hfin]
  have h9 : (4 : ℝ) * (N : ℝ) / (7 * ((M : ℝ) + N)) = 4/7 * ((N : ℝ) / ((M : ℝ) + N)) := by
    field_simp
  have h10 : (N : ℝ) / ((M : ℝ) + N) ≤ 1 := by
    rw [div_le_one hMN]; linarith
  calc (4 : ℝ) * (N : ℝ) / (7 * ((M : ℝ) + N))
      = 4/7 * ((N : ℝ) / ((M : ℝ) + N)) := h9
    _ ≤ 4/7 * 1 := mul_le_mul_of_nonneg_left h10 (by norm_num)
    _ = 4/7 := mul_one _

end Endgame

/-! ### The core normalised theorem -/

section Core

open Metric

/-- Core of the second main theorem: the family is normalised so that the
designated entry is `1` and every entry has modulus at most `1`. -/
theorem core_norm_bound (M N : ℕ) (hN2 : 2 ≤ N) (hN0 : 0 < N) (z : Fin N → ℂ)
    (h0 : z ⟨0, hN0⟩ = 1) (hle : ∀ j, ‖z j‖ ≤ 1) :
    ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (8 * Real.exp 1 * (M + N))) ^ N ≤ ‖∑ j, z j ^ k‖ := by
  classical
  set cN : ℝ := ((N : ℝ) / (8 * Real.exp 1 * (M + N))) ^ N with hcN
  have hN2R : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hMN : (0 : ℝ) < (M : ℝ) + N := by linarith
  -- the window scale
  set δ : ℝ := ((N : ℝ) - 1) / ((M : ℝ) + N) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact div_pos (by linarith) hMN
  have hδ1 : δ < 1 := by
    rw [hδdef, div_lt_one hMN]
    linarith
  -- Chebyshev radius against the unsorted distance data
  set d' : ℕ → ℝ := fun h => if hh : h < N then ‖z ⟨h, hh⟩ - 1‖ else 0 with hd'
  obtain ⟨R, hRmem, hRprod⟩ := exists_cheb_radius (by omega : 1 ≤ N) d' hδ0
  have hRδ : R ≤ δ := hRmem.2
  have hRnn : 0 ≤ R := hRmem.1
  have hprodpos' : (0 : ℝ) < ∏ h ∈ Finset.range N, |R - d' h| :=
    lt_of_lt_of_le (by positivity) hRprod
  have hfac' : ∀ h, h < N → (0 : ℝ) < |R - d' h| := by
    intro h hh
    rcases (abs_nonneg (R - d' h)).lt_or_eq with hpos | heq
    · exact hpos
    · exfalso
      have h00 : |R - d' h| = 0 := heq.symm
      have hz := Finset.prod_eq_zero (f := fun h => |R - d' h|)
        (Finset.mem_range.mpr hh) h00
      rw [hz] at hprodpos'
      exact lt_irrefl _ hprodpos'
  have hR0 : 0 < R := by
    rcases hRnn.lt_or_eq with h | h
    · exact h
    · exfalso
      have hd0 : d' 0 = 0 := by
        simp only [hd']
        rw [dif_pos hN0, h0, sub_self, norm_zero]
      have := hfac' 0 hN0
      rw [hd0, ← h, sub_zero, abs_zero] at this
      exact lt_irrefl _ this
  have hR1 : R < 1 := lt_of_le_of_lt hRδ hδ1
  -- sort the nodes by decreasing distance-to-the-circle
  obtain ⟨σ, hσmono⟩ : ∃ σ : Equiv.Perm (Fin N),
      Monotone ((fun j => -|R - ‖z j - 1‖|) ∘ σ) :=
    ⟨Tuple.sort _, Tuple.monotone_sort _⟩
  set ν : ℕ → ℂ := fun h => if hh : h < N then z (σ ⟨h, hh⟩) else 0 with hν
  have hνval : ∀ j : Fin N, ν (j : ℕ) = z (σ j) := by
    intro j
    rw [hν]
    simp only
    rw [dif_pos j.isLt, Fin.eta]
  have hd'j : ∀ j : Fin N, d' (j : ℕ) = ‖z j - 1‖ := by
    intro j
    rw [hd']
    simp only
    rw [dif_pos j.isLt, Fin.eta]
  -- transport the Chebyshev product to the sorted enumeration
  have htrans : ∏ h ∈ Finset.range N, |R - ‖ν h - 1‖|
      = ∏ h ∈ Finset.range N, |R - d' h| := by
    calc ∏ h ∈ Finset.range N, |R - ‖ν h - 1‖|
        = ∏ j : Fin N, |R - ‖ν (j : ℕ) - 1‖| :=
          (Fin.prod_univ_eq_prod_range (fun h => |R - ‖ν h - 1‖|) N).symm
      _ = ∏ j : Fin N, |R - ‖z (σ j) - 1‖| :=
          Finset.prod_congr rfl fun j _ => by rw [hνval j]
      _ = ∏ j : Fin N, |R - ‖z j - 1‖| :=
          Equiv.prod_comp σ (fun j => |R - ‖z j - 1‖|)
      _ = ∏ j : Fin N, |R - d' (j : ℕ)| :=
          Finset.prod_congr rfl fun j _ => by rw [hd'j j]
      _ = ∏ h ∈ Finset.range N, |R - d' h| :=
          Fin.prod_univ_eq_prod_range (fun h => |R - d' h|) N
  have hwfull : 2 * (δ/4) ^ N ≤ ∏ h ∈ Finset.range N, |R - ‖ν h - 1‖| := by
    rw [htrans]; exact hRprod
  have hwprodpos : (0 : ℝ) < ∏ h ∈ Finset.range N, |R - ‖ν h - 1‖| :=
    lt_of_lt_of_le (by positivity) hwfull
  have hwpos : ∀ h, h < N → (0 : ℝ) < |R - ‖ν h - 1‖| := by
    intro h hh
    rcases (abs_nonneg (R - ‖ν h - 1‖)).lt_or_eq with hpos | heq
    · exact hpos
    · exfalso
      have h00 : |R - ‖ν h - 1‖| = 0 := heq.symm
      have hz := Finset.prod_eq_zero (f := fun h => |R - ‖ν h - 1‖|)
        (Finset.mem_range.mpr hh) h00
      rw [hz] at hwprodpos
      exact lt_irrefl _ hwprodpos
  have hwanti : ∀ h h', h ≤ h' → h' < N → |R - ‖ν h' - 1‖| ≤ |R - ‖ν h - 1‖| := by
    intro h h' hhh hh'
    have hh : h < N := lt_of_le_of_lt hhh hh'
    have hmk : (⟨h, hh⟩ : Fin N) ≤ ⟨h', hh'⟩ := by
      rw [Fin.mk_le_mk]; exact hhh
    have hmono := hσmono hmk
    simp only [Function.comp_apply] at hmono
    have e1 : ν h = z (σ ⟨h, hh⟩) := by rw [hν]; simp only; rw [dif_pos hh]
    have e2 : ν h' = z (σ ⟨h', hh'⟩) := by rw [hν]; simp only; rw [dif_pos hh']
    rw [e1, e2]
    linarith
  -- no node sits on the circle
  have hoff : ∀ h, h < N → ‖ν h - 1‖ ≠ R := by
    intro h hh hEq
    have := hwpos h hh
    rw [hEq, sub_self, abs_zero] at this
    exact lt_irrefl _ this
  -- sorted prefix products beat `(δ/4)^{i+1}`
  have hprefix : ∀ i, i < N →
      (δ/4) ^ (i+1) ≤ ∏ h ∈ Finset.range (i+1), |R - ‖ν h - 1‖| := by
    intro i hiN
    have hkey := prod_range_pow_le_prod_prefix_pow (fun h => |R - ‖ν h - 1‖|)
      hwpos hwanti (Nat.succ_le_of_lt hiN)
    have h1 : (((δ/4 : ℝ)) ^ (i+1)) ^ N
        ≤ (∏ h ∈ Finset.range (i+1), |R - ‖ν h - 1‖|) ^ N := by
      calc (((δ/4 : ℝ)) ^ (i+1)) ^ N = (((δ/4 : ℝ)) ^ N) ^ (i+1) := by
            rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ ≤ (∏ h ∈ Finset.range N, |R - ‖ν h - 1‖|) ^ (i+1) := by
            refine pow_le_pow_left₀ (by positivity) ?_ _
            have hnn : (0:ℝ) ≤ (δ/4) ^ N := by positivity
            linarith [hwfull]
        _ ≤ (∏ h ∈ Finset.range (i+1), |R - ‖ν h - 1‖|) ^ N := hkey
    exact le_of_pow_le_pow_left₀ (by omega) (Finset.prod_nonneg fun _ _ => abs_nonneg _) h1
  -- the interpolant
  obtain ⟨P, hPdeg, hPval, hPl1⟩ := exists_window_interpolant M N hN0 ν hR0 hR1 hoff
  -- geometric sum bound
  have hq8 : (8 : ℝ) ≤ 8 / δ := by
    rw [le_div_iff₀ hδ0]
    nlinarith [hδ1]
  have hgeom : ∑ i ∈ Finset.range N, ((8:ℝ)/δ) ^ i ≤ (8/7) * ((8:ℝ)/δ) ^ (N-1) := by
    set q : ℝ := 8/δ with hqdef
    have hq1 : (1:ℝ) < q := by linarith
    have hqN : q ^ N = q ^ (N-1) * q := by
      rw [← pow_succ]
      congr 1
      omega
    have hsum : ∑ i ∈ Finset.range N, q ^ i = (q ^ N - 1) / (q - 1) := by
      rw [eq_div_iff (by linarith : q - 1 ≠ 0)]
      exact geom_sum_mul q N
    rw [hsum, div_le_iff₀ (by linarith)]
    have h87 : q ≤ (8/7) * (q - 1) := by linarith
    have hqpow : (0:ℝ) ≤ q ^ (N-1) := by positivity
    calc q ^ N - 1 ≤ q ^ N := by linarith
      _ = q ^ (N-1) * q := hqN
      _ ≤ q ^ (N-1) * ((8/7) * (q - 1)) := mul_le_mul_of_nonneg_left h87 hqpow
      _ = 8/7 * q ^ (N-1) * (q - 1) := by ring
  -- fold the interpolant bound into the closed form
  have h1δ : (1:ℝ) - δ = ((M:ℝ) + 1) / ((M:ℝ) + N) := by
    rw [hδdef]
    field_simp
    ring
  have h1δ0 : (0:ℝ) < 1 - δ := by linarith
  have hinv : (((1:ℝ) - δ) ^ (M+1))⁻¹ = (((M:ℝ) + N) / ((M:ℝ) + 1)) ^ (M+1) := by
    rw [h1δ, ← inv_pow, inv_div]
  have hchain : l1 P ≤ (32/7) * (((M:ℝ) + N) / ((M:ℝ) + 1)) ^ (M+1) * ((8:ℝ)/δ) ^ (N-1) := by
    refine le_trans hPl1 ?_
    have hstep : ∀ i ∈ Finset.range N,
        R / ((1-R) ^ (M+1) * ∏ h ∈ Finset.range (i+1), |R - ‖ν h - 1‖|) *
          ∏ h ∈ Finset.range i, (1 + ‖ν h‖)
        ≤ (((1:ℝ)-δ) ^ (M+1))⁻¹ * (4 * ((8:ℝ)/δ) ^ i) := by
      intro i hi
      have hiN := Finset.mem_range.mp hi
      have hpre := hprefix i hiN
      have hd1 : (0:ℝ) < (1-δ) ^ (M+1) := by positivity
      have hd2 : (0:ℝ) < (δ/4) ^ (i+1) := by positivity
      have hdenle : (1-δ) ^ (M+1) * (δ/4) ^ (i+1)
          ≤ (1-R) ^ (M+1) * ∏ h ∈ Finset.range (i+1), |R - ‖ν h - 1‖| := by
        refine mul_le_mul (pow_le_pow_left₀ h1δ0.le (by linarith) _) hpre hd2.le ?_
        positivity
      have hmass : ∏ h ∈ Finset.range i, (1 + ‖ν h‖) ≤ 2 ^ i := by
        calc ∏ h ∈ Finset.range i, (1 + ‖ν h‖) ≤ ∏ _h ∈ Finset.range i, 2 := by
              refine Finset.prod_le_prod (fun _ _ => by positivity) ?_
              intro h hh
              have hhN : h < N := lt_trans (Finset.mem_range.mp hh) hiN
              have hν1 : ‖ν h‖ ≤ 1 := by
                rw [hν]
                simp only
                rw [dif_pos hhN]
                exact hle _
              linarith
          _ = 2 ^ i := by rw [Finset.prod_const, Finset.card_range]
      have hdiv : R / ((1-R) ^ (M+1) * ∏ h ∈ Finset.range (i+1), |R - ‖ν h - 1‖|)
          ≤ δ / ((1-δ) ^ (M+1) * (δ/4) ^ (i+1)) :=
        div_le_div₀ hδ0.le hRδ (mul_pos hd1 hd2) hdenle
      have hcomb : R / ((1-R) ^ (M+1) * ∏ h ∈ Finset.range (i+1), |R - ‖ν h - 1‖|) *
            ∏ h ∈ Finset.range i, (1 + ‖ν h‖)
          ≤ δ / ((1-δ) ^ (M+1) * (δ/4) ^ (i+1)) * 2 ^ i := by
        refine mul_le_mul hdiv hmass (Finset.prod_nonneg fun _ _ => by positivity) ?_
        positivity
      refine le_trans hcomb (le_of_eq ?_)
      have e1 : (((δ/4 : ℝ)) ^ (i+1))⁻¹ = ((4:ℝ)/δ) ^ (i+1) := by
        rw [← inv_pow, inv_div]
      have e4 : δ * ((4:ℝ)/δ) = 4 := by field_simp
      have e5 : ((4:ℝ)/δ) * 2 = 8/δ := by
        rw [div_mul_eq_mul_div]
        norm_num
      have e2 : δ * ((4:ℝ)/δ) ^ (i+1) * (2:ℝ) ^ i = 4 * ((8:ℝ)/δ) ^ i := by
        rw [pow_succ]
        calc δ * (((4:ℝ)/δ) ^ i * (4/δ)) * 2 ^ i
            = (δ * ((4:ℝ)/δ)) * (((4:ℝ)/δ) * 2) ^ i := by rw [mul_pow]; ring
          _ = 4 * ((8:ℝ)/δ) ^ i := by rw [e4, e5]
      rw [div_eq_mul_inv, mul_inv, e1]
      calc δ * ((((1:ℝ)-δ) ^ (M+1))⁻¹ * ((4:ℝ)/δ) ^ (i+1)) * 2 ^ i
          = (((1:ℝ)-δ) ^ (M+1))⁻¹ * (δ * ((4:ℝ)/δ) ^ (i+1) * 2 ^ i) := by ring
        _ = (((1:ℝ)-δ) ^ (M+1))⁻¹ * (4 * ((8:ℝ)/δ) ^ i) := by rw [e2]
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    have h4sum : ∑ i ∈ Finset.range N, 4 * ((8:ℝ)/δ) ^ i ≤ (32/7) * ((8:ℝ)/δ) ^ (N-1) := by
      rw [← Finset.mul_sum]
      calc 4 * ∑ i ∈ Finset.range N, ((8:ℝ)/δ) ^ i
          ≤ 4 * ((8/7) * ((8:ℝ)/δ) ^ (N-1)) := by
            refine mul_le_mul_of_nonneg_left hgeom (by norm_num)
        _ = (32/7) * ((8:ℝ)/δ) ^ (N-1) := by ring
    calc (((1:ℝ)-δ) ^ (M+1))⁻¹ * ∑ i ∈ Finset.range N, 4 * ((8:ℝ)/δ) ^ i
        ≤ (((1:ℝ)-δ) ^ (M+1))⁻¹ * ((32/7) * ((8:ℝ)/δ) ^ (N-1)) := by
          refine mul_le_mul_of_nonneg_left h4sum (by positivity)
      _ = (32/7) * (((1:ℝ)-δ) ^ (M+1))⁻¹ * ((8:ℝ)/δ) ^ (N-1) := by ring
      _ = (32/7) * (((M:ℝ) + N) / ((M:ℝ) + 1)) ^ (M+1) * ((8:ℝ)/δ) ^ (N-1) := by
          rw [hinv]
  -- suppose every window power sum is small
  by_contra hcon
  have hall : ∀ k, M + 1 ≤ k → k ≤ M + N → ‖∑ j, z j ^ k‖ ≤ cN := by
    intro k h1 h2
    by_contra h3
    exact hcon ⟨k, h1, h2, (not_le.mp h3).le⟩
  -- the window polynomial
  set T : ℂ[X] := P * Polynomial.X ^ (M+1) with hT
  have hTdeg : T.natDegree < M + N + 1 := by
    have h1 : T.natDegree ≤ P.natDegree + (M+1) := by
      rw [hT]
      refine le_trans Polynomial.natDegree_mul_le ?_
      rw [Polynomial.natDegree_X_pow]
    omega
  have hTcoeff : ∀ k, T.coeff k = if M+1 ≤ k then P.coeff (k - (M+1)) else 0 := by
    intro k
    rw [hT, Polynomial.coeff_mul_X_pow']
  have hTeval : ∀ x : ℂ, T.eval x = P.eval x * x ^ (M+1) := by
    intro x
    rw [hT, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  -- the value sum counts the inside nodes
  have hvalsum : ∑ j, T.eval (z j)
      = (((Finset.range N).filter (fun h => ‖ν h - 1‖ < R)).card : ℂ) := by
    have h1 : ∑ j, T.eval (z j) = ∑ j : Fin N, T.eval (z (σ j)) :=
      (Equiv.sum_comp σ (fun j => T.eval (z j))).symm
    have h2 : ∑ j : Fin N, T.eval (z (σ j)) = ∑ h ∈ Finset.range N, T.eval (ν h) := by
      rw [← Fin.sum_univ_eq_sum_range (fun h => T.eval (ν h)) N]
      exact Finset.sum_congr rfl fun j _ => by rw [hνval j]
    have h3 : ∀ h ∈ Finset.range N, T.eval (ν h) = if ‖ν h - 1‖ < R then 1 else 0 := by
      intro h hh
      have hhN := Finset.mem_range.mp hh
      rw [hTeval, hPval h hhN]
      by_cases hcase : ‖ν h - 1‖ < R
      · rw [if_pos hcase, if_pos hcase]
        have hν0 : ν h ≠ 0 := by
          intro h00
          rw [h00, zero_sub, norm_neg, norm_one] at hcase
          linarith
        rw [inv_mul_cancel₀ (pow_ne_zero _ hν0)]
      · rw [if_neg hcase, if_neg hcase, zero_mul]
    rw [h1, h2, Finset.sum_congr rfl h3, Finset.sum_boole]
  have hcard1 : 1 ≤ ((Finset.range N).filter (fun h => ‖ν h - 1‖ < R)).card := by
    refine Finset.card_pos.mpr ?_
    refine ⟨((σ.symm ⟨0, hN0⟩ : Fin N) : ℕ), ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (σ.symm ⟨0, hN0⟩).isLt, ?_⟩
    have hν0 : ν ((σ.symm ⟨0, hN0⟩ : Fin N) : ℕ) = 1 := by
      rw [hνval (σ.symm ⟨0, hN0⟩), Equiv.apply_symm_apply]
      exact h0
    rw [hν0, sub_self, norm_zero]
    exact hR0
  -- pair coefficients against window power sums
  have hpair : ∑ j, T.eval (z j)
      = ∑ k ∈ Finset.Ico (M+1) (M+N+1), T.coeff k * ∑ j, z j ^ k := by
    have h1 : ∑ j, T.eval (z j)
        = ∑ j, ∑ k ∈ Finset.range (M+N+1), T.coeff k * z j ^ k :=
      Finset.sum_congr rfl fun j _ => Polynomial.eval_eq_sum_range' hTdeg (z j)
    rw [h1, Finset.sum_comm]
    have h2 : ∀ k ∈ Finset.range (M+N+1),
        ∑ j, T.coeff k * z j ^ k = T.coeff k * ∑ j, z j ^ k := fun k _ => by
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl h2, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le (M+1)) (by omega : M+1 ≤ M+N+1)]
    have hlow : ∑ k ∈ Finset.Ico 0 (M+1), T.coeff k * ∑ j, z j ^ k = 0 := by
      refine Finset.sum_eq_zero fun k hk => ?_
      have hk2 := (Finset.mem_Ico.mp hk).2
      rw [hTcoeff k, if_neg (by omega), zero_mul]
    rw [hlow, zero_add]
  -- the norm chain
  have hnorm1 : (1:ℝ) ≤ ‖∑ j, T.eval (z j)‖ := by
    rw [hvalsum, Complex.norm_natCast]
    exact_mod_cast hcard1
  have hcN0 : (0:ℝ) ≤ cN := by rw [hcN]; positivity
  have hnorm2 : ‖∑ j, T.eval (z j)‖ ≤ l1 P * cN := by
    rw [hpair]
    refine le_trans (norm_sum_le _ _) ?_
    have hterm2 : ∀ k ∈ Finset.Ico (M+1) (M+N+1),
        ‖T.coeff k * ∑ j, z j ^ k‖ ≤ ‖T.coeff k‖ * cN := by
      intro k hk
      have hk' := Finset.mem_Ico.mp hk
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hall k hk'.1 (by omega)) (norm_nonneg _)
    refine le_trans (Finset.sum_le_sum hterm2) ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ hcN0
    have hre : ∑ k ∈ Finset.Ico (M+1) (M+N+1), ‖T.coeff k‖
        = ∑ r ∈ Finset.range N, ‖P.coeff r‖ := by
      rw [Finset.sum_Ico_eq_sum_range]
      have hNN : M + N + 1 - (M + 1) = N := by omega
      rw [hNN]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hTcoeff, if_pos (by omega)]
      have hidx : M + 1 + r - (M + 1) = r := by omega
      rw [hidx]
    rw [hre, ← l1_eq_sum_range hPdeg]
  -- numeric contradiction
  have hfinal : l1 P * cN ≤ 4/7 := by
    calc l1 P * cN
        ≤ ((32/7) * (((M:ℝ) + N) / ((M:ℝ) + 1)) ^ (M+1) * ((8:ℝ)/δ) ^ (N-1)) * cN :=
          mul_le_mul_of_nonneg_right hchain hcN0
      _ ≤ 4/7 := by
          rw [hcN, hδdef]
          exact endgame_bound M N hN2
  have : (1:ℝ) ≤ 4/7 := le_trans hnorm1 (le_trans hnorm2 hfinal)
  norm_num at this

end Core

/-! ### The frozen deliverables (Z7-tzlite §1.1) -/

/-- **Turán's second main theorem, lossy form**: among the exponents
`k ∈ [M+1, M+N]` some power sum is at least `(N/(8e(M+N)))^N` times the
`k`-th power of the LARGEST modulus. -/
theorem turan_power_sum_max {N : ℕ} (hN : 1 ≤ N) (M : ℕ) (z : Fin N → ℂ)
    (hmax : ∀ j, ‖z j‖ ≤ ‖z ⟨0, hN⟩‖) :
    ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (8 * Real.exp 1 * (M + N))) ^ N * ‖z ⟨0, hN⟩‖ ^ k
        ≤ ‖∑ j, z j ^ k‖ := by
  rcases eq_or_ne (z ⟨0, hN⟩) 0 with h00 | h00
  · -- the designated entry vanishes: the bound is trivial
    refine ⟨M + 1, le_rfl, by omega, ?_⟩
    rw [h00, norm_zero, zero_pow (by omega : M + 1 ≠ 0), mul_zero]
    exact norm_nonneg _
  · have hz0pos : 0 < ‖z ⟨0, hN⟩‖ := norm_pos_iff.mpr h00
    rcases Nat.lt_or_ge N 2 with hN1 | hN2
    · -- `N = 1`
      have hN1' : N = 1 := by omega
      subst hN1'
      refine ⟨M + 1, le_rfl, by omega, ?_⟩
      have hz : ∑ j, z j ^ (M + 1) = z ⟨0, hN⟩ ^ (M + 1) := by
        rw [Fin.sum_univ_one]
        congr 1
      rw [hz, norm_pow, pow_one]
      have he2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp 1
        linarith
      have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      refine mul_le_of_le_one_left (by positivity) ?_
      push_cast
      rw [div_le_one (by nlinarith)]
      nlinarith
    · -- `N ≥ 2`: normalise and invoke the core theorem
      have hN0 : 0 < N := by omega
      set w : Fin N → ℂ := fun j => z j / z ⟨0, hN⟩ with hw
      have hw0 : w ⟨0, hN0⟩ = 1 := by
        rw [hw]
        simp only
        exact div_self h00
      have hwle : ∀ j, ‖w j‖ ≤ 1 := by
        intro j
        rw [hw]
        simp only [norm_div]
        rw [div_le_one hz0pos]
        exact hmax j
      obtain ⟨k, hk1, hk2, hk3⟩ := core_norm_bound M N hN2 hN0 w hw0 hwle
      refine ⟨k, hk1, hk2, ?_⟩
      have hsum : ∑ j, w j ^ k = (∑ j, z j ^ k) / (z ⟨0, hN⟩) ^ k := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hw]
        simp only
        rw [div_pow]
      rw [hsum, norm_div, norm_pow] at hk3
      rw [le_div_iff₀ (pow_pos hz0pos k)] at hk3
      exact hk3

/-- **Turán's second main theorem against any lower bound `t` on the largest
modulus.** -/
theorem turan_power_sum_max_lb {N : ℕ} (hN : 1 ≤ N) (M : ℕ) (z : Fin N → ℂ)
    {t : ℝ} (ht0 : 0 ≤ t) (hmax : ∀ j, ‖z j‖ ≤ ‖z ⟨0, hN⟩‖)
    (ht : t ≤ ‖z ⟨0, hN⟩‖) :
    ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧
      ((N : ℝ) / (8 * Real.exp 1 * (M + N))) ^ N * t ^ k
        ≤ ‖∑ j, z j ^ k‖ := by
  obtain ⟨k, hk1, hk2, hk3⟩ := turan_power_sum_max hN M z hmax
  refine ⟨k, hk1, hk2, le_trans ?_ hk3⟩
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact pow_le_pow_left₀ ht0 ht k

end

end Turan

end Carmichael
