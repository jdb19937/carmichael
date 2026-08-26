/-
Elementary mean-value bounds for `k^ω(d)` over squarefree `d`, used to control
sieve remainder sums:
  * `∑_{d ≤ y squarefree} k^{ω(d)} / d ≤ (1 + log y)^k`;
  * `∑_{d ≤ y squarefree} k^{ω(d)} ≤ y · (1 + log y)^{k-1}`  (for `k ≥ 1`).

Proof outline (induction on `k`):
* key identity: for squarefree `d`, `∑_{e ∣ d} x^{ω(e)} = (x + 1)^{ω(d)}`, via the
  powerset expansion of `∏_{p ∣ d} (x + 1)` over the prime factors of `d`;
* the base case `k = 0` collapses both sums to the `d = 1` term;
* the inductive step expands `k^{ω(d)} = ∑_{e ∣ d} (k-1)^{ω(e)}`, swaps the double
  sum over pairs `(e, f)` with `e·f ≤ y`, drops the squarefreeness constraint on
  `f`, and bounds the inner harmonic sum by `1 + log y`.
-/
import Mathlib

namespace Carmichael

open Finset ArithmeticFunction
open scoped ArithmeticFunction.omega

/-- `ω n` is the number of distinct prime factors of `n`. -/
private lemma omega_eq_card_primeFactors (n : ℕ) : ω n = n.primeFactors.card := by
  rw [cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]

/-- The key identity: for squarefree `d`, `∑_{e ∣ d} x^{ω(e)} = (x + 1)^{ω(d)}`. -/
private lemma sum_divisors_pow_omega {d : ℕ} (hd : Squarefree d) (x : ℝ) :
    ∑ e ∈ d.divisors, x ^ (ω e) = (x + 1) ^ (ω d) := by
  have h0 : d ≠ 0 := hd.ne_zero
  -- All divisors of a squarefree number are squarefree, so the sum over divisors
  -- is a sum over subsets of the prime factors.
  have h1 : ∑ e ∈ d.divisors, x ^ (ω e)
      = ∑ t ∈ d.primeFactors.powerset, x ^ (ω t.val.prod) := by
    rw [← Nat.divisors_filter_squarefree_of_squarefree hd,
      Nat.sum_divisors_filter_squarefree h0, Nat.factors_eq]
    rfl
  -- A subset `t` of the prime factors contributes `x ^ t.card`.
  have h2 : ∀ t ∈ d.primeFactors.powerset, x ^ (ω t.val.prod) = x ^ t.card := by
    intro t ht
    have hpr : ∀ p ∈ t, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp)
    rw [show t.val.prod = ∏ p ∈ t, p from t.prod_val, omega_eq_card_primeFactors,
      Nat.primeFactors_prod hpr]
  -- Binomial expansion over the powerset.
  have h3 : ∑ t ∈ d.primeFactors.powerset, x ^ t.card
      = (x + 1) ^ d.primeFactors.card := by
    calc ∑ t ∈ d.primeFactors.powerset, x ^ t.card
        = ∑ t ∈ d.primeFactors.powerset,
            (∏ _p ∈ t, x) * ∏ _p ∈ d.primeFactors \ t, (1 : ℝ) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [Finset.prod_const, Finset.prod_const, one_pow, mul_one]
      _ = ∏ _p ∈ d.primeFactors, (x + 1) :=
          (Finset.prod_add (fun _ => x) (fun _ => (1 : ℝ)) d.primeFactors).symm
      _ = (x + 1) ^ d.primeFactors.card := by rw [Finset.prod_const]
  rw [h1, Finset.sum_congr rfl h2, h3, omega_eq_card_primeFactors]

/-- The harmonic sum `∑_{f ≤ N} 1/f` is at most `1 + log M` whenever `1 ≤ N ≤ M`. -/
private lemma harmonic_Icc_le {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ f ∈ Icc 1 N, ((f : ℝ))⁻¹ ≤ 1 + Real.log M := by
  have h1 : ∑ f ∈ Icc 1 N, ((f : ℝ))⁻¹ = ((harmonic N : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [h1]
  calc ((harmonic N : ℚ) : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
    _ ≤ 1 + Real.log M := by
        have hpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        have hle : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
        linarith [Real.log_le_log hpos hle]

/-- **Divisor mean-value bound, weighted form**:
`∑_{d ≤ y squarefree} k^{ω(d)} / d ≤ (1 + log y)^k`. -/
theorem sum_pow_omega_div_le (k y : ℕ) (hy : 1 ≤ y) :
    ∑ d ∈ Finset.Icc 1 y, (if Squarefree d then ((k : ℝ)) ^ (ω d) / d else 0)
      ≤ (1 + Real.log y) ^ k := by
  induction k with
  | zero =>
    -- Only the `d = 1` term survives: `0^{ω(d)} = 0` for `d ≥ 2`.
    rw [pow_zero]
    have hzero : ∀ d ∈ Icc 1 y, d ≠ 1 →
        (if Squarefree d then ((0 : ℕ) : ℝ) ^ (ω d) / d else 0) = 0 := by
      intro d hd hd1
      obtain ⟨hdl, _⟩ := Finset.mem_Icc.mp hd
      by_cases hsf : Squarefree d
      · have hω : ω d ≠ 0 := (cardDistinctFactors_pos.mpr (by omega)).ne'
        rw [if_pos hsf, Nat.cast_zero, zero_pow hω, zero_div]
      · rw [if_neg hsf]
    rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_Icc.mpr ⟨le_rfl, hy⟩) hzero]
    simp
  | succ k ih =>
    have hlog : (0 : ℝ) ≤ Real.log y := Real.log_nonneg (by exact_mod_cast hy)
    -- Step 1: expand `(k+1)^{ω(d)} = ∑_{e ∣ d} k^{ω(e)}` for squarefree `d`.
    have step1 : ∑ d ∈ Icc 1 y, (if Squarefree d then ((k + 1 : ℕ) : ℝ) ^ (ω d) / d else 0)
        = ∑ d ∈ Icc 1 y, ∑ e ∈ d.divisors,
            (if Squarefree d then ((k : ℝ)) ^ (ω e) / d else 0) := by
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hsf : Squarefree d
      · simp only [if_pos hsf]
        rw [← Finset.sum_div, sum_divisors_pow_omega hsf]
        push_cast
        ring
      · simp [if_neg hsf]
    -- Step 2: swap the double sum over pairs `(e, f)` with `e·f ≤ y`.
    have step2 : ∑ d ∈ Icc 1 y, ∑ e ∈ d.divisors,
            (if Squarefree d then ((k : ℝ)) ^ (ω e) / d else 0)
        = ∑ e ∈ Icc 1 y, ∑ f ∈ Icc 1 (y / e),
            (if Squarefree (e * f) then ((k : ℝ)) ^ (ω e) / ((e : ℝ) * (f : ℝ)) else 0) := by
      rw [Finset.sum_sigma', Finset.sum_sigma']
      refine Finset.sum_nbij' (fun x => ⟨x.2, x.1 / x.2⟩) (fun z => ⟨z.1 * z.2, z.1⟩)
        ?_ ?_ ?_ ?_ ?_
      · rintro ⟨d, e⟩ hx
        simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx ⊢
        obtain ⟨⟨hd1, hdy⟩, hdvd, hd0⟩ := hx
        have he0 : 0 < e := Nat.pos_of_dvd_of_pos hdvd (by omega)
        have hed : e ≤ d := Nat.le_of_dvd (by omega) hdvd
        exact ⟨⟨he0, hed.trans hdy⟩, (Nat.one_le_div_iff he0).mpr hed, Nat.div_le_div_right hdy⟩
      · rintro ⟨e, f⟩ hz
        simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hz ⊢
        obtain ⟨⟨he1, hey⟩, hf1, hfy⟩ := hz
        have hef : e * f ≤ y := by
          have h := (Nat.le_div_iff_mul_le (by omega : 0 < e)).mp hfy
          rw [mul_comm]
          exact h
        exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hef⟩,
          dvd_mul_right e f, Nat.mul_ne_zero (by omega) (by omega)⟩
      · rintro ⟨d, e⟩ hx
        simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
        obtain ⟨⟨hd1, hdy⟩, hdvd, hd0⟩ := hx
        simp only [Nat.mul_div_cancel' hdvd]
      · rintro ⟨e, f⟩ hz
        simp only [Finset.mem_sigma, Finset.mem_Icc] at hz
        obtain ⟨⟨he1, hey⟩, hf1, hfy⟩ := hz
        simp only [Nat.mul_div_cancel_left _ (by omega : 0 < e)]
      · rintro ⟨d, e⟩ hx
        simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
        obtain ⟨⟨hd1, hdy⟩, hdvd, hd0⟩ := hx
        have heq : e * (d / e) = d := Nat.mul_div_cancel' hdvd
        have hcast : (e : ℝ) * ((d / e : ℕ) : ℝ) = (d : ℝ) := by
          rw [← Nat.cast_mul, heq]
        simp only [heq, hcast]
    -- Step 3: drop squarefreeness of `f` and bound the inner harmonic sums.
    have step3 : ∀ e ∈ Icc 1 y,
        ∑ f ∈ Icc 1 (y / e),
            (if Squarefree (e * f) then ((k : ℝ)) ^ (ω e) / ((e : ℝ) * (f : ℝ)) else 0)
          ≤ (if Squarefree e then ((k : ℝ)) ^ (ω e) / e else 0) * (1 + Real.log y) := by
      intro e he
      obtain ⟨he1, hey⟩ := Finset.mem_Icc.mp he
      by_cases hsf : Squarefree e
      · have hbound : ∀ f ∈ Icc 1 (y / e),
            (if Squarefree (e * f) then ((k : ℝ)) ^ (ω e) / ((e : ℝ) * (f : ℝ)) else 0)
              ≤ ((k : ℝ)) ^ (ω e) / e * ((f : ℝ))⁻¹ := by
          intro f hf
          obtain ⟨hf1, _⟩ := Finset.mem_Icc.mp hf
          have hterm : ((k : ℝ)) ^ (ω e) / ((e : ℝ) * (f : ℝ))
              = ((k : ℝ)) ^ (ω e) / e * ((f : ℝ))⁻¹ := by
            rw [div_mul_eq_div_div, div_eq_mul_inv (((k : ℝ)) ^ (ω e) / e)]
          split_ifs with h
          · rw [hterm]
          · positivity
        calc ∑ f ∈ Icc 1 (y / e),
              (if Squarefree (e * f) then ((k : ℝ)) ^ (ω e) / ((e : ℝ) * (f : ℝ)) else 0)
            ≤ ∑ f ∈ Icc 1 (y / e), ((k : ℝ)) ^ (ω e) / e * ((f : ℝ))⁻¹ :=
              Finset.sum_le_sum hbound
          _ = ((k : ℝ)) ^ (ω e) / e * ∑ f ∈ Icc 1 (y / e), ((f : ℝ))⁻¹ := by
              rw [Finset.mul_sum]
          _ ≤ ((k : ℝ)) ^ (ω e) / e * (1 + Real.log y) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact harmonic_Icc_le ((Nat.one_le_div_iff (by omega)).mpr hey)
                (Nat.div_le_self y e)
          _ = (if Squarefree e then ((k : ℝ)) ^ (ω e) / e else 0) * (1 + Real.log y) := by
              rw [if_pos hsf]
      · have hall : ∀ f ∈ Icc 1 (y / e),
            (if Squarefree (e * f) then ((k : ℝ)) ^ (ω e) / ((e : ℝ) * (f : ℝ)) else 0) = 0 :=
          fun f _ => if_neg fun h => hsf (h.squarefree_of_dvd (dvd_mul_right e f))
        rw [Finset.sum_eq_zero hall, if_neg hsf, zero_mul]
    -- Assemble, applying the inductive hypothesis.
    calc ∑ d ∈ Icc 1 y, (if Squarefree d then ((k + 1 : ℕ) : ℝ) ^ (ω d) / d else 0)
        = ∑ e ∈ Icc 1 y, ∑ f ∈ Icc 1 (y / e),
            (if Squarefree (e * f) then ((k : ℝ)) ^ (ω e) / ((e : ℝ) * (f : ℝ)) else 0) := by
          rw [step1, step2]
      _ ≤ ∑ e ∈ Icc 1 y,
            (if Squarefree e then ((k : ℝ)) ^ (ω e) / e else 0) * (1 + Real.log y) :=
          Finset.sum_le_sum step3
      _ = (∑ e ∈ Icc 1 y, (if Squarefree e then ((k : ℝ)) ^ (ω e) / e else 0))
            * (1 + Real.log y) := by rw [Finset.sum_mul]
      _ ≤ (1 + Real.log y) ^ k * (1 + Real.log y) :=
          mul_le_mul_of_nonneg_right ih (by linarith)
      _ = (1 + Real.log y) ^ (k + 1) := by ring

/-- **Divisor mean-value bound, unweighted form**:
`∑_{d ≤ y squarefree} k^{ω(d)} ≤ y · (1 + log y)^{k-1}` for `k ≥ 1`. -/
theorem sum_pow_omega_le (k y : ℕ) (hy : 1 ≤ y) (hk : 1 ≤ k) :
    ∑ d ∈ Finset.Icc 1 y, (if Squarefree d then ((k : ℝ)) ^ (ω d) else 0)
      ≤ (y : ℝ) * (1 + Real.log y) ^ (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  -- Step 1: expand `(j+1)^{ω(d)} = ∑_{e ∣ d} j^{ω(e)}` for squarefree `d`.
  have step1 : ∑ d ∈ Icc 1 y, (if Squarefree d then ((j + 1 : ℕ) : ℝ) ^ (ω d) else 0)
      = ∑ d ∈ Icc 1 y, ∑ e ∈ d.divisors,
          (if Squarefree d then ((j : ℝ)) ^ (ω e) else 0) := by
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hsf : Squarefree d
    · simp only [if_pos hsf]
      rw [sum_divisors_pow_omega hsf]
      push_cast
      ring
    · simp [if_neg hsf]
  -- Step 2: swap the double sum over pairs `(e, f)` with `e·f ≤ y`.
  have step2 : ∑ d ∈ Icc 1 y, ∑ e ∈ d.divisors,
          (if Squarefree d then ((j : ℝ)) ^ (ω e) else 0)
      = ∑ e ∈ Icc 1 y, ∑ f ∈ Icc 1 (y / e),
          (if Squarefree (e * f) then ((j : ℝ)) ^ (ω e) else 0) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij' (fun x => ⟨x.2, x.1 / x.2⟩) (fun z => ⟨z.1 * z.2, z.1⟩)
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨d, e⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx ⊢
      obtain ⟨⟨hd1, hdy⟩, hdvd, hd0⟩ := hx
      have he0 : 0 < e := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hed : e ≤ d := Nat.le_of_dvd (by omega) hdvd
      exact ⟨⟨he0, hed.trans hdy⟩, (Nat.one_le_div_iff he0).mpr hed, Nat.div_le_div_right hdy⟩
    · rintro ⟨e, f⟩ hz
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hz ⊢
      obtain ⟨⟨he1, hey⟩, hf1, hfy⟩ := hz
      have hef : e * f ≤ y := by
        have h := (Nat.le_div_iff_mul_le (by omega : 0 < e)).mp hfy
        rw [mul_comm]
        exact h
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hef⟩,
        dvd_mul_right e f, Nat.mul_ne_zero (by omega) (by omega)⟩
    · rintro ⟨d, e⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
      obtain ⟨⟨hd1, hdy⟩, hdvd, hd0⟩ := hx
      simp only [Nat.mul_div_cancel' hdvd]
    · rintro ⟨e, f⟩ hz
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hz
      obtain ⟨⟨he1, hey⟩, hf1, hfy⟩ := hz
      simp only [Nat.mul_div_cancel_left _ (by omega : 0 < e)]
    · rintro ⟨d, e⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
      obtain ⟨⟨hd1, hdy⟩, hdvd, hd0⟩ := hx
      have heq : e * (d / e) = d := Nat.mul_div_cancel' hdvd
      simp only [heq]
  -- Step 3: the inner sum has at most `y/e` terms, each at most `j^{ω(e)}`.
  have step3 : ∀ e ∈ Icc 1 y,
      ∑ f ∈ Icc 1 (y / e), (if Squarefree (e * f) then ((j : ℝ)) ^ (ω e) else 0)
        ≤ (y : ℝ) * (if Squarefree e then ((j : ℝ)) ^ (ω e) / e else 0) := by
    intro e he
    obtain ⟨he1, hey⟩ := Finset.mem_Icc.mp he
    by_cases hsf : Squarefree e
    · have hpow : (0 : ℝ) ≤ ((j : ℝ)) ^ (ω e) := by positivity
      have hterm : ∀ f ∈ Icc 1 (y / e),
          (if Squarefree (e * f) then ((j : ℝ)) ^ (ω e) else 0) ≤ ((j : ℝ)) ^ (ω e) := by
        intro f _
        split_ifs
        · exact le_rfl
        · exact hpow
      calc ∑ f ∈ Icc 1 (y / e), (if Squarefree (e * f) then ((j : ℝ)) ^ (ω e) else 0)
          ≤ (Icc 1 (y / e)).card • ((j : ℝ)) ^ (ω e) :=
            Finset.sum_le_card_nsmul _ _ _ hterm
        _ = ((y / e : ℕ) : ℝ) * ((j : ℝ)) ^ (ω e) := by
            rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        _ ≤ ((y : ℝ) / (e : ℝ)) * ((j : ℝ)) ^ (ω e) :=
            mul_le_mul_of_nonneg_right Nat.cast_div_le hpow
        _ = (y : ℝ) * (((j : ℝ)) ^ (ω e) / e) := by ring
        _ = (y : ℝ) * (if Squarefree e then ((j : ℝ)) ^ (ω e) / e else 0) := by
            rw [if_pos hsf]
    · have hall : ∀ f ∈ Icc 1 (y / e),
          (if Squarefree (e * f) then ((j : ℝ)) ^ (ω e) else 0) = 0 :=
        fun f _ => if_neg fun h => hsf (h.squarefree_of_dvd (dvd_mul_right e f))
      rw [Finset.sum_eq_zero hall, if_neg hsf, mul_zero]
  -- Assemble, applying the weighted bound at `j = k - 1`.
  calc ∑ d ∈ Icc 1 y, (if Squarefree d then ((j + 1 : ℕ) : ℝ) ^ (ω d) else 0)
      = ∑ e ∈ Icc 1 y, ∑ f ∈ Icc 1 (y / e),
          (if Squarefree (e * f) then ((j : ℝ)) ^ (ω e) else 0) := by rw [step1, step2]
    _ ≤ ∑ e ∈ Icc 1 y, (y : ℝ) * (if Squarefree e then ((j : ℝ)) ^ (ω e) / e else 0) :=
        Finset.sum_le_sum step3
    _ = (y : ℝ) * ∑ e ∈ Icc 1 y, (if Squarefree e then ((j : ℝ)) ^ (ω e) / e else 0) := by
        rw [Finset.mul_sum]
    _ ≤ (y : ℝ) * (1 + Real.log y) ^ j :=
        mul_le_mul_of_nonneg_left (sum_pow_omega_div_le j y hy) (by positivity)

end Carmichael
