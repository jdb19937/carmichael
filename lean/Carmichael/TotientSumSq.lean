/-
A squared variant of the totient reciprocal sum bound:
  ∑_{m ≤ M} (m/φ(m))² / m ≤ e³ · (1 + log M).

Proof outline (mirroring `Carmichael/TotientSum.lean`):
* comparison: (m/φ(m))² ≤ ∑_{d ∣ m, d squarefree} 3^{ω(d)}/φ(d), via the factor-wise
  inequality (p/(p-1))² ≤ 1 + 3/(p-1) for primes p and the powerset expansion of
  ∏_{p ∣ m} (1 + 3/(p-1));
* swap the double sum over pairs (d, k) with d·k ≤ M;
* the inner sum is a harmonic number, bounded by 1 + log M;
* the outer constant ∑_{d squarefree} 3^{ω(d)}/(d·φ(d)) is at most
  ∏_{p ≤ M} (1 + 3/(p(p-1))) ≤ exp(3·∑_{n≥2} 1/(n(n-1))) ≤ e³.
-/
import Mathlib
import Carmichael.TotientSum

namespace Carmichael

open Finset

/-- The summand `μ²(d)·3^{ω(d)}/φ(d)`: the indicator of squarefreeness times
`3` to the number of distinct prime factors, divided by the totient. -/
noncomputable def sqf3 (d : ℕ) : ℝ :=
  if Squarefree d then (3 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ) else 0

lemma sqf3_nonneg (d : ℕ) : 0 ≤ sqf3 d := by
  unfold sqf3
  split <;> positivity

/-- The key comparison: `(m/φ(m))² ≤ ∑_{d ∣ m} μ²(d)·3^{ω(d)}/φ(d)`. -/
lemma sq_le_sum_divisors_sqf3 {m : ℕ} (hm : m ≠ 0) :
    ((m : ℝ) / (Nat.totient m)) ^ 2 ≤ ∑ d ∈ m.divisors, sqf3 d := by
  have hprime : ∀ p ∈ m.primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  -- Reduce to squarefree divisors, i.e. subsets of the prime factors.
  have h1 : ∑ d ∈ m.divisors, sqf3 d
      = ∑ t ∈ m.primeFactors.powerset,
          (3 : ℝ) ^ t.val.prod.primeFactors.card / (Nat.totient t.val.prod : ℝ) := by
    simp only [sqf3]
    rw [← Finset.sum_filter, Nat.sum_divisors_filter_squarefree hm, Nat.factors_eq]
    rfl
  -- Each subset contributes a product of `3/(p-1)`.
  have h2 : ∀ t ∈ m.primeFactors.powerset,
      (3 : ℝ) ^ t.val.prod.primeFactors.card / (Nat.totient t.val.prod : ℝ)
        = ∏ p ∈ t, (3 * ((p : ℝ) - 1)⁻¹) := by
    intro t ht
    have hsub := Finset.mem_powerset.mp ht
    have hpr : ∀ p ∈ t, p.Prime := fun p hp => hprime p (hsub hp)
    rw [show t.val.prod = ∏ p ∈ t, p from t.prod_val, Nat.primeFactors_prod hpr,
      totient_prod_primes_real t hpr, div_eq_mul_inv, ← Finset.prod_inv_distrib,
      ← Finset.prod_const, ← Finset.prod_mul_distrib]
  -- Sum over the powerset is the product `∏ (3/(p-1) + 1)`.
  have h3 : ∑ t ∈ m.primeFactors.powerset, ∏ p ∈ t, (3 * ((p : ℝ) - 1)⁻¹)
      = ∏ p ∈ m.primeFactors, (3 * ((p : ℝ) - 1)⁻¹ + 1) := by
    rw [Finset.prod_add]
    exact Finset.sum_congr rfl fun t _ => by simp
  have hpos : ∀ p ∈ m.primeFactors, (0 : ℝ) < (p : ℝ) - 1 := by
    intro p hp
    have h2le : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hprime p hp).two_le
    linarith
  have hφ : (0 : ℝ) < (Nat.totient m : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)
  have hprodpos : (0 : ℝ) < ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) :=
    Finset.prod_pos hpos
  -- Euler's product formula, cast to the reals.
  have hsubcast : ((∏ p ∈ m.primeFactors, (p - 1) : ℕ) : ℝ)
      = ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl fun p hp => by
      rw [Nat.cast_sub (hprime p hp).one_lt.le, Nat.cast_one]
  have hcast : (Nat.totient m : ℝ) * ∏ p ∈ m.primeFactors, (p : ℝ)
      = (m : ℝ) * ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.totient_mul_prod_primeFactors m)
    simp only [Nat.cast_mul] at h
    rw [hsubcast] at h
    rw [Nat.cast_prod] at h
    exact h
  -- The left side as a product over the prime factors.
  have hL : (m : ℝ) / (Nat.totient m : ℝ)
      = ∏ p ∈ m.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
    rw [Finset.prod_div_distrib, div_eq_div_iff hφ.ne' hprodpos.ne']
    linear_combination -hcast
  -- Compare factor by factor.
  calc ((m : ℝ) / (Nat.totient m)) ^ 2
      = ∏ p ∈ m.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 := by
        rw [hL, Finset.prod_pow]
    _ ≤ ∏ p ∈ m.primeFactors, (3 * ((p : ℝ) - 1)⁻¹ + 1) := by
        refine Finset.prod_le_prod (fun p hp => by positivity) (fun p hp => ?_)
        have h2le : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hprime p hp).two_le
        have hx0 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        have hrw : 3 * ((p : ℝ) - 1)⁻¹ + 1 = ((p : ℝ) + 2) / ((p : ℝ) - 1) := by
          rw [eq_div_iff hx0.ne', add_mul, one_mul, mul_assoc, inv_mul_cancel₀ hx0.ne']
          ring
        rw [hrw, div_pow, div_le_div_iff₀ (by positivity) hx0]
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1)
          (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2)]
    _ = ∑ d ∈ m.divisors, sqf3 d := by
        rw [h1, Finset.sum_congr rfl h2, h3]

/-- The constant sum: `∑_{d ≤ M} μ²(d)·3^{ω(d)}/(d·φ(d)) ≤ e³`. -/
lemma sum_sqf3_div_le (M : ℕ) :
    ∑ d ∈ Icc 1 M, sqf3 d / (d : ℝ) ≤ Real.exp 3 := by
  classical
  set P : Finset ℕ := (Icc 1 M).filter Nat.Prime with hP
  -- (a) restrict to squarefree d
  have ha : ∑ d ∈ Icc 1 M, sqf3 d / (d : ℝ)
      = ∑ d ∈ (Icc 1 M).filter Squarefree,
          (3 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ) / (d : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [sqf3]
    split_ifs <;> simp
  -- (b) each squarefree term is a product over its prime factors
  have hb : ∀ d ∈ (Icc 1 M).filter Squarefree,
      (3 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ) / (d : ℝ)
        = ∏ p ∈ d.primeFactors, (3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
    intro d hd
    obtain ⟨_, hsq⟩ := Finset.mem_filter.mp hd
    have hpr : ∀ p ∈ d.primeFactors, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors hp
    have h1 : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    have h2 : ((Nat.totient d : ℕ) : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
      exact totient_prod_primes_real d.primeFactors hpr
    calc (3 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ) / (d : ℝ)
        = (3 : ℝ) ^ d.primeFactors.card * ((d : ℝ) * (Nat.totient d : ℝ))⁻¹ := by
          rw [div_div, mul_comm (Nat.totient d : ℝ) (d : ℝ), div_eq_mul_inv]
      _ = ∏ p ∈ d.primeFactors, (3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
          rw [h1, h2, ← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib,
            ← Finset.prod_const, ← Finset.prod_mul_distrib]
  -- (c) reindex by the set of prime factors
  have hinj : ∀ d₁ ∈ (Icc 1 M).filter Squarefree, ∀ d₂ ∈ (Icc 1 M).filter Squarefree,
      d₁.primeFactors = d₂.primeFactors → d₁ = d₂ := by
    intro d₁ h₁ d₂ h₂ h
    have hsq₁ := (Finset.mem_filter.mp h₁).2
    have hsq₂ := (Finset.mem_filter.mp h₂).2
    rw [← Nat.prod_primeFactors_of_squarefree hsq₁, ← Nat.prod_primeFactors_of_squarefree hsq₂, h]
  have hc : ∑ d ∈ (Icc 1 M).filter Squarefree,
        ∏ p ∈ d.primeFactors, (3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹)
      = ∑ t ∈ ((Icc 1 M).filter Squarefree).image Nat.primeFactors,
          ∏ p ∈ t, (3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
    rw [Finset.sum_image hinj]
  -- (d) the image consists of subsets of the primes up to M
  have hsubset : ((Icc 1 M).filter Squarefree).image Nat.primeFactors ⊆ P.powerset := by
    intro t ht
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hdIcc, _⟩ := Finset.mem_filter.mp hd
    obtain ⟨hd1, hdM⟩ := Finset.mem_Icc.mp hdIcc
    refine Finset.mem_powerset.mpr fun p hp => ?_
    have hppr := Nat.prime_of_mem_primeFactors hp
    have hpd : p ≤ d := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors hp)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hppr.pos, hpd.trans hdM⟩, hppr⟩
  -- nonnegativity of the subset products
  have hnonneg : ∀ t ∈ P.powerset,
      (0 : ℝ) ≤ ∏ p ∈ t, (3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
    intro t ht
    refine Finset.prod_nonneg fun p hp => ?_
    have hppr : p.Prime := (Finset.mem_filter.mp (Finset.mem_powerset.mp ht hp)).2
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hppr.two_le
    exact mul_nonneg (by norm_num)
      (inv_nonneg.mpr (mul_nonneg (by linarith) (by linarith)))
  -- (f) the powerset sum is a product
  have hf : ∑ t ∈ P.powerset, ∏ p ∈ t, (3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹)
      = ∏ p ∈ P, (3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹ + 1) := by
    rw [Finset.prod_add]
    exact (Finset.sum_congr rfl fun t _ => by simp).symm
  -- (g) bound the product by an exponential
  have hg : ∏ p ∈ P, (3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹ + 1)
      ≤ Real.exp (∑ p ∈ P, 3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => Real.add_one_le_exp _)
    have hppr : p.Prime := (Finset.mem_filter.mp hp).2
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hppr.two_le
    have := inv_nonneg.mpr (mul_nonneg (by linarith : (0 : ℝ) ≤ (p : ℝ))
      (by linarith : (0 : ℝ) ≤ (p : ℝ) - 1))
    linarith
  -- (h) the exponent is at most 3
  have hPsub : P ⊆ Icc 2 M := by
    intro p hp
    obtain ⟨hIcc, hpr⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨hpr.two_le, (Finset.mem_Icc.mp hIcc).2⟩
  have hh : ∑ p ∈ P, 3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹ ≤ 3 := by
    have hbase : ∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ ≤ 1 := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hPsub fun n hn _ => ?_)
        (sum_telescope_le M)
      have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      exact inv_nonneg.mpr (mul_nonneg (by linarith) (by linarith))
    calc ∑ p ∈ P, 3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹
        = 3 * ∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by rw [Finset.mul_sum]
      _ ≤ 3 * 1 := by linarith
      _ = 3 := by norm_num
  calc ∑ d ∈ Icc 1 M, sqf3 d / (d : ℝ)
      = ∑ d ∈ (Icc 1 M).filter Squarefree,
          (3 : ℝ) ^ d.primeFactors.card / (Nat.totient d : ℝ) / (d : ℝ) := ha
    _ = ∑ d ∈ (Icc 1 M).filter Squarefree,
          ∏ p ∈ d.primeFactors, (3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := Finset.sum_congr rfl hb
    _ = ∑ t ∈ ((Icc 1 M).filter Squarefree).image Nat.primeFactors,
          ∏ p ∈ t, (3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := hc
    _ ≤ ∑ t ∈ P.powerset, ∏ p ∈ t, (3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset fun t ht _ => hnonneg t ht
    _ = ∏ p ∈ P, (3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹ + 1) := hf
    _ ≤ Real.exp (∑ p ∈ P, 3 * ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := hg
    _ ≤ Real.exp 3 := Real.exp_le_exp.mpr hh

/-- **Squared totient ratio sum bound**:
`∑_{m ≤ M} (m/φ(m))²/m ≤ e³·(1 + log M)`. -/
theorem sum_sq_div_totient_sq_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, ((m : ℝ) / (Nat.totient m)) ^ 2 / m ≤
      Real.exp 3 * (1 + Real.log M) := by
  have hlogM : (0 : ℝ) ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  -- Step 1: bound each term via the divisor comparison.
  have step1 : ∑ m ∈ Icc 1 M, ((m : ℝ) / (Nat.totient m)) ^ 2 / m
      ≤ ∑ m ∈ Icc 1 M, ∑ d ∈ m.divisors, sqf3 d / (m : ℝ) := by
    refine Finset.sum_le_sum fun m hm => ?_
    obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
    have hm0 : m ≠ 0 := by omega
    have hminv : (0 : ℝ) ≤ ((m : ℝ))⁻¹ := by positivity
    calc ((m : ℝ) / (Nat.totient m)) ^ 2 / m
        = ((m : ℝ) / (Nat.totient m)) ^ 2 * ((m : ℝ))⁻¹ := div_eq_mul_inv _ _
      _ ≤ (∑ d ∈ m.divisors, sqf3 d) * ((m : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right (sq_le_sum_divisors_sqf3 hm0) hminv
      _ = ∑ d ∈ m.divisors, sqf3 d / (m : ℝ) := by
          rw [← div_eq_mul_inv, Finset.sum_div]
  -- Step 2: swap the double sum over pairs (d, k) with d·k ≤ M.
  have step2 : ∑ m ∈ Icc 1 M, ∑ d ∈ m.divisors, sqf3 d / (m : ℝ)
      = ∑ d ∈ Icc 1 M, ∑ k ∈ Icc 1 (M / d), sqf3 d / ((d : ℝ) * (k : ℝ)) := by
    rw [Finset.sum_sigma', Finset.sum_sigma']
    refine Finset.sum_nbij' (fun x => ⟨x.2, x.1 / x.2⟩) (fun y => ⟨y.1 * y.2, y.1⟩)
      ?_ ?_ ?_ ?_ ?_
    · rintro ⟨m, d⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx ⊢
      obtain ⟨⟨hm1, hmM⟩, hdvd, hm0⟩ := hx
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hdm : d ≤ m := Nat.le_of_dvd (by omega) hdvd
      exact ⟨⟨hd0, hdm.trans hmM⟩, (Nat.one_le_div_iff hd0).mpr hdm, Nat.div_le_div_right hmM⟩
    · rintro ⟨d, k⟩ hy
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hy ⊢
      obtain ⟨⟨hd1, hdM⟩, hk1, hkM⟩ := hy
      have hdk : d * k ≤ M := by
        have h := (Nat.le_div_iff_mul_le (by omega : 0 < d)).mp hkM
        rw [mul_comm]
        exact h
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hdk⟩,
        dvd_mul_right d k, Nat.mul_ne_zero (by omega) (by omega)⟩
    · rintro ⟨m, d⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
      obtain ⟨⟨hm1, hmM⟩, hdvd, hm0⟩ := hx
      simp only [Nat.mul_div_cancel' hdvd]
    · rintro ⟨d, k⟩ hy
      simp only [Finset.mem_sigma, Finset.mem_Icc] at hy
      obtain ⟨⟨hd1, hdM⟩, hk1, hkM⟩ := hy
      simp only [Nat.mul_div_cancel_left _ (by omega : 0 < d)]
    · rintro ⟨m, d⟩ hx
      simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
      obtain ⟨⟨hm1, hmM⟩, hdvd, hm0⟩ := hx
      have hcast : ((d : ℝ)) * (((m / d : ℕ)) : ℝ) = (m : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      simp only [hcast]
  -- Step 3: bound the inner harmonic sums uniformly.
  have step3 : ∀ d ∈ Icc 1 M, ∑ k ∈ Icc 1 (M / d), sqf3 d / ((d : ℝ) * (k : ℝ))
      ≤ (sqf3 d / (d : ℝ)) * (1 + Real.log M) := by
    intro d hd
    obtain ⟨hd1, hdM⟩ := Finset.mem_Icc.mp hd
    have hrw : ∀ k : ℕ, sqf3 d / ((d : ℝ) * (k : ℝ)) = (sqf3 d / (d : ℝ)) * ((k : ℝ))⁻¹ := by
      intro k
      rw [div_mul_eq_div_div, div_eq_mul_inv (sqf3 d / (d : ℝ))]
    calc ∑ k ∈ Icc 1 (M / d), sqf3 d / ((d : ℝ) * (k : ℝ))
        = (sqf3 d / (d : ℝ)) * ∑ k ∈ Icc 1 (M / d), ((k : ℝ))⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => hrw k
      _ ≤ (sqf3 d / (d : ℝ)) * (1 + Real.log M) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (sqf3_nonneg d) (Nat.cast_nonneg d))
          exact sum_Icc_inv_le ((Nat.one_le_div_iff (by omega)).mpr hdM) (Nat.div_le_self M d)
  -- Assemble.
  calc ∑ m ∈ Icc 1 M, ((m : ℝ) / (Nat.totient m)) ^ 2 / m
      ≤ ∑ m ∈ Icc 1 M, ∑ d ∈ m.divisors, sqf3 d / (m : ℝ) := step1
    _ = ∑ d ∈ Icc 1 M, ∑ k ∈ Icc 1 (M / d), sqf3 d / ((d : ℝ) * (k : ℝ)) := step2
    _ ≤ ∑ d ∈ Icc 1 M, (sqf3 d / (d : ℝ)) * (1 + Real.log M) := Finset.sum_le_sum step3
    _ = (∑ d ∈ Icc 1 M, sqf3 d / (d : ℝ)) * (1 + Real.log M) := by rw [Finset.sum_mul]
    _ ≤ Real.exp 3 * (1 + Real.log M) := by
        refine mul_le_mul_of_nonneg_right (sum_sqf3_div_le M) ?_
        linarith

end Carmichael
