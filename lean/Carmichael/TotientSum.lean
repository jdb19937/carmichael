/-
An elementary bound on the totient reciprocal sum:
  ∑_{m ≤ M} 1/φ(m) ≤ e · (1 + log M).

Proof outline (all finite and elementary):
* identity: m/φ(m) = ∑_{d ∣ m, d squarefree} 1/φ(d), via Euler's product for φ
  and the powerset expansion of ∏_{p ∣ m} (1 + 1/(p-1));
* swap the double sum over pairs (d, k) with d·k ≤ M;
* the inner sum is a harmonic number, bounded by 1 + log M;
* the outer constant ∑_{d squarefree} 1/(d·φ(d)) is at most
  ∏_{p ≤ M} (1 + 1/(p(p-1))) ≤ exp(∑_{n≥2} 1/(n(n-1))) ≤ e.
-/
import Mathlib

namespace Carmichael

open Finset

/-- The summand `μ²(d)/φ(d)`: the indicator of squarefreeness divided by the totient. -/
noncomputable def sqf (d : ℕ) : ℝ := if Squarefree d then ((Nat.totient d : ℝ))⁻¹ else 0

lemma sqf_nonneg (d : ℕ) : 0 ≤ sqf d := by
  unfold sqf
  split <;> positivity

/-- The totient of a product of distinct primes. -/
lemma totient_prod_primes (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    Nat.totient (∏ p ∈ t, p) = ∏ p ∈ t, (p - 1) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert q s hqs ih =>
    have hq : q.Prime := ht q (mem_insert_self q s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => ht p (mem_insert_of_mem hp)
    have hcop : Nat.Coprime q (∏ p ∈ s, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hq (hs p hp)).mpr (by rintro rfl; exact hqs hp)
    rw [prod_insert hqs, prod_insert hqs, Nat.totient_mul hcop, Nat.totient_prime hq, ih hs]

/-- Real-cast version of `totient_prod_primes`. -/
lemma totient_prod_primes_real (t : Finset ℕ) (ht : ∀ p ∈ t, p.Prime) :
    ((Nat.totient (∏ p ∈ t, p) : ℕ) : ℝ) = ∏ p ∈ t, ((p : ℝ) - 1) := by
  rw [totient_prod_primes t ht, Nat.cast_prod]
  exact Finset.prod_congr rfl fun p hp => by
    rw [Nat.cast_sub (ht p hp).one_lt.le, Nat.cast_one]

/-- The key identity: `∑_{d ∣ m} μ²(d)/φ(d) = m/φ(m)`. -/
lemma sum_divisors_sqf {m : ℕ} (hm : m ≠ 0) :
    ∑ d ∈ m.divisors, sqf d = (m : ℝ) / (Nat.totient m) := by
  have hprime : ∀ p ∈ m.primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  -- Reduce to squarefree divisors, i.e. subsets of the prime factors.
  have h1 : ∑ d ∈ m.divisors, sqf d
      = ∑ t ∈ m.primeFactors.powerset, ((Nat.totient t.val.prod : ℝ))⁻¹ := by
    simp only [sqf]
    rw [← Finset.sum_filter, Nat.sum_divisors_filter_squarefree hm, Nat.factors_eq]
    rfl
  -- Each subset contributes a product of `1/(p-1)`.
  have h2 : ∀ t ∈ m.primeFactors.powerset,
      ((Nat.totient t.val.prod : ℝ))⁻¹ = ∏ p ∈ t, ((p : ℝ) - 1)⁻¹ := by
    intro t ht
    have hsub := Finset.mem_powerset.mp ht
    have hpr : ∀ p ∈ t, p.Prime := fun p hp => hprime p (hsub hp)
    rw [show t.val.prod = ∏ p ∈ t, p from t.prod_val, totient_prod_primes_real t hpr,
      Finset.prod_inv_distrib]
  -- Sum over the powerset is the product `∏ (1/(p-1) + 1)`.
  have h3 : ∑ t ∈ m.primeFactors.powerset, ∏ p ∈ t, ((p : ℝ) - 1)⁻¹
      = ∏ p ∈ m.primeFactors, (((p : ℝ) - 1)⁻¹ + 1) := by
    rw [Finset.prod_add]
    exact Finset.sum_congr rfl fun t _ => by simp
  have hpos : ∀ p ∈ m.primeFactors, (0 : ℝ) < (p : ℝ) - 1 := by
    intro p hp
    have h2le : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hprime p hp).two_le
    linarith
  -- `∏ (1/(p-1) + 1) = ∏ p · (∏ (p-1))⁻¹`.
  have h4 : ∏ p ∈ m.primeFactors, (((p : ℝ) - 1)⁻¹ + 1)
      = (∏ p ∈ m.primeFactors, (p : ℝ)) * (∏ p ∈ m.primeFactors, ((p : ℝ) - 1))⁻¹ := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have h0 : ((p : ℝ) - 1) ≠ 0 := (hpos p hp).ne'
    have hexp : (p : ℝ) * ((p : ℝ) - 1)⁻¹
        = ((p : ℝ) - 1) * ((p : ℝ) - 1)⁻¹ + 1 * ((p : ℝ) - 1)⁻¹ := by ring
    rw [hexp, mul_inv_cancel₀ h0, one_mul, add_comm]
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
  have hφ : (0 : ℝ) < (Nat.totient m : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm)
  have hprodpos : (0 : ℝ) < ∏ p ∈ m.primeFactors, ((p : ℝ) - 1) :=
    Finset.prod_pos hpos
  rw [h1, Finset.sum_congr rfl h2, h3, h4, eq_div_iff hφ.ne']
  field_simp
  linear_combination hcast

/-- The harmonic sum `∑_{k ≤ N} 1/k` is at most `1 + log M` whenever `1 ≤ N ≤ M`. -/
lemma sum_Icc_inv_le {N M : ℕ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    ∑ k ∈ Icc 1 N, ((k : ℝ))⁻¹ ≤ 1 + Real.log M := by
  have h1 : ∑ k ∈ Icc 1 N, ((k : ℝ))⁻¹ = ((harmonic N : ℚ) : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    rfl
  rw [h1]
  calc ((harmonic N : ℚ) : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
    _ ≤ 1 + Real.log M := by
        have hpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        have hle : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hNM
        linarith [Real.log_le_log hpos hle]

/-- Telescoping: `∑_{2 ≤ n ≤ M} 1/(n(n-1)) ≤ 1`. -/
lemma sum_telescope_le (M : ℕ) :
    ∑ n ∈ Icc 2 M, ((n : ℝ) * ((n : ℝ) - 1))⁻¹ ≤ 1 := by
  have key : ∀ K : ℕ, 1 ≤ K →
      ∑ n ∈ Icc 2 K, ((n : ℝ) * ((n : ℝ) - 1))⁻¹ = 1 - ((K : ℝ))⁻¹ := by
    intro K hK
    induction K, hK using Nat.le_induction with
    | base =>
      rw [Finset.Icc_eq_empty_of_lt (by norm_num)]
      norm_num
    | succ K hK ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ K + 1), ih]
      have hK1 : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
      have hK0 : ((K : ℝ)) ≠ 0 := by linarith
      have hK10 : ((K : ℝ) + 1) ≠ 0 := by linarith
      have hcast : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hinv : (((K : ℝ) + 1) * ((K : ℝ) + 1 - 1))⁻¹ = (K : ℝ)⁻¹ - ((K : ℝ) + 1)⁻¹ := by
        rw [show ((K : ℝ) + 1 - 1) = (K : ℝ) from by ring, inv_eq_one_div, inv_eq_one_div,
          inv_eq_one_div, div_sub_div _ _ hK0 hK10,
          show (1 * ((K : ℝ) + 1) - (K : ℝ) * 1) = 1 from by ring, mul_comm]
      rw [hinv]
      ring
  rcases Nat.lt_or_ge M 1 with hM | hM
  · interval_cases M
    rw [Finset.Icc_eq_empty_of_lt (by norm_num)]
    norm_num
  · rw [key M hM]
    have : (0 : ℝ) ≤ ((M : ℝ))⁻¹ := by positivity
    linarith

/-- The constant sum: `∑_{d ≤ M} μ²(d)/(d·φ(d)) ≤ e`. -/
lemma sum_sqf_div_le (M : ℕ) :
    ∑ d ∈ Icc 1 M, sqf d / (d : ℝ) ≤ Real.exp 1 := by
  classical
  set P : Finset ℕ := (Icc 1 M).filter Nat.Prime with hP
  -- (a) restrict to squarefree d
  have ha : ∑ d ∈ Icc 1 M, sqf d / (d : ℝ)
      = ∑ d ∈ (Icc 1 M).filter Squarefree, ((Nat.totient d : ℝ))⁻¹ / (d : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [sqf]
    split_ifs <;> simp
  -- (b) each squarefree term is a product over its prime factors
  have hb : ∀ d ∈ (Icc 1 M).filter Squarefree,
      ((Nat.totient d : ℝ))⁻¹ / (d : ℝ)
        = ∏ p ∈ d.primeFactors, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
    intro d hd
    obtain ⟨_, hsq⟩ := Finset.mem_filter.mp hd
    have hpr : ∀ p ∈ d.primeFactors, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors hp
    have h1 : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
      rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
    have h2 : ((Nat.totient d : ℕ) : ℝ) = ∏ p ∈ d.primeFactors, ((p : ℝ) - 1) := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
      exact totient_prod_primes_real d.primeFactors hpr
    calc ((Nat.totient d : ℝ))⁻¹ / (d : ℝ)
        = ((d : ℝ) * (Nat.totient d : ℝ))⁻¹ := by
          rw [mul_inv, div_eq_mul_inv, mul_comm]
      _ = ((∏ p ∈ d.primeFactors, (p : ℝ)) * ∏ p ∈ d.primeFactors, ((p : ℝ) - 1))⁻¹ := by
          rw [h1, h2]
      _ = ∏ p ∈ d.primeFactors, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
          rw [← Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  -- (c) reindex by the set of prime factors
  have hinj : ∀ d₁ ∈ (Icc 1 M).filter Squarefree, ∀ d₂ ∈ (Icc 1 M).filter Squarefree,
      d₁.primeFactors = d₂.primeFactors → d₁ = d₂ := by
    intro d₁ h₁ d₂ h₂ h
    have hsq₁ := (Finset.mem_filter.mp h₁).2
    have hsq₂ := (Finset.mem_filter.mp h₂).2
    rw [← Nat.prod_primeFactors_of_squarefree hsq₁, ← Nat.prod_primeFactors_of_squarefree hsq₂, h]
  have hc : ∑ d ∈ (Icc 1 M).filter Squarefree,
        ∏ p ∈ d.primeFactors, ((p : ℝ) * ((p : ℝ) - 1))⁻¹
      = ∑ t ∈ ((Icc 1 M).filter Squarefree).image Nat.primeFactors,
          ∏ p ∈ t, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
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
  have hnonneg : ∀ t ∈ P.powerset, (0 : ℝ) ≤ ∏ p ∈ t, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
    intro t ht
    refine Finset.prod_nonneg fun p hp => ?_
    have hppr : p.Prime := (Finset.mem_filter.mp (Finset.mem_powerset.mp ht hp)).2
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hppr.two_le
    exact inv_nonneg.mpr (mul_nonneg (by linarith) (by linarith))
  -- (f) the powerset sum is a product
  have hf : ∑ t ∈ P.powerset, ∏ p ∈ t, ((p : ℝ) * ((p : ℝ) - 1))⁻¹
      = ∏ p ∈ P, (((p : ℝ) * ((p : ℝ) - 1))⁻¹ + 1) := by
    rw [Finset.prod_add]
    exact (Finset.sum_congr rfl fun t _ => by simp).symm
  -- (g) bound the product by an exponential
  have hg : ∏ p ∈ P, (((p : ℝ) * ((p : ℝ) - 1))⁻¹ + 1)
      ≤ Real.exp (∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
    rw [Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => Real.add_one_le_exp _)
    have hppr : p.Prime := (Finset.mem_filter.mp hp).2
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hppr.two_le
    have := inv_nonneg.mpr (mul_nonneg (by linarith : (0:ℝ) ≤ (p:ℝ))
      (by linarith : (0:ℝ) ≤ (p:ℝ) - 1))
    linarith
  -- (h) the exponent is at most 1
  have hPsub : P ⊆ Icc 2 M := by
    intro p hp
    obtain ⟨hIcc, hpr⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr ⟨hpr.two_le, (Finset.mem_Icc.mp hIcc).2⟩
  have hh : ∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ ≤ 1 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hPsub fun n hn _ => ?_)
      (sum_telescope_le M)
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact inv_nonneg.mpr (mul_nonneg (by linarith) (by linarith))
  calc ∑ d ∈ Icc 1 M, sqf d / (d : ℝ)
      = ∑ d ∈ (Icc 1 M).filter Squarefree, ((Nat.totient d : ℝ))⁻¹ / (d : ℝ) := ha
    _ = ∑ d ∈ (Icc 1 M).filter Squarefree,
          ∏ p ∈ d.primeFactors, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := Finset.sum_congr rfl hb
    _ = ∑ t ∈ ((Icc 1 M).filter Squarefree).image Nat.primeFactors,
          ∏ p ∈ t, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := hc
    _ ≤ ∑ t ∈ P.powerset, ∏ p ∈ t, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset fun t ht _ => hnonneg t ht
    _ = ∏ p ∈ P, (((p : ℝ) * ((p : ℝ) - 1))⁻¹ + 1) := hf
    _ ≤ Real.exp (∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := hg
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr hh

/-- **Totient reciprocal sum bound**: `∑_{m ≤ M} 1/φ(m) ≤ e·(1 + log M)`. -/
theorem sum_inv_totient_le (M : ℕ) (hM : 1 ≤ M) :
    ∑ m ∈ Finset.Icc 1 M, (1 : ℝ) / (Nat.totient m) ≤
      Real.exp 1 * (1 + Real.log M) := by
  have hlogM : (0 : ℝ) ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM)
  -- Step 1: rewrite each term via the divisor identity.
  have step1 : ∑ m ∈ Icc 1 M, (1 : ℝ) / (Nat.totient m)
      = ∑ m ∈ Icc 1 M, ∑ d ∈ m.divisors, sqf d / (m : ℝ) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
    have hm0 : m ≠ 0 := by omega
    have hmR : ((m : ℝ)) ≠ 0 := by exact_mod_cast hm0
    have hφ : ((Nat.totient m : ℝ)) ≠ 0 := by
      have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm0)
      exact_mod_cast this.ne'
    rw [← Finset.sum_div, sum_divisors_sqf hm0]
    field_simp
  -- Step 2: swap the double sum over pairs (d, k) with d·k ≤ M.
  have step2 : ∑ m ∈ Icc 1 M, ∑ d ∈ m.divisors, sqf d / (m : ℝ)
      = ∑ d ∈ Icc 1 M, ∑ k ∈ Icc 1 (M / d), sqf d / ((d : ℝ) * (k : ℝ)) := by
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
  have step3 : ∀ d ∈ Icc 1 M, ∑ k ∈ Icc 1 (M / d), sqf d / ((d : ℝ) * (k : ℝ))
      ≤ (sqf d / (d : ℝ)) * (1 + Real.log M) := by
    intro d hd
    obtain ⟨hd1, hdM⟩ := Finset.mem_Icc.mp hd
    have hrw : ∀ k : ℕ, sqf d / ((d : ℝ) * (k : ℝ)) = (sqf d / (d : ℝ)) * ((k : ℝ))⁻¹ := by
      intro k
      rw [div_mul_eq_div_div, div_eq_mul_inv (sqf d / (d : ℝ))]
    calc ∑ k ∈ Icc 1 (M / d), sqf d / ((d : ℝ) * (k : ℝ))
        = (sqf d / (d : ℝ)) * ∑ k ∈ Icc 1 (M / d), ((k : ℝ))⁻¹ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => hrw k
      _ ≤ (sqf d / (d : ℝ)) * (1 + Real.log M) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (sqf_nonneg d) (Nat.cast_nonneg d))
          exact sum_Icc_inv_le ((Nat.one_le_div_iff (by omega)).mpr hdM) (Nat.div_le_self M d)
  -- Assemble.
  calc ∑ m ∈ Icc 1 M, (1 : ℝ) / (Nat.totient m)
      = ∑ d ∈ Icc 1 M, ∑ k ∈ Icc 1 (M / d), sqf d / ((d : ℝ) * (k : ℝ)) := by
        rw [step1, step2]
    _ ≤ ∑ d ∈ Icc 1 M, (sqf d / (d : ℝ)) * (1 + Real.log M) := Finset.sum_le_sum step3
    _ = (∑ d ∈ Icc 1 M, sqf d / (d : ℝ)) * (1 + Real.log M) := by rw [Finset.sum_mul]
    _ ≤ Real.exp 1 * (1 + Real.log M) := by
        refine mul_le_mul_of_nonneg_right (sum_sqf_div_le M) ?_
        linarith

end Carmichael
