/-
A weak form of Alford--Granville--Pomerance Theorem 3: for some explicit
`E ∈ (0, 1/2]` and `γ > 0`, eventually at least `γ · π(x)` of the primes
`p ≤ x` have `p - 1` free of prime factors exceeding `x^(1-E)`.

Proof sketch. A prime `p ≤ x` that fails has a prime factor `q > x^(1-E)`
of `p - 1`, so `p = m·q + 1` with `1 ≤ m < x^E` and `q ≤ x/m`; hence the
count of failing primes is at most
`∑_{m ≤ x^E} #{q ≤ x/m : q prime, m·q + 1 prime}`.  The twin-type sieve
bound `twin_type_bound` estimates each inner count by
`C₀ (m/φ(m))² (x/m)/log²(x/m)`, and since `x/m ≥ x^(1-E)/2` each
`log(x/m) ≥ (log x)/4`; summing with `sum_sq_div_totient_sq_le` gives
`O(C₀ e³ E) · x/log x`, a small fraction of `π(x)` by `chebyshev_lower`
once `E` is chosen small against the sieve constant `C₀`.
-/
import Mathlib
import Carmichael.Defs
import Carmichael.PrimeCount
import Carmichael.TotientSumSq
import Carmichael.TwinSieve

namespace Carmichael

open Filter

open Classical in
/-- Weak AGP Theorem 3: some positive smoothness exponent `E ≤ 1/2` works,
with density `γ = 1/2`. -/
theorem smooth_shifted_weak :
    ∃ E : ℝ, 0 < E ∧ E ≤ 1/2 ∧ ∃ γ : ℝ, 0 < γ ∧ ∃ x₁ : ℕ, ∀ x : ℕ, x₁ ≤ x →
      γ * (primePi x : ℝ) ≤
        (((Finset.range (x + 1)).filter (fun p => p.Prime ∧
          ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) - E))).card : ℝ) := by
  obtain ⟨C₀, hC₀, t₀, htwin⟩ := twin_type_bound
  set E : ℝ := min (1/2) (1/(200 * Real.exp 3 * C₀)) with hEdef
  have hEpos : 0 < E := lt_min (by norm_num) (by positivity)
  have hE2 : E ≤ 1/2 := min_le_left _ _
  have hE1 : E ≤ 1/(200 * Real.exp 3 * C₀) := min_le_right _ _
  -- the eventual statement, with `γ = 1/2`
  have key : ∀ᶠ x : ℕ in atTop, (1/2 : ℝ) * (primePi x : ℝ) ≤
      (((Finset.range (x + 1)).filter (fun p => p.Prime ∧
        ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) - E))).card : ℝ) := by
    have h1E : (0:ℝ) < 1 - E := by linarith
    filter_upwards [eventually_ge_atTop 2,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
        (max 4 (1/E)),
      ((tendsto_rpow_atTop h1E).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 2,
      ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/2)).comp
        tendsto_natCast_atTop_atTop).eventually_ge_atTop (t₀ : ℝ),
      chebyshev_lower] with x hx2 hlogx hpowx hhalfx hchebx
    simp only [Function.comp_apply] at hlogx hpowx hhalfx
    -- basic facts about x
    have hx0 : 0 < x := by omega
    have hx0R : (0:ℝ) < (x:ℝ) := by exact_mod_cast hx0
    have hx1R : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx0
    have hlog4 : (4:ℝ) ≤ Real.log x := le_trans (le_max_left _ _) hlogx
    have hlogpos : (0:ℝ) < Real.log x := by linarith
    have hLne : Real.log x ≠ 0 := ne_of_gt hlogpos
    have hlogE1 : (1:ℝ) ≤ E * Real.log x := by
      have h := le_trans (le_max_right (4:ℝ) (1/E)) hlogx
      have h2 := mul_le_mul_of_nonneg_left h hEpos.le
      rwa [one_div, mul_inv_cancel₀ hEpos.ne'] at h2
    -- the smooth cutoff `M` for the cofactor `m`
    set M : ℕ := ⌊(x:ℝ) ^ E⌋₊ with hMdef
    have hxE1 : (1:ℝ) ≤ (x:ℝ) ^ E := by
      have h := Real.rpow_le_rpow_of_exponent_le hx1R hEpos.le
      rwa [Real.rpow_zero] at h
    have hM1 : 1 ≤ M := Nat.le_floor (by exact_mod_cast hxE1)
    have hMle : (M:ℝ) ≤ (x:ℝ) ^ E := Nat.floor_le (Real.rpow_nonneg hx0R.le _)
    have hMhalf : (M:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/2) :=
      hMle.trans (Real.rpow_le_rpow_of_exponent_le hx1R hE2)
    -- each `m ≤ M` leaves a long enough range for the twin sieve
    have ht₀m : ∀ m : ℕ, 1 ≤ m → m ≤ M → t₀ ≤ x / m := by
      intro m hm1 hmM
      have hmR : (m:ℝ) ≤ (x:ℝ) ^ ((1:ℝ)/2) :=
        le_trans (by exact_mod_cast hmM) hMhalf
      have hxx : (x:ℝ) ^ ((1:ℝ)/2) * (x:ℝ) ^ ((1:ℝ)/2) = x := by
        rw [← Real.rpow_add hx0R, show (1:ℝ)/2 + 1/2 = 1 by norm_num, Real.rpow_one]
      have hprod : (t₀:ℝ) * m ≤ (x:ℝ) := by
        have h := mul_le_mul hhalfx hmR (by positivity) (Real.rpow_nonneg hx0R.le _)
        linarith
      have hnat : t₀ * m ≤ x := by exact_mod_cast hprod
      exact (Nat.le_div_iff_mul_le (by omega)).mpr hnat
    -- the bad primes: `p ≤ x` prime with a prime factor of `p - 1` above `x^(1-E)`
    set Sbad : Finset ℕ := (Finset.range (x + 1)).filter (fun p => p.Prime ∧
      ¬ ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) - E)) with hSb
    -- a bad prime is `m·q + 1` with `1 ≤ m ≤ M` and `q ≤ x/m` prime
    have hbad_sub : Sbad ⊆ (Finset.Icc 1 M).biUnion (fun m =>
        ((Finset.Icc 1 (x / m)).filter (fun q => q.Prime ∧ (m * q + 1).Prime)).image
          (fun q => m * q + 1)) := by
      intro p hp
      simp only [hSb, Finset.mem_filter, Finset.mem_range] at hp
      obtain ⟨hpx, hpp, hG⟩ := hp
      push Not at hG
      obtain ⟨q, hq, hqd, hqbig⟩ := hG
      have hp2 : 2 ≤ p := hpp.two_le
      have hq2 : 2 ≤ q := hq.two_le
      have hqle : q ≤ p - 1 := Nat.le_of_dvd (by omega) hqd
      set m : ℕ := (p - 1) / q with hmdef
      have hmq : m * q = p - 1 := Nat.div_mul_cancel hqd
      have hm1 : 1 ≤ m := (Nat.one_le_div_iff (by omega)).mpr hqle
      have hmqx : m * q ≤ x := by rw [hmq]; omega
      have hpeq : m * q + 1 = p := by rw [hmq]; omega
      -- `m < x^E`
      have hm0R : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
      have hmqxR : (m:ℝ) * q ≤ (x:ℝ) := by exact_mod_cast hmqx
      have hxeq : (x:ℝ) ^ E * (x:ℝ) ^ ((1:ℝ) - E) = x := by
        rw [← Real.rpow_add hx0R, show E + ((1:ℝ) - E) = 1 by ring, Real.rpow_one]
      have hpow_pos : (0:ℝ) < (x:ℝ) ^ ((1:ℝ) - E) := Real.rpow_pos_of_pos hx0R _
      have hmE : (m:ℝ) < (x:ℝ) ^ E := by
        have h1 : (m:ℝ) * ((x:ℝ) ^ ((1:ℝ) - E)) < (m:ℝ) * q :=
          mul_lt_mul_of_pos_left hqbig hm0R
        have h2 : (m:ℝ) * ((x:ℝ) ^ ((1:ℝ) - E)) < (x:ℝ) ^ E * (x:ℝ) ^ ((1:ℝ) - E) := by
          rw [hxeq]; linarith
        exact lt_of_mul_lt_mul_right h2 hpow_pos.le
      have hmM : m ≤ M := Nat.le_floor hmE.le
      have hqt : q ≤ x / m :=
        (Nat.le_div_iff_mul_le (by omega)).mpr (by rw [mul_comm]; exact hmqx)
      refine Finset.mem_biUnion.mpr ⟨m, Finset.mem_Icc.mpr ⟨hm1, hmM⟩, ?_⟩
      refine Finset.mem_image.mpr ⟨q, ?_, hpeq⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hqt⟩, hq, ?_⟩
      rw [hpeq]; exact hpp
    -- count the bad primes by the twin-type counts
    have hbad_card : Sbad.card ≤ ∑ m ∈ Finset.Icc 1 M,
        ((Finset.Icc 1 (x / m)).filter (fun q => q.Prime ∧ (m * q + 1).Prime)).card := by
      calc Sbad.card
          ≤ ((Finset.Icc 1 M).biUnion (fun m =>
              ((Finset.Icc 1 (x / m)).filter (fun q => q.Prime ∧ (m * q + 1).Prime)).image
                (fun q => m * q + 1))).card := Finset.card_le_card hbad_sub
        _ ≤ ∑ m ∈ Finset.Icc 1 M, (((Finset.Icc 1 (x / m)).filter
            (fun q => q.Prime ∧ (m * q + 1).Prime)).image (fun q => m * q + 1)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ m ∈ Finset.Icc 1 M, ((Finset.Icc 1 (x / m)).filter
            (fun q => q.Prime ∧ (m * q + 1).Prime)).card :=
            Finset.sum_le_sum (fun m _ => Finset.card_image_le)
    -- the twin sieve bound for each cofactor `m`
    have hterm : ∀ m ∈ Finset.Icc 1 M,
        (((Finset.Icc 1 (x / m)).filter (fun q => q.Prime ∧ (m * q + 1).Prime)).card : ℝ)
          ≤ 16 * C₀ * ((x:ℝ) / (Real.log x)^2) * (((m:ℝ) / (Nat.totient m))^2 / m) := by
      intro m hm
      obtain ⟨hm1, hmM⟩ := Finset.mem_Icc.mp hm
      have hm0 : 0 < m := hm1
      have hm0R : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm0
      have hmne : (m:ℝ) ≠ 0 := hm0R.ne'
      refine (htwin m (x / m) hm1 (ht₀m m hm1 hmM)).trans ?_
      -- upper bound `(x/m)·m ≤ x`
      have htm : ((x / m : ℕ):ℝ) * m ≤ (x:ℝ) := by
        exact_mod_cast Nat.div_mul_le_self x m
      -- lower bound `x^(1-E)/2 ≤ x/m`
      have hmxE : (m:ℝ) ≤ (x:ℝ) ^ E := le_trans (by exact_mod_cast hmM) hMle
      have hxlt : x < m * (x / m) + m := by
        conv_lhs => rw [← Nat.div_add_mod x m]
        exact Nat.add_lt_add_left (Nat.mod_lt x hm0) _
      have hxltR : (x:ℝ) < (m:ℝ) * ((x / m : ℕ):ℝ) + m := by exact_mod_cast hxlt
      have hdiv : (x:ℝ) ^ ((1:ℝ) - E) ≤ (x:ℝ) / m := by
        rw [le_div_iff₀ hm0R]
        calc (x:ℝ) ^ ((1:ℝ) - E) * m
            ≤ (x:ℝ) ^ ((1:ℝ) - E) * (x:ℝ) ^ E :=
              mul_le_mul_of_nonneg_left hmxE (Real.rpow_nonneg hx0R.le _)
          _ = x := by
              rw [← Real.rpow_add hx0R, show (1:ℝ) - E + E = 1 by ring, Real.rpow_one]
      have hxm : (x:ℝ) / m < ((x / m : ℕ):ℝ) + 1 := by
        rw [div_lt_iff₀ hm0R]
        linarith [hxltR]
      have htlb : (x:ℝ) ^ ((1:ℝ) - E) / 2 ≤ ((x / m : ℕ):ℝ) := by
        linarith [hpowx, hdiv, hxm]
      -- `log (x/m) ≥ (log x)/4`
      have hlogt : (1/4) * Real.log x ≤ Real.log ((x / m : ℕ):ℝ) := by
        have h2pos : (0:ℝ) < (x:ℝ) ^ ((1:ℝ) - E) / 2 := by positivity
        have hlt := Real.log_le_log h2pos htlb
        rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hx0R] at hlt
        have hlog2 : Real.log 2 ≤ 1 := by
          have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
          linarith
        have hEnn : (0:ℝ) ≤ (1/2 - E) * Real.log x :=
          mul_nonneg (by linarith) hlogpos.le
        linarith
      have hlogt_pos : (0:ℝ) < Real.log ((x / m : ℕ):ℝ) := by linarith
      have hsq : (1/16) * (Real.log x)^2 ≤ (Real.log ((x / m : ℕ):ℝ))^2 := by
        nlinarith [mul_self_le_mul_self
          (by linarith : (0:ℝ) ≤ 1/4 * Real.log x) hlogt]
      -- combine into the per-term bound
      have h1 : ((x / m : ℕ):ℝ) / (Real.log ((x / m : ℕ):ℝ))^2
          ≤ 16 * x / ((m:ℝ) * (Real.log x)^2) := by
        rw [div_le_div_iff₀ (pow_pos hlogt_pos 2) (mul_pos hm0R (pow_pos hlogpos 2))]
        nlinarith [mul_le_mul_of_nonneg_right htm (sq_nonneg (Real.log x)),
          mul_le_mul_of_nonneg_left hsq (by positivity : (0:ℝ) ≤ (x:ℝ))]
      have hR0 : (0:ℝ) ≤ ((m:ℝ) / (Nat.totient m))^2 := sq_nonneg _
      calc C₀ * ((m:ℝ) / (Nat.totient m))^2 * ((x / m : ℕ):ℝ)
            / (Real.log ((x / m : ℕ):ℝ))^2
          = (C₀ * ((m:ℝ) / (Nat.totient m))^2)
            * (((x / m : ℕ):ℝ) / (Real.log ((x / m : ℕ):ℝ))^2) := by ring
        _ ≤ (C₀ * ((m:ℝ) / (Nat.totient m))^2) * (16 * x / ((m:ℝ) * (Real.log x)^2)) :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg hC₀.le hR0)
        _ = 16 * C₀ * ((x:ℝ) / (Real.log x)^2) * (((m:ℝ) / (Nat.totient m))^2 / m) := by
            field_simp
    -- sum the per-term bounds
    have hK0 : (0:ℝ) ≤ 16 * C₀ * ((x:ℝ) / (Real.log x)^2) :=
      mul_nonneg (mul_nonneg (by norm_num) hC₀.le) (div_nonneg hx0R.le (sq_nonneg _))
    have hbadR : (Sbad.card : ℝ) ≤
        16 * C₀ * ((x:ℝ) / (Real.log x)^2) * (Real.exp 3 * (1 + Real.log M)) := by
      have hcast : (Sbad.card : ℝ) ≤ ∑ m ∈ Finset.Icc 1 M,
          (((Finset.Icc 1 (x / m)).filter (fun q => q.Prime ∧ (m * q + 1).Prime)).card : ℝ) := by
        exact_mod_cast hbad_card
      calc (Sbad.card : ℝ)
          ≤ ∑ m ∈ Finset.Icc 1 M, (((Finset.Icc 1 (x / m)).filter
              (fun q => q.Prime ∧ (m * q + 1).Prime)).card : ℝ) := hcast
        _ ≤ ∑ m ∈ Finset.Icc 1 M,
            16 * C₀ * ((x:ℝ) / (Real.log x)^2) * (((m:ℝ) / (Nat.totient m))^2 / m) :=
            Finset.sum_le_sum hterm
        _ = 16 * C₀ * ((x:ℝ) / (Real.log x)^2) *
            ∑ m ∈ Finset.Icc 1 M, ((m:ℝ) / (Nat.totient m))^2 / m := by
            rw [← Finset.mul_sum]
        _ ≤ 16 * C₀ * ((x:ℝ) / (Real.log x)^2) * (Real.exp 3 * (1 + Real.log M)) :=
            mul_le_mul_of_nonneg_left (sum_sq_div_totient_sq_le M hM1) hK0
    -- `1 + log M ≤ 2 E log x`
    have hlogM : 1 + Real.log M ≤ 2 * E * Real.log x := by
      have hMpos : (0:ℝ) < (M:ℝ) := by exact_mod_cast hM1
      have h := Real.log_le_log hMpos hMle
      rw [Real.log_rpow hx0R] at h
      linarith
    -- `|bad| ≤ 32 C₀ e³ E · x/log x`
    have hbadR2 : (Sbad.card : ℝ) ≤ 32 * C₀ * Real.exp 3 * E * ((x:ℝ) / Real.log x) := by
      refine hbadR.trans ?_
      have h1 : Real.exp 3 * (1 + Real.log M) ≤ Real.exp 3 * (2 * E * Real.log x) :=
        mul_le_mul_of_nonneg_left hlogM (Real.exp_pos 3).le
      have h2 := mul_le_mul_of_nonneg_left h1 hK0
      refine h2.trans_eq ?_
      field_simp
      ring
    -- Chebyshev: `x/log x ≤ 3 π(x)`
    have hxL : (x:ℝ) / Real.log x ≤ 3 * (primePi x : ℝ) := by
      have h : (x:ℝ) / Real.log x = 3 * ((x:ℝ) / (3 * Real.log x)) := by
        field_simp
      rw [h]
      linarith [hchebx]
    -- the bad primes are at most half of all primes
    have hbadPi : (Sbad.card : ℝ) ≤ (1/2) * (primePi x : ℝ) := by
      have hC₀ne : C₀ ≠ 0 := hC₀.ne'
      have hexpne : Real.exp 3 ≠ 0 := (Real.exp_pos 3).ne'
      have h96 : 96 * C₀ * Real.exp 3 * E ≤ 1/2 := by
        have hc : (0:ℝ) ≤ 96 * C₀ * Real.exp 3 :=
          mul_nonneg (mul_nonneg (by norm_num) hC₀.le) (Real.exp_pos 3).le
        calc 96 * C₀ * Real.exp 3 * E
            ≤ 96 * C₀ * Real.exp 3 * (1/(200 * Real.exp 3 * C₀)) :=
              mul_le_mul_of_nonneg_left hE1 hc
          _ = 96/200 := by
              field_simp
          _ ≤ 1/2 := by norm_num
      calc (Sbad.card : ℝ)
          ≤ 32 * C₀ * Real.exp 3 * E * ((x:ℝ) / Real.log x) := hbadR2
        _ ≤ 32 * C₀ * Real.exp 3 * E * (3 * (primePi x : ℝ)) :=
            mul_le_mul_of_nonneg_left hxL (by positivity)
        _ = (96 * C₀ * Real.exp 3 * E) * (primePi x : ℝ) := by ring
        _ ≤ (1/2) * (primePi x : ℝ) :=
            mul_le_mul_of_nonneg_right h96 (Nat.cast_nonneg _)
    -- split `π(x)` into good and bad primes and conclude
    set Sgood : Finset ℕ := (Finset.range (x + 1)).filter (fun p => p.Prime ∧
      ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) - E)) with hSg
    have hsub : (Finset.range (x + 1)).filter Nat.Prime ⊆ Sgood ∪ Sbad := by
      intro p hp
      rw [Finset.mem_filter] at hp
      by_cases hG : ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) - E)
      · exact Finset.mem_union_left _
          (by rw [hSg]; exact Finset.mem_filter.mpr ⟨hp.1, hp.2, hG⟩)
      · exact Finset.mem_union_right _
          (by rw [hSb]; exact Finset.mem_filter.mpr ⟨hp.1, hp.2, hG⟩)
    have hsplit : primePi x ≤ Sgood.card + Sbad.card := by
      calc primePi x = ((Finset.range (x + 1)).filter Nat.Prime).card := rfl
        _ ≤ (Sgood ∪ Sbad).card := Finset.card_le_card hsub
        _ ≤ Sgood.card + Sbad.card := Finset.card_union_le _ _
    have hsplitR : (primePi x : ℝ) ≤ (Sgood.card : ℝ) + (Sbad.card : ℝ) := by
      exact_mod_cast hsplit
    linarith [hbadPi, hsplitR]
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp key
  exact ⟨E, hEpos, hE2, 1/2, by norm_num, x₁, fun x hx => hx₁ x hx⟩

end Carmichael
