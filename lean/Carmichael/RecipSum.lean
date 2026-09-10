/-
Bound on the prime reciprocal sum over an interval (w, z], derived from the
vendored Mertens' first theorem (Carmichael/Mertens.lean).
-/
import Carmichael.Defs
import Carmichael.Mertens

namespace Carmichael

open scoped ArithmeticFunction

theorem primeRecipSum_sub_le {w z : ℕ} (hw : 2 ≤ w) (hwz : w ≤ z) :
    primeRecipSum z - primeRecipSum w ≤
      (Real.log z - Real.log w + 2 * (Real.log 4 + 4)) / Real.log w := by
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hw1 : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast (show 1 ≤ w by omega)
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show 1 ≤ z by omega)
  have hlogw : 0 < Real.log w :=
    Real.log_pos (by exact_mod_cast (show 1 < w by omega))
  -- Step 1: the difference is the reciprocal sum over primes in (w, z].
  have hsub : (Finset.range (w + 1)).filter Nat.Prime ⊆
      (Finset.range (z + 1)).filter Nat.Prime :=
    Finset.filter_subset_filter _ (by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega)
  have hdiff : (Finset.range (z + 1)).filter Nat.Prime \
      (Finset.range (w + 1)).filter Nat.Prime = (Finset.Ioc w z).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have h4 : ¬ p < w + 1 := fun h => h3 ⟨h, h2⟩
      exact ⟨⟨by omega, by omega⟩, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by omega, h3⟩, fun h => absurd h.1 (by omega)⟩
  have hsplit : primeRecipSum z - primeRecipSum w
      = ∑ p ∈ (Finset.Ioc w z).filter Nat.Prime, (1 : ℝ) / p := by
    simp only [primeRecipSum]
    rw [← Finset.sum_sdiff_eq_sub hsub, hdiff]
  -- Step 2: pointwise bound 1/p ≤ (Λ p / p) / log w for primes p ∈ (w, z].
  have h2 : ∀ p ∈ (Finset.Ioc w z).filter Nat.Prime,
      (1 : ℝ) / p ≤ (Λ p / p) / Real.log w := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hwp, hpz⟩, hprime⟩ := hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hcast : (w : ℝ) ≤ p := by exact_mod_cast hwp.le
    have hlogp : Real.log w ≤ Real.log p := by gcongr
    rw [ArithmeticFunction.vonMangoldt_apply_prime hprime]
    have hne : Real.log w ≠ 0 := ne_of_gt hlogw
    have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
    calc (1 : ℝ) / p = (Real.log w / p) / Real.log w := by field_simp
      _ ≤ (Real.log p / p) / Real.log w := by gcongr
  -- Step 3: primes in (w, z] contribute at most the full von Mangoldt sum.
  have h3 : ∑ p ∈ (Finset.Ioc w z).filter Nat.Prime, Λ p / (p : ℝ)
      ≤ ∑ n ∈ Finset.Ioc w z, Λ n / (n : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
  -- Step 4: split the full von Mangoldt sum at w.
  have h4 : ∑ n ∈ Finset.Ioc w z, Λ n / (n : ℝ)
      = (∑ n ∈ Finset.Ioc 0 z, Λ n / (n : ℝ))
        - ∑ n ∈ Finset.Ioc 0 w, Λ n / (n : ℝ) := by
    have := Finset.sum_Ioc_consecutive (fun n : ℕ => Λ n / (n : ℝ)) (Nat.zero_le w) hwz
    linarith
  -- Step 5: Mertens' first theorem at z and at w.
  have hMz := Mertens.sum_mangoldt_div_eq_log hz1
  have hMw := Mertens.sum_mangoldt_div_eq_log hw1
  simp only [Nat.floor_natCast] at hMz hMw
  obtain ⟨hMz1, hMz2⟩ := abs_le.mp hMz
  obtain ⟨hMw1, hMw2⟩ := abs_le.mp hMw
  have hbound : ∑ n ∈ Finset.Ioc w z, Λ n / (n : ℝ)
      ≤ Real.log z - Real.log w + 2 * (Real.log 4 + 4) := by
    rw [h4]; linarith
  -- Step 6: combine.
  calc primeRecipSum z - primeRecipSum w
      = ∑ p ∈ (Finset.Ioc w z).filter Nat.Prime, (1 : ℝ) / p := hsplit
    _ ≤ ∑ p ∈ (Finset.Ioc w z).filter Nat.Prime, (Λ p / p) / Real.log w :=
        Finset.sum_le_sum h2
    _ = (∑ p ∈ (Finset.Ioc w z).filter Nat.Prime, Λ p / (p : ℝ)) / Real.log w := by
        rw [Finset.sum_div]
    _ ≤ (∑ n ∈ Finset.Ioc w z, Λ n / (n : ℝ)) / Real.log w := by gcongr
    _ ≤ (Real.log z - Real.log w + 2 * (Real.log 4 + 4)) / Real.log w := by gcongr

end Carmichael
