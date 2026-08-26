/-
Korselt's criterion: a composite `m > 1` is a Carmichael number iff `m` is
squarefree and `p - 1 ∣ m - 1` for every prime `p ∣ m`.
-/
import Carmichael.Defs

namespace Carmichael

theorem korselt (m : ℕ) (hm : 1 < m) (hcomp : ¬ m.Prime) :
    IsCarmichael m ↔
      Squarefree m ∧ ∀ p : ℕ, p.Prime → p ∣ m → (p - 1) ∣ (m - 1) := by
  have hme : m - 1 + 1 = m := by omega
  constructor
  · rintro ⟨-, -, hdvd⟩
    constructor
    · -- Squarefree: if `p * p ∣ m` then `p * p ∣ p ^ m - p = p * (p ^ (m - 1) - 1)`,
      -- so `p ∣ p ^ (m - 1) - 1`, contradicting `p ∣ p ^ (m - 1)`.
      rw [Nat.squarefree_iff_prime_squarefree]
      rintro p hp ⟨k, hk⟩
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hd : ((p : ℤ) * p) ∣ (m : ℤ) := by
        exact_mod_cast Int.natCast_dvd_natCast.mpr ⟨k, hk⟩
      have h1 : ((p : ℤ) * p) ∣ (p : ℤ) ^ m - p := hd.trans (hdvd (p : ℤ))
      have hfac : (p : ℤ) ^ m - p = p * ((p : ℤ) ^ (m - 1) - 1) := by
        rw [mul_sub, mul_one, ← pow_succ', hme]
      rw [hfac] at h1
      have h2 : (p : ℤ) ∣ (p : ℤ) ^ (m - 1) - 1 :=
        (mul_dvd_mul_iff_left hpz).mp h1
      have h3 : (p : ℤ) ∣ (p : ℤ) ^ (m - 1) :=
        dvd_pow_self _ (by omega : m - 1 ≠ 0)
      have h4 : (p : ℤ) ∣ 1 := by
        have := dvd_sub h3 h2
        simpa using this
      have h5 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos h4
      have h6 : 2 ≤ p := hp.two_le
      omega
    · -- Divisibility: take a generator `g` of `(ZMod p)ˣ`; from `g ^ m = g`
      -- deduce `g ^ (m - 1) = 1`, so `p - 1 = orderOf g ∣ m - 1`.
      intro p hp hpm
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
      have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
          Nat.totient_prime hp]
      rw [hcard] at hg
      obtain ⟨a, hae⟩ := ZMod.intCast_surjective ((g : ZMod p))
      have h1 : (p : ℤ) ∣ a ^ m - a :=
        (Int.natCast_dvd_natCast.mpr hpm).trans (hdvd a)
      have h2 : ((a ^ m - a : ℤ) : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h1
      push_cast at h2
      rw [sub_eq_zero, hae] at h2
      have h4 : g ^ m = g := by
        apply Units.ext
        rwa [Units.val_pow_eq_pow_val]
      have h5 : g ^ (m - 1) = 1 := by
        have h6 : g ^ (m - 1) * g = 1 * g := by
          rw [one_mul, ← pow_succ, hme, h4]
        exact mul_right_cancel h6
      rw [← hg]
      exact orderOf_dvd_of_pow_eq_one h5
  · -- Sufficiency: for each prime `p ∣ m`, Fermat's little theorem together
    -- with `p - 1 ∣ m - 1` gives `p ∣ a ^ m - a`; then the product of the
    -- (distinct) prime factors, which is `m` by squarefreeness, divides too.
    rintro ⟨hsf, hdiv⟩
    refine ⟨hm, hcomp, fun a => ?_⟩
    have hkey : ∀ p ∈ m.primeFactors, (p : ℤ) ∣ a ^ m - a := by
      intro p hp'
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp'
      have hpm : p ∣ m := Nat.dvd_of_mem_primeFactors hp'
      have : Fact p.Prime := ⟨hp⟩
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [sub_eq_zero]
      by_cases h0 : (a : ZMod p) = 0
      · rw [h0]
        exact zero_pow (by omega : m ≠ 0)
      · obtain ⟨t, ht⟩ := hdiv p hp hpm
        have hf : (a : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h0
        calc (a : ZMod p) ^ m = (a : ZMod p) ^ (m - 1) * a := by
              rw [← pow_succ, hme]
          _ = ((a : ZMod p) ^ (p - 1)) ^ t * a := by rw [← pow_mul, ← ht]
          _ = (a : ZMod p) := by rw [hf, one_pow, one_mul]
    have hprod : (∏ p ∈ m.primeFactors, p) ∣ (a ^ m - a).natAbs := by
      refine Finset.prod_primes_dvd _
        (fun p hp => Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors hp))
        (fun p hp => ?_)
      exact Int.natCast_dvd.mp (hkey p hp)
    rw [Nat.prod_primeFactors_of_squarefree hsf] at hprod
    exact Int.natCast_dvd.mpr hprod

end Carmichael
