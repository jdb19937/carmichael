/-
Brun–Titchmarsh for the arithmetic progression `1 mod m`.

For `2 ≤ m` and `m ≤ y^{19/20}` with `y` above an absolute threshold,

  `#{p ≤ y : p prime, p ≡ 1 (mod m)} ≤ 3·y / (φ(m)·log(y/m))`.

The proof applies the fundamental theorem of the Selberg sieve
(`Carmichael.selberg_bound`, see `Carmichael/SelbergBound.lean`) to the
progression `{n ≤ y : n ≡ 1 (mod m)}`, sifted by the primes `p ≤ z`, `p ∤ m`,
where `z = ⌊(y/m)^{2/5}⌋`.  The three analytic inputs are:

* remainders: by CRT the count of `n ≤ y` with `n ≡ 1 (mod m)`, `d ∣ n` is
  within `1` of `y/(dm)` for every squarefree `d` coprime to `m`, so
  `|R_d| ≤ 1`;
* error sum: `∑_{d ∣ P, d ≤ D} 3^{ω(d)} ≤ D·(1 + log D)²`, via the
  injection of pairs of divisors with lcm `d` into triples `(a,b,g)` with
  `abg = d ≤ D` and the harmonic-sum bound;
* main term: the Selberg bounding sum satisfies
  `S ≥ ∑_{l ≤ z, (l,m)=1} 1/φ(l) ≥ ∑_{j ≤ z, (j,m)=1} 1/j ≥ (φ(m)/m)·log z`,
  by the completely multiplicative inflation `1/φ(l) ≥ ∑_{rad j = l} 1/j`
  and the smooth/coprime factorisation of the harmonic sum.

With `log z ≥ (5/14)·log(y/m)` the main term contributes at most
`(14/5)·y/(φ(m)·log(y/m))` and everything else at most `(1/5)` of the same,
for the constant `3`.
-/
import Mathlib
import Carmichael.TwinSieve

set_option autoImplicit false

namespace Carmichael

noncomputable section

open Finset Nat ArithmeticFunction BoundingSieve

open scoped ArithmeticFunction.omega

/-! ### The coprime harmonic sum

For `K ≠ 0` and `w ≥ 1`, `∑_{i ≤ w, (i,K)=1} 1/i ≥ (φ(K)/K)·log w`: every
`n ≤ w` factors as its `K`-smooth part times a part coprime to `K`, the
smooth harmonic sum is at most the Euler product `K/φ(K)`, and the full
harmonic sum dominates `log w`.  This generalises the modulus-`2m` version
in `Carmichael/TwinSieve.lean`. -/

/-- The `K`-smooth part of `n`: the largest divisor of `n` all of whose
prime factors divide `K`. -/
def smoothPartM (K n : ℕ) : ℕ := ∏ p ∈ K.primeFactors, p ^ n.factorization p

lemma smoothPartM_ne_zero (K n : ℕ) : smoothPartM K n ≠ 0 := by
  rw [smoothPartM]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

lemma smoothPartM_dvd (K : ℕ) {n : ℕ} (hn : n ≠ 0) : smoothPartM K n ∣ n := by
  have hQ : ∀ p ∈ K.primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  rw [← Nat.factorization_le_iff_dvd (smoothPartM_ne_zero K n) hn, Finsupp.le_def]
  intro q
  rw [smoothPartM, factorization_prod_pow_apply _ hQ]
  split_ifs
  · exact le_refl _
  · exact Nat.zero_le _

lemma smoothPartM_primeFactors_subset (K n : ℕ) :
    (smoothPartM K n).primeFactors ⊆ K.primeFactors := by
  intro q hq
  have h0 : (smoothPartM K n).factorization q ≠ 0 := by
    rw [← Nat.support_factorization] at hq
    exact Finsupp.mem_support_iff.mp hq
  rw [smoothPartM, factorization_prod_pow_apply _
    (fun p hp => Nat.prime_of_mem_primeFactors hp)] at h0
  by_contra hc
  rw [if_neg hc] at h0
  exact h0 rfl

lemma coprime_div_smoothPartM {K : ℕ} (hK : K ≠ 0) {n : ℕ} (hn : n ≠ 0) :
    Nat.Coprime (n / smoothPartM K n) K := by
  have hQ : ∀ p ∈ K.primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  have hdvd := smoothPartM_dvd K hn
  have hb0 : n / smoothPartM K n ≠ 0 := by
    have h1 : smoothPartM K n ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    have h2 := Nat.div_pos h1 (Nat.pos_of_ne_zero (smoothPartM_ne_zero K n))
    omega
  apply Nat.coprime_of_dvd
  intro k hk hkdvd hkK
  have hkQ : k ∈ K.primeFactors := Nat.mem_primeFactors.mpr ⟨hk, hkK, hK⟩
  have hfact : (n / smoothPartM K n).factorization k = 0 := by
    rw [Nat.factorization_div hdvd, Finsupp.tsub_apply, smoothPartM,
      factorization_prod_pow_apply _ hQ, if_pos hkQ]
    omega
  have := hk.factorization_pos_of_dvd hb0 hkdvd
  omega

/-- The integers in `[1, w]` coprime to `K`. -/
def coprimeSetM (K w : ℕ) : Finset ℕ :=
  (Icc 1 w).filter (fun i => Nat.Coprime i K)

lemma mem_coprimeSetM {K w i : ℕ} :
    i ∈ coprimeSetM K w ↔ (1 ≤ i ∧ i ≤ w) ∧ Nat.Coprime i K := by
  rw [coprimeSetM, mem_filter, mem_Icc]

/-- The coprime harmonic sum is at least `(φ(K)/K)·log w`. -/
lemma coprime_harmonic_geM {K : ℕ} (hK : K ≠ 0) {w : ℕ} (hw : 1 ≤ w) :
    (Nat.totient K : ℝ) / (K : ℝ) * Real.log w
      ≤ ∑ i ∈ coprimeSetM K w, (i : ℝ)⁻¹ := by
  classical
  set Q := K.primeFactors with hQdef
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  set A := (Icc 1 w).filter (fun a => a.primeFactors ⊆ Q) with hA
  set Lsum := ∑ i ∈ coprimeSetM K w, (i : ℝ)⁻¹ with hLsum
  have hLnonneg : 0 ≤ Lsum := Finset.sum_nonneg fun i _ => by positivity
  -- (i) the harmonic sum factors through smooth × coprime pairs
  have hkey : ∑ n ∈ Icc 1 w, (n : ℝ)⁻¹ ≤ (∑ a ∈ A, (a : ℝ)⁻¹) * Lsum := by
    have hφmem : ∀ n ∈ Icc 1 w,
        (smoothPartM K n, n / smoothPartM K n) ∈ A ×ˢ coprimeSetM K w := by
      intro n hn
      obtain ⟨hn1, hnw⟩ := mem_Icc.mp hn
      have hn0 : n ≠ 0 := by omega
      have hdvd := smoothPartM_dvd K hn0
      rw [Finset.mem_product]
      constructor
      · rw [hA, mem_filter, mem_Icc]
        refine ⟨⟨Nat.pos_of_ne_zero (smoothPartM_ne_zero K n),
          le_trans (Nat.le_of_dvd (by omega) hdvd) hnw⟩,
          smoothPartM_primeFactors_subset K n⟩
      · rw [mem_coprimeSetM]
        have hbdvd : n / smoothPartM K n ∣ n := Nat.div_dvd_of_dvd hdvd
        have hb0 : n / smoothPartM K n ≠ 0 := by
          have h1 : smoothPartM K n ≤ n := Nat.le_of_dvd (by omega) hdvd
          have h2 := Nat.div_pos h1 (Nat.pos_of_ne_zero (smoothPartM_ne_zero K n))
          omega
        exact ⟨⟨Nat.pos_of_ne_zero hb0,
          le_trans (Nat.le_of_dvd (by omega) hbdvd) hnw⟩,
          coprime_div_smoothPartM hK hn0⟩
    have hinj : ∀ n₁ ∈ Icc 1 w, ∀ n₂ ∈ Icc 1 w,
        (smoothPartM K n₁, n₁ / smoothPartM K n₁)
          = (smoothPartM K n₂, n₂ / smoothPartM K n₂) → n₁ = n₂ := by
      intro n₁ h₁ n₂ h₂ he
      have hn₁ : n₁ ≠ 0 := by have := (mem_Icc.mp h₁).1; omega
      have hn₂ : n₂ ≠ 0 := by have := (mem_Icc.mp h₂).1; omega
      have e1 : smoothPartM K n₁ = smoothPartM K n₂ := congrArg Prod.fst he
      have e2 : n₁ / smoothPartM K n₁ = n₂ / smoothPartM K n₂ := congrArg Prod.snd he
      calc n₁ = smoothPartM K n₁ * (n₁ / smoothPartM K n₁) :=
            (Nat.mul_div_cancel' (smoothPartM_dvd K hn₁)).symm
        _ = smoothPartM K n₂ * (n₂ / smoothPartM K n₂) := by rw [e2, e1]
        _ = n₂ := Nat.mul_div_cancel' (smoothPartM_dvd K hn₂)
    calc ∑ n ∈ Icc 1 w, (n : ℝ)⁻¹
        = ∑ n ∈ Icc 1 w, ((smoothPartM K n : ℕ) : ℝ)⁻¹
            * ((n / smoothPartM K n : ℕ) : ℝ)⁻¹ := by
          refine sum_congr rfl fun n hn => ?_
          have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
          rw [← mul_inv, ← Nat.cast_mul,
            Nat.mul_div_cancel' (smoothPartM_dvd K hn0)]
      _ = ∑ q ∈ (Icc 1 w).image (fun n => (smoothPartM K n, n / smoothPartM K n)),
            ((q.1 : ℕ) : ℝ)⁻¹ * ((q.2 : ℕ) : ℝ)⁻¹ := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ q ∈ A ×ˢ coprimeSetM K w, ((q.1 : ℕ) : ℝ)⁻¹ * ((q.2 : ℕ) : ℝ)⁻¹ := by
          apply sum_le_sum_of_subset_of_nonneg
          · rw [Finset.image_subset_iff]
            exact hφmem
          · intro q _ _
            positivity
      _ = (∑ a ∈ A, (a : ℝ)⁻¹) * Lsum := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_product' _ _ (fun i j : ℕ => ((i : ℕ) : ℝ)⁻¹ * ((j : ℕ) : ℝ)⁻¹)
  -- (ii) the smooth sum is bounded by the Euler product
  have hAle : ∑ a ∈ A, (a : ℝ)⁻¹ ≤ ∏ p ∈ Q, (1 - (p : ℝ)⁻¹)⁻¹ := by
    refine le_trans (sum_le_prod_sum_pow Q (range (w + 1))
      (fun n : ℕ => (n : ℝ)⁻¹) (fun n => by positivity) (by simp)
      (fun a b => by push_cast; rw [mul_inv]) A ?_ ?_ ?_) ?_
    · intro a ha
      have := (mem_Icc.mp (mem_filter.mp ha).1).1
      omega
    · intro a ha
      exact (mem_filter.mp ha).2
    · intro a ha p _
      have ha0 : a ≠ 0 := by
        have := (mem_Icc.mp (mem_filter.mp ha).1).1
        omega
      have haw := (mem_Icc.mp (mem_filter.mp ha).1).2
      rw [mem_range]
      have := Nat.factorization_lt p ha0
      omega
    · apply Finset.prod_le_prod
      · intro p _
        exact Finset.sum_nonneg fun k _ => by positivity
      · intro p hp
        have hp2 : 2 ≤ p := (hQp p hp).two_le
        have hp0 : (0 : ℝ) < (p : ℝ) := by
          have : 0 < p := by omega
          exact_mod_cast this
        have hx1 : ((p : ℝ))⁻¹ < 1 := by
          rw [inv_lt_one₀ hp0]
          exact_mod_cast (by omega : 1 < p)
        calc ∑ k ∈ range (w + 1), (((p ^ k : ℕ) : ℝ))⁻¹
            = ∑ k ∈ range (w + 1), ((p : ℝ)⁻¹) ^ k := by
              refine sum_congr rfl fun k _ => ?_
              rw [Nat.cast_pow, inv_pow]
          _ ≤ (1 - (p : ℝ)⁻¹)⁻¹ := geom_sum_range_le (by positivity) hx1 _
  -- (iii) the Euler product is `(φ(K)/K)⁻¹`
  have hprod : ∏ p ∈ Q, (1 - (p : ℝ)⁻¹)⁻¹
      = ((Nat.totient K : ℝ) / (K : ℝ))⁻¹ := by
    rw [Finset.prod_inv_distrib, prod_one_sub_inv_primeFactors hK]
  -- (iv) the harmonic sum dominates the logarithm
  have hHw : Real.log w ≤ ∑ n ∈ Icc 1 w, (n : ℝ)⁻¹ := by
    have h1 : ∑ n ∈ Icc 1 w, (n : ℝ)⁻¹ = ((harmonic w : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    rw [h1]
    have h2 := log_le_harmonic_floor (w : ℝ) (by positivity)
    rwa [Nat.floor_natCast] at h2
  -- combine
  have hφpos : (0 : ℝ) < (Nat.totient K : ℝ) / (K : ℝ) := by
    have h1 : 0 < Nat.totient K := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hK)
    have h2 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hK
    have h3 : (0 : ℝ) < (Nat.totient K : ℝ) := by exact_mod_cast h1
    positivity
  have hHL : ∑ n ∈ Icc 1 w, (n : ℝ)⁻¹
      ≤ ((Nat.totient K : ℝ) / (K : ℝ))⁻¹ * Lsum := by
    calc ∑ n ∈ Icc 1 w, (n : ℝ)⁻¹ ≤ (∑ a ∈ A, (a : ℝ)⁻¹) * Lsum := hkey
      _ ≤ ((Nat.totient K : ℝ) / (K : ℝ))⁻¹ * Lsum :=
          mul_le_mul_of_nonneg_right (hAle.trans_eq hprod) hLnonneg
  calc (Nat.totient K : ℝ) / (K : ℝ) * Real.log w
      ≤ (Nat.totient K : ℝ) / (K : ℝ)
          * (((Nat.totient K : ℝ) / (K : ℝ))⁻¹ * Lsum) :=
        mul_le_mul_of_nonneg_left (le_trans hHw hHL) hφpos.le
    _ = Lsum := by
        rw [← mul_assoc, mul_inv_cancel₀ hφpos.ne', one_mul]

/-! ### The `3^ω` divisor-sum bound

`∑_{d ∣ P, d ≤ D} 3^{ω(d)} ≤ D·(1 + log D)²`: for squarefree `d`, `3^{ω(d)}`
counts the pairs of divisors of `d` with lcm `d`, and the pair `(d1, d2)`
with `g = gcd(d1, d2)` maps injectively to the triple
`(d1/g, d2/g, g)` whose product is `d ≤ D`. -/

/-- For squarefree `d`, `3^{ω(d)}` counts the pairs of divisors with
lcm equal to `d`. -/
lemma three_pow_omega_eq_card {d : ℕ} (hd : Squarefree d) :
    ((#((d.divisors ×ˢ d.divisors).filter
        (fun q : ℕ × ℕ => d = q.1.lcm q.2)) : ℕ) : ℝ) = (3 : ℝ) ^ ω d := by
  classical
  rw [← Finset.sum_boole, Finset.sum_product' d.divisors d.divisors
    (fun d1 d2 : ℕ => if d = d1.lcm d2 then (1 : ℝ) else 0)]
  exact sum_sum_ite_lcm_eq hd

set_option maxHeartbeats 1000000 in
/-- The divisor-bounded `3^ω` sum over the divisors of a squarefree number:
`∑_{d ∣ P, d ≤ D} 3^{ω(d)} ≤ D·(1 + log D)²`. -/
lemma sum_three_pow_omega_le {P : ℕ} (hP : Squarefree P) (D : ℕ) (hD : 1 ≤ D) :
    ∑ d ∈ P.divisors.filter (fun d => d ≤ D), (3 : ℝ) ^ ω d
      ≤ (D : ℝ) * (1 + Real.log D) ^ 2 := by
  classical
  -- convert the sum to the cardinality of a sigma set of (divisor, pair)s
  have hcard : ∑ d ∈ P.divisors.filter (fun d => d ≤ D), (3 : ℝ) ^ ω d
      = (((P.divisors.filter (fun d => d ≤ D)).sigma
          (fun d => (d.divisors ×ˢ d.divisors).filter
            (fun q : ℕ × ℕ => d = q.1.lcm q.2))).card : ℝ) := by
    rw [Finset.card_sigma, Nat.cast_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    exact (three_pow_omega_eq_card
      (hP.squarefree_of_dvd (dvd_of_mem_divisors (mem_filter.mp hd).1))).symm
  rw [hcard]
  -- inject into triples (a, b, g) with a*b*g ≤ D
  have hinj : ((P.divisors.filter (fun d => d ≤ D)).sigma
      (fun d => (d.divisors ×ˢ d.divisors).filter
        (fun q : ℕ × ℕ => d = q.1.lcm q.2))).card
      ≤ (((Icc 1 D) ×ˢ (Icc 1 D)).sigma
          (fun ab : ℕ × ℕ => Icc 1 (D / (ab.1 * ab.2)))).card := by
    apply Finset.card_le_card_of_injOn
      (fun x : (_ : ℕ) × ℕ × ℕ =>
        (⟨(x.2.1 / x.2.1.gcd x.2.2, x.2.2 / x.2.1.gcd x.2.2),
          x.2.1.gcd x.2.2⟩ : (_ : ℕ × ℕ) × ℕ))
    · -- maps into the target
      rintro ⟨d, d1, d2⟩ hx
      rw [Finset.mem_coe, Finset.mem_sigma] at hx
      obtain ⟨hdF, hq⟩ := hx
      rw [mem_filter] at hdF
      obtain ⟨hdmem, hdD⟩ := hdF
      rw [mem_filter, Finset.mem_product] at hq
      obtain ⟨⟨hq1, hq2⟩, hlcm⟩ := hq
      have hd0 : 0 < d := Nat.pos_of_mem_divisors hdmem
      have hd1pos : 0 < d1 := Nat.pos_of_mem_divisors hq1
      have hd2pos : 0 < d2 := Nat.pos_of_mem_divisors hq2
      have hg0 : 0 < d1.gcd d2 := Nat.gcd_pos_of_pos_left d2 hd1pos
      have hga : d1.gcd d2 * (d1 / d1.gcd d2) = d1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hgb : d1.gcd d2 * (d2 / d1.gcd d2) = d2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have hkey : d1 / d1.gcd d2 * (d2 / d1.gcd d2) * d1.gcd d2 = d := by
        apply Nat.eq_of_mul_eq_mul_left hg0
        calc d1.gcd d2 * (d1 / d1.gcd d2 * (d2 / d1.gcd d2) * d1.gcd d2)
            = (d1.gcd d2 * (d1 / d1.gcd d2)) * (d1.gcd d2 * (d2 / d1.gcd d2)) := by
              ring
          _ = d1 * d2 := by rw [hga, hgb]
          _ = d1.gcd d2 * d1.lcm d2 := (Nat.gcd_mul_lcm d1 d2).symm
          _ = d1.gcd d2 * d := by rw [← hlcm]
      have hapos : 0 < d1 / d1.gcd d2 :=
        Nat.div_pos (Nat.le_of_dvd hd1pos (Nat.gcd_dvd_left _ _)) hg0
      have hbpos : 0 < d2 / d1.gcd d2 :=
        Nat.div_pos (Nat.le_of_dvd hd2pos (Nat.gcd_dvd_right _ _)) hg0
      have haD : d1 / d1.gcd d2 ≤ D := by
        calc d1 / d1.gcd d2 ≤ d1 := Nat.div_le_self _ _
          _ ≤ d := Nat.le_of_dvd hd0 (dvd_of_mem_divisors hq1)
          _ ≤ D := hdD
      have hbD : d2 / d1.gcd d2 ≤ D := by
        calc d2 / d1.gcd d2 ≤ d2 := Nat.div_le_self _ _
          _ ≤ d := Nat.le_of_dvd hd0 (dvd_of_mem_divisors hq2)
          _ ≤ D := hdD
      rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_product]
      refine ⟨⟨mem_Icc.mpr ⟨hapos, haD⟩, mem_Icc.mpr ⟨hbpos, hbD⟩⟩, ?_⟩
      rw [mem_Icc]
      refine ⟨hg0, ?_⟩
      rw [Nat.le_div_iff_mul_le (Nat.mul_pos hapos hbpos)]
      calc d1.gcd d2 * (d1 / d1.gcd d2 * (d2 / d1.gcd d2))
          = d1 / d1.gcd d2 * (d2 / d1.gcd d2) * d1.gcd d2 := by ring
        _ = d := hkey
        _ ≤ D := hdD
    · -- injective on the sigma set
      rintro ⟨d, d1, d2⟩ hx ⟨e, e1, e2⟩ hy hxy
      rw [Finset.mem_coe, Finset.mem_sigma] at hx hy
      obtain ⟨-, hqx⟩ := hx
      obtain ⟨-, hqy⟩ := hy
      rw [mem_filter] at hqx hqy
      have hlcmx : d = d1.lcm d2 := hqx.2
      have hlcmy : e = e1.lcm e2 := hqy.2
      simp only [Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq] at hxy
      obtain ⟨⟨ha, hb⟩, hg⟩ := hxy
      have hgax : d1.gcd d2 * (d1 / d1.gcd d2) = d1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hgbx : d1.gcd d2 * (d2 / d1.gcd d2) = d2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have hgay : e1.gcd e2 * (e1 / e1.gcd e2) = e1 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
      have hgby : e1.gcd e2 * (e2 / e1.gcd e2) = e2 :=
        Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
      have h1 : d1 = e1 := by rw [← hgax, ha, hg, hgay]
      have h2 : d2 = e2 := by rw [← hgbx, hb, hg, hgby]
      subst h1
      subst h2
      have h3 : d = e := by rw [hlcmx, hlcmy]
      subst h3
      rfl
  -- count the triples
  have htarget : (((((Icc 1 D) ×ˢ (Icc 1 D)).sigma
      (fun ab : ℕ × ℕ => Icc 1 (D / (ab.1 * ab.2)))).card : ℕ) : ℝ)
      ≤ (D : ℝ) * (∑ a ∈ Icc 1 D, (a : ℝ)⁻¹) ^ 2 := by
    rw [Finset.card_sigma, Nat.cast_sum]
    have hstep : ∀ ab ∈ (Icc 1 D) ×ˢ (Icc 1 D),
        ((#(Icc 1 (D / (ab.1 * ab.2))) : ℕ) : ℝ)
          ≤ (D : ℝ) * ((ab.1 : ℝ)⁻¹ * (ab.2 : ℝ)⁻¹) := by
      intro ab hab
      rw [Finset.mem_product, mem_Icc, mem_Icc] at hab
      have ha1 : 1 ≤ ab.1 := hab.1.1
      have hb1 : 1 ≤ ab.2 := hab.2.1
      have h1 : (0 : ℝ) < (ab.1 : ℝ) := by exact_mod_cast (by omega : 0 < ab.1)
      have h2 : (0 : ℝ) < (ab.2 : ℝ) := by exact_mod_cast (by omega : 0 < ab.2)
      rw [Nat.card_Icc, Nat.add_sub_cancel]
      calc ((D / (ab.1 * ab.2) : ℕ) : ℝ)
          ≤ (D : ℝ) / ((ab.1 * ab.2 : ℕ) : ℝ) := Nat.cast_div_le
        _ = (D : ℝ) * ((ab.1 : ℝ)⁻¹ * (ab.2 : ℝ)⁻¹) := by
            push_cast
            rw [div_eq_mul_inv, mul_inv]
    calc ∑ ab ∈ (Icc 1 D) ×ˢ (Icc 1 D), ((#(Icc 1 (D / (ab.1 * ab.2))) : ℕ) : ℝ)
        ≤ ∑ ab ∈ (Icc 1 D) ×ˢ (Icc 1 D), (D : ℝ) * ((ab.1 : ℝ)⁻¹ * (ab.2 : ℝ)⁻¹) :=
          Finset.sum_le_sum hstep
      _ = (D : ℝ) * (∑ a ∈ Icc 1 D, (a : ℝ)⁻¹) ^ 2 := by
          rw [← Finset.mul_sum, sq, Finset.sum_mul_sum]
          congr 1
          exact Finset.sum_product' _ _ (fun i j : ℕ => (i : ℝ)⁻¹ * (j : ℝ)⁻¹)
  -- the harmonic bound
  have hH : ∑ a ∈ Icc 1 D, (a : ℝ)⁻¹ ≤ 1 + Real.log D := by
    have h1 : ∑ a ∈ Icc 1 D, (a : ℝ)⁻¹ = ((harmonic D : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    rw [h1]
    exact_mod_cast harmonic_le_one_add_log D
  have hHnonneg : 0 ≤ ∑ a ∈ Icc 1 D, (a : ℝ)⁻¹ :=
    Finset.sum_nonneg fun a _ => by positivity
  calc (((P.divisors.filter (fun d => d ≤ D)).sigma
      (fun d => (d.divisors ×ˢ d.divisors).filter
        (fun q : ℕ × ℕ => d = q.1.lcm q.2))).card : ℝ)
      ≤ ((((Icc 1 D) ×ˢ (Icc 1 D)).sigma
          (fun ab : ℕ × ℕ => Icc 1 (D / (ab.1 * ab.2)))).card : ℝ) := by
        exact_mod_cast hinj
    _ ≤ (D : ℝ) * (∑ a ∈ Icc 1 D, (a : ℝ)⁻¹) ^ 2 := htarget
    _ ≤ (D : ℝ) * (1 + Real.log D) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ hHnonneg hH 2

/-! ### The progression sieve -/

/-- The sifting primes: `p ≤ z`, `p` prime, `p ∤ m`. -/
def progPrimeSet (m z : ℕ) : Finset ℕ :=
  (range (z + 1)).filter (fun p => p.Prime ∧ ¬p ∣ m)

/-- The product of the sifting primes. -/
def progProdPrimes (m z : ℕ) : ℕ := ∏ p ∈ progPrimeSet m z, p

lemma mem_progPrimeSet {m z p : ℕ} :
    p ∈ progPrimeSet m z ↔ p ≤ z ∧ p.Prime ∧ ¬p ∣ m := by
  rw [progPrimeSet, mem_filter, mem_range, Nat.lt_succ_iff]

lemma progPrimeSet_prime {m z p : ℕ} (hp : p ∈ progPrimeSet m z) : p.Prime :=
  (mem_progPrimeSet.mp hp).2.1

lemma progProdPrimes_squarefree (m z : ℕ) : Squarefree (progProdPrimes m z) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => ?_) fun p hp => (progPrimeSet_prime hp).squarefree
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (progPrimeSet_prime hp) (progPrimeSet_prime hq)).mpr hpq

lemma mem_progPrimeSet_of_dvd {m z p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ progProdPrimes m z) : p ∈ progPrimeSet m z := by
  rw [progProdPrimes] at hdvd
  obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd hdvd
  rwa [Nat.prime_dvd_prime_iff_eq hp (progPrimeSet_prime hq) |>.mp hpq]

/-- The Selberg sieve for the progression `1 mod m`: support
`{n ∈ [1, y] : n ≡ 1 (mod m)}`, sifting primes `p ≤ z` with `p ∤ m`,
density `ν(d) = 1/d`, total mass `y/m`, level `z²`. -/
def progSieve (m z y : ℕ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Icc 1 y).filter (fun n => n % m = 1 % m)
  prodPrimes := progProdPrimes m z
  prodPrimes_squarefree := progProdPrimes_squarefree m z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := (y : ℝ) / m
  nu := ArithmeticFunction.prodPrimeFactors (fun p => (p : ℝ)⁻¹)
  nu_mult := by arith_mult
  nu_pos_of_prime := by
    intro p hp _
    rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
      Finset.prod_singleton]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  nu_lt_one_of_prime := by
    intro p hp _
    rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
      Finset.prod_singleton]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    rw [inv_lt_one₀ (by linarith)]
    exact hp1
  level := ((z : ℕ) : ℝ) ^ 2
  one_le_level := by
    have : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    nlinarith

variable {m z y : ℕ}

@[simp] lemma progSieve_level (hz : 1 ≤ z) :
    (progSieve m z y hz).level = ((z : ℕ) : ℝ) ^ 2 := rfl

@[simp] lemma progSieve_totalMass (hz : 1 ≤ z) :
    (progSieve m z y hz).totalMass = (y : ℝ) / m := rfl

@[simp] lemma progSieve_prodPrimes (hz : 1 ≤ z) :
    (progSieve m z y hz).prodPrimes = progProdPrimes m z := rfl

lemma progSieve_nu_apply_prime (hz : 1 ≤ z) {p : ℕ} (hp : p.Prime) :
    (progSieve m z y hz).nu p = (p : ℝ)⁻¹ := by
  show (ArithmeticFunction.prodPrimeFactors (fun p => (p : ℝ)⁻¹)) p = (p : ℝ)⁻¹
  rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
    Finset.prod_singleton]

/-- On squarefree divisors of the sifting product, `ν(d) = 1/d`. -/
lemma progSieve_nu_eq (hz : 1 ≤ z) {d : ℕ} (hd : d ∣ progProdPrimes m z) :
    (progSieve m z y hz).nu d = ((d : ℕ) : ℝ)⁻¹ := by
  have hsq : Squarefree d := (progProdPrimes_squarefree m z).squarefree_of_dvd hd
  have h1 : ∏ p ∈ d.primeFactors, (progSieve m z y hz).nu p
      = (progSieve m z y hz).nu d :=
    prod_primeFactors_nu (s := (progSieve m z y hz).toBoundingSieve) hd
  rw [← h1]
  have h2 : ∀ p ∈ d.primeFactors, (progSieve m z y hz).nu p = (p : ℝ)⁻¹ := by
    intro p hp
    exact progSieve_nu_apply_prime hz (Nat.prime_of_mem_primeFactors hp)
  rw [Finset.prod_congr rfl h2, Finset.prod_inv_distrib, ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree hsq]

lemma progSieve_multSum (hz : 1 ≤ z) (d : ℕ) :
    (progSieve m z y hz).multSum d
      = (#((Icc 1 y).filter (fun n => n % m = 1 % m ∧ d ∣ n)) : ℝ) := by
  classical
  show (∑ n ∈ (Icc 1 y).filter (fun n => n % m = 1 % m),
      if d ∣ n then (1 : ℝ) else 0) = _
  rw [Finset.sum_boole, Finset.filter_filter]

lemma progSieve_siftedSum (hz : 1 ≤ z) :
    (progSieve m z y hz).siftedSum
      = ∑ n ∈ (Icc 1 y).filter (fun n => n % m = 1 % m),
          if Nat.Coprime (progProdPrimes m z) n then (1 : ℝ) else 0 := rfl

/-! ### The remainder bound -/

/-- For `d` dividing the sifting product, the remainder of the progression
sieve is at most `1` in absolute value: by CRT the conditions `n ≡ 1 (mod m)`
and `d ∣ n` define a single residue class mod `dm`, whose count over `[1, y]`
is within `1` of `y/(dm)`. -/
lemma progSieve_abs_rem_le (hm2 : 2 ≤ m) (hz : 1 ≤ z) {d : ℕ}
    (hd : d ∣ progProdPrimes m z) :
    |(progSieve m z y hz).rem d| ≤ 1 := by
  classical
  have hsq : Squarefree d := (progProdPrimes_squarefree m z).squarefree_of_dvd hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero hsq.ne_zero
  have hm0 : 0 < m := by omega
  have hcop : Nat.Coprime d m := by
    apply Nat.coprime_of_dvd
    intro k hk hkd hkm
    have hkP : k ∣ progProdPrimes m z := hkd.trans hd
    exact (mem_progPrimeSet.mp (mem_progPrimeSet_of_dvd hk hkP)).2.2 hkm
  obtain ⟨x, hx0, hx1⟩ := Nat.chineseRemainder hcop 0 1
  have hdm0 : 0 < d * m := Nat.mul_pos hd0 hm0
  set r := x % (d * m) with hr
  have hrlt : r < d * m := Nat.mod_lt x hdm0
  have hiff : ∀ n : ℕ, ((n % m = 1 % m) ∧ d ∣ n) ↔ n % (d * m) = r := by
    intro n
    have h1 : (n % (d * m) = r) ↔ n ≡ x [MOD d * m] := by
      rw [hr]
      exact Iff.rfl
    rw [h1, ← Nat.modEq_and_modEq_iff_modEq_mul hcop]
    constructor
    · rintro ⟨hclass, hdvd⟩
      exact ⟨(Nat.modEq_zero_iff_dvd.mpr hdvd).trans hx0.symm,
        (show n ≡ 1 [MOD m] from hclass).trans hx1.symm⟩
    · rintro ⟨hnd, hnm⟩
      exact ⟨(hnm.trans hx1 : n ≡ 1 [MOD m]),
        Nat.modEq_zero_iff_dvd.mp (hnd.trans hx0)⟩
  have hcount : (progSieve m z y hz).multSum d
      = (#((Icc 1 y).filter (fun n => n % (d * m) = r)) : ℝ) := by
    rw [progSieve_multSum hz d]
    have hseteq : (Icc 1 y).filter (fun n => n % m = 1 % m ∧ d ∣ n)
        = (Icc 1 y).filter (fun n => n % (d * m) = r) := by
      ext n
      simp only [Finset.mem_filter]
      exact and_congr_right fun _ => hiff n
    rw [hseteq]
  have hnu : (progSieve m z y hz).nu d = ((d : ℕ) : ℝ)⁻¹ := progSieve_nu_eq hz hd
  have hrem : (progSieve m z y hz).rem d
      = (#((Icc 1 y).filter (fun n => n % (d * m) = r)) : ℝ)
          - (y : ℝ) / ((d * m : ℕ) : ℝ) := by
    rw [rem, hcount, hnu, progSieve_totalMass]
    congr 1
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
    push_cast
    field_simp
  rw [hrem]
  exact card_Icc_filter_mod y hdm0 hrlt

/-! ### Counting: the primes in the progression survive the sieve -/

/-- The count of primes `p ≤ y` with `p ≡ 1 (mod m)` is at most `z` plus the
sifted sum. -/
lemma prog_count_le_siftedSum_add (hz : 1 ≤ z) :
    ((#((range (y + 1)).filter (fun p => p.Prime ∧ p % m = 1 % m))) : ℝ)
      ≤ (progSieve m z y hz).siftedSum + z := by
  classical
  set T := (range (y + 1)).filter (fun p => p.Prime ∧ p % m = 1 % m) with hT
  set T' := T.filter (fun q => z < q) with hT'
  have hsplit : T ⊆ T' ∪ Icc 1 z := by
    intro q hq
    rcases le_or_gt q z with h | h
    · refine mem_union_right _ (mem_Icc.mpr ⟨?_, h⟩)
      have := (mem_filter.mp hq).2.1.two_le
      omega
    · exact mem_union_left _ (mem_filter.mpr ⟨hq, h⟩)
  have hcard : #T ≤ #T' + z := by
    calc #T ≤ #(T' ∪ Icc 1 z) := Finset.card_le_card hsplit
      _ ≤ #T' + #(Icc 1 z) := Finset.card_union_le _ _
      _ = #T' + z := by rw [Nat.card_Icc, Nat.add_sub_cancel]
  have hsurvive : (#T' : ℝ) ≤ (progSieve m z y hz).siftedSum := by
    rw [progSieve_siftedSum hz]
    have hone : ∀ q ∈ T',
        (if Nat.Coprime (progProdPrimes m z) q then (1 : ℝ) else 0) = 1 := by
      intro q hq
      rw [hT', mem_filter, hT, mem_filter] at hq
      obtain ⟨⟨hqr, hqp, hqm⟩, hqz⟩ := hq
      rw [if_pos]
      apply Nat.coprime_of_dvd
      intro k hk hkP hkq
      have hkz : k ≤ z := (mem_progPrimeSet.mp (mem_progPrimeSet_of_dvd hk hkP)).1
      have : k = q := (Nat.prime_dvd_prime_iff_eq hk hqp).mp hkq
      omega
    have hTsub : T' ⊆ (Icc 1 y).filter (fun n => n % m = 1 % m) := by
      intro q hq
      rw [hT', mem_filter, hT, mem_filter, mem_range] at hq
      obtain ⟨⟨hqr, hqp, hqm⟩, -⟩ := hq
      rw [mem_filter, mem_Icc]
      exact ⟨⟨hqp.pos, by omega⟩, hqm⟩
    calc (#T' : ℝ) = ∑ n ∈ T', (1 : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ n ∈ T', if Nat.Coprime (progProdPrimes m z) n then (1 : ℝ) else 0 :=
          (Finset.sum_congr rfl hone).symm
      _ ≤ ∑ n ∈ (Icc 1 y).filter (fun n => n % m = 1 % m),
            if Nat.Coprime (progProdPrimes m z) n then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hTsub
          intro q _ _
          positivity
  have hcast : (#T : ℝ) ≤ (#T' : ℝ) + z := by exact_mod_cast hcard
  linarith

/-! ### The error term -/

/-- The sieve error term is at most `z²·(1 + log z²)²`. -/
lemma progSieve_errSum_le (hm2 : 2 ≤ m) (hz : 1 ≤ z) :
    (∑ d ∈ divisors (progSieve m z y hz).prodPrimes,
      if (d : ℝ) ≤ (progSieve m z y hz).level then
        (3 : ℝ) ^ ω d * |(progSieve m z y hz).rem d| else 0)
      ≤ ((z ^ 2 : ℕ) : ℝ) * (1 + Real.log ((z ^ 2 : ℕ) : ℝ)) ^ 2 := by
  classical
  rw [show (progSieve m z y hz).prodPrimes = progProdPrimes m z from rfl]
  have hstep : ∀ d ∈ divisors (progProdPrimes m z),
      (if (d : ℝ) ≤ (progSieve m z y hz).level then
        (3 : ℝ) ^ ω d * |(progSieve m z y hz).rem d| else 0)
        ≤ (if d ≤ z ^ 2 then (3 : ℝ) ^ ω d else 0) := by
    intro d hd
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
    by_cases h : (d : ℝ) ≤ (progSieve m z y hz).level
    · have hd2 : d ≤ z ^ 2 := by
        have h' : (d : ℝ) ≤ ((z ^ 2 : ℕ) : ℝ) := by
          push_cast
          exact h
        exact_mod_cast h'
      rw [if_pos h, if_pos hd2]
      calc (3 : ℝ) ^ ω d * |(progSieve m z y hz).rem d|
          ≤ (3 : ℝ) ^ ω d * 1 :=
            mul_le_mul_of_nonneg_left (progSieve_abs_rem_le hm2 hz hdvd)
              (by positivity)
        _ = (3 : ℝ) ^ ω d := mul_one _
    · rw [if_neg h]
      split_ifs
      · positivity
      · exact le_refl 0
  calc (∑ d ∈ divisors (progProdPrimes m z),
      if (d : ℝ) ≤ (progSieve m z y hz).level then
        (3 : ℝ) ^ ω d * |(progSieve m z y hz).rem d| else 0)
      ≤ ∑ d ∈ divisors (progProdPrimes m z),
          if d ≤ z ^ 2 then (3 : ℝ) ^ ω d else 0 := Finset.sum_le_sum hstep
    _ = ∑ d ∈ (divisors (progProdPrimes m z)).filter (fun d => d ≤ z ^ 2),
          (3 : ℝ) ^ ω d := (Finset.sum_filter _ _).symm
    _ ≤ ((z ^ 2 : ℕ) : ℝ) * (1 + Real.log ((z ^ 2 : ℕ) : ℝ)) ^ 2 :=
        sum_three_pow_omega_le (progProdPrimes_squarefree m z) (z ^ 2)
          (Nat.one_le_pow _ _ (by omega))

/-! ### The lower bound for the Selberg bounding sum -/

lemma prog_primeFactors_subset {w j : ℕ} (hw : w ≤ z) (hj : j ∈ coprimeSetM m w) :
    j.primeFactors ⊆ progPrimeSet m z := by
  intro p hp
  obtain ⟨⟨hj1, hjw⟩, hcop⟩ := mem_coprimeSetM.mp hj
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpj := Nat.dvd_of_mem_primeFactors hp
  rw [mem_progPrimeSet]
  refine ⟨le_trans (le_trans (Nat.le_of_dvd (by omega) hpj) hjw) hw, hpp, ?_⟩
  intro hdvd
  have hgcd : p ∣ Nat.gcd j m := Nat.dvd_gcd hpj hdvd
  rw [Nat.Coprime] at hcop
  rw [hcop] at hgcd
  exact hpp.ne_one (Nat.dvd_one.mp hgcd)

/-- Each fiber sum of `1/j` over `rad j = l` is dominated by the Selberg
term `g(l) = ∏_{p ∣ l} (1/p)·(1 − 1/p)⁻¹ = 1/φ(l)`. -/
lemma prog_fiber_sum_le (hz : 1 ≤ z) {l : ℕ} (hl : l ∣ progProdPrimes m z) :
    ∑ j ∈ (coprimeSetM m z).filter (fun j => radd j = l), (j : ℝ)⁻¹
      ≤ (progSieve m z y hz).selbergTerms l := by
  have hlp : ∀ p ∈ l.primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  have h1 : ∑ j ∈ (coprimeSetM m z).filter (fun j => radd j = l), (j : ℝ)⁻¹
      ≤ ∏ p ∈ l.primeFactors, ∑ k ∈ Icc 1 z, ((p ^ k : ℕ) : ℝ)⁻¹ := by
    refine sum_le_prod_sum_pow l.primeFactors (Icc 1 z) (fun n : ℕ => (n : ℝ)⁻¹)
      (fun n => by positivity) (by simp) (fun a b => by push_cast; rw [mul_inv])
      ((coprimeSetM m z).filter (fun j => radd j = l)) ?_ ?_ ?_
    · intro j hj
      have := (mem_coprimeSetM.mp (mem_filter.mp hj).1).1.1
      omega
    · intro j hj
      obtain ⟨-, hrad⟩ := mem_filter.mp hj
      rw [← hrad, primeFactors_radd]
    · intro j hj p hp
      obtain ⟨hjJ, hrad⟩ := mem_filter.mp hj
      obtain ⟨⟨hj1, hjz⟩, -⟩ := mem_coprimeSetM.mp hjJ
      rw [← hrad, primeFactors_radd] at hp
      rw [mem_Icc]
      constructor
      · exact (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
          (by omega) (Nat.dvd_of_mem_primeFactors hp)
      · have := Nat.factorization_lt p (show j ≠ 0 by omega)
        omega
  have h2 : ∏ p ∈ l.primeFactors, ∑ k ∈ Icc 1 z, ((p ^ k : ℕ) : ℝ)⁻¹
      ≤ ∏ p ∈ l.primeFactors, (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹)⁻¹ := by
    apply Finset.prod_le_prod
    · intro p _
      exact Finset.sum_nonneg fun k _ => by positivity
    · intro p hp
      have hp2 : 2 ≤ p := (hlp p hp).two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by
        have : 0 < p := by omega
        exact_mod_cast this
      have hx1 : ((p : ℝ))⁻¹ < 1 := by
        rw [inv_lt_one₀ hp0]
        exact_mod_cast (by omega : 1 < p)
      calc ∑ k ∈ Icc 1 z, ((p ^ k : ℕ) : ℝ)⁻¹
          = ∑ k ∈ Icc 1 z, ((p : ℝ)⁻¹) ^ k := by
            refine sum_congr rfl fun k _ => ?_
            rw [Nat.cast_pow, inv_pow]
        _ ≤ (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹)⁻¹ := geom_sum_Icc_le (by positivity) hx1 z
  have h3 : (progSieve m z y hz).selbergTerms l
      = ∏ p ∈ l.primeFactors, (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [selbergTerms_apply,
      ← prod_primeFactors_nu (s := (progSieve m z y hz).toBoundingSieve) hl,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [progSieve_nu_apply_prime hz (hlp p hp)]
  rw [h3]
  exact le_trans h1 h2

/-- The Selberg bounding sum dominates the coprime harmonic sum up to `z`. -/
lemma prog_sum_inv_le_boundingSum (hz : 1 ≤ z) :
    ∑ j ∈ coprimeSetM m z, (j : ℝ)⁻¹
      ≤ selbergBoundingSum (progSieve m z y hz) := by
  have hP0 : progProdPrimes m z ≠ 0 := (progProdPrimes_squarefree m z).ne_zero
  have hmaps : ∀ j ∈ coprimeSetM m z, radd j ∈ divisors (progProdPrimes m z) := by
    intro j hj
    rw [Nat.mem_divisors]
    exact ⟨Finset.prod_dvd_prod_of_subset _ _ _
      (prog_primeFactors_subset le_rfl hj), hP0⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun j : ℕ => (j : ℝ)⁻¹)]
  apply Finset.sum_le_sum
  intro l hl
  obtain ⟨hldvd, -⟩ := Nat.mem_divisors.mp hl
  by_cases hcond : ((l : ℕ) : ℝ) ^ 2 ≤ (progSieve m z y hz).level
  · rw [if_pos hcond]
    exact prog_fiber_sum_le hz hldvd
  · rw [if_neg hcond]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro j hj
    exfalso
    apply hcond
    obtain ⟨hjJ, hrad⟩ := mem_filter.mp hj
    obtain ⟨⟨hj1, hjz⟩, -⟩ := mem_coprimeSetM.mp hjJ
    have hlz : l ≤ z := by
      have h1 : radd j ≤ j := Nat.le_of_dvd (by omega) (radd_dvd_self j)
      omega
    rw [progSieve_level]
    have h2 : ((l : ℕ) : ℝ) ≤ ((z : ℕ) : ℝ) := by exact_mod_cast hlz
    have hl0 : (0 : ℝ) ≤ ((l : ℕ) : ℝ) := by positivity
    exact pow_le_pow_left₀ hl0 h2 2

/-- **The lower bound for the Selberg bounding sum**:
`S ≥ (φ(m)/m)·log z`. -/
lemma progSieve_boundingSum_ge (hm : m ≠ 0) (hz : 1 ≤ z) :
    (Nat.totient m : ℝ) / (m : ℝ) * Real.log z
      ≤ selbergBoundingSum (progSieve m z y hz) :=
  le_trans (coprime_harmonic_geM hm hz) (prog_sum_inv_le_boundingSum hz)

/-! ### Final assembly -/

set_option maxHeartbeats 4000000 in
/-- **Brun–Titchmarsh for the progression `1 mod m`.**  For `2 ≤ m` with
`m ≤ y^{19/20}` and `y ≥ exp(2·10⁸)`, the number of primes `p ≤ y` with
`p ≡ 1 (mod m)` is at most `3·y / (φ(m)·log(y/m))`. -/
theorem brunTitchmarsh_progression (y m : ℕ) (hm2 : 2 ≤ m)
    (hmy : (m : ℝ) ≤ (y : ℝ) ^ (19 / 20 : ℝ))
    (hy : Real.exp 200000000 ≤ (y : ℝ)) :
    ((#((Finset.range (y + 1)).filter
        (fun p => p.Prime ∧ p % m = 1 % m))) : ℝ)
      ≤ 3 * y / (Nat.totient m * Real.log ((y : ℝ) / m)) := by
  -- basic positivity
  have hyR : (200000001 : ℝ) ≤ (y : ℝ) := by
    have := Real.add_one_le_exp (200000000 : ℝ)
    linarith
  have hy0 : (0 : ℝ) < (y : ℝ) := by linarith
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hmne : (m : ℝ) ≠ 0 := hmR.ne'
  have hφpos : 0 < Nat.totient m := Nat.totient_pos.mpr (by omega)
  have hφR : (0 : ℝ) < (Nat.totient m : ℝ) := by exact_mod_cast hφpos
  have hφle : (Nat.totient m : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.totient_le m
  -- logs
  have hlogy : (200000000 : ℝ) ≤ Real.log y := (Real.le_log_iff_exp_le hy0).mpr hy
  set N : ℝ := (y : ℝ) / m with hNdef
  have hN0 : 0 < N := by positivity
  set L : ℝ := Real.log N with hLdef
  have hLsplit : L = Real.log y - Real.log m := by
    rw [hLdef, hNdef]
    exact Real.log_div hy0.ne' hmne
  have hlogm : Real.log m ≤ (19 / 20) * Real.log y := by
    calc Real.log m ≤ Real.log ((y : ℝ) ^ (19 / 20 : ℝ)) :=
          Real.log_le_log hmR hmy
      _ = (19 / 20) * Real.log y := Real.log_rpow hy0 _
  have hL7 : (10000000 : ℝ) ≤ L := by
    have h20 : (1 / 20) * Real.log y ≤ L := by rw [hLsplit]; linarith
    linarith
  have hL0 : (0 : ℝ) < L := by linarith
  -- the sifting level z = ⌊exp((2/5)·L)⌋ = ⌊(y/m)^{2/5}⌋
  set Z : ℝ := Real.exp ((2 / 5) * L) with hZdef
  have hZ0 : (0 : ℝ) < Z := Real.exp_pos _
  have hZ2 : (2 : ℝ) ≤ Z := by
    have := Real.add_one_le_exp ((2 / 5) * L)
    linarith
  set z : ℕ := ⌊Z⌋₊ with hzdef
  have hz2 : 2 ≤ z := Nat.le_floor (by exact_mod_cast hZ2)
  have hz1 : 1 ≤ z := by omega
  have hzZ : (z : ℝ) ≤ Z := Nat.floor_le hZ0.le
  have hZz : Z ≤ 2 * z := by
    have h1 : Z < (z : ℝ) + 1 := Nat.lt_floor_add_one Z
    have h2 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
    linarith
  clear_value z
  have hzR1 : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz1
  have hz0R : (0 : ℝ) < (z : ℝ) := by linarith
  -- bounds on log z
  have hlogZ : Real.log Z = (2 / 5) * L := by rw [hZdef]; exact Real.log_exp _
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hlogz_ge : (2 / 5) * L - Real.log 2 ≤ Real.log z := by
    have h1 : Z / 2 ≤ (z : ℝ) := by linarith
    have h2 : Real.log (Z / 2) ≤ Real.log z :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_div hZ0.ne' (by norm_num)] at h2
    linarith [hlogZ]
  have hlogz : (5 / 14) * L ≤ Real.log z := by linarith
  have hlogz_le : Real.log z ≤ (2 / 5) * L := by
    have := Real.log_le_log hz0R hzZ
    linarith [hlogZ]
  have hlogz_pos : (0 : ℝ) < Real.log z := by linarith
  -- apply the sieve
  have hcount := prog_count_le_siftedSum_add (m := m) (y := y) hz1
  have hsel := selberg_bound (progSieve m z y hz1)
  rw [progSieve_totalMass] at hsel
  have herr := progSieve_errSum_le (m := m) (y := y) hm2 hz1
  have hSge := progSieve_boundingSum_ge (m := m) (y := y) (by omega) hz1
  set S := selbergBoundingSum (progSieve m z y hz1) with hSdef
  have hSpos : 0 < S := selbergBoundingSum_pos _
  -- main term: X/S ≤ (14/5)·y/(φ(m)·L)
  have hγpos : (0 : ℝ) < (Nat.totient m : ℝ) / m * ((5 / 14) * L) :=
    mul_pos (div_pos hφR hmR) (by linarith)
  have hγS : (Nat.totient m : ℝ) / m * ((5 / 14) * L) ≤ S := by
    refine le_trans ?_ hSge
    apply mul_le_mul_of_nonneg_left hlogz (by positivity)
  have hmain : (y : ℝ) / m / S
      ≤ (14 / 5) * ((y : ℝ) / ((Nat.totient m : ℝ) * L)) := by
    have h1 : (y : ℝ) / m / S
        ≤ (y : ℝ) / m / ((Nat.totient m : ℝ) / m * ((5 / 14) * L)) :=
      div_le_div_of_nonneg_left (by positivity) hγpos hγS
    have h2 : (y : ℝ) / m / ((Nat.totient m : ℝ) / m * ((5 / 14) * L))
        = (14 / 5) * ((y : ℝ) / ((Nat.totient m : ℝ) * L)) := by
      field_simp
    linarith
  -- error term: err + z ≤ (1/5)·y/(φ(m)·L)
  have hz2cast : ((z ^ 2 : ℕ) : ℝ) = (z : ℝ) ^ 2 := by push_cast; ring
  have herr2 : (∑ d ∈ divisors (progSieve m z y hz1).prodPrimes,
      if (d : ℝ) ≤ (progSieve m z y hz1).level then
        (3 : ℝ) ^ ω d * |(progSieve m z y hz1).rem d| else 0)
      ≤ Z ^ 2 * (1 + L) ^ 2 := by
    refine le_trans herr ?_
    have e2 : Real.log ((z ^ 2 : ℕ) : ℝ) ≤ L := by
      rw [hz2cast, Real.log_pow]
      push_cast
      linarith [hlogz_le]
    have e3 : (0 : ℝ) ≤ Real.log ((z ^ 2 : ℕ) : ℝ) := by
      apply Real.log_nonneg
      rw [hz2cast]
      nlinarith [hzR1]
    have e4 : ((z ^ 2 : ℕ) : ℝ) ≤ Z ^ 2 := by
      rw [hz2cast]
      nlinarith [hzZ, hz0R]
    apply mul_le_mul e4 _ (by positivity) (by positivity)
    apply pow_le_pow_left₀ (by linarith) (by linarith)
  have herrz : (z : ℝ) + Z ^ 2 * (1 + L) ^ 2
      ≤ (1 / 5) * ((y : ℝ) / ((Nat.totient m : ℝ) * L)) := by
    have hZZ2 : Z ≤ Z ^ 2 := by nlinarith [hZ2]
    have hone : (1 : ℝ) ≤ (1 + L) ^ 2 := by nlinarith [hL0]
    have hz_small : (z : ℝ) ≤ Z ^ 2 * (1 + L) ^ 2 := by
      calc (z : ℝ) ≤ Z := hzZ
        _ ≤ Z ^ 2 := hZZ2
        _ = Z ^ 2 * 1 := (mul_one _).symm
        _ ≤ Z ^ 2 * (1 + L) ^ 2 := by
            apply mul_le_mul_of_nonneg_left hone (by positivity)
    -- the key exponential inequality 10·L·(1+L)² ≤ exp(L/5)
    have hkey : 10 * L * (1 + L) ^ 2 ≤ Real.exp ((1 / 5) * L) := by
      have hE : Real.exp ((1 / 5) * L) = Real.exp (L / 20) ^ 4 := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have hE2 : L / 20 ≤ Real.exp (L / 20) := by
        have := Real.add_one_le_exp (L / 20)
        linarith
      have hE3 : (L / 20) ^ 4 ≤ Real.exp (L / 20) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hE2 4
      have hL1 : (1 : ℝ) ≤ L := by linarith
      have hc1 : L ≤ L ^ 3 := by nlinarith
      have hc2 : L ^ 2 ≤ L ^ 3 := by nlinarith
      have hc3 : (10000000 : ℝ) * L ^ 3 ≤ L ^ 4 := by
        nlinarith [mul_le_mul_of_nonneg_right hL7
          (show (0 : ℝ) ≤ L ^ 3 by positivity)]
      have hexp : 10 * L * (1 + L) ^ 2 = 10 * L + 20 * L ^ 2 + 10 * L ^ 3 := by
        ring
      have hpow : (L / 20) ^ 4 = L ^ 4 / 160000 := by ring
      have hpoly : 10 * L * (1 + L) ^ 2 ≤ (L / 20) ^ 4 := by
        rw [hexp, hpow]
        linarith
      calc 10 * L * (1 + L) ^ 2 ≤ (L / 20) ^ 4 := hpoly
        _ ≤ Real.exp (L / 20) ^ 4 := hE3
        _ = Real.exp ((1 / 5) * L) := hE.symm
    have hNsplit : N = Z ^ 2 * Real.exp ((1 / 5) * L) := by
      have h1 : Z ^ 2 = Real.exp ((4 / 5) * L) := by
        rw [hZdef, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [h1, ← Real.exp_add, show (4 / 5) * L + (1 / 5) * L = L by ring]
      rw [hLdef]
      exact (Real.exp_log hN0).symm
    have h2NL : 2 * (Z ^ 2 * (1 + L) ^ 2) ≤ (1 / 5) * (N / L) := by
      have hpos : (0 : ℝ) < Z ^ 2 / (5 * L) := by positivity
      have hmul := mul_le_mul_of_nonneg_left hkey hpos.le
      calc 2 * (Z ^ 2 * (1 + L) ^ 2)
          = Z ^ 2 / (5 * L) * (10 * L * (1 + L) ^ 2) := by
            field_simp
            ring
        _ ≤ Z ^ 2 / (5 * L) * Real.exp ((1 / 5) * L) := hmul
        _ = (1 / 5) * (Z ^ 2 * Real.exp ((1 / 5) * L) / L) := by
            field_simp
        _ = (1 / 5) * (N / L) := by rw [← hNsplit]
    have hNy : N / L ≤ (y : ℝ) / ((Nat.totient m : ℝ) * L) := by
      have h1 : N / L = (y : ℝ) / ((m : ℝ) * L) := by
        rw [hNdef, div_div]
      rw [h1]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      apply mul_le_mul_of_nonneg_right hφle hL0.le
    calc (z : ℝ) + Z ^ 2 * (1 + L) ^ 2 ≤ 2 * (Z ^ 2 * (1 + L) ^ 2) := by
          linarith [hz_small]
      _ ≤ (1 / 5) * (N / L) := h2NL
      _ ≤ (1 / 5) * ((y : ℝ) / ((Nat.totient m : ℝ) * L)) := by
          apply mul_le_mul_of_nonneg_left hNy (by norm_num)
  -- final assembly
  calc ((#((Finset.range (y + 1)).filter
      (fun p => p.Prime ∧ p % m = 1 % m))) : ℝ)
      ≤ (progSieve m z y hz1).siftedSum + z := hcount
    _ ≤ ((y : ℝ) / m / S + Z ^ 2 * (1 + L) ^ 2) + z := by
        have := le_trans hsel (add_le_add le_rfl herr2)
        linarith
    _ ≤ (14 / 5) * ((y : ℝ) / ((Nat.totient m : ℝ) * L))
          + (1 / 5) * ((y : ℝ) / ((Nat.totient m : ℝ) * L)) := by
        linarith [hmain, herrz]
    _ = 3 * (y : ℝ) / ((Nat.totient m : ℝ) * L) := by ring

end

end Carmichael
