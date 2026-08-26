/-
The twin-type sieve upper bound.

For `m ≥ 1` the number of primes `q ≤ t` with `m*q + 1` prime is at most
`C₀ · (m/φ(m))² · t / (log t)²` for all `t ≥ t₀`, with `C₀` and `t₀` absolute
constants.  This is the standard dimension-two Selberg sieve bound, proved by
applying the fundamental theorem of the Selberg sieve
(`Carmichael.selberg_bound`, see `Carmichael/SelbergBound.lean`) to the
sequence `n(mn+1)`, `1 ≤ n ≤ t`, sifted by the primes `p ≤ z`, `p ∤ 2m`,
where `z = t^{1/16}` (realised as a fourfold iterated `Nat.sqrt`).

Structure of the proof:
* root counting: `n(mn+1) ≡ 0 (mod d)` has exactly `2^{ω(d)}` roots mod `d`
  for squarefree `d` coprime to `2m` (CRT + the two roots `0, -m⁻¹` mod `p`);
* the remainder `R_d` is bounded by `2^{ω(d)} ≤ d`, so the sieve error term
  is at most `z⁸ ≤ √t`;
* the Selberg bounding sum `S` is bounded below by
  `(∑_{i ≤ w, (i,2m)=1} 1/i)² ≥ ((φ(2m)/2m)·log w)²` via the completely
  multiplicative inflation `g(l) ≥ ∑_{rad j = l} 2^{Ω(j)}/j` and the
  smooth/coprime factorisation of the harmonic sum.
-/
import Mathlib
import Carmichael.SelbergBound

set_option autoImplicit false

namespace Carmichael

noncomputable section

open Finset Nat ArithmeticFunction BoundingSieve

open scoped ArithmeticFunction.omega ArithmeticFunction.Omega

/-! ### Elementary helper lemmas -/

/-- Finite geometric sums are bounded by `(1-x)⁻¹`. -/
lemma geom_sum_range_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    ∑ k ∈ range n, x ^ k ≤ (1 - x)⁻¹ := by
  have hne : x ≠ 1 := ne_of_lt h1
  have hpos : 0 < 1 - x := by linarith
  rw [geom_sum_eq hne, show (x ^ n - 1) / (x - 1) = (1 - x ^ n) / (1 - x) by
    rw [div_eq_div_iff (by linarith) hpos.ne']; ring]
  rw [div_le_iff₀ hpos, inv_mul_cancel₀ hpos.ne']
  have := pow_nonneg h0 n
  linarith

/-- Geometric sums starting from the first power are bounded by `x·(1-x)⁻¹`. -/
lemma geom_sum_Icc_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    ∑ k ∈ Icc 1 n, x ^ k ≤ x * (1 - x)⁻¹ := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hins : range (n + 1) = insert 0 (Icc 1 n) := by
    ext k
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  have h00 : (0 : ℕ) ∉ Icc 1 n := by simp
  have hb := geom_sum_range_le h0 h1 (n + 1)
  rw [hins, sum_insert h00, pow_zero] at hb
  have heq : x * (1 - x)⁻¹ = (1 - x)⁻¹ - 1 := by
    field_simp
    ring
  rw [heq]
  linarith

/-- A completely multiplicative function maps finite products to products. -/
lemma comp_mult_map_prod {α : Type*} (f : ℕ → ℝ) (hf1 : f 1 = 1)
    (hfm : ∀ a b : ℕ, f (a * b) = f a * f b) (s : Finset α) (g : α → ℕ) :
    f (∏ i ∈ s, g i) = ∏ i ∈ s, f (g i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using hf1
  | cons a s ha ih => rw [prod_cons, prod_cons, hfm, ih]

/-- A completely multiplicative function maps powers to powers. -/
lemma comp_mult_map_pow (f : ℕ → ℝ) (hf1 : f 1 = 1)
    (hfm : ∀ a b : ℕ, f (a * b) = f a * f b) (p k : ℕ) :
    f (p ^ k) = f p ^ k := by
  induction k with
  | zero => simpa using hf1
  | succ k ih => rw [pow_succ, pow_succ, hfm, ih]

/-- **Injection into exponent vectors.**  If every `n ∈ A` is nonzero, has all
prime factors in `Q` and all exponents in `K`, then for a nonnegative
completely multiplicative `f` the sum of `f` over `A` is at most the product
over `p ∈ Q` of the geometric-type sums `∑_{k ∈ K} f(p^k)`. -/
lemma sum_le_prod_sum_pow (Q : Finset ℕ) (K : Finset ℕ) (f : ℕ → ℝ)
    (hf0 : ∀ n : ℕ, 0 ≤ f n) (hf1 : f 1 = 1) (hfm : ∀ a b : ℕ, f (a * b) = f a * f b)
    (A : Finset ℕ) (hA0 : ∀ n ∈ A, n ≠ 0) (hAQ : ∀ n ∈ A, n.primeFactors ⊆ Q)
    (hAK : ∀ n ∈ A, ∀ p ∈ Q, n.factorization p ∈ K) :
    ∑ n ∈ A, f n ≤ ∏ p ∈ Q, ∑ k ∈ K, f (p ^ k) := by
  classical
  rw [Finset.prod_sum]
  have hrepr : ∀ n ∈ A, n = ∏ p ∈ Q, p ^ n.factorization p := by
    intro n hn
    have h1 : (n.factorization.prod fun p k => p ^ k) = n :=
      Nat.prod_factorization_pow_eq_self (hA0 n hn)
    rw [Finsupp.prod, Nat.support_factorization] at h1
    calc n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := h1.symm
      _ = ∏ p ∈ Q, p ^ n.factorization p := by
          apply Finset.prod_subset (hAQ n hn)
          intro p _ hp
          rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
          rw [hp, pow_zero]
  have hval : ∀ n ∈ A,
      f n = ∏ x ∈ Q.attach, f (x.1 ^ n.factorization x.1) := by
    intro n hn
    conv_lhs => rw [hrepr n hn]
    rw [comp_mult_map_prod f hf1 hfm,
      ← Finset.prod_attach Q (fun p => f (p ^ n.factorization p))]
  calc ∑ n ∈ A, f n
      = ∑ n ∈ A, ∏ x ∈ Q.attach,
          f (x.1 ^ (fun p (_ : p ∈ Q) => n.factorization p) x.1 x.2) :=
        sum_congr rfl fun n hn => hval n hn
    _ = ∑ e ∈ A.image (fun n => fun p (_ : p ∈ Q) => n.factorization p),
          ∏ x ∈ Q.attach, f (x.1 ^ e x.1 x.2) := by
        rw [Finset.sum_image]
        intro n₁ h₁ n₂ h₂ he
        apply Nat.eq_of_factorization_eq (hA0 _ h₁) (hA0 _ h₂)
        intro p
        by_cases hp : p ∈ Q
        · exact congrFun (congrFun he p) hp
        · have hz : ∀ n₀, n₀ ∈ A → n₀.factorization p = 0 := by
            intro n₀ h₀
            by_contra hc
            exact hp (hAQ _ h₀ (by
              rw [← Nat.support_factorization]
              exact Finsupp.mem_support_iff.mpr hc))
          rw [hz _ h₁, hz _ h₂]
    _ ≤ ∑ e ∈ Q.pi (fun _ => K), ∏ x ∈ Q.attach, f (x.1 ^ e x.1 x.2) := by
        apply sum_le_sum_of_subset_of_nonneg
        · rw [Finset.image_subset_iff]
          intro n hn
          rw [Finset.mem_pi]
          intro p hp
          exact hAK n hn p hp
        · intro e _ _
          exact Finset.prod_nonneg fun x _ => hf0 _

/-- The divisor count is at most `2^Ω`. -/
lemma card_divisors_le_two_pow_cardFactors {n : ℕ} (hn : n ≠ 0) :
    #n.divisors ≤ 2 ^ Ω n := by
  rw [Nat.card_divisors hn, cardFactors_eq_sum_factorization, Finsupp.sum,
    Nat.support_factorization, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod'
  intro p _
  exact Nat.succ_le_of_lt Nat.lt_two_pow_self

/-- The number of ordered factorizations of `j` into two parts drawn from a
finset `I` is at most `2^Ω(j)`. -/
lemma card_pair_fiber_le (I : Finset ℕ) {j : ℕ} (hj : j ≠ 0) :
    #((I ×ˢ I).filter (fun q => q.1 * q.2 = j)) ≤ 2 ^ Ω j := by
  calc #((I ×ˢ I).filter (fun q => q.1 * q.2 = j))
      ≤ #(Nat.divisorsAntidiagonal j) := by
        apply Finset.card_le_card
        intro q hq
        rw [mem_filter] at hq
        exact Nat.mem_divisorsAntidiagonal.mpr ⟨hq.2, hj⟩
    _ = #j.divisors := by rw [← Nat.map_div_right_divisors, Finset.card_map]
    _ ≤ 2 ^ Ω j := card_divisors_le_two_pow_cardFactors hj

/-- Euler's product for `φ(K)/K` over the reals. -/
lemma prod_one_sub_inv_primeFactors {K : ℕ} (hK : K ≠ 0) :
    ∏ p ∈ K.primeFactors, (1 - (p : ℝ)⁻¹) = (Nat.totient K : ℝ) / K := by
  have hprime : ∀ p ∈ K.primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  have hppos : ∀ p ∈ K.primeFactors, (0 : ℝ) < (p : ℝ) := by
    intro p hp
    exact_mod_cast (hprime p hp).pos
  have hsubcast : ((∏ p ∈ K.primeFactors, (p - 1) : ℕ) : ℝ)
      = ∏ p ∈ K.primeFactors, ((p : ℝ) - 1) := by
    rw [Nat.cast_prod]
    exact Finset.prod_congr rfl fun p hp => by
      rw [Nat.cast_sub (hprime p hp).one_lt.le, Nat.cast_one]
  have hcast : (Nat.totient K : ℝ) * ∏ p ∈ K.primeFactors, (p : ℝ)
      = (K : ℝ) * ∏ p ∈ K.primeFactors, ((p : ℝ) - 1) := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (Nat.totient_mul_prod_primeFactors K)
    simp only [Nat.cast_mul] at h
    rw [hsubcast] at h
    rw [Nat.cast_prod] at h
    exact h
  have hprodpos : (0 : ℝ) < ∏ p ∈ K.primeFactors, (p : ℝ) :=
    Finset.prod_pos hppos
  have hstep : ∏ p ∈ K.primeFactors, (1 - (p : ℝ)⁻¹)
      = (∏ p ∈ K.primeFactors, ((p : ℝ) - 1)) / ∏ p ∈ K.primeFactors, (p : ℝ) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have h0 : (p : ℝ) ≠ 0 := (hppos p hp).ne'
    field_simp
  have hK0 : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hK
  rw [hstep, div_eq_div_iff hprodpos.ne' hK0.ne']
  linarith [hcast]

/-- The number of `n ∈ [1, t]` in a fixed residue class mod `d` differs from
`t/d` by at most `1`. -/
lemma card_Icc_filter_mod (t : ℕ) {d r : ℕ} (hd : 0 < d) (hr : r < d) :
    |(#((Icc 1 t).filter (fun n => n % d = r)) : ℝ) - t / d| ≤ 1 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rcases Nat.eq_zero_or_pos r with rfl | hr1
  · -- r = 0 : the count is exactly t / d
    have hset : (Icc 1 t).filter (fun n => n % d = 0)
        = (Icc 1 (t / d)).image (· * d) := by
      ext n
      simp only [mem_filter, mem_Icc, mem_image]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have hdvd : d ∣ n := Nat.dvd_of_mod_eq_zero h3
        exact ⟨n / d, ⟨(Nat.one_le_div_iff hd).mpr (Nat.le_of_dvd (by omega) hdvd),
          Nat.div_le_div_right h2⟩, Nat.div_mul_cancel hdvd⟩
      · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
        refine ⟨⟨?_, ?_⟩, Nat.mul_mod_left q d⟩
        · have : 1 * 1 ≤ q * d := Nat.mul_le_mul hq1 hd
          omega
        · calc q * d ≤ t / d * d := Nat.mul_le_mul_right d hq2
            _ ≤ t := Nat.div_mul_le_self t d
    rw [hset, Finset.card_image_of_injective _
      (fun a b hab => Nat.eq_of_mul_eq_mul_right hd hab), Nat.card_Icc,
      Nat.add_sub_cancel]
    have key : (t : ℝ) = d * ((t / d : ℕ) : ℝ) + ((t % d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod t d).symm
    have hmod : ((t % d : ℕ) : ℝ) < d := by exact_mod_cast Nat.mod_lt t hd
    have hmod0 : (0 : ℝ) ≤ ((t % d : ℕ) : ℝ) := by positivity
    rw [abs_le]
    constructor
    · rw [neg_le_sub_iff_le_add, div_le_iff₀ hdR]
      nlinarith
    · rw [sub_le_iff_le_add]
      have hcd : ((t / d : ℕ) : ℝ) ≤ (t : ℝ) / d := Nat.cast_div_le
      linarith
  · by_cases hrt : r ≤ t
    · -- 1 ≤ r ≤ t : the count is (t - r)/d + 1
      have hset : (Icc 1 t).filter (fun n => n % d = r)
          = (range ((t - r) / d + 1)).image (fun q => q * d + r) := by
        ext n
        simp only [mem_filter, mem_Icc, mem_image, mem_range]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨n / d, ?_, ?_⟩
          · rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hd]
            have := Nat.div_add_mod' n d
            omega
          · have := Nat.div_add_mod' n d
            omega
        · rintro ⟨q, hq, rfl⟩
          rw [Nat.lt_succ_iff, Nat.le_div_iff_mul_le hd] at hq
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          rw [mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
      rw [hset, Finset.card_image_of_injective _
        (fun a b hab => Nat.eq_of_mul_eq_mul_right hd (by omega : a * d = b * d)),
        Finset.card_range]
      have key : ((t - r : ℕ) : ℝ)
          = d * (((t - r) / d : ℕ) : ℝ) + (((t - r) % d : ℕ) : ℝ) := by
        exact_mod_cast (Nat.div_add_mod (t - r) d).symm
      have hsub : ((t - r : ℕ) : ℝ) = (t : ℝ) - r := Nat.cast_sub hrt
      have hmod : (((t - r) % d : ℕ) : ℝ) < d := by
        exact_mod_cast Nat.mod_lt _ hd
      have hmod0 : (0 : ℝ) ≤ (((t - r) % d : ℕ) : ℝ) := by positivity
      have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
      have hrd : (r : ℝ) < d := by exact_mod_cast hr
      rw [hsub] at key
      rw [abs_le]
      constructor
      · rw [neg_le_sub_iff_le_add, div_le_iff₀ hdR]
        push_cast
        nlinarith
      · rw [sub_le_iff_le_add]
        push_cast
        have hQ : (((t - r) / d : ℕ) : ℝ) ≤ (t : ℝ) / d := by
          rw [le_div_iff₀ hdR]
          nlinarith
        linarith
    · -- r > t : the class is empty and t/d < 1
      have hset : (Icc 1 t).filter (fun n => n % d = r) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro n hn
        rw [mem_Icc] at hn
        intro hc
        have h1 : n % d ≤ n := Nat.mod_le n d
        omega
      rw [hset]
      simp only [Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg]
      rw [abs_of_nonneg (by positivity), div_le_one hdR]
      exact_mod_cast (by omega : t ≤ d)

/-! ### Root counting for `n(mn+1) mod d` -/

/-- Divisibility of `n(mn+1)` only depends on `n` mod `d`. -/
lemma dvd_quad_iff_of_modEq (m : ℕ) {d r n : ℕ} (h : r ≡ n [MOD d]) :
    d ∣ r * (m * r + 1) ↔ d ∣ n * (m * n + 1) := by
  have h2 : r * (m * r + 1) ≡ n * (m * n + 1) [MOD d] :=
    h.mul ((h.mul_left m).add_right 1)
  constructor
  · intro hd
    exact Nat.modEq_zero_iff_dvd.mp (h2.symm.trans (Nat.modEq_zero_iff_dvd.mpr hd))
  · intro hd
    exact Nat.modEq_zero_iff_dvd.mp (h2.trans (Nat.modEq_zero_iff_dvd.mpr hd))

/-- The number of roots of `X(mX+1)` modulo `d`. -/
def rootCount (m d : ℕ) : ℕ := #((range d).filter (fun r => d ∣ r * (m * r + 1)))

lemma rootCount_one (m : ℕ) : rootCount m 1 = 1 := by
  simp [rootCount, Finset.range_one]

/-- For a prime `p ∤ m` the polynomial `X(mX+1)` has exactly two roots mod
`p`, namely `0` and `-m⁻¹`. -/
lemma rootCount_prime {m p : ℕ} (hp : p.Prime) (hpm : ¬p ∣ m) : rootCount m p = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hm0 : (m : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpm
  have hsol : ∀ x : ZMod p, x * ((m : ZMod p) * x + 1) = 0 ↔
      x = 0 ∨ x = -(m : ZMod p)⁻¹ := by
    intro x
    rw [_root_.mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact Or.inl h
      · right
        have hmx : (m : ZMod p) * x = -1 := by linear_combination h
        calc x = (m : ZMod p)⁻¹ * ((m : ZMod p) * x) := by
              rw [← mul_assoc, inv_mul_cancel₀ hm0, one_mul]
          _ = -(m : ZMod p)⁻¹ := by rw [hmx]; ring
    · rintro (h | h)
      · exact Or.inl h
      · right
        rw [h, mul_neg, mul_inv_cancel₀ hm0]
        ring
  have hcard : rootCount m p
      = #(Finset.univ.filter (fun x : ZMod p => x * ((m : ZMod p) * x + 1) = 0)) := by
    unfold rootCount
    apply Finset.card_bij (fun (r : ℕ) _ => (Nat.cast r : ZMod p))
    · intro r hr
      rw [mem_filter, mem_range] at hr
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have hz : ((r * (m * r + 1) : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff _ _).mpr hr.2
      push_cast at hz
      exact hz
    · intro r₁ hr₁ r₂ hr₂ he
      rw [mem_filter, mem_range] at hr₁ hr₂
      have := congrArg ZMod.val he
      rwa [ZMod.val_cast_of_lt hr₁.1, ZMod.val_cast_of_lt hr₂.1] at this
    · intro x hx
      rw [mem_filter] at hx
      refine ⟨x.val, ?_, ?_⟩
      · rw [mem_filter, mem_range]
        refine ⟨ZMod.val_lt x, ?_⟩
        rw [← ZMod.natCast_eq_zero_iff]
        push_cast
        rw [ZMod.natCast_val, ZMod.cast_id]
        exact hx.2
      · rw [ZMod.natCast_val, ZMod.cast_id]
  rw [hcard,
    show Finset.univ.filter (fun x : ZMod p => x * ((m : ZMod p) * x + 1) = 0)
      = {0, -(m : ZMod p)⁻¹} by
        ext x
        simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
        exact hsol x]
  rw [Finset.card_insert_of_notMem, Finset.card_singleton]
  rw [mem_singleton]
  intro hc
  have h1 : (m : ZMod p)⁻¹ = 0 := neg_eq_zero.mp hc.symm
  exact hm0 (inv_eq_zero.mp h1)

/-- Root counts are multiplicative in coprime moduli (CRT). -/
lemma rootCount_mul (m : ℕ) {d₁ d₂ : ℕ} (h : Nat.Coprime d₁ d₂)
    (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    rootCount m (d₁ * d₂) = rootCount m d₁ * rootCount m d₂ := by
  unfold rootCount
  rw [← Finset.card_product]
  have hD : 0 < d₁ * d₂ := Nat.mul_pos h₁ h₂
  rw [show ((range d₁).filter (fun r => d₁ ∣ r * (m * r + 1))) ×ˢ
      ((range d₂).filter (fun r => d₂ ∣ r * (m * r + 1)))
      = ((range d₁) ×ˢ (range d₂)).filter
        (fun q => d₁ ∣ q.1 * (m * q.1 + 1) ∧ d₂ ∣ q.2 * (m * q.2 + 1)) by
    ext q
    simp only [mem_product, mem_filter, mem_range]
    tauto]
  apply Finset.card_bij (fun r _ => ((r % d₁ : ℕ), (r % d₂ : ℕ)))
  · intro r hr
    rw [mem_filter, mem_range] at hr
    rw [mem_filter, mem_product, mem_range, mem_range]
    refine ⟨⟨Nat.mod_lt r h₁, Nat.mod_lt r h₂⟩, ?_, ?_⟩
    · rw [dvd_quad_iff_of_modEq m (Nat.mod_modEq r d₁)]
      exact dvd_trans (Dvd.intro d₂ rfl) hr.2
    · rw [dvd_quad_iff_of_modEq m (Nat.mod_modEq r d₂)]
      exact dvd_trans (Dvd.intro_left d₁ rfl) hr.2
  · intro r₁ hr₁ r₂ hr₂ he
    rw [mem_filter, mem_range] at hr₁ hr₂
    have he1 : r₁ % d₁ = r₂ % d₁ := congrArg Prod.fst he
    have he2 : r₁ % d₂ = r₂ % d₂ := congrArg Prod.snd he
    have hmod : r₁ ≡ r₂ [MOD d₁ * d₂] :=
      (Nat.modEq_and_modEq_iff_modEq_mul h).mp ⟨he1, he2⟩
    calc r₁ = r₁ % (d₁ * d₂) := (Nat.mod_eq_of_lt hr₁.1).symm
      _ = r₂ % (d₁ * d₂) := hmod
      _ = r₂ := Nat.mod_eq_of_lt hr₂.1
  · intro q hq
    rw [mem_filter, mem_product, mem_range, mem_range] at hq
    obtain ⟨⟨hq1, hq2⟩, hd1, hd2⟩ := hq
    obtain ⟨x, hx1, hx2⟩ := Nat.chineseRemainder h q.1 q.2
    refine ⟨x % (d₁ * d₂), ?_, ?_⟩
    · rw [mem_filter, mem_range]
      refine ⟨Nat.mod_lt x hD, ?_⟩
      have hxq1 : x % (d₁ * d₂) ≡ q.1 [MOD d₁] :=
        ((Nat.mod_modEq x (d₁ * d₂)).of_dvd (Dvd.intro d₂ rfl)).trans hx1
      have hxq2 : x % (d₁ * d₂) ≡ q.2 [MOD d₂] :=
        ((Nat.mod_modEq x (d₁ * d₂)).of_dvd (Dvd.intro_left d₁ rfl)).trans hx2
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd h
      · rw [dvd_quad_iff_of_modEq m hxq1.symm] at hd1
        exact hd1
      · rw [dvd_quad_iff_of_modEq m hxq2.symm] at hd2
        exact hd2
    · have hxq1 : x % (d₁ * d₂) ≡ q.1 [MOD d₁] :=
        ((Nat.mod_modEq x (d₁ * d₂)).of_dvd (Dvd.intro d₂ rfl)).trans hx1
      have hxq2 : x % (d₁ * d₂) ≡ q.2 [MOD d₂] :=
        ((Nat.mod_modEq x (d₁ * d₂)).of_dvd (Dvd.intro_left d₁ rfl)).trans hx2
      have e1 : x % (d₁ * d₂) % d₁ = q.1 := by
        have := hxq1
        unfold Nat.ModEq at this
        rwa [Nat.mod_eq_of_lt hq1] at this
      have e2 : x % (d₁ * d₂) % d₂ = q.2 := by
        have := hxq2
        unfold Nat.ModEq at this
        rwa [Nat.mod_eq_of_lt hq2] at this
      rw [e1, e2]

/-- The root count of a product of distinct primes avoiding `m` is `2^#s`. -/
lemma rootCount_prod (m : ℕ) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ ¬p ∣ m) :
    rootCount m (∏ p ∈ s, p) = 2 ^ #s := by
  induction s using Finset.cons_induction with
  | empty => simpa using rootCount_one m
  | cons a s ha ih =>
    have hap : a.Prime := (hs a (mem_cons_self a s)).1
    have hsp : ∀ p ∈ s, p.Prime ∧ ¬p ∣ m := fun p hp => hs p (mem_cons_of_mem hp)
    have hcop : Nat.Coprime a (∏ p ∈ s, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hap (hsp p hp).1).mpr (by rintro rfl; exact ha hp)
    have hprod_pos : 0 < ∏ p ∈ s, p :=
      Finset.prod_pos fun p hp => (hsp p hp).1.pos
    rw [prod_cons, rootCount_mul m hcop hap.pos hprod_pos,
      rootCount_prime hap (hs a (mem_cons_self a s)).2, ih hsp,
      Finset.card_cons, pow_succ]
    ring

/-! ### The twin-type sieve -/

/-- The sifting primes: `p ≤ z`, `p` prime, `p ∤ 2m` (this excludes `2` and
the primes dividing `m`, so that `X(mX+1)` has exactly two roots mod `p` and
the density `2/p` is strictly less than `1`). -/
def twinPrimeSet (m z : ℕ) : Finset ℕ :=
  (range (z + 1)).filter (fun p => p.Prime ∧ ¬p ∣ 2 * m)

/-- The product of the sifting primes. -/
def twinProdPrimes (m z : ℕ) : ℕ := ∏ p ∈ twinPrimeSet m z, p

lemma mem_twinPrimeSet {m z p : ℕ} :
    p ∈ twinPrimeSet m z ↔ p ≤ z ∧ p.Prime ∧ ¬p ∣ 2 * m := by
  rw [twinPrimeSet, mem_filter, mem_range, Nat.lt_succ_iff]

lemma twinPrimeSet_prime {m z p : ℕ} (hp : p ∈ twinPrimeSet m z) : p.Prime :=
  (mem_twinPrimeSet.mp hp).2.1

lemma twinProdPrimes_squarefree (m z : ℕ) : Squarefree (twinProdPrimes m z) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q hq hpq => ?_) fun p hp => (twinPrimeSet_prime hp).squarefree
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (twinPrimeSet_prime hp) (twinPrimeSet_prime hq)).mpr hpq

lemma mem_twinPrimeSet_of_dvd {m z p : ℕ} (hp : p.Prime)
    (hdvd : p ∣ twinProdPrimes m z) : p ∈ twinPrimeSet m z := by
  rw [twinProdPrimes] at hdvd
  obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd hdvd
  rwa [Nat.prime_dvd_prime_iff_eq hp (twinPrimeSet_prime hq) |>.mp hpq]

lemma three_le_of_mem_twinPrimeSet {m z p : ℕ} (hp : p ∈ twinPrimeSet m z) :
    3 ≤ p := by
  obtain ⟨-, hpp, hpm⟩ := mem_twinPrimeSet.mp hp
  rcases hpp.two_le.lt_or_eq with h | h
  · omega
  · exact absurd (h ▸ Dvd.intro m rfl) hpm

/-- The twin-type Selberg sieve: support `n(mn+1)` for `1 ≤ n ≤ t`, sifting
primes `p ≤ z` with `p ∤ 2m`, density `ν(d) = 2^{ω(d)}/d`, level `z²`. -/
def twinSieve (m z t : ℕ) (hz : 1 ≤ z) : SelbergSieve where
  support := (Icc 1 t).image (fun n => n * (m * n + 1))
  prodPrimes := twinProdPrimes m z
  prodPrimes_squarefree := twinProdPrimes_squarefree m z
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := t
  nu := ArithmeticFunction.prodPrimeFactors (fun p => 2 / (p : ℝ))
  nu_mult := by arith_mult
  nu_pos_of_prime := by
    intro p hp _
    rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
      Finset.prod_singleton]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    positivity
  nu_lt_one_of_prime := by
    intro p hp hdvd
    rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
      Finset.prod_singleton]
    have h3 : 3 ≤ p := three_le_of_mem_twinPrimeSet (mem_twinPrimeSet_of_dvd hp hdvd)
    rw [div_lt_one (by positivity)]
    exact_mod_cast h3
  level := ((z : ℕ) : ℝ) ^ 2
  one_le_level := by
    have : (1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
    nlinarith

variable {m z t : ℕ}

@[simp] lemma twinSieve_level (hz : 1 ≤ z) :
    (twinSieve m z t hz).level = ((z : ℕ) : ℝ) ^ 2 := rfl

@[simp] lemma twinSieve_totalMass (hz : 1 ≤ z) :
    (twinSieve m z t hz).totalMass = (t : ℝ) := rfl

@[simp] lemma twinSieve_prodPrimes (hz : 1 ≤ z) :
    (twinSieve m z t hz).prodPrimes = twinProdPrimes m z := rfl

lemma twinSieve_nu_apply_prime (hz : 1 ≤ z) {p : ℕ} (hp : p.Prime) :
    (twinSieve m z t hz).nu p = 2 / (p : ℝ) := by
  show (ArithmeticFunction.prodPrimeFactors (fun p => 2 / (p : ℝ))) p = 2 / (p : ℝ)
  rw [ArithmeticFunction.prodPrimeFactors_apply hp.ne_zero, hp.primeFactors,
    Finset.prod_singleton]

/-- On squarefree divisors of the sifting product, `ν(d) = 2^{ω(d)}/d`. -/
lemma twinSieve_nu_eq (hz : 1 ≤ z) {d : ℕ} (hd : d ∣ twinProdPrimes m z) :
    (twinSieve m z t hz).nu d = (2 : ℝ) ^ (#d.primeFactors) / d := by
  have hsq : Squarefree d := (twinProdPrimes_squarefree m z).squarefree_of_dvd hd
  have h1 : ∏ p ∈ d.primeFactors, (twinSieve m z t hz).nu p = (twinSieve m z t hz).nu d :=
    prod_primeFactors_nu (s := (twinSieve m z t hz).toBoundingSieve) hd
  rw [← h1]
  have h2 : ∀ p ∈ d.primeFactors, (twinSieve m z t hz).nu p = 2 / (p : ℝ) := by
    intro p hp
    exact twinSieve_nu_apply_prime hz (Nat.prime_of_mem_primeFactors hp)
  rw [Finset.prod_congr rfl h2, Finset.prod_div_distrib, Finset.prod_const,
    ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]

/-- The map `n ↦ n(mn+1)` is strictly monotone. -/
lemma quadMap_strictMono (m : ℕ) : StrictMono (fun n : ℕ => n * (m * n + 1)) := by
  intro a b hab
  simp only
  have h1 : m * a + 1 ≤ m * b + 1 := by
    have := Nat.mul_le_mul (le_refl m) hab.le
    omega
  calc a * (m * a + 1) < b * (m * a + 1) :=
        mul_lt_mul_of_pos_right hab (by omega)
    _ ≤ b * (m * b + 1) := Nat.mul_le_mul le_rfl h1

lemma twinSieve_multSum (hz : 1 ≤ z) (d : ℕ) :
    (twinSieve m z t hz).multSum d
      = ∑ n ∈ Icc 1 t, if d ∣ n * (m * n + 1) then (1 : ℝ) else 0 := by
  show (∑ k ∈ (Icc 1 t).image (fun n => n * (m * n + 1)),
      if d ∣ k then (1 : ℝ) else 0) = _
  rw [Finset.sum_image]
  intro a _ b _ hab
  exact (quadMap_strictMono m).injective hab

lemma twinSieve_siftedSum (hz : 1 ≤ z) :
    (twinSieve m z t hz).siftedSum
      = ∑ n ∈ Icc 1 t,
          if Nat.Coprime (twinProdPrimes m z) (n * (m * n + 1)) then (1 : ℝ) else 0 := by
  show (∑ k ∈ (Icc 1 t).image (fun n => n * (m * n + 1)),
      if Nat.Coprime (twinProdPrimes m z) k then (1 : ℝ) else 0) = _
  rw [Finset.sum_image]
  intro a _ b _ hab
  exact (quadMap_strictMono m).injective hab

/-- The count of twin-type primes is at most `z` plus the sifted sum. -/
lemma count_le_siftedSum_add (hm : 1 ≤ m) (hz : 1 ≤ z) :
    ((#((Icc 1 t).filter (fun q => q.Prime ∧ (m * q + 1).Prime))) : ℝ)
      ≤ (twinSieve m z t hz).siftedSum + z := by
  classical
  set T := (Icc 1 t).filter (fun q => q.Prime ∧ (m * q + 1).Prime) with hT
  set T' := T.filter (fun q => z < q) with hT'
  -- split off the small primes
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
  -- the large twin-type primes survive the sieve
  have hsurvive : (#T' : ℝ) ≤ (twinSieve m z t hz).siftedSum := by
    rw [twinSieve_siftedSum hz]
    have hsub : ∀ n ∈ T', (if Nat.Coprime (twinProdPrimes m z) (n * (m * n + 1))
        then (1 : ℝ) else 0) = 1 := by
      intro q hq
      rw [mem_filter, hT, mem_filter] at hq
      obtain ⟨⟨hqIcc, hqp, hmqp⟩, hqz⟩ := hq
      rw [if_pos]
      apply Nat.coprime_of_dvd
      intro k hk hkP hkq
      have hkset := mem_twinPrimeSet_of_dvd hk hkP
      have hkz : k ≤ z := (mem_twinPrimeSet.mp hkset).1
      rcases (Nat.Prime.dvd_mul hk).mp hkq with h | h
      · have : k = q := (Nat.prime_dvd_prime_iff_eq hk hqp).mp h
        omega
      · have : k = m * q + 1 := (Nat.prime_dvd_prime_iff_eq hk hmqp).mp h
        have hq1 : 1 ≤ q := (mem_Icc.mp hqIcc).1
        nlinarith
    calc (#T' : ℝ) = ∑ n ∈ T', (1 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = ∑ n ∈ T', if Nat.Coprime (twinProdPrimes m z) (n * (m * n + 1))
            then (1 : ℝ) else 0 := (Finset.sum_congr rfl hsub).symm
      _ ≤ ∑ n ∈ Icc 1 t, if Nat.Coprime (twinProdPrimes m z) (n * (m * n + 1))
            then (1 : ℝ) else 0 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro q hq
            exact (mem_filter.mp ((mem_filter.mp hq).1)).1
          · intro q _ _
            positivity
  have hcast : (#T : ℝ) ≤ (#T' : ℝ) + z := by exact_mod_cast hcard
  linarith

/-! ### The remainder bound -/

/-- The root count of a squarefree divisor of the sifting product is
`2^{ω(d)}`. -/
lemma rootCount_of_dvd_twinProdPrimes {d : ℕ} (hd : d ∣ twinProdPrimes m z) :
    rootCount m d = 2 ^ (#d.primeFactors) := by
  have hsq : Squarefree d := (twinProdPrimes_squarefree m z).squarefree_of_dvd hd
  have hrepr : d = ∏ p ∈ d.primeFactors, p :=
    (Nat.prod_primeFactors_of_squarefree hsq).symm
  conv_lhs => rw [hrepr]
  apply rootCount_prod
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpP : p ∣ twinProdPrimes m z := (Nat.dvd_of_mem_primeFactors hp).trans hd
  have hset := mem_twinPrimeSet.mp (mem_twinPrimeSet_of_dvd hpp hpP)
  exact ⟨hpp, fun hc => hset.2.2 (hc.trans (dvd_mul_left m 2))⟩

/-- `2^{ω(d)} ≤ d` for squarefree `d`. -/
lemma two_pow_card_primeFactors_le {d : ℕ} (hsq : Squarefree d) :
    2 ^ (#d.primeFactors) ≤ d := by
  calc 2 ^ (#d.primeFactors) = ∏ _p ∈ d.primeFactors, 2 := by
        rw [Finset.prod_const]
    _ ≤ ∏ p ∈ d.primeFactors, p :=
        Finset.prod_le_prod' fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
    _ = d := Nat.prod_primeFactors_of_squarefree hsq

/-- `3^{ω(d)} ≤ d²` for squarefree `d`. -/
lemma three_pow_card_primeFactors_le {d : ℕ} (hsq : Squarefree d) :
    3 ^ (#d.primeFactors) ≤ d ^ 2 := by
  calc 3 ^ (#d.primeFactors) = ∏ _p ∈ d.primeFactors, 3 := by
        rw [Finset.prod_const]
    _ ≤ ∏ p ∈ d.primeFactors, p ^ 2 := by
        apply Finset.prod_le_prod'
        intro p hp
        have := (Nat.prime_of_mem_primeFactors hp).two_le
        nlinarith
    _ = (∏ p ∈ d.primeFactors, p) ^ 2 := by rw [Finset.prod_pow]
    _ = d ^ 2 := by rw [Nat.prod_primeFactors_of_squarefree hsq]

/-- The remainder of the twin sieve at a divisor `d` of the sifting product
is at most `2^{ω(d)} ≤ d` in absolute value. -/
lemma twinSieve_abs_rem_le (hz : 1 ≤ z) {d : ℕ} (hd : d ∣ twinProdPrimes m z) :
    |(twinSieve m z t hz).rem d| ≤ (d : ℝ) := by
  classical
  have hsq : Squarefree d := (twinProdPrimes_squarefree m z).squarefree_of_dvd hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero hsq.ne_zero
  -- decompose the mult-sum by residue classes
  have hfib : ∀ n : ℕ, n ∈ Icc 1 t → n % d ∈ range d :=
    fun n _ => mem_range.mpr (Nat.mod_lt n hd0)
  have hmult : (twinSieve m z t hz).multSum d
      = ∑ r ∈ (range d).filter (fun r => d ∣ r * (m * r + 1)),
          (#((Icc 1 t).filter (fun n => n % d = r)) : ℝ) := by
    rw [twinSieve_multSum hz,
      ← Finset.sum_fiberwise_of_maps_to hfib
        (fun n => if d ∣ n * (m * n + 1) then (1 : ℝ) else 0)]
    rw [Finset.sum_filter]
    refine sum_congr rfl fun r _ => ?_
    have hinner : ∀ n ∈ (Icc 1 t).filter (fun n => n % d = r),
        (if d ∣ n * (m * n + 1) then (1 : ℝ) else 0)
          = (if d ∣ r * (m * r + 1) then (1 : ℝ) else 0) := by
      intro n hn
      have hr : n % d = r := (mem_filter.mp hn).2
      have hcong : r ≡ n [MOD d] := hr ▸ Nat.mod_modEq n d
      exact if_congr (dvd_quad_iff_of_modEq m hcong).symm rfl rfl
    rw [Finset.sum_congr rfl hinner]
    split_ifs with h
    · rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    · rw [Finset.sum_const, smul_zero]
  -- the main term matches the root count
  have hnut : (twinSieve m z t hz).nu d * (twinSieve m z t hz).totalMass
      = ∑ _r ∈ (range d).filter (fun r => d ∣ r * (m * r + 1)), ((t : ℝ) / d) := by
    rw [Finset.sum_const, twinSieve_totalMass, twinSieve_nu_eq hz hd]
    have hcard : #((range d).filter (fun r => d ∣ r * (m * r + 1)))
        = 2 ^ (#d.primeFactors) := rootCount_of_dvd_twinProdPrimes hd
    rw [hcard, nsmul_eq_mul]
    push_cast
    have hdR : ((d : ℝ)) ≠ 0 := by positivity
    field_simp
  -- combine
  have hrem : (twinSieve m z t hz).rem d
      = ∑ r ∈ (range d).filter (fun r => d ∣ r * (m * r + 1)),
          ((#((Icc 1 t).filter (fun n => n % d = r)) : ℝ) - (t : ℝ) / d) := by
    rw [rem, hmult, hnut, Finset.sum_sub_distrib]
  rw [hrem]
  calc |∑ r ∈ (range d).filter (fun r => d ∣ r * (m * r + 1)),
        ((#((Icc 1 t).filter (fun n => n % d = r)) : ℝ) - (t : ℝ) / d)|
      ≤ ∑ r ∈ (range d).filter (fun r => d ∣ r * (m * r + 1)),
          |(#((Icc 1 t).filter (fun n => n % d = r)) : ℝ) - (t : ℝ) / d| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r ∈ (range d).filter (fun r => d ∣ r * (m * r + 1)), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrd : r < d := mem_range.mp (mem_filter.mp hr).1
        exact card_Icc_filter_mod t hd0 hrd
    _ ≤ (d : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        show ((rootCount m d : ℕ) : ℝ) ≤ (d : ℝ)
        rw [rootCount_of_dvd_twinProdPrimes hd]
        exact_mod_cast two_pow_card_primeFactors_le hsq

/-- The sieve error term is at most `z⁸`. -/
lemma twinSieve_errSum_le (hz : 1 ≤ z) :
    (∑ d ∈ divisors (twinSieve m z t hz).prodPrimes,
      if (d : ℝ) ≤ (twinSieve m z t hz).level then
        (3 : ℝ) ^ ω d * |(twinSieve m z t hz).rem d| else 0)
      ≤ ((z : ℕ) : ℝ) ^ 8 := by
  classical
  rw [show (twinSieve m z t hz).prodPrimes = twinProdPrimes m z from rfl]
  simp only [twinSieve_level]
  have hzR : (0 : ℝ) ≤ (z : ℝ) := by positivity
  calc (∑ d ∈ divisors (twinProdPrimes m z),
      if (d : ℝ) ≤ ((z : ℕ) : ℝ) ^ 2 then
        (3 : ℝ) ^ (ω d) * |(twinSieve m z t hz).rem d| else 0)
      ≤ ∑ d ∈ divisors (twinProdPrimes m z),
          (if (d : ℝ) ≤ ((z : ℕ) : ℝ) ^ 2 then ((z : ℝ) ^ 2) ^ 3 else 0) := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp hd
        have hsq : Squarefree d := (twinProdPrimes_squarefree m z).squarefree_of_dvd hdvd
        split_ifs with h
        · have h3 : (3 : ℝ) ^ (ω d) ≤ (d : ℝ) ^ 2 := by
            rw [cardDistinctFactors_eq_card_primeFactors]
            exact_mod_cast three_pow_card_primeFactors_le hsq
          have hrem : |(twinSieve m z t hz).rem d| ≤ (d : ℝ) :=
            twinSieve_abs_rem_le hz hdvd
          have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
          calc (3 : ℝ) ^ (ω d) * |(twinSieve m z t hz).rem d|
              ≤ (d : ℝ) ^ 2 * (d : ℝ) := by
                apply mul_le_mul h3 hrem (abs_nonneg _) (by positivity)
            _ = (d : ℝ) ^ 3 := by ring
            _ ≤ ((z : ℝ) ^ 2) ^ 3 := by
                apply pow_le_pow_left₀ hd0 h
        · exact le_refl 0
    _ = (#((divisors (twinProdPrimes m z)).filter
          (fun d : ℕ => (d : ℝ) ≤ ((z : ℕ) : ℝ) ^ 2)) : ℝ) * ((z : ℝ) ^ 2) ^ 3 := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((z : ℝ) ^ 2) * ((z : ℝ) ^ 2) ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        have hsub : (divisors (twinProdPrimes m z)).filter
            (fun d : ℕ => (d : ℝ) ≤ ((z : ℕ) : ℝ) ^ 2) ⊆ Icc 1 (z ^ 2) := by
          intro d hd
          rw [mem_filter, Nat.mem_divisors] at hd
          rw [mem_Icc]
          constructor
          · exact Nat.pos_of_ne_zero fun hc =>
              hd.1.2 (by simpa [hc] using hd.1.1)
          · exact_mod_cast hd.2
        calc (#((divisors (twinProdPrimes m z)).filter
              (fun d : ℕ => (d : ℝ) ≤ ((z : ℕ) : ℝ) ^ 2)) : ℝ)
            ≤ (#(Icc 1 (z ^ 2)) : ℝ) := by
              exact_mod_cast Finset.card_le_card hsub
          _ = ((z : ℝ)) ^ 2 := by
              rw [Nat.card_Icc, Nat.add_sub_cancel]
              push_cast
              ring
    _ = ((z : ℕ) : ℝ) ^ 8 := by ring

/-! ### The lower bound for the Selberg bounding sum -/

/-- The radical of `j`: the product of its distinct prime factors. -/
def radd (j : ℕ) : ℕ := ∏ p ∈ j.primeFactors, p

lemma radd_dvd_self (j : ℕ) : radd j ∣ j := Nat.prod_primeFactors_dvd j

lemma primeFactors_radd (j : ℕ) : (radd j).primeFactors = j.primeFactors :=
  Nat.primeFactors_prod_primeFactors j

/-- The completely multiplicative density `2^{Ω(j)}/j`. -/
def nuC (j : ℕ) : ℝ := 2 ^ (Ω j) / j

lemma nuC_nonneg (j : ℕ) : 0 ≤ nuC j := by
  unfold nuC
  positivity

lemma nuC_one : nuC 1 = 1 := by simp [nuC]

lemma nuC_mul (a b : ℕ) : nuC (a * b) = nuC a * nuC b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [nuC]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [nuC]
  unfold nuC
  rw [cardFactors_mul ha hb, pow_add, Nat.cast_mul]
  ring

lemma nuC_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    nuC (p ^ k) = (2 / (p : ℝ)) ^ k := by
  unfold nuC
  rw [cardFactors_apply_prime_pow hp, Nat.cast_pow, div_pow]

/-- The integers in `[1, w]` coprime to `2m`. -/
def coprimeSet (m w : ℕ) : Finset ℕ :=
  (Icc 1 w).filter (fun i => Nat.Coprime i (2 * m))

lemma mem_coprimeSet {m w i : ℕ} :
    i ∈ coprimeSet m w ↔ (1 ≤ i ∧ i ≤ w) ∧ Nat.Coprime i (2 * m) := by
  rw [coprimeSet, mem_filter, mem_Icc]

lemma primeFactors_subset_twinPrimeSet {w j : ℕ} (hw : w ≤ z)
    (hj : j ∈ coprimeSet m w) : j.primeFactors ⊆ twinPrimeSet m z := by
  intro p hp
  obtain ⟨⟨hj1, hjw⟩, hcop⟩ := mem_coprimeSet.mp hj
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpj := Nat.dvd_of_mem_primeFactors hp
  rw [mem_twinPrimeSet]
  refine ⟨le_trans (le_trans (Nat.le_of_dvd (by omega) hpj) hjw) hw, hpp, ?_⟩
  intro hdvd
  have hgcd : p ∣ Nat.gcd j (2 * m) := Nat.dvd_gcd hpj hdvd
  rw [Nat.Coprime] at hcop
  rw [hcop] at hgcd
  exact hpp.ne_one (Nat.dvd_one.mp hgcd)

/-- Each fiber sum of the inflated density is dominated by the corresponding
Selberg term. -/
lemma fiber_sum_le_selbergTerms (hz : 1 ≤ z) {l : ℕ} (hl : l ∣ twinProdPrimes m z) :
    ∑ j ∈ (coprimeSet m z).filter (fun j => radd j = l), nuC j
      ≤ (twinSieve m z t hz).selbergTerms l := by
  have hlp : ∀ p ∈ l.primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  have hl3 : ∀ p ∈ l.primeFactors, 3 ≤ p := fun p hp =>
    three_le_of_mem_twinPrimeSet (mem_twinPrimeSet_of_dvd (hlp p hp)
      ((Nat.dvd_of_mem_primeFactors hp).trans hl))
  have h1 : ∑ j ∈ (coprimeSet m z).filter (fun j => radd j = l), nuC j
      ≤ ∏ p ∈ l.primeFactors, ∑ k ∈ Icc 1 z, nuC (p ^ k) := by
    apply sum_le_prod_sum_pow _ _ _ nuC_nonneg nuC_one nuC_mul
    · intro j hj
      have := (mem_coprimeSet.mp (mem_filter.mp hj).1).1.1
      omega
    · intro j hj
      obtain ⟨-, hrad⟩ := mem_filter.mp hj
      rw [← hrad, primeFactors_radd]
    · intro j hj p hp
      obtain ⟨hjJ, hrad⟩ := mem_filter.mp hj
      obtain ⟨⟨hj1, hjz⟩, -⟩ := mem_coprimeSet.mp hjJ
      rw [← hrad, primeFactors_radd] at hp
      rw [mem_Icc]
      constructor
      · exact (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
          (by omega) (Nat.dvd_of_mem_primeFactors hp)
      · have := Nat.factorization_lt p (show j ≠ 0 by omega)
        omega
  have h2 : ∏ p ∈ l.primeFactors, ∑ k ∈ Icc 1 z, nuC (p ^ k)
      ≤ ∏ p ∈ l.primeFactors, (2 / (p : ℝ)) * (1 - 2 / (p : ℝ))⁻¹ := by
    apply Finset.prod_le_prod
    · intro p _
      exact Finset.sum_nonneg fun k _ => nuC_nonneg _
    · intro p hp
      have h3p := hl3 p hp
      have hp0 : (0 : ℝ) < (p : ℝ) := by
        have : 0 < p := by omega
        exact_mod_cast this
      have hx0 : (0 : ℝ) ≤ 2 / p := by positivity
      have hx1 : (2 : ℝ) / p < 1 := by
        rw [div_lt_one hp0]
        exact_mod_cast (by omega : 2 < p)
      calc ∑ k ∈ Icc 1 z, nuC (p ^ k) = ∑ k ∈ Icc 1 z, (2 / (p : ℝ)) ^ k :=
            sum_congr rfl fun k _ => nuC_prime_pow (hlp p hp) k
        _ ≤ (2 / (p : ℝ)) * (1 - 2 / (p : ℝ))⁻¹ := geom_sum_Icc_le hx0 hx1 z
  have h3 : (twinSieve m z t hz).selbergTerms l
      = ∏ p ∈ l.primeFactors, (2 / (p : ℝ)) * (1 - 2 / (p : ℝ))⁻¹ := by
    rw [selbergTerms_apply,
      ← prod_primeFactors_nu (s := (twinSieve m z t hz).toBoundingSieve) hl,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [twinSieve_nu_apply_prime hz (hlp p hp)]
  rw [h3]
  exact le_trans h1 h2

/-- The Selberg bounding sum dominates the inflated density sum. -/
lemma sum_nuC_le_selbergBoundingSum (hz : 1 ≤ z) :
    ∑ j ∈ coprimeSet m z, nuC j ≤ selbergBoundingSum (twinSieve m z t hz) := by
  have hP0 : twinProdPrimes m z ≠ 0 := (twinProdPrimes_squarefree m z).ne_zero
  have hmaps : ∀ j ∈ coprimeSet m z, radd j ∈ divisors (twinProdPrimes m z) := by
    intro j hj
    rw [Nat.mem_divisors]
    exact ⟨Finset.prod_dvd_prod_of_subset _ _ _
      (primeFactors_subset_twinPrimeSet le_rfl hj), hP0⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps nuC]
  apply Finset.sum_le_sum
  intro l hl
  obtain ⟨hldvd, -⟩ := Nat.mem_divisors.mp hl
  by_cases hcond : ((l : ℕ) : ℝ) ^ 2 ≤ (twinSieve m z t hz).level
  · rw [if_pos hcond]
    exact fiber_sum_le_selbergTerms hz hldvd
  · rw [if_neg hcond]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro j hj
    exfalso
    apply hcond
    obtain ⟨hjJ, hrad⟩ := mem_filter.mp hj
    obtain ⟨⟨hj1, hjz⟩, -⟩ := mem_coprimeSet.mp hjJ
    have hlz : l ≤ z := by
      have h1 : radd j ≤ j := Nat.le_of_dvd (by omega) (radd_dvd_self j)
      omega
    rw [twinSieve_level]
    have : ((l : ℕ) : ℝ) ≤ ((z : ℕ) : ℝ) := by exact_mod_cast hlz
    have hl0 : (0 : ℝ) ≤ ((l : ℕ) : ℝ) := by positivity
    exact pow_le_pow_left₀ hl0 this 2

/-- The square of the coprime harmonic sum up to `√z` is dominated by the
inflated density sum up to `z`. -/
lemma sq_sum_inv_le_sum_nuC (m z : ℕ) :
    (∑ i ∈ coprimeSet m z.sqrt, (i : ℝ)⁻¹) ^ 2 ≤ ∑ j ∈ coprimeSet m z, nuC j := by
  classical
  set w := z.sqrt with hw
  set I := coprimeSet m w with hI
  have hmaps : ∀ q ∈ I ×ˢ I, q.1 * q.2 ∈ coprimeSet m z := by
    intro q hq
    rw [mem_product] at hq
    obtain ⟨h1, h2⟩ := hq
    obtain ⟨⟨h11, h12⟩, h1c⟩ := mem_coprimeSet.mp h1
    obtain ⟨⟨h21, h22⟩, h2c⟩ := mem_coprimeSet.mp h2
    rw [mem_coprimeSet]
    refine ⟨⟨?_, ?_⟩, Nat.Coprime.mul_left h1c h2c⟩
    · have := Nat.mul_le_mul h11 h21
      omega
    · calc q.1 * q.2 ≤ w * w := Nat.mul_le_mul h12 h22
        _ ≤ z := Nat.sqrt_le z
  have hexp : (∑ i ∈ I, (i : ℝ)⁻¹) ^ 2
      = ∑ q ∈ I ×ˢ I, ((q.1 * q.2 : ℕ) : ℝ)⁻¹ := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
    refine sum_congr rfl fun q _ => ?_
    rw [Nat.cast_mul, mul_inv]
  rw [hexp, ← Finset.sum_fiberwise_of_maps_to hmaps
    (fun q : ℕ × ℕ => ((q.1 * q.2 : ℕ) : ℝ)⁻¹)]
  apply Finset.sum_le_sum
  intro j hj
  obtain ⟨⟨hj1, hjz⟩, -⟩ := mem_coprimeSet.mp hj
  have hj0 : j ≠ 0 := by omega
  calc ∑ q ∈ (I ×ˢ I).filter (fun q => q.1 * q.2 = j), ((q.1 * q.2 : ℕ) : ℝ)⁻¹
      = ∑ _q ∈ (I ×ˢ I).filter (fun q => q.1 * q.2 = j), ((j : ℕ) : ℝ)⁻¹ := by
        refine sum_congr rfl fun q hq => ?_
        rw [(mem_filter.mp hq).2]
    _ = (#((I ×ˢ I).filter (fun q => q.1 * q.2 = j)) : ℝ) * ((j : ℕ) : ℝ)⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ (Ω j) * ((j : ℕ) : ℝ)⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast card_pair_fiber_le I hj0
    _ = nuC j := by rw [nuC, div_eq_mul_inv]

/-! ### The coprime harmonic sum -/

/-- The `2m`-smooth part of `n`. -/
def smoothPart (m n : ℕ) : ℕ := ∏ p ∈ (2 * m).primeFactors, p ^ n.factorization p

/-- Factorization of a product of prime powers over a finset of primes. -/
lemma factorization_prod_pow_apply (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (e : ℕ → ℕ) (q : ℕ) :
    (∏ p ∈ Q, p ^ e p).factorization q = if q ∈ Q then e q else 0 := by
  classical
  rw [Nat.factorization_prod (fun p hp => pow_ne_zero _ (hQ p hp).ne_zero),
    Finset.sum_apply']
  have hstep : ∀ p ∈ Q, ((p ^ e p).factorization) q = if p = q then e p else 0 := by
    intro p hp
    rw [(hQ p hp).factorization_pow, Finsupp.single_apply]
  rw [Finset.sum_congr rfl hstep, Finset.sum_ite_eq' Q q e]

lemma smoothPart_ne_zero (m n : ℕ) : smoothPart m n ≠ 0 := by
  rw [smoothPart]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero

lemma smoothPart_dvd (m : ℕ) {n : ℕ} (hn : n ≠ 0) : smoothPart m n ∣ n := by
  have hQ : ∀ p ∈ (2 * m).primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  rw [← Nat.factorization_le_iff_dvd (smoothPart_ne_zero m n) hn, Finsupp.le_def]
  intro q
  rw [smoothPart, factorization_prod_pow_apply _ hQ]
  split_ifs
  · exact le_refl _
  · exact Nat.zero_le _

lemma smoothPart_primeFactors_subset (m n : ℕ) :
    (smoothPart m n).primeFactors ⊆ (2 * m).primeFactors := by
  intro q hq
  have h0 : (smoothPart m n).factorization q ≠ 0 := by
    rw [← Nat.support_factorization] at hq
    exact Finsupp.mem_support_iff.mp hq
  rw [smoothPart, factorization_prod_pow_apply _
    (fun p hp => Nat.prime_of_mem_primeFactors hp)] at h0
  by_contra hc
  rw [if_neg hc] at h0
  exact h0 rfl

lemma coprime_div_smoothPart (hm : 1 ≤ m) {n : ℕ} (hn : n ≠ 0) :
    Nat.Coprime (n / smoothPart m n) (2 * m) := by
  have hQ : ∀ p ∈ (2 * m).primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  have hdvd := smoothPart_dvd m hn
  have hb0 : n / smoothPart m n ≠ 0 := by
    have h1 : smoothPart m n ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
    have h2 := Nat.div_pos h1 (Nat.pos_of_ne_zero (smoothPart_ne_zero m n))
    omega
  apply Nat.coprime_of_dvd
  intro k hk hkdvd hk2m
  have hkQ : k ∈ (2 * m).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hk, hk2m, by omega⟩
  have hfact : (n / smoothPart m n).factorization k = 0 := by
    rw [Nat.factorization_div hdvd, Finsupp.tsub_apply, smoothPart,
      factorization_prod_pow_apply _ hQ, if_pos hkQ]
    omega
  have := hk.factorization_pos_of_dvd hb0 hkdvd
  omega

/-- The coprime harmonic sum is at least `(φ(2m)/2m)·log w`. -/
lemma coprime_harmonic_ge (hm : 1 ≤ m) {w : ℕ} (hw : 1 ≤ w) :
    (Nat.totient (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ) * Real.log w
      ≤ ∑ i ∈ coprimeSet m w, (i : ℝ)⁻¹ := by
  classical
  set Q := (2 * m).primeFactors with hQdef
  have h2m0 : 2 * m ≠ 0 := by omega
  have hQp : ∀ p ∈ Q, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  set A := (Icc 1 w).filter (fun a => a.primeFactors ⊆ Q) with hA
  set L := ∑ i ∈ coprimeSet m w, (i : ℝ)⁻¹ with hL
  have hLnonneg : 0 ≤ L := Finset.sum_nonneg fun i _ => by positivity
  -- (i) the harmonic sum factors through smooth × coprime pairs
  have hkey : ∑ n ∈ Icc 1 w, (n : ℝ)⁻¹ ≤ (∑ a ∈ A, (a : ℝ)⁻¹) * L := by
    have hφmem : ∀ n ∈ Icc 1 w,
        (smoothPart m n, n / smoothPart m n) ∈ A ×ˢ coprimeSet m w := by
      intro n hn
      obtain ⟨hn1, hnw⟩ := mem_Icc.mp hn
      have hn0 : n ≠ 0 := by omega
      have hdvd := smoothPart_dvd m hn0
      rw [mem_product]
      constructor
      · rw [hA, mem_filter, mem_Icc]
        refine ⟨⟨Nat.pos_of_ne_zero (smoothPart_ne_zero m n),
          le_trans (Nat.le_of_dvd (by omega) hdvd) hnw⟩,
          smoothPart_primeFactors_subset m n⟩
      · rw [mem_coprimeSet]
        have hbdvd : n / smoothPart m n ∣ n := Nat.div_dvd_of_dvd hdvd
        have hb0 : n / smoothPart m n ≠ 0 := by
          have h1 : smoothPart m n ≤ n := Nat.le_of_dvd (by omega) hdvd
          have h2 := Nat.div_pos h1 (Nat.pos_of_ne_zero (smoothPart_ne_zero m n))
          omega
        exact ⟨⟨Nat.pos_of_ne_zero hb0,
          le_trans (Nat.le_of_dvd (by omega) hbdvd) hnw⟩,
          coprime_div_smoothPart hm hn0⟩
    have hinj : ∀ n₁ ∈ Icc 1 w, ∀ n₂ ∈ Icc 1 w,
        (smoothPart m n₁, n₁ / smoothPart m n₁)
          = (smoothPart m n₂, n₂ / smoothPart m n₂) → n₁ = n₂ := by
      intro n₁ h₁ n₂ h₂ he
      have hn₁ : n₁ ≠ 0 := by have := (mem_Icc.mp h₁).1; omega
      have hn₂ : n₂ ≠ 0 := by have := (mem_Icc.mp h₂).1; omega
      have e1 : smoothPart m n₁ = smoothPart m n₂ := congrArg Prod.fst he
      have e2 : n₁ / smoothPart m n₁ = n₂ / smoothPart m n₂ := congrArg Prod.snd he
      calc n₁ = smoothPart m n₁ * (n₁ / smoothPart m n₁) :=
            (Nat.mul_div_cancel' (smoothPart_dvd m hn₁)).symm
        _ = smoothPart m n₂ * (n₂ / smoothPart m n₂) := by rw [e2, e1]
        _ = n₂ := Nat.mul_div_cancel' (smoothPart_dvd m hn₂)
    calc ∑ n ∈ Icc 1 w, (n : ℝ)⁻¹
        = ∑ n ∈ Icc 1 w, ((smoothPart m n : ℕ) : ℝ)⁻¹
            * ((n / smoothPart m n : ℕ) : ℝ)⁻¹ := by
          refine sum_congr rfl fun n hn => ?_
          have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
          rw [← mul_inv, ← Nat.cast_mul,
            Nat.mul_div_cancel' (smoothPart_dvd m hn0)]
      _ = ∑ q ∈ (Icc 1 w).image (fun n => (smoothPart m n, n / smoothPart m n)),
            ((q.1 : ℕ) : ℝ)⁻¹ * ((q.2 : ℕ) : ℝ)⁻¹ := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ q ∈ A ×ˢ coprimeSet m w, ((q.1 : ℕ) : ℝ)⁻¹ * ((q.2 : ℕ) : ℝ)⁻¹ := by
          apply sum_le_sum_of_subset_of_nonneg
          · rw [Finset.image_subset_iff]
            exact hφmem
          · intro q _ _
            positivity
      _ = (∑ a ∈ A, (a : ℝ)⁻¹) * L := by
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
  -- (iii) the Euler product is `(φ(2m)/2m)⁻¹`
  have hprod : ∏ p ∈ Q, (1 - (p : ℝ)⁻¹)⁻¹
      = ((Nat.totient (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ))⁻¹ := by
    rw [Finset.prod_inv_distrib, prod_one_sub_inv_primeFactors h2m0]
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
  have hφpos : (0 : ℝ) < (Nat.totient (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ) := by
    have h1 : 0 < Nat.totient (2 * m) := Nat.totient_pos.mpr (by omega)
    have h2 : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * m)
    have h3 : (0 : ℝ) < (Nat.totient (2 * m) : ℝ) := by exact_mod_cast h1
    positivity
  have hHL : ∑ n ∈ Icc 1 w, (n : ℝ)⁻¹
      ≤ ((Nat.totient (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ))⁻¹ * L := by
    calc ∑ n ∈ Icc 1 w, (n : ℝ)⁻¹ ≤ (∑ a ∈ A, (a : ℝ)⁻¹) * L := hkey
      _ ≤ ((Nat.totient (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ))⁻¹ * L :=
          mul_le_mul_of_nonneg_right (hAle.trans_eq hprod) hLnonneg
  calc (Nat.totient (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ) * Real.log w
      ≤ (Nat.totient (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ)
          * (((Nat.totient (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ))⁻¹ * L) :=
        mul_le_mul_of_nonneg_left (le_trans hHw hHL) hφpos.le
    _ = L := by
        rw [← mul_assoc, mul_inv_cancel₀ hφpos.ne', one_mul]

/-- **The lower bound for the Selberg bounding sum**:
`S ≥ ((φ(2m)/2m)·log √z)²`. -/
lemma selbergBoundingSum_ge (hm : 1 ≤ m) (hz : 1 ≤ z) :
    ((Nat.totient (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ) * Real.log (z.sqrt : ℝ)) ^ 2
      ≤ selbergBoundingSum (twinSieve m z t hz) := by
  have hw1 : 1 ≤ z.sqrt := Nat.le_sqrt.mpr (by omega)
  have hβ := coprime_harmonic_ge hm (w := z.sqrt) hw1
  have hφ0 : (0 : ℝ) ≤ (Nat.totient (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ) := by positivity
  have hlog0 : (0 : ℝ) ≤ Real.log (z.sqrt : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hw1)
  calc ((Nat.totient (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ) * Real.log (z.sqrt : ℝ)) ^ 2
      ≤ (∑ i ∈ coprimeSet m z.sqrt, (i : ℝ)⁻¹) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hφ0 hlog0) hβ 2
    _ ≤ ∑ j ∈ coprimeSet m z, nuC j := sq_sum_inv_le_sum_nuC m z
    _ ≤ selbergBoundingSum (twinSieve m z t hz) := sum_nuC_le_selbergBoundingSum hz

/-! ### Final assembly -/

/-- `φ(m) ≤ φ(2m)`. -/
lemma totient_le_totient_two_mul (m : ℕ) (hm : 1 ≤ m) :
    Nat.totient m ≤ Nat.totient (2 * m) := by
  apply Nat.le_of_dvd
  · exact Nat.totient_pos.mpr (by omega)
  · exact Nat.totient_dvd_of_dvd (dvd_mul_left m 2)

/-- If `a < (b+1)^k` then `log a ≤ k · log(b+1)`. -/
lemma log_le_mul_log_succ_of_lt_pow {a b k : ℕ} (ha : 0 < a) (h : a < (b + 1) ^ k) :
    Real.log a ≤ (k : ℕ) * Real.log ((b : ℝ) + 1) := by
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have h1 : Real.log a ≤ Real.log (((b + 1) ^ k : ℕ) : ℝ) :=
    Real.log_le_log ha0 (by exact_mod_cast h.le)
  have h2 : (((b + 1) ^ k : ℕ) : ℝ) = ((b : ℝ) + 1) ^ k := by push_cast; ring
  rw [h2, Real.log_pow] at h1
  exact h1

/-- `log(w+1) ≤ 2·log w` for `w ≥ 2`. -/
lemma log_succ_le_two_log {w : ℕ} (hw : 2 ≤ w) :
    Real.log ((w : ℝ) + 1) ≤ 2 * Real.log w := by
  have hwR : (2 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have h1 : ((w : ℝ) + 1) ≤ (w : ℝ) ^ 2 := by nlinarith
  have h2 : Real.log ((w : ℝ) + 1) ≤ Real.log ((w : ℝ) ^ 2) :=
    Real.log_le_log (by linarith) h1
  rw [Real.log_pow] at h2
  calc Real.log ((w : ℝ) + 1) ≤ ((2 : ℕ) : ℝ) * Real.log w := h2
    _ = 2 * Real.log w := by norm_num

/-- `log(b+1) ≤ b`. -/
lemma log_succ_le_self (b : ℕ) : Real.log ((b : ℝ) + 1) ≤ (b : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (b : ℝ) + 1 by positivity)
  linarith

set_option maxHeartbeats 1600000 in
/-- **The twin-type sieve upper bound.**  There are absolute constants
`C₀ > 0` and `t₀` such that for every `m ≥ 1` and `t ≥ t₀`, the number of
primes `q ≤ t` for which `m·q + 1` is also prime is at most
`C₀ · (m/φ(m))² · t / (log t)²`. -/
theorem twin_type_bound :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ t₀ : ℕ, ∀ m t : ℕ, 1 ≤ m → t₀ ≤ t →
      ((#((Finset.Icc 1 t).filter (fun q => q.Prime ∧ (m * q + 1).Prime))) : ℝ)
        ≤ C₀ * ((m : ℝ) / (Nat.totient m)) ^ 2 * t / (Real.log t) ^ 2 := by
  refine ⟨16416, by norm_num, 2 ^ 64, ?_⟩
  intro m t hm ht
  set t1 := t.sqrt with ht1
  set t2 := t1.sqrt with ht2
  set t3 := t2.sqrt with ht3
  set z := t3.sqrt with hzdef
  set w := z.sqrt with hwdef
  -- ℕ-level inequalities between the iterated square roots
  have b1 : t < (t1 + 1) ^ 2 := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' t
  have b2 : t1 < (t2 + 1) ^ 2 := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' t1
  have b3 : t2 < (t3 + 1) ^ 2 := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' t2
  have b4 : t3 < (z + 1) ^ 2 := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' t3
  have b5 : z < (w + 1) ^ 2 := by
    simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' z
  have sq1 : z ^ 2 ≤ t3 := Nat.sqrt_le' t3
  have sq2 : t3 ^ 2 ≤ t2 := Nat.sqrt_le' t2
  have sq3 : t2 ^ 2 ≤ t1 := Nat.sqrt_le' t1
  have sq0 : t1 ^ 2 ≤ t := Nat.sqrt_le' t
  have hwz : w ≤ z := Nat.sqrt_le_self z
  -- from here on the defining equations are no longer needed, and keeping
  -- the local definitions transparent makes `whnf`-heavy tactics time out
  clear_value w z t3 t2 t1
  have hC4 : t < (t2 + 1) ^ 4 := by
    calc t < (t1 + 1) ^ 2 := b1
      _ ≤ ((t2 + 1) ^ 2) ^ 2 := Nat.pow_le_pow_left b2 2
      _ = (t2 + 1) ^ 4 := by ring
  have hB : t < (w + 1) ^ 32 := by
    calc t < (t2 + 1) ^ 4 := hC4
      _ ≤ ((t3 + 1) ^ 2) ^ 4 := Nat.pow_le_pow_left b3 4
      _ = (t3 + 1) ^ 8 := by ring
      _ ≤ ((z + 1) ^ 2) ^ 8 := Nat.pow_le_pow_left b4 8
      _ = (z + 1) ^ 16 := by ring
      _ ≤ ((w + 1) ^ 2) ^ 16 := Nat.pow_le_pow_left b5 16
      _ = (w + 1) ^ 32 := by ring
  have hw2 : 2 ≤ w := by
    by_contra hc
    have h1 : (w + 1) ^ 32 ≤ 2 ^ 32 := Nat.pow_le_pow_left (by omega) 32
    have h2 : (2 : ℕ) ^ 32 ≤ 2 ^ 64 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have hz1 : 1 ≤ z := by omega
  have ht2pos : 2 ≤ t := by
    have h2 : (2 : ℕ) ≤ 2 ^ 64 := by norm_num
    omega
  have hA : z ^ 8 ≤ t1 := by
    calc z ^ 8 = (z ^ 2) ^ 4 := by ring
      _ ≤ t3 ^ 4 := Nat.pow_le_pow_left sq1 4
      _ = (t3 ^ 2) ^ 2 := by ring
      _ ≤ t2 ^ 2 := Nat.pow_le_pow_left sq2 2
      _ ≤ t1 := sq3
  have hzt1 : z ≤ t1 := le_trans (Nat.le_self_pow (by norm_num) z) hA
  -- transfer everything needed to ℝ, in term mode (hypotheses containing
  -- `(x+1)^k` over ℕ send context-scanning tactics into `whnf` divergence)
  have hlog64 : Real.log t ≤ 64 * Real.log w := by
    calc Real.log t ≤ (32 : ℕ) * Real.log ((w : ℝ) + 1) :=
          log_le_mul_log_succ_of_lt_pow (by omega) hB
      _ ≤ (32 : ℕ) * (2 * Real.log w) :=
          mul_le_mul_of_nonneg_left (log_succ_le_two_log hw2) (by norm_num)
      _ = 64 * Real.log w := by push_cast; ring
  have hlog4t2 : Real.log t ≤ 4 * (t2 : ℝ) := by
    calc Real.log t ≤ (4 : ℕ) * Real.log ((t2 : ℝ) + 1) :=
          log_le_mul_log_succ_of_lt_pow (by omega) hC4
      _ ≤ (4 : ℕ) * (t2 : ℝ) :=
          mul_le_mul_of_nonneg_left (log_succ_le_self t2) (by norm_num)
      _ = 4 * (t2 : ℝ) := by push_cast; ring
  have hz8R : ((z : ℕ) : ℝ) ^ 8 ≤ (t1 : ℝ) := by exact_mod_cast hA
  have hzt1R : ((z : ℕ) : ℝ) ≤ (t1 : ℝ) := by exact_mod_cast hzt1
  have ht1tR : ((t1 : ℕ) : ℝ) ^ 2 ≤ (t : ℝ) := by exact_mod_cast sq0
  have ht2t1R : ((t2 : ℕ) : ℝ) ^ 2 ≤ (t1 : ℝ) := by exact_mod_cast sq3
  have htR : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht2pos
  -- discard the ℕ-power hypotheses
  clear b1 b2 b3 b4 b5 hC4 hB hA sq0 sq1 sq2 sq3 hwz hzt1 ht
  have hlogt_pos : 0 < Real.log t := Real.log_pos (by linarith)
  have hlog_sq : (Real.log t) ^ 2 ≤ 16 * (t1 : ℝ) := by
    have h1 : (Real.log t) ^ 2 ≤ (4 * (t2 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hlogt_pos.le hlog4t2 2
    nlinarith [ht2t1R]
  -- apply the sieve
  have hcount := count_le_siftedSum_add (t := t) hm hz1
  have hsel := selberg_bound (twinSieve m z t hz1)
  have herr := twinSieve_errSum_le (m := m) (t := t) hz1
  -- lower bound for the bounding sum
  set S := selbergBoundingSum (twinSieve m z t hz1) with hSdef
  have hSpos : 0 < S := selbergBoundingSum_pos _
  set γ : ℝ := (Nat.totient m : ℝ) / m * Real.log t / 128 with hγdef
  have hφm_pos : (0 : ℝ) < (Nat.totient m : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hγpos : 0 < γ := by
    rw [hγdef]
    positivity
  have hw1R : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast (by omega : 1 ≤ w)
  have hlogw_nonneg : 0 ≤ Real.log w := Real.log_nonneg hw1R
  have h2m_pos : (0 : ℝ) < ((2 * m : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 0 < 2 * m)
  have hSγ : γ ^ 2 ≤ S := by
    have hβ := selbergBoundingSum_ge (t := t) (z := z) hm hz1
    rw [← hwdef] at hβ
    have hγβ : γ ≤ (Nat.totient (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ) * Real.log (w : ℝ) := by
      have hfrac : (Nat.totient m : ℝ) / ((2 * m : ℕ) : ℝ)
          ≤ (Nat.totient (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ) := by
        gcongr
        exact_mod_cast totient_le_totient_two_mul m hm
      have hlogw_ge : Real.log t / 64 ≤ Real.log w := by linarith
      calc γ = ((Nat.totient m : ℝ) / ((2 * m : ℕ) : ℝ)) * (Real.log t / 64) := by
            rw [hγdef]
            push_cast
            ring
        _ ≤ ((Nat.totient (2 * m) : ℝ) / ((2 * m : ℕ) : ℝ)) * Real.log w := by
            apply mul_le_mul hfrac hlogw_ge (by positivity) (by positivity)
    exact le_trans (pow_le_pow_left₀ hγpos.le hγβ 2) hβ
  -- combine the main term
  have hupper : (twinSieve m z t hz1).siftedSum
      ≤ (t : ℝ) / S + ((z : ℕ) : ℝ) ^ 8 :=
    le_trans hsel (add_le_add (le_of_eq rfl) herr)
  have hmain : (t : ℝ) / S ≤ (t : ℝ) / γ ^ 2 := by
    gcongr
  have hγident : (t : ℝ) / γ ^ 2
      = 16384 * ((m : ℝ) / (Nat.totient m)) ^ 2 * t / (Real.log t) ^ 2 := by
    rw [hγdef]
    field_simp
    ring
  have hmain' : (t : ℝ) / S
      ≤ 16384 * ((m : ℝ) / (Nat.totient m)) ^ 2 * t / (Real.log t) ^ 2 :=
    hγident ▸ hmain
  -- combine the error and small-prime terms
  have ht1_nonneg : (0 : ℝ) ≤ (t1 : ℝ) := by positivity
  have h2t1 : 2 * (t1 : ℝ)
      ≤ 32 * ((m : ℝ) / (Nat.totient m)) ^ 2 * t / (Real.log t) ^ 2 := by
    have hX1 : (1 : ℝ) ≤ ((m : ℝ) / (Nat.totient m)) ^ 2 := by
      have h1 : (Nat.totient m : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.totient_le m
      have h2 : (1 : ℝ) ≤ (m : ℝ) / (Nat.totient m) := (one_le_div hφm_pos).mpr h1
      nlinarith
    have hstep : 2 * (t1 : ℝ) ≤ 32 * t / (Real.log t) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hlog_sq
        (by positivity : (0 : ℝ) ≤ 2 * (t1 : ℝ)), ht1tR]
    calc 2 * (t1 : ℝ) ≤ 32 * t / (Real.log t) ^ 2 := hstep
      _ ≤ 32 * ((m : ℝ) / (Nat.totient m)) ^ 2 * t / (Real.log t) ^ 2 := by
          gcongr ?_ / _
          nlinarith [hX1, (by positivity : (0 : ℝ) ≤ (t : ℝ))]
  -- final assembly
  calc ((#((Finset.Icc 1 t).filter (fun q => q.Prime ∧ (m * q + 1).Prime))) : ℝ)
      ≤ (twinSieve m z t hz1).siftedSum + z := hcount
    _ ≤ ((t : ℝ) / S + ((z : ℕ) : ℝ) ^ 8) + z := by linarith [hupper]
    _ ≤ (t : ℝ) / S + 2 * (t1 : ℝ) := by linarith [hz8R, hzt1R]
    _ ≤ 16384 * ((m : ℝ) / (Nat.totient m)) ^ 2 * t / (Real.log t) ^ 2
          + 32 * ((m : ℝ) / (Nat.totient m)) ^ 2 * t / (Real.log t) ^ 2 := by
        linarith [hmain', h2t1]
    _ = 16416 * ((m : ℝ) / (Nat.totient m)) ^ 2 * t / (Real.log t) ^ 2 := by
        ring

end

end Carmichael
