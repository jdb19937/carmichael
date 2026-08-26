/-
E-generic version of Lemma 4.4 (`Carmichael/Output.lean`): the output is
Carmichael and lies in `(n, n^{1+ε}]`, with the smoothness scale
`y = ⌈z^{1-E}⌉` for any fixed `0 < E ≤ 1/2`. Proved from Korselt's
criterion and divisibility bookkeeping; the only change from the `E = 1/3`
instance is the overshoot arithmetic, which here runs through
`ℓ₃^{2-E} ≤ ℓ₃² ≤ ℓ₂^{E/2}` (from `Carmichael/LogPow.lean`).
-/
import Carmichael.Defs
import Carmichael.Korselt
import Carmichael.LogPow

set_option autoImplicit false

namespace Carmichael

open Filter Finset

/-! ### Elementary bookkeeping lemmas -/

/-- Unpack membership in the pool of step 3. -/
private lemma mem_pool {Q : Finset ℕ} {z k p : ℕ} (hp : p ∈ pool Q z k) :
    p.Prime ∧ p ≤ xceil Q ∧ z < p ∧ ∃ d, d ∣ Lmod Q ∧ p = d * k + 1 := by
  simp only [pool, Finset.mem_image, Finset.mem_filter, Nat.mem_divisors] at hp
  obtain ⟨d, ⟨⟨hdvd, -⟩, hle, hpr, hz⟩, rfl⟩ := hp
  exact ⟨hpr, hle, hz, d, hdvd, rfl⟩

/-- Unpack membership in the reservoir of good primes (generic `E`). -/
private lemma mem_goodPrimesE {C₁ E : ℝ} {n q : ℕ} (hq : q ∈ goodPrimesE C₁ n E) :
    q.Prime ∧ q ≤ zscale C₁ n ∧ SmoothUpTo (yscaleE C₁ n E) (q - 1) := by
  simp only [goodPrimesE, Finset.mem_filter, Finset.mem_range] at hq
  exact ⟨hq.2.1, by omega, hq.2.2.2⟩

/-- A product of distinct primes is squarefree. -/
private lemma prod_primes_squarefree (S : Finset ℕ) :
    (∀ p ∈ S, p.Prime) → Squarefree (∏ p ∈ S, p) := by
  induction S using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.prod_empty]
    exact squarefree_one
  | @insert a s ha ih =>
    intro h
    have hap : a.Prime := h a (Finset.mem_insert_self a s)
    have hs : ∀ p ∈ s, p.Prime := fun p hp => h p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (∏ p ∈ s, p) :=
      Nat.Coprime.prod_right fun p hp =>
        (Nat.coprime_primes hap (hs p hp)).mpr fun he => ha (he ▸ hp)
    rw [Finset.prod_insert ha]
    exact (Nat.squarefree_mul hcop).mpr ⟨hap.squarefree, ih hs⟩

/-- A product of naturals that are all `≡ 1 (mod k)` is `≡ 1 (mod k)`. -/
private lemma prod_modEq_one {k : ℕ} (S : Finset ℕ) :
    (∀ p ∈ S, p ≡ 1 [MOD k]) → (∏ p ∈ S, p) ≡ 1 [MOD k] := by
  induction S using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.prod_empty]
  | @insert a s ha ih =>
    intro h
    rw [Finset.prod_insert ha]
    have h1 := h a (Finset.mem_insert_self a s)
    have h2 := ih fun p hp => h p (Finset.mem_insert_of_mem hp)
    simpa using h1.mul h2

/-- Smoothness bound for the exponent of `(ℤ/L)ˣ`: since every `q - 1` is
`y`-smooth and at most `z`, the lcm of the `q - 1` divides
`∏_{p ≤ y} p^{⌊log_p z⌋} ≤ z^{y+1}`. -/
private lemma lambdaL_le_pow {Q : Finset ℕ} {y z : ℕ} (hz : z ≠ 0)
    (hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ z ∧ SmoothUpTo y (q - 1)) :
    lambdaL Q ≤ z ^ (y + 1) := by
  have hMdvd : lambdaL Q ∣ ∏ p ∈ (y + 1).primesBelow, p ^ Nat.log p z := by
    refine Finset.lcm_dvd fun q hq => ?_
    obtain ⟨hqp, hqz, hsm⟩ := hQ q hq
    have hq1 : q - 1 ≠ 0 := by have := hqp.two_le; omega
    have heq : ∏ p ∈ (q - 1).primeFactors, p ^ (q - 1).factorization p = q - 1 := by
      conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hq1]
      rfl
    show q - 1 ∣ ∏ p ∈ (y + 1).primesBelow, p ^ Nat.log p z
    rw [← heq]
    refine dvd_trans (Finset.prod_dvd_prod_of_dvd _ _ fun p hp => ?_)
      (Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => ?_)
    · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpd : p ^ (q - 1).factorization p ∣ q - 1 :=
        (Nat.Prime.pow_dvd_iff_le_factorization hpp hq1).mpr le_rfl
      have hle : p ^ (q - 1).factorization p ≤ z :=
        le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hq1) hpd)
          (le_trans (Nat.sub_le q 1) hqz)
      exact pow_dvd_pow p ((Nat.le_log_iff_pow_le hpp.one_lt hz).mpr hle)
    · have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact Nat.mem_primesBelow.mpr
        ⟨Nat.lt_succ_of_le (hsm p hpp (Nat.dvd_of_mem_primeFactors hp)), hpp⟩
  have hM0 : 0 < ∏ p ∈ (y + 1).primesBelow, p ^ Nat.log p z :=
    Finset.prod_pos fun p hp => pow_pos (Nat.prime_of_mem_primesBelow hp).pos _
  have hcard : (y + 1).primesBelow.card ≤ y + 1 := by
    have hsub : (y + 1).primesBelow ⊆ Finset.range (y + 1) := fun p hp =>
      Finset.mem_range.mpr (Nat.mem_primesBelow.mp hp).1
    simpa using Finset.card_le_card hsub
  calc lambdaL Q ≤ ∏ p ∈ (y + 1).primesBelow, p ^ Nat.log p z := Nat.le_of_dvd hM0 hMdvd
    _ ≤ z ^ (y + 1).primesBelow.card :=
        Finset.prod_le_pow_card _ _ _ fun p _ => Nat.pow_log_le_self p hz
    _ ≤ z ^ (y + 1) := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hz) hcard

/-! ### The analytic eventual bounds

All quantitative facts about the scales that are needed for `n` large,
phrased in terms of the single variable `u = ℓ₂(n) → ∞`. The only
difference from `Output.lean` is the third conjunct, whose exponent
arithmetic runs through `v^{2-E} ≤ v² ≤ u^{E/2}` instead of the
`(2/3, 29/36, 7/36)` juggling. -/

private lemma eventually_uE (ε C₁ E : ℝ) (hε : 0 < ε) (hC₁ : 1 ≤ C₁)
    (hE : 0 < E) (hE2 : E ≤ 1 / 2) :
    ∀ᶠ u : ℝ in atTop,
      1 ≤ ⌈C₁ * u * Real.log u⌉₊ ∧
      (⌈C₁ * u * Real.log u⌉₊ : ℝ) ^ (10 * ⌈(3 : ℝ) * u⌉₊) ≤ Real.exp (Real.exp u) ∧
      ((⌈C₁ * u * Real.log u⌉₊ : ℝ) ^
            (⌈(⌈C₁ * u * Real.log u⌉₊ : ℝ) ^ ((1 : ℝ) - E)⌉₊ + 1) *
            (1 + (⌈(3 : ℝ) * u⌉₊ : ℝ) * Real.log (⌈C₁ * u * Real.log u⌉₊ : ℝ)) + 2) *
          (5 * (⌈(3 : ℝ) * u⌉₊ : ℝ) * Real.log (⌈C₁ * u * Real.log u⌉₊ : ℝ)) ≤
        ε * Real.exp u := by
  -- auxiliary eventual facts
  have hexp2 : ∀ᶠ u : ℝ in atTop, 120 * u ^ 2 ≤ Real.exp u := by
    filter_upwards [(Real.tendsto_exp_div_pow_atTop 2).eventually_ge_atTop 120,
      eventually_gt_atTop (0 : ℝ)] with u h hu0
    have h2 := (le_div_iff₀ (pow_pos hu0 2)).mp h
    linarith
  have hlog12 : ∀ᶠ u : ℝ in atTop, Real.log u ≤ u ^ ((1 : ℝ) / 12) := by
    filter_upwards [(isLittleO_log_rpow_atTop
        (by norm_num : (0 : ℝ) < 1 / 12)).eventuallyLE,
      eventually_ge_atTop (0 : ℝ)] with u h hu0
    calc Real.log u ≤ ‖Real.log u‖ := by
          rw [Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ ‖u ^ ((1 : ℝ) / 12)‖ := h
      _ = u ^ ((1 : ℝ) / 12) := by
          rw [Real.norm_eq_abs]; exact abs_of_nonneg (Real.rpow_nonneg hu0 _)
  filter_upwards [eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.log (2 * C₁)),
    hexp2, hlog12,
    (tendsto_rpow_atTop (half_pos hE)).eventually_ge_atTop (12 * C₁),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 11 / 12)).eventually_ge_atTop 40,
    eventually_ge_atTop (4 * (Real.log 900 - Real.log ε)),
    eventually_log_sq_le_rpow (half_pos hE)]
    with u hu3 hv1 hvC hexpu hlogu hK h40 hc0 hsq
  have hu0 : (0 : ℝ) < u := by linarith
  have hv0 : (0 : ℝ) < Real.log u := by linarith
  have hvu : Real.log u ≤ u := by
    have := Real.log_le_sub_one_of_pos hu0
    linarith
  have hCuv1 : (1 : ℝ) ≤ C₁ * u * Real.log u := by
    nlinarith [mul_le_mul_of_nonneg_right hC₁ (mul_nonneg hu0.le hv0.le),
      mul_le_mul_of_nonneg_left hv1 hu0.le]
  have hCuv0 : (0 : ℝ) < C₁ * u * Real.log u := by linarith
  have hz1 : 1 ≤ ⌈C₁ * u * Real.log u⌉₊ := Nat.one_le_ceil_iff.mpr hCuv0
  have hZ1 : (1 : ℝ) ≤ (⌈C₁ * u * Real.log u⌉₊ : ℝ) := by exact_mod_cast hz1
  have hZ0 : (0 : ℝ) < (⌈C₁ * u * Real.log u⌉₊ : ℝ) := by linarith
  have hZub : (⌈C₁ * u * Real.log u⌉₊ : ℝ) ≤ 2 * C₁ * u * Real.log u := by
    have h := Nat.ceil_lt_add_one hCuv0.le
    linarith
  have hlZ : Real.log (⌈C₁ * u * Real.log u⌉₊ : ℝ) ≤ 3 * Real.log u := by
    have h1 : Real.log (⌈C₁ * u * Real.log u⌉₊ : ℝ) ≤ Real.log (2 * C₁ * u * Real.log u) :=
      (Real.log_le_log_iff hZ0 (by linarith)).mpr hZub
    have h2 : Real.log (2 * C₁ * u * Real.log u)
        = Real.log (2 * C₁) + Real.log u + Real.log (Real.log u) := by
      rw [show 2 * C₁ * u * Real.log u = 2 * C₁ * (u * Real.log u) by ring,
        Real.log_mul (ne_of_gt (by linarith : (0 : ℝ) < 2 * C₁)) (ne_of_gt (mul_pos hu0 hv0)),
        Real.log_mul hu0.ne' hv0.ne']
      ring
    have h3 : Real.log (Real.log u) ≤ Real.log u := by
      have := Real.log_le_sub_one_of_pos hv0
      linarith
    linarith [hvC]
  have hlZ0 : (0 : ℝ) ≤ Real.log (⌈C₁ * u * Real.log u⌉₊ : ℝ) := Real.log_nonneg hZ1
  have hTub : (⌈(3 : ℝ) * u⌉₊ : ℝ) ≤ 4 * u := by
    have h := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 3 * u)
    linarith
  have hTc0 : (0 : ℝ) ≤ (⌈(3 : ℝ) * u⌉₊ : ℝ) := Nat.cast_nonneg _
  set v := Real.log u with hvdef
  set Z := (⌈C₁ * u * v⌉₊ : ℝ) with hZdef
  set Tc := (⌈(3 : ℝ) * u⌉₊ : ℝ) with hTcdef
  set yc := ⌈Z ^ ((1 : ℝ) - E)⌉₊ with hycdef
  have huv0 : (0 : ℝ) ≤ u * v := mul_nonneg hu0.le hv0.le
  have huv1 : (1 : ℝ) ≤ u * v := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ u - 3) (by linarith : (0 : ℝ) ≤ v - 1)]
  refine ⟨hz1, ?_, ?_⟩
  · -- (z : ℝ) ^ (10 T) ≤ n
    have heq : Z ^ (10 * ⌈(3 : ℝ) * u⌉₊)
        = Real.exp (((10 * ⌈(3 : ℝ) * u⌉₊ : ℕ) : ℝ) * Real.log Z) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos hZ0 _)]
    rw [heq, show ((10 * ⌈(3 : ℝ) * u⌉₊ : ℕ) : ℝ) = 10 * Tc by rw [hTcdef]; push_cast; ring]
    apply Real.exp_le_exp.mpr
    have h1 : Tc * Real.log Z ≤ 4 * u * (3 * v) := mul_le_mul hTub hlZ hlZ0 (by linarith)
    have h2 : u * v ≤ u * u := mul_le_mul_of_nonneg_left hvu hu0.le
    linarith [hexpu]
  · -- the overshoot bound, generic-E route
    have hW0 : (0 : ℝ) ≤ 6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v := by
      have h1 : (0 : ℝ) ≤ 6 * C₁ * u ^ ((1 : ℝ) - E / 2) :=
        mul_nonneg (by linarith) (Real.rpow_nonneg hu0.le _)
      linarith
    -- (yc + 1) · log Z ≤ 6 C₁ u^{1 - E/2} + 6 v
    have hyub : (yc : ℝ) + 1 ≤ Z ^ ((1 : ℝ) - E) + 2 := by
      have h1 : (yc : ℝ) < Z ^ ((1 : ℝ) - E) + 1 :=
        Nat.ceil_lt_add_one (Real.rpow_nonneg hZ0.le _)
      linarith
    have h1E0 : (0 : ℝ) ≤ 1 - E := by linarith
    have h2Cuv0 : (0 : ℝ) ≤ 2 * C₁ * u * v :=
      mul_nonneg (mul_nonneg (by linarith) hu0.le) hv0.le
    have hZE : Z ^ ((1 : ℝ) - E) ≤ (2 * C₁ * u * v) ^ ((1 : ℝ) - E) :=
      Real.rpow_le_rpow hZ0.le hZub h1E0
    have hZE0 : (0 : ℝ) ≤ (2 * C₁ * u * v) ^ ((1 : ℝ) - E) :=
      Real.rpow_nonneg h2Cuv0 _
    have hsplit : (2 * C₁ * u * v) ^ ((1 : ℝ) - E)
        = (2 * C₁) ^ ((1 : ℝ) - E) * (u ^ ((1 : ℝ) - E) * v ^ ((1 : ℝ) - E)) := by
      rw [show 2 * C₁ * u * v = 2 * C₁ * (u * v) by ring,
        Real.mul_rpow (by linarith) huv0, Real.mul_rpow hu0.le hv0.le]
    have h2C : (2 * C₁) ^ ((1 : ℝ) - E) ≤ 2 * C₁ := by
      calc (2 * C₁) ^ ((1 : ℝ) - E) ≤ (2 * C₁) ^ ((1 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 2 * C₁ := Real.rpow_one _
    have hv2E : v ^ ((2 : ℝ) - E) ≤ u ^ (E / 2) := by
      calc v ^ ((2 : ℝ) - E) ≤ v ^ ((2 : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hv1 (by linarith)
        _ = v ^ (2 : ℕ) := by
            rw [← Real.rpow_natCast v 2]; norm_num
        _ ≤ u ^ (E / 2) := hsq
    have hvv : v ^ ((1 : ℝ) - E) * v = v ^ ((2 : ℝ) - E) := by
      rw [← Real.rpow_add_one hv0.ne', show (1 : ℝ) - E + 1 = 2 - E by ring]
    have hZlog : Z ^ ((1 : ℝ) - E) * Real.log Z ≤ 6 * C₁ * u ^ ((1 : ℝ) - E / 2) := by
      have hnn : (0 : ℝ) ≤ u ^ ((1 : ℝ) - E) * v ^ ((2 : ℝ) - E) :=
        mul_nonneg (Real.rpow_nonneg hu0.le _) (Real.rpow_nonneg hv0.le _)
      have h4 : u ^ ((1 : ℝ) - E) * v ^ ((2 : ℝ) - E) ≤ u ^ ((1 : ℝ) - E) * u ^ (E / 2) :=
        mul_le_mul_of_nonneg_left hv2E (Real.rpow_nonneg hu0.le _)
      have h5 : u ^ ((1 : ℝ) - E) * u ^ (E / 2) = u ^ ((1 : ℝ) - E / 2) := by
        rw [← Real.rpow_add hu0, show (1 : ℝ) - E + E / 2 = 1 - E / 2 by ring]
      calc Z ^ ((1 : ℝ) - E) * Real.log Z
          ≤ (2 * C₁ * u * v) ^ ((1 : ℝ) - E) * (3 * v) :=
            mul_le_mul hZE hlZ hlZ0 hZE0
        _ = 3 * (2 * C₁) ^ ((1 : ℝ) - E) * (u ^ ((1 : ℝ) - E) * v ^ ((2 : ℝ) - E)) := by
            rw [hsplit, ← hvv]; ring
        _ ≤ 3 * (2 * C₁) * (u ^ ((1 : ℝ) - E) * v ^ ((2 : ℝ) - E)) :=
            mul_le_mul_of_nonneg_right (by linarith) hnn
        _ ≤ 3 * (2 * C₁) * (u ^ ((1 : ℝ) - E) * u ^ (E / 2)) :=
            mul_le_mul_of_nonneg_left h4 (by linarith)
        _ = 6 * C₁ * u ^ ((1 : ℝ) - E / 2) := by rw [h5]; ring
    have hylog : ((yc : ℝ) + 1) * Real.log Z
        ≤ 6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v := by
      have h1 : ((yc : ℝ) + 1) * Real.log Z ≤ (Z ^ ((1 : ℝ) - E) + 2) * Real.log Z :=
        mul_le_mul_of_nonneg_right hyub hlZ0
      have h2 : (Z ^ ((1 : ℝ) - E) + 2) * Real.log Z
          = Z ^ ((1 : ℝ) - E) * Real.log Z + 2 * Real.log Z := by ring
      have h3 : 2 * Real.log Z ≤ 6 * v := by linarith [hlZ]
      linarith [hZlog]
    -- Z^(yc+1) ≤ exp(6 C₁ u^{1 - E/2} + 6 v)
    have hZpow : Z ^ (yc + 1)
        ≤ Real.exp (6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v) := by
      have heq : Z ^ (yc + 1) = Real.exp (((yc + 1 : ℕ) : ℝ) * Real.log Z) := by
        rw [← Real.log_pow, Real.exp_log (pow_pos hZ0 _)]
      rw [heq, show ((yc + 1 : ℕ) : ℝ) = (yc : ℝ) + 1 by push_cast; ring]
      exact Real.exp_le_exp.mpr hylog
    have hexpW1 : (1 : ℝ) ≤ Real.exp (6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v) := by
      have h0 := Real.exp_le_exp.mpr hW0
      rwa [Real.exp_zero] at h0
    have h1 : Tc * Real.log Z ≤ 4 * u * (3 * v) := mul_le_mul hTub hlZ hlZ0 (by linarith)
    have hP : 1 + Tc * Real.log Z ≤ 13 * (u * v) := by linarith
    have hP0 : (0 : ℝ) ≤ 1 + Tc * Real.log Z := by linarith [mul_nonneg hTc0 hlZ0]
    have hR : 5 * Tc * Real.log Z ≤ 60 * (u * v) := by linarith
    have hR0 : (0 : ℝ) ≤ 5 * Tc * Real.log Z := by linarith [mul_nonneg hTc0 hlZ0]
    have hEP : Z ^ (yc + 1) * (1 + Tc * Real.log Z) + 2
        ≤ 15 * (Real.exp (6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v) * (u * v)) := by
      have h3 : Z ^ (yc + 1) * (1 + Tc * Real.log Z)
          ≤ Real.exp (6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v) * (13 * (u * v)) :=
        mul_le_mul hZpow hP hP0 (Real.exp_pos _).le
      have h4 : (1 : ℝ)
          ≤ Real.exp (6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v) * (u * v) := by
        calc (1 : ℝ) = 1 * 1 := by ring
          _ ≤ _ := mul_le_mul hexpW1 huv1 (by norm_num) (Real.exp_pos _).le
      linarith [h3, h4]
    have hEP0 : (0 : ℝ)
        ≤ 15 * (Real.exp (6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v) * (u * v)) :=
      mul_nonneg (by norm_num) (mul_nonneg (Real.exp_pos _).le huv0)
    have huv_u2 : u * v ≤ u * u := mul_le_mul_of_nonneg_left hvu hu0.le
    have hexp4v : Real.exp (4 * v) = u ^ (4 : ℕ) := by
      rw [show (4 : ℝ) * v = Real.log (u ^ (4 : ℕ)) by rw [Real.log_pow]; push_cast; ring,
        Real.exp_log (pow_pos hu0 4)]
    -- the two little-o facts, in the form of linear bounds
    have hF1 : 6 * C₁ * u ^ ((1 : ℝ) - E / 2) ≤ u / 2 := by
      have h2 : 12 * C₁ * u ^ ((1 : ℝ) - E / 2) ≤ u ^ (E / 2) * u ^ ((1 : ℝ) - E / 2) :=
        mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hu0.le _)
      have h3 : u ^ (E / 2) * u ^ ((1 : ℝ) - E / 2) = u := by
        rw [← Real.rpow_add hu0, show E / 2 + ((1 : ℝ) - E / 2) = 1 by ring, Real.rpow_one]
      linarith
    have hF2 : 10 * v ≤ u / 4 := by
      have e1 : u ^ ((11 : ℝ) / 12) * u ^ ((1 : ℝ) / 12) = u := by
        rw [← Real.rpow_add hu0, show (11 : ℝ) / 12 + 1 / 12 = 1 by norm_num, Real.rpow_one]
      have e2 : 40 * u ^ ((1 : ℝ) / 12) ≤ u ^ ((11 : ℝ) / 12) * u ^ ((1 : ℝ) / 12) :=
        mul_le_mul_of_nonneg_right h40 (Real.rpow_nonneg hu0.le _)
      rw [e1] at e2
      have e3 : 40 * v ≤ 40 * u ^ ((1 : ℝ) / 12) := by linarith [hlogu]
      linarith
    have hlin : (6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v) + (Real.log 900 + 4 * v)
        ≤ Real.log ε + u := by
      linarith [hF1, hF2, hc0]
    calc (Z ^ (yc + 1) * (1 + Tc * Real.log Z) + 2) * (5 * Tc * Real.log Z)
        ≤ (15 * (Real.exp (6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v) * (u * v)))
            * (60 * (u * v)) := mul_le_mul hEP hR hR0 hEP0
      _ = 900 * (Real.exp (6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v)
            * ((u * v) * (u * v))) := by ring
      _ ≤ 900 * (Real.exp (6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v)
            * u ^ (4 : ℕ)) := by
          have h5 : (u * v) * (u * v) ≤ u ^ (4 : ℕ) := by
            calc (u * v) * (u * v) ≤ (u * u) * (u * u) :=
                  mul_le_mul huv_u2 huv_u2 huv0 (mul_nonneg hu0.le hu0.le)
              _ = u ^ (4 : ℕ) := by ring
          have h6 := mul_le_mul_of_nonneg_left h5 (Real.exp_pos
            (6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v)).le
          linarith
      _ = Real.exp ((6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v)
            + (Real.log 900 + 4 * v)) := by
          rw [Real.exp_add (6 * C₁ * u ^ ((1 : ℝ) - E / 2) + 6 * v)
              (Real.log 900 + 4 * v),
            Real.exp_add (Real.log 900) (4 * v), hexp4v,
            Real.exp_log (by norm_num : (0 : ℝ) < 900)]
          ring
      _ ≤ Real.exp (Real.log ε + u) := Real.exp_le_exp.mpr hlin
      _ = ε * Real.exp u := by rw [Real.exp_add, Real.exp_log hε]

/-! ### The main lemma -/

/-- E-generic Lemma 4.4 (the output is Carmichael, in `(n, n^{1+ε}]`): any
subset of the pool as produced by `extraction`, with the reservoir built at
smoothness scale `y = ⌈z^{1-E}⌉` for a fixed `0 < E ≤ 1/2`, is a Carmichael
number with at least three prime factors, and the overshoot `x^{N*}` is at
most `n^ε` for `n` large. Uses Korselt's criterion. -/
theorem output_carmichaelE (C₁ E : ℝ) (hE : 0 < E) (hE2 : E ≤ 1 / 2)
    (h1000 : (1000 : ℝ) ≤ C₁) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ Q ⊆ goodPrimesE C₁ n E, Q.card = Tscale n →
      ∀ k : ℕ, 0 < k → k.Coprime (Lmod Q) →
      ∀ S : Finset ℕ, S ⊆ pool Q (zscale C₁ n) k → S.Nonempty →
      (∏ p ∈ S, p) ≡ 1 [MOD Lmod Q] →
      n < ∏ p ∈ S, p →
      ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (n : ℝ) * (xceil Q : ℝ) ^ (Nstar Q : ℕ) →
      (∀ p ∈ S, p.Prime) ∧ 3 ≤ S.card ∧ IsCarmichael (∏ p ∈ S, p) ∧
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 + ε) := by
  have hC₁ : (1 : ℝ) ≤ C₁ := le_trans (by norm_num) h1000
  have htend : Tendsto (fun n : ℕ => ell2 n) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp h1)
  filter_upwards [htend.eventually (eventually_uE ε C₁ E hε hC₁ hE hE2),
    eventually_ge_atTop 2]
    with n hpack hn2
  obtain ⟨hz1c, hP2c, hP3c⟩ := hpack
  -- translate the eventual facts to the scale functions (all `rfl`-conversions)
  have hz1' : 1 ≤ zscale C₁ n := hz1c
  have hP2' : ((zscale C₁ n : ℝ)) ^ (10 * Tscale n) ≤ Real.exp (Real.exp (ell2 n)) := hP2c
  have hP3' : (((zscale C₁ n : ℝ)) ^ (yscaleE C₁ n E + 1) *
        (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ)) + 2) *
      (5 * (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ)) ≤ ε * Real.exp (ell2 n) := hP3c
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have h1n : (1 : ℝ) < (n : ℝ) := by
    have : (1 : ℕ) < n := by omega
    exact_mod_cast this
  have hlogn : Real.exp (ell2 n) = Real.log n := Real.exp_log (Real.log_pos h1n)
  have hnexp : Real.exp (Real.exp (ell2 n)) = (n : ℝ) := by
    rw [hlogn]; exact Real.exp_log hn0
  rw [hnexp] at hP2'
  rw [hlogn] at hP3'
  have hP2nat : zscale C₁ n ^ (10 * Tscale n) ≤ n := by exact_mod_cast hP2'
  -- now the actual argument
  intro Q hQg hQT k hk0 hkL S hSp hSne hmodL hlt hub
  have hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ zscale C₁ n ∧ SmoothUpTo (yscaleE C₁ n E) (q - 1) :=
    fun q hq => mem_goodPrimesE (hQg hq)
  have hpool : ∀ p ∈ S, p.Prime ∧ p ≤ xceil Q ∧ zscale C₁ n < p ∧
      ∃ d, d ∣ Lmod Q ∧ p = d * k + 1 := fun p hp => mem_pool (hSp hp)
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => (hpool p hp).1
  have hL1 : 1 ≤ Lmod Q := Finset.one_le_prod' fun q hq => (hQ q hq).1.one_lt.le
  have hLzT : Lmod Q ≤ zscale C₁ n ^ Tscale n := by
    rw [← hQT]
    exact Finset.prod_le_pow_card Q (fun q => q) _ fun q hq => (hQ q hq).2.1
  have hx1 : 1 ≤ xceil Q := Nat.one_le_pow _ _ (by omega)
  have hxzT : xceil Q ≤ zscale C₁ n ^ (5 * Tscale n) := by
    calc xceil Q = Lmod Q ^ 5 := rfl
      _ ≤ (zscale C₁ n ^ Tscale n) ^ 5 := Nat.pow_le_pow_left hLzT 5
      _ = zscale C₁ n ^ (5 * Tscale n) := by rw [← pow_mul, mul_comm]
  -- at least three prime factors
  have hcard3 : 3 ≤ S.card := by
    by_contra hc
    have h1 : (∏ p ∈ S, p) ≤ xceil Q ^ S.card :=
      Finset.prod_le_pow_card S (fun p => p) _ fun p hp => (hpool p hp).2.1
    have hfin : (∏ p ∈ S, p) ≤ n := by
      calc (∏ p ∈ S, p) ≤ xceil Q ^ S.card := h1
        _ ≤ (zscale C₁ n ^ (5 * Tscale n)) ^ S.card := Nat.pow_le_pow_left hxzT _
        _ = zscale C₁ n ^ (5 * Tscale n * S.card) := (pow_mul _ _ _).symm
        _ ≤ zscale C₁ n ^ (10 * Tscale n) := by
            refine Nat.pow_le_pow_right (by omega) ?_
            calc 5 * Tscale n * S.card ≤ 5 * Tscale n * 2 :=
                  Nat.mul_le_mul_left _ (by omega)
              _ = 10 * Tscale n := by ring
        _ ≤ n := hP2nat
    exact absurd hlt (not_lt.mpr hfin)
  -- basic facts about m = ∏ S
  have hm1 : 1 < ∏ p ∈ S, p := lt_of_le_of_lt (by omega : 1 ≤ n) hlt
  have hsqf : Squarefree (∏ p ∈ S, p) := prod_primes_squarefree S hSprime
  -- m ≡ 1 (mod kL)
  have hmodk : (∏ p ∈ S, p) ≡ 1 [MOD k] := by
    refine prod_modEq_one S fun p hp => ?_
    obtain ⟨d, hd, hpe⟩ := (hpool p hp).2.2.2
    rw [hpe]
    refine ((Nat.modEq_iff_dvd' (Nat.le_add_left 1 (d * k))).mpr ?_).symm
    simp only [Nat.add_sub_cancel]
    exact dvd_mul_left k d
  have hmodkL : (∏ p ∈ S, p) ≡ 1 [MOD k * Lmod Q] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hkL).mp ⟨hmodk, hmodL⟩
  have hdvdkL : k * Lmod Q ∣ (∏ p ∈ S, p) - 1 :=
    (Nat.modEq_iff_dvd' hm1.le).mp hmodkL.symm
  -- the Korselt divisibility condition
  have hkors : ∀ p : ℕ, p.Prime → p ∣ (∏ p ∈ S, p) → (p - 1) ∣ ((∏ p ∈ S, p) - 1) := by
    intro p hp hpd
    obtain ⟨q, hqS, hpq⟩ := (hp.prime.dvd_finsetProd_iff (fun x => x)).mp hpd
    have hpq' : p = q := (Nat.prime_dvd_prime_iff_eq hp (hSprime q hqS)).mp hpq
    subst hpq'
    obtain ⟨d, hd, hpe⟩ := (hpool p hqS).2.2.2
    have h1 : p - 1 = d * k := by rw [hpe]; simp
    rw [h1]
    refine dvd_trans ?_ hdvdkL
    rw [mul_comm k (Lmod Q)]
    exact mul_dvd_mul_right hd k
  -- m is not prime
  have hnp : ¬ (∏ p ∈ S, p).Prime := by
    intro hmp
    obtain ⟨p, hpS⟩ := hSne
    have hpp := hSprime p hpS
    have hme : p * ∏ q ∈ S.erase p, q = ∏ q ∈ S, q :=
      Finset.mul_prod_erase S (fun q => q) hpS
    have ht := hmp.eq_one_or_self_of_dvd (∏ q ∈ S.erase p, q)
      (Finset.prod_dvd_prod_of_subset _ _ (fun x => x) (Finset.erase_subset p S))
    obtain ⟨q, hq⟩ : (S.erase p).Nonempty := Finset.card_pos.mp
      (by rw [Finset.card_erase_of_mem hpS]; omega)
    have hq2 : 2 ≤ q := (hSprime q (Finset.mem_of_mem_erase hq)).two_le
    have hqt : q ∣ ∏ x ∈ S.erase p, x := Finset.dvd_prod_of_mem _ hq
    rcases ht with h1 | h1
    · rw [h1] at hqt
      have := Nat.dvd_one.mp hqt
      omega
    · rw [h1] at hme
      have h3 : p = 1 := by
        refine Nat.eq_of_mul_eq_mul_right (show 0 < ∏ q ∈ S, q by omega) ?_
        rw [one_mul]
        rw [mul_comm p _] at hme
        rw [mul_comm]
        exact hme
      exact absurd h3 hpp.ne_one
  have hcar : IsCarmichael (∏ p ∈ S, p) :=
    (korselt _ hm1 hnp).mpr ⟨hsqf, hkors⟩
  -- the overshoot bound
  have hlam : lambdaL Q ≤ zscale C₁ n ^ (yscaleE C₁ n E + 1) :=
    lambdaL_le_pow (by omega) hQ
  have hZ0R : (0 : ℝ) < (zscale C₁ n : ℝ) := by
    have : (0 : ℕ) < zscale C₁ n := by omega
    exact_mod_cast this
  have hZ1R : (1 : ℝ) ≤ (zscale C₁ n : ℝ) := by exact_mod_cast hz1'
  have hlZ0 : (0 : ℝ) ≤ Real.log (zscale C₁ n : ℝ) := Real.log_nonneg hZ1R
  have hL0R : (0 : ℝ) < (Lmod Q : ℝ) := by
    have : (0 : ℕ) < Lmod Q := by omega
    exact_mod_cast this
  have hL1R : (1 : ℝ) ≤ (Lmod Q : ℝ) := by exact_mod_cast hL1
  have hlogL0 : (0 : ℝ) ≤ Real.log (Lmod Q : ℝ) := Real.log_nonneg hL1R
  have hlogL : Real.log (Lmod Q : ℝ) ≤ (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ) := by
    have h1 : Real.log (Lmod Q : ℝ) ≤ Real.log ((zscale C₁ n : ℝ) ^ Tscale n) := by
      refine (Real.log_le_log_iff hL0R (pow_pos hZ0R _)).mpr ?_
      exact_mod_cast hLzT
    rwa [Real.log_pow] at h1
  have hlamR : (lambdaL Q : ℝ) ≤ (zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) := by
    exact_mod_cast hlam
  have hNstar : (Nstar Q : ℝ) ≤ (lambdaL Q : ℝ) * (1 + Real.log (Lmod Q : ℝ)) + 2 := by
    have h2 : Nstar Q = ⌈(lambdaL Q : ℝ) * (1 + Real.log (Lmod Q : ℝ))⌉₊ + 1 := rfl
    have h1 : (⌈(lambdaL Q : ℝ) * (1 + Real.log (Lmod Q : ℝ))⌉₊ : ℝ)
        < (lambdaL Q : ℝ) * (1 + Real.log (Lmod Q : ℝ)) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg (Nat.cast_nonneg _) (by linarith))
    have h3 : (Nstar Q : ℝ)
        = (⌈(lambdaL Q : ℝ) * (1 + Real.log (Lmod Q : ℝ))⌉₊ : ℝ) + 1 := by
      rw [h2]; push_cast; ring
    linarith
  have hNle : (Nstar Q : ℝ) ≤ (zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) *
      (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ)) + 2 := by
    have h3 : (lambdaL Q : ℝ) * (1 + Real.log (Lmod Q : ℝ))
        ≤ (zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) *
          (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ)) :=
      mul_le_mul hlamR (by linarith) (by linarith) (by positivity)
    linarith
  have hx0R : (0 : ℝ) < (xceil Q : ℝ) := by
    have : (0 : ℕ) < xceil Q := by omega
    exact_mod_cast this
  have hx1R : (1 : ℝ) ≤ (xceil Q : ℝ) := by exact_mod_cast hx1
  have hlogx0 : (0 : ℝ) ≤ Real.log (xceil Q : ℝ) := Real.log_nonneg hx1R
  have hlogx : Real.log (xceil Q : ℝ)
      ≤ 5 * (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ) := by
    have h1 : Real.log (xceil Q : ℝ) = 5 * Real.log (Lmod Q : ℝ) := by
      rw [show ((xceil Q : ℕ) : ℝ) = ((Lmod Q : ℕ) : ℝ) ^ (5 : ℕ) by push_cast [xceil]; ring,
        Real.log_pow]
      push_cast
      ring
    rw [h1]
    nlinarith [hlogL]
  have hNs0 : (0 : ℝ) ≤ (Nstar Q : ℝ) := Nat.cast_nonneg _
  have hfin : (Nstar Q : ℝ) * Real.log (xceil Q : ℝ) ≤ ε * Real.log n := by
    calc (Nstar Q : ℝ) * Real.log (xceil Q : ℝ)
        ≤ ((zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) *
            (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ)) + 2) *
          (5 * (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ)) :=
          mul_le_mul hNle hlogx hlogx0 (by positivity)
      _ ≤ ε * Real.log n := hP3'
  have hxpow : ((xceil Q : ℝ)) ^ (Nstar Q) ≤ (n : ℝ) ^ ε := by
    calc ((xceil Q : ℝ)) ^ (Nstar Q)
        = Real.exp ((Nstar Q : ℝ) * Real.log (xceil Q : ℝ)) := by
          rw [← Real.log_pow, Real.exp_log (pow_pos hx0R _)]
      _ ≤ Real.exp (ε * Real.log n) := Real.exp_le_exp.mpr hfin
      _ = (n : ℝ) ^ ε := by rw [Real.rpow_def_of_pos hn0, mul_comm]
  have hfinal : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (n : ℝ) ^ (1 + ε) := by
    calc ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (n : ℝ) * (xceil Q : ℝ) ^ (Nstar Q) := hub
      _ ≤ (n : ℝ) * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_left hxpow hn0.le
      _ = (n : ℝ) ^ (1 + ε) := by rw [Real.rpow_add hn0, Real.rpow_one]
  exact ⟨hSprime, hcard3, hcar, hfinal⟩

end Carmichael
