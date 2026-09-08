/-
E-generic version of Lemma 4.2 of the paper (Step 3 halts), proved from an
explicit AGP pigeonhole hypothesis (Theorem 3.1 at B = 21/100) together with the
Mertens-type bound `primeRecipSum_sub_le` (proved in `Carmichael/RecipSum.lean`),
which controls the reciprocal sum of the reservoir primes `q ∈ (z^{99/100}, z]`.

This is a transliteration of `Carmichael/Step3.lean` with `goodPrimes` replaced
by `goodPrimesE _ _ E`: the smoothness component of `goodPrimesE` membership is
never used in the analysis, so the proof goes through unchanged.
-/
import Carmichael.Defs
import Carmichael.RecipSum

namespace Carmichael

open Filter Finset

/-! ### Growth of the scales (as in `Step2.lean`) -/

private lemma tendsto_ell2 : Tendsto ell2 atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma tendsto_ell3 : Tendsto ell3 atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_ell2

private lemma tendsto_zreal (C₁ : ℝ) (h1000 : (1000 : ℝ) ≤ C₁) :
    Tendsto (fun n : ℕ => C₁ * ell2 n * ell3 n) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ tendsto_ell3
  filter_upwards [tendsto_ell2.eventually_ge_atTop 1,
    tendsto_ell3.eventually_ge_atTop 0] with n h2 h3
  have hC : (0 : ℝ) < C₁ := by linarith
  have hCℓ₂ : C₁ * 1 ≤ C₁ * ell2 n := mul_le_mul_of_nonneg_left h2 hC.le
  have h1 : (1 : ℝ) ≤ C₁ * ell2 n := by linarith
  have := mul_le_mul_of_nonneg_right h1 h3
  linarith

private lemma tendsto_zcast (C₁ : ℝ) (h1000 : (1000 : ℝ) ≤ C₁) :
    Tendsto (fun n : ℕ => (zscale C₁ n : ℝ)) atTop atTop :=
  tendsto_atTop_mono (fun _ => Nat.le_ceil _) (tendsto_zreal C₁ h1000)

private lemma tendsto_zrpow (C₁ : ℝ) (h1000 : (1000 : ℝ) ≤ C₁) :
    Tendsto (fun n : ℕ => (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 99 / 100)).comp (tendsto_zcast C₁ h1000)

/-! ### Elementary helpers -/

/-- A product of distinct primes is squarefree. (As in `Output.lean`.) -/
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

/-- Exponentials beat quadratics, with an arbitrary constant. -/
private lemma eventually_quad_le_exp (K : ℝ) :
    ∀ᶠ u : ℝ in atTop, K * u ^ 2 ≤ Real.exp (0.8 * u) := by
  have hcomp : Tendsto (fun u : ℝ => 0.8 * u) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) tendsto_id
  filter_upwards [hcomp.eventually
      ((Real.tendsto_exp_div_pow_atTop 2).eventually_ge_atTop (2 * |K| + 1)),
    eventually_gt_atTop (0 : ℝ)] with u hu hu0
  have h2 : (0 : ℝ) < (0.8 * u) ^ 2 := by positivity
  rw [le_div_iff₀ h2] at hu
  nlinarith [hu, sq_nonneg u, abs_nonneg K, le_abs_self K,
    mul_nonneg (sub_nonneg.mpr (le_abs_self K)) (sq_nonneg u),
    mul_nonneg (abs_nonneg K) (sq_nonneg u)]

/-! ### The main lemma -/

set_option maxHeartbeats 4000000 in
/-- Lemma 4.2 (Step 3 halts), E-generic version: for `n` large and any
admissible `Q ⊆ goodPrimesE C₁ n E`, some shift `k ≤ x^{79/100}` coprime to `L`
yields a pool of at least `(log n)^{1.2}` primes `dk + 1 ∈ (z, x]` with
`d ∣ L`. -/
theorem step3_haltsE (C₁ D E : ℝ) (z₃ : ℕ)
    (hE : 0 < E) (hE2 : E ≤ 1 / 2) (h1000 : (1000 : ℝ) ≤ C₁)
    (hpigeon : ∀ x L : ℕ, z₃ < x → 1 < L → Squarefree L →
      (∀ q : ℕ, q.Prime → q ∣ L → (q : ℝ) ≤ (x : ℝ) ^ ((79 : ℝ) / 200)) →
      (∑ q ∈ L.primeFactors, (1 : ℝ) / q) ≤ 3 / 160 →
      ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ (x : ℝ) ^ ((79 : ℝ) / 100) ∧ k.Coprime L ∧
        (2 : ℝ) ^ (-D - 2) / Real.log x *
          ((L.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (x : ℝ) ^ ((21 : ℝ) / 100))).card : ℝ)
        ≤ ((L.divisors.filter (fun d => d * k + 1 ≤ x ∧ (d * k + 1).Prime)).card : ℝ)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ Q ⊆ goodPrimesE C₁ n E, Q.card = Tscale n →
      ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ (xceil Q : ℝ) ^ ((79 : ℝ) / 100) ∧
        k.Coprime (Lmod Q) ∧
        (Real.log n) ^ (1.2 : ℝ) ≤ ((pool Q (zscale C₁ n) k).card : ℝ) := by
  classical
  have hC : (1000 : ℝ) ≤ C₁ := h1000
  have hc₀pos : (0 : ℝ) < (2 : ℝ) ^ (-D - 2) := Real.rpow_pos_of_pos (by norm_num) _
  filter_upwards [eventually_ge_atTop 3,
    tendsto_ell2.eventually_ge_atTop 50,
    tendsto_ell2.eventually_ge_atTop (z₃ : ℝ),
    tendsto_ell3.eventually_ge_atTop 139,
    tendsto_ell3.eventually_ge_atTop (Real.log (2 * C₁)),
    tendsto_ell3.eventually_ge_atTop 11000,
    (tendsto_zrpow C₁ h1000).eventually_ge_atTop 3,
    tendsto_ell2.eventually (eventually_quad_le_exp (120 / (2 : ℝ) ^ (-D - 2))),
    tendsto_ell2.eventually (eventually_quad_le_exp (3 * C₁))]
    with n hn3 ha50 haz₃ hb139 hbC hb11000 hmw3 hquadD hquadC
  intro Q hQsub hQcard
  set a := ell2 n with hadef
  set b := ell3 n with hbdef
  have hba : b = Real.log a := rfl
  have haeq : a = Real.log (Real.log (n : ℝ)) := rfl
  have hzdef : zscale C₁ n = ⌈C₁ * a * b⌉₊ := rfl
  have hTdef : Tscale n = ⌈(3 : ℝ) * a⌉₊ := rfl
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hb_le_a : b ≤ a := by
    have := Real.log_le_sub_one_of_pos ha0
    rw [hba]
    linarith
  -- z bounds
  have hzlbR : C₁ * a * b ≤ (zscale C₁ n : ℝ) := by
    rw [hzdef]; exact Nat.le_ceil _
  have hCa : (1000 : ℝ) * 50 ≤ C₁ * a := mul_le_mul hC ha50 (by norm_num) (by linarith)
  have hCab : (1000 : ℝ) * 50 * 139 ≤ C₁ * a * b :=
    mul_le_mul hCa hb139 (by norm_num) (le_trans (by norm_num) hCa)
  have hzposR : (0 : ℝ) < (zscale C₁ n : ℝ) := by linarith
  have hz1R : (1 : ℝ) < (zscale C₁ n : ℝ) := by linarith
  have hzubR : (zscale C₁ n : ℝ) ≤ 2 * (C₁ * a * b) := by
    rw [hzdef]
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ C₁ * a * b by linarith)
    linarith
  -- log z bounds
  have hCb : (1000 : ℝ) * 139 ≤ C₁ * b := mul_le_mul hC hb139 (by norm_num) (by linarith)
  have ha_le_Cab : a ≤ C₁ * a * b := by nlinarith [mul_le_mul_of_nonneg_left hCb ha0.le]
  have hlogz_lb : b ≤ Real.log (zscale C₁ n : ℝ) := by
    rw [hba]
    exact Real.log_le_log ha0 (le_trans ha_le_Cab hzlbR)
  have hlogz_pos : (0 : ℝ) < Real.log (zscale C₁ n : ℝ) := by linarith
  have hlogb_le : Real.log b ≤ b := by
    have := Real.log_le_sub_one_of_pos hb0
    linarith
  have h2C₁pos : (0 : ℝ) < 2 * C₁ := by linarith
  have hlogz_ub : Real.log (zscale C₁ n : ℝ) ≤ 3 * b := by
    calc Real.log (zscale C₁ n : ℝ) ≤ Real.log (2 * C₁ * (a * b)) := by
          apply Real.log_le_log hzposR
          calc (zscale C₁ n : ℝ) ≤ 2 * (C₁ * a * b) := hzubR
            _ = 2 * C₁ * (a * b) := by ring
      _ = Real.log (2 * C₁) + (Real.log a + Real.log b) := by
          rw [Real.log_mul (ne_of_gt h2C₁pos) (ne_of_gt (mul_pos ha0 hb0)),
            Real.log_mul (ne_of_gt ha0) (ne_of_gt hb0)]
      _ ≤ b + (b + b) := by
          have h2 : Real.log a = b := hba.symm
          linarith [hbC]
      _ = 3 * b := by ring
  -- T bounds
  have hT_lb : 3 * a ≤ (Tscale n : ℝ) := by rw [hTdef]; exact Nat.le_ceil _
  have hT_ub : (Tscale n : ℝ) ≤ 4 * a := by
    rw [hTdef]
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3 * a by linarith)
    linarith
  have hT1 : 1 ≤ Tscale n := by
    have h : (1 : ℝ) ≤ (Tscale n : ℝ) := by linarith
    exact_mod_cast h
  -- facts about the primes of Q
  have hQfacts : ∀ q ∈ Q, q.Prime ∧ q ≤ zscale C₁ n ∧
      (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) < (q : ℝ) := by
    intro q hq
    have hmem := hQsub hq
    simp only [goodPrimesE, Finset.mem_filter, Finset.mem_range] at hmem
    exact ⟨hmem.2.1, Nat.lt_succ_iff.mp hmem.1, hmem.2.2.1⟩
  have hQprime : ∀ q ∈ Q, q.Prime := fun q hq => (hQfacts q hq).1
  -- L facts
  have hL2T : 2 ^ Tscale n ≤ Lmod Q := by
    rw [← hQcard]
    show 2 ^ Q.card ≤ ∏ q ∈ Q, q
    calc 2 ^ Q.card = ∏ _q ∈ Q, 2 := (Finset.prod_const 2).symm
      _ ≤ ∏ q ∈ Q, q := Finset.prod_le_prod' fun q hq => (hQprime q hq).two_le
  have hL1 : 1 < Lmod Q := by
    have h1 : 2 ^ 1 ≤ 2 ^ Tscale n := Nat.pow_le_pow_right (by norm_num) hT1
    omega
  have hLpos : 0 < Lmod Q := by omega
  have hsqL : Squarefree (Lmod Q) := prod_primes_squarefree Q hQprime
  have hPF : (Lmod Q).primeFactors = Q := Nat.primeFactors_prod hQprime
  have hLzT : Lmod Q ≤ zscale C₁ n ^ Tscale n := by
    rw [← hQcard]
    exact Finset.prod_le_pow_card Q (fun q => q) _ fun q hq => (hQfacts q hq).2.1
  have hL0R : (0 : ℝ) < (Lmod Q : ℝ) := by exact_mod_cast hLpos
  have hL1R : (1 : ℝ) ≤ (Lmod Q : ℝ) := by exact_mod_cast hLpos
  have hL2TR : (2 : ℝ) ^ Tscale n ≤ (Lmod Q : ℝ) := by exact_mod_cast hL2T
  -- x facts
  have hx2 : 2 ≤ xceil Q := by
    have h1 : Lmod Q ≤ xceil Q := Nat.le_self_pow (by norm_num) _
    omega
  have hxR : ((xceil Q : ℕ) : ℝ) = (Lmod Q : ℝ) ^ (5 : ℕ) := by
    show ((Lmod Q ^ 5 : ℕ) : ℝ) = (Lmod Q : ℝ) ^ (5 : ℕ)
    push_cast
    ring
  have hlogx_pos : (0 : ℝ) < Real.log (xceil Q : ℝ) := by
    apply Real.log_pos
    have h : (2 : ℝ) ≤ (xceil Q : ℝ) := by exact_mod_cast hx2
    linarith
  have hlogL_ub : Real.log (Lmod Q : ℝ) ≤ (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ) := by
    have h1 : Real.log (Lmod Q : ℝ) ≤ Real.log ((zscale C₁ n : ℝ) ^ Tscale n) := by
      apply Real.log_le_log hL0R
      exact_mod_cast hLzT
    rwa [Real.log_pow] at h1
  have hlogx_ub : Real.log (xceil Q : ℝ) ≤ 60 * (a * b) := by
    have hlogx_eq : Real.log (xceil Q : ℝ) = 5 * Real.log (Lmod Q : ℝ) := by
      rw [hxR, Real.log_pow]
      push_cast
      ring
    rw [hlogx_eq]
    have h1 : (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ) ≤ 4 * a * (3 * b) :=
      mul_le_mul hT_ub hlogz_ub hlogz_pos.le (by linarith)
    linarith [hlogL_ub]
  -- the Mertens window (z^{99/100}, z]
  set w := ⌊(zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100)⌋₊ with hwdef
  have hrw_pos : (0 : ℝ) < (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) :=
    Real.rpow_pos_of_pos hzposR _
  have hrw2 : (2 : ℝ) ≤ (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) := by
    linarith [hmw3]
  have hwleR : (w : ℝ) ≤ (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) := Nat.floor_le hrw_pos.le
  have hw2 : 2 ≤ w := Nat.le_floor (by exact_mod_cast hrw2)
  have hw_half : (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) / 2 ≤ (w : ℝ) := by
    have h1 := Nat.lt_floor_add_one ((zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100))
    linarith
  have hz99_le_z : (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) ≤ (zscale C₁ n : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hz1R.le
      (show (99 : ℝ) / 100 ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hwz : w ≤ zscale C₁ n := by
    have h : (w : ℝ) ≤ (zscale C₁ n : ℝ) := le_trans hwleR hz99_le_z
    exact_mod_cast h
  have hlogw_lb : 197 / 200 * Real.log (zscale C₁ n : ℝ) ≤ Real.log (w : ℝ) := by
    have h1 : Real.log ((zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) / 2) ≤ Real.log (w : ℝ) :=
      Real.log_le_log (div_pos hrw_pos two_pos) hw_half
    rw [Real.log_div (ne_of_gt hrw_pos) (by norm_num), Real.log_rpow hzposR] at h1
    have hlog2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
    linarith [hlogz_lb, hb139]
  have hlogw_pos : (0 : ℝ) < Real.log (w : ℝ) := by linarith [hlogw_lb, hlogz_pos]
  -- the reciprocal sum over Q is at most 3/160
  have hsum_Q : ∑ q ∈ Q, (1 : ℝ) / q ≤ 3 / 160 := by
    have hsub_ranges : (Finset.range (w + 1)).filter Nat.Prime ⊆
        (Finset.range (zscale C₁ n + 1)).filter Nat.Prime :=
      Finset.filter_subset_filter _ (Finset.range_subset_range.mpr (Nat.succ_le_succ hwz))
    have hQsub2 : Q ⊆ ((Finset.range (zscale C₁ n + 1)).filter Nat.Prime) \
        ((Finset.range (w + 1)).filter Nat.Prime) := by
      intro q hq
      obtain ⟨hqp, hqz, hq99⟩ := hQfacts q hq
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range]
      refine ⟨⟨by omega, hqp⟩, ?_⟩
      intro hmem
      rw [Finset.mem_filter, Finset.mem_range] at hmem
      have h1 : (q : ℝ) ≤ (w : ℝ) := by
        have h2 : q ≤ w := Nat.lt_succ_iff.mp hmem.1
        exact_mod_cast h2
      linarith [hwleR, hq99]
    have h1 : ∑ q ∈ Q, (1 : ℝ) / q ≤
        ∑ p ∈ ((Finset.range (zscale C₁ n + 1)).filter Nat.Prime) \
          ((Finset.range (w + 1)).filter Nat.Prime), (1 : ℝ) / p :=
      Finset.sum_le_sum_of_subset_of_nonneg hQsub2 (fun i _ _ => by positivity)
    have h2 : ∑ p ∈ ((Finset.range (zscale C₁ n + 1)).filter Nat.Prime) \
        ((Finset.range (w + 1)).filter Nat.Prime), (1 : ℝ) / p
        = primeRecipSum (zscale C₁ n) - primeRecipSum w := by
      simp only [primeRecipSum]
      exact Finset.sum_sdiff_eq_sub hsub_ranges
    rw [h2] at h1
    have h3 : primeRecipSum (zscale C₁ n) - primeRecipSum w ≤
        (Real.log (zscale C₁ n : ℝ) - Real.log (w : ℝ) + 2 * (Real.log 4 + 4)) /
          Real.log (w : ℝ) :=
      primeRecipSum_sub_le hw2 hwz
    have hlog4 : Real.log 4 < 1.39 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have h := Real.log_two_lt_d9
      push_cast
      linarith
    have hZ11000 : (11000 : ℝ) ≤ Real.log (zscale C₁ n : ℝ) :=
      le_trans hb11000 hlogz_lb
    have h4 : (Real.log (zscale C₁ n : ℝ) - Real.log (w : ℝ) + 2 * (Real.log 4 + 4)) /
        Real.log (w : ℝ) ≤ 3 / 160 := by
      rw [div_le_iff₀ hlogw_pos]
      linarith [hlogw_lb]
    linarith [h1, h3, h4]
  -- x exceeds the AGP threshold
  have hz₃x : z₃ < xceil Q := by
    have h1 : z₃ ≤ Tscale n := by
      have h : (z₃ : ℝ) ≤ (Tscale n : ℝ) := by linarith [haz₃, ha0, hT_lb]
      exact_mod_cast h
    have h2 : Tscale n < 2 ^ Tscale n := Nat.lt_two_pow_self
    have h3 : Lmod Q ≤ xceil Q := Nat.le_self_pow (by norm_num) _
    omega
  -- every prime factor of L is at most x^{3/10}
  have hxr310 : (xceil Q : ℝ) ^ ((3 : ℝ) / 10) = (Lmod Q : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [hxR, ← Real.rpow_natCast (Lmod Q : ℝ) 5, ← Real.rpow_mul hL0R.le]
    norm_num
  have h2Texp : ((2 : ℝ) ^ Tscale n) ^ ((3 : ℝ) / 2)
      = Real.exp (Real.log 2 * ((Tscale n : ℝ) * (3 / 2))) := by
    rw [← Real.rpow_natCast (2 : ℝ) (Tscale n), ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog2_lb : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hzle_pow : (zscale C₁ n : ℝ)
      ≤ Real.exp (Real.log 2 * ((Tscale n : ℝ) * (3 / 2))) := by
    rw [← Real.exp_log hzposR]
    apply Real.exp_le_exp.mpr
    have h6 : (0.6931471803 : ℝ) * (3 * a * (3 / 2))
        ≤ Real.log 2 * ((Tscale n : ℝ) * (3 / 2)) :=
      mul_le_mul hlog2_lb.le (by linarith [hT_lb]) (by linarith [ha0])
        (le_trans (by norm_num) hlog2_lb.le)
    linarith [hlogz_ub, hb_le_a, ha0, h6]
  have hqbound310 : ∀ q : ℕ, q.Prime → q ∣ Lmod Q →
      (q : ℝ) ≤ (xceil Q : ℝ) ^ ((3 : ℝ) / 10) := by
    intro q hqp hqd
    have hqQ : q ∈ Q := by
      rw [← hPF, Nat.mem_primeFactors]
      exact ⟨hqp, hqd, by omega⟩
    have hq_le_z : (q : ℝ) ≤ (zscale C₁ n : ℝ) := by
      exact_mod_cast (hQfacts q hqQ).2.1
    calc (q : ℝ) ≤ (zscale C₁ n : ℝ) := hq_le_z
      _ ≤ Real.exp (Real.log 2 * ((Tscale n : ℝ) * (3 / 2))) := hzle_pow
      _ = ((2 : ℝ) ^ Tscale n) ^ ((3 : ℝ) / 2) := h2Texp.symm
      _ ≤ (Lmod Q : ℝ) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) hL2TR (by norm_num)
      _ = (xceil Q : ℝ) ^ ((3 : ℝ) / 10) := hxr310.symm
  -- hence at most x^{79/200}, the prime-factor bound of Theorem 3.1 at B = 21/100
  have hx1R : (1 : ℝ) ≤ (xceil Q : ℝ) := by
    have h : (1 : ℕ) ≤ xceil Q := by omega
    exact_mod_cast h
  have hqbound : ∀ q : ℕ, q.Prime → q ∣ Lmod Q →
      (q : ℝ) ≤ (xceil Q : ℝ) ^ ((79 : ℝ) / 200) := by
    intro q hqp hqd
    calc (q : ℝ) ≤ (xceil Q : ℝ) ^ ((3 : ℝ) / 10) := hqbound310 q hqp hqd
      _ ≤ (xceil Q : ℝ) ^ ((79 : ℝ) / 200) :=
          Real.rpow_le_rpow_of_exponent_le hx1R (by norm_num)
  have hsumL : ∑ q ∈ (Lmod Q).primeFactors, (1 : ℝ) / q ≤ 3 / 160 := by
    rw [hPF]; exact hsum_Q
  -- apply AGP Theorem 3.1
  obtain ⟨k, hk0, hkx, hkL, hcount⟩ :=
    hpigeon (xceil Q) (Lmod Q) hz₃x hL1 hsqL hqbound hsumL
  refine ⟨k, hk0, hkx, hkL, ?_⟩
  -- all divisors of L are at most L ≤ L^{21/20} = x^{21/100}, so the pigeonhole
  -- filter keeps them all
  have hfilter_all : (Lmod Q).divisors.filter
      (fun d : ℕ => (d : ℝ) ≤ (xceil Q : ℝ) ^ ((21 : ℝ) / 100)) = (Lmod Q).divisors := by
    apply Finset.filter_true_of_mem
    intro c hc
    have hdL : c ≤ Lmod Q := Nat.divisor_le hc
    have hx21 : (xceil Q : ℝ) ^ ((21 : ℝ) / 100) = (Lmod Q : ℝ) ^ ((21 : ℝ) / 20) := by
      rw [hxR, ← Real.rpow_natCast (Lmod Q : ℝ) 5, ← Real.rpow_mul hL0R.le]
      norm_num
    have h1 : (c : ℝ) ≤ (Lmod Q : ℝ) := by exact_mod_cast hdL
    have h2 : (Lmod Q : ℝ) ≤ (Lmod Q : ℝ) ^ ((21 : ℝ) / 20) := by
      nth_rewrite 1 [← Real.rpow_one (Lmod Q : ℝ)]
      exact Real.rpow_le_rpow_of_exponent_le hL1R (by norm_num)
    rw [hx21]
    linarith
  -- L has exactly 2^T divisors
  have hdivcard : (Lmod Q).divisors.card = 2 ^ Tscale n := by
    have h1 : ∀ p ∈ (Lmod Q).primeFactors, (Lmod Q).factorization p + 1 = 2 := by
      intro p hp
      have h2 : (Lmod Q).factorization p ≤ 1 := hsqL.natFactorization_le_one p
      have h3 : (Lmod Q).factorization p ≠ 0 := by
        rw [← Finsupp.mem_support_iff, Nat.support_factorization]
        exact hp
      omega
    calc (Lmod Q).divisors.card
        = (Lmod Q).primeFactors.prod (fun p => (Lmod Q).factorization p + 1) :=
          Nat.card_divisors (by omega)
      _ = (Lmod Q).primeFactors.prod (fun _ => 2) := Finset.prod_congr rfl h1
      _ = 2 ^ (Lmod Q).primeFactors.card := Finset.prod_const 2
      _ = 2 ^ Tscale n := by rw [hPF, hQcard]
  rw [hfilter_all, hdivcard] at hcount
  -- the pool is the image of the pigeonhole set with the small terms removed
  have hinj : Function.Injective (fun d : ℕ => d * k + 1) := by
    intro d₁ d₂ h
    simp only at h
    exact Nat.eq_of_mul_eq_mul_right hk0 (Nat.add_right_cancel h)
  have hpool_card : (pool Q (zscale C₁ n) k).card
      = ((Lmod Q).divisors.filter (fun d => d * k + 1 ≤ xceil Q ∧ (d * k + 1).Prime ∧
          zscale C₁ n < d * k + 1)).card := by
    simp only [pool]
    exact Finset.card_image_of_injective _ hinj
  have hS₁subS₀ : ((Lmod Q).divisors.filter (fun d => d * k + 1 ≤ xceil Q ∧
      (d * k + 1).Prime ∧ zscale C₁ n < d * k + 1)) ⊆
      ((Lmod Q).divisors.filter (fun d => d * k + 1 ≤ xceil Q ∧ (d * k + 1).Prime)) := by
    intro d hd
    rw [Finset.mem_filter] at hd ⊢
    exact ⟨hd.1, hd.2.1, hd.2.2.1⟩
  have hsdiff_sub : ((Lmod Q).divisors.filter (fun d => d * k + 1 ≤ xceil Q ∧
      (d * k + 1).Prime)) \
      ((Lmod Q).divisors.filter (fun d => d * k + 1 ≤ xceil Q ∧
      (d * k + 1).Prime ∧ zscale C₁ n < d * k + 1)) ⊆
      Finset.range (zscale C₁ n + 1) := by
    intro d hd
    rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_filter] at hd
    obtain ⟨⟨hdd, hdx, hdp⟩, hnot⟩ := hd
    have h1 : ¬ (zscale C₁ n < d * k + 1) := fun hzlt => hnot ⟨hdd, hdx, hdp, hzlt⟩
    have h2 : d * k + 1 ≤ zscale C₁ n := Nat.not_lt.mp h1
    have h3 : d ≤ d * k := Nat.le_mul_of_pos_right d hk0
    rw [Finset.mem_range]
    omega
  have hcard_split : ((Lmod Q).divisors.filter (fun d => d * k + 1 ≤ xceil Q ∧
      (d * k + 1).Prime)).card ≤
      ((Lmod Q).divisors.filter (fun d => d * k + 1 ≤ xceil Q ∧
      (d * k + 1).Prime ∧ zscale C₁ n < d * k + 1)).card + (zscale C₁ n + 1) := by
    have h1 := Finset.card_le_card hsdiff_sub
    rw [Finset.card_range] at h1
    have h2 := Finset.card_sdiff_add_card_eq_card hS₁subS₀
    omega
  -- final asymptotics
  have hn1R : (1 : ℝ) < (n : ℝ) := by
    have h : (1 : ℕ) < n := by omega
    exact_mod_cast h
  have hlogn_pos : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos hn1R
  have hgoal_exp : (Real.log (n : ℝ)) ^ (1.2 : ℝ) = Real.exp (1.2 * a) := by
    rw [Real.rpow_def_of_pos hlogn_pos, ← haeq, mul_comm]
  have h2T_ge : Real.exp (2.07 * a) ≤ (2 : ℝ) ^ Tscale n := by
    have h1 : (2 : ℝ) ^ Tscale n = Real.exp (Real.log 2 * (Tscale n : ℝ)) := by
      rw [← Real.rpow_natCast (2 : ℝ) (Tscale n), Real.rpow_def_of_pos (by norm_num)]
    rw [h1]
    apply Real.exp_le_exp.mpr
    have h6 : (0.6931471803 : ℝ) * (3 * a) ≤ Real.log 2 * (Tscale n : ℝ) :=
      mul_le_mul hlog2_lb.le hT_lb (by linarith [ha0]) (le_trans (by norm_num) hlog2_lb.le)
    linarith [ha0]
  have hab_pos : (0 : ℝ) < a * b := mul_pos ha0 hb0
  have hquad87 : 120 / (2 : ℝ) ^ (-D - 2) * (a * b) ≤ Real.exp (0.87 * a) := by
    have hK0 : (0 : ℝ) ≤ 120 / (2 : ℝ) ^ (-D - 2) := by positivity
    have h1 : 120 / (2 : ℝ) ^ (-D - 2) * (a * b)
        ≤ 120 / (2 : ℝ) ^ (-D - 2) * a ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hK0
      nlinarith [hb_le_a, ha0]
    calc 120 / (2 : ℝ) ^ (-D - 2) * (a * b)
        ≤ 120 / (2 : ℝ) ^ (-D - 2) * a ^ 2 := h1
      _ ≤ Real.exp (0.8 * a) := hquadD
      _ ≤ Real.exp (0.87 * a) := Real.exp_le_exp.mpr (by linarith [ha0])
  have hzp1_exp : (zscale C₁ n : ℝ) + 1 ≤ Real.exp (1.2 * a) := by
    have hC₁a_pos : (0 : ℝ) < C₁ * a := mul_pos (by linarith) ha0
    have h1a : C₁ * a * b ≤ C₁ * a * a :=
      mul_le_mul_of_nonneg_left hb_le_a hC₁a_pos.le
    have h1b : (1 : ℝ) ≤ C₁ * a * a := by nlinarith [hC, ha50]
    have h1 : (zscale C₁ n : ℝ) + 1 ≤ 3 * C₁ * a ^ 2 := by
      nlinarith [hzubR, h1a, h1b]
    calc (zscale C₁ n : ℝ) + 1 ≤ 3 * C₁ * a ^ 2 := h1
      _ ≤ Real.exp (0.8 * a) := hquadC
      _ ≤ Real.exp (1.2 * a) := Real.exp_le_exp.mpr (by linarith [ha0])
  have hc₀logx_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-D - 2) / Real.log (xceil Q : ℝ) :=
    div_nonneg hc₀pos.le hlogx_pos.le
  have hmain : Real.exp (1.2 * a) + ((zscale C₁ n : ℝ) + 1)
      ≤ (2 : ℝ) ^ (-D - 2) / Real.log (xceil Q : ℝ) * ((2 : ℝ) ^ Tscale n) := by
    have h60ab_pos : (0 : ℝ) < 60 * (a * b) := by linarith [hab_pos]
    have h1 : (2 : ℝ) ^ (-D - 2) / (60 * (a * b))
        ≤ (2 : ℝ) ^ (-D - 2) / Real.log (xceil Q : ℝ) :=
      div_le_div_of_nonneg_left hc₀pos.le hlogx_pos hlogx_ub
    have h2 : (2 : ℝ) ^ (-D - 2) / (60 * (a * b)) * Real.exp (2.07 * a)
        ≤ (2 : ℝ) ^ (-D - 2) / Real.log (xceil Q : ℝ) * ((2 : ℝ) ^ Tscale n) :=
      mul_le_mul h1 h2T_ge (Real.exp_nonneg _) hc₀logx_nonneg
    have h4 : Real.exp (2.07 * a) = Real.exp (0.87 * a) * Real.exp (1.2 * a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h5 : (2 : ℝ) ≤ (2 : ℝ) ^ (-D - 2) / (60 * (a * b)) * Real.exp (0.87 * a) := by
      have hc₀ne : (2 : ℝ) ^ (-D - 2) ≠ 0 := ne_of_gt hc₀pos
      have habne : a * b ≠ 0 := ne_of_gt hab_pos
      have h6 : (2 : ℝ) ^ (-D - 2) / (60 * (a * b))
          * (120 / (2 : ℝ) ^ (-D - 2) * (a * b)) = 2 := by
        field_simp
        norm_num
      have h8 : (2 : ℝ) ^ (-D - 2) / (60 * (a * b))
          * (120 / (2 : ℝ) ^ (-D - 2) * (a * b))
          ≤ (2 : ℝ) ^ (-D - 2) / (60 * (a * b)) * Real.exp (0.87 * a) :=
        mul_le_mul_of_nonneg_left hquad87 (div_nonneg hc₀pos.le h60ab_pos.le)
      linarith [h6, h8]
    have h7 : 2 * Real.exp (1.2 * a)
        ≤ (2 : ℝ) ^ (-D - 2) / (60 * (a * b)) * Real.exp (2.07 * a) := by
      rw [h4, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right h5 (Real.exp_nonneg _)
    linarith [hzp1_exp, h2, h7]
  -- conclude
  rw [hgoal_exp, hpool_card]
  have hcastT : ((2 ^ Tscale n : ℕ) : ℝ) = (2 : ℝ) ^ Tscale n := by push_cast; ring
  rw [hcastT] at hcount
  have hcast_split : (((Lmod Q).divisors.filter (fun d => d * k + 1 ≤ xceil Q ∧
      (d * k + 1).Prime)).card : ℝ) ≤
      (((Lmod Q).divisors.filter (fun d => d * k + 1 ≤ xceil Q ∧
      (d * k + 1).Prime ∧ zscale C₁ n < d * k + 1)).card : ℝ)
      + ((zscale C₁ n : ℝ) + 1) := by
    exact_mod_cast hcard_split
  linarith [hcount, hmain, hcast_split]

end Carmichael
