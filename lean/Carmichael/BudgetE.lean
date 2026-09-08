/-
Lemma 4.5 of the paper (running time), in operation-count form, for a
generic smoothness parameter `E` (so `y = z^{1-E}`).
-/
import Carmichael.Defs
import Carmichael.LogPow

namespace Carmichael

open Filter Finset

/-- The operation-count budget of the algorithm of Section 3, run with a
generic smoothness parameter `E` (step 1 takes `y = z^{1-E}`): an explicit
upper bound for the number of primitive operations, one summand per step.

Primitive operations are unit-cost arithmetic/dictionary operations on
integers of `O(log x) = O(ℓ₂ℓ₃)` bits (steps 2-4) or `O(log n)` bits
(step 5). Every primality test of a candidate `≤ x` is charged trial
division: at most `√x + 1 ≤ 2 · z^{5T/2}` unit operations, since
`x = L^5 ≤ z^{5T}`. AKS [AKS] is no longer used: the class `exp(O(ℓ₂ℓ₃))`
absorbs `√x`, so trial division suffices (matching the remark added to
the paper). Converting operations on such integers to bit operations
costs a further factor polynomial in `ℓ₂ℓ₃` (resp. `log n`), which the
bound `exp(O(ℓ₂ℓ₃))` (resp. the paper's `(log n)^{2+o(1)}` for step 5)
absorbs; the class `exp(O(ℓ₂ℓ₃))` is closed under polynomial overhead,
so the statement is machine-model independent.

Summands, using `L ≤ z^T` and `x = L^5 ≤ z^{5T}`:
* step 2: sieve and trial division up to `z`;
* step 3: at most `x^{79/100} ≤ z^{79T/20}` shifts (the shift range of AGP
  Theorem 3.1 at `B = 21/100`) × `2^T` divisors, at trial division cost
  `2 · z^{5T/2} ≥ √x + 1` per candidate;
* step 4: at most `log n` rounds, each at most `L · N*` dictionary
  operations, with `N* ≤ exp(z^{1-E} log z)(1 + T log z) + 2`;
* step 5a: certificate primality checks: at most `log n` factors, each
  by trial division;
* step 5b: assembling and verifying the product, `(log n)³`.
-/
noncomputable def opBudgetE (C₁ E : ℝ) (n : ℕ) : ℝ :=
  let z : ℝ := (zscale C₁ n : ℝ)
  let T : ℝ := (Tscale n : ℝ)
  z ^ (2 : ℝ)
    + z ^ (79 * T / 20) * (2 : ℝ) ^ T * (2 * z ^ (5 * T / 2))
    + Real.log n * z ^ T *
        (Real.exp (z ^ ((1 : ℝ) - E) * Real.log z) * (1 + T * Real.log z) + 2) *
        (T * Real.log z)
    + Real.log n * (2 * z ^ (5 * T / 2))
    + (Real.log n) ^ (3 : ℝ)

/-- `ℓ₂(n) → ∞`. -/
private lemma tendsto_ell2_atTop : Tendsto ell2 atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- `ℓ₃(n) → ∞`. -/
private lemma tendsto_ell3_atTop : Tendsto ell3 atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_ell2_atTop

set_option maxHeartbeats 1000000 in
/-- The pure real-number heart of the `E`-generic Lemma 4.5: with `ℓ₂, ℓ₃`
large enough (relative to the constant `c = C₁` and the parameter `E`),
`z` in the window `[c ℓ₂ ℓ₃, 2 c ℓ₂ ℓ₃]` and `T` in `[3 ℓ₂, 4 ℓ₂]`, the
budget expression is at most `exp(100 ℓ₂ ℓ₃)`. The `E`-specific inputs are
`h32 : ℓ₃² ≤ ℓ₂^{E/2}` and `h6c : 6c ≤ ℓ₂^{E/2}`, which drive the key
sub-polynomial estimate `z^{1-E} log z ≤ ℓ₂ ℓ₃`. -/
private lemma budgetE_bound
    {c E ℓ2 ℓ3 lgn z T : ℝ}
    (hc : 1000 ≤ c)
    (hE : 0 < E)
    (hE2 : E ≤ 1 / 2)
    (h2 : 1 ≤ ℓ2)
    (h3 : 3 ≤ ℓ3)
    (hlgn_pos : 0 < lgn)
    (h_eq2 : ℓ2 = Real.log lgn)
    (h_eq3 : ℓ3 = Real.log ℓ2)
    (hlogc : Real.log (2 * c) ≤ ℓ3)
    (h32 : ℓ3 ^ 2 ≤ ℓ2 ^ (E / 2))
    (h6c : 6 * c ≤ ℓ2 ^ (E / 2))
    (hz_lb : c * ℓ2 * ℓ3 ≤ z)
    (hz_ub : z ≤ 2 * (c * ℓ2 * ℓ3))
    (hT_lb : 3 * ℓ2 ≤ T)
    (hT_ub : T ≤ 4 * ℓ2) :
    z ^ (2 : ℝ) + z ^ (79 * T / 20) * (2 : ℝ) ^ T * (2 * z ^ (5 * T / 2))
      + lgn * z ^ T *
          (Real.exp (z ^ ((1 : ℝ) - E) * Real.log z) * (1 + T * Real.log z) + 2) *
          (T * Real.log z)
      + lgn * (2 * z ^ (5 * T / 2))
      + lgn ^ (3 : ℝ)
    ≤ Real.exp (100 * ℓ2 * ℓ3) := by
  -- Basic positivity facts.
  have h2pos : (0 : ℝ) < ℓ2 := by linarith only [h2]
  have h3pos : (0 : ℝ) < ℓ3 := by linarith only [h3]
  have hcpos : (0 : ℝ) < c := by linarith only [hc]
  have hM3 : (3 : ℝ) ≤ ℓ2 * ℓ3 := by
    have h := mul_le_mul h2 h3 (by norm_num : (0 : ℝ) ≤ 3) h2pos.le
    linarith only [h]
  have hMpos : (0 : ℝ) < ℓ2 * ℓ3 := by linarith only [hM3]
  have hstar : (0 : ℝ) ≤ ℓ2 * ℓ3 - ℓ3 := by
    have h := mul_nonneg (show (0 : ℝ) ≤ ℓ2 - 1 by linarith only [h2]) h3pos.le
    linarith only [h]
  have hstar2 : (0 : ℝ) ≤ ℓ2 * ℓ3 - ℓ2 := by
    have h := mul_nonneg h2pos.le (show (0 : ℝ) ≤ ℓ3 - 1 by linarith only [h3])
    linarith only [h]
  have htriple : (3000 : ℝ) ≤ c * ℓ2 * ℓ3 := by
    have i1 : (1000 : ℝ) * 1 ≤ c * ℓ2 :=
      mul_le_mul hc h2 zero_le_one (by linarith only [hc])
    have i2 : (1000 : ℝ) * 1 * 3 ≤ c * ℓ2 * ℓ3 :=
      mul_le_mul i1 h3 (by norm_num)
        (mul_nonneg (by linarith only [hc]) (by linarith only [h2]))
    linarith only [i2]
  have hz1 : (1 : ℝ) ≤ z := by linarith only [htriple, hz_lb]
  have hzpos : (0 : ℝ) < z := by linarith only [hz1]
  have hlz_nonneg : (0 : ℝ) ≤ Real.log z := Real.log_nonneg hz1
  have hT1 : (1 : ℝ) ≤ T := by linarith only [hT_lb, h2]
  have hT_nonneg : (0 : ℝ) ≤ T := by linarith only [hT1]
  -- `log z ≤ 3 ℓ₃`.
  have hzc : z ≤ 2 * c * (ℓ2 * ℓ3) := by linarith only [hz_ub]
  have hlz : Real.log z ≤ 3 * ℓ3 := by
    have e1 : Real.log z ≤ Real.log (2 * c * (ℓ2 * ℓ3)) := Real.log_le_log hzpos hzc
    have e2 : Real.log (2 * c * (ℓ2 * ℓ3))
        = Real.log (2 * c) + (Real.log ℓ2 + Real.log ℓ3) := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (ne_of_gt h2pos) (ne_of_gt h3pos)]
    have e3 : Real.log ℓ3 ≤ ℓ3 := by
      have h := Real.log_le_sub_one_of_pos h3pos; linarith only [h]
    have e4 : Real.log ℓ2 ≤ ℓ3 := le_of_eq h_eq3.symm
    linarith only [e1, e2.le, e3, e4, hlogc]
  have hTlz : T * Real.log z ≤ 12 * (ℓ2 * ℓ3) := by
    have h := mul_le_mul hT_ub hlz hlz_nonneg (by linarith only [h2] : (0 : ℝ) ≤ 4 * ℓ2)
    linarith only [h]
  -- Summand 1: `z² ≤ exp(6 ℓ₂ ℓ₃)`.
  have term1 : z ^ (2 : ℝ) ≤ Real.exp (6 * (ℓ2 * ℓ3)) := by
    rw [Real.rpow_def_of_pos hzpos]
    apply Real.exp_le_exp.mpr
    linarith only [hlz, hstar]
  -- Summand 2: `z^{79T/20} 2^T (2 z^{5T/2}) ≤ exp(83 ℓ₂ ℓ₃)`.
  have t2a : z ^ (79 * T / 20) ≤ Real.exp (48 * (ℓ2 * ℓ3)) := by
    rw [Real.rpow_def_of_pos hzpos]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul hlz (show 79 * T / 20 ≤ 16 * ℓ2 by linarith only [hT_ub, h2pos])
      (by linarith only [hT1] : (0 : ℝ) ≤ 79 * T / 20)
      (by linarith only [h3] : (0 : ℝ) ≤ 3 * ℓ3)
    linarith only [h]
  have t2b : (2 : ℝ) ^ T ≤ Real.exp (4 * (ℓ2 * ℓ3)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith only [h]
    have h := mul_le_mul hlog2 hT_ub hT_nonneg zero_le_one
    linarith only [h, hstar2]
  have h2E : (2 : ℝ) ≤ Real.exp (ℓ2 * ℓ3) := by
    linarith only [Real.add_one_le_exp (ℓ2 * ℓ3), hM3]
  have hz52 : z ^ (5 * T / 2) ≤ Real.exp (30 * (ℓ2 * ℓ3)) := by
    rw [Real.rpow_def_of_pos hzpos]
    apply Real.exp_le_exp.mpr
    linarith only [hTlz]
  have t2c : 2 * z ^ (5 * T / 2) ≤ Real.exp (31 * (ℓ2 * ℓ3)) := by
    have h := mul_le_mul h2E hz52 (Real.rpow_nonneg hzpos.le _) (Real.exp_pos _).le
    refine h.trans (le_of_eq ?_)
    rw [← Real.exp_add]
    exact congrArg Real.exp (by ring)
  have t2c_nn : (0 : ℝ) ≤ 2 * z ^ (5 * T / 2) := by
    have h := Real.rpow_nonneg hzpos.le (5 * T / 2)
    linarith only [h]
  have term2 : z ^ (79 * T / 20) * (2 : ℝ) ^ T * (2 * z ^ (5 * T / 2))
      ≤ Real.exp (83 * (ℓ2 * ℓ3)) := by
    have step : z ^ (79 * T / 20) * (2 : ℝ) ^ T * (2 * z ^ (5 * T / 2))
        ≤ Real.exp (48 * (ℓ2 * ℓ3)) * Real.exp (4 * (ℓ2 * ℓ3))
            * Real.exp (31 * (ℓ2 * ℓ3)) :=
      mul_le_mul
        (mul_le_mul t2a t2b (Real.rpow_nonneg (by norm_num) _) (Real.exp_pos _).le)
        t2c t2c_nn (by positivity)
    refine step.trans (le_of_eq ?_)
    rw [← Real.exp_add, ← Real.exp_add]
    exact congrArg Real.exp (by ring)
  -- Summand 3: `log n · z^T · N* · (T log z) ≤ exp(40 ℓ₂ ℓ₃)`.
  have h_lgn : lgn ≤ Real.exp (ℓ2 * ℓ3) := by
    have e : lgn = Real.exp ℓ2 := by rw [h_eq2, Real.exp_log hlgn_pos]
    rw [e]
    apply Real.exp_le_exp.mpr
    linarith only [hstar2]
  have h_zT : z ^ T ≤ Real.exp (12 * (ℓ2 * ℓ3)) := by
    rw [Real.rpow_def_of_pos hzpos]
    apply Real.exp_le_exp.mpr
    linarith only [hTlz]
  -- The key sub-polynomial estimate: `z^{1-E} log z ≤ ℓ₂ ℓ₃`.
  have h2cnn : (0 : ℝ) ≤ 2 * c := by linarith only [hc]
  have h1mE_nn : (0 : ℝ) ≤ 1 - E := by linarith only [hE2]
  have h1mE_le1 : (1 : ℝ) - E ≤ 1 := by linarith only [hE]
  have hA_nn : (0 : ℝ) ≤ ℓ2 ^ ((1 : ℝ) - E) := (Real.rpow_pos_of_pos h2pos _).le
  have hP_nn : (0 : ℝ) ≤ ℓ2 ^ (E / 2) := (Real.rpow_pos_of_pos h2pos _).le
  have h3E_nn : (0 : ℝ) ≤ ℓ3 ^ ((1 : ℝ) - E) := (Real.rpow_pos_of_pos h3pos _).le
  have h_mid_exp : z ^ ((1 : ℝ) - E) * Real.log z ≤ ℓ2 * ℓ3 := by
    -- `z^{1-E} ≤ (2c)^{1-E} ℓ₂^{1-E} ℓ₃^{1-E}` from `z ≤ 2c ℓ₂ ℓ₃`.
    have hz1E : z ^ ((1 : ℝ) - E)
        ≤ (2 * c) ^ ((1 : ℝ) - E) * (ℓ2 ^ ((1 : ℝ) - E) * ℓ3 ^ ((1 : ℝ) - E)) := by
      calc z ^ ((1 : ℝ) - E) ≤ (2 * c * (ℓ2 * ℓ3)) ^ ((1 : ℝ) - E) :=
            Real.rpow_le_rpow hzpos.le hzc h1mE_nn
        _ = (2 * c) ^ ((1 : ℝ) - E) * (ℓ2 * ℓ3) ^ ((1 : ℝ) - E) :=
            Real.mul_rpow h2cnn hMpos.le
        _ = (2 * c) ^ ((1 : ℝ) - E) * (ℓ2 ^ ((1 : ℝ) - E) * ℓ3 ^ ((1 : ℝ) - E)) := by
            rw [Real.mul_rpow h2pos.le h3pos.le]
    -- `(2c)^{1-E} ≤ 2c` since `2c ≥ 1`, and `ℓ₃^{1-E} ≤ ℓ₃` since `ℓ₃ ≥ 1`.
    have h2cE : (2 * c) ^ ((1 : ℝ) - E) ≤ 2 * c := by
      calc (2 * c) ^ ((1 : ℝ) - E) ≤ (2 * c) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith only [hc]) h1mE_le1
        _ = 2 * c := Real.rpow_one _
    have h3E : ℓ3 ^ ((1 : ℝ) - E) ≤ ℓ3 := by
      calc ℓ3 ^ ((1 : ℝ) - E) ≤ ℓ3 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith only [h3]) h1mE_le1
        _ = ℓ3 := Real.rpow_one _
    -- Multiply by `log z ≤ 3 ℓ₃` and collect: bound by `6c · ℓ₂^{1-E} · ℓ₃²`.
    have s1 : z ^ ((1 : ℝ) - E) * Real.log z
        ≤ ((2 * c) ^ ((1 : ℝ) - E) * (ℓ2 ^ ((1 : ℝ) - E) * ℓ3 ^ ((1 : ℝ) - E)))
            * (3 * ℓ3) :=
      mul_le_mul hz1E hlz hlz_nonneg
        (mul_nonneg (Real.rpow_nonneg h2cnn _) (mul_nonneg hA_nn h3E_nn))
    have s2 : ((2 * c) ^ ((1 : ℝ) - E) * (ℓ2 ^ ((1 : ℝ) - E) * ℓ3 ^ ((1 : ℝ) - E)))
        * (3 * ℓ3)
        ≤ ((2 * c) * (ℓ2 ^ ((1 : ℝ) - E) * ℓ3)) * (3 * ℓ3) := by
      have inner : ℓ2 ^ ((1 : ℝ) - E) * ℓ3 ^ ((1 : ℝ) - E) ≤ ℓ2 ^ ((1 : ℝ) - E) * ℓ3 :=
        mul_le_mul_of_nonneg_left h3E hA_nn
      have outer : (2 * c) ^ ((1 : ℝ) - E) * (ℓ2 ^ ((1 : ℝ) - E) * ℓ3 ^ ((1 : ℝ) - E))
          ≤ (2 * c) * (ℓ2 ^ ((1 : ℝ) - E) * ℓ3) :=
        mul_le_mul h2cE inner (mul_nonneg hA_nn h3E_nn) h2cnn
      exact mul_le_mul_of_nonneg_right outer (by linarith only [h3])
    have s3 : ((2 * c) * (ℓ2 ^ ((1 : ℝ) - E) * ℓ3)) * (3 * ℓ3)
        = (6 * c) * (ℓ2 ^ ((1 : ℝ) - E) * ℓ3 ^ 2) := by ring
    -- `ℓ₃² ≤ ℓ₂^{E/2}` and `6c ≤ ℓ₂^{E/2}` (the eventual inputs) finish:
    -- `ℓ₂^{E/2} · ℓ₂^{1-E} · ℓ₂^{E/2} = ℓ₂ ≤ ℓ₂ ℓ₃`.
    have s4 : (6 * c) * (ℓ2 ^ ((1 : ℝ) - E) * ℓ3 ^ 2)
        ≤ ℓ2 ^ (E / 2) * (ℓ2 ^ ((1 : ℝ) - E) * ℓ2 ^ (E / 2)) := by
      have inner : ℓ2 ^ ((1 : ℝ) - E) * ℓ3 ^ 2 ≤ ℓ2 ^ ((1 : ℝ) - E) * ℓ2 ^ (E / 2) :=
        mul_le_mul_of_nonneg_left h32 hA_nn
      exact mul_le_mul h6c inner (mul_nonneg hA_nn (by positivity)) hP_nn
    have s5 : ℓ2 ^ (E / 2) * (ℓ2 ^ ((1 : ℝ) - E) * ℓ2 ^ (E / 2)) = ℓ2 := by
      rw [← Real.rpow_add h2pos, ← Real.rpow_add h2pos,
        show E / 2 + ((1 : ℝ) - E + E / 2) = (1 : ℝ) by ring, Real.rpow_one]
    have s6 : ℓ2 ≤ ℓ2 * ℓ3 :=
      le_mul_of_one_le_right h2pos.le (by linarith only [h3])
    linarith only [s1, s2, s3.le, s3.ge, s4, s5.le, s5.ge, s6]
  have hTlz_nn : (0 : ℝ) ≤ T * Real.log z := mul_nonneg hT_nonneg hlz_nonneg
  have h_mid : Real.exp (z ^ ((1 : ℝ) - E) * Real.log z) * (1 + T * Real.log z) + 2
      ≤ Real.exp (15 * (ℓ2 * ℓ3)) := by
    have f1 : Real.exp (z ^ ((1 : ℝ) - E) * Real.log z) ≤ Real.exp (ℓ2 * ℓ3) :=
      Real.exp_le_exp.mpr h_mid_exp
    have f2 : 1 + T * Real.log z ≤ Real.exp (13 * (ℓ2 * ℓ3)) := by
      have h13 : 1 + T * Real.log z ≤ 13 * (ℓ2 * ℓ3) := by linarith only [hTlz, hM3]
      linarith only [h13, Real.add_one_le_exp (13 * (ℓ2 * ℓ3))]
    have f3 : (0 : ℝ) ≤ 1 + T * Real.log z := by linarith only [hTlz_nn]
    have f4 : Real.exp (z ^ ((1 : ℝ) - E) * Real.log z) * (1 + T * Real.log z)
        ≤ Real.exp (ℓ2 * ℓ3) * Real.exp (13 * (ℓ2 * ℓ3)) :=
      mul_le_mul f1 f2 f3 (Real.exp_pos _).le
    have f5 : Real.exp (ℓ2 * ℓ3) * Real.exp (13 * (ℓ2 * ℓ3))
        = Real.exp (14 * (ℓ2 * ℓ3)) := by
      rw [← Real.exp_add]; exact congrArg Real.exp (by ring)
    have f6 : (2 : ℝ) ≤ Real.exp (ℓ2 * ℓ3) := by
      linarith only [Real.add_one_le_exp (ℓ2 * ℓ3), hM3]
    have hB2 : (2 : ℝ) ≤ Real.exp (14 * (ℓ2 * ℓ3)) := by
      linarith only [Real.add_one_le_exp (14 * (ℓ2 * ℓ3)), hM3]
    have f7 : Real.exp (14 * (ℓ2 * ℓ3)) + 2 ≤ Real.exp (15 * (ℓ2 * ℓ3)) := by
      have e : Real.exp (15 * (ℓ2 * ℓ3))
          = Real.exp (ℓ2 * ℓ3) * Real.exp (14 * (ℓ2 * ℓ3)) := by
        rw [← Real.exp_add]; exact congrArg Real.exp (by ring)
      have h5 : (0 : ℝ) ≤ (Real.exp (ℓ2 * ℓ3) - 2) * Real.exp (14 * (ℓ2 * ℓ3)) :=
        mul_nonneg (by linarith only [f6]) (Real.exp_pos _).le
      linarith only [e.le, e.ge, hB2, h5]
    linarith only [f4, f5.le, f5.ge, f7]
  have h_mid_nn : (0 : ℝ)
      ≤ Real.exp (z ^ ((1 : ℝ) - E) * Real.log z) * (1 + T * Real.log z) + 2 := by
    have h1 : (0 : ℝ) ≤ 1 + T * Real.log z := by linarith only [hTlz_nn]
    have h := mul_nonneg (Real.exp_pos (z ^ ((1 : ℝ) - E) * Real.log z)).le h1
    linarith only [h]
  have h_Tlz_exp : T * Real.log z ≤ Real.exp (12 * (ℓ2 * ℓ3)) := by
    linarith only [hTlz, Real.add_one_le_exp (12 * (ℓ2 * ℓ3))]
  have term3 : lgn * z ^ T *
      (Real.exp (z ^ ((1 : ℝ) - E) * Real.log z) * (1 + T * Real.log z) + 2) *
      (T * Real.log z) ≤ Real.exp (40 * (ℓ2 * ℓ3)) := by
    have n2 : (0 : ℝ) ≤ z ^ T := Real.rpow_nonneg hzpos.le _
    have s1 : lgn * z ^ T ≤ Real.exp (ℓ2 * ℓ3) * Real.exp (12 * (ℓ2 * ℓ3)) :=
      mul_le_mul h_lgn h_zT n2 (Real.exp_pos _).le
    have s2 : lgn * z ^ T *
        (Real.exp (z ^ ((1 : ℝ) - E) * Real.log z) * (1 + T * Real.log z) + 2)
        ≤ Real.exp (ℓ2 * ℓ3) * Real.exp (12 * (ℓ2 * ℓ3)) * Real.exp (15 * (ℓ2 * ℓ3)) :=
      mul_le_mul s1 h_mid h_mid_nn (by positivity)
    have s3 : lgn * z ^ T *
        (Real.exp (z ^ ((1 : ℝ) - E) * Real.log z) * (1 + T * Real.log z) + 2) *
        (T * Real.log z)
        ≤ Real.exp (ℓ2 * ℓ3) * Real.exp (12 * (ℓ2 * ℓ3)) * Real.exp (15 * (ℓ2 * ℓ3))
            * Real.exp (12 * (ℓ2 * ℓ3)) :=
      mul_le_mul s2 h_Tlz_exp hTlz_nn (by positivity)
    refine s3.trans (le_of_eq ?_)
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    exact congrArg Real.exp (by ring)
  -- Summand 4: `log n · (2 z^{5T/2}) ≤ exp(32 ℓ₂ ℓ₃)`.
  have term4 : lgn * (2 * z ^ (5 * T / 2)) ≤ Real.exp (32 * (ℓ2 * ℓ3)) := by
    have h := mul_le_mul h_lgn t2c t2c_nn (Real.exp_pos _).le
    refine h.trans (le_of_eq ?_)
    rw [← Real.exp_add]
    exact congrArg Real.exp (by ring)
  -- Summand 5: `(log n)³ ≤ exp(3 ℓ₂ ℓ₃)`.
  have term5 : lgn ^ (3 : ℝ) ≤ Real.exp (3 * (ℓ2 * ℓ3)) := by
    rw [Real.rpow_def_of_pos hlgn_pos]
    apply Real.exp_le_exp.mpr
    rw [← h_eq2]
    linarith only [hstar2]
  -- Combine the five summands.
  have mono : ∀ s t : ℝ, s ≤ t →
      Real.exp (s * (ℓ2 * ℓ3)) ≤ Real.exp (t * (ℓ2 * ℓ3)) := fun s t hst =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hst hMpos.le)
  have b1 : z ^ (2 : ℝ) ≤ Real.exp (98 * (ℓ2 * ℓ3)) :=
    term1.trans (mono 6 98 (by norm_num))
  have b2 : z ^ (79 * T / 20) * (2 : ℝ) ^ T * (2 * z ^ (5 * T / 2))
      ≤ Real.exp (98 * (ℓ2 * ℓ3)) := term2.trans (mono 83 98 (by norm_num))
  have b3 : lgn * z ^ T *
      (Real.exp (z ^ ((1 : ℝ) - E) * Real.log z) * (1 + T * Real.log z) + 2) *
      (T * Real.log z) ≤ Real.exp (98 * (ℓ2 * ℓ3)) :=
    term3.trans (mono 40 98 (by norm_num))
  have b4 : lgn * (2 * z ^ (5 * T / 2)) ≤ Real.exp (98 * (ℓ2 * ℓ3)) :=
    term4.trans (mono 32 98 (by norm_num))
  have b5 : lgn ^ (3 : ℝ) ≤ Real.exp (98 * (ℓ2 * ℓ3)) :=
    term5.trans (mono 3 98 (by norm_num))
  have h5E : (5 : ℝ) ≤ Real.exp (2 * (ℓ2 * ℓ3)) := by
    linarith only [Real.add_one_le_exp (2 * (ℓ2 * ℓ3)), hM3]
  have e : Real.exp (2 * (ℓ2 * ℓ3)) * Real.exp (98 * (ℓ2 * ℓ3))
      = Real.exp (100 * ℓ2 * ℓ3) := by
    rw [← Real.exp_add]; exact congrArg Real.exp (by ring)
  have h5 : (0 : ℝ) ≤ (Real.exp (2 * (ℓ2 * ℓ3)) - 5)
      * Real.exp (98 * (ℓ2 * ℓ3)) :=
    mul_nonneg (by linarith only [h5E]) (Real.exp_pos _).le
  linarith only [b1, b2, b3, b4, b5, h5, e.le, e.ge]

/-- The `E`-generic Lemma 4.5 (running time): for any `C₁ ≥ 1000` and any
smoothness parameter `E ∈ (0, 1/2]`, the operation count is
`exp(O(ℓ₂ ℓ₃))`. -/
theorem opBudgetE_le (C₁ E : ℝ) (hE : 0 < E) (hE2 : E ≤ 1 / 2)
    (h1000 : (1000 : ℝ) ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in Filter.atTop, opBudgetE C₁ E n ≤ Real.exp (C * ell2 n * ell3 n) := by
  refine ⟨100, by norm_num, ?_⟩
  have h2ev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ell2 n :=
    tendsto_ell2_atTop.eventually_ge_atTop 1
  have h3ev : ∀ᶠ n : ℕ in atTop, (3 : ℝ) ≤ ell3 n :=
    tendsto_ell3_atTop.eventually_ge_atTop 3
  have hlogcev : ∀ᶠ n : ℕ in atTop, Real.log (2 * C₁) ≤ ell3 n :=
    tendsto_ell3_atTop.eventually_ge_atTop _
  have h32ev : ∀ᶠ n : ℕ in atTop, (ell3 n) ^ 2 ≤ (ell2 n) ^ (E / 2) :=
    tendsto_ell2_atTop.eventually (eventually_log_sq_le_rpow (half_pos hE))
  have h6cev : ∀ᶠ n : ℕ in atTop, 6 * C₁ ≤ (ell2 n) ^ (E / 2) :=
    ((tendsto_rpow_atTop (half_pos hE)).comp
      tendsto_ell2_atTop).eventually_ge_atTop _
  have hlgnev : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < Real.log n :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0
  filter_upwards [h2ev, h3ev, hlogcev, h32ev, h6cev, hlgnev]
    with n h2 h3 hlogc h32 h6c hlgn
  -- Bounds on `z = ⌈C₁ ℓ₂ ℓ₃⌉₊` and `T = ⌈3 ℓ₂⌉₊` as reals.
  have hv1 : (1 : ℝ) ≤ C₁ * ell2 n * ell3 n := by
    have i1 : (1000 : ℝ) * 1 ≤ C₁ * ell2 n :=
      mul_le_mul h1000 h2 zero_le_one (by linarith only [h1000])
    have i2 : (1000 : ℝ) * 1 * 3 ≤ C₁ * ell2 n * ell3 n :=
      mul_le_mul i1 h3 (by norm_num)
        (mul_nonneg (by linarith only [h1000]) (by linarith only [h2]))
    linarith only [i2]
  have hz_lb : C₁ * ell2 n * ell3 n ≤ (zscale C₁ n : ℝ) := by
    unfold zscale; exact Nat.le_ceil _
  have hz_ub : (zscale C₁ n : ℝ) ≤ 2 * (C₁ * ell2 n * ell3 n) := by
    have h := Nat.ceil_lt_add_one
      (show (0 : ℝ) ≤ C₁ * ell2 n * ell3 n by linarith only [hv1])
    unfold zscale; linarith only [h, hv1]
  have hT_lb : 3 * ell2 n ≤ (Tscale n : ℝ) := by
    unfold Tscale; exact Nat.le_ceil _
  have hT_ub : (Tscale n : ℝ) ≤ 4 * ell2 n := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3 * ell2 n by linarith only [h2])
    unfold Tscale; linarith only [h, h2]
  exact budgetE_bound h1000 hE hE2 h2 h3 hlgn rfl rfl hlogc h32 h6c
    hz_lb hz_ub hT_lb hT_ub

end Carmichael
