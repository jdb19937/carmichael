/-
Route A, sortie A5: the operation budget `costPieces` of `Alg.search` is
`exp(O(ℓ₂ ℓ₃))` at every scale in the window, and `Alg.search` on its
success path with output and cost unfolded.

Exponent bookkeeping (`M := ℓ₂ ℓ₃`, eventually `ℓ₂ ≥ 1`, `ℓ₃ ≥ 12`, so
`12 ℓ₂ ≤ M`, `log z ≤ 3 ℓ₃`, `T log z ≤ 15 M`):
* atoms: `z ≤ exp(3M)`, `z^T ≤ exp(15M)`, `2^T ≤ exp(M/3)` (`log 2 ≤ 7/10`),
  `x = L^5 ≤ exp(75M)`, `√x ≤ exp(75M/2)`, `k ≤ x^{79/100} ≤ exp(237M/4)`,
  and every constant `≤ 8` is `≤ exp(M/4)`;
* step 2: `≤ 7 z² ≤ exp(25M/4)`;
* step 3: `≤ exp(237M/4) · exp(115M/3) = exp(1171M/12)`;
* step 4: `≤ exp(95M/6)`; step 5: `≤ exp(115M/3)`;
* total: `≤ 4 exp(1171M/12) ≤ exp(1174M/12) ≤ exp(100M)`.
-/
import Carmichael.Algorithm
import Carmichael.DefsW
import Carmichael.LogPow

set_option autoImplicit false

namespace Carmichael

open Filter

/-- `ℓ₂(n) → ∞`. -/
private lemma tendsto_ell2_atTop' : Tendsto ell2 atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- `ℓ₃(n) → ∞`. -/
private lemma tendsto_ell3_atTop' : Tendsto ell3 atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_ell2_atTop'

set_option maxHeartbeats 1000000 in
/-- The pure real-number heart of `costPieces_leW`: with `ℓ₂ ≥ 1`, `ℓ₃ ≥ 12`,
`log(4c) ≤ ℓ₃`, `z ∈ [c ℓ₂ ℓ₃, 4 c ℓ₂ ℓ₃]`, `T ∈ [3 ℓ₂, 5 ℓ₂]`, `y ≤ 4z`,
and the integer quantities of `costPieces` replaced by reals with the
bounds the wrapper supplies (`sz = √z ≤ z`, `lgz = log₂ z ≤ z`, `L ≤ z^T`,
`x = L^5`, `sx ≤ √x`, `k ≤ x^{79/100}`, `tw = 2^T`, `P, S ≤ tw`), the
budget expression is at most `exp(100 ℓ₂ ℓ₃)`. -/
private lemma costPieces_bound
    {c ℓ2 ℓ3 z y T L x k P S sz lgz sx tw : ℝ}
    (hc : 1000 ≤ c)
    (h2 : 1 ≤ ℓ2)
    (h3 : 12 ≤ ℓ3)
    (h_eq3 : ℓ3 = Real.log ℓ2)
    (hlogc : Real.log (4 * c) ≤ ℓ3)
    (hz_lb : c * ℓ2 * ℓ3 ≤ z)
    (hz_ub : z ≤ 4 * (c * ℓ2 * ℓ3))
    (hy : y ≤ 4 * z)
    (hT_lb : 3 * ℓ2 ≤ T)
    (hT_ub : T ≤ 5 * ℓ2)
    (hsz : sz ≤ z)
    (hlgz : lgz ≤ z)
    (hL0 : 0 ≤ L)
    (hL : L ≤ z ^ T)
    (hx : x = L ^ 5)
    (hsx0 : 0 ≤ sx)
    (hsx : sx ≤ Real.sqrt x)
    (hk0 : 0 ≤ k)
    (hk : k ≤ x ^ ((79 : ℝ) / 100))
    (htw : tw = (2 : ℝ) ^ T)
    (hP0 : 0 ≤ P)
    (hP : P ≤ tw)
    (hS0 : 0 ≤ S)
    (hS : S ≤ tw) :
    (z + 1) * (sz + y + lgz + 6) + 2 * T + 2 + k * (T + 2 + tw * (sx + 3))
      + P * (L + 3) + 1 + S * (sx + S + 6) + 4 ≤ Real.exp (100 * ℓ2 * ℓ3) := by
  -- Basic positivity facts.
  have h2pos : (0 : ℝ) < ℓ2 := by linarith only [h2]
  have h3pos : (0 : ℝ) < ℓ3 := by linarith only [h3]
  have hM : (12 : ℝ) ≤ ℓ2 * ℓ3 := by
    have h := mul_le_mul h2 h3 (by norm_num : (0 : ℝ) ≤ 12) h2pos.le
    linarith only [h]
  have hMpos : (0 : ℝ) < ℓ2 * ℓ3 := by linarith only [hM]
  have hstar : (0 : ℝ) ≤ ℓ2 * ℓ3 - ℓ3 := by
    have h := mul_nonneg (show (0 : ℝ) ≤ ℓ2 - 1 by linarith only [h2]) h3pos.le
    linarith only [h]
  have h12l2 : 12 * ℓ2 ≤ ℓ2 * ℓ3 := by
    have h := mul_le_mul_of_nonneg_left h3 h2pos.le
    linarith only [h]
  have hstar2 : ℓ2 ≤ ℓ2 * ℓ3 := by linarith only [h12l2, h2]
  have htriple : (12000 : ℝ) ≤ c * ℓ2 * ℓ3 := by
    have i1 : (1000 : ℝ) * 1 ≤ c * ℓ2 :=
      mul_le_mul hc h2 zero_le_one (by linarith only [hc])
    have i2 : (1000 : ℝ) * 1 * 12 ≤ c * ℓ2 * ℓ3 :=
      mul_le_mul i1 h3 (by norm_num)
        (mul_nonneg (by linarith only [hc]) (by linarith only [h2]))
    linarith only [i2]
  have hML : ℓ2 * ℓ3 ≤ z := by
    have h : (1 : ℝ) * (ℓ2 * ℓ3) ≤ c * (ℓ2 * ℓ3) :=
      mul_le_mul_of_nonneg_right (by linarith only [hc]) hMpos.le
    linarith only [h, hz_lb]
  have hl2z : ℓ2 ≤ z := by linarith only [hML, hstar2]
  have hz12000 : (12000 : ℝ) ≤ z := by linarith only [htriple, hz_lb]
  have hz1 : (1 : ℝ) ≤ z := by linarith only [hz12000]
  have hzpos : (0 : ℝ) < z := by linarith only [hz1]
  have hT_nonneg : (0 : ℝ) ≤ T := by linarith only [hT_lb, h2]
  -- `log z ≤ 3 ℓ₃`, hence `T log z ≤ 15 ℓ₂ ℓ₃`.
  have hzc : z ≤ 4 * c * (ℓ2 * ℓ3) := by linarith only [hz_ub]
  have hlz : Real.log z ≤ 3 * ℓ3 := by
    have e1 : Real.log z ≤ Real.log (4 * c * (ℓ2 * ℓ3)) := Real.log_le_log hzpos hzc
    have e2 : Real.log (4 * c * (ℓ2 * ℓ3))
        = Real.log (4 * c) + (Real.log ℓ2 + Real.log ℓ3) := by
      rw [Real.log_mul (by linarith only [hc] : (0 : ℝ) < 4 * c).ne' hMpos.ne',
        Real.log_mul h2pos.ne' h3pos.ne']
    have e3 : Real.log ℓ3 ≤ ℓ3 := by
      have h := Real.log_le_sub_one_of_pos h3pos; linarith only [h]
    have e4 : Real.log ℓ2 ≤ ℓ3 := le_of_eq h_eq3.symm
    linarith only [e1, e2.le, e3, e4, hlogc]
  have hlz_nonneg : (0 : ℝ) ≤ Real.log z := Real.log_nonneg hz1
  have hTlz : T * Real.log z ≤ 15 * (ℓ2 * ℓ3) := by
    have h := mul_le_mul hT_ub hlz hlz_nonneg (by linarith only [h2] : (0 : ℝ) ≤ 5 * ℓ2)
    linarith only [h]
  -- Generic combination tools.
  have mulE : ∀ {a b s t : ℝ}, 0 ≤ a → 0 ≤ b → a ≤ Real.exp s → b ≤ Real.exp t →
      a * b ≤ Real.exp (s + t) := by
    intro a b s t ha hb has hbt
    rw [Real.exp_add]
    exact mul_le_mul has hbt hb (Real.exp_pos _).le
  have expE : ∀ {s t : ℝ}, s ≤ t → Real.exp s ≤ Real.exp t :=
    fun h => Real.exp_le_exp.mpr h
  have oneE : ∀ s : ℝ, 0 ≤ s → (1 : ℝ) ≤ Real.exp s := fun s hs => by
    linarith only [Real.add_one_le_exp s, hs]
  -- Constants: `8 ≤ exp(ℓ₂ ℓ₃ / 4)`.
  have h8 : (8 : ℝ) ≤ Real.exp (1 / 4 * (ℓ2 * ℓ3)) := by
    have hq : (3 : ℝ) ≤ 1 / 4 * (ℓ2 * ℓ3) := by linarith only [hM]
    have h := Real.quadratic_le_exp_of_nonneg (by linarith only [hq] : (0 : ℝ) ≤ 1 / 4 * (ℓ2 * ℓ3))
    have hsq : (3 : ℝ) ^ 2 ≤ (1 / 4 * (ℓ2 * ℓ3)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hq 2
    linarith only [h, hsq, hq]
  have h2c : (2 : ℝ) ≤ Real.exp (1 / 4 * (ℓ2 * ℓ3)) := by linarith only [h8]
  have h4c : (4 : ℝ) ≤ Real.exp (1 / 4 * (ℓ2 * ℓ3)) := by linarith only [h8]
  have h5c : (5 : ℝ) ≤ Real.exp (1 / 4 * (ℓ2 * ℓ3)) := by linarith only [h8]
  have h7c : (7 : ℝ) ≤ Real.exp (1 / 4 * (ℓ2 * ℓ3)) := by linarith only [h8]
  -- Atoms.
  have hzE : z ≤ Real.exp (3 * (ℓ2 * ℓ3)) := by
    calc z = Real.exp (Real.log z) := (Real.exp_log hzpos).symm
      _ ≤ Real.exp (3 * (ℓ2 * ℓ3)) := expE (by linarith only [hlz, hstar])
  have hzT : z ^ T ≤ Real.exp (15 * (ℓ2 * ℓ3)) := by
    rw [Real.rpow_def_of_pos hzpos]
    exact expE (by linarith only [hTlz])
  have htw0 : 0 ≤ tw := by rw [htw]; exact Real.rpow_nonneg (by norm_num) _
  have htwE : tw ≤ Real.exp (1 / 3 * (ℓ2 * ℓ3)) := by
    rw [htw, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply expE
    have hlog2 : Real.log 2 ≤ 7 / 10 := by
      have h := Real.log_two_lt_d9
      norm_num at h
      linarith only [h]
    have h := mul_le_mul hlog2 hT_ub hT_nonneg (by norm_num)
    linarith only [h, h12l2, hMpos]
  have hx0 : 0 ≤ x := by rw [hx]; exact pow_nonneg hL0 5
  have hxE : x ≤ Real.exp (75 * (ℓ2 * ℓ3)) := by
    rw [hx]
    have h1 : L ^ 5 ≤ Real.exp (15 * (ℓ2 * ℓ3)) ^ 5 := pow_le_pow_left₀ hL0 (hL.trans hzT) 5
    have h2' : Real.exp (15 * (ℓ2 * ℓ3)) ^ 5 = Real.exp (75 * (ℓ2 * ℓ3)) := by
      rw [← Real.exp_nat_mul]
      exact congrArg Real.exp (by push_cast; ring)
    rw [h2'] at h1
    exact h1
  have hkE : k ≤ Real.exp (237 / 4 * (ℓ2 * ℓ3)) := by
    refine hk.trans ?_
    have h1 : x ^ ((79 : ℝ) / 100) ≤ Real.exp (75 * (ℓ2 * ℓ3)) ^ ((79 : ℝ) / 100) :=
      Real.rpow_le_rpow hx0 hxE (by norm_num)
    rw [← Real.exp_mul] at h1
    exact h1.trans (expE (le_of_eq (by ring)))
  have hsxE : sx ≤ Real.exp (75 / 2 * (ℓ2 * ℓ3)) := by
    refine hsx.trans ?_
    rw [Real.sqrt_le_left (Real.exp_pos _).le, sq, ← Real.exp_add]
    exact hxE.trans (expE (le_of_eq (by ring)))
  have hPE : P ≤ Real.exp (1 / 3 * (ℓ2 * ℓ3)) := hP.trans htwE
  have hSE : S ≤ Real.exp (1 / 3 * (ℓ2 * ℓ3)) := hS.trans htwE
  -- Step 2: `(z + 1)(√z + y + log₂ z + 6) + 2T + 2 ≤ 7 z² ≤ exp(25 ℓ₂ ℓ₃ / 4)`.
  have term1 : (z + 1) * (sz + y + lgz + 6) + 2 * T + 2
      ≤ Real.exp (25 / 4 * (ℓ2 * ℓ3)) := by
    have i1 : sz + y + lgz + 6 ≤ 6 * (z + 1) := by linarith only [hsz, hy, hlgz]
    have i2 : (z + 1) * (sz + y + lgz + 6) ≤ (z + 1) * (6 * (z + 1)) :=
      mul_le_mul_of_nonneg_left i1 (by linarith only [hz1])
    have i3 : 12000 * z ≤ z * z := mul_le_mul_of_nonneg_right hz12000 hzpos.le
    have i4 : (z + 1) * (sz + y + lgz + 6) + 2 * T + 2 ≤ 7 * (z * z) := by
      linarith only [i2, i3, hT_ub, hl2z, hz1]
    have i5 : z * z ≤ Real.exp (3 * (ℓ2 * ℓ3) + 3 * (ℓ2 * ℓ3)) :=
      mulE hzpos.le hzpos.le hzE hzE
    have i6 : 7 * (z * z)
        ≤ Real.exp (1 / 4 * (ℓ2 * ℓ3) + (3 * (ℓ2 * ℓ3) + 3 * (ℓ2 * ℓ3))) :=
      mulE (by norm_num) (mul_nonneg hzpos.le hzpos.le) h7c i5
    exact i4.trans (i6.trans (expE (le_of_eq (by ring))))
  -- Step 3: `k (T + 2 + 2^T (√x + 3)) ≤ exp(1171 ℓ₂ ℓ₃ / 12)`.
  have hsx3 : sx + 3 ≤ Real.exp (151 / 4 * (ℓ2 * ℓ3)) := by
    have i1 : sx + 3 ≤ 4 * Real.exp (75 / 2 * (ℓ2 * ℓ3)) := by
      linarith only [hsxE, oneE (75 / 2 * (ℓ2 * ℓ3)) (by linarith only [hMpos])]
    have i2 : (4 : ℝ) * Real.exp (75 / 2 * (ℓ2 * ℓ3))
        ≤ Real.exp (1 / 4 * (ℓ2 * ℓ3) + 75 / 2 * (ℓ2 * ℓ3)) :=
      mulE (by norm_num) (Real.exp_pos _).le h4c (le_refl _)
    exact i1.trans (i2.trans (expE (le_of_eq (by ring))))
  have htwsx : tw * (sx + 3) ≤ Real.exp (457 / 12 * (ℓ2 * ℓ3)) :=
    (mulE htw0 (by linarith only [hsx0]) htwE hsx3).trans (expE (le_of_eq (by ring)))
  have hT2E : T + 2 ≤ Real.exp (457 / 12 * (ℓ2 * ℓ3)) := by
    linarith only [Real.add_one_le_exp (457 / 12 * (ℓ2 * ℓ3)), hT_ub, h12l2, hM]
  have hinner0 : 0 ≤ T + 2 + tw * (sx + 3) := by
    have h := mul_nonneg htw0 (by linarith only [hsx0] : (0 : ℝ) ≤ sx + 3)
    linarith only [h, hT_nonneg]
  have hinner : T + 2 + tw * (sx + 3) ≤ Real.exp (115 / 3 * (ℓ2 * ℓ3)) := by
    have i1 : T + 2 + tw * (sx + 3) ≤ 2 * Real.exp (457 / 12 * (ℓ2 * ℓ3)) := by
      linarith only [hT2E, htwsx]
    have i2 : (2 : ℝ) * Real.exp (457 / 12 * (ℓ2 * ℓ3))
        ≤ Real.exp (1 / 4 * (ℓ2 * ℓ3) + 457 / 12 * (ℓ2 * ℓ3)) :=
      mulE (by norm_num) (Real.exp_pos _).le h2c (le_refl _)
    exact i1.trans (i2.trans (expE (le_of_eq (by ring))))
  have term2 : k * (T + 2 + tw * (sx + 3)) ≤ Real.exp (1171 / 12 * (ℓ2 * ℓ3)) :=
    (mulE hk0 hinner0 hkE hinner).trans (expE (le_of_eq (by ring)))
  -- Step 4: `P (L + 3) + 1 ≤ exp(95 ℓ₂ ℓ₃ / 6)`.
  have hL3 : L + 3 ≤ Real.exp (61 / 4 * (ℓ2 * ℓ3)) := by
    have i1 : L + 3 ≤ 4 * Real.exp (15 * (ℓ2 * ℓ3)) := by
      linarith only [hL, hzT, oneE (15 * (ℓ2 * ℓ3)) (by linarith only [hMpos])]
    have i2 : (4 : ℝ) * Real.exp (15 * (ℓ2 * ℓ3))
        ≤ Real.exp (1 / 4 * (ℓ2 * ℓ3) + 15 * (ℓ2 * ℓ3)) :=
      mulE (by norm_num) (Real.exp_pos _).le h4c (le_refl _)
    exact i1.trans (i2.trans (expE (le_of_eq (by ring))))
  have hPL : P * (L + 3) ≤ Real.exp (187 / 12 * (ℓ2 * ℓ3)) :=
    (mulE hP0 (by linarith only [hL0]) hPE hL3).trans (expE (le_of_eq (by ring)))
  have term3 : P * (L + 3) + 1 ≤ Real.exp (95 / 6 * (ℓ2 * ℓ3)) := by
    have i1 : P * (L + 3) + 1 ≤ 2 * Real.exp (187 / 12 * (ℓ2 * ℓ3)) := by
      linarith only [hPL, oneE (187 / 12 * (ℓ2 * ℓ3)) (by linarith only [hMpos])]
    have i2 : (2 : ℝ) * Real.exp (187 / 12 * (ℓ2 * ℓ3))
        ≤ Real.exp (1 / 4 * (ℓ2 * ℓ3) + 187 / 12 * (ℓ2 * ℓ3)) :=
      mulE (by norm_num) (Real.exp_pos _).le h2c (le_refl _)
    exact i1.trans (i2.trans (expE (le_of_eq (by ring))))
  -- Step 5: `S (√x + S + 6) + 4 ≤ exp(115 ℓ₂ ℓ₃ / 3)`.
  have hSE' : S ≤ Real.exp (75 / 2 * (ℓ2 * ℓ3)) :=
    hSE.trans (expE (by linarith only [hMpos]))
  have hinner4 : sx + S + 6 ≤ Real.exp (151 / 4 * (ℓ2 * ℓ3)) := by
    have i1 : sx + S + 6 ≤ 8 * Real.exp (75 / 2 * (ℓ2 * ℓ3)) := by
      linarith only [hsxE, hSE', oneE (75 / 2 * (ℓ2 * ℓ3)) (by linarith only [hMpos])]
    have i2 : (8 : ℝ) * Real.exp (75 / 2 * (ℓ2 * ℓ3))
        ≤ Real.exp (1 / 4 * (ℓ2 * ℓ3) + 75 / 2 * (ℓ2 * ℓ3)) :=
      mulE (by norm_num) (Real.exp_pos _).le h8 (le_refl _)
    exact i1.trans (i2.trans (expE (le_of_eq (by ring))))
  have hSin : S * (sx + S + 6) ≤ Real.exp (457 / 12 * (ℓ2 * ℓ3)) :=
    (mulE hS0 (by linarith only [hsx0, hS0]) hSE hinner4).trans (expE (le_of_eq (by ring)))
  have term4 : S * (sx + S + 6) + 4 ≤ Real.exp (115 / 3 * (ℓ2 * ℓ3)) := by
    have i1 : S * (sx + S + 6) + 4 ≤ 5 * Real.exp (457 / 12 * (ℓ2 * ℓ3)) := by
      linarith only [hSin, oneE (457 / 12 * (ℓ2 * ℓ3)) (by linarith only [hMpos])]
    have i2 : (5 : ℝ) * Real.exp (457 / 12 * (ℓ2 * ℓ3))
        ≤ Real.exp (1 / 4 * (ℓ2 * ℓ3) + 457 / 12 * (ℓ2 * ℓ3)) :=
      mulE (by norm_num) (Real.exp_pos _).le h5c (le_refl _)
    exact i1.trans (i2.trans (expE (le_of_eq (by ring))))
  -- Combine the four summands.
  have mono : ∀ s t : ℝ, s ≤ t →
      Real.exp (s * (ℓ2 * ℓ3)) ≤ Real.exp (t * (ℓ2 * ℓ3)) := fun s t hst =>
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hst hMpos.le)
  have b1 := term1.trans (mono _ _ (by norm_num : (25 / 4 : ℝ) ≤ 1171 / 12))
  have b3 := term3.trans (mono _ _ (by norm_num : (95 / 6 : ℝ) ≤ 1171 / 12))
  have b4 := term4.trans (mono _ _ (by norm_num : (115 / 3 : ℝ) ≤ 1171 / 12))
  have hsum : (z + 1) * (sz + y + lgz + 6) + 2 * T + 2 + k * (T + 2 + tw * (sx + 3))
      + P * (L + 3) + 1 + S * (sx + S + 6) + 4
      ≤ 4 * Real.exp (1171 / 12 * (ℓ2 * ℓ3)) := by
    linarith only [b1, term2, b3, b4]
  have hfin : (4 : ℝ) * Real.exp (1171 / 12 * (ℓ2 * ℓ3))
      ≤ Real.exp (1 / 4 * (ℓ2 * ℓ3) + 1171 / 12 * (ℓ2 * ℓ3)) :=
    mulE (by norm_num) (Real.exp_pos _).le h4c (le_refl _)
  refine hsum.trans (hfin.trans (expE ?_))
  linarith only [hMpos]

/-- The budget `costPieces` of `Alg.search` at any scales in the window is
`exp(O(ℓ₂ ℓ₃))`. -/
theorem costPieces_leW (C₁ E : ℝ) (hE : 0 < E) (_hE2 : E ≤ 1 / 2)
    (h1000 : (1000 : ℝ) ≤ C₁) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ z w y T : ℕ, InWindow C₁ E n z w y T →
      ∀ L x k P S : ℕ,
      L ≤ z ^ T → x = L ^ 5 → (k : ℝ) ≤ (x : ℝ) ^ ((79 : ℝ) / 100) →
      P ≤ 2 ^ T → S ≤ 2 ^ T →
      (costPieces z y T L x k P S : ℝ) ≤ Real.exp (100 * ell2 n * ell3 n) := by
  have h2ev : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ell2 n :=
    tendsto_ell2_atTop'.eventually_ge_atTop 1
  have h3ev : ∀ᶠ n : ℕ in atTop, (12 : ℝ) ≤ ell3 n :=
    tendsto_ell3_atTop'.eventually_ge_atTop 12
  have hlogcev : ∀ᶠ n : ℕ in atTop, Real.log (4 * C₁) ≤ ell3 n :=
    tendsto_ell3_atTop'.eventually_ge_atTop _
  filter_upwards [h2ev, h3ev, hlogcev] with n h2 h3 hlogc
  intro z w y T hw L x k P S hL hx hk hP hS
  -- The real-number inputs.
  have hz1 : (1 : ℝ) ≤ (z : ℝ) := by
    have i1 : (1000 : ℝ) * 1 ≤ C₁ * ell2 n :=
      mul_le_mul h1000 h2 zero_le_one (by linarith only [h1000])
    have i2 : (1000 : ℝ) * 1 * 12 ≤ C₁ * ell2 n * ell3 n :=
      mul_le_mul i1 h3 (by norm_num)
        (mul_nonneg (by linarith only [h1000]) (by linarith only [h2]))
    linarith only [i2, hw.z_lo]
  have hy : (y : ℝ) ≤ 4 * (z : ℝ) := by
    have h1 : (z : ℝ) ^ ((1 : ℝ) - E) ≤ (z : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hz1 (by linarith only [hE])
    rw [Real.rpow_one] at h1
    linarith only [hw.y_hi, h1]
  have hsz : ((Nat.sqrt z : ℕ) : ℝ) ≤ (z : ℝ) := by exact_mod_cast Nat.sqrt_le_self z
  have hlgz : ((Nat.log 2 z : ℕ) : ℝ) ≤ (z : ℝ) := by exact_mod_cast Nat.log_le_self 2 z
  have hLr : (L : ℝ) ≤ (z : ℝ) ^ (T : ℝ) := by
    rw [Real.rpow_natCast]; exact_mod_cast hL
  have hxr : (x : ℝ) = (L : ℝ) ^ 5 := by rw [hx, Nat.cast_pow]
  have hsx : ((Nat.sqrt x : ℕ) : ℝ) ≤ Real.sqrt (x : ℝ) := Real.nat_sqrt_le_real_sqrt
  have hPr : (P : ℝ) ≤ (2 : ℝ) ^ T := by exact_mod_cast hP
  have hSr : (S : ℝ) ≤ (2 : ℝ) ^ T := by exact_mod_cast hS
  have key := costPieces_bound h1000 h2 h3 rfl hlogc hw.z_lo hw.z_hi hy hw.T_lo hw.T_hi
    hsz hlgz (Nat.cast_nonneg L) hLr hxr (Nat.cast_nonneg _) hsx (Nat.cast_nonneg k) hk
    (Real.rpow_natCast 2 T).symm (Nat.cast_nonneg P) hPr (Nat.cast_nonneg S) hSr
  unfold costPieces
  push_cast
  linarith only [key]

namespace Alg

/-- `prodL` computes the product. -/
theorem prodL_fst : ∀ Q : List ℕ, (prodL Q).1 = Q.prod
  | [] => rfl
  | p :: S => by simp only [prodL, List.prod_cons, prodL_fst S]

/-- `prodL` charges one unit per element. -/
theorem prodL_snd : ∀ Q : List ℕ, (prodL Q).2 = Q.length
  | [] => rfl
  | p :: S => by simp only [prodL, List.length_cons, prodL_snd S]

end Alg

/-- `Alg.search` on its success path, output and cost unfolded. -/
theorem search_success (sc : Scales) (n : ℕ) (Q : List ℕ) (k : ℕ) (P : List ℕ)
    (m : ℕ) (S : List ℕ)
    (hlen : sc.T ≤ (Alg.reservoir sc.z sc.z99 sc.y).1.length)
    (hQ : Q = (Alg.reservoir sc.z sc.z99 sc.y).1.drop
      ((Alg.reservoir sc.z sc.z99 sc.y).1.length - sc.T))
    (hscan : (Alg.scan Q (Q.prod ^ 5) sc.z sc.θ 1 (Q.prod ^ 5)).1 = some (k, P))
    (hext : (Alg.extract Q.prod n P).1 = some (m, S))
    (hver : (Alg.verify m S).1 = true) :
    Alg.search sc n = (some (m, S),
      (Alg.reservoir sc.z sc.z99 sc.y).2 + 2 * sc.T + 2
        + (Alg.scan Q (Q.prod ^ 5) sc.z sc.θ 1 (Q.prod ^ 5)).2
        + (Alg.extract Q.prod n P).2 + (Alg.verify m S).2) := by
  have hp1 : (Alg.prodL Q).1 = Q.prod := Alg.prodL_fst Q
  have hp2 : (Alg.prodL Q).2 = sc.T := by
    rw [Alg.prodL_snd, hQ, List.length_drop]; omega
  simp only [Alg.search]
  rw [if_neg (not_lt.mpr hlen), ← hQ, hp1, hp2]
  simp only [hscan, hext, hver, if_true]
  congr 1
  omega

end Carmichael
