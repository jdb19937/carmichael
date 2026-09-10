/-
Machine scales (Route T, sortie T7).

A Turing machine computes the step-1 scales from bit lengths only
(iterated `Nat.log 2`); `scalesTM` is that computation as a plain `def`, and
`scalesTM_inWindow` shows the result lies in the analysis window `InWindow`
with the pool threshold within a constant factor of `(log n)^{1.2}`.
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Carmichael.Algorithm
import Carmichael.DefsW

set_option autoImplicit false

namespace Carmichael

open Filter

/-- The scales a Turing machine computes from `n` using only bit lengths
(`Nat.log 2`): `a ≈ ℓ₂ / log 2`, `b ≈ ℓ₃ / log 2`, `z = C₁ a b`, floor
`w = 2^{⌈0.99·bits z⌉}`, smoothness bound `y = 2^{⌈(1 - 1/K)·bits z⌉}`,
`T = 3a`, threshold `θ = 2^{⌈1.2·bits(bits n)⌉}`. -/
def scalesTM (C₁ K n : ℕ) : Scales :=
  let a := Nat.log 2 (Nat.log 2 n)
  let b := Nat.log 2 a
  let z := C₁ * a * b
  let bz := Nat.log 2 z + 1
  ⟨z, 2 ^ ((99 * bz + 99) / 100), 2 ^ (((K - 1) * bz + K - 1) / K), 3 * a,
   2 ^ ((6 * (Nat.log 2 (Nat.log 2 n + 1) + 1) + 4) / 5)⟩

/-- The bridge between `Nat.log 2` and `Real.log`:
`⌊log₂ m⌋ · log 2 ≤ log m < (⌊log₂ m⌋ + 1) · log 2`. -/
theorem natLog_bridge (m : ℕ) (hm : 1 ≤ m) :
    (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m ∧
      Real.log m < ((Nat.log 2 m : ℝ) + 1) * Real.log 2 := by
  have h1 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
  have h2 : m < 2 ^ (Nat.log 2 m + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have h1r : (2 : ℝ) ^ Nat.log 2 m ≤ (m : ℝ) := by exact_mod_cast h1
  have h2r : (m : ℝ) < (2 : ℝ) ^ (Nat.log 2 m + 1) := by exact_mod_cast h2
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · have := Real.log_le_log (by positivity) h1r
    rwa [Real.log_pow] at this
  · have := Real.log_lt_log hm0 h2r
    rw [Real.log_pow] at this
    push_cast at this
    exact this

/-- Powers of two sandwich a real power: if `e` is within `c` above
`α · bits m` (with `bits m = ⌊log₂ m⌋ + 1`), then
`m^α ≤ 2^e ≤ 2^c · 2^α · m^α`. -/
theorem pow2_sandwich (m e : ℕ) (hm : 1 ≤ m) (α c : ℝ) (hα : 0 ≤ α)
    (hlo : α * ((Nat.log 2 m : ℝ) + 1) ≤ e)
    (hhi : (e : ℝ) ≤ α * ((Nat.log 2 m : ℝ) + 1) + c) :
    (m : ℝ) ^ α ≤ (2 : ℝ) ^ e ∧
      ((2 : ℝ) ^ e : ℝ) ≤ 2 ^ c * (2 ^ α * (m : ℝ) ^ α) := by
  set B : ℕ := Nat.log 2 m + 1 with hB
  have hB' : ((Nat.log 2 m : ℝ) + 1) = (B : ℝ) := by rw [hB]; push_cast; ring
  rw [hB'] at hlo hhi
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : (m : ℝ) ≤ (2 : ℝ) ^ B := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
    exact_mod_cast this.le
  have h2 : (2 : ℝ) ^ B ≤ 2 * m := by
    have := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
    have h' : (2 : ℝ) ^ (Nat.log 2 m) ≤ m := by exact_mod_cast this
    rw [hB, pow_succ]
    linarith
  have e1 : ((2 : ℝ) ^ e : ℝ) = (2 : ℝ) ^ (e : ℝ) := (Real.rpow_natCast 2 e).symm
  have e2 : ((2 : ℝ) ^ B : ℝ) = (2 : ℝ) ^ (B : ℝ) := (Real.rpow_natCast 2 B).symm
  have hB0 : (0 : ℝ) ≤ (2 : ℝ) ^ B := by positivity
  constructor
  · calc (m : ℝ) ^ α ≤ ((2 : ℝ) ^ B) ^ α := Real.rpow_le_rpow hm0 h1 hα
      _ = (2 : ℝ) ^ ((B : ℝ) * α) := by
          rw [e2, ← Real.rpow_mul (by norm_num)]
      _ ≤ (2 : ℝ) ^ (e : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = (2 : ℝ) ^ e := Real.rpow_natCast 2 e
  · calc ((2 : ℝ) ^ e : ℝ) = (2 : ℝ) ^ (e : ℝ) := e1
      _ ≤ (2 : ℝ) ^ (α * (B : ℝ) + c) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hhi
      _ = 2 ^ c * ((2 : ℝ) ^ B) ^ α := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2), e2,
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm (B : ℝ) α]
          exact mul_comm _ _
      _ ≤ 2 ^ c * (2 * m) ^ α :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hB0 h2 hα) (by positivity)
      _ = 2 ^ c * (2 ^ α * (m : ℝ) ^ α) := by
          rw [Real.mul_rpow (by norm_num) hm0]

/-- The sandwich with exponents `α, c ≤ 1`: `m^α ≤ 2^e ≤ 4 m^α`. -/
theorem pow2_sandwich4 (m e : ℕ) (hm : 1 ≤ m) (α c : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hc1 : c ≤ 1)
    (hlo : α * ((Nat.log 2 m : ℝ) + 1) ≤ e)
    (hhi : (e : ℝ) ≤ α * ((Nat.log 2 m : ℝ) + 1) + c) :
    (m : ℝ) ^ α ≤ (2 : ℝ) ^ e ∧ ((2 : ℝ) ^ e : ℝ) ≤ 4 * (m : ℝ) ^ α := by
  obtain ⟨h1, h2⟩ := pow2_sandwich m e hm α c hα hlo hhi
  refine ⟨h1, le_trans h2 ?_⟩
  have hP : (0 : ℝ) ≤ (m : ℝ) ^ α := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hu : (2 : ℝ) ^ c ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hc1
    rwa [Real.rpow_one] at this
  have hv : (2 : ℝ) ^ α ≤ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1
    rwa [Real.rpow_one] at this
  have hv0 : (0 : ℝ) ≤ (2 : ℝ) ^ α := by positivity
  calc (2 : ℝ) ^ c * (2 ^ α * (m : ℝ) ^ α)
      ≤ 2 * (2 ^ α * (m : ℝ) ^ α) :=
        mul_le_mul_of_nonneg_right hu (mul_nonneg hv0 hP)
    _ ≤ 2 * (2 * (m : ℝ) ^ α) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hv hP) (by norm_num)
    _ = 4 * (m : ℝ) ^ α := by ring

/-- For `n` large the machine's scales lie in the analysis window, and the
threshold is within a constant factor of `(log n)^{1.2}`. -/
theorem scalesTM_inWindow (C₁ K : ℕ) (h1000 : 1000 ≤ C₁) (hK : 2 ≤ K) :
    ∀ᶠ n : ℕ in Filter.atTop,
      InWindow (C₁ : ℝ) (1 / (K : ℝ)) n (scalesTM C₁ K n).z (scalesTM C₁ K n).z99
        (scalesTM C₁ K n).y (scalesTM C₁ K n).T ∧
      (Real.log n) ^ (1.2 : ℝ) ≤ ((scalesTM C₁ K n).θ : ℝ) ∧
      ((scalesTM C₁ K n).θ : ℝ) ≤ 16 * (Real.log n) ^ (1.2 : ℝ) := by
  obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
  have hL1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hL2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have t1 : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have t2 : Tendsto ell2 atTop atTop := Real.tendsto_log_atTop.comp t1
  have t3 : Tendsto ell3 atTop atTop := Real.tendsto_log_atTop.comp t2
  filter_upwards [eventually_ge_atTop 2, t1.eventually_ge_atTop 3,
    t2.eventually_ge_atTop 200, t3.eventually_ge_atTop 3] with n hn2 h1 h2 h3
  simp only [scalesTM, Nat.add_sub_cancel]
  have hl1pos : (0 : ℝ) < Real.log n := by linarith
  have hl2pos : (0 : ℝ) < ell2 n := by linarith
  have hl3nn : (0 : ℝ) ≤ ell3 n := by linarith
  have hC : (1000 : ℝ) ≤ C₁ := by exact_mod_cast h1000
  have hC0 : (0 : ℝ) ≤ C₁ := by linarith
  -- Layer 1: `n → M = ⌊log₂ n⌋`.
  have hn1 : 1 ≤ n := by omega
  obtain ⟨bn1, bn2⟩ := natLog_bridge n hn1
  set M := Nat.log 2 n with hM
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  -- `log n ≤ M` (as reals), since `log n < (M+1) log 2` and `log n (1 - log 2) ≥ log 2`.
  have hMreal : Real.log n ≤ (M : ℝ) := by
    have hpos : (0 : ℝ) ≤ 1 - Real.log 2 := by linarith
    have := mul_le_mul_of_nonneg_right h1 hpos
    have key : Real.log n * Real.log 2 < (M : ℝ) * Real.log 2 := by linarith
    exact (lt_of_mul_lt_mul_right key (by linarith)).le
  have hM1 : 1 ≤ M := by
    have h : (0 : ℝ) < M := by linarith
    have h' : 0 < M := by exact_mod_cast h
    omega
  -- `M ≤ 1.5 log n`, since `M log 2 ≤ log n` and `1.5 log 2 ≥ 1`.
  have hMhi : (M : ℝ) ≤ 1.5 * Real.log n := by
    have : (M : ℝ) * 1 ≤ (M : ℝ) * (1.5 * Real.log 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hM0
    linarith
  -- `log n ≤ M + 1 ≤ 2 log n`.
  have hN_lo : Real.log n ≤ (M : ℝ) + 1 := by
    have : ((M : ℝ) + 1) * Real.log 2 ≤ ((M : ℝ) + 1) * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hN_hi : (M : ℝ) + 1 ≤ 2 * Real.log n := by
    have hpos : (0 : ℝ) ≤ 2 * Real.log 2 - 1 := by linarith
    have := mul_le_mul_of_nonneg_right h1 hpos
    have key : ((M : ℝ) + 1) * Real.log 2 ≤ (2 * Real.log n) * Real.log 2 := by linarith
    exact le_of_mul_le_mul_right key (by linarith)
  -- Layer 2: `M → a = ⌊log₂ M⌋`, with `ℓ₂ ≤ a ≤ 1.45 ℓ₂`.
  obtain ⟨bM1, bM2⟩ := natLog_bridge M hM1
  set a := Nat.log 2 M with ha
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hlogM_lo : ell2 n ≤ Real.log M := Real.log_le_log hl1pos hMreal
  have hlogM_hi : Real.log M ≤ ell2 n + 0.5 := by
    have hMpos : (0 : ℝ) < M := by linarith
    have := Real.log_le_log hMpos hMhi
    rw [Real.log_mul (by norm_num) hl1pos.ne'] at this
    have h15 : Real.log 1.5 ≤ 0.5 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.5)
      linarith
    unfold ell2
    linarith
  have ha_lo : ell2 n ≤ (a : ℝ) := by
    have hpos : (0 : ℝ) ≤ 1 - Real.log 2 := by linarith
    have := mul_le_mul_of_nonneg_right h2 hpos
    have key : ell2 n * Real.log 2 < (a : ℝ) * Real.log 2 := by linarith
    exact (lt_of_mul_lt_mul_right key (by linarith)).le
  have ha_hi : (a : ℝ) ≤ 1.45 * ell2 n := by
    have : (a : ℝ) * 0.6931471803 ≤ (a : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hL1.le ha0
    linarith
  have ha1 : 1 ≤ a := by
    have h : (0 : ℝ) < a := by linarith
    have h' : 0 < a := by exact_mod_cast h
    omega
  -- Layer 3: `a → b = ⌊log₂ a⌋`, with `ℓ₃ ≤ b ≤ 2 ℓ₃`.
  obtain ⟨ba1, ba2⟩ := natLog_bridge a ha1
  set b := Nat.log 2 a with hb
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hloga_lo : ell3 n ≤ Real.log a := Real.log_le_log hl2pos ha_lo
  have hloga_hi : Real.log a ≤ ell3 n + 0.45 := by
    have hapos : (0 : ℝ) < a := by linarith
    have := Real.log_le_log hapos ha_hi
    rw [Real.log_mul (by norm_num) hl2pos.ne'] at this
    have h145 : Real.log 1.45 ≤ 0.45 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.45)
      linarith
    unfold ell3
    linarith
  have hb_lo : ell3 n ≤ (b : ℝ) := by
    have hpos : (0 : ℝ) ≤ 1 - Real.log 2 := by linarith
    have := mul_le_mul_of_nonneg_right h3 hpos
    have key : ell3 n * Real.log 2 < (b : ℝ) * Real.log 2 := by linarith
    exact (lt_of_mul_lt_mul_right key (by linarith)).le
  have hb_hi : (b : ℝ) ≤ 2 * ell3 n := by
    have : (b : ℝ) * 0.6931471803 ≤ (b : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hL1.le hb0
    linarith
  -- `z = C₁ a b ∈ [C₁ ℓ₂ ℓ₃, 2.9 C₁ ℓ₂ ℓ₃]`.
  set z := C₁ * a * b with hz
  have hzr : (z : ℝ) = C₁ * a * b := by rw [hz]; push_cast; ring
  have hz_lo : (C₁ : ℝ) * ell2 n * ell3 n ≤ (z : ℝ) := by
    rw [hzr]
    have h' : (C₁ : ℝ) * ell2 n ≤ (C₁ : ℝ) * a := mul_le_mul_of_nonneg_left ha_lo hC0
    exact mul_le_mul h' hb_lo hl3nn (mul_nonneg hC0 ha0)
  have hz_hi : (z : ℝ) ≤ 4 * ((C₁ : ℝ) * ell2 n * ell3 n) := by
    rw [hzr]
    have h' : (C₁ : ℝ) * a ≤ (C₁ : ℝ) * (1.45 * ell2 n) := mul_le_mul_of_nonneg_left ha_hi hC0
    have h'' : (C₁ : ℝ) * a * b ≤ (C₁ : ℝ) * (1.45 * ell2 n) * (2 * ell3 n) :=
      mul_le_mul h' hb_hi hb0 (mul_nonneg hC0 (by linarith))
    have hp : (0 : ℝ) ≤ (C₁ : ℝ) * ell2 n * ell3 n :=
      mul_nonneg (mul_nonneg hC0 hl2pos.le) hl3nn
    linarith
  have hz1 : 1 ≤ z := by
    have h : (0 : ℝ) < z := by
      have := mul_pos (mul_pos (by linarith : (0 : ℝ) < C₁) hl2pos)
        (by linarith : (0 : ℝ) < ell3 n)
      linarith
    have h' : 0 < z := by exact_mod_cast h
    omega
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  -- Bits of `z`.
  set bz := Nat.log 2 z + 1 with hbz
  have hbzr : (bz : ℝ) = (Nat.log 2 z : ℝ) + 1 := by rw [hbz]; push_cast; ring
  -- The reservoir floor `w = 2^{⌈99 bz / 100⌉}`.
  set e₁ := (99 * bz + 99) / 100 with he₁
  have e₁_nat : 99 * bz ≤ 100 * e₁ ∧ 100 * e₁ ≤ 99 * bz + 99 := by omega
  have e₁_lo : (99 / 100 : ℝ) * ((Nat.log 2 z : ℝ) + 1) ≤ e₁ := by
    have : ((99 * bz : ℕ) : ℝ) ≤ ((100 * e₁ : ℕ) : ℝ) := by exact_mod_cast e₁_nat.1
    push_cast at this
    rw [hbzr] at this
    linarith
  have e₁_hi : (e₁ : ℝ) ≤ (99 / 100 : ℝ) * ((Nat.log 2 z : ℝ) + 1) + 99 / 100 := by
    have : ((100 * e₁ : ℕ) : ℝ) ≤ ((99 * bz + 99 : ℕ) : ℝ) := by exact_mod_cast e₁_nat.2
    push_cast at this
    rw [hbzr] at this
    linarith
  obtain ⟨w_lo, w_hi⟩ := pow2_sandwich4 z e₁ hz1 (99 / 100) (99 / 100) (by norm_num)
    (by norm_num) (by norm_num) e₁_lo e₁_hi
  -- The smoothness bound `y = 2^{⌈(K-1) bz / K⌉}`.
  rw [show K' * bz + (K' + 1) - 1 = K' * bz + K' by omega]
  set e₂ := (K' * bz + K') / (K' + 1) with he₂
  have e₂_nat : K' * bz ≤ (K' + 1) * e₂ ∧ (K' + 1) * e₂ ≤ K' * bz + K' := by
    have h1 : (K' + 1) * e₂ + (K' * bz + K') % (K' + 1) = K' * bz + K' :=
      Nat.div_add_mod (K' * bz + K') (K' + 1)
    have h2 := Nat.mod_lt (K' * bz + K') (show 0 < K' + 1 by omega)
    omega
  have hKpos : (0 : ℝ) < ((K' + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos K'
  set α : ℝ := (1 : ℝ) - 1 / ((K' + 1 : ℕ) : ℝ) with hα
  have hαK : α * ((K' + 1 : ℕ) : ℝ) = (K' : ℝ) := by
    rw [hα]
    push_cast
    field_simp
    ring
  have hα0 : 0 ≤ α := by
    rw [hα]
    have : 1 / ((K' + 1 : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one hKpos]
      push_cast
      linarith [(Nat.cast_nonneg K' : (0 : ℝ) ≤ K')]
    linarith
  have hα1 : α ≤ 1 := by
    rw [hα]
    have : 0 ≤ 1 / ((K' + 1 : ℕ) : ℝ) := by positivity
    linarith
  have e₂_lo : α * ((Nat.log 2 z : ℝ) + 1) ≤ e₂ := by
    refine le_of_mul_le_mul_right ?_ hKpos
    have : ((K' * bz : ℕ) : ℝ) ≤ (((K' + 1) * e₂ : ℕ) : ℝ) := by exact_mod_cast e₂_nat.1
    push_cast at this
    rw [hbzr] at this
    calc α * ((Nat.log 2 z : ℝ) + 1) * ((K' + 1 : ℕ) : ℝ)
        = (α * ((K' + 1 : ℕ) : ℝ)) * ((Nat.log 2 z : ℝ) + 1) := by ring
      _ = (K' : ℝ) * ((Nat.log 2 z : ℝ) + 1) := by rw [hαK]
      _ ≤ (e₂ : ℝ) * ((K' + 1 : ℕ) : ℝ) := by push_cast; linarith
  have e₂_hi : (e₂ : ℝ) ≤ α * ((Nat.log 2 z : ℝ) + 1) + 1 := by
    have h := e₂_nat.2
    have : (((K' + 1) * e₂ : ℕ) : ℝ) ≤ ((K' * bz + K' : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this
    rw [hbzr] at this
    have hsub : (e₂ : ℝ) - 1 ≤ α * ((Nat.log 2 z : ℝ) + 1) := by
      refine le_of_mul_le_mul_right ?_ hKpos
      calc ((e₂ : ℝ) - 1) * ((K' + 1 : ℕ) : ℝ) ≤ (K' : ℝ) * ((Nat.log 2 z : ℝ) + 1) := by
            push_cast; linarith
        _ = (α * ((K' + 1 : ℕ) : ℝ)) * ((Nat.log 2 z : ℝ) + 1) := by rw [hαK]
        _ = α * ((Nat.log 2 z : ℝ) + 1) * ((K' + 1 : ℕ) : ℝ) := by ring
    linarith
  obtain ⟨y_lo, y_hi⟩ := pow2_sandwich4 z e₂ hz1 α 1 hα0 hα1 le_rfl e₂_lo e₂_hi
  -- The threshold `θ = 2^{⌈6 bN / 5⌉}` with `bN = bits (M + 1)`.
  set N := M + 1 with hN
  have hN1 : 1 ≤ N := by omega
  have hNr : (N : ℝ) = (M : ℝ) + 1 := by rw [hN]; push_cast; ring
  set bN := Nat.log 2 N + 1 with hbN
  have hbNr : (bN : ℝ) = (Nat.log 2 N : ℝ) + 1 := by rw [hbN]; push_cast; ring
  set f := (6 * bN + 4) / 5 with hf
  have f_nat : 6 * bN ≤ 5 * f ∧ 5 * f ≤ 6 * bN + 4 := by omega
  have f_lo : (1.2 : ℝ) * ((Nat.log 2 N : ℝ) + 1) ≤ f := by
    have : ((6 * bN : ℕ) : ℝ) ≤ ((5 * f : ℕ) : ℝ) := by exact_mod_cast f_nat.1
    push_cast at this
    rw [hbNr] at this
    linarith
  have f_hi : (f : ℝ) ≤ (1.2 : ℝ) * ((Nat.log 2 N : ℝ) + 1) + 0.8 := by
    have : ((5 * f : ℕ) : ℝ) ≤ ((6 * bN + 4 : ℕ) : ℝ) := by exact_mod_cast f_nat.2
    push_cast at this
    rw [hbNr] at this
    linarith
  obtain ⟨θ_lo, θ_hi⟩ := pow2_sandwich N f hN1 (1.2) (0.8) (by norm_num) f_lo f_hi
  have h4 : (2 : ℝ) ^ (0.8 : ℝ) * 2 ^ (1.2 : ℝ) = 4 := by
    rw [← Real.rpow_add two_pos, show (0.8 : ℝ) + 1.2 = 2 by norm_num, Real.rpow_two]
    norm_num
  have h2pow : (2 : ℝ) ^ (1.2 : ℝ) ≤ 4 := by
    calc (2 : ℝ) ^ (1.2 : ℝ) ≤ 2 ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 4 := by rw [Real.rpow_two]; norm_num
  have hN12_lo : (Real.log n) ^ (1.2 : ℝ) ≤ (N : ℝ) ^ (1.2 : ℝ) := by
    rw [hNr]
    exact Real.rpow_le_rpow hl1pos.le hN_lo (by norm_num)
  have hN12_hi : (N : ℝ) ^ (1.2 : ℝ) ≤ 4 * (Real.log n) ^ (1.2 : ℝ) := by
    rw [hNr]
    calc ((M : ℝ) + 1) ^ (1.2 : ℝ) ≤ (2 * Real.log n) ^ (1.2 : ℝ) :=
          Real.rpow_le_rpow (by linarith) hN_hi (by norm_num)
      _ = 2 ^ (1.2 : ℝ) * (Real.log n) ^ (1.2 : ℝ) :=
          Real.mul_rpow (by norm_num) hl1pos.le
      _ ≤ 4 * (Real.log n) ^ (1.2 : ℝ) :=
          mul_le_mul_of_nonneg_right h2pow (Real.rpow_nonneg hl1pos.le _)
  have hθ_hi : ((2 : ℝ) ^ f : ℝ) ≤ 16 * (Real.log n) ^ (1.2 : ℝ) := by
    calc ((2 : ℝ) ^ f : ℝ) ≤ 2 ^ (0.8 : ℝ) * (2 ^ (1.2 : ℝ) * (N : ℝ) ^ (1.2 : ℝ)) := θ_hi
      _ = 4 * (N : ℝ) ^ (1.2 : ℝ) := by rw [← mul_assoc, h4]
      _ ≤ 4 * (4 * (Real.log n) ^ (1.2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hN12_hi (by norm_num)
      _ = 16 * (Real.log n) ^ (1.2 : ℝ) := by ring
  -- Assemble.
  refine ⟨⟨hz_lo, hz_hi, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    exact w_hi
  · simp only [Nat.cast_pow, Nat.cast_ofNat]
    exact y_lo
  · simp only [Nat.cast_pow, Nat.cast_ofNat]
    exact y_hi
  · push_cast
    linarith
  · push_cast
    linarith
  · push_cast
    exact le_trans hN12_lo θ_lo
  · push_cast
    exact hθ_hi

end Carmichael
