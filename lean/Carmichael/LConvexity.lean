/-
Route Z, sortie Z4a′: the convexity bound for Dirichlet L-functions
(routez/Z0b-density.md §12.1, frozen interface I1, primitive case).

Deliverable: an explicit `C_cx` with
  `‖L(s,χ)‖ ≤ C_cx · (N·(|t|+2))^{(1−σ)/2} · log(N·(|t|+3))`
for primitive nontrivial `χ mod N` and `s = σ + it` with `1/200 ≤ σ ≤ 1`
(`norm_LFunction_le_convexity`), together with the combined form on
`1/200 ≤ σ ≤ 2` where the exponent is `max ((1−σ)/2) 0`
(`norm_LFunction_le_convexity'`).  Delivered constant: `C_cx = 100000`.

Architecture (two Phragmén–Lindelöf applications, no Stirling):
1. `gaussSum_mul_conj`: `g(χ)·conj g(χ) = N` for primitive `χ` (mulShift
   averaging against `AddChar.sum_mulShift` orthogonality), hence
   `norm_rootNumber_eq_one`.
2. `norm_LFunction_le_of_one_lt_re`: `‖L(z,χ)‖ ≤ 1 + 1/(Re z − 1)` on `Re z > 1`
   (termwise Dirichlet-series bound).
3. `norm_Gamma_sq_of_re_one`: exact modulus `‖Γ(1+iv)‖² = πv/sinh(πv)`, giving
   `‖Γ(1−z)·sin(π(z+a)/2)‖ ≤ 3(2+|Im z|)^{1/2}` on the line `Re z = 0`.
4. `norm_Gamma_one_sub_mul_sin_interp`: Phragmén–Lindelöf on the strip
   `[−1/2, 0]` with Gaussian and power normalizers interpolates the LGrowth
   strip bound (exponent 1 at `Re = −1/2`) against step 3 (exponent 1/2 at
   `Re = 0`): `‖Γ(1−z)·sin(π(z+a)/2)‖ ≤ 34(2+|Im z|)^{1/2−Re z}`.
5. Functional equation (copied identities from LGrowth) + steps 1–4 give the
   left-edge bound `‖L(z,χ)‖ ≤ 12(1+1/(−Re z))·(N(2+|Im z|))^{1/2−Re z}` on
   `−1/2 ≤ Re z < 0`.
6. Main Phragmén–Lindelöf on the strip `[−1/L, 1+1/L]`, `L := 1+log(N(|t|+3))`,
   with Gaussian and equalizer normalizers; the interpolation exponent is
   `(1−σ)/2 + O(1/L)` and `D^{1/L} ≤ 3` absorbs the correction.
-/
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Carmichael.LGrowth

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Carmichael

open Complex Finset Filter Set
open scoped Real Topology

/-! ### Elementary helpers -/

section Helpers

private lemma le_of_sq_le_sq' {A B : ℝ} (_hA : 0 ≤ A) (hB : 0 ≤ B) (h : A ^ 2 ≤ B ^ 2) :
    A ≤ B := by nlinarith

private lemma exp_one_le_three : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le

private lemma exp_four_le : Real.exp 4 ≤ 81 := by
  have h1 : Real.exp 1 ≤ 3 := exp_one_le_three
  have h0 : (0:ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  have h2 : Real.exp 1 * Real.exp 1 ≤ 9 := by nlinarith
  have h02 : (0:ℝ) ≤ Real.exp 1 * Real.exp 1 := by positivity
  have h4 : Real.exp 4 = Real.exp 1 * Real.exp 1 * (Real.exp 1 * Real.exp 1) := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  calc Real.exp 4 = Real.exp 1 * Real.exp 1 * (Real.exp 1 * Real.exp 1) := h4
    _ ≤ 9 * 9 := mul_le_mul h2 h2 h02 (by norm_num)
    _ = 81 := by norm_num

/-- `(1+|v|)·e^{−v²} ≤ 3`. -/
private lemma one_add_abs_mul_exp_neg_sq_le (v : ℝ) : (1 + |v|) * Real.exp (-v ^ 2) ≤ 3 := by
  have h1 : 1 + |v| ≤ Real.exp |v| := by
    have := Real.add_one_le_exp |v|; linarith
  have h2 : (1 + |v|) * Real.exp (-v ^ 2) ≤ Real.exp |v| * Real.exp (-v ^ 2) :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have h3 : Real.exp |v| * Real.exp (-v ^ 2) = Real.exp (|v| + -v ^ 2) := by
    rw [← Real.exp_add]
  have h4 : |v| + -v ^ 2 ≤ 1 := by
    nlinarith [sq_abs v, sq_nonneg (|v| - 1/2)]
  calc (1 + |v|) * Real.exp (-v ^ 2) ≤ Real.exp (|v| + -v ^ 2) := by rw [← h3]; exact h2
    _ ≤ Real.exp 1 := Real.exp_le_exp.mpr h4
    _ ≤ 3 := exp_one_le_three

/-- Modulus of the Gaussian normalizer. -/
private lemma norm_exp_sq_sub (z w : ℂ) :
    ‖Complex.exp ((z - w) ^ 2)‖ = Real.exp ((z.re - w.re) ^ 2 - (z.im - w.im) ^ 2) := by
  rw [Complex.norm_exp]
  congr 1
  rw [sq, Complex.mul_re, Complex.sub_re, Complex.sub_im]
  ring

/-- Modulus of the power normalizer. -/
private lemma norm_exp_mul_ofReal (u : ℂ) (c : ℝ) :
    ‖Complex.exp (u * (c : ℂ))‖ = Real.exp (u.re * c) := by
  rw [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]

/-- `2+|y| ≤ (2+|y₀|)·(1+|y−y₀|)`. -/
private lemma two_add_abs_le (y y₀ : ℝ) : 2 + |y| ≤ (2 + |y₀|) * (1 + |y - y₀|) := by
  have hy : y = y₀ + (y - y₀) := by ring
  have h1 : |y| ≤ |y₀| + |y - y₀| := by
    calc |y| = |y₀ + (y - y₀)| := by rw [← hy]
      _ ≤ |y₀| + |y - y₀| := abs_add_le _ _
  nlinarith [abs_nonneg y₀, abs_nonneg (y - y₀),
    mul_nonneg (abs_nonneg y₀) (abs_nonneg (y - y₀))]

end Helpers

/-! ### The Gauss sum modulus and the root number -/

section GaussModulus

variable {N : ℕ} [NeZero N]

private lemma conj_stdAddChar (x : ZMod N) :
    (starRingEnd ℂ) (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have h : ‖ZMod.stdAddChar (N := N) x‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj h]

omit [NeZero N] in
private lemma char_mul_conj_of_isUnit {χ : DirichletCharacter ℂ N} {x : ZMod N}
    (hx : IsUnit x) : χ x * (starRingEnd ℂ) (χ x) = 1 := by
  have h : ‖χ x‖ = 1 := by
    have := χ.unit_norm_eq_one hx.unit
    rwa [IsUnit.unit_spec] at this
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
  norm_num

private lemma sum_char_mul_conj_eq (χ : DirichletCharacter ℂ N) :
    ∑ x : ZMod N, χ⁻¹ x * (starRingEnd ℂ) (χ⁻¹ x)
      = ∑ x : ZMod N, χ x * (starRingEnd ℂ) (χ x) := by
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : IsUnit x
  · rw [char_mul_conj_of_isUnit hx, char_mul_conj_of_isUnit hx]
  · rw [MulChar.map_nonunit χ hx, MulChar.map_nonunit χ⁻¹ hx]

private lemma sum_char_mul_conj_ne_zero (χ : DirichletCharacter ℂ N) :
    ∑ x : ZMod N, χ x * (starRingEnd ℂ) (χ x) ≠ 0 := by
  have hre : ∀ x : ZMod N, χ x * (starRingEnd ℂ) (χ x) = ((‖χ x‖ ^ 2 : ℝ) : ℂ) := by
    intro x
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcast : ∑ x : ZMod N, χ x * (starRingEnd ℂ) (χ x)
      = ((∑ x : ZMod N, ‖χ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun x _ => hre x
  rw [hcast]
  have h1 : ‖χ (1 : ZMod N)‖ ^ 2 = 1 := by
    rw [map_one]
    norm_num
  have h2 : ‖χ (1 : ZMod N)‖ ^ 2 ≤ ∑ x : ZMod N, ‖χ x‖ ^ 2 :=
    Finset.single_le_sum (fun x _ => sq_nonneg ‖χ x‖) (Finset.mem_univ 1)
  rw [h1] at h2
  exact Complex.ofReal_ne_zero.mpr (by linarith)

/-- **Gauss sum modulus** for primitive characters: `g(χ)·conj(g(χ)) = N`. -/
lemma gaussSum_mul_conj {χ : DirichletCharacter ℂ N} (hχp : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar * (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar) = (N : ℂ) := by
  -- expansion of each shifted Gauss sum times its conjugate
  have hexpand : ∀ a : ZMod N,
      gaussSum χ (ZMod.stdAddChar.mulShift a) *
          (starRingEnd ℂ) (gaussSum χ (ZMod.stdAddChar.mulShift a))
        = ∑ x : ZMod N, ∑ y : ZMod N,
            χ x * (starRingEnd ℂ) (χ y) * ZMod.stdAddChar (a * (x - y)) := by
    intro a
    simp only [gaussSum]
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [AddChar.mulShift_apply]
    rw [map_mul (starRingEnd ℂ) (χ y) (ZMod.stdAddChar (a * y)), conj_stdAddChar]
    have he : ZMod.stdAddChar (a * x) * ZMod.stdAddChar (-(a * y))
        = ZMod.stdAddChar (a * (x - y)) := by
      rw [← AddChar.map_add_eq_mul]
      congr 1
      ring
    calc χ x * ZMod.stdAddChar (a * x) *
          ((starRingEnd ℂ) (χ y) * ZMod.stdAddChar (-(a * y)))
        = χ x * (starRingEnd ℂ) (χ y) *
            (ZMod.stdAddChar (a * x) * ZMod.stdAddChar (-(a * y))) := by ring
      _ = χ x * (starRingEnd ℂ) (χ y) * ZMod.stdAddChar (a * (x - y)) := by rw [he]
  -- orthogonality collapse
  have hway2 : ∑ a : ZMod N,
      gaussSum χ (ZMod.stdAddChar.mulShift a) *
          (starRingEnd ℂ) (gaussSum χ (ZMod.stdAddChar.mulShift a))
        = (N : ℂ) * ∑ x : ZMod N, χ x * (starRingEnd ℂ) (χ x) := by
    have horth : ∀ w : ZMod N,
        ∑ a : ZMod N, ZMod.stdAddChar (a * w) = if w = 0 then (N : ℂ) else 0 := by
      intro w
      have h := AddChar.sum_mulShift w (ZMod.isPrimitive_stdAddChar N)
      rw [ZMod.card] at h
      push_cast at h
      exact h
    have hswap : ∀ x : ZMod N,
        ∑ a : ZMod N, ∑ y : ZMod N,
            χ x * (starRingEnd ℂ) (χ y) * ZMod.stdAddChar (a * (x - y))
          = ∑ y : ZMod N, χ x * (starRingEnd ℂ) (χ y) *
              ∑ a : ZMod N, ZMod.stdAddChar (a * (x - y)) := by
      intro x
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun y _ => by rw [Finset.mul_sum]
    have hcollapse : ∀ x : ZMod N,
        ∑ y : ZMod N, χ x * (starRingEnd ℂ) (χ y) *
            (if x - y = 0 then (N : ℂ) else 0)
          = χ x * (starRingEnd ℂ) (χ x) * (N : ℂ) := by
      intro x
      rw [Finset.sum_eq_single x]
      · rw [if_pos (sub_self x)]
      · intro y _ hyx
        rw [if_neg (sub_ne_zero.mpr (Ne.symm hyx)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ x) h
    calc ∑ a : ZMod N,
        gaussSum χ (ZMod.stdAddChar.mulShift a) *
          (starRingEnd ℂ) (gaussSum χ (ZMod.stdAddChar.mulShift a))
        = ∑ a : ZMod N, ∑ x : ZMod N, ∑ y : ZMod N,
            χ x * (starRingEnd ℂ) (χ y) * ZMod.stdAddChar (a * (x - y)) :=
          Finset.sum_congr rfl fun a _ => hexpand a
      _ = ∑ x : ZMod N, ∑ a : ZMod N, ∑ y : ZMod N,
            χ x * (starRingEnd ℂ) (χ y) * ZMod.stdAddChar (a * (x - y)) :=
          Finset.sum_comm
      _ = ∑ x : ZMod N, ∑ y : ZMod N, χ x * (starRingEnd ℂ) (χ y) *
            ∑ a : ZMod N, ZMod.stdAddChar (a * (x - y)) :=
          Finset.sum_congr rfl fun x _ => hswap x
      _ = ∑ x : ZMod N, ∑ y : ZMod N, χ x * (starRingEnd ℂ) (χ y) *
            (if x - y = 0 then (N : ℂ) else 0) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
            rw [horth (x - y)]
      _ = ∑ x : ZMod N, χ x * (starRingEnd ℂ) (χ x) * (N : ℂ) :=
          Finset.sum_congr rfl fun x _ => hcollapse x
      _ = (N : ℂ) * ∑ x : ZMod N, χ x * (starRingEnd ℂ) (χ x) := by
          rw [← Finset.sum_mul]
          ring
  -- evaluation via primitivity
  have hway1 : ∑ a : ZMod N,
      gaussSum χ (ZMod.stdAddChar.mulShift a) *
          (starRingEnd ℂ) (gaussSum χ (ZMod.stdAddChar.mulShift a))
        = (∑ a : ZMod N, χ⁻¹ a * (starRingEnd ℂ) (χ⁻¹ a)) *
            (gaussSum χ ZMod.stdAddChar * (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχp a, map_mul]
    ring
  have hkey : (∑ x : ZMod N, χ x * (starRingEnd ℂ) (χ x)) *
      (gaussSum χ ZMod.stdAddChar * (starRingEnd ℂ) (gaussSum χ ZMod.stdAddChar))
      = (∑ x : ZMod N, χ x * (starRingEnd ℂ) (χ x)) * (N : ℂ) := by
    rw [← sum_char_mul_conj_eq χ, ← hway1, hway2, sum_char_mul_conj_eq χ]
    ring
  exact mul_left_cancel₀ (sum_char_mul_conj_ne_zero χ) hkey

/-- `‖g(χ)‖² = N` for primitive `χ`. -/
lemma norm_gaussSum_sq {χ : DirichletCharacter ℂ N} (hχp : χ.IsPrimitive) :
    ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = (N : ℝ) := by
  have h := gaussSum_mul_conj hχp
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

/-- **Root number modulus 1** for primitive characters. -/
lemma norm_rootNumber_eq_one {χ : DirichletCharacter ℂ N} (hχp : χ.IsPrimitive) :
    ‖DirichletCharacter.rootNumber χ‖ = 1 := by
  classical
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hg : ‖gaussSum χ ZMod.stdAddChar‖ = (N : ℝ) ^ ((1:ℝ)/2) := by
    have hsq : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = ((N:ℝ) ^ ((1:ℝ)/2)) ^ 2 := by
      rw [norm_gaussSum_sq hχp]
      rw [← Real.rpow_natCast ((N:ℝ) ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hNpos.le]
      norm_num
    have h1 : (0:ℝ) ≤ (N:ℝ) ^ ((1:ℝ)/2) := Real.rpow_nonneg hNpos.le _
    exact le_antisymm (le_of_sq_le_sq' (norm_nonneg _) h1 hsq.le)
      (le_of_sq_le_sq' h1 (norm_nonneg _) hsq.ge)
  rw [DirichletCharacter.rootNumber, norm_div, norm_div]
  have hI : ‖(I : ℂ) ^ (if χ.Even then 0 else 1)‖ = 1 := by
    rw [norm_pow, Complex.norm_I, one_pow]
  have hNhalf : ‖((N : ℂ)) ^ ((1:ℂ)/2)‖ = (N:ℝ) ^ ((1:ℝ)/2) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    norm_num
  have hpos : (0:ℝ) < (N:ℝ) ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hNpos _
  rw [hI, div_one, hNhalf, hg, div_self hpos.ne']

end GaussModulus

/-! ### Right-edge bound: the Dirichlet series on `Re z > 1` -/

section RightEdge

variable {N : ℕ} [NeZero N]

/-- Termwise Dirichlet-series bound: `‖L(z,χ)‖ ≤ 1 + 1/(Re z − 1)` on `Re z > 1`
(any Dirichlet character). -/
lemma norm_LFunction_le_of_one_lt_re (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : 1 < z.re) :
    ‖DirichletCharacter.LFunction χ z‖ ≤ 1 + 1 / (z.re - 1) := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hz]
  have hbound : ∀ n : ℕ, ‖LSeries.term (χ ·) z n‖ ≤ (n : ℝ) ^ (-z.re) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [LSeries.term_zero, norm_zero, Nat.cast_zero,
        Real.zero_rpow (ne_of_lt (by linarith : -z.re < 0))]
    · rw [LSeries.term_of_ne_zero (Nat.pos_iff_ne_zero.mp hn), norm_div]
      have hn0 : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hnorm : ‖((n : ℕ) : ℂ) ^ z‖ = (n : ℝ) ^ z.re := by
        rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hn0]
      rw [hnorm, Real.rpow_neg hn0.le, div_eq_mul_inv]
      have h1 := χ.norm_le_one ((n : ℕ) : ZMod N)
      have h2 : (0:ℝ) ≤ ((n : ℝ) ^ z.re)⁻¹ := by positivity
      calc ‖χ ((n : ℕ) : ZMod N)‖ * ((n : ℝ) ^ z.re)⁻¹
          ≤ 1 * ((n : ℝ) ^ z.re)⁻¹ := mul_le_mul_of_nonneg_right h1 h2
        _ = ((n : ℝ) ^ z.re)⁻¹ := one_mul _
  have hmaj : Summable (fun n : ℕ => (n : ℝ) ^ (-z.re)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hsumnorm : Summable fun n : ℕ => ‖LSeries.term (χ ·) z n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hmaj
  have htsum : ∑' n : ℕ, (n : ℝ) ^ (-z.re) ≤ 1 + 1 / (z.re - 1) := by
    apply Real.tsum_le_of_sum_range_le (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    intro K
    have h := sum_range_rpow_le (σ := z.re - 1) (by linarith) K
    calc ∑ k ∈ range K, (k : ℝ) ^ (-z.re)
        = ∑ k ∈ range K, (k : ℝ) ^ (-(z.re - 1) - 1) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          congr 1
          ring
      _ ≤ 1 + 1 / (z.re - 1) := h
  calc ‖LSeries (χ ·) z‖ ≤ ∑' n, ‖LSeries.term (χ ·) z n‖ := norm_tsum_le_tsum_norm hsumnorm
    _ ≤ ∑' n : ℕ, (n : ℝ) ^ (-z.re) := hsumnorm.tsum_le_tsum hbound hmaj
    _ ≤ 1 + 1 / (z.re - 1) := htsum

end RightEdge

/-! ### Exact Γ-modulus on `Re = 1` and the line-zero bound -/

section GammaLineOne

/-- Exact modulus of Γ on the line `Re = 1`: `‖Γ(1+iv)‖² = πv/sinh(πv)` for `v ≠ 0`. -/
lemma norm_Gamma_sq_of_re_one {v : ℝ} (hv : v ≠ 0) :
    ‖Complex.Gamma (1 + (v : ℂ) * I)‖ ^ 2 = π * v / Real.sinh (π * v) := by
  have hvC : (v : ℂ) * I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hv) Complex.I_ne_zero
  have hconj : (starRingEnd ℂ) (1 + (v : ℂ) * I) = 1 - (v : ℂ) * I := by
    rw [map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hmul : Complex.Gamma (1 + (v : ℂ) * I) *
      (starRingEnd ℂ) (Complex.Gamma (1 + (v : ℂ) * I))
      = ((‖Complex.Gamma (1 + (v : ℂ) * I)‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hGconj : (starRingEnd ℂ) (Complex.Gamma (1 + (v : ℂ) * I))
      = Complex.Gamma (1 - (v : ℂ) * I) := by
    rw [← Complex.Gamma_conj, hconj]
  have hΓ1 : Complex.Gamma (1 + (v : ℂ) * I)
      = ((v : ℂ) * I) * Complex.Gamma ((v : ℂ) * I) := by
    rw [show (1 : ℂ) + (v : ℂ) * I = ((v : ℂ) * I) + 1 from by ring,
      Complex.Gamma_add_one _ hvC]
  have hrefl : Complex.Gamma ((v : ℂ) * I) * Complex.Gamma (1 - (v : ℂ) * I)
      = ↑π / Complex.sin (↑π * ((v : ℂ) * I)) := Complex.Gamma_mul_Gamma_one_sub _
  have hsin : Complex.sin (↑π * ((v : ℂ) * I)) = ((Real.sinh (π * v) : ℝ) : ℂ) * I := by
    rw [show ↑π * ((v : ℂ) * I) = ((π * v : ℝ) : ℂ) * I from by push_cast; ring,
      Complex.sin_mul_I, ← Complex.ofReal_sinh]
  have hsinh0 : Real.sinh (π * v) ≠ 0 := by
    intro h
    have h2 : π * v = 0 := Real.sinh_eq_zero.mp h
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact Real.pi_ne_zero h3
    · exact hv h3
  have hchain : ((‖Complex.Gamma (1 + (v : ℂ) * I)‖ ^ 2 : ℝ) : ℂ)
      = ((π * v / Real.sinh (π * v) : ℝ) : ℂ) := by
    rw [← hmul, hGconj, hΓ1, mul_assoc, hrefl, hsin]
    have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hs : ((Real.sinh (π * v) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hsinh0
    push_cast
    field_simp
  exact_mod_cast hchain

/-- Recreated (private in LGrowth): `‖sin(π(z+a)/2)‖ ≤ e^{π|Im z|/2}`. -/
private lemma norm_sin_pi_shift_le (a : ℝ) (z : ℂ) :
    ‖Complex.sin (↑π * (z + ↑a) / 2)‖ ≤ Real.exp (π * |z.im| / 2) := by
  refine (norm_sin_le_exp _).trans (le_of_eq ?_)
  congr 1
  have h2 : ↑π * (z + ↑a) / 2 = ↑(π / 2) * (z + ↑a) := by push_cast; ring
  rw [h2, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
    Complex.ofReal_im, add_zero, zero_mul, add_zero]
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < π / 2)]
  ring

/-- Line-zero bound with the *square-root* growth: on `Re z = 0`,
`‖Γ(1−z)·sin(π(z+a)/2)‖ ≤ 3·(2+|Im z|)^{1/2}`. -/
lemma norm_Gamma_one_sub_mul_sin_line_zero (a : ℝ) {z : ℂ} (hz : z.re = 0) :
    ‖Complex.Gamma (1 - z) * Complex.sin (↑π * (z + ↑a) / 2)‖
      ≤ 3 * (2 + |z.im|) ^ ((1:ℝ)/2) := by
  have hy0 : (0:ℝ) ≤ |z.im| := abs_nonneg _
  have hrpow1 : (1:ℝ) ≤ (2 + |z.im|) ^ ((1:ℝ)/2) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  have hrpow0 : (0:ℝ) ≤ (2 + |z.im|) ^ ((1:ℝ)/2) := by linarith
  rcases eq_or_ne z.im 0 with hy | hy
  · -- `z = 0`: Γ(1) = 1 and `‖sin‖ ≤ 1`
    have h1z : (1 : ℂ) - z = 1 := by
      apply Complex.ext
      · simp [hz]
      · simp [hy]
    rw [h1z, Complex.Gamma_one, one_mul]
    calc ‖Complex.sin (↑π * (z + ↑a) / 2)‖ ≤ Real.exp (π * |z.im| / 2) :=
          norm_sin_pi_shift_le a z
      _ = 1 := by rw [hy]; simp
      _ ≤ 3 * (2 + |z.im|) ^ ((1:ℝ)/2) := by nlinarith
  · -- `z.im ≠ 0`: exact modulus
    have h1z : (1 : ℂ) - z = 1 + ((-z.im : ℝ) : ℂ) * I := by
      apply Complex.ext
      · simp [hz]
      · simp
    have hΓsq : ‖Complex.Gamma (1 - z)‖ ^ 2 = π * z.im / Real.sinh (π * z.im) := by
      rw [h1z, norm_Gamma_sq_of_re_one (neg_ne_zero.mpr hy)]
      rw [mul_neg, Real.sinh_neg, neg_div_neg_eq]
    have hu0 : 0 < |z.im| := abs_pos.mpr hy
    have huval : π * z.im / Real.sinh (π * z.im) = π * |z.im| / Real.sinh (π * |z.im|) := by
      rcases abs_cases z.im with ⟨h1, _⟩ | ⟨h1, _⟩
      · rw [h1]
      · rw [h1, mul_neg, Real.sinh_neg, neg_div_neg_eq]
    -- key inequality: `X·e^X ≤ (1+2X)·sinh X` for `X = π|z.im| > 0`
    have hkey : π * |z.im| * Real.exp (π * |z.im|)
        ≤ (1 + 2 * (π * |z.im|)) * Real.sinh (π * |z.im|) := by
      set X : ℝ := π * |z.im| with hX
      have hX0 : 0 < X := by positivity
      set A : ℝ := Real.exp X with hA
      have hA0 : 0 < A := Real.exp_pos X
      have hE : 1 + 2 * X ≤ A * A := by
        have h1 : 1 + 2 * X ≤ Real.exp (2 * X) := by
          have := Real.add_one_le_exp (2 * X); linarith
        have h2 : Real.exp (2 * X) = A * A := by
          rw [hA, ← Real.exp_add]; congr 1; ring
        rw [h2] at h1
        exact h1
      have hgoal2 : 2 * X * (A * A) ≤ (1 + 2 * X) * (A * A - 1) := by nlinarith
      have hsinh' : Real.sinh X = (A * A - 1) / (2 * A) := by
        rw [Real.sinh_eq, Real.exp_neg, ← hA]
        field_simp
      rw [hsinh']
      rw [show X * A = (2 * X * (A * A)) / (2 * A) from by field_simp]
      calc (2 * X * (A * A)) / (2 * A) ≤ ((1 + 2 * X) * (A * A - 1)) / (2 * A) := by
            gcongr
      _ = (1 + 2 * X) * ((A * A - 1) / (2 * A)) := by ring
    have hsinh0 : 0 < Real.sinh (π * |z.im|) := by
      rw [Real.sinh_pos_iff]
      positivity
    have hsin := norm_sin_pi_shift_le a z
    have hsin2 : ‖Complex.sin (↑π * (z + ↑a) / 2)‖ ^ 2 ≤ Real.exp (π * |z.im|) := by
      have h2 : Real.exp (π * |z.im| / 2) ^ 2 = Real.exp (π * |z.im|) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      nlinarith [norm_nonneg (Complex.sin (↑π * (z + ↑a) / 2)),
        Real.exp_pos (π * |z.im| / 2)]
    have hsq : (‖Complex.Gamma (1 - z)‖ * ‖Complex.sin (↑π * (z + ↑a) / 2)‖) ^ 2
        ≤ 1 + 2 * (π * |z.im|) := by
      rw [mul_pow, hΓsq, huval]
      have h1 : π * |z.im| / Real.sinh (π * |z.im|) *
          ‖Complex.sin (↑π * (z + ↑a) / 2)‖ ^ 2
          ≤ π * |z.im| / Real.sinh (π * |z.im|) * Real.exp (π * |z.im|) :=
        mul_le_mul_of_nonneg_left hsin2 (by positivity)
      have h2 : π * |z.im| / Real.sinh (π * |z.im|) * Real.exp (π * |z.im|)
          ≤ 1 + 2 * (π * |z.im|) := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hsinh0]
        linarith [hkey]
      linarith
    have hfin : (3 * (2 + |z.im|) ^ ((1:ℝ)/2)) ^ 2 = 9 * (2 + |z.im|) := by
      rw [mul_pow]
      have h1 : ((2 + |z.im|) ^ ((1:ℝ)/2)) ^ 2 = 2 + |z.im| := by
        rw [← Real.rpow_natCast ((2 + |z.im|) ^ ((1:ℝ)/2)) 2,
          ← Real.rpow_mul (by linarith : (0:ℝ) ≤ 2 + |z.im|)]
        norm_num
      rw [h1]
      norm_num
    have hle : 1 + 2 * (π * |z.im|) ≤ 9 * (2 + |z.im|) := by
      nlinarith [Real.pi_le_four, hu0]
    rw [norm_mul]
    apply le_of_sq_le_sq' (by positivity) (by positivity)
    calc (‖Complex.Gamma (1 - z)‖ * ‖Complex.sin (↑π * (z + ↑a) / 2)‖) ^ 2
        ≤ 1 + 2 * (π * |z.im|) := hsq
      _ ≤ 9 * (2 + |z.im|) := hle
      _ = (3 * (2 + |z.im|) ^ ((1:ℝ)/2)) ^ 2 := hfin.symm

end GammaLineOne

/-! ### The Phragmén–Lindelöf growth condition helper -/

section Growth

/-- Cubic-in-`|Im|` bounds satisfy the double-exponential Phragmén–Lindelöf
growth condition (with `c = 1`). -/
private lemma isBigO_double_exp {P : ℝ} (hP : 1 ≤ P) {f : ℂ → ℂ} {S : Set ℂ}
    (hf : ∀ z ∈ S, ‖f z‖ ≤ P * (4 + |z.im|) ^ 3) :
    f =O[comap (_root_.abs ∘ Complex.im) atTop ⊓ 𝓟 S]
      (fun z : ℂ => Real.exp ((Real.log P + 12) * Real.exp |z.im|)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨1, ?_⟩
  rw [Filter.eventually_inf_principal]
  apply Filter.Eventually.of_forall
  intro z hz
  rw [one_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine (hf z hz).trans ?_
  have hu0 : (0:ℝ) ≤ |z.im| := abs_nonneg _
  have hP0 : (0:ℝ) < P := by linarith
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg hP
  have h4u : (0:ℝ) < 4 + |z.im| := by linarith
  have hlog : Real.log (4 + |z.im|) ≤ 3 + |z.im| := by
    have := Real.log_le_sub_one_of_pos h4u
    linarith
  have hexpu : 1 ≤ Real.exp |z.im| := Real.one_le_exp hu0
  have huexp : |z.im| ≤ Real.exp |z.im| := by
    have := Real.add_one_le_exp |z.im|
    linarith
  have heq : P * (4 + |z.im|) ^ 3
      = Real.exp (Real.log P + 3 * Real.log (4 + |z.im|)) := by
    rw [Real.exp_add, Real.exp_log hP0]
    congr 1
    rw [show (3:ℝ) * Real.log (4 + |z.im|) = ((3:ℕ) : ℝ) * Real.log (4 + |z.im|) from
      by norm_num, ← Real.log_pow, Real.exp_log (by positivity)]
  rw [heq]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hlogP (sub_nonneg.mpr hexpu)]

end Growth

/-! ### The interpolated Γ-factor bound on the strip `[−1/2, 0]` -/

section GammaInterp

/-- **Interpolated Γ-factor bound**: on `−1/2 ≤ Re w ≤ 0`,
`‖Γ(1−w)·sin(π(w+a)/2)‖ ≤ 34·(2+|Im w|)^{1/2−Re w}` for every real shift `a`.
Phragmén–Lindelöf between the LGrowth strip bound (exponent 1 on `Re = −1/2`)
and the exact-modulus line-zero bound (exponent 1/2 on `Re = 0`), with a
Gaussian normalizer to localize and a power normalizer to equalize. -/
lemma norm_Gamma_one_sub_mul_sin_interp (a : ℝ) {w : ℂ}
    (h1 : -(1/2 : ℝ) ≤ w.re) (h2 : w.re ≤ 0) :
    ‖Complex.Gamma (1 - w) * Complex.sin (↑π * (w + ↑a) / 2)‖
      ≤ 34 * (2 + |w.im|) ^ ((1:ℝ)/2 - w.re) := by
  set q : ℝ := 2 + |w.im| with hqdef
  have hq2 : (2:ℝ) ≤ q := by
    rw [hqdef]
    linarith [abs_nonneg w.im]
  have hq0 : (0:ℝ) < q := by linarith
  have hq1 : (1:ℝ) ≤ q := by linarith
  have hlogq : (0:ℝ) ≤ Real.log q := Real.log_nonneg hq1
  have hqq : q * q ^ (-(1/2 : ℝ)) = q ^ ((1:ℝ)/2) := by
    nth_rewrite 1 [← Real.rpow_one q]
    rw [← Real.rpow_add hq0]
    norm_num
  set G : ℂ → ℂ := fun z => Complex.Gamma (1 - z) * Complex.sin (↑π * (z + ↑a) / 2) *
    (Complex.exp ((z - w) ^ 2) * Complex.exp (z * (Real.log q : ℂ))) with hG
  have hnormG : ∀ z : ℂ, ‖G z‖
      = ‖Complex.Gamma (1 - z) * Complex.sin (↑π * (z + ↑a) / 2)‖ *
        (Real.exp ((z.re - w.re) ^ 2 - (z.im - w.im) ^ 2) *
          Real.exp (z.re * Real.log q)) := by
    intro z
    rw [hG]
    simp only []
    rw [norm_mul,
      norm_mul (Complex.exp ((z - w) ^ 2)) (Complex.exp (z * (Real.log q : ℂ))),
      norm_exp_sq_sub, norm_exp_mul_ofReal]
  -- Gaussian factor bound, used on both boundary lines and in the interior
  have hgaussE : ∀ x y : ℝ, (x - w.re) ^ 2 ≤ 1 →
      Real.exp ((x - w.re) ^ 2 - (y - w.im) ^ 2)
        ≤ 3 * Real.exp (-(y - w.im) ^ 2) := by
    intro x y hre
    rw [show (x - w.re) ^ 2 - (y - w.im) ^ 2
        = (x - w.re) ^ 2 + -(y - w.im) ^ 2 from by ring, Real.exp_add]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc Real.exp ((x - w.re) ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr hre
      _ ≤ 3 := exp_one_le_three
  have main : ‖G w‖ ≤ 34 * q ^ ((1:ℝ)/2) := by
    apply PhragmenLindelof.vertical_strip (a := -(1/2 : ℝ)) (b := (0:ℝ))
      (C := 34 * q ^ ((1:ℝ)/2))
    -- differentiability
    · have hdiff : DifferentiableOn ℂ G {z : ℂ | z.re < 1} := by
        intro z hz
        have hz1 : z.re < 1 := hz
        have hΓ : DifferentiableAt ℂ (fun x : ℂ => Complex.Gamma (1 - x)) z := by
          have hne : ∀ m : ℕ, 1 - z ≠ -m := by
            intro m h
            have := congrArg Complex.re h
            simp at this
            have hm : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
            linarith
          exact (Complex.differentiableAt_Gamma _ hne).comp z (by fun_prop)
        have hsin : DifferentiableAt ℂ (fun x : ℂ => Complex.sin (↑π * (x + ↑a) / 2)) z := by
          apply Complex.differentiable_sin.differentiableAt.comp
          fun_prop
        have hexp1 : DifferentiableAt ℂ (fun x : ℂ => Complex.exp ((x - w) ^ 2)) z := by
          apply Complex.differentiable_exp.differentiableAt.comp
          fun_prop
        have hexp2 : DifferentiableAt ℂ
            (fun x : ℂ => Complex.exp (x * (Real.log q : ℂ))) z := by
          apply Complex.differentiable_exp.differentiableAt.comp
          fun_prop
        exact ((hΓ.mul hsin).mul (hexp1.mul hexp2)).differentiableWithinAt
      apply DifferentiableOn.diffContOnCl
      refine hdiff.mono ?_
      have hsub : closure (Complex.re ⁻¹' (Set.Ioo (-(1/2:ℝ)) 0))
          ⊆ Complex.re ⁻¹' (Set.Icc (-(1/2:ℝ)) 0) :=
        closure_minimal (Set.preimage_mono Set.Ioo_subset_Icc_self)
          (isClosed_Icc.preimage Complex.continuous_re)
      refine hsub.trans ?_
      intro z hz
      have := hz.2
      show z.re < 1
      linarith
    -- growth condition
    · refine ⟨1, ?_, Real.log 9 + 12, ?_⟩
      · rw [show (0:ℝ) - -(1/2) = 1/2 from by norm_num, lt_div_iff₀ (by norm_num : (0:ℝ) < 1/2)]
        nlinarith [Real.pi_gt_three]
      · have hb : ∀ z ∈ Complex.re ⁻¹' (Set.Ioo (-(1/2:ℝ)) 0),
            ‖G z‖ ≤ 9 * (4 + |z.im|) ^ 3 := by
          intro z hz
          have hz1 : -(1/2:ℝ) < z.re := hz.1
          have hz2 : z.re < 0 := hz.2
          rw [hnormG z]
          have hF : ‖Complex.Gamma (1 - z) * Complex.sin (↑π * (z + ↑a) / 2)‖
              ≤ 3 * (2 + ‖z‖) := norm_Gamma_one_sub_mul_sin_le a hz1.le (by linarith)
          have hE1 : Real.exp ((z.re - w.re) ^ 2 - (z.im - w.im) ^ 2) ≤ 3 := by
            calc Real.exp ((z.re - w.re) ^ 2 - (z.im - w.im) ^ 2) ≤ Real.exp 1 := by
                  apply Real.exp_le_exp.mpr
                  nlinarith [sq_nonneg (z.im - w.im)]
              _ ≤ 3 := exp_one_le_three
          have hE2 : Real.exp (z.re * Real.log q) ≤ 1 := by
            rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
            apply Real.exp_le_exp.mpr
            exact mul_nonpos_iff.mpr (Or.inr ⟨hz2.le, hlogq⟩)
          have hzn : 2 + ‖z‖ ≤ 4 + |z.im| := by
            have h := Complex.norm_le_abs_re_add_abs_im z
            have h2 : |z.re| ≤ 2 := by
              rw [abs_le]
              constructor <;> linarith
            linarith
          have hcube : (4:ℝ) + |z.im| ≤ (4 + |z.im|) ^ 3 := by
            have h1 : (1:ℝ) ≤ 4 + |z.im| := by linarith [abs_nonneg z.im]
            calc (4:ℝ) + |z.im| = (4 + |z.im|) ^ 1 := (pow_one _).symm
              _ ≤ (4 + |z.im|) ^ 3 := pow_le_pow_right₀ h1 (by norm_num)
          calc ‖Complex.Gamma (1 - z) * Complex.sin (↑π * (z + ↑a) / 2)‖ *
              (Real.exp ((z.re - w.re) ^ 2 - (z.im - w.im) ^ 2) *
                Real.exp (z.re * Real.log q))
              ≤ (3 * (2 + ‖z‖)) * (3 * 1) := by
                apply mul_le_mul hF _ (by positivity) (by positivity)
                exact mul_le_mul hE1 hE2 (Real.exp_pos _).le (by norm_num)
            _ = 9 * (2 + ‖z‖) := by ring
            _ ≤ 9 * (4 + |z.im|) := by linarith
            _ ≤ 9 * (4 + |z.im|) ^ 3 := by linarith
        simpa only [one_mul] using isBigO_double_exp (by norm_num : (1:ℝ) ≤ 9) hb
    -- boundary line `Re z = −1/2`
    · intro z hz
      rw [hnormG z, hz]
      have hpow : Real.exp (-(1/2) * Real.log q) = q ^ (-(1/2 : ℝ)) := by
        rw [Real.rpow_def_of_pos hq0, mul_comm]
      rw [hpow]
      have hF : ‖Complex.Gamma (1 - z) * Complex.sin (↑π * (z + ↑a) / 2)‖
          ≤ (15/4) * (q * (1 + |z.im - w.im|)) := by
        have hFs := norm_Gamma_one_sub_mul_sin_le a hz.symm.le
          (by rw [hz]; norm_num : z.re ≤ 1/2)
        have hzn : ‖z‖ ≤ 1/2 + |z.im| := by
          have h := Complex.norm_le_abs_re_add_abs_im z
          rw [hz] at h
          have h2 : |(-(1/2) : ℝ)| = 1/2 := by norm_num
          rw [h2] at h
          exact h
        calc ‖Complex.Gamma (1 - z) * Complex.sin (↑π * (z + ↑a) / 2)‖
            ≤ 3 * (2 + ‖z‖) := hFs
          _ ≤ 3 * (2 + (1/2 + |z.im|)) := by linarith
          _ ≤ (15/4) * (2 + |z.im|) := by nlinarith [abs_nonneg z.im]
          _ ≤ (15/4) * (q * (1 + |z.im - w.im|)) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              rw [hqdef]
              exact two_add_abs_le z.im w.im
      have hE1 : Real.exp ((-(1/2) - w.re) ^ 2 - (z.im - w.im) ^ 2)
          ≤ 3 * Real.exp (-(z.im - w.im) ^ 2) :=
        hgaussE (-(1/2)) z.im (by nlinarith)
      calc ‖Complex.Gamma (1 - z) * Complex.sin (↑π * (z + ↑a) / 2)‖ *
          (Real.exp ((-(1/2) - w.re) ^ 2 - (z.im - w.im) ^ 2) * q ^ (-(1/2 : ℝ)))
          ≤ ((15/4) * (q * (1 + |z.im - w.im|))) *
              ((3 * Real.exp (-(z.im - w.im) ^ 2)) * q ^ (-(1/2 : ℝ))) := by
            apply mul_le_mul hF _ (by positivity) (by positivity)
            exact mul_le_mul_of_nonneg_right hE1 (Real.rpow_nonneg hq0.le _)
        _ = (45/4) * ((1 + |z.im - w.im|) * Real.exp (-(z.im - w.im) ^ 2)) *
              (q * q ^ (-(1/2 : ℝ))) := by ring
        _ ≤ (45/4) * 3 * (q * q ^ (-(1/2 : ℝ))) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left (one_add_abs_mul_exp_neg_sq_le _) (by norm_num)
        _ = (135/4) * q ^ ((1:ℝ)/2) := by rw [hqq]; ring
        _ ≤ 34 * q ^ ((1:ℝ)/2) := by
            apply mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hq0.le _)
    -- boundary line `Re z = 0`
    · intro z hz
      rw [hnormG z, hz, zero_mul, Real.exp_zero, mul_one]
      have hF := norm_Gamma_one_sub_mul_sin_line_zero a hz
      have hchain : (2 + |z.im|) ^ ((1:ℝ)/2)
          ≤ q ^ ((1:ℝ)/2) * (1 + |z.im - w.im|) := by
        calc (2 + |z.im|) ^ ((1:ℝ)/2)
            ≤ (q * (1 + |z.im - w.im|)) ^ ((1:ℝ)/2) := by
              apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
              rw [hqdef]
              exact two_add_abs_le z.im w.im
          _ = q ^ ((1:ℝ)/2) * (1 + |z.im - w.im|) ^ ((1:ℝ)/2) :=
              Real.mul_rpow hq0.le (by positivity)
          _ ≤ q ^ ((1:ℝ)/2) * (1 + |z.im - w.im|) := by
              have h1v : (1:ℝ) ≤ 1 + |z.im - w.im| := by linarith [abs_nonneg (z.im - w.im)]
              have h2v : (1 + |z.im - w.im|) ^ ((1:ℝ)/2) ≤ (1 + |z.im - w.im|) ^ (1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_le h1v (by norm_num)
              rw [Real.rpow_one] at h2v
              exact mul_le_mul_of_nonneg_left h2v (Real.rpow_nonneg hq0.le _)
      have hE1 : Real.exp ((0 - w.re) ^ 2 - (z.im - w.im) ^ 2)
          ≤ 3 * Real.exp (-(z.im - w.im) ^ 2) :=
        hgaussE 0 z.im (by nlinarith)
      calc ‖Complex.Gamma (1 - z) * Complex.sin (↑π * (z + ↑a) / 2)‖ *
          Real.exp ((0 - w.re) ^ 2 - (z.im - w.im) ^ 2)
          ≤ (3 * (q ^ ((1:ℝ)/2) * (1 + |z.im - w.im|))) *
              (3 * Real.exp (-(z.im - w.im) ^ 2)) := by
            apply mul_le_mul _ hE1 (Real.exp_pos _).le (by positivity)
            exact hF.trans (mul_le_mul_of_nonneg_left hchain (by norm_num))
        _ = 9 * q ^ ((1:ℝ)/2) *
              ((1 + |z.im - w.im|) * Real.exp (-(z.im - w.im) ^ 2)) := by ring
        _ ≤ 9 * q ^ ((1:ℝ)/2) * 3 := by
            apply mul_le_mul_of_nonneg_left (one_add_abs_mul_exp_neg_sq_le _) (by positivity)
        _ = 27 * q ^ ((1:ℝ)/2) := by ring
        _ ≤ 34 * q ^ ((1:ℝ)/2) := by
            apply mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hq0.le _)
    · exact h1
    · exact h2
  -- unfold `G` at `w`
  have hqw : Real.exp (w.re * Real.log q) = q ^ w.re := by
    rw [Real.rpow_def_of_pos hq0, mul_comm]
  have hGw : ‖G w‖ = ‖Complex.Gamma (1 - w) * Complex.sin (↑π * (w + ↑a) / 2)‖ *
      q ^ w.re := by
    rw [hnormG w, show (w.re - w.re) ^ 2 - (w.im - w.im) ^ 2 = 0 from by ring,
      Real.exp_zero, one_mul, hqw]
  rw [hGw] at main
  have hqw0 : (0:ℝ) < q ^ w.re := Real.rpow_pos_of_pos hq0 _
  have hle : ‖Complex.Gamma (1 - w) * Complex.sin (↑π * (w + ↑a) / 2)‖ * q ^ w.re
      ≤ (34 * (2 + |w.im|) ^ ((1:ℝ)/2 - w.re)) * q ^ w.re := by
    rw [mul_assoc, ← hqdef, ← Real.rpow_add hq0,
      show (1:ℝ)/2 - w.re + w.re = 1/2 from by ring]
    exact main
  exact le_of_mul_le_mul_right hle hqw0

end GammaInterp

/-! ### The left-edge bound via the functional equation -/

section LeftEdge

variable {N : ℕ} [NeZero N]

/-- Deligne-factor version of the interpolated bound. -/
private lemma norm_GammaC_mul_trig_interp {z : ℂ} (h1 : -(1/2 : ℝ) ≤ z.re) (h2 : z.re ≤ 0)
    {T : ℂ} (hT : T = Complex.sin (↑π * z / 2) ∨ T = Complex.cos (↑π * z / 2)) :
    ‖Complex.Gammaℂ (1 - z) * T‖ ≤ 12 * (2 + |z.im|) ^ ((1:ℝ)/2 - z.re) := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  have hrp : (0:ℝ) ≤ (2 + |z.im|) ^ ((1:ℝ)/2 - z.re) :=
    Real.rpow_nonneg (by positivity) _
  have hstrip : ‖Complex.Gamma (1 - z) * T‖ ≤ 34 * (2 + |z.im|) ^ ((1:ℝ)/2 - z.re) := by
    rcases hT with rfl | rfl
    · have h := norm_Gamma_one_sub_mul_sin_interp 0 h1 h2
      rw [show ((0:ℝ) : ℂ) = 0 from by norm_num, add_zero] at h
      exact h
    · have h := norm_Gamma_one_sub_mul_sin_interp 1 h1 h2
      rw [show ↑π * (z + ((1:ℝ) : ℂ)) / 2 = ↑π/2 - -(↑π * z / 2) from by push_cast; ring,
        Complex.sin_pi_div_two_sub, Complex.cos_neg] at h
      exact h
  have hpow : ‖((2:ℂ) * ↑π) ^ (-(1 - z))‖ ≤ (2*π)⁻¹ := by
    rw [show ((2:ℂ) * ↑π) = (((2 * π : ℝ)) : ℂ) from by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    have h2π : (1:ℝ) ≤ 2*π := by nlinarith [Real.two_le_pi]
    have hre : (-(1-z)).re ≤ -1 := by
      simp only [Complex.neg_re, Complex.sub_re, Complex.one_re]
      linarith
    calc (2*π) ^ (-(1-z)).re ≤ (2*π) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h2π hre
      _ = (2*π)⁻¹ := Real.rpow_neg_one _
  have hexpand : Complex.Gammaℂ (1 - z) * T
      = 2 * (((2:ℂ) * ↑π) ^ (-(1 - z))) * (Complex.Gamma (1 - z) * T) := by
    rw [Complex.Gammaℂ_def]
    ring
  rw [hexpand, norm_mul, norm_mul, show ‖(2:ℂ)‖ = 2 from by norm_num]
  calc 2 * ‖((2:ℂ) * ↑π) ^ (-(1 - z))‖ * ‖Complex.Gamma (1 - z) * T‖
      ≤ 2 * (2*π)⁻¹ * (34 * (2 + |z.im|) ^ ((1:ℝ)/2 - z.re)) := by
        apply mul_le_mul _ hstrip (norm_nonneg _) (by positivity)
        exact mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = (34/π) * (2 + |z.im|) ^ ((1:ℝ)/2 - z.re) := by
        field_simp
    _ ≤ 12 * (2 + |z.im|) ^ ((1:ℝ)/2 - z.re) := by
        apply mul_le_mul_of_nonneg_right _ hrp
        rw [div_le_iff₀ hπ]
        nlinarith [Real.pi_gt_three]

-- Functional-equation identities, recreated from LGrowth (private there).

omit [NeZero N] in
private lemma inv_mul_neg_one (χ : DirichletCharacter ℂ N) :
    χ (-1) * χ⁻¹ (-1) = 1 := by
  have h : (χ * χ⁻¹) (-1) = 1 := by
    rw [mul_inv_cancel]
    exact MulChar.one_apply isUnit_one.neg
  rwa [MulChar.mul_apply] at h

omit [NeZero N] in
private lemma even_inv {χ : DirichletCharacter ℂ N} (h : χ.Even) : (χ⁻¹).Even := by
  have := inv_mul_neg_one χ
  rw [h] at this
  rwa [one_mul] at this

omit [NeZero N] in
private lemma odd_inv {χ : DirichletCharacter ℂ N} (h : χ.Odd) : (χ⁻¹).Odd := by
  have hmul := inv_mul_neg_one χ
  rw [h] at hmul
  show χ⁻¹ (-1) = -1
  linear_combination -hmul

private lemma one_sub_ne_neg_nat {s : ℂ} (hs : s.re ≤ 1/2) :
    ∀ n : ℕ, (1:ℂ) - s ≠ -n := by
  intro n h
  have := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at this
  have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  linarith

/-- Functional-equation identity for even primitive nontrivial characters
(valid on `Re s ≤ 1/2`); recreated from LGrowth. -/
private lemma LFunction_left_even {χ : DirichletCharacter ℂ N} (hχp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (hE : χ.Even) {s : ℂ} (hs : s.re ≤ 1/2) :
    DirichletCharacter.LFunction χ s
      = (N:ℂ) ^ ((1:ℂ)/2 - s) * DirichletCharacter.rootNumber χ *
        (Complex.Gammaℂ (1 - s) * Complex.sin (↑π * s / 2)) *
        DirichletCharacter.LFunction χ⁻¹ (1 - s) := by
  have hN : N ≠ 1 := fun h => hχ (χ.level_one' h)
  have hre1s : 0 < (1 - s : ℂ).re := by
    rw [Complex.sub_re, Complex.one_re]; linarith
  have hEinv : (χ⁻¹).Even := even_inv hE
  have hΓne : Complex.Gammaℝ (1 - s) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre1s
  have hΛinv : DirichletCharacter.completedLFunction χ⁻¹ (1 - s)
      = DirichletCharacter.LFunction χ⁻¹ (1 - s) * Complex.Gammaℝ (1 - s) := by
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inr hN)
    rw [hEinv.gammaFactor_def] at h
    rw [h, div_mul_cancel₀ _ hΓne]
  have hFE : DirichletCharacter.completedLFunction χ s
      = (N:ℂ) ^ ((1:ℂ)/2 - s) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ (1 - s) := by
    have h := hχp.completedLFunction_one_sub (1 - s)
    rw [sub_sub_cancel] at h
    rw [show ((1:ℂ) - s - 1/2) = (1:ℂ)/2 - s from by ring] at h
    exact h
  have hrefl : (Complex.Gammaℝ s)⁻¹
      = Complex.Gammaℂ (1 - s) * Complex.sin (↑π * s / 2) * (Complex.Gammaℝ (1 - s))⁻¹ := by
    have h := Complex.inv_Gammaℝ_one_sub (s := 1 - s) (one_sub_ne_neg_nat hs)
    rw [sub_sub_cancel] at h
    rw [h]
    congr 2
    rw [show ↑π * (1 - s) / 2 = ↑π/2 - ↑π * s / 2 from by ring, Complex.cos_pi_div_two_sub]
  have hL : DirichletCharacter.LFunction χ s
      = DirichletCharacter.completedLFunction χ s * (Complex.Gammaℝ s)⁻¹ := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN),
      hE.gammaFactor_def, div_eq_mul_inv]
  rw [hL, hFE, hΛinv, hrefl]
  field_simp

/-- Functional-equation identity for odd primitive characters (valid on
`Re s ≤ 1/2`); recreated from LGrowth. -/
private lemma LFunction_left_odd {χ : DirichletCharacter ℂ N} (hχp : χ.IsPrimitive)
    (hχ : χ ≠ 1) (hO : χ.Odd) {s : ℂ} (hs : s.re ≤ 1/2) :
    DirichletCharacter.LFunction χ s
      = (N:ℂ) ^ ((1:ℂ)/2 - s) * DirichletCharacter.rootNumber χ *
        (Complex.Gammaℂ (1 - s) * Complex.cos (↑π * s / 2)) *
        DirichletCharacter.LFunction χ⁻¹ (1 - s) := by
  have hN : N ≠ 1 := fun h => hχ (χ.level_one' h)
  have hre2s : 0 < ((1 - s : ℂ) + 1).re := by
    rw [Complex.add_re, Complex.sub_re, Complex.one_re]; linarith
  have hOinv : (χ⁻¹).Odd := odd_inv hO
  have hΓne : Complex.Gammaℝ ((1 - s) + 1) ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre2s
  have hΛinv : DirichletCharacter.completedLFunction χ⁻¹ (1 - s)
      = DirichletCharacter.LFunction χ⁻¹ (1 - s) * Complex.Gammaℝ ((1 - s) + 1) := by
    have h := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inr hN)
    rw [hOinv.gammaFactor_def] at h
    rw [h, div_mul_cancel₀ _ hΓne]
  have hFE : DirichletCharacter.completedLFunction χ s
      = (N:ℂ) ^ ((1:ℂ)/2 - s) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ (1 - s) := by
    have h := hχp.completedLFunction_one_sub (1 - s)
    rw [sub_sub_cancel] at h
    rw [show ((1:ℂ) - s - 1/2) = (1:ℂ)/2 - s from by ring] at h
    exact h
  have hrefl : (Complex.Gammaℝ (s + 1))⁻¹
      = Complex.Gammaℂ (1 - s) * Complex.cos (↑π * s / 2) *
        (Complex.Gammaℝ ((1 - s) + 1))⁻¹ := by
    have h := Complex.inv_Gammaℝ_two_sub (s := 1 - s) (one_sub_ne_neg_nat hs)
    rw [show (2:ℂ) - (1 - s) = s + 1 from by ring] at h
    rw [h]
    congr 2
    rw [show ↑π * (1 - s) / 2 = ↑π/2 - ↑π * s / 2 from by ring, Complex.sin_pi_div_two_sub]
  have hL : DirichletCharacter.LFunction χ s
      = DirichletCharacter.completedLFunction χ s * (Complex.Gammaℝ (s + 1))⁻¹ := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN),
      hO.gammaFactor_def, div_eq_mul_inv]
  rw [hL, hFE, hΛinv, hrefl]
  field_simp

/-- **Left-edge bound.** For primitive nontrivial `χ mod N` and `−1/2 ≤ Re z < 0`,
`‖L(z,χ)‖ ≤ 12·(1 + 1/(−Re z))·(N·(2+|Im z|))^{1/2−Re z}`. -/
lemma norm_LFunction_le_left_edge {χ : DirichletCharacter ℂ N}
    (hχp : χ.IsPrimitive) (hχ : χ ≠ 1) {z : ℂ} (h1 : -(1/2 : ℝ) ≤ z.re) (h2 : z.re < 0) :
    ‖DirichletCharacter.LFunction χ z‖
      ≤ 12 * (1 + 1/(-z.re)) * ((N:ℝ) * (2 + |z.im|)) ^ ((1:ℝ)/2 - z.re) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hb1 : ‖(N:ℂ) ^ ((1:ℂ)/2 - z)‖ = (N:ℝ) ^ ((1:ℝ)/2 - z.re) := by
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
    congr 1
    rw [show ((1:ℂ)/2) = (((1:ℝ)/2 : ℝ) : ℂ) from by norm_num,
      Complex.sub_re, Complex.ofReal_re]
  have hb2 : ‖DirichletCharacter.rootNumber χ‖ = 1 := norm_rootNumber_eq_one hχp
  have hb4 : ‖DirichletCharacter.LFunction χ⁻¹ (1 - z)‖ ≤ 1 + 1/(-z.re) := by
    have hinv1 : χ⁻¹ ≠ 1 := fun h => hχ (inv_eq_one.mp h)
    have hre : 1 < (1 - z : ℂ).re := by
      rw [Complex.sub_re, Complex.one_re]; linarith
    have h := norm_LFunction_le_of_one_lt_re χ⁻¹ hre
    have heq : (1 - z : ℂ).re - 1 = -z.re := by
      rw [Complex.sub_re, Complex.one_re]; ring
    rwa [heq] at h
  have hfrac0 : (0:ℝ) ≤ 1 + 1/(-z.re) := by
    have hpos : 0 < -z.re := by linarith
    positivity
  have hmulrp : ((N:ℝ) * (2 + |z.im|)) ^ ((1:ℝ)/2 - z.re)
      = (N:ℝ) ^ ((1:ℝ)/2 - z.re) * (2 + |z.im|) ^ ((1:ℝ)/2 - z.re) :=
    Real.mul_rpow hNpos.le (by positivity)
  have hNrp0 : (0:ℝ) ≤ (N:ℝ) ^ ((1:ℝ)/2 - z.re) := Real.rpow_nonneg hNpos.le _
  have hfinal : ∀ T : ℂ, (T = Complex.sin (↑π * z / 2) ∨ T = Complex.cos (↑π * z / 2)) →
      ‖(N:ℂ) ^ ((1:ℂ)/2 - z) * DirichletCharacter.rootNumber χ *
        (Complex.Gammaℂ (1 - z) * T) * DirichletCharacter.LFunction χ⁻¹ (1 - z)‖
      ≤ 12 * (1 + 1/(-z.re)) * ((N:ℝ) * (2 + |z.im|)) ^ ((1:ℝ)/2 - z.re) := by
    intro T hT
    have hb3 := norm_GammaC_mul_trig_interp h1 h2.le hT
    rw [norm_mul, norm_mul, norm_mul, hb1, hb2, mul_one, hmulrp]
    calc (N:ℝ) ^ ((1:ℝ)/2 - z.re) * ‖Complex.Gammaℂ (1 - z) * T‖ *
        ‖DirichletCharacter.LFunction χ⁻¹ (1 - z)‖
        ≤ (N:ℝ) ^ ((1:ℝ)/2 - z.re) * (12 * (2 + |z.im|) ^ ((1:ℝ)/2 - z.re)) *
            (1 + 1/(-z.re)) := by
          apply mul_le_mul _ hb4 (norm_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hb3 hNrp0
      _ = 12 * (1 + 1/(-z.re)) *
            ((N:ℝ) ^ ((1:ℝ)/2 - z.re) * (2 + |z.im|) ^ ((1:ℝ)/2 - z.re)) := by ring
  rcases χ.even_or_odd with hE | hO
  · rw [LFunction_left_even hχp hχ hE (by linarith : z.re ≤ 1/2)]
    exact hfinal _ (Or.inl rfl)
  · rw [LFunction_left_odd hχp hχ hO (by linarith : z.re ≤ 1/2)]
    exact hfinal _ (Or.inr rfl)

end LeftEdge

/-! ### The convexity bound -/

section Convexity

variable {N : ℕ} [NeZero N]

/-- **Z4a′, combined form.** For primitive nontrivial `χ mod N` and
`s = σ + it` with `1/200 ≤ σ ≤ 2`:
`‖L(s,χ)‖ ≤ 100000·(N·(|t|+2))^{max((1−σ)/2, 0)}·log(N·(|t|+3))`. -/
theorem norm_LFunction_le_convexity' {χ : DirichletCharacter ℂ N}
    (hχp : χ.IsPrimitive) (hχ : χ ≠ 1) {s : ℂ}
    (hσ1 : 1/200 ≤ s.re) (hσ2 : s.re ≤ 2) :
    ‖DirichletCharacter.LFunction χ s‖
      ≤ 100000 * ((N:ℝ) * (|s.im| + 2)) ^ (max ((1 - s.re)/2) 0)
          * Real.log ((N:ℝ) * (|s.im| + 3)) := by
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  set D : ℝ := (N:ℝ) * (|s.im| + 2) with hDdef
  set M : ℝ := (N:ℝ) * (|s.im| + 3) with hMdef
  have habs : (0:ℝ) ≤ |s.im| := abs_nonneg _
  have hD1 : (1:ℝ) ≤ D := by rw [hDdef]; nlinarith
  have hD0 : (0:ℝ) < D := by linarith
  have hM3 : (3:ℝ) ≤ M := by rw [hMdef]; nlinarith
  have hM0 : (0:ℝ) < M := by linarith
  have hDM : D ≤ M := by rw [hDdef, hMdef]; nlinarith
  have hlogM1 : (1:ℝ) ≤ Real.log M := by
    rw [Real.le_log_iff_exp_le hM0]
    linarith [exp_one_le_three]
  set L : ℝ := 1 + Real.log M with hLdef
  have hL2 : (2:ℝ) ≤ L := by rw [hLdef]; linarith
  have hL0 : (0:ℝ) < L := by linarith
  have h1L0 : (0:ℝ) < 1 + L := by linarith
  have hiL : (1:ℝ)/L ≤ 1/2 := by
    rw [div_le_iff₀ hL0]
    linarith
  have hiL0 : (0:ℝ) < 1/L := by positivity
  have hlogD : Real.log D ≤ L := by
    have h := Real.log_le_log hD0 hDM
    rw [hLdef]
    linarith
  have hD3 : D ^ ((1:ℝ)/L) ≤ 3 := by
    rw [Real.rpow_def_of_pos hD0]
    calc Real.exp (Real.log D * (1/L)) ≤ Real.exp 1 := by
          apply Real.exp_le_exp.mpr
          rw [mul_one_div, div_le_one hL0]
          exact hlogD
      _ ≤ 3 := exp_one_le_three
  have hmaxE0 : (0:ℝ) ≤ max ((1 - s.re)/2) 0 := le_max_right _ _
  have hDmax0 : (0:ℝ) ≤ D ^ (max ((1 - s.re)/2) 0) := Real.rpow_nonneg hD0.le _
  have hDmax1 : (1:ℝ) ≤ D ^ (max ((1 - s.re)/2) 0) := Real.one_le_rpow hD1 hmaxE0
  set σR : ℝ := 1 + 1/L with hσRdef
  have hσR1 : 1 < σR := by rw [hσRdef]; linarith
  have hσR32 : σR ≤ 3/2 := by rw [hσRdef]; linarith
  set σL : ℝ := -(1/L) with hσLdef
  have hσLhalf : -(1/2 : ℝ) ≤ σL := by rw [hσLdef]; linarith
  have hσL0 : σL < 0 := by rw [hσLdef]; linarith
  set W : ℝ := σR - σL with hWdef
  have hW : W = 1 + 2/L := by
    rw [hWdef, hσRdef, hσLdef]
    ring
  have hiL2 : (2:ℝ)/L ≤ 1 := by
    rw [div_le_iff₀ hL0]
    linarith
  have hW1 : 1 ≤ W := by
    have h2L0 : (0:ℝ) < 2/L := div_pos two_pos hL0
    rw [hW]
    linarith
  have hW2 : W ≤ 2 := by rw [hW]; linarith
  have hW0 : (0:ℝ) < W := by linarith
  have h1L3logM : 1 + L ≤ 3 * Real.log M := by rw [hLdef]; linarith
  rcases le_or_gt s.re σR with hcase | hcase
  · -- Phragmén–Lindelöf branch: `1/200 ≤ σ ≤ σR`
    set b : ℝ := 108 * D ^ ((1:ℝ)/2) with hbdef
    have hDhalf1 : (1:ℝ) ≤ D ^ ((1:ℝ)/2) := Real.one_le_rpow hD1 (by norm_num)
    have hDhalf0 : (0:ℝ) < D ^ ((1:ℝ)/2) := by linarith
    have hb1 : (1:ℝ) ≤ b := by rw [hbdef]; nlinarith
    have hb0 : (0:ℝ) < b := by linarith
    set c : ℝ := Real.log b / W with hcdef
    have hc0 : (0:ℝ) ≤ c := div_nonneg (Real.log_nonneg hb1) hW0.le
    set K : ℂ → ℂ := fun z =>
      DirichletCharacter.LFunction χ z * Complex.exp ((z - s) ^ 2) *
        Complex.exp ((z - (σR : ℂ)) * (c : ℂ)) with hKdef
    have hnormK : ∀ z : ℂ, ‖K z‖ = ‖DirichletCharacter.LFunction χ z‖ *
        Real.exp ((z.re - s.re) ^ 2 - (z.im - s.im) ^ 2) *
        Real.exp ((z.re - σR) * c) := by
      intro z
      rw [hKdef]
      simp only []
      rw [norm_mul, norm_mul, norm_exp_sq_sub, norm_exp_mul_ofReal,
        Complex.sub_re, Complex.ofReal_re]
    -- right boundary
    have hright : ∀ z : ℂ, z.re = σR → ‖K z‖ ≤ 81 * (1 + L) := by
      intro z hz
      rw [hnormK z, hz, sub_self, zero_mul, Real.exp_zero, mul_one]
      have hLz : ‖DirichletCharacter.LFunction χ z‖ ≤ 1 + L := by
        have h := norm_LFunction_le_of_one_lt_re χ (z := z) (by rw [hz]; exact hσR1)
        rw [hz, show σR - 1 = 1/L from by rw [hσRdef]; ring, one_div_one_div] at h
        exact h
      have hgauss : Real.exp ((σR - s.re) ^ 2 - (z.im - s.im) ^ 2) ≤ 81 := by
        calc Real.exp ((σR - s.re) ^ 2 - (z.im - s.im) ^ 2) ≤ Real.exp 4 := by
              apply Real.exp_le_exp.mpr
              nlinarith [sq_nonneg (z.im - s.im)]
          _ ≤ 81 := exp_four_le
      calc ‖DirichletCharacter.LFunction χ z‖ *
          Real.exp ((σR - s.re) ^ 2 - (z.im - s.im) ^ 2)
          ≤ (1 + L) * 81 := mul_le_mul hLz hgauss (Real.exp_pos _).le h1L0.le
        _ = 81 * (1 + L) := by ring
    -- left boundary
    have hcancel : 108 * D ^ ((1:ℝ)/2) * b⁻¹ = 1 := by
      rw [← hbdef]
      exact mul_inv_cancel₀ hb0.ne'
    have hleft : ∀ z : ℂ, z.re = σL → ‖K z‖ ≤ 81 * (1 + L) := by
      intro z hz
      rw [hnormK z, hz]
      have hnorm2 : Real.exp ((σL - σR) * c) = b⁻¹ := by
        have h1 : (σL - σR) * c = -Real.log b := by
          rw [hcdef, show σL - σR = -W from by rw [hWdef]; ring]
          field_simp
        rw [h1, Real.exp_neg, Real.exp_log hb0]
      rw [hnorm2]
      -- the L-function bound with base split
      have hL1b : ‖DirichletCharacter.LFunction χ z‖
          ≤ 12 * (1 + L) * (D ^ ((1:ℝ)/2) * D ^ ((1:ℝ)/L) * (1 + |z.im - s.im|)) := by
        have h := norm_LFunction_le_left_edge hχp hχ (z := z)
          (by rw [hz]; exact hσLhalf) (by rw [hz]; exact hσL0)
        rw [hz, show 1 + 1/(-σL) = 1 + L from by
          rw [hσLdef, neg_neg, one_div_one_div, hLdef]] at h
        have hE : (1:ℝ)/2 - σL = 1/2 + 1/L := by rw [hσLdef]; ring
        have hbase : ((N:ℝ) * (2 + |z.im|)) ^ ((1:ℝ)/2 - σL)
            ≤ D ^ ((1:ℝ)/2) * D ^ ((1:ℝ)/L) * (1 + |z.im - s.im|) := by
          have hstep1 : (N:ℝ) * (2 + |z.im|) ≤ D * (1 + |z.im - s.im|) := by
            have h3 := mul_le_mul_of_nonneg_left (two_add_abs_le z.im s.im)
              (by linarith : (0:ℝ) ≤ (N:ℝ))
            calc (N:ℝ) * (2 + |z.im|)
                ≤ (N:ℝ) * ((2 + |s.im|) * (1 + |z.im - s.im|)) := h3
              _ = D * (1 + |z.im - s.im|) := by rw [hDdef]; ring
          have hexp0 : (0:ℝ) ≤ (1:ℝ)/2 - σL := by rw [hE]; positivity
          have hexple : (1:ℝ)/2 - σL ≤ 1 := by rw [hE]; linarith
          calc ((N:ℝ) * (2 + |z.im|)) ^ ((1:ℝ)/2 - σL)
              ≤ (D * (1 + |z.im - s.im|)) ^ ((1:ℝ)/2 - σL) :=
                Real.rpow_le_rpow (by positivity) hstep1 hexp0
            _ = D ^ ((1:ℝ)/2 - σL) * (1 + |z.im - s.im|) ^ ((1:ℝ)/2 - σL) :=
                Real.mul_rpow hD0.le (by positivity)
            _ ≤ D ^ ((1:ℝ)/2 - σL) * (1 + |z.im - s.im|) := by
                have h1v : (1:ℝ) ≤ 1 + |z.im - s.im| := by
                  linarith [abs_nonneg (z.im - s.im)]
                have h2v : (1 + |z.im - s.im|) ^ ((1:ℝ)/2 - σL)
                    ≤ (1 + |z.im - s.im|) ^ (1:ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le h1v hexple
                rw [Real.rpow_one] at h2v
                exact mul_le_mul_of_nonneg_left h2v (Real.rpow_nonneg hD0.le _)
            _ = D ^ ((1:ℝ)/2) * D ^ ((1:ℝ)/L) * (1 + |z.im - s.im|) := by
                rw [hE, Real.rpow_add hD0]
        calc ‖DirichletCharacter.LFunction χ z‖
            ≤ 12 * (1 + L) * (((N:ℝ) * (2 + |z.im|)) ^ ((1:ℝ)/2 - σL)) := h
          _ ≤ 12 * (1 + L) * (D ^ ((1:ℝ)/2) * D ^ ((1:ℝ)/L) * (1 + |z.im - s.im|)) := by
              apply mul_le_mul_of_nonneg_left hbase
              nlinarith
      have hgauss : Real.exp ((σL - s.re) ^ 2 - (z.im - s.im) ^ 2)
          ≤ 81 * Real.exp (-(z.im - s.im) ^ 2) := by
        rw [show (σL - s.re) ^ 2 - (z.im - s.im) ^ 2
            = (σL - s.re) ^ 2 + -(z.im - s.im) ^ 2 from by ring, Real.exp_add]
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        calc Real.exp ((σL - s.re) ^ 2) ≤ Real.exp 4 := by
              apply Real.exp_le_exp.mpr
              nlinarith
          _ ≤ 81 := exp_four_le
      have hA0 : (0:ℝ) ≤ 12 * 81 * (1 + L) * D ^ ((1:ℝ)/2) := by
        have := hDhalf0.le
        nlinarith
      calc ‖DirichletCharacter.LFunction χ z‖ *
          Real.exp ((σL - s.re) ^ 2 - (z.im - s.im) ^ 2) * b⁻¹
          ≤ (12 * (1 + L) * (D ^ ((1:ℝ)/2) * D ^ ((1:ℝ)/L) * (1 + |z.im - s.im|))) *
              (81 * Real.exp (-(z.im - s.im) ^ 2)) * b⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hb0.le)
            apply mul_le_mul hL1b hgauss (Real.exp_pos _).le
            have h0a : (0:ℝ) ≤ D ^ ((1:ℝ)/L) := Real.rpow_nonneg hD0.le _
            have h0b : (0:ℝ) ≤ 1 + |z.im - s.im| := by
              linarith [abs_nonneg (z.im - s.im)]
            nlinarith [hDhalf0.le, mul_nonneg (mul_nonneg hDhalf0.le h0a) h0b]
        _ = 12 * 81 * (1 + L) * D ^ ((1:ℝ)/2) * (D ^ ((1:ℝ)/L)) *
              ((1 + |z.im - s.im|) * Real.exp (-(z.im - s.im) ^ 2)) * b⁻¹ := by ring
        _ ≤ 12 * 81 * (1 + L) * D ^ ((1:ℝ)/2) * 3 * 3 * b⁻¹ := by
            apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr hb0.le)
            apply mul_le_mul (mul_le_mul_of_nonneg_left hD3 hA0)
              (one_add_abs_mul_exp_neg_sq_le _) (by positivity)
            nlinarith
        _ = 81 * (1 + L) * (108 * D ^ ((1:ℝ)/2) * b⁻¹) := by ring
        _ = 81 * (1 + L) := by rw [hcancel, mul_one]
    -- growth condition data
    have hN3 : (1:ℝ) ≤ (N:ℝ) ^ 3 := one_le_pow₀ hN1
    have hP1 : (1:ℝ) ≤ 1458 * (N:ℝ) ^ 3 := by nlinarith
    have hgrowth : ∀ z ∈ Complex.re ⁻¹' (Set.Ioo σL σR),
        ‖K z‖ ≤ (1458 * (N:ℝ) ^ 3) * (4 + |z.im|) ^ 3 := by
      intro z hz
      have hz1 : σL < z.re := hz.1
      have hz2 : z.re < σR := hz.2
      rw [hnormK z]
      have hLb : ‖DirichletCharacter.LFunction χ z‖ ≤ 18 * ((N:ℝ) * (2 + ‖z‖)) ^ 3 :=
        norm_LFunction_le_of_neg_half_le_re hχp hχ (by linarith)
      have hgauss : Real.exp ((z.re - s.re) ^ 2 - (z.im - s.im) ^ 2) ≤ 81 := by
        calc Real.exp ((z.re - s.re) ^ 2 - (z.im - s.im) ^ 2) ≤ Real.exp 4 := by
              apply Real.exp_le_exp.mpr
              nlinarith [sq_nonneg (z.im - s.im)]
          _ ≤ 81 := exp_four_le
      have hnorm1 : Real.exp ((z.re - σR) * c) ≤ 1 := by
        rw [show (1:ℝ) = Real.exp 0 from Real.exp_zero.symm]
        apply Real.exp_le_exp.mpr
        exact mul_nonpos_iff.mpr (Or.inr ⟨by linarith, hc0⟩)
      have hzb : (N:ℝ) * (2 + ‖z‖) ≤ (N:ℝ) * (4 + |z.im|) := by
        have h := Complex.norm_le_abs_re_add_abs_im z
        have h2 : |z.re| ≤ 2 := by
          rw [abs_le]
          constructor <;> linarith
        have h3 : 2 + ‖z‖ ≤ 4 + |z.im| := by linarith
        exact mul_le_mul_of_nonneg_left h3 (by linarith)
      have hcube : ((N:ℝ) * (2 + ‖z‖)) ^ 3 ≤ ((N:ℝ) * (4 + |z.im|)) ^ 3 :=
        pow_le_pow_left₀ (by positivity) hzb 3
      calc ‖DirichletCharacter.LFunction χ z‖ *
          Real.exp ((z.re - s.re) ^ 2 - (z.im - s.im) ^ 2) *
          Real.exp ((z.re - σR) * c)
          ≤ (18 * ((N:ℝ) * (2 + ‖z‖)) ^ 3) * 81 * 1 := by
            apply mul_le_mul _ hnorm1 (Real.exp_pos _).le (by positivity)
            exact mul_le_mul hLb hgauss (Real.exp_pos _).le (by positivity)
        _ = 1458 * ((N:ℝ) * (2 + ‖z‖)) ^ 3 := by ring
        _ ≤ 1458 * ((N:ℝ) * (4 + |z.im|)) ^ 3 := by linarith
        _ = (1458 * (N:ℝ) ^ 3) * (4 + |z.im|) ^ 3 := by rw [mul_pow]; ring
    -- Phragmén–Lindelöf
    have main : ‖K s‖ ≤ 81 * (1 + L) := by
      apply PhragmenLindelof.vertical_strip (a := σL) (b := σR) (C := 81 * (1 + L))
      · have hKd : Differentiable ℂ K := by
          apply Differentiable.mul
          · apply Differentiable.mul
            · exact DirichletCharacter.differentiable_LFunction hχ
            · apply Complex.differentiable_exp.comp
              fun_prop
          · apply Complex.differentiable_exp.comp
            fun_prop
        exact hKd.diffContOnCl
      · refine ⟨1, ?_, Real.log (1458 * (N:ℝ) ^ 3) + 12, ?_⟩
        · rw [← hWdef, lt_div_iff₀ hW0]
          nlinarith [Real.pi_gt_three]
        · simpa only [one_mul] using isBigO_double_exp hP1 hgrowth
      · exact hleft
      · exact hright
      · linarith
      · exact hcase
    -- unwind at `s`
    have hKs : ‖K s‖ = ‖DirichletCharacter.LFunction χ s‖ *
        Real.exp ((s.re - σR) * c) := by
      rw [hnormK s, show (s.re - s.re) ^ 2 - (s.im - s.im) ^ 2 = 0 from by ring,
        Real.exp_zero, mul_one]
    have hLs : ‖DirichletCharacter.LFunction χ s‖
        = ‖K s‖ * Real.exp ((σR - s.re) * c) := by
      rw [hKs, mul_assoc, ← Real.exp_add,
        show (s.re - σR) * c + (σR - s.re) * c = 0 from by ring,
        Real.exp_zero, mul_one]
    set θ : ℝ := (σR - s.re) / W with hθdef
    have hθ0 : (0:ℝ) ≤ θ := div_nonneg (by linarith) hW0.le
    have hθ1 : θ ≤ 1 := by
      rw [hθdef, div_le_one hW0]
      linarith
    have hbθ : Real.exp ((σR - s.re) * c) = b ^ θ := by
      rw [Real.rpow_def_of_pos hb0]
      congr 1
      rw [hcdef, hθdef]
      ring
    have hθhalf : θ/2 ≤ max ((1 - s.re)/2) 0 + 1/L := by
      have hexpand : θ/2 = (σR - s.re) / (W * 2) := by
        rw [hθdef, div_div]
      rcases le_total s.re 1 with hσle | hσge
      · rw [max_eq_left (by linarith : (0:ℝ) ≤ (1 - s.re)/2), hexpand,
          div_le_iff₀ (by linarith : (0:ℝ) < W * 2), hσRdef, hW]
        nlinarith [mul_nonneg hiL0.le (by linarith : (0:ℝ) ≤ 1 - s.re),
          sq_nonneg (1/L)]
      · rw [max_eq_right (by linarith : (1 - s.re)/2 ≤ 0), zero_add, hexpand,
          div_le_iff₀ (by linarith : (0:ℝ) < W * 2), hσRdef, hW]
        nlinarith [sq_nonneg (1/L)]
    have hbθle : b ^ θ ≤ 324 * D ^ (max ((1 - s.re)/2) 0) := by
      have h108 : (108:ℝ) ^ θ ≤ 108 := by
        calc (108:ℝ) ^ θ ≤ (108:ℝ) ^ (1:ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hθ1
          _ = 108 := Real.rpow_one _
      have hsplit : b ^ θ = 108 ^ θ * (D ^ ((1:ℝ)/2)) ^ θ := by
        rw [hbdef, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hD0.le _)]
      have hDθ : (D ^ ((1:ℝ)/2)) ^ θ = D ^ (θ/2) := by
        rw [← Real.rpow_mul hD0.le]
        congr 1
        ring
      calc b ^ θ = 108 ^ θ * (D ^ ((1:ℝ)/2)) ^ θ := hsplit
        _ ≤ 108 * D ^ (θ/2) := by
            rw [hDθ]
            exact mul_le_mul_of_nonneg_right h108 (Real.rpow_nonneg hD0.le _)
        _ ≤ 108 * D ^ (max ((1 - s.re)/2) 0 + 1/L) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact Real.rpow_le_rpow_of_exponent_le hD1 hθhalf
        _ = 108 * (D ^ (max ((1 - s.re)/2) 0) * D ^ ((1:ℝ)/L)) := by
            rw [Real.rpow_add hD0]
        _ ≤ 108 * (D ^ (max ((1 - s.re)/2) 0) * 3) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            exact mul_le_mul_of_nonneg_left hD3 hDmax0
        _ = 324 * D ^ (max ((1 - s.re)/2) 0) := by ring
    calc ‖DirichletCharacter.LFunction χ s‖
        = ‖K s‖ * Real.exp ((σR - s.re) * c) := hLs
      _ ≤ (81 * (1 + L)) * (324 * D ^ (max ((1 - s.re)/2) 0)) := by
          apply mul_le_mul main _ (Real.exp_pos _).le (by positivity)
          rw [hbθ]
          exact hbθle
      _ = 26244 * (1 + L) * D ^ (max ((1 - s.re)/2) 0) := by ring
      _ ≤ 26244 * (3 * Real.log M) * D ^ (max ((1 - s.re)/2) 0) := by
          apply mul_le_mul_of_nonneg_right _ hDmax0
          apply mul_le_mul_of_nonneg_left h1L3logM (by norm_num)
      _ = 78732 * D ^ (max ((1 - s.re)/2) 0) * Real.log M := by ring
      _ ≤ 100000 * D ^ (max ((1 - s.re)/2) 0) * Real.log M := by
          nlinarith [mul_nonneg hDmax0 (by linarith : (0:ℝ) ≤ Real.log M)]
  · -- direct branch: `σR < σ ≤ 2`
    have hσgt1 : 1 < s.re := lt_trans hσR1 hcase
    have h := norm_LFunction_le_of_one_lt_re χ hσgt1
    have h2 : 1/(s.re - 1) ≤ L := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < s.re - 1)]
      have h3 : 1/L ≤ s.re - 1 := by
        have : σR - 1 = 1/L := by rw [hσRdef]; ring
        linarith
      calc (1:ℝ) = L * (1/L) := by field_simp
        _ ≤ L * (s.re - 1) := mul_le_mul_of_nonneg_left h3 hL0.le
    have hDlog : Real.log M ≤ D ^ (max ((1 - s.re)/2) 0) * Real.log M := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hDmax1)
        (by linarith : (0:ℝ) ≤ Real.log M)]
    calc ‖DirichletCharacter.LFunction χ s‖ ≤ 1 + 1/(s.re - 1) := h
      _ ≤ 1 + L := by linarith
      _ ≤ 3 * Real.log M := h1L3logM
      _ ≤ 100000 * (D ^ (max ((1 - s.re)/2) 0) * Real.log M) := by nlinarith
      _ = 100000 * D ^ (max ((1 - s.re)/2) 0) * Real.log M := by ring

/-- **Z4a′ (frozen, §12.1).** The convexity bound for Dirichlet L-functions:
for primitive nontrivial `χ mod N` and `s = σ + it` with `1/200 ≤ σ ≤ 1`,
`‖L(s,χ)‖ ≤ C_cx·(N·(|t|+2))^{(1−σ)/2}·log(N·(|t|+3))` with `C_cx = 100000`. -/
theorem norm_LFunction_le_convexity {χ : DirichletCharacter ℂ N}
    (hχp : χ.IsPrimitive) (hχ : χ ≠ 1) {s : ℂ}
    (hσ1 : 1/200 ≤ s.re) (hσ2 : s.re ≤ 1) :
    ‖DirichletCharacter.LFunction χ s‖
      ≤ 100000 * ((N:ℝ) * (|s.im| + 2)) ^ ((1 - s.re)/2)
          * Real.log ((N:ℝ) * (|s.im| + 3)) := by
  have h := norm_LFunction_le_convexity' hχp hχ hσ1 (by linarith)
  rwa [max_eq_left (by linarith : (0:ℝ) ≤ (1 - s.re)/2)] at h

end Convexity

end Carmichael
