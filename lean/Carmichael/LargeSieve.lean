/-
Route Z, TZ-lite File 2: the pre-sifted multiplicative large sieve,
t-integrated (Gallagher 1970, Theorem 4 shape, lossy constants).

Main result: `presifted_large_sieve`.  For coefficients supported on
integers whose least prime factor exceeds `Q`,

  ∑_{f ≤ Q} log(Q/f) ∑_{ψ primitive mod f} ∫_{−T}^{T} ‖∑ aₙ ψ(n) n^{−it}‖² dt
    ≤ 100 ∑ (n + Q²T) ‖aₙ‖².

Route (Gallagher pp. 332–333 with the Z6a Fejér kernel replacing his
Theorem 1):

* smoothing: `MeanValue.kernel_mvt` bounds the t-integral by the bilinear
  triangle form, which equals `(1/δ)∫‖U(x)‖²dx` for the window sums
  `U(x) = ∑_{|log n − x| ≤ δ/2} cₙ` (indicator-overlap identity);
* at each x, the window sum is attacked by the multiplicative machine:
  Gauss-sum transfer `∑_u χ(u)T(u/q) = τ(χ)·S(χ⁻¹)`, unit-group Parseval,
  the induced-character modulus `‖τ(changeLevel ψ)‖² = f` (CRT split of
  the standard additive character; the Ramanujan block at the squarefree
  level contributes norm 1), and the totient-quotient weight
  `∑_{r ≤ Q/f} μ²(r)/φ(r) ≥ (φ(f)/f)·log(Q/f)`;
* the resulting Farey-point family is 1/Q²-spaced in [0, 1 − 1/Q²], and a
  Gallagher–Sobolev argument with exact Parseval over a unit period gives
  the additive large sieve with constant `1/δ + 4πF`.

The `log (Q/f)` conductor weight is the pre-sift gain (log-freeness of the
census machine); it must not be weakened.
-/
import Mathlib
import Carmichael.MeanValue
import Carmichael.TotientSum
import Carmichael.BrunTitchmarsh

set_option autoImplicit false

namespace Carmichael
namespace LargeSieve

open Complex MeasureTheory Finset intervalIntegral DirichletCharacter
open scoped Real ComplexConjugate Classical

/-! ### Frozen definitions -/

/-- Distance to the nearest integer. -/
noncomputable def circleDist (x : ℝ) : ℝ := |x - round x|

/-- The primitive Dirichlet characters mod `f` (junk `∅` at `f = 0`). -/
noncomputable def primChars (f : ℕ) : Finset (DirichletCharacter ℂ f) :=
  if h : f = 0 then ∅ else
    haveI : NeZero f := ⟨h⟩
    (Finset.univ.filter (fun ψ : DirichletCharacter ℂ f => ψ.IsPrimitive))

lemma mem_primChars {f : ℕ} [NeZero f] {ψ : DirichletCharacter ℂ f} :
    ψ ∈ primChars f ↔ ψ.IsPrimitive := by
  rw [primChars, dif_neg (NeZero.ne f)]
  simp

/-! ### Complex helpers -/

lemma norm_sq_eq_mul_conj_re (z : ℂ) : ‖z‖ ^ 2 = (z * conj z).re := by
  rw [Complex.mul_conj, ← Complex.normSq_eq_norm_sq]
  simp

/-- Sums of unit-supported functions over `ZMod q` collapse to unit sums. -/
lemma sum_units_eq {q : ℕ} [NeZero q] (F : ZMod q → ℂ)
    (hF : ∀ x : ZMod q, ¬IsUnit x → F x = 0) :
    ∑ x : ZMod q, F x = ∑ u : (ZMod q)ˣ, F u := by
  rw [← Finset.sum_filter_of_ne (p := fun x : ZMod q => IsUnit x)
    (fun x _ h => by by_contra hu; exact h (hF x hu))]
  refine Finset.sum_nbij' (fun x => if h : IsUnit x then h.unit else 1)
    (fun u => (u : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact Finset.mem_univ _
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact u.isUnit
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [dif_pos hx, IsUnit.unit_spec]
  · intro u hu
    rw [dif_pos u.isUnit]
    ext
    rw [IsUnit.unit_spec]
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [dif_pos hx, IsUnit.unit_spec]

/-- `∑_x χ(x)·conj(χ(x)) = φ(q)`. -/
lemma sum_char_mul_conj_self {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∑ x : ZMod q, χ x * conj (χ x) = (q.totient : ℂ) := by
  rw [sum_units_eq (fun x => χ x * conj (χ x))
    (fun x hx => by rw [χ.map_nonunit hx]; simp)]
  have h1 : ∀ u : (ZMod q)ˣ, χ u * conj (χ u) = 1 := by
    intro u
    have h2 := χ.unit_norm_eq_one u
    rw [Complex.mul_conj]
    have h3 : Complex.normSq (χ u) = 1 := by
      rw [Complex.normSq_eq_norm_sq, h2]; norm_num
    rw [h3]
    simp
  rw [Finset.sum_congr rfl fun u _ => h1 u, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_univ, ZMod.card_units_eq_totient]

/-- The norm-square of a Dirichlet character sums to `φ(q)`. -/
lemma sum_norm_sq_char {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∑ x : ZMod q, ‖χ x‖ ^ 2 = q.totient := by
  have h1 := congrArg Complex.re (sum_char_mul_conj_self χ)
  rw [Complex.re_sum] at h1
  calc ∑ x : ZMod q, ‖χ x‖ ^ 2
      = ∑ x : ZMod q, (χ x * conj (χ x)).re :=
        Finset.sum_congr rfl fun x _ => norm_sq_eq_mul_conj_re _
    _ = ((q.totient : ℂ) : ℂ).re := h1
    _ = q.totient := by norm_cast

/-! ### Gauss sums: the modulus of a primitive Gauss sum -/

/-- `‖τ(ψ)‖² = q` for `ψ` primitive mod `q` (averaged inversion; no
field structure needed). -/
lemma norm_sq_gaussSum_primitive {q : ℕ} [NeZero q] {ψ : DirichletCharacter ℂ q}
    (hψ : ψ.IsPrimitive) :
    ‖gaussSum ψ ZMod.stdAddChar‖ ^ 2 = q := by
  set e : AddChar (ZMod q) ℂ := ZMod.stdAddChar with he
  set τ : ℂ := gaussSum ψ e with hτ
  -- the averaged square: ∑_a ‖τ(ψ, e·a)‖² = q · φ(q)
  have hkey : ∑ a : ZMod q, ‖gaussSum ψ (e.mulShift a)‖ ^ 2
      = (q : ℝ) * q.totient := by
    have hC : ∑ a : ZMod q, gaussSum ψ (e.mulShift a) * conj (gaussSum ψ (e.mulShift a))
        = (q : ℂ) * q.totient := by
      have hexp : ∀ a : ZMod q,
          gaussSum ψ (e.mulShift a) * conj (gaussSum ψ (e.mulShift a))
            = ∑ b : ZMod q, ∑ c : ZMod q, ψ b * conj (ψ c) * e (a * (b - c)) := by
        intro a
        rw [gaussSum, map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
        rw [map_mul]
        have h1 : e.mulShift a b * conj (e.mulShift a c) = e (a * (b - c)) := by
          rw [AddChar.mulShift_apply, AddChar.mulShift_apply, ← AddChar.map_neg_eq_conj,
            ← AddChar.map_add_eq_mul, mul_sub, sub_eq_add_neg]
        calc ψ b * e.mulShift a b * (conj (ψ c) * conj (e.mulShift a c))
            = ψ b * conj (ψ c) * (e.mulShift a b * conj (e.mulShift a c)) := by ring
          _ = ψ b * conj (ψ c) * e (a * (b - c)) := by rw [h1]
      rw [Finset.sum_congr rfl fun a _ => hexp a, Finset.sum_comm]
      have hswap : ∀ b : ZMod q,
          ∑ a : ZMod q, ∑ c : ZMod q, ψ b * conj (ψ c) * e (a * (b - c))
            = ∑ c : ZMod q, ψ b * conj (ψ c) * ∑ a : ZMod q, e (a * (b - c)) := by
        intro b
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl fun b _ => hswap b]
      have hdiag : ∀ b : ZMod q, ∑ c : ZMod q, ψ b * conj (ψ c) * ∑ a : ZMod q, e (a * (b - c))
          = ψ b * conj (ψ b) * q := by
        intro b
        rw [Finset.sum_eq_single b]
        · rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
          rw [sub_self, if_pos rfl, ZMod.card]
        · intro c _ hc
          rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q),
            if_neg (sub_ne_zero.mpr (Ne.symm hc))]
          simp
        · intro hb
          exact absurd (Finset.mem_univ b) hb
      rw [Finset.sum_congr rfl fun b _ => hdiag b, ← Finset.sum_mul,
        sum_char_mul_conj_self ψ]
      ring
    have hre := congrArg Complex.re hC
    rw [Complex.re_sum] at hre
    calc ∑ a : ZMod q, ‖gaussSum ψ (e.mulShift a)‖ ^ 2
        = ∑ a : ZMod q, (gaussSum ψ (e.mulShift a) * conj (gaussSum ψ (e.mulShift a))).re :=
          Finset.sum_congr rfl fun a _ => norm_sq_eq_mul_conj_re _
      _ = ((q : ℂ) * q.totient).re := hre
      _ = (q : ℝ) * q.totient := by
          norm_cast
  -- the inversion: each shifted Gauss sum is `ψ⁻¹(a) · τ`
  have hinv : ∀ a : ZMod q, ‖gaussSum ψ (e.mulShift a)‖ ^ 2 = ‖ψ⁻¹ a‖ ^ 2 * ‖τ‖ ^ 2 := by
    intro a
    rw [gaussSum_mulShift_of_isPrimitive e hψ a, norm_mul, mul_pow]
  have hsum : ∑ a : ZMod q, ‖gaussSum ψ (e.mulShift a)‖ ^ 2
      = (q.totient : ℝ) * ‖τ‖ ^ 2 := by
    rw [Finset.sum_congr rfl fun a _ => hinv a, ← Finset.sum_mul, sum_norm_sq_char ψ⁻¹]
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast q.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have h5 : (q.totient : ℝ) * ‖τ‖ ^ 2 = (q.totient : ℝ) * q := by
    rw [← hsum, hkey]
    ring
  exact mul_left_cancel₀ hφ.ne' h5

/-! ### CRT factorization of the standard additive character -/

/-- Additive characters of `ZMod n` are determined by their value at `1`. -/
lemma addChar_zmod_ext {n : ℕ} [NeZero n] {e₁ e₂ : AddChar (ZMod n) ℂ}
    (h : e₁ 1 = e₂ 1) : e₁ = e₂ := by
  ext x
  have hx : (x.val : ℕ) • (1 : ZMod n) = x := by
    rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
  rw [← hx, AddChar.map_nsmul_eq_pow, AddChar.map_nsmul_eq_pow, h]

/-- CRT splitting of `stdAddChar`: for coprime `u`, `v` there are unit
multipliers `A`, `B` with `e_{uv}(x) = e_u(A·x)·e_v(B·x)`. -/
lemma stdAddChar_crt {u v : ℕ} [NeZero u] [NeZero v] [NeZero (u * v)]
    (huv : Nat.Coprime u v) :
    ∃ (A : (ZMod u)ˣ) (B : (ZMod v)ˣ), ∀ x : ZMod (u * v),
      ZMod.stdAddChar x
        = ZMod.stdAddChar ((A : ZMod u) * ZMod.castHom (dvd_mul_right u v) (ZMod u) x)
          * ZMod.stdAddChar ((B : ZMod v) * ZMod.castHom (dvd_mul_left v u) (ZMod v) x) := by
  set A : (ZMod u)ˣ := (ZMod.unitOfCoprime v huv.symm)⁻¹ with hA
  set B : (ZMod v)ˣ := (ZMod.unitOfCoprime u huv)⁻¹ with hB
  refine ⟨A, B, ?_⟩
  have hAv : (A : ZMod u) * (v : ZMod u) = 1 := by
    rw [hA, ← ZMod.coe_unitOfCoprime v huv.symm, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  have hBu : (B : ZMod v) * (u : ZMod v) = 1 := by
    rw [hB, ← ZMod.coe_unitOfCoprime u huv, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  -- both sides are additive characters; compare at 1
  set E₁ : AddChar (ZMod (u * v)) ℂ := ZMod.stdAddChar with hE₁
  set Eu : AddChar (ZMod (u * v)) ℂ :=
    (ZMod.stdAddChar.mulShift (A : ZMod u)).compAddMonoidHom
      (ZMod.castHom (dvd_mul_right u v) (ZMod u)).toAddMonoidHom with hEu
  set Ev : AddChar (ZMod (u * v)) ℂ :=
    (ZMod.stdAddChar.mulShift (B : ZMod v)).compAddMonoidHom
      (ZMod.castHom (dvd_mul_left v u) (ZMod v)).toAddMonoidHom with hEv
  suffices hmain : E₁ = Eu * Ev by
    intro x
    have := congrFun (congrArg (fun e : AddChar (ZMod (u * v)) ℂ => (e : ZMod (u * v) → ℂ)) hmain) x
    simpa [hE₁, hEu, hEv, AddChar.mul_apply, AddChar.compAddMonoidHom_apply,
      AddChar.mulShift_apply] using this
  refine addChar_zmod_ext ?_
  -- values at 1
  set na : ℕ := (A : ZMod u).val with hna
  set nb : ℕ := (B : ZMod v).val with hnb
  -- the key congruence: na·v + nb·u ≡ 1 (mod u·v)
  have hcong : ((na * v + nb * u : ℕ) : ZMod (u * v)) = ((1 : ℕ) : ZMod (u * v)) := by
    apply (ZMod.chineseRemainder huv).injective
    rw [map_natCast, map_natCast]
    apply Prod.ext
    · rw [Prod.fst_natCast, Prod.fst_natCast]
      push_cast
      rw [ZMod.natCast_self]
      rw [show ((na : ZMod u)) = (A : ZMod u) by rw [hna, ZMod.natCast_zmod_val]]
      rw [hAv]
      norm_num
    · rw [Prod.snd_natCast, Prod.snd_natCast]
      push_cast
      rw [ZMod.natCast_self]
      rw [show ((nb : ZMod v)) = (B : ZMod v) by rw [hnb, ZMod.natCast_zmod_val]]
      rw [hBu]
      norm_num
  have hmodeq : (na * v + nb * u) ≡ 1 [MOD u * v] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hcong
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (1 : ℤ) - ((na : ℤ) * v + nb * u) = (u * v) * k := by
    have h1 := (Nat.modEq_iff_dvd (n := u * v)).mp hmodeq
    obtain ⟨k, hk⟩ := h1
    refine ⟨k, ?_⟩
    push_cast at hk ⊢
    linarith
  -- evaluate both sides at 1
  have hu0 : (u : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne u)
  have hv0 : (v : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne v)
  have hlhs : E₁ (1 : ZMod (u * v)) = Complex.exp (2 * π * Complex.I * 1 / (u * v : ℕ)) := by
    rw [hE₁, show (1 : ZMod (u * v)) = ((1 : ℤ) : ZMod (u * v)) by norm_cast,
      ZMod.stdAddChar_coe]
    norm_num
  have hEu1 : Eu (1 : ZMod (u * v)) = Complex.exp (2 * π * Complex.I * na / u) := by
    rw [hEu, AddChar.compAddMonoidHom_apply, AddChar.mulShift_apply]
    have h2 : (ZMod.castHom (dvd_mul_right u v) (ZMod u)).toAddMonoidHom (1 : ZMod (u * v))
        = 1 := by
      simp
    rw [h2, mul_one, show ((A : ZMod u)) = ((na : ℤ) : ZMod u) by
      rw [hna]; push_cast; rw [ZMod.natCast_zmod_val], ZMod.stdAddChar_coe]
    norm_num
  have hEv1 : Ev (1 : ZMod (u * v)) = Complex.exp (2 * π * Complex.I * nb / v) := by
    rw [hEv, AddChar.compAddMonoidHom_apply, AddChar.mulShift_apply]
    have h2 : (ZMod.castHom (dvd_mul_left v u) (ZMod v)).toAddMonoidHom (1 : ZMod (u * v))
        = 1 := by
      simp
    rw [h2, mul_one, show ((B : ZMod v)) = ((nb : ℤ) : ZMod v) by
      rw [hnb]; push_cast; rw [ZMod.natCast_zmod_val], ZMod.stdAddChar_coe]
    norm_num
  rw [hlhs, AddChar.mul_apply, hEu1, hEv1, ← Complex.exp_add]
  rw [Complex.exp_eq_exp_iff_exists_int]
  refine ⟨k, ?_⟩
  have huv0 : ((u : ℂ) * v) ≠ 0 := mul_ne_zero hu0 hv0
  have hkC : ((na : ℂ) * v + nb * u) + k * (u * v) = 1 := by
    have h2 : ((1 : ℤ) - ((na : ℤ) * v + nb * u) : ℂ) = (((u * v) * k : ℤ) : ℂ) := by
      exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) hk
    push_cast at h2
    linear_combination -h2
  have hexpand : 2 * π * Complex.I * (na : ℂ) / u + 2 * π * Complex.I * nb / v
        + k * (2 * π * Complex.I)
      = 2 * π * Complex.I * ((((na : ℂ) * v + nb * u) + k * (u * v)) / (u * v)) := by
    field_simp
  rw [hexpand, hkC]
  push_cast
  ring

/-! ### CRT factorization of Gauss sums -/

section CRT

variable {u v : ℕ}

/-- The first CRT component is the cast. -/
lemma crt_fst (huv : Nat.Coprime u v) (x : ZMod (u * v)) :
    (ZMod.chineseRemainder huv x).1 = ZMod.castHom (dvd_mul_right u v) (ZMod u) x := by
  have h : (RingHom.fst (ZMod u) (ZMod v)).comp
        ((ZMod.chineseRemainder huv : ZMod (u * v) ≃+* ZMod u × ZMod v) :
          ZMod (u * v) →+* ZMod u × ZMod v)
      = ZMod.castHom (dvd_mul_right u v) (ZMod u) := RingHom.ext_zmod _ _
  exact congrFun (congrArg (fun f : ZMod (u * v) →+* ZMod u => (f : ZMod (u * v) → ZMod u)) h) x

/-- The second CRT component is the cast. -/
lemma crt_snd (huv : Nat.Coprime u v) (x : ZMod (u * v)) :
    (ZMod.chineseRemainder huv x).2 = ZMod.castHom (dvd_mul_left v u) (ZMod v) x := by
  have h : (RingHom.snd (ZMod u) (ZMod v)).comp
        ((ZMod.chineseRemainder huv : ZMod (u * v) ≃+* ZMod u × ZMod v) :
          ZMod (u * v) →+* ZMod u × ZMod v)
      = ZMod.castHom (dvd_mul_left v u) (ZMod v) := RingHom.ext_zmod _ _
  exact congrFun (congrArg (fun f : ZMod (u * v) →+* ZMod v => (f : ZMod (u * v) → ZMod v)) h) x

/-- Units of `ZMod (u·v)` are detected componentwise. -/
lemma isUnit_iff_casts (huv : Nat.Coprime u v) (x : ZMod (u * v)) :
    IsUnit x ↔ IsUnit (ZMod.castHom (dvd_mul_right u v) (ZMod u) x)
      ∧ IsUnit (ZMod.castHom (dvd_mul_left v u) (ZMod v) x) := by
  constructor
  · intro hx
    exact ⟨hx.map _, hx.map _⟩
  · rintro ⟨h1, h2⟩
    have h3 : IsUnit (ZMod.chineseRemainder huv x) := by
      rw [Prod.isUnit_iff, crt_fst huv x, crt_snd huv x]
      exact ⟨h1, h2⟩
    have h4 := h3.map (ZMod.chineseRemainder huv).symm.toRingHom
    simpa using h4

/-- Pointwise CRT splitting of a product of raised characters. -/
lemma changeLevel_mul_apply (huv : Nat.Coprime u v)
    (χ₁ : DirichletCharacter ℂ u) (χ₂ : DirichletCharacter ℂ v)
    (x : ZMod (u * v)) :
    (changeLevel (dvd_mul_right u v) χ₁ * changeLevel (dvd_mul_left v u) χ₂) x
      = χ₁ (ZMod.castHom (dvd_mul_right u v) (ZMod u) x)
        * χ₂ (ZMod.castHom (dvd_mul_left v u) (ZMod v) x) := by
  by_cases hx : IsUnit x
  · have hspec : (hx.unit : ZMod (u * v)) = x := hx.unit_spec
    rw [MulChar.mul_apply]
    congr 1
    · conv_lhs => rw [← hspec]
      rw [changeLevel_eq_cast_of_dvd χ₁ (dvd_mul_right u v) hx.unit, hspec,
        ZMod.castHom_apply]
    · conv_lhs => rw [← hspec]
      rw [changeLevel_eq_cast_of_dvd χ₂ (dvd_mul_left v u) hx.unit, hspec,
        ZMod.castHom_apply]
  · rw [MulChar.map_nonunit _ hx]
    rcases (not_and_or.mp (fun h => hx ((isUnit_iff_casts huv x).mpr h))) with h | h
    · rw [MulChar.map_nonunit χ₁ h, zero_mul]
    · rw [MulChar.map_nonunit χ₂ h, mul_zero]

/-- **CRT factorization of the Gauss sum** for a product of raised
characters at coprime levels, up to unit mul-shifts. -/
lemma gaussSum_crt [NeZero u] [NeZero v] [NeZero (u * v)] (huv : Nat.Coprime u v)
    (χ₁ : DirichletCharacter ℂ u) (χ₂ : DirichletCharacter ℂ v) :
    ∃ (A : (ZMod u)ˣ) (B : (ZMod v)ˣ),
      gaussSum (changeLevel (dvd_mul_right u v) χ₁ * changeLevel (dvd_mul_left v u) χ₂)
          ZMod.stdAddChar
        = gaussSum χ₁ (ZMod.stdAddChar.mulShift (A : ZMod u))
          * gaussSum χ₂ (ZMod.stdAddChar.mulShift (B : ZMod v)) := by
  obtain ⟨A, B, hAB⟩ := stdAddChar_crt (u := u) (v := v) huv
  refine ⟨A, B, ?_⟩
  set cu := ZMod.castHom (dvd_mul_right u v) (ZMod u) with hcu
  set cv := ZMod.castHom (dvd_mul_left v u) (ZMod v) with hcv
  have hterm : ∀ x : ZMod (u * v),
      (changeLevel (dvd_mul_right u v) χ₁ * changeLevel (dvd_mul_left v u) χ₂) x
          * ZMod.stdAddChar x
        = (χ₁ (cu x) * ZMod.stdAddChar ((A : ZMod u) * cu x))
          * (χ₂ (cv x) * ZMod.stdAddChar ((B : ZMod v) * cv x)) := by
    intro x
    rw [changeLevel_mul_apply huv, hAB x]
    ring
  rw [gaussSum, Finset.sum_congr rfl fun x _ => hterm x]
  -- reindex by the CRT equivalence and split the product sum
  calc ∑ x : ZMod (u * v),
        (χ₁ (cu x) * ZMod.stdAddChar ((A : ZMod u) * cu x))
          * (χ₂ (cv x) * ZMod.stdAddChar ((B : ZMod v) * cv x))
      = ∑ y : ZMod u × ZMod v,
          (χ₁ y.1 * ZMod.stdAddChar ((A : ZMod u) * y.1))
            * (χ₂ y.2 * ZMod.stdAddChar ((B : ZMod v) * y.2)) := by
        refine Fintype.sum_bijective _ (ZMod.chineseRemainder huv).bijective _ _ fun x => ?_
        rw [crt_fst huv x, crt_snd huv x]
    _ = (∑ y₁ : ZMod u, χ₁ y₁ * ZMod.stdAddChar ((A : ZMod u) * y₁))
          * (∑ y₂ : ZMod v, χ₂ y₂ * ZMod.stdAddChar ((B : ZMod v) * y₂)) := by
        rw [Finset.sum_mul_sum]
        exact Fintype.sum_prod_type _
    _ = gaussSum χ₁ (ZMod.stdAddChar.mulShift (A : ZMod u))
          * gaussSum χ₂ (ZMod.stdAddChar.mulShift (B : ZMod v)) := by
        rw [gaussSum, gaussSum]
        congr 1

end CRT

/-- Ramanujan block: the trivial-character Gauss sum at squarefree level
has norm 1 (it equals `μ(r)`). -/
lemma norm_gaussSum_one_squarefree :
    ∀ r : ℕ, ∀ [NeZero r], Squarefree r →
      ‖gaussSum (1 : DirichletCharacter ℂ r) ZMod.stdAddChar‖ = 1 := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro _ hsf
    have hr0 : r ≠ 0 := NeZero.ne r
    rcases eq_or_ne r 1 with rfl | hr1
    · have h1 : gaussSum (1 : DirichletCharacter ℂ 1) ZMod.stdAddChar = 1 := by
        rw [gaussSum, Fintype.sum_eq_single (0 : ZMod 1)
          (fun x hx => absurd (Subsingleton.elim x 0) hx)]
        rw [MulChar.one_apply (isUnit_of_subsingleton _), AddChar.map_zero_eq_one, one_mul]
      rw [h1, norm_one]
    · -- split off the least prime factor (with variables independent of `r`)
      obtain ⟨p, m, hp, hm0, rfl⟩ :
          ∃ p m, p.Prime ∧ m ≠ 0 ∧ r = p * m := by
        refine ⟨r.minFac, r / r.minFac, Nat.minFac_prime hr1, ?_, ?_⟩
        · intro h
          have := (Nat.mul_div_cancel' r.minFac_dvd).symm
          rw [h, mul_zero] at this
          exact hr0 this
        · exact (Nat.mul_div_cancel' r.minFac_dvd).symm
      have : NeZero p := ⟨hp.ne_zero⟩
      have : NeZero m := ⟨hm0⟩
      have hmdvd : m ∣ p * m := ⟨p, mul_comm p m⟩
      have hpm : ¬ p ∣ m := by
        intro hdvd
        obtain ⟨c, hc⟩ := hdvd
        have h2 : p * p ∣ p * m := ⟨c, by rw [hc]; ring⟩
        exact hp.ne_one (Nat.isUnit_iff.mp (hsf p h2))
      have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpm
      have hsfm : Squarefree m := hsf.squarefree_of_dvd hmdvd
      have hmlt : m < p * m := by
        have h2 : 2 ≤ p := hp.two_le
        have h3 : 0 < m := Nat.pos_of_ne_zero hm0
        nlinarith
      -- the CRT split at `p * m`
      have h1 : (1 : DirichletCharacter ℂ (p * m))
          = changeLevel (dvd_mul_right p m) (1 : DirichletCharacter ℂ p)
            * changeLevel (dvd_mul_left m p) (1 : DirichletCharacter ℂ m) := by
        rw [changeLevel_one, changeLevel_one, one_mul]
      obtain ⟨A, B, hAB⟩ := gaussSum_crt hcop
        (1 : DirichletCharacter ℂ p) (1 : DirichletCharacter ℂ m)
      have hshiftA : gaussSum (1 : DirichletCharacter ℂ p)
            (ZMod.stdAddChar.mulShift (A : ZMod p))
          = gaussSum (1 : DirichletCharacter ℂ p) ZMod.stdAddChar := by
        rw [gaussSum_mulShift_eq, inv_one, MulChar.one_apply_coe, one_mul]
      have hshiftB : gaussSum (1 : DirichletCharacter ℂ m)
            (ZMod.stdAddChar.mulShift (B : ZMod m))
          = gaussSum (1 : DirichletCharacter ℂ m) ZMod.stdAddChar := by
        rw [gaussSum_mulShift_eq, inv_one, MulChar.one_apply_coe, one_mul]
      -- prime block: the Gauss sum is −1
      have := Fact.mk hp
      have hne : (ZMod.stdAddChar : AddChar (ZMod p) ℂ) ≠ 1 := by
        intro h
        have h2 : ZMod.stdAddChar (1 : ZMod p) = ZMod.stdAddChar (0 : ZMod p) := by
          rw [h, AddChar.one_apply, AddChar.one_apply]
        exact one_ne_zero (ZMod.injective_stdAddChar h2)
      have hprime : ‖gaussSum (1 : DirichletCharacter ℂ p) ZMod.stdAddChar‖ = 1 := by
        rw [show gaussSum (1 : DirichletCharacter ℂ p) ZMod.stdAddChar
            = gaussSum (1 : MulChar (ZMod p) ℂ) ZMod.stdAddChar from rfl,
          gaussSum_one_left hne, norm_neg, norm_one]
      -- assemble
      rw [h1, hAB, norm_mul, hshiftA, hshiftB, hprime, one_mul]
      exact ih m hmlt hsfm

/-- **The induced-character Gauss sum** (File 2's designated risk item):
for `ψ` primitive mod `f`, raising the level by a squarefree coprime `r`
preserves the Gauss-sum modulus: `‖τ(changeLevel ψ)‖² = f`. -/
lemma norm_sq_gaussSum_changeLevel {f r : ℕ} [NeZero f] [NeZero r] [NeZero (r * f)]
    (hr : Squarefree r) (hrf : Nat.Coprime r f)
    {ψ : DirichletCharacter ℂ f} (hψ : ψ.IsPrimitive) :
    ‖gaussSum (changeLevel (dvd_mul_left f r) ψ) ZMod.stdAddChar‖ ^ 2 = f := by
  have h1 : changeLevel (dvd_mul_left f r) ψ
      = changeLevel (dvd_mul_right r f) (1 : DirichletCharacter ℂ r)
        * changeLevel (dvd_mul_left f r) ψ := by
    rw [changeLevel_one, one_mul]
  rw [h1]
  obtain ⟨A, B, hAB⟩ := gaussSum_crt hrf (1 : DirichletCharacter ℂ r) ψ
  rw [hAB, norm_mul, mul_pow]
  have hA : ‖gaussSum (1 : DirichletCharacter ℂ r)
      (ZMod.stdAddChar.mulShift (A : ZMod r))‖ = 1 := by
    rw [gaussSum_mulShift_eq, inv_one, MulChar.one_apply_coe, one_mul]
    exact norm_gaussSum_one_squarefree r hr
  have hB : ‖gaussSum ψ (ZMod.stdAddChar.mulShift (B : ZMod f))‖ ^ 2 = f := by
    rw [gaussSum_mulShift_eq, norm_mul, mul_pow]
    have h2 : ‖ψ⁻¹ (B : ZMod f)‖ = 1 := (ψ⁻¹).unit_norm_eq_one B
    rw [h2, one_pow, one_mul]
    exact norm_sq_gaussSum_primitive hψ
  rw [hA, hB, one_pow, one_mul]

/-! ### The multiplicative transfer and unit-group Parseval -/

/-- **Gauss-sum transfer**: for coefficients supported on integers that are
units mod `q`, the character-twisted average of the additive evaluations is
`τ(χ)` times the `χ⁻¹`-twisted sum. -/
lemma char_twisted_sum_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {κ : Type*} (s' : Finset κ) (c : κ → ℂ) (nn : κ → ℕ)
    (hcop : ∀ i ∈ s', IsUnit ((nn i : ZMod q))) :
    ∑ u : (ZMod q)ˣ, χ u *
        (∑ i ∈ s', c i * ZMod.stdAddChar ((nn i : ZMod q) * (u : ZMod q)))
      = gaussSum χ ZMod.stdAddChar * ∑ i ∈ s', c i * χ⁻¹ ((nn i : ZMod q)) := by
  have hswap : ∑ u : (ZMod q)ˣ, χ u *
        (∑ i ∈ s', c i * ZMod.stdAddChar ((nn i : ZMod q) * (u : ZMod q)))
      = ∑ i ∈ s', c i *
          ∑ u : (ZMod q)ˣ, χ u * ZMod.stdAddChar ((nn i : ZMod q) * (u : ZMod q)) := by
    calc ∑ u : (ZMod q)ˣ, χ u *
          (∑ i ∈ s', c i * ZMod.stdAddChar ((nn i : ZMod q) * (u : ZMod q)))
        = ∑ u : (ZMod q)ˣ, ∑ i ∈ s',
            c i * (χ u * ZMod.stdAddChar ((nn i : ZMod q) * (u : ZMod q))) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i ∈ s', ∑ u : (ZMod q)ˣ,
            c i * (χ u * ZMod.stdAddChar ((nn i : ZMod q) * (u : ZMod q))) :=
          Finset.sum_comm
      _ = ∑ i ∈ s', c i *
            ∑ u : (ZMod q)ˣ, χ u * ZMod.stdAddChar ((nn i : ZMod q) * (u : ZMod q)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  rw [hswap]
  have hinner : ∀ i ∈ s',
      ∑ u : (ZMod q)ˣ, χ u * ZMod.stdAddChar ((nn i : ZMod q) * (u : ZMod q))
        = χ⁻¹ ((nn i : ZMod q)) * gaussSum χ ZMod.stdAddChar := by
    intro i hi
    have h1 : ∑ u : (ZMod q)ˣ, χ u * ZMod.stdAddChar ((nn i : ZMod q) * (u : ZMod q))
        = ∑ x : ZMod q, χ x * ZMod.stdAddChar ((nn i : ZMod q) * x) :=
      (sum_units_eq (fun x => χ x * ZMod.stdAddChar ((nn i : ZMod q) * x))
        (fun x hx => by rw [χ.map_nonunit hx, zero_mul])).symm
    have h2 : ∑ x : ZMod q, χ x * ZMod.stdAddChar ((nn i : ZMod q) * x)
        = gaussSum χ (ZMod.stdAddChar.mulShift ((nn i : ZMod q))) := rfl
    have hu := hcop i hi
    have h3 : gaussSum χ (ZMod.stdAddChar.mulShift ((nn i : ZMod q)))
        = χ⁻¹ ((nn i : ZMod q)) * gaussSum χ ZMod.stdAddChar := by
      have h4 := gaussSum_mulShift_eq χ ZMod.stdAddChar hu.unit
      rw [IsUnit.unit_spec] at h4
      exact h4
    rw [h1, h2, h3]
  have hfinal : ∑ i ∈ s', c i *
        ∑ u : (ZMod q)ˣ, χ u * ZMod.stdAddChar ((nn i : ZMod q) * (u : ZMod q))
      = ∑ i ∈ s', c i * (χ⁻¹ ((nn i : ZMod q)) * gaussSum χ ZMod.stdAddChar) :=
    Finset.sum_congr rfl fun i hi => by rw [hinner i hi]
  rw [hfinal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Unit-group Parseval**: summing the squared character-linear forms over
all Dirichlet characters mod `q` gives `φ(q)` times the coefficient mass. -/
lemma parseval_units {q : ℕ} [NeZero q] (G : (ZMod q)ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ u * G u‖ ^ 2
      = q.totient * ∑ u : (ZMod q)ˣ, ‖G u‖ ^ 2 := by
  have hchar : ∀ u v : (ZMod q)ˣ,
      ∑ χ : DirichletCharacter ℂ q, (G u * conj (G v)) * (χ u * conj (χ v))
        = (G u * conj (G v)) * (if u = v then (q.totient : ℂ) else 0) := by
    intro u v
    rw [← Finset.mul_sum]
    have h := Carmichael.MeanValue.sum_char_mul_conj ((u : ZMod q)) ((v : ZMod q))
    rw [show (∑ χ : DirichletCharacter ℂ q, χ u * conj (χ v))
        = (if ((u : ZMod q) = (v : ZMod q) ∧ IsUnit ((v : ZMod q) : ZMod q))
          then ((q.totient : ℕ) : ℂ) else 0) from h]
    congr 1
    by_cases hp : u = v
    · rw [if_pos ⟨by rw [hp], v.isUnit⟩, if_pos hp]
    · rw [if_neg (fun h2 => hp (Units.ext h2.1)), if_neg hp]
  have hC : ∑ χ : DirichletCharacter ℂ q,
        (∑ u : (ZMod q)ˣ, χ u * G u) * conj (∑ v : (ZMod q)ˣ, χ v * G v)
      = (q.totient : ℂ) * ∑ u : (ZMod q)ˣ, G u * conj (G u) := by
    have hexp : ∀ χ : DirichletCharacter ℂ q,
        (∑ u : (ZMod q)ˣ, χ u * G u) * conj (∑ v : (ZMod q)ˣ, χ v * G v)
          = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
              (G u * conj (G v)) * (χ u * conj (χ v)) := by
      intro χ
      rw [map_sum, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
        rw [map_mul]; ring
    rw [Finset.sum_congr rfl fun χ _ => hexp χ, Finset.sum_comm]
    rw [Finset.sum_congr rfl fun u (_ : u ∈ Finset.univ) => Finset.sum_comm]
    rw [Finset.sum_congr rfl fun u (_ : u ∈ Finset.univ) =>
      Finset.sum_congr rfl fun v (_ : v ∈ Finset.univ) => hchar u v]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_eq_single u]
    · rw [if_pos rfl]
      ring
    · intro v _ hv
      rw [if_neg (Ne.symm hv), mul_zero]
    · intro hu
      exact absurd (Finset.mem_univ u) hu
  have hre := congrArg Complex.re hC
  rw [Complex.re_sum] at hre
  calc ∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ u * G u‖ ^ 2
      = ∑ χ : DirichletCharacter ℂ q,
          ((∑ u : (ZMod q)ˣ, χ u * G u) * conj (∑ v : (ZMod q)ˣ, χ v * G v)).re :=
        Finset.sum_congr rfl fun χ _ => norm_sq_eq_mul_conj_re _
    _ = ((q.totient : ℂ) * ∑ u : (ZMod q)ˣ, G u * conj (G u)).re := hre
    _ = q.totient * ∑ u : (ZMod q)ˣ, ‖G u‖ ^ 2 := by
        rw [Complex.mul_re]
        have h1 : (∑ u : (ZMod q)ˣ, G u * conj (G u)).im = 0 := by
          rw [Complex.im_sum]
          refine Finset.sum_eq_zero fun u _ => ?_
          rw [Complex.mul_conj]
          simp
        have h2 : (∑ u : (ZMod q)ˣ, G u * conj (G u)).re
            = ∑ u : (ZMod q)ˣ, ‖G u‖ ^ 2 := by
          rw [Complex.re_sum]
          exact Finset.sum_congr rfl fun u _ => (norm_sq_eq_mul_conj_re _).symm
        rw [h1, h2]
        simp

/-! ### The unit-period exponential and finite Parseval -/

/-- The exponential `e(νβ) = exp(2πiνβ)` with integer frequency. -/
noncomputable def eAt (ν : ℤ) (β : ℝ) : ℂ :=
  Complex.exp (((2 * π * ν) * β : ℝ) * Complex.I)

lemma continuous_eAt (ν : ℤ) : Continuous (eAt ν) := by
  unfold eAt
  fun_prop

lemma hasDerivAt_eAt (ν : ℤ) (β : ℝ) :
    HasDerivAt (eAt ν) ((((2 * π * ν : ℝ) : ℂ) * Complex.I) * eAt ν β) β :=
  MeanValue.hasDerivAt_exp_mul_I (2 * π * ν) β

lemma norm_eAt (ν : ℤ) (β : ℝ) : ‖eAt ν β‖ = 1 := by
  unfold eAt
  exact Complex.norm_exp_ofReal_mul_I _

/-- Period-1 orthogonality: the integral of `e(νβ)` over any unit interval
is `1` for `ν = 0` and `0` otherwise. -/
lemma integral_eAt (ν : ℤ) (c : ℝ) :
    ∫ β in c..(c + 1), eAt ν β = if ν = 0 then 1 else 0 := by
  split_ifs with hν
  · subst hν
    have h1 : ∀ β : ℝ, eAt 0 β = 1 := by
      intro β
      unfold eAt
      norm_num
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℂ)) (fun β _ => h1 β)]
    simp
  · have hνR : (2 * π * (ν : ℝ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (Int.cast_ne_zero.mpr hν)
    have hc0 : (((2 * π * ν : ℝ) : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (Complex.ofReal_ne_zero.mpr hνR) Complex.I_ne_zero
    have hF : ∀ β : ℝ, HasDerivAt (fun t => eAt ν t / (((2 * π * ν : ℝ) : ℂ) * Complex.I))
        (eAt ν β) β := by
      intro β
      have h2 := (hasDerivAt_eAt ν β).div_const (((2 * π * ν : ℝ) : ℂ) * Complex.I)
      have h3 : (((2 * π * ν : ℝ) : ℂ) * Complex.I) * eAt ν β
          / (((2 * π * ν : ℝ) : ℂ) * Complex.I) = eAt ν β := by
        field_simp
      rwa [h3] at h2
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun β _ => hF β)
      ((continuous_eAt ν).intervalIntegrable _ _)]
    have hper : eAt ν (c + 1) = eAt ν c := by
      unfold eAt
      rw [show (((2 * π * ν) * (c + 1) : ℝ) : ℂ) * Complex.I
          = ((2 * π * ν) * c : ℝ) * Complex.I + (ν : ℂ) * (2 * π * Complex.I) by
        push_cast; ring]
      rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hper, sub_self]

/-- **Finite Parseval over a unit period** (deliverable 1): for distinct
integer frequencies, `∫_c^{c+1} ‖∑ wₖ e(νₖβ)‖² dβ = ∑ ‖wₖ‖²`. -/
lemma parseval_period {κ : Type*} (s' : Finset κ) (w : κ → ℂ) (ν : κ → ℤ)
    (hinj : ∀ i ∈ s', ∀ j ∈ s', ν i = ν j → i = j) (c : ℝ) :
    ∫ β in c..(c + 1), ‖∑ i ∈ s', w i * eAt (ν i) β‖ ^ 2 = ∑ i ∈ s', ‖w i‖ ^ 2 := by
  have hpt : ∀ β : ℝ, ((‖∑ i ∈ s', w i * eAt (ν i) β‖ ^ 2 : ℝ) : ℂ)
      = ∑ i ∈ s', ∑ j ∈ s', (w i * conj (w j)) * eAt (ν i - ν j) β := by
    intro β
    have h1 : ((‖∑ i ∈ s', w i * eAt (ν i) β‖ ^ 2 : ℝ) : ℂ)
        = (∑ i ∈ s', w i * eAt (ν i) β) * conj (∑ j ∈ s', w j * eAt (ν j) β) := by
      rw [Complex.mul_conj, ← Complex.normSq_eq_norm_sq]
    rw [h1, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    have h2 : eAt (ν i) β * conj (eAt (ν j) β) = eAt (ν i - ν j) β := by
      unfold eAt
      rw [MeanValue.exp_mul_conj_exp]
      congr 2
      push_cast
      ring
    calc w i * eAt (ν i) β * (conj (w j) * conj (eAt (ν j) β))
        = (w i * conj (w j)) * (eAt (ν i) β * conj (eAt (ν j) β)) := by ring
      _ = (w i * conj (w j)) * eAt (ν i - ν j) β := by rw [h2]
  have hint1 : ∀ i j : κ,
      IntervalIntegrable (fun β => (w i * conj (w j)) * eAt (ν i - ν j) β)
        MeasureTheory.volume c (c + 1) :=
    fun i j => ((continuous_eAt _).const_mul _).intervalIntegrable _ _
  have hint2 : ∀ i : κ,
      IntervalIntegrable (fun β => ∑ j ∈ s', (w i * conj (w j)) * eAt (ν i - ν j) β)
        MeasureTheory.volume c (c + 1) :=
    fun i => (continuous_finsetSum _ fun j _ =>
      (continuous_eAt _).const_mul _).intervalIntegrable _ _
  have hC : ∫ β in c..(c + 1), ((‖∑ i ∈ s', w i * eAt (ν i) β‖ ^ 2 : ℝ) : ℂ)
      = ((∑ i ∈ s', ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_congr (fun β _ => hpt β)]
    rw [intervalIntegral.integral_finsetSum (fun i _ => hint2 i)]
    have hone : ∀ i ∈ s',
        (∫ β in c..(c + 1), ∑ j ∈ s', (w i * conj (w j)) * eAt (ν i - ν j) β)
          = w i * conj (w i) := by
      intro i hi
      rw [intervalIntegral.integral_finsetSum (fun j _ => hint1 i j)]
      have hterm : ∀ j ∈ s', (∫ β in c..(c + 1), (w i * conj (w j)) * eAt (ν i - ν j) β)
          = if j = i then w i * conj (w i) else 0 := by
        intro j hj
        rw [intervalIntegral.integral_const_mul, integral_eAt]
        by_cases hji : j = i
        · subst hji
          rw [if_pos (sub_self (ν j)), if_pos rfl, mul_one]
        · rw [if_neg (fun h : ν i - ν j = 0 => hji (hinj j hj i hi (by omega))),
            if_neg hji, mul_zero]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s' i]
      rw [if_pos hi]
    rw [Finset.sum_congr rfl hone, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h3 : ((∫ β in c..(c + 1), ‖∑ i ∈ s', w i * eAt (ν i) β‖ ^ 2 : ℝ) : ℂ)
      = ((∑ i ∈ s', ‖w i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    exact hC
  exact_mod_cast h3

/-! ### The Sobolev localization step -/

/-- **Gallagher–Sobolev pointwise bound**: for continuously differentiable
`f : ℝ → ℂ` and any `δ > 0`,
`‖f(α)‖² ≤ δ⁻¹∫_J ‖f‖² + ∫_J 2‖f‖‖f′‖` over `J = [α − δ/2, α + δ/2]`. -/
lemma sobolev_sq_le {f f' : ℝ → ℂ} (hderiv : ∀ β, HasDerivAt f (f' β) β)
    (hf : Continuous f) (hf' : Continuous f') {δ : ℝ} (hδ : 0 < δ) (α : ℝ) :
    ‖f α‖ ^ 2 ≤ (1 / δ) * (∫ β in (α - δ / 2)..(α + δ / 2), ‖f β‖ ^ 2)
      + ∫ β in (α - δ / 2)..(α + δ / 2), 2 * ‖f β‖ * ‖f' β‖ := by
  set g : ℝ → ℝ := fun β => ‖f β‖ ^ 2 with hgdef
  set g' : ℝ → ℝ := fun β => 2 * (f' β * conj (f β)).re with hg'def
  have hgc : Continuous g := (hf.norm.pow 2)
  have hg'c : Continuous g' := by
    have h1 : Continuous fun β => f' β * conj (f β) :=
      hf'.mul (Complex.continuous_conj.comp hf)
    exact (Complex.continuous_re.comp h1).const_mul 2
  have hgderiv : ∀ β, HasDerivAt g (g' β) β := by
    intro β
    have hconj : HasDerivAt (fun t => conj (f t)) (conj (f' β)) β := by
      simpa only [starRingEnd_apply] using (hderiv β).star
    have hprod : HasDerivAt (fun t => f t * conj (f t))
        (f' β * conj (f β) + f β * conj (f' β)) β := (hderiv β).mul hconj
    have hre : HasDerivAt (fun t => (f t * conj (f t)).re)
        ((f' β * conj (f β) + f β * conj (f' β)).re) β :=
      (Complex.reCLM.hasFDerivAt.comp_hasDerivAt β hprod)
    have heq : (fun t => (f t * conj (f t)).re) = g := by
      funext t
      rw [hgdef]
      exact (norm_sq_eq_mul_conj_re (f t)).symm
    have heq2 : (f' β * conj (f β) + f β * conj (f' β)).re = g' β := by
      rw [hg'def]
      have h2 : f β * conj (f' β) = conj (f' β * conj (f β)) := by
        rw [map_mul, Complex.conj_conj]
        ring
      rw [h2, Complex.add_re, Complex.conj_re]
      ring
    rw [← heq, ← heq2]
    exact hre
  have habs : ∀ β, |g' β| ≤ 2 * ‖f β‖ * ‖f' β‖ := by
    intro β
    rw [hg'def]
    have h1 : |(f' β * conj (f β)).re| ≤ ‖f' β * conj (f β)‖ := Complex.abs_re_le_norm _
    rw [norm_mul, Complex.norm_conj] at h1
    rw [abs_mul, abs_two]
    calc 2 * |(f' β * conj (f β)).re| ≤ 2 * (‖f' β‖ * ‖f β‖) := by linarith
      _ = 2 * ‖f β‖ * ‖f' β‖ := by ring
  set a : ℝ := α - δ / 2 with hadef
  set b : ℝ := α + δ / 2 with hbdef
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have hg'int : IntervalIntegrable g' MeasureTheory.volume a b :=
    hg'c.intervalIntegrable _ _
  have hhint : IntervalIntegrable (fun β => 2 * ‖f β‖ * ‖f' β‖) MeasureTheory.volume a b :=
    ((hf.norm.const_mul 2).mul hf'.norm).intervalIntegrable _ _
  -- the derivative-mass over J bounds the oscillation of g inside J
  have hosc : ∀ β ∈ Set.Icc a b, g α ≤ g β + ∫ t in a..b, 2 * ‖f t‖ * ‖f' t‖ := by
    intro β hβ
    have hαJ : α ∈ Set.Icc a b := by
      constructor <;> [rw [hadef]; rw [hbdef]] <;> linarith
    have hftc : ∫ t in β..α, g' t = g α - g β :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hgderiv t)
        (hg'c.intervalIntegrable _ _)
    have hmono : ∫ t in β..α, g' t ≤ ∫ t in a..b, 2 * ‖f t‖ * ‖f' t‖ := by
      have h2 : ∫ t in β..α, g' t ≤ |∫ t in β..α, g' t| := le_abs_self _
      have h3 : |∫ t in β..α, g' t| ≤ abs (∫ t in β..α, |g' t|) := by
        have := intervalIntegral.norm_integral_le_abs_integral_norm
          (f := g') (a := β) (b := α) (μ := MeasureTheory.volume)
        simpa [Real.norm_eq_abs] using this
      have h4 : abs (∫ t in β..α, |g' t|) ≤ ∫ t in a..b, |g' t| := by
        rcases le_total β α with hle | hle
        · rw [abs_of_nonneg (intervalIntegral.integral_nonneg hle fun t _ => abs_nonneg _)]
          exact intervalIntegral.integral_mono_interval hβ.1 hle hαJ.2
            (Filter.Eventually.of_forall fun t => abs_nonneg _)
            (hg'c.abs.intervalIntegrable _ _)
        · rw [intervalIntegral.integral_symm α β, abs_neg,
            abs_of_nonneg (intervalIntegral.integral_nonneg hle fun t _ => abs_nonneg _)]
          exact intervalIntegral.integral_mono_interval hαJ.1 hle hβ.2
            (Filter.Eventually.of_forall fun t => abs_nonneg _)
            (hg'c.abs.intervalIntegrable _ _)
      have h5 : ∫ t in a..b, |g' t| ≤ ∫ t in a..b, 2 * ‖f t‖ * ‖f' t‖ :=
        intervalIntegral.integral_mono_on hab (hg'c.abs.intervalIntegrable _ _)
          hhint fun t _ => habs t
      linarith
    linarith [hftc ▸ hmono]
  -- average over β ∈ J
  set C : ℝ := ∫ t in a..b, 2 * ‖f t‖ * ‖f' t‖ with hCdef
  have havg : δ * g α ≤ (∫ β in a..b, g β) + δ * C := by
    have h1 : ∫ (_ : ℝ) in a..b, g α = δ * g α := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      congr 1
      rw [hadef, hbdef]
      ring
    have h2 : (∫ β in a..b, (g β + C)) = (∫ β in a..b, g β) + δ * C := by
      rw [intervalIntegral.integral_add (hgc.intervalIntegrable _ _)
        (intervalIntegrable_const), intervalIntegral.integral_const, smul_eq_mul]
      congr 2
      rw [hadef, hbdef]
      ring
    have h3 : (∫ (_ : ℝ) in a..b, g α) ≤ ∫ β in a..b, (g β + C) := by
      refine intervalIntegral.integral_mono_on hab intervalIntegrable_const
        ((hgc.intervalIntegrable _ _).add intervalIntegrable_const) ?_
      intro β hβ
      exact hosc β hβ
    rw [h1] at h3
    rw [h2] at h3
    exact h3
  have hδ' : 0 < 1 / δ := by positivity
  have hfin := mul_le_mul_of_nonneg_left havg hδ'.le
  rw [← mul_assoc] at hfin
  rw [one_div_mul_cancel hδ.ne', one_mul] at hfin
  calc ‖f α‖ ^ 2 = g α := rfl
    _ ≤ 1 / δ * ((∫ β in a..b, g β) + δ * C) := hfin
    _ = (1 / δ) * (∫ β in a..b, g β) + C := by
        field_simp
    _ = (1 / δ) * (∫ β in (α - δ / 2)..(α + δ / 2), ‖f β‖ ^ 2)
        + ∫ β in (α - δ / 2)..(α + δ / 2), 2 * ‖f β‖ * ‖f' β‖ := rfl

/-! ### The additive large sieve over separated points -/

/-- **Additive large sieve** (deliverable 2): for a family of `δ`-separated
points in `[0, 1 − δ]` and integer frequencies of size at most `F`,

  `∑_α ‖∑ wₖ e(νₖ α)‖² ≤ (1/δ + 4πF) ∑ ‖wₖ‖²`. -/
lemma points_large_sieve {ι : Type*} (P : Finset ι) (α : ι → ℝ) {δ : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → δ ≤ |α i - α j|)
    (hrange : ∀ i ∈ P, 0 ≤ α i ∧ α i ≤ 1 - δ)
    {κ : Type*} (s' : Finset κ) (w : κ → ℂ) (ν : κ → ℤ)
    (hinj : ∀ i ∈ s', ∀ j ∈ s', ν i = ν j → i = j)
    {F : ℝ} (hF : 0 < F) (hνF : ∀ k ∈ s', |(ν k : ℝ)| ≤ F) :
    ∑ i ∈ P, ‖∑ k ∈ s', w k * eAt (ν k) (α i)‖ ^ 2
      ≤ (1 / δ + 4 * π * F) * ∑ k ∈ s', ‖w k‖ ^ 2 := by
  set f : ℝ → ℂ := fun β => ∑ k ∈ s', w k * eAt (ν k) β with hfdef
  set w' : κ → ℂ := fun k => w k * (((2 * π * (ν k) : ℝ) : ℂ) * Complex.I) with hw'def
  set f' : ℝ → ℂ := fun β => ∑ k ∈ s', w' k * eAt (ν k) β with hf'def
  set SW : ℝ := ∑ k ∈ s', ‖w k‖ ^ 2 with hSWdef
  have hSW0 : 0 ≤ SW := Finset.sum_nonneg fun k _ => by positivity
  have hderiv : ∀ β, HasDerivAt f (f' β) β := by
    intro β
    have h1 : HasDerivAt f
        (∑ k ∈ s', w k * ((((2 * π * (ν k) : ℝ)) : ℂ) * Complex.I * eAt (ν k) β)) β :=
      HasDerivAt.fun_sum (fun k _ => (hasDerivAt_eAt (ν k) β).const_mul (w k))
    have h2 : (∑ k ∈ s', w k * ((((2 * π * (ν k) : ℝ)) : ℂ) * Complex.I * eAt (ν k) β))
        = f' β := by
      rw [hf'def]
      exact Finset.sum_congr rfl fun k _ => by rw [hw'def]; ring
    rw [h2] at h1
    exact h1
  have hfc : Continuous f := by
    rw [hfdef]
    exact continuous_finsetSum _ fun k _ => (continuous_eAt (ν k)).const_mul (w k)
  have hf'c : Continuous f' := by
    rw [hf'def]
    exact continuous_finsetSum _ fun k _ => (continuous_eAt (ν k)).const_mul (w' k)
  -- disjoint-interval summation of nonnegative integrals
  have hdisj : ∀ h : ℝ → ℝ, Continuous h → (∀ β, 0 ≤ h β) →
      ∑ i ∈ P, (∫ β in (α i - δ / 2)..(α i + δ / 2), h β)
        ≤ ∫ β in (-(δ / 2))..(1 - δ / 2), h β := by
    intro h hc hnn
    have hIoc : ∀ i ∈ P, (∫ β in (α i - δ / 2)..(α i + δ / 2), h β)
        = ∫ β in Set.Ioc (α i - δ / 2) (α i + δ / 2), h β :=
      fun i _ => intervalIntegral.integral_of_le (by linarith)
    rw [Finset.sum_congr rfl hIoc]
    have hpair : (↑P : Set ι).Pairwise
        (Function.onFun Disjoint (fun i => Set.Ioc (α i - δ / 2) (α i + δ / 2))) := by
      intro i hi j hj hij
      have hs := hsep i (Finset.mem_coe.mp hi) j (Finset.mem_coe.mp hj) hij
      have hcase : δ ≤ α i - α j ∨ δ ≤ α j - α i := by
        rcases abs_cases (α i - α j) with ⟨he, _⟩ | ⟨he, _⟩
        · left; linarith
        · right; linarith
      rw [Function.onFun, Set.Ioc_disjoint_Ioc]
      rcases hcase with hcs | hcs
      · calc min (α i + δ / 2) (α j + δ / 2) ≤ α j + δ / 2 := min_le_right _ _
          _ ≤ α i - δ / 2 := by linarith
          _ ≤ max (α i - δ / 2) (α j - δ / 2) := le_max_left _ _
      · calc min (α i + δ / 2) (α j + δ / 2) ≤ α i + δ / 2 := min_le_left _ _
          _ ≤ α j - δ / 2 := by linarith
          _ ≤ max (α i - δ / 2) (α j - δ / 2) := le_max_right _ _
    rw [← MeasureTheory.integral_biUnion_finset P (fun i _ => measurableSet_Ioc) hpair
      (fun i _ => (hc.intervalIntegrable _ _).1)]
    have hsub : (⋃ i ∈ P, Set.Ioc (α i - δ / 2) (α i + δ / 2))
        ⊆ Set.Ioc (-(δ / 2)) (1 - δ / 2) := by
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨i, hi, hx⟩ := hx
      obtain ⟨hr1, hr2⟩ := hrange i hi
      obtain ⟨hx1, hx2⟩ := hx
      exact ⟨by linarith, by linarith⟩
    rw [intervalIntegral.integral_of_le (by linarith : -(δ / 2) ≤ 1 - δ / 2)]
    exact MeasureTheory.setIntegral_mono_set ((hc.intervalIntegrable _ _).1)
      (Filter.Eventually.of_forall fun β => hnn β) hsub.eventuallyLE
  -- Parseval on the length-1 interval, for both `f` and `f'`
  have hpars : (∫ β in (-(δ / 2))..(1 - δ / 2), ‖f β‖ ^ 2) = SW := by
    have h1 : (1 - δ / 2 : ℝ) = -(δ / 2) + 1 := by ring
    rw [hfdef, hSWdef, h1]
    exact parseval_period s' w ν hinj (-(δ / 2))
  have hpars' : (∫ β in (-(δ / 2))..(1 - δ / 2), ‖f' β‖ ^ 2)
      ≤ 4 * π ^ 2 * F ^ 2 * SW := by
    have h1 : (1 - δ / 2 : ℝ) = -(δ / 2) + 1 := by ring
    have h2 : (∫ β in (-(δ / 2))..(1 - δ / 2), ‖f' β‖ ^ 2) = ∑ k ∈ s', ‖w' k‖ ^ 2 := by
      rw [hf'def, h1]
      exact parseval_period s' w' ν hinj (-(δ / 2))
    rw [h2]
    have h3 : ∀ k ∈ s', ‖w' k‖ ^ 2 ≤ 4 * π ^ 2 * F ^ 2 * ‖w k‖ ^ 2 := by
      intro k hk
      rw [hw'def]
      have h4 : ‖w k * (((2 * π * (ν k) : ℝ) : ℂ) * Complex.I)‖
          = ‖w k‖ * |2 * π * (ν k : ℝ)| := by
        rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_eq_abs]
      rw [h4, mul_pow, sq_abs]
      have h5 : (2 * π * (ν k : ℝ)) ^ 2 ≤ 4 * π ^ 2 * F ^ 2 := by
        have h6 := hνF k hk
        have h7 : (ν k : ℝ) ^ 2 ≤ F ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h6 2
        nlinarith [Real.pi_pos]
      nlinarith [norm_nonneg (w k), sq_nonneg (‖w k‖)]
    calc ∑ k ∈ s', ‖w' k‖ ^ 2 ≤ ∑ k ∈ s', 4 * π ^ 2 * F ^ 2 * ‖w k‖ ^ 2 :=
          Finset.sum_le_sum h3
      _ = 4 * π ^ 2 * F ^ 2 * SW := by rw [hSWdef, Finset.mul_sum]
  -- the Sobolev bound at each point, summed
  have hsob : ∑ i ∈ P, ‖f (α i)‖ ^ 2
      ≤ (1 / δ) * ∑ i ∈ P, (∫ β in (α i - δ / 2)..(α i + δ / 2), ‖f β‖ ^ 2)
        + ∑ i ∈ P, (∫ β in (α i - δ / 2)..(α i + δ / 2), 2 * ‖f β‖ * ‖f' β‖) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => sobolev_sq_le hderiv hfc hf'c hδ (α i)
  -- AM–GM under the integral for the cross term
  set θ : ℝ := 2 * π * F with hθdef
  have hθ : 0 < θ := by
    rw [hθdef]
    positivity
  have hAMGM : (∫ β in (-(δ / 2))..(1 - δ / 2), 2 * ‖f β‖ * ‖f' β‖)
      ≤ θ * SW + θ⁻¹ * (4 * π ^ 2 * F ^ 2 * SW) := by
    have hpt : ∀ β, 2 * ‖f β‖ * ‖f' β‖ ≤ θ * ‖f β‖ ^ 2 + θ⁻¹ * ‖f' β‖ ^ 2 := by
      intro β
      have h1 := sq_nonneg (θ * ‖f β‖ - ‖f' β‖)
      have h2 : 0 < θ⁻¹ := inv_pos.mpr hθ
      have h3 : θ * θ⁻¹ = 1 := mul_inv_cancel₀ hθ.ne'
      nlinarith [h1, h2, h3, sq_nonneg (‖f' β‖)]
    have hi1 : IntervalIntegrable (fun β => θ * ‖f β‖ ^ 2)
        MeasureTheory.volume (-(δ / 2)) (1 - δ / 2) :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    have hi2 : IntervalIntegrable (fun β => θ⁻¹ * ‖f' β‖ ^ 2)
        MeasureTheory.volume (-(δ / 2)) (1 - δ / 2) :=
      Continuous.intervalIntegrable (by fun_prop) _ _
    have h4 : (∫ β in (-(δ / 2))..(1 - δ / 2), 2 * ‖f β‖ * ‖f' β‖)
        ≤ ∫ β in (-(δ / 2))..(1 - δ / 2), (θ * ‖f β‖ ^ 2 + θ⁻¹ * ‖f' β‖ ^ 2) := by
      refine intervalIntegral.integral_mono_on (by linarith)
        (Continuous.intervalIntegrable (by fun_prop) _ _) (hi1.add hi2) ?_
      intro β _
      exact hpt β
    have h5 : (∫ β in (-(δ / 2))..(1 - δ / 2), (θ * ‖f β‖ ^ 2 + θ⁻¹ * ‖f' β‖ ^ 2))
        = θ * (∫ β in (-(δ / 2))..(1 - δ / 2), ‖f β‖ ^ 2)
          + θ⁻¹ * (∫ β in (-(δ / 2))..(1 - δ / 2), ‖f' β‖ ^ 2) := by
      rw [intervalIntegral.integral_add hi1 hi2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rw [h5, hpars] at h4
    refine h4.trans ?_
    have h6 : (∫ β in (-(δ / 2))..(1 - δ / 2), ‖f' β‖ ^ 2) ≤ 4 * π ^ 2 * F ^ 2 * SW :=
      hpars'
    have h7 : 0 < θ⁻¹ := inv_pos.mpr hθ
    nlinarith [h6, h7]
  -- assemble
  have hsum1 : ∑ i ∈ P, (∫ β in (α i - δ / 2)..(α i + δ / 2), ‖f β‖ ^ 2) ≤ SW := by
    rw [← hpars]
    exact hdisj _ (hfc.norm.pow 2) (fun β => by positivity)
  have hsum2 : ∑ i ∈ P, (∫ β in (α i - δ / 2)..(α i + δ / 2), 2 * ‖f β‖ * ‖f' β‖)
      ≤ θ * SW + θ⁻¹ * (4 * π ^ 2 * F ^ 2 * SW) := by
    refine le_trans (hdisj _ ((hfc.norm.const_mul 2).mul hf'c.norm)
      (fun β => by positivity)) hAMGM
  have hθterm : θ * SW + θ⁻¹ * (4 * π ^ 2 * F ^ 2 * SW) = 4 * π * F * SW := by
    rw [hθdef]
    have hπF : (2 * π * F) ≠ 0 := by positivity
    field_simp
    ring
  have hnn1 : ∀ i ∈ P, (0 : ℝ) ≤ ∫ β in (α i - δ / 2)..(α i + δ / 2), ‖f β‖ ^ 2 :=
    fun i _ => intervalIntegral.integral_nonneg (by linarith) fun β _ => by positivity
  have hδinv : (0 : ℝ) < 1 / δ := by positivity
  calc ∑ i ∈ P, ‖f (α i)‖ ^ 2
      ≤ (1 / δ) * ∑ i ∈ P, (∫ β in (α i - δ / 2)..(α i + δ / 2), ‖f β‖ ^ 2)
        + ∑ i ∈ P, (∫ β in (α i - δ / 2)..(α i + δ / 2), 2 * ‖f β‖ * ‖f' β‖) := hsob
    _ ≤ (1 / δ) * SW + (θ * SW + θ⁻¹ * (4 * π ^ 2 * F ^ 2 * SW)) := by
        have h8 := mul_le_mul_of_nonneg_left hsum1 hδinv.le
        linarith [hsum2]
    _ = (1 / δ + 4 * π * F) * SW := by
        rw [hθterm]
        ring

/-! ### Farey spacing -/

/-- Distinct reduced fractions with denominators `q, q′` are `1/(qq′)`-spaced
on the line. -/
lemma farey_sep_abs {q q' a a' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (hg : Nat.gcd a q = 1) (hg' : Nat.gcd a' q' = 1)
    (hne : ¬(q = q' ∧ a = a')) :
    1 / ((q : ℝ) * q') ≤ |(a : ℝ) / q - (a' : ℝ) / q'| := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'0 : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hnum : (a : ℤ) * q' - a' * q ≠ 0 := by
    intro h
    have h1 : a * q' = a' * q := by exact_mod_cast sub_eq_zero.mp h
    have h2 : q ∣ q' := by
      have h3 : q ∣ a * q' := ⟨a', by linarith⟩
      exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hg) h3)
    have h4 : q' ∣ q := by
      have h5 : q' ∣ a' * q := ⟨a, by linarith⟩
      exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hg') h5)
    have h6 : q = q' := Nat.dvd_antisymm h2 h4
    subst h6
    have h7 : a = a' := by
      have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) h1
      omega
    exact hne ⟨rfl, h7⟩
  have habs : (1 : ℝ) ≤ |((a : ℤ) * q' - a' * q : ℤ)| := by
    exact_mod_cast Int.one_le_abs (by exact_mod_cast hnum)
  have heq : (a : ℝ) / q - (a' : ℝ) / q' = (((a : ℤ) * q' - a' * q : ℤ) : ℝ) / (q * q') := by
    push_cast
    field_simp
  rw [heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) * q')]
  gcongr
  rw [← Int.cast_abs]
  exact habs

/-- **Farey spacing** (deliverable 3): distinct reduced fractions with
denominators at most `Q` are `1/Q²`-separated in the circle metric. -/
lemma farey_circleDist {Q : ℝ} {q q' a a' : ℕ} (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q)
    (hq' : 1 ≤ q') (hq'Q : (q' : ℝ) ≤ Q) (ha : a < q) (ha' : a' < q')
    (hg : Nat.gcd a q = 1) (hg' : Nat.gcd a' q' = 1)
    (hne : ¬(q = q' ∧ a = a')) :
    1 / Q ^ 2 ≤ circleDist ((a : ℝ) / q - (a' : ℝ) / q') := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'0 : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le hq0 hqQ
  set x : ℝ := (a : ℝ) / q - (a' : ℝ) / q' with hxdef
  set k : ℤ := round x with hkdef
  -- the recentered numerator is a nonzero integer
  have hbound1 : 0 ≤ (a : ℝ) / q := by positivity
  have hbound2 : (a : ℝ) / q < 1 := by
    rw [div_lt_one hq0]
    exact_mod_cast ha
  have hbound1' : 0 ≤ (a' : ℝ) / q' := by positivity
  have hbound2' : (a' : ℝ) / q' < 1 := by
    rw [div_lt_one hq'0]
    exact_mod_cast ha'
  have hnum : ((a : ℤ) * q' - a' * q) - k * (q * q') ≠ 0 := by
    rcases eq_or_ne k 0 with hk0 | hk0
    · rw [hk0, zero_mul, sub_zero]
      intro h
      have h1 : a * q' = a' * q := by exact_mod_cast sub_eq_zero.mp h
      have h2 : q ∣ q' :=
        Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hg) ⟨a', by linarith⟩
      have h4 : q' ∣ q :=
        Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hg') ⟨a, by linarith⟩
      have h6 : q = q' := Nat.dvd_antisymm h2 h4
      subst h6
      exact hne ⟨rfl, by
        have := Nat.eq_of_mul_eq_mul_right (by omega : 0 < q) h1
        omega⟩
    · intro h
      have h1 : ((a : ℤ) * q' - a' * q) = k * (q * q') := by linarith [sub_eq_zero.mp h]
      have h2 : |(a : ℤ) * q' - a' * q| < (q : ℤ) * q' := by
        have h3 : (0 : ℤ) ≤ (a : ℤ) * q' := by positivity
        have h4 : (a : ℤ) * q' < q * q' := by
          have : (a : ℤ) < q := by exact_mod_cast ha
          have hq'p : (0 : ℤ) < q' := by exact_mod_cast hq'
          exact mul_lt_mul_of_pos_right this hq'p
        have h5 : (0 : ℤ) ≤ (a' : ℤ) * q := by positivity
        have h6 : (a' : ℤ) * q < q' * q := by
          have : (a' : ℤ) < q' := by exact_mod_cast ha'
          have hqp : (0 : ℤ) < q := by exact_mod_cast hq
          exact mul_lt_mul_of_pos_right this hqp
        rw [abs_lt]
        constructor <;> nlinarith
      rw [h1, abs_mul, abs_mul] at h2
      have h7 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      have h8 : (0 : ℤ) < q := by exact_mod_cast hq
      have h9 : (0 : ℤ) < q' := by exact_mod_cast hq'
      rw [abs_of_pos h8, abs_of_pos h9] at h2
      have h10 : (q : ℤ) * q' ≤ |k| * ((q : ℤ) * q') :=
        le_mul_of_one_le_left (by positivity) h7
      linarith
  have heq : x - k = ((((a : ℤ) * q' - a' * q) - k * (q * q') : ℤ) : ℝ) / (q * q') := by
    rw [hxdef]
    push_cast
    field_simp
  have h10 : circleDist ((a : ℝ) / q - (a' : ℝ) / q') = |x - (k : ℝ)| := by
    rw [circleDist, hxdef, hkdef]
  rw [h10, heq, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (q : ℝ) * q')]
  have h11 : (1 : ℝ) ≤ |((((a : ℤ) * q' - a' * q) - k * (q * q') : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hnum
  have h12 : (q : ℝ) * q' ≤ Q ^ 2 := by nlinarith
  calc 1 / Q ^ 2 ≤ 1 / ((q : ℝ) * q') := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity) h12
    _ ≤ |((((a : ℤ) * q' - a' * q) - k * (q * q') : ℤ) : ℝ)| / ((q : ℝ) * q') := by
        gcongr

/-! ### The totient-quotient weight -/

/-- The radical of a positive integer is squarefree. -/
lemma radd_squarefree (j : ℕ) : Squarefree (radd j) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime
    (fun p hp q' hq' hpq => ?_)
    fun p hp => (Nat.prime_of_mem_primeFactors hp).squarefree
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
    (Nat.prime_of_mem_primeFactors hq')).mpr hpq

/-- Strengthened coprime harmonic bound: `(φ(K)/K)·log(w+1) ≤ ∑_{i ≤ w, (i,K)=1} 1/i`
(clone of `coprime_harmonic_geM` with the `log(w+1)` harmonic floor). -/
lemma coprime_harmonic_ge' {K : ℕ} (hK : K ≠ 0) (w : ℕ) :
    (Nat.totient K : ℝ) / (K : ℝ) * Real.log (w + 1)
      ≤ ∑ i ∈ coprimeSetM K w, (i : ℝ)⁻¹ := by
  set L : ℝ := ∑ i ∈ coprimeSetM K w, (i : ℝ)⁻¹ with hLdef
  have hLnn : 0 ≤ L := Finset.sum_nonneg fun i _ => by positivity
  have hφpos : (0 : ℝ) < (Nat.totient K : ℝ) / (K : ℝ) := by
    have h1 : 0 < Nat.totient K := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hK)
    have h2 : (0 : ℝ) < (K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hK
    have h3 : (0 : ℝ) < (Nat.totient K : ℝ) := by exact_mod_cast h1
    positivity
  -- pivot on the plain harmonic sum: log(w+1) ≤ H(w) and, per the geM proof,
  -- H(w) ≤ (K/φ(K))·L; both are recovered from `coprime_harmonic_geM`'s
  -- companion pieces below.
  have hH : Real.log (w + 1) ≤ ∑ n ∈ Finset.Icc 1 w, (n : ℝ)⁻¹ := by
    have h1 : ∑ n ∈ Finset.Icc 1 w, (n : ℝ)⁻¹ = ((harmonic w : ℚ) : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    rw [h1]
    have h2 := log_add_one_le_harmonic w
    calc Real.log (w + 1) = Real.log ((w : ℝ) + 1) := by norm_num
      _ ≤ _ := by exact_mod_cast h2
  -- the smooth × coprime factorization (verbatim from `coprime_harmonic_geM`)
  set Qs := K.primeFactors with hQdef
  have hQp : ∀ p ∈ Qs, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  set A := (Finset.Icc 1 w).filter (fun a => a.primeFactors ⊆ Qs) with hA
  have hkey : ∑ n ∈ Finset.Icc 1 w, (n : ℝ)⁻¹ ≤ (∑ a ∈ A, (a : ℝ)⁻¹) * L := by
    have hφmem : ∀ n ∈ Finset.Icc 1 w,
        (smoothPartM K n, n / smoothPartM K n) ∈ A ×ˢ coprimeSetM K w := by
      intro n hn
      obtain ⟨hn1, hnw⟩ := Finset.mem_Icc.mp hn
      have hn0 : n ≠ 0 := by omega
      have hdvd := smoothPartM_dvd K hn0
      rw [Finset.mem_product]
      constructor
      · rw [hA, Finset.mem_filter, Finset.mem_Icc]
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
    have hinj : ∀ n₁ ∈ Finset.Icc 1 w, ∀ n₂ ∈ Finset.Icc 1 w,
        (smoothPartM K n₁, n₁ / smoothPartM K n₁)
          = (smoothPartM K n₂, n₂ / smoothPartM K n₂) → n₁ = n₂ := by
      intro n₁ h₁ n₂ h₂ he
      have hn₁ : n₁ ≠ 0 := by have := (Finset.mem_Icc.mp h₁).1; omega
      have hn₂ : n₂ ≠ 0 := by have := (Finset.mem_Icc.mp h₂).1; omega
      have e1 : smoothPartM K n₁ = smoothPartM K n₂ := congrArg Prod.fst he
      have e2 : n₁ / smoothPartM K n₁ = n₂ / smoothPartM K n₂ := congrArg Prod.snd he
      calc n₁ = smoothPartM K n₁ * (n₁ / smoothPartM K n₁) :=
            (Nat.mul_div_cancel' (smoothPartM_dvd K hn₁)).symm
        _ = smoothPartM K n₂ * (n₂ / smoothPartM K n₂) := by rw [e2, e1]
        _ = n₂ := Nat.mul_div_cancel' (smoothPartM_dvd K hn₂)
    calc ∑ n ∈ Finset.Icc 1 w, (n : ℝ)⁻¹
        = ∑ n ∈ Finset.Icc 1 w, ((smoothPartM K n : ℕ) : ℝ)⁻¹
            * ((n / smoothPartM K n : ℕ) : ℝ)⁻¹ := by
          refine Finset.sum_congr rfl fun n hn => ?_
          have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
          rw [← mul_inv, ← Nat.cast_mul,
            Nat.mul_div_cancel' (smoothPartM_dvd K hn0)]
      _ = ∑ qp ∈ (Finset.Icc 1 w).image
            (fun n => (smoothPartM K n, n / smoothPartM K n)),
            ((qp.1 : ℕ) : ℝ)⁻¹ * ((qp.2 : ℕ) : ℝ)⁻¹ := by
          rw [Finset.sum_image hinj]
      _ ≤ ∑ qp ∈ A ×ˢ coprimeSetM K w, ((qp.1 : ℕ) : ℝ)⁻¹ * ((qp.2 : ℕ) : ℝ)⁻¹ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · rw [Finset.image_subset_iff]
            exact hφmem
          · intro qp _ _
            positivity
      _ = (∑ a ∈ A, (a : ℝ)⁻¹) * L := by
          rw [Finset.sum_mul_sum]
          exact Finset.sum_product' _ _ (fun i j : ℕ => ((i : ℕ) : ℝ)⁻¹ * ((j : ℕ) : ℝ)⁻¹)
  have hAle : ∑ a ∈ A, (a : ℝ)⁻¹ ≤ ∏ p ∈ Qs, (1 - (p : ℝ)⁻¹)⁻¹ := by
    refine le_trans (sum_le_prod_sum_pow Qs (Finset.range (w + 1))
      (fun n : ℕ => (n : ℝ)⁻¹) (fun n => by positivity) (by simp)
      (fun a b => by push_cast; rw [mul_inv]) A ?_ ?_ ?_) ?_
    · intro a ha
      have := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
      omega
    · intro a ha
      exact (Finset.mem_filter.mp ha).2
    · intro a ha p _
      have ha0 : a ≠ 0 := by
        have := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
        omega
      have haw := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
      rw [Finset.mem_range]
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
        calc ∑ k ∈ Finset.range (w + 1), (((p ^ k : ℕ) : ℝ))⁻¹
            = ∑ k ∈ Finset.range (w + 1), ((p : ℝ)⁻¹) ^ k := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Nat.cast_pow, inv_pow]
          _ ≤ (1 - (p : ℝ)⁻¹)⁻¹ := geom_sum_range_le (by positivity) hx1 _
  have hprod : ∏ p ∈ Qs, (1 - (p : ℝ)⁻¹)⁻¹
      = ((Nat.totient K : ℝ) / (K : ℝ))⁻¹ := by
    rw [Finset.prod_inv_distrib, prod_one_sub_inv_primeFactors hK]
  have hHL : ∑ n ∈ Finset.Icc 1 w, (n : ℝ)⁻¹
      ≤ ((Nat.totient K : ℝ) / (K : ℝ))⁻¹ * L := by
    calc ∑ n ∈ Finset.Icc 1 w, (n : ℝ)⁻¹ ≤ (∑ a ∈ A, (a : ℝ)⁻¹) * L := hkey
      _ ≤ ((Nat.totient K : ℝ) / (K : ℝ))⁻¹ * L :=
          mul_le_mul_of_nonneg_right (hAle.trans_eq hprod) hLnn
  calc (Nat.totient K : ℝ) / (K : ℝ) * Real.log (w + 1)
      ≤ (Nat.totient K : ℝ) / (K : ℝ)
          * (((Nat.totient K : ℝ) / (K : ℝ))⁻¹ * L) :=
        mul_le_mul_of_nonneg_left (le_trans hH hHL) hφpos.le
    _ = L := by
        rw [← mul_assoc, mul_inv_cancel₀ hφpos.ne', one_mul]

/-- Fiber bound: the harmonic mass of integers with radical `r` is at most
`1/φ(r)` (`r` squarefree). -/
lemma fiber_inv_sum_le {f X r : ℕ} (hr : Squarefree r) :
    ∑ j ∈ (coprimeSetM f X).filter (fun j => radd j = r), (j : ℝ)⁻¹
      ≤ ((r.totient : ℝ))⁻¹ := by
  have hrp : ∀ p ∈ r.primeFactors, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors hp
  have h1 : ∑ j ∈ (coprimeSetM f X).filter (fun j => radd j = r), (j : ℝ)⁻¹
      ≤ ∏ p ∈ r.primeFactors, ∑ k ∈ Finset.Icc 1 X, ((p ^ k : ℕ) : ℝ)⁻¹ := by
    refine sum_le_prod_sum_pow r.primeFactors (Finset.Icc 1 X) (fun n : ℕ => (n : ℝ)⁻¹)
      (fun n => by positivity) (by simp) (fun a b => by push_cast; rw [mul_inv])
      ((coprimeSetM f X).filter (fun j => radd j = r)) ?_ ?_ ?_
    · intro j hj
      have := (mem_coprimeSetM.mp (Finset.mem_filter.mp hj).1).1.1
      omega
    · intro j hj
      obtain ⟨-, hrad⟩ := Finset.mem_filter.mp hj
      rw [← hrad, primeFactors_radd]
    · intro j hj p hp
      obtain ⟨hjJ, hrad⟩ := Finset.mem_filter.mp hj
      obtain ⟨⟨hj1, hjX⟩, -⟩ := mem_coprimeSetM.mp hjJ
      rw [← hrad, primeFactors_radd] at hp
      rw [Finset.mem_Icc]
      constructor
      · exact (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
          (by omega) (Nat.dvd_of_mem_primeFactors hp)
      · have := Nat.factorization_lt p (show j ≠ 0 by omega)
        omega
  have h2 : ∏ p ∈ r.primeFactors, ∑ k ∈ Finset.Icc 1 X, ((p ^ k : ℕ) : ℝ)⁻¹
      ≤ ∏ p ∈ r.primeFactors, ((p : ℝ) - 1)⁻¹ := by
    apply Finset.prod_le_prod
    · intro p _
      exact Finset.sum_nonneg fun k _ => by positivity
    · intro p hp
      have hp2 : 2 ≤ p := (hrp p hp).two_le
      have hp0 : (0 : ℝ) < (p : ℝ) := by
        have : 0 < p := by omega
        exact_mod_cast this
      have hx1 : ((p : ℝ))⁻¹ < 1 := by
        rw [inv_lt_one₀ hp0]
        exact_mod_cast (by omega : 1 < p)
      have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
      calc ∑ k ∈ Finset.Icc 1 X, ((p ^ k : ℕ) : ℝ)⁻¹
          = ∑ k ∈ Finset.Icc 1 X, ((p : ℝ)⁻¹) ^ k := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Nat.cast_pow, inv_pow]
        _ ≤ (p : ℝ)⁻¹ * (1 - (p : ℝ)⁻¹)⁻¹ := geom_sum_Icc_le (by positivity) hx1 X
        _ = ((p : ℝ) - 1)⁻¹ := by
            rw [← mul_inv]
            congr 1
            field_simp
  have h3 : ∏ p ∈ r.primeFactors, ((p : ℝ) - 1)⁻¹ = ((r.totient : ℝ))⁻¹ := by
    rw [Finset.prod_inv_distrib]
    congr 1
    have h4 : ((Nat.totient (∏ p ∈ r.primeFactors, p) : ℕ) : ℝ)
        = ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := totient_prod_primes_real _ hrp
    rw [← h4, Nat.prod_primeFactors_of_squarefree hr]
  calc ∑ j ∈ (coprimeSetM f X).filter (fun j => radd j = r), (j : ℝ)⁻¹
      ≤ ∏ p ∈ r.primeFactors, ∑ k ∈ Finset.Icc 1 X, ((p ^ k : ℕ) : ℝ)⁻¹ := h1
    _ ≤ ∏ p ∈ r.primeFactors, ((p : ℝ) - 1)⁻¹ := h2
    _ = ((r.totient : ℝ))⁻¹ := h3

/-- **The totient-quotient lower bound** (deliverable 6):
`∑_{r ≤ X, squarefree, (r,f)=1} 1/φ(r) ≥ (φ(f)/f)·log(X+1)`. -/
lemma sum_inv_totient_ge {f : ℕ} (hf : f ≠ 0) (X : ℕ) :
    (f.totient : ℝ) / f * Real.log (X + 1)
      ≤ ∑ r ∈ (Finset.Icc 1 X).filter (fun r => Squarefree r ∧ Nat.Coprime r f),
          ((r.totient : ℝ))⁻¹ := by
  have hmaps : ∀ j ∈ coprimeSetM f X,
      radd j ∈ (Finset.Icc 1 X).filter (fun r => Squarefree r ∧ Nat.Coprime r f) := by
    intro j hj
    obtain ⟨⟨hj1, hjX⟩, hcop⟩ := mem_coprimeSetM.mp hj
    have hj0 : j ≠ 0 := by omega
    have hd := radd_dvd_self j
    have hr0 : 0 < radd j := Nat.pos_of_dvd_of_pos hd (by omega)
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hr0, le_trans (Nat.le_of_dvd (by omega) hd) hjX⟩,
      radd_squarefree j, Nat.Coprime.coprime_dvd_left hd hcop⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun j : ℕ => (j : ℝ)⁻¹)
  calc (f.totient : ℝ) / f * Real.log (X + 1)
      ≤ ∑ j ∈ coprimeSetM f X, (j : ℝ)⁻¹ := coprime_harmonic_ge' hf X
    _ = ∑ r ∈ (Finset.Icc 1 X).filter (fun r => Squarefree r ∧ Nat.Coprime r f),
          ∑ j ∈ (coprimeSetM f X).filter (fun j => radd j = r), (j : ℝ)⁻¹ := hfib.symm
    _ ≤ ∑ r ∈ (Finset.Icc 1 X).filter (fun r => Squarefree r ∧ Nat.Coprime r f),
          ((r.totient : ℝ))⁻¹ := by
        refine Finset.sum_le_sum fun r hr => ?_
        exact fiber_inv_sum_le (Finset.mem_filter.mp hr).2.1

/-! ### Smoothing: the triangle bilinear form is a window mean square -/

lemma tri_mul_eq {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    δ * MeanValue.tri δ y = max 0 (δ - |y|) := by
  unfold MeanValue.tri
  rw [mul_max_of_nonneg _ _ hδ.le, mul_zero]
  congr 1
  field_simp

/-- **Indicator-overlap identity**: the real part of the triangle bilinear
form equals `(1/δ)` times the window mean square. -/
lemma tri_bilinear_eq {ι : Type*} (s : Finset ι) (c : ι → ℂ) (lam : ι → ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j)
        * ((MeanValue.tri δ (lam i - lam j) : ℝ) : ℂ)).re
      = (1 / δ) * ∫ x : ℝ, ‖∑ i ∈ s.filter (fun i => |lam i - x| ≤ δ / 2), c i‖ ^ 2 := by
  set I : ι → Set ℝ := fun i => Set.Icc (lam i - δ / 2) (lam i + δ / 2) with hIdef
  set U : ℝ → ℂ := fun x => ∑ i ∈ s, Set.indicator (I i) (fun _ => c i) x with hUdef
  have hmem : ∀ (i : ι) (x : ℝ), x ∈ I i ↔ |lam i - x| ≤ δ / 2 := by
    intro i x
    rw [hIdef]
    simp only [Set.mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hU : ∀ x : ℝ, (∑ i ∈ s.filter (fun i => |lam i - x| ≤ δ / 2), c i) = U x := by
    intro x
    rw [hUdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Set.indicator_apply]
    by_cases h : x ∈ I i
    · rw [if_pos ((hmem i x).mp h), if_pos h]
    · rw [if_neg (fun hc => h ((hmem i x).mpr hc)), if_neg h]
  -- the pairwise product is an indicator of the intersection
  have hprod : ∀ (i j : ι) (x : ℝ),
      Set.indicator (I i) (fun _ => c i) x * conj (Set.indicator (I j) (fun _ => c j) x)
        = Set.indicator (I i ∩ I j) (fun _ => c i * conj (c j)) x := by
    intro i j x
    by_cases h1 : x ∈ I i <;> by_cases h2 : x ∈ I j <;>
      simp [h1, h2]
  have hvol : ∀ i j : ι, (MeasureTheory.volume (I i ∩ I j)).toReal
      = δ * MeanValue.tri δ (lam i - lam j) := by
    intro i j
    rw [hIdef]
    simp only
    rw [Set.Icc_inter_Icc, Real.volume_Icc]
    have harith : min (lam i + δ / 2) (lam j + δ / 2) - max (lam i - δ / 2) (lam j - δ / 2)
        = δ - |lam i - lam j| := by
      rcases le_total (lam i) (lam j) with h | h
      · rw [min_eq_left (by linarith), max_eq_right (by linarith),
          abs_of_nonpos (by linarith : lam i - lam j ≤ 0)]
        ring
      · rw [min_eq_right (by linarith), max_eq_left (by linarith),
          abs_of_nonneg (by linarith : 0 ≤ lam i - lam j)]
        ring
    rw [harith, tri_mul_eq hδ]
    rcases le_total 0 (δ - |lam i - lam j|) with h | h
    · rw [ENNReal.toReal_ofReal h, max_eq_right h]
    · rw [ENNReal.ofReal_eq_zero.mpr h, ENNReal.toReal_zero, max_eq_left h]
  have hIint : ∀ i j : ι, MeasureTheory.Integrable
      (fun x => Set.indicator (I i ∩ I j) (fun _ => c i * conj (c j)) x) := by
    intro i j
    rw [MeasureTheory.integrable_indicator_iff
      ((measurableSet_Icc).inter (measurableSet_Icc))]
    refine MeasureTheory.integrableOn_const ?_
    refine ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  -- the complex integral of ‖U‖²
  have hCint : ∫ x : ℝ, (U x * conj (U x))
      = ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j)
          * ((δ * MeanValue.tri δ (lam i - lam j) : ℝ) : ℂ) := by
    have hpt : ∀ x : ℝ, U x * conj (U x)
        = ∑ i ∈ s, ∑ j ∈ s, Set.indicator (I i ∩ I j) (fun _ => c i * conj (c j)) x := by
      intro x
      rw [hUdef]
      simp only
      rw [map_sum, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hprod i j x
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
    rw [MeasureTheory.integral_finsetSum _ (fun i _ =>
      MeasureTheory.integrable_finsetSum _ (fun j _ => hIint i j))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MeasureTheory.integral_finsetSum _ (fun j _ => hIint i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MeasureTheory.integral_indicator_const _
      ((measurableSet_Icc).inter (measurableSet_Icc))]
    rw [MeasureTheory.measureReal_def, hvol i j]
    rw [Complex.real_smul, mul_comm]
  -- pass to real parts
  have hreal : ∫ x : ℝ, ‖U x‖ ^ 2
      = (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j)
          * ((δ * MeanValue.tri δ (lam i - lam j) : ℝ) : ℂ)).re := by
    have h1 : ∀ x : ℝ, ((‖U x‖ ^ 2 : ℝ) : ℂ) = U x * conj (U x) := by
      intro x
      rw [Complex.mul_conj, ← Complex.normSq_eq_norm_sq]
    have h2 : ∫ x : ℝ, ((‖U x‖ ^ 2 : ℝ) : ℂ)
        = ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j)
            * ((δ * MeanValue.tri δ (lam i - lam j) : ℝ) : ℂ) := by
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h1)]
      exact hCint
    have h3 := congrArg Complex.re h2
    rwa [integral_complex_ofReal] at h3
  have hpull : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j)
        * ((δ * MeanValue.tri δ (lam i - lam j) : ℝ) : ℂ))
      = (δ : ℂ) * ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j)
          * ((MeanValue.tri δ (lam i - lam j) : ℝ) : ℂ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have h4 : ∫ x : ℝ, ‖∑ i ∈ s.filter (fun i => |lam i - x| ≤ δ / 2), c i‖ ^ 2
      = ∫ x : ℝ, ‖U x‖ ^ 2 :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => by
      beta_reduce
      rw [hU x])
  rw [h4, hreal, hpull]
  rw [Complex.mul_re]
  have h5 : ((δ : ℂ)).im = 0 := by simp
  have h6 : ((δ : ℂ)).re = δ := by simp
  rw [h5, h6]
  field_simp
  ring

/-- **Gallagher smoothing** (deliverable 7): the `t`-integrated mean square is
bounded by the window mean square along `dx`. -/
lemma t_integral_le {T : ℝ} (hT : 1 ≤ T) {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (lam : ι → ℝ) :
    (∫ t in (-T)..T, ‖∑ i ∈ s, c i * Complex.exp ((lam i * t : ℝ) * Complex.I)‖ ^ 2)
      ≤ 48 * T ^ 2 / π
          * ∫ x : ℝ, ‖∑ i ∈ s.filter (fun i => |lam i - x| ≤ π / (8 * T)), c i‖ ^ 2 := by
  have hT0 : (0 : ℝ) < T := by linarith
  have h2T : (2 : ℝ) ≤ 2 * T := by linarith
  have hcont : Continuous fun t : ℝ =>
      ‖∑ i ∈ s, c i * Complex.exp ((lam i * t : ℝ) * Complex.I)‖ ^ 2 := by
    refine Continuous.pow (Continuous.norm ?_) 2
    refine continuous_finsetSum _ fun i _ => Continuous.const_mul ?_ (c i)
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
        continuous_const)
  have hmono : (∫ t in (-T)..T, ‖∑ i ∈ s, c i * Complex.exp ((lam i * t : ℝ) * Complex.I)‖ ^ 2)
      ≤ ∫ t in (-(2 * T))..(2 * T),
          ‖∑ i ∈ s, c i * Complex.exp ((lam i * t : ℝ) * Complex.I)‖ ^ 2 := by
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall fun t => by positivity)
      (hcont.intervalIntegrable _ _)
  have hker := MeanValue.kernel_mvt (2 * T) h2T s c lam
  have htriarg : ∀ i j : ι,
      MeanValue.tri (1 / (4 * (2 * T))) ((lam i - lam j) / (2 * π))
        = MeanValue.tri (π / (4 * T)) (lam i - lam j) := by
    intro i j
    unfold MeanValue.tri
    congr 2
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
    rw [div_div]
    congr 1
    field_simp
  have hδ : (0 : ℝ) < π / (4 * T) := by positivity
  have hbil := tri_bilinear_eq s c lam hδ
  have hfilter : ∀ x : ℝ, s.filter (fun i => |lam i - x| ≤ π / (4 * T) / 2)
      = s.filter (fun i => |lam i - x| ≤ π / (8 * T)) := by
    intro x
    refine Finset.filter_congr fun i _ => ?_
    rw [show π / (4 * T) / 2 = π / (8 * T) by ring]
  have hsum_eq : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j)
        * ((MeanValue.tri (1 / (4 * (2 * T))) ((lam i - lam j) / (2 * π)) : ℝ) : ℂ)).re
      = (1 / (π / (4 * T)))
          * ∫ x : ℝ, ‖∑ i ∈ s.filter (fun i => |lam i - x| ≤ π / (8 * T)), c i‖ ^ 2 := by
    have h1 : (∑ i ∈ s, ∑ j ∈ s, c i * conj (c j)
          * ((MeanValue.tri (1 / (4 * (2 * T))) ((lam i - lam j) / (2 * π)) : ℝ) : ℂ))
        = ∑ i ∈ s, ∑ j ∈ s, c i * conj (c j)
            * ((MeanValue.tri (π / (4 * T)) (lam i - lam j) : ℝ) : ℂ) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [htriarg i j]
    rw [h1, hbil]
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [hfilter x]
  have hgoal := hker.trans (le_of_eq (by rw [hsum_eq]))
  refine hmono.trans (hgoal.trans (le_of_eq ?_))
  rw [← mul_assoc]
  congr 1
  field_simp
  ring

/-! ### The selected-character identity -/

/-- For `ψ` primitive mod `f` raised (inverted) to level `r·f`, the twisted
unit average has norm² exactly `f` times the `ψ`-twisted window sum. -/
lemma W_norm_eq {r f : ℕ} [NeZero r] [NeZero f] [NeZero (r * f)]
    (hsf : Squarefree r) (hco : Nat.Coprime r f)
    {ψ : DirichletCharacter ℂ f} (hψ : ψ.IsPrimitive)
    (w' : Finset ℕ) (a : ℕ → ℂ)
    (hcop : ∀ n ∈ w', IsUnit ((n : ZMod (r * f)))) :
    ‖∑ u : (ZMod (r * f))ˣ, (changeLevel (dvd_mul_left f r) ψ⁻¹) u
        * (∑ n ∈ w', a n * ZMod.stdAddChar ((n : ZMod (r * f)) * (u : ZMod (r * f))))‖ ^ 2
      = (f : ℝ) * ‖∑ n ∈ w', a n * ψ ((n : ZMod f))‖ ^ 2 := by
  set χ : DirichletCharacter ℂ (r * f) := changeLevel (dvd_mul_left f r) ψ⁻¹ with hχdef
  have htrans := char_twisted_sum_eq χ w' a (fun n => n) hcop
  rw [htrans, norm_mul, mul_pow]
  have hψinv : (ψ⁻¹).IsPrimitive := by
    rw [IsPrimitive, conductor_inv]
    exact hψ
  have hτ : ‖gaussSum χ ZMod.stdAddChar‖ ^ 2 = f := by
    rw [hχdef]
    exact norm_sq_gaussSum_changeLevel hsf hco hψinv
  have hχinv : χ⁻¹ = changeLevel (dvd_mul_left f r) ψ := by
    rw [hχdef, ← map_inv, inv_inv]
  have heval : ∀ n ∈ w', χ⁻¹ ((n : ZMod (r * f))) = ψ ((n : ZMod f)) := by
    intro n hn
    rw [hχinv]
    have hu := hcop n hn
    have hspec : (hu.unit : ZMod (r * f)) = (n : ZMod (r * f)) := hu.unit_spec
    conv_lhs => rw [← hspec]
    rw [changeLevel_eq_cast_of_dvd ψ (dvd_mul_left f r) hu.unit, hspec,
      ZMod.cast_natCast (dvd_mul_left f r)]
  have hsum : ∑ n ∈ w', a n * χ⁻¹ ((n : ZMod (r * f)))
      = ∑ n ∈ w', a n * ψ ((n : ZMod f)) :=
    Finset.sum_congr rfl fun n hn => by rw [heval n hn]
  rw [hsum, hτ]

lemma eAt_add (mu nu : ℤ) (β : ℝ) : eAt (mu + nu) β = eAt mu β * eAt nu β := by
  unfold eAt
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Recentering: window sums of `eAt` twists have the same norm after
shifting all frequencies by `n₀`. -/
lemma norm_eAt_center (w' : Finset ℕ) (a : ℕ → ℂ) (n₀ : ℕ) (α : ℝ) :
    ‖∑ n ∈ w', a n * eAt (n : ℤ) α‖
      = ‖∑ n ∈ w', a n * eAt ((n : ℤ) - (n₀ : ℤ)) α‖ := by
  have h1 : ∑ n ∈ w', a n * eAt (n : ℤ) α
      = eAt (n₀ : ℤ) α * ∑ n ∈ w', a n * eAt ((n : ℤ) - (n₀ : ℤ)) α := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have h2 : eAt (n : ℤ) α = eAt (n₀ : ℤ) α * eAt ((n : ℤ) - (n₀ : ℤ)) α := by
      rw [← eAt_add]
      congr 1
      ring
    rw [h2]
    ring
  rw [h1, norm_mul, norm_eAt, one_mul]

/-- **Per-modulus block bound**: the selected induced characters at modulus
`q` are dominated by the Farey-point mean square at denominator `q`. -/
lemma fiber_block_le {Q₀ : ℕ} {q : ℕ} [NeZero q] (hqmem : q ∈ Finset.Icc 1 Q₀)
    (w' : Finset ℕ) (a : ℕ → ℂ) (n₀ : ℕ)
    (hcop : ∀ n ∈ w', Nat.Coprime n q) :
    ∑ p ∈ ((Finset.Icc 1 Q₀ ×ˢ Finset.Icc 1 Q₀).filter
        (fun p => p.2 * p.1 ≤ Q₀ ∧ Squarefree p.2 ∧ Nat.Coprime p.2 p.1)).filter
        (fun p => p.2 * p.1 = q),
      ((p.1 : ℝ) / (Nat.totient (p.2 * p.1)))
        * ∑ ψ ∈ primChars p.1, ‖∑ n ∈ w', a n * ψ ((n : ZMod p.1))‖ ^ 2
      ≤ ∑ v ∈ (Finset.range q).filter (fun v => Nat.gcd v q = 1),
          ‖∑ n ∈ w', a n * eAt ((n : ℤ) - (n₀ : ℤ)) ((v : ℝ) / q)‖ ^ 2 := by
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hqmem).1
  have hunit : ∀ n ∈ w', IsUnit ((n : ZMod q)) := by
    intro n hn
    rw [ZMod.isUnit_iff_coprime]
    exact hcop n hn
  have hφpos : (0 : ℝ) < q.totient := by
    exact_mod_cast q.totient_pos.mpr (by omega)
  set PPq := ((Finset.Icc 1 Q₀ ×ˢ Finset.Icc 1 Q₀).filter
      (fun p => p.2 * p.1 ≤ Q₀ ∧ Squarefree p.2 ∧ Nat.Coprime p.2 p.1)).filter
      (fun p => p.2 * p.1 = q) with hPPq
  set Tzu : (ZMod q)ˣ → ℂ := fun u =>
    ∑ n ∈ w', a n * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) with hTzu
  -- Step 1: pull out 1/φ(q)
  have hstep1 : ∑ p ∈ PPq,
      ((p.1 : ℝ) / (Nat.totient (p.2 * p.1)))
        * ∑ ψ ∈ primChars p.1, ‖∑ n ∈ w', a n * ψ ((n : ZMod p.1))‖ ^ 2
      = (q.totient : ℝ)⁻¹ * ∑ p ∈ PPq, (p.1 : ℝ)
          * ∑ ψ ∈ primChars p.1, ‖∑ n ∈ w', a n * ψ ((n : ZMod p.1))‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hfib : p.2 * p.1 = q := (Finset.mem_filter.mp hp).2
    rw [hfib]
    ring
  rw [hstep1]
  -- Step 2: selected characters are dominated by the full character sum
  have hsel : ∑ p ∈ PPq, (p.1 : ℝ)
        * ∑ ψ ∈ primChars p.1, ‖∑ n ∈ w', a n * ψ ((n : ZMod p.1))‖ ^ 2
      ≤ ∑ χ : DirichletCharacter ℂ q, ‖∑ u : (ZMod q)ˣ, χ u * Tzu u‖ ^ 2 := by
    have hSigma : ∑ p ∈ PPq, (p.1 : ℝ)
          * ∑ ψ ∈ primChars p.1, ‖∑ n ∈ w', a n * ψ ((n : ZMod p.1))‖ ^ 2
        = ∑ x ∈ PPq.sigma (fun p => primChars p.1),
            (x.1.1 : ℝ) * ‖∑ n ∈ w', a n * (x.2) ((n : ZMod x.1.1))‖ ^ 2 := by
      rw [Finset.sum_sigma]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
    rw [hSigma]
    set emb : ((p : ℕ × ℕ) × DirichletCharacter ℂ p.1) → DirichletCharacter ℂ q :=
      fun x => if h : x.1.1 ∣ q then changeLevel h (x.2)⁻¹ else 1 with hembdef
    have hmemfacts : ∀ x ∈ PPq.sigma (fun p => primChars p.1),
        x.1.2 * x.1.1 = q ∧ 1 ≤ x.1.1 ∧ 1 ≤ x.1.2 ∧ Squarefree x.1.2
          ∧ Nat.Coprime x.1.2 x.1.1 := by
      intro x hx
      rw [Finset.mem_sigma] at hx
      obtain ⟨hp, -⟩ := hx
      rw [hPPq, Finset.mem_filter, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc, Finset.mem_Icc] at hp
      exact ⟨hp.2, hp.1.1.1.1, hp.1.1.2.1, hp.1.2.2.1, hp.1.2.2.2⟩
    have hval : ∀ x ∈ PPq.sigma (fun p => primChars p.1),
        (x.1.1 : ℝ) * ‖∑ n ∈ w', a n * (x.2) ((n : ZMod x.1.1))‖ ^ 2
          = ‖∑ u : (ZMod q)ˣ, (emb x) u * Tzu u‖ ^ 2 := by
      intro x hx
      obtain ⟨hfib, hf1, hr1, hsf, hco⟩ := hmemfacts x hx
      have hψmem : x.2 ∈ primChars x.1.1 := (Finset.mem_sigma.mp hx).2
      obtain ⟨⟨f, r⟩, ψ⟩ := x
      simp only at hfib hf1 hr1 hsf hco hψmem ⊢
      have : NeZero f := ⟨by omega⟩
      have : NeZero r := ⟨by omega⟩
      have hψ : ψ.IsPrimitive := mem_primChars.mp hψmem
      subst hfib
      have : NeZero (r * f) := ⟨by positivity⟩
      have hdvd : f ∣ r * f := dvd_mul_left f r
      have hemb : emb ⟨(f, r), ψ⟩ = changeLevel hdvd ψ⁻¹ := by
        rw [hembdef]
        simp only
        rw [dif_pos hdvd]
      rw [hemb]
      exact (W_norm_eq hsf hco hψ w' a hunit).symm
    have hinj : ∀ x ∈ PPq.sigma (fun p => primChars p.1),
        ∀ y ∈ PPq.sigma (fun p => primChars p.1), emb x = emb y → x = y := by
      rintro ⟨⟨f, r⟩, ψ⟩ hx ⟨⟨f', r'⟩, ψ'⟩ hy hxy
      obtain ⟨hfibx, hf1x, hr1x, -, -⟩ := hmemfacts _ hx
      obtain ⟨hfiby, hf1y, hr1y, -, -⟩ := hmemfacts _ hy
      have hψx : ψ ∈ primChars f := (Finset.mem_sigma.mp hx).2
      have hψy : ψ' ∈ primChars f' := (Finset.mem_sigma.mp hy).2
      dsimp only at hfibx hf1x hr1x hfiby hf1y hr1y
      have : NeZero f := ⟨by omega⟩
      have : NeZero f' := ⟨by omega⟩
      have hdx : f ∣ q := Dvd.intro_left r hfibx
      have hdy : f' ∣ q := Dvd.intro_left r' hfiby
      have hex : emb ⟨(f, r), ψ⟩ = changeLevel hdx ψ⁻¹ := by
        rw [hembdef]; exact dif_pos hdx
      have hey : emb ⟨(f', r'), ψ'⟩ = changeLevel hdy ψ'⁻¹ := by
        rw [hembdef]; exact dif_pos hdy
      rw [hex, hey] at hxy
      -- conductors identify the levels
      have hcx : (changeLevel hdx ψ⁻¹).conductor = f := by
        rw [conductor_changeLevel, conductor_inv]
        exact mem_primChars.mp hψx
      have hcy : (changeLevel hdy ψ'⁻¹).conductor = f' := by
        rw [conductor_changeLevel, conductor_inv]
        exact mem_primChars.mp hψy
      have hff : f = f' := by rw [← hcx, ← hcy, hxy]
      subst hff
      have hrr : r = r' := by
        have h2 : r * f = r' * f := by rw [hfibx, hfiby]
        exact Nat.eq_of_mul_eq_mul_right (by omega) h2
      subst hrr
      have hψψ : ψ⁻¹ = ψ'⁻¹ := changeLevel_injective hdx hxy
      have h3 : ψ = ψ' := inv_injective hψψ
      subst h3
      rfl
    have himg : ∑ χ ∈ (PPq.sigma (fun p => primChars p.1)).image emb,
          ‖∑ u : (ZMod q)ˣ, χ u * Tzu u‖ ^ 2
        = ∑ x ∈ PPq.sigma (fun p => primChars p.1),
            ‖∑ u : (ZMod q)ˣ, (emb x) u * Tzu u‖ ^ 2 :=
      Finset.sum_image hinj
    rw [Finset.sum_congr rfl hval, ← himg]
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro χ _ _
    positivity
  -- Step 3: Parseval over the character group and the bridge to `eAt`
  have hpars := parseval_units Tzu
  have hbridge : ∀ u : (ZMod q)ˣ, ‖Tzu u‖
      = ‖∑ n ∈ w', a n * eAt ((n : ℤ) - (n₀ : ℤ)) (((u : ZMod q).val : ℝ) / q)‖ := by
    intro u
    have h1 : ∀ n ∈ w', ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q))
        = eAt (n : ℤ) (((u : ZMod q).val : ℝ) / q) := by
      intro n _
      have h2 : (n : ZMod q) * (u : ZMod q) = ((n * (u : ZMod q).val : ℕ) : ZMod q) := by
        push_cast
        rw [ZMod.natCast_zmod_val]
      rw [h2, show ((n * (u : ZMod q).val : ℕ) : ZMod q)
          = (((n * (u : ZMod q).val : ℕ) : ℤ) : ZMod q) by push_cast; ring,
        ZMod.stdAddChar_coe]
      unfold eAt
      congr 1
      have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast
      field_simp
    have h3 : Tzu u = ∑ n ∈ w', a n * eAt (n : ℤ) (((u : ZMod q).val : ℝ) / q) := by
      rw [hTzu]
      exact Finset.sum_congr rfl fun n hn => by rw [h1 n hn]
    rw [h3, norm_eAt_center]
  -- Step 4: reindex the units onto the Farey numerators
  have hreidx : ∑ u : (ZMod q)ˣ, ‖Tzu u‖ ^ 2
      = ∑ v ∈ (Finset.range q).filter (fun v => Nat.gcd v q = 1),
          ‖∑ n ∈ w', a n * eAt ((n : ℤ) - (n₀ : ℤ)) ((v : ℝ) / q)‖ ^ 2 := by
    refine Finset.sum_nbij' (fun u => (u : ZMod q).val)
      (fun v => if h : Nat.gcd v q = 1 then ZMod.unitOfCoprime v h else 1) ?_ ?_ ?_ ?_ ?_
    · intro u _
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime u⟩
    · intro v _
      exact Finset.mem_univ _
    · intro u _
      rw [dif_pos (ZMod.val_coe_unit_coprime u)]
      ext
      rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]
    · intro v hv
      rw [Finset.mem_filter, Finset.mem_range] at hv
      rw [dif_pos hv.2]
      simp only [ZMod.coe_unitOfCoprime]
      exact ZMod.val_cast_of_lt hv.1
    · intro u _
      rw [hbridge u]
  calc (q.totient : ℝ)⁻¹ * ∑ p ∈ PPq, (p.1 : ℝ)
        * ∑ ψ ∈ primChars p.1, ‖∑ n ∈ w', a n * ψ ((n : ZMod p.1))‖ ^ 2
      ≤ (q.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
          ‖∑ u : (ZMod q)ˣ, χ u * Tzu u‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsel (by positivity)
    _ = (q.totient : ℝ)⁻¹ * ((q.totient : ℝ) * ∑ u : (ZMod q)ˣ, ‖Tzu u‖ ^ 2) := by
        rw [hpars]
    _ = ∑ u : (ZMod q)ˣ, ‖Tzu u‖ ^ 2 := by
        rw [← mul_assoc, inv_mul_cancel₀ hφpos.ne', one_mul]
    _ = ∑ v ∈ (Finset.range q).filter (fun v => Nat.gcd v q = 1),
          ‖∑ n ∈ w', a n * eAt ((n : ℤ) - (n₀ : ℤ)) ((v : ℝ) / q)‖ ^ 2 := hreidx

/-! ### The per-window multiplicative large sieve -/

set_option maxHeartbeats 1000000 in
/-- **Window sieve**: for coefficients supported on integers coprime to all
moduli up to `Q` and within `F` of a center `n₀`, the log-weighted primitive
character mean square is bounded by `(Q² + 4πF)` times the mass. -/
lemma window_sieve {Q : ℝ} (hQ : 2 ≤ Q) (w' : Finset ℕ) (a : ℕ → ℂ) (n₀ : ℕ)
    {F : ℝ} (hF : 0 < F)
    (hcop : ∀ n ∈ w', ∀ q : ℕ, 1 ≤ q → q ≤ ⌊Q⌋₊ → Nat.Coprime n q)
    (hνF : ∀ n ∈ w', |(n : ℝ) - (n₀ : ℝ)| ≤ F) :
    ∑ f ∈ Finset.Icc 1 ⌊Q⌋₊, Real.log (Q / f)
        * ∑ ψ ∈ primChars f, ‖∑ n ∈ w', a n * ψ ((n : ZMod f))‖ ^ 2
      ≤ (Q ^ 2 + 4 * π * F) * ∑ n ∈ w', ‖a n‖ ^ 2 := by
  set Q₀ : ℕ := ⌊Q⌋₊ with hQ₀def
  have hQ₀2 : 2 ≤ Q₀ := Nat.le_floor (by exact_mod_cast hQ)
  have hQ₀R : (Q₀ : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hQ0 : (0 : ℝ) < Q := by linarith
  -- the window-sum block at conductor f
  set Block : (f : ℕ) → ℝ := fun f =>
    ∑ ψ ∈ primChars f, ‖∑ n ∈ w', a n * ψ ((n : ZMod f))‖ ^ 2 with hBlockdef
  have hBlock0 : ∀ f, 0 ≤ Block f := fun f =>
    Finset.sum_nonneg fun ψ _ => by positivity
  -- Step 1: the log weight is dominated by the totient-quotient sum
  have hstep1 : ∀ f ∈ Finset.Icc 1 Q₀, Real.log (Q / f) * Block f
      ≤ ∑ r ∈ (Finset.Icc 1 Q₀).filter
          (fun r => r * f ≤ Q₀ ∧ Squarefree r ∧ Nat.Coprime r f),
          ((f : ℝ) / (Nat.totient (r * f))) * Block f := by
    intro f hf
    obtain ⟨hf1, hfQ₀⟩ := Finset.mem_Icc.mp hf
    have hf0R : (0 : ℝ) < f := by exact_mod_cast hf1
    have hφf : (0 : ℝ) < f.totient := by
      exact_mod_cast f.totient_pos.mpr (by omega)
    set X : ℕ := Q₀ / f with hXdef
    have hX1 : 1 ≤ X := (Nat.one_le_div_iff (by omega)).mpr hfQ₀
    have hlogle : Q / f ≤ (X : ℝ) + 1 := by
      have h1 := Nat.div_add_mod Q₀ f
      have h2 := Nat.mod_lt Q₀ (show 0 < f by omega)
      have h3 : Q₀ + 1 ≤ f * X + f := by rw [hXdef]; omega
      have h4 : Q < (Q₀ : ℝ) + 1 := Nat.lt_floor_add_one Q
      have h5 : ((Q₀ : ℝ) + 1) ≤ (f : ℝ) * ((X : ℝ) + 1) := by
        have : ((Q₀ + 1 : ℕ) : ℝ) ≤ ((f * X + f : ℕ) : ℝ) := by exact_mod_cast h3
        push_cast at this
        linarith
      rw [div_le_iff₀ hf0R]
      nlinarith
    have hlog2 : Real.log (Q / f) ≤ Real.log ((X : ℝ) + 1) :=
      Real.log_le_log (by positivity) hlogle
    have htot := sum_inv_totient_ge (show f ≠ 0 by omega) X
    have hset : (Finset.Icc 1 X).filter (fun r => Squarefree r ∧ Nat.Coprime r f)
        = (Finset.Icc 1 Q₀).filter
            (fun r => r * f ≤ Q₀ ∧ Squarefree r ∧ Nat.Coprime r f) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        have h5 : r * f ≤ Q₀ := (Nat.le_div_iff_mul_le (by omega)).mp h2
        have h6 : r ≤ Q₀ := le_trans (Nat.le_mul_of_pos_right r (by omega)) h5
        exact ⟨⟨h1, h6⟩, h5, h3, h4⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
        exact ⟨⟨h1, (Nat.le_div_iff_mul_le (by omega)).mpr h3⟩, h4, h5⟩
    have hw : Real.log (Q / f) ≤ (f : ℝ) / f.totient
        * ∑ r ∈ (Finset.Icc 1 Q₀).filter
            (fun r => r * f ≤ Q₀ ∧ Squarefree r ∧ Nat.Coprime r f),
            ((Nat.totient r : ℝ))⁻¹ := by
      rw [← hset]
      calc Real.log (Q / f) ≤ Real.log ((X : ℝ) + 1) := hlog2
        _ = ((f : ℝ) / f.totient) * ((f.totient : ℝ) / f * Real.log ((X : ℝ) + 1)) := by
            field_simp
        _ ≤ ((f : ℝ) / f.totient) * ∑ r ∈ (Finset.Icc 1 X).filter
              (fun r => Squarefree r ∧ Nat.Coprime r f), ((Nat.totient r : ℝ))⁻¹ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact_mod_cast htot
    have hexpand : ∀ (R : Finset ℕ) (t : ℕ → ℝ) (A B : ℝ),
        (A * ∑ r ∈ R, t r) * B = ∑ r ∈ R, A * t r * B := by
      intro R t A B
      rw [Finset.mul_sum, Finset.sum_mul]
    calc Real.log (Q / f) * Block f
        ≤ ((f : ℝ) / f.totient
            * ∑ r ∈ (Finset.Icc 1 Q₀).filter
                (fun r => r * f ≤ Q₀ ∧ Squarefree r ∧ Nat.Coprime r f),
                ((Nat.totient r : ℝ))⁻¹) * Block f :=
          mul_le_mul_of_nonneg_right hw (hBlock0 f)
      _ = ∑ r ∈ (Finset.Icc 1 Q₀).filter
            (fun r => r * f ≤ Q₀ ∧ Squarefree r ∧ Nat.Coprime r f),
            (f : ℝ) / f.totient * ((Nat.totient r : ℝ))⁻¹ * Block f :=
          hexpand _ _ _ _
      _ = ∑ r ∈ (Finset.Icc 1 Q₀).filter
            (fun r => r * f ≤ Q₀ ∧ Squarefree r ∧ Nat.Coprime r f),
            ((f : ℝ) / (Nat.totient (r * f))) * Block f := by
          refine Finset.sum_congr rfl fun r hr => ?_
          obtain ⟨-, -, -, hco⟩ := Finset.mem_filter.mp hr
          have hφr : (0 : ℝ) < r.totient := by
            have hr1 : 1 ≤ r := (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
            exact_mod_cast r.totient_pos.mpr (by omega)
          congr 1
          rw [Nat.totient_mul hco]
          push_cast
          field_simp
  -- Step 2: sum over f, regroup as a pair sum, and fiber by q = r·f
  set PP := (Finset.Icc 1 Q₀ ×ˢ Finset.Icc 1 Q₀).filter
      (fun p => p.2 * p.1 ≤ Q₀ ∧ Squarefree p.2 ∧ Nat.Coprime p.2 p.1) with hPPdef
  have hregroup : ∑ f ∈ Finset.Icc 1 Q₀,
        ∑ r ∈ (Finset.Icc 1 Q₀).filter
          (fun r => r * f ≤ Q₀ ∧ Squarefree r ∧ Nat.Coprime r f),
          ((f : ℝ) / (Nat.totient (r * f))) * Block f
      = ∑ p ∈ PP, ((p.1 : ℝ) / (Nat.totient (p.2 * p.1))) * Block p.1 := by
    rw [hPPdef, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.sum_filter]
  have hfiber : ∑ p ∈ PP, ((p.1 : ℝ) / (Nat.totient (p.2 * p.1))) * Block p.1
      = ∑ q ∈ Finset.Icc 1 Q₀, ∑ p ∈ PP.filter (fun p => p.2 * p.1 = q),
          ((p.1 : ℝ) / (Nat.totient (p.2 * p.1))) * Block p.1 := by
    refine (Finset.sum_fiberwise_of_maps_to ?_ _).symm
    intro p hp
    rw [hPPdef, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    rw [Finset.mem_Icc]
    constructor
    · have h1 := hp.1.1.1
      have h2 := hp.1.2.1
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · exact hp.2.1
  -- Step 3: per q, the fiber is dominated by the Farey mean square
  have hstep3 : ∀ q ∈ Finset.Icc 1 Q₀,
      ∑ p ∈ PP.filter (fun p => p.2 * p.1 = q),
          ((p.1 : ℝ) / (Nat.totient (p.2 * p.1))) * Block p.1
        ≤ ∑ v ∈ (Finset.range q).filter (fun v => Nat.gcd v q = 1),
            ‖∑ n ∈ w', a n * eAt ((n : ℤ) - (n₀ : ℤ)) ((v : ℝ) / q)‖ ^ 2 := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ₀ : q ≤ Q₀ := (Finset.mem_Icc.mp hq).2
    have : NeZero q := ⟨by omega⟩
    have hcopq : ∀ n ∈ w', Nat.Coprime n q := fun n hn => hcop n hn q hq1 hqQ₀
    exact fiber_block_le hq w' a n₀ hcopq
  -- Step 4: assemble the Farey family as a pair Finset
  set FP := (Finset.Icc 1 Q₀ ×ˢ Finset.range Q₀).filter
      (fun p => p.2 < p.1 ∧ Nat.gcd p.2 p.1 = 1) with hFPdef
  have hsetq : ∀ q ∈ Finset.Icc 1 Q₀,
      (Finset.range Q₀).filter (fun v => v < q ∧ Nat.gcd v q = 1)
        = (Finset.range q).filter (fun v => Nat.gcd v q = 1) := by
    intro q hq
    have hqQ₀ : q ≤ Q₀ := (Finset.mem_Icc.mp hq).2
    ext v
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨-, h2, h3⟩
      exact ⟨h2, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h1, h2⟩
  have hstep4 : ∑ q ∈ Finset.Icc 1 Q₀,
        ∑ v ∈ (Finset.range q).filter (fun v => Nat.gcd v q = 1),
          ‖∑ n ∈ w', a n * eAt ((n : ℤ) - (n₀ : ℤ)) ((v : ℝ) / q)‖ ^ 2
      = ∑ p ∈ FP, ‖∑ n ∈ w', a n * eAt ((n : ℤ) - (n₀ : ℤ)) ((p.2 : ℝ) / p.1)‖ ^ 2 := by
    rw [hFPdef, Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← Finset.sum_filter, hsetq q hq]
  -- Step 5: the additive large sieve at spacing 1/Q²
  have hδpos : (0 : ℝ) < 1 / Q ^ 2 := by positivity
  have hstep5 : ∑ p ∈ FP, ‖∑ n ∈ w', a n * eAt ((n : ℤ) - (n₀ : ℤ)) ((p.2 : ℝ) / p.1)‖ ^ 2
      ≤ (1 / (1 / Q ^ 2) + 4 * π * F) * ∑ n ∈ w', ‖a n‖ ^ 2 := by
    have hmemFP : ∀ p ∈ FP, 1 ≤ p.1 ∧ p.1 ≤ Q₀ ∧ p.2 < p.1 ∧ Nat.gcd p.2 p.1 = 1 := by
      intro p hp
      rw [hFPdef, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      exact ⟨hp.1.1.1, hp.1.1.2, hp.2.1, hp.2.2⟩
    refine points_large_sieve FP (fun p => (p.2 : ℝ) / p.1) hδpos ?_ ?_ w' a
      (fun n => (n : ℤ) - (n₀ : ℤ)) ?_ hF ?_
    · -- separation
      intro p hp p' hp' hne
      obtain ⟨h1, h2, h3, h4⟩ := hmemFP p hp
      obtain ⟨h1', h2', h3', h4'⟩ := hmemFP p' hp'
      have hne2 : ¬(p.1 = p'.1 ∧ p.2 = p'.2) := by
        intro h
        exact hne (Prod.ext h.1 h.2)
      have hsep := farey_sep_abs h1 h1' h4 h4' hne2
      refine le_trans ?_ hsep
      have hq1 : (p.1 : ℝ) ≤ Q := le_trans (by exact_mod_cast h2) hQ₀R
      have hq2 : (p'.1 : ℝ) ≤ Q := le_trans (by exact_mod_cast h2') hQ₀R
      have hp1p : (0 : ℝ) < p.1 := by exact_mod_cast h1
      have hp2p : (0 : ℝ) < p'.1 := by exact_mod_cast h1'
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith
    · -- range
      intro p hp
      obtain ⟨h1, h2, h3, h4⟩ := hmemFP p hp
      have hp1p : (0 : ℝ) < p.1 := by exact_mod_cast h1
      constructor
      · positivity
      · have h5 : (p.2 : ℝ) ≤ (p.1 : ℝ) - 1 := by
          have : (p.2 + 1 : ℕ) ≤ p.1 := h3
          have := (Nat.cast_le (α := ℝ)).mpr this
          push_cast at this
          linarith
        have h6 : (p.2 : ℝ) / p.1 ≤ 1 - 1 / p.1 := by
          rw [div_le_iff₀ hp1p]
          field_simp
          linarith
        have h7 : 1 / Q ^ 2 ≤ 1 / (p.1 : ℝ) := by
          apply div_le_div_of_nonneg_left (by norm_num) hp1p
          nlinarith [hQ₀R, (show (p.1 : ℝ) ≤ Q₀ by exact_mod_cast h2)]
        linarith
    · -- frequency injectivity
      intro n _ m _ h
      omega
    · -- frequency bound
      intro n hn
      have := hνF n hn
      rw [show (((n : ℤ) - (n₀ : ℤ) : ℤ) : ℝ) = (n : ℝ) - (n₀ : ℝ) by push_cast; ring]
      exact this
  -- collect
  have hone : 1 / (1 / Q ^ 2) = Q ^ 2 := one_div_one_div _
  calc ∑ f ∈ Finset.Icc 1 Q₀, Real.log (Q / f) * Block f
      ≤ ∑ f ∈ Finset.Icc 1 Q₀,
          ∑ r ∈ (Finset.Icc 1 Q₀).filter
            (fun r => r * f ≤ Q₀ ∧ Squarefree r ∧ Nat.Coprime r f),
            ((f : ℝ) / (Nat.totient (r * f))) * Block f :=
        Finset.sum_le_sum hstep1
    _ = ∑ q ∈ Finset.Icc 1 Q₀, ∑ p ∈ PP.filter (fun p => p.2 * p.1 = q),
          ((p.1 : ℝ) / (Nat.totient (p.2 * p.1))) * Block p.1 := by
        rw [hregroup, hfiber]
    _ ≤ ∑ q ∈ Finset.Icc 1 Q₀,
          ∑ v ∈ (Finset.range q).filter (fun v => Nat.gcd v q = 1),
            ‖∑ n ∈ w', a n * eAt ((n : ℤ) - (n₀ : ℤ)) ((v : ℝ) / q)‖ ^ 2 :=
        Finset.sum_le_sum hstep3
    _ = ∑ p ∈ FP, ‖∑ n ∈ w', a n * eAt ((n : ℤ) - (n₀ : ℤ)) ((p.2 : ℝ) / p.1)‖ ^ 2 :=
        hstep4
    _ ≤ (1 / (1 / Q ^ 2) + 4 * π * F) * ∑ n ∈ w', ‖a n‖ ^ 2 := hstep5
    _ = (Q ^ 2 + 4 * π * F) * ∑ n ∈ w', ‖a n‖ ^ 2 := by rw [hone]

/-! ### Assembly helpers -/

/-- Window mean squares are integrable over `ℝ`. -/
lemma window_integrable {ι : Type*} (s : Finset ι) (c : ι → ℂ) (lam : ι → ℝ)
    (d2 : ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => ‖∑ i ∈ s.filter (fun i => |lam i - x| ≤ d2), c i‖ ^ 2) := by
  set I : ι → Set ℝ := fun i => Set.Icc (lam i - d2) (lam i + d2) with hIdef
  set U : ℝ → ℂ := fun x => ∑ i ∈ s, Set.indicator (I i) (fun _ => c i) x with hUdef
  have hmem : ∀ (i : ι) (x : ℝ), x ∈ I i ↔ |lam i - x| ≤ d2 := by
    intro i x
    rw [hIdef]
    simp only [Set.mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hU : ∀ x : ℝ, (∑ i ∈ s.filter (fun i => |lam i - x| ≤ d2), c i) = U x := by
    intro x
    rw [hUdef, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Set.indicator_apply]
    by_cases h : x ∈ I i
    · rw [if_pos ((hmem i x).mp h), if_pos h]
    · rw [if_neg (fun hc => h ((hmem i x).mpr hc)), if_neg h]
  have hprod : ∀ (i j : ι) (x : ℝ),
      Set.indicator (I i) (fun _ => c i) x * conj (Set.indicator (I j) (fun _ => c j) x)
        = Set.indicator (I i ∩ I j) (fun _ => c i * conj (c j)) x := by
    intro i j x
    by_cases h1 : x ∈ I i <;> by_cases h2 : x ∈ I j <;>
      simp [h1, h2]
  have hIint : ∀ i j : ι, MeasureTheory.Integrable
      (fun x => Set.indicator (I i ∩ I j) (fun _ => c i * conj (c j)) x) := by
    intro i j
    rw [MeasureTheory.integrable_indicator_iff
      ((measurableSet_Icc).inter (measurableSet_Icc))]
    refine MeasureTheory.integrableOn_const ?_
    refine ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono Set.inter_subset_left) ?_)
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hCint : MeasureTheory.Integrable (fun x => U x * conj (U x)) := by
    have hpt : ∀ x : ℝ, U x * conj (U x)
        = ∑ i ∈ s, ∑ j ∈ s, Set.indicator (I i ∩ I j) (fun _ => c i * conj (c j)) x := by
      intro x
      rw [hUdef]
      simp only
      rw [map_sum, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hprod i j x
    refine MeasureTheory.Integrable.congr ?_
      (Filter.Eventually.of_forall fun x => (hpt x).symm)
    exact MeasureTheory.integrable_finsetSum _ fun i _ =>
      MeasureTheory.integrable_finsetSum _ fun j _ => hIint i j
  have hre := hCint.re
  refine MeasureTheory.Integrable.congr hre
    (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [hU x]
  exact (norm_sq_eq_mul_conj_re (U x)).symm

/-- Sifted integers are coprime to all moduli up to `Q`. -/
lemma coprime_of_minFac {Q : ℝ} {n : ℕ} (h : Q < (n.minFac : ℝ)) {q : ℕ}
    (h1 : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q) : Nat.Coprime n q := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra h2
  set g : ℕ := Nat.gcd n q with hgdef
  have hg1 : 0 < g := Nat.gcd_pos_of_pos_right n (by omega)
  have hg2 : 2 ≤ g := by omega
  set p : ℕ := g.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := dvd_trans (Nat.minFac_dvd g) (Nat.gcd_dvd_left n q)
  have hpq : p ∣ q := dvd_trans (Nat.minFac_dvd g) (Nat.gcd_dvd_right n q)
  have h3 : n.minFac ≤ p := Nat.minFac_le_of_dvd hp.two_le hpn
  have h4 : p ≤ q := Nat.le_of_dvd (by omega) hpq
  have h5 : (n.minFac : ℝ) ≤ q := by exact_mod_cast le_trans h3 h4
  linarith

/-- The lossy exponential-ratio numeric: `24πT(e^{π/(4T)} − 1) ≤ 91` for `T ≥ 1`. -/
lemma exp_ratio_bound {T : ℝ} (hT : 1 ≤ T) :
    24 * π * T * (Real.exp (π / (4 * T)) - 1) ≤ 91 := by
  have hT0 : (0 : ℝ) < T := by linarith
  set u : ℝ := π / (4 * T) with hudef
  have hu0 : 0 < u := by positivity
  have huπ4 : u ≤ π / 4 := by
    rw [hudef]
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num)
    linarith
  have hπ : π < 3.1416 := Real.pi_lt_d4
  have hu1 : |u| ≤ 1 := by
    rw [abs_of_pos hu0]
    nlinarith
  -- cubic Taylor bound
  have hexp := Real.exp_bound hu1 (by norm_num : 0 < 3)
  have hsum : ∑ i ∈ Finset.range 3, u ^ i / (Nat.factorial i) = 1 + u + u ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num [Nat.factorial]
  rw [hsum] at hexp
  have hcube2 : Real.exp u - 1 ≤ u + u ^ 2 / 2 + (2 / 9) * u ^ 3 := by
    have h5 := le_trans (le_abs_self _) hexp
    rw [abs_of_pos hu0] at h5
    norm_num [Nat.factorial] at h5
    nlinarith [h5]
  have hTu : T * u = π / 4 := by
    rw [hudef]
    field_simp
  have hexpand : 24 * π * T * (u + u ^ 2 / 2 + (2 / 9) * u ^ 3)
      = 6 * π ^ 2 + 3 * π ^ 2 * u + (4 * π ^ 2 / 3) * u ^ 2 := by
    have h1 : 24 * π * T * u = 6 * π ^ 2 := by
      rw [show 24 * π * T * u = 24 * π * (T * u) by ring, hTu]
      ring
    have h2 : 24 * π * T * (u ^ 2 / 2) = 3 * π ^ 2 * u := by
      rw [show 24 * π * T * (u ^ 2 / 2) = 12 * π * (T * u) * u by ring, hTu]
      ring
    have h3 : 24 * π * T * ((2 / 9) * u ^ 3) = (4 * π ^ 2 / 3) * u ^ 2 := by
      rw [show 24 * π * T * ((2 / 9) * u ^ 3) = (16 / 3) * π * (T * u) * u ^ 2 by ring, hTu]
      ring
    linarith [h1, h2, h3]
  have hbound : 24 * π * T * (Real.exp u - 1)
      ≤ 6 * π ^ 2 + 3 * π ^ 2 * u + (4 * π ^ 2 / 3) * u ^ 2 := by
    rw [← hexpand]
    refine mul_le_mul_of_nonneg_left hcube2 (by positivity)
  have hufin : 3 * π ^ 2 * u + (4 * π ^ 2 / 3) * u ^ 2
      ≤ 3 * π ^ 2 * (π / 4) + (4 * π ^ 2 / 3) * (π / 4) ^ 2 := by
    have h1 : u ^ 2 ≤ (π / 4) ^ 2 := by nlinarith
    nlinarith [Real.pi_pos, sq_nonneg π]
  have hnum : 6 * π ^ 2 + 3 * π ^ 2 * (π / 4) + (4 * π ^ 2 / 3) * (π / 4) ^ 2 ≤ 91 := by
    have hπ0 : (3 : ℝ) < π := Real.pi_gt_three
    have h2 : π ^ 2 < 9.8697 := by nlinarith
    have h3 : π ^ 3 < 31.007 := by nlinarith
    have h4 : π ^ 4 < 97.42 := by nlinarith
    nlinarith [h2, h3, h4]
  linarith

/-- **Pointwise window bound** (the per-`x` sieve with per-`n` weights). -/
lemma pointwise_window_bound {Q T : ℝ} (hQ : 2 ≤ Q) (hT : 1 ≤ T)
    (s : Finset ℕ) (a : ℕ → ℂ) (hsift : ∀ n ∈ s, Q < (n.minFac : ℝ)) (x : ℝ) :
    ∑ f ∈ Finset.Icc 1 ⌊Q⌋₊, Real.log (Q / f)
        * ∑ ψ ∈ primChars f,
            ‖∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
              a n * ψ ((n : ZMod f))‖ ^ 2
      ≤ ∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
          (Q ^ 2 + 2 * π * (Real.exp (π / (4 * T)) - 1) * n + 4 * π) * ‖a n‖ ^ 2 := by
  have hT0 : (0 : ℝ) < T := by linarith
  set δ2 : ℝ := π / (8 * T) with hδ2def
  set W : Finset ℕ := s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ δ2) with hWdef
  have hn2 : ∀ n ∈ W, 2 ≤ n := by
    intro n hn
    have hns : n ∈ s := Finset.mem_of_mem_filter n hn
    have h1 := hsift n hns
    by_contra h2
    interval_cases n
    · rw [Nat.minFac_zero] at h1
      norm_num at h1
      linarith
    · rw [Nat.minFac_one] at h1
      norm_num at h1
      linarith
  rcases W.eq_empty_or_nonempty with hW | hW
  · rw [hW]
    simp only [Finset.sum_empty, norm_zero]
    rw [show (0 : ℝ) = ∑ f ∈ Finset.Icc 1 ⌊Q⌋₊, Real.log (Q / f) * ∑ _ψ ∈ primChars f,
        ((0 : ℝ) ^ 2) from by simp]
    simp
  · set A : ℕ := W.min' hW with hAdef
    set B : ℕ := W.max' hW with hBdef
    set n₀ : ℕ := (A + B) / 2 with hn₀def
    set F : ℝ := ((B : ℝ) - A) / 2 + 1 with hFdef
    have hAB : A ≤ B := W.min'_le _ (W.max'_mem hW)
    have hABR : (A : ℝ) ≤ B := by exact_mod_cast hAB
    have hF : 0 < F := by rw [hFdef]; linarith
    -- exponential window bounds
    have hwin : ∀ n ∈ W, Real.exp (-x - δ2) ≤ (n : ℝ)
        ∧ (n : ℝ) ≤ Real.exp (-x + δ2) := by
      intro n hn
      have h1 : |(-Real.log n) - x| ≤ δ2 := (Finset.mem_filter.mp hn).2
      have h2 : 2 ≤ n := hn2 n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      rw [abs_le] at h1
      constructor
      · calc Real.exp (-x - δ2) ≤ Real.exp (Real.log n) :=
            Real.exp_le_exp.mpr (by linarith [h1.2])
          _ = n := Real.exp_log hn0
      · calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log hn0).symm
          _ ≤ Real.exp (-x + δ2) := Real.exp_le_exp.mpr (by linarith [h1.1])
    have hAlow : Real.exp (-x - δ2) ≤ (A : ℝ) := (hwin A (W.min'_mem hW)).1
    have hBhigh : (B : ℝ) ≤ Real.exp (-x + δ2) := (hwin B (W.max'_mem hW)).2
    -- the frequency bound
    have hn₀bounds : 2 * n₀ ≤ A + B ∧ A + B ≤ 2 * n₀ + 1 := by
      rw [hn₀def]
      omega
    have hνF : ∀ n ∈ W, |(n : ℝ) - (n₀ : ℝ)| ≤ F := by
      intro n hn
      have h1 : A ≤ n := W.min'_le n hn
      have h2 : n ≤ B := W.le_max' n hn
      have h1R : (A : ℝ) ≤ n := by exact_mod_cast h1
      have h2R : (n : ℝ) ≤ B := by exact_mod_cast h2
      have h3 : (2 * n₀ : ℝ) ≤ A + B := by exact_mod_cast hn₀bounds.1
      have h4 : ((A : ℝ) + B) ≤ 2 * n₀ + 1 := by exact_mod_cast hn₀bounds.2
      rw [abs_le, hFdef]
      constructor <;> linarith
    -- coprimality
    have hcop : ∀ n ∈ W, ∀ q : ℕ, 1 ≤ q → q ≤ ⌊Q⌋₊ → Nat.Coprime n q := by
      intro n hn q hq1 hq2
      have hns : n ∈ s := Finset.mem_of_mem_filter n hn
      refine coprime_of_minFac (hsift n hns) hq1 ?_
      calc (q : ℝ) ≤ (⌊Q⌋₊ : ℝ) := by exact_mod_cast hq2
        _ ≤ Q := Nat.floor_le (by linarith)
    have hmain := window_sieve hQ W a n₀ hF hcop hνF
    -- per-n weight domination
    set ρ : ℝ := Real.exp (π / (4 * T)) - 1 with hρdef
    have hρ0 : 0 ≤ ρ := by
      rw [hρdef]
      have := Real.one_le_exp (show (0 : ℝ) ≤ π / (4 * T) by positivity)
      linarith
    have hBA : ∀ n ∈ W, (B : ℝ) - A ≤ ρ * n := by
      intro n hn
      have h1 : (A : ℝ) ≤ n := by exact_mod_cast W.min'_le n hn
      have h2 : Real.exp (-x + δ2) = Real.exp (-x - δ2) * Real.exp (π / (4 * T)) := by
        rw [← Real.exp_add]
        congr 1
        rw [hδ2def]
        field_simp
        ring
      have h3 : (B : ℝ) - A ≤ Real.exp (-x - δ2) * ρ := by
        rw [hρdef]
        nlinarith [hAlow, hBhigh, h2, Real.exp_pos (-x - δ2)]
      calc (B : ℝ) - A ≤ Real.exp (-x - δ2) * ρ := h3
        _ ≤ (n : ℝ) * ρ := by
            refine mul_le_mul_of_nonneg_right ?_ hρ0
            linarith [hAlow]
        _ = ρ * n := by ring
    have hweight : ∀ n ∈ W, (Q ^ 2 + 4 * π * F) * ‖a n‖ ^ 2
        ≤ (Q ^ 2 + 2 * π * ρ * n + 4 * π) * ‖a n‖ ^ 2 := by
      intro n hn
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      have h1 := hBA n hn
      rw [hFdef]
      have hπ0 := Real.pi_pos
      nlinarith [h1]
    calc ∑ f ∈ Finset.Icc 1 ⌊Q⌋₊, Real.log (Q / f)
          * ∑ ψ ∈ primChars f, ‖∑ n ∈ W, a n * ψ ((n : ZMod f))‖ ^ 2
        ≤ (Q ^ 2 + 4 * π * F) * ∑ n ∈ W, ‖a n‖ ^ 2 := hmain
      _ = ∑ n ∈ W, (Q ^ 2 + 4 * π * F) * ‖a n‖ ^ 2 := Finset.mul_sum _ _ _
      _ ≤ ∑ n ∈ W, (Q ^ 2 + 2 * π * ρ * n + 4 * π) * ‖a n‖ ^ 2 :=
          Finset.sum_le_sum hweight

/-- The `x`-integral of the window weights: each `n` contributes measure
`π/(4T)`. -/
lemma integral_window_weight {T : ℝ} (hT : 1 ≤ T) (s : Finset ℕ) (g : ℕ → ℝ) :
    ∫ x : ℝ, ∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)), g n
      = (π / (4 * T)) * ∑ n ∈ s, g n := by
  have hT0 : (0 : ℝ) < T := by linarith
  set δ2 : ℝ := π / (8 * T) with hδ2def
  have hδ2 : 0 < δ2 := by rw [hδ2def]; positivity
  set I : ℕ → Set ℝ := fun n => Set.Icc (-Real.log n - δ2) (-Real.log n + δ2) with hIdef
  have hmem : ∀ (n : ℕ) (x : ℝ), x ∈ I n ↔ |(-Real.log n) - x| ≤ δ2 := by
    intro n x
    rw [hIdef]
    simp only [Set.mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hpt : ∀ x : ℝ, ∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ δ2), g n
      = ∑ n ∈ s, Set.indicator (I n) (fun _ => g n) x := by
    intro x
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Set.indicator_apply]
    by_cases h : x ∈ I n
    · rw [if_pos ((hmem n x).mp h), if_pos h]
    · rw [if_neg (fun hc => h ((hmem n x).mpr hc)), if_neg h]
  have hIint : ∀ n : ℕ, MeasureTheory.Integrable
      (fun x => Set.indicator (I n) (fun _ => g n) x) := by
    intro n
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
    refine MeasureTheory.integrableOn_const ?_
    refine ne_of_lt ?_
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_finsetSum _ (fun n _ => hIint n)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MeasureTheory.integral_indicator_const _ measurableSet_Icc,
    MeasureTheory.measureReal_def]
  rw [Real.volume_Icc, smul_eq_mul]
  have h1 : (-Real.log n + δ2) - (-Real.log n - δ2) = 2 * δ2 := by ring
  rw [h1, ENNReal.toReal_ofReal (by positivity)]
  rw [hδ2def]
  congr 1
  field_simp
  ring

/-- Window weight sums are integrable over `ℝ`. -/
lemma window_sum_integrable (s : Finset ℕ) (g : ℕ → ℝ) (lam : ℕ → ℝ) (d2 : ℝ) :
    MeasureTheory.Integrable
      (fun x : ℝ => ∑ n ∈ s.filter (fun n : ℕ => |lam n - x| ≤ d2), g n) := by
  set I : ℕ → Set ℝ := fun n => Set.Icc (lam n - d2) (lam n + d2) with hIdef
  have hmem : ∀ (n : ℕ) (x : ℝ), x ∈ I n ↔ |lam n - x| ≤ d2 := by
    intro n x
    rw [hIdef]
    simp only [Set.mem_Icc, abs_le]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hpt : ∀ x : ℝ, ∑ n ∈ s.filter (fun n : ℕ => |lam n - x| ≤ d2), g n
      = ∑ n ∈ s, Set.indicator (I n) (fun _ => g n) x := by
    intro x
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Set.indicator_apply]
    by_cases h : x ∈ I n
    · rw [if_pos ((hmem n x).mp h), if_pos h]
    · rw [if_neg (fun hc => h ((hmem n x).mpr hc)), if_neg h]
  refine MeasureTheory.Integrable.congr ?_ (Filter.Eventually.of_forall fun x => (hpt x).symm)
  refine MeasureTheory.integrable_finsetSum _ fun n _ => ?_
  rw [MeasureTheory.integrable_indicator_iff measurableSet_Icc]
  refine MeasureTheory.integrableOn_const (ne_of_lt ?_)
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

/-! ### The frozen main theorem -/

set_option maxHeartbeats 2000000 in
/-- **Pre-sifted multiplicative large sieve, t-integrated** (Gallagher
1970, Theorem 4, lossy constants).  Coefficients supported on integers
with least prime factor exceeding `Q`; the weight `log (Q/f)` on the
conductor-`f` block is the pre-sift gain and is load-critical for
log-freeness. -/
theorem presifted_large_sieve {Q T : ℝ} (hQ : 2 ≤ Q) (hT : 1 ≤ T)
    (s : Finset ℕ) (a : ℕ → ℂ)
    (hsift : ∀ n ∈ s, Q < (n.minFac : ℝ)) :
    ∑ f ∈ Finset.Icc 1 ⌊Q⌋₊, Real.log (Q / f) *
      ∑ ψ ∈ primChars f,
        ∫ t in (-T)..T,
          ‖∑ n ∈ s, a n * ψ n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2
    ≤ 100 * ∑ n ∈ s, ((n : ℝ) + Q ^ 2 * T) * ‖a n‖ ^ 2 := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hπ0 := Real.pi_pos
  have hn2 : ∀ n ∈ s, 2 ≤ n := by
    intro n hn
    have h1 := hsift n hn
    by_contra h2
    interval_cases n
    · rw [Nat.minFac_zero] at h1
      norm_num at h1
      linarith
    · rw [Nat.minFac_one] at h1
      norm_num at h1
      linarith
  set ρ : ℝ := Real.exp (π / (4 * T)) - 1 with hρdef
  -- Step A: cpow conversion and smoothing, per (f, ψ)
  have hA : ∀ f ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ ψ ∈ primChars f,
      (∫ t in (-T)..T, ‖∑ n ∈ s, a n * ψ n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2)
        ≤ 48 * T ^ 2 / π * ∫ x : ℝ,
            ‖∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
              (a n * ψ ((n : ZMod f)))‖ ^ 2 := by
    intro f _ ψ _
    have hconv : ∀ t : ℝ, (∑ n ∈ s, a n * ψ n * (n : ℂ) ^ (-(t : ℂ) * Complex.I))
        = ∑ n ∈ s, (a n * ψ ((n : ZMod f)))
            * Complex.exp (((-Real.log n) * t : ℝ) * Complex.I) := by
      intro t
      refine Finset.sum_congr rfl fun n hn => ?_
      have h2 : 2 ≤ n := hn2 n hn
      have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      congr 1
      rw [Complex.cpow_def_of_ne_zero hn0]
      congr 1
      rw [show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_log (Nat.cast_nonneg n)]
      push_cast
      ring
    have hcong : (∫ t in (-T)..T, ‖∑ n ∈ s, a n * ψ n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2)
        = ∫ t in (-T)..T, ‖∑ n ∈ s, (a n * ψ ((n : ZMod f)))
            * Complex.exp (((-Real.log n) * t : ℝ) * Complex.I)‖ ^ 2 :=
      intervalIntegral.integral_congr fun t _ => by rw [hconv t]
    rw [hcong]
    exact t_integral_le hT s (fun n => a n * ψ ((n : ZMod f))) (fun n => -Real.log n)
  -- Step B: bound the outer sum and swap sums with the x-integral
  have hlognn : ∀ f ∈ Finset.Icc 1 ⌊Q⌋₊, 0 ≤ Real.log (Q / f) := by
    intro f hf
    obtain ⟨hf1, hf2⟩ := Finset.mem_Icc.mp hf
    have hfR : (f : ℝ) ≤ Q := le_trans (by exact_mod_cast hf2) (Nat.floor_le (by linarith))
    have hf0 : (0 : ℝ) < f := by exact_mod_cast hf1
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hf0]
    linarith
  have hB : ∑ f ∈ Finset.Icc 1 ⌊Q⌋₊, Real.log (Q / f) *
        ∑ ψ ∈ primChars f,
          ∫ t in (-T)..T, ‖∑ n ∈ s, a n * ψ n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2
      ≤ ∑ f ∈ Finset.Icc 1 ⌊Q⌋₊, Real.log (Q / f) *
          ∑ ψ ∈ primChars f, 48 * T ^ 2 / π * ∫ x : ℝ,
            ‖∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
              (a n * ψ ((n : ZMod f)))‖ ^ 2 := by
    refine Finset.sum_le_sum fun f hf => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hlognn f hf)
    exact Finset.sum_le_sum fun ψ hψ => hA f hf ψ hψ
  have hWint : ∀ (f : ℕ) (ψ : DirichletCharacter ℂ f), MeasureTheory.Integrable
      (fun x : ℝ => ‖∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
        (a n * ψ ((n : ZMod f)))‖ ^ 2) :=
    fun f ψ => window_integrable s (fun n => a n * ψ ((n : ZMod f)))
      (fun n => -Real.log n) (π / (8 * T))
  have hswap : ∑ f ∈ Finset.Icc 1 ⌊Q⌋₊, Real.log (Q / f) *
        ∑ ψ ∈ primChars f, 48 * T ^ 2 / π * ∫ x : ℝ,
          ‖∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
            (a n * ψ ((n : ZMod f)))‖ ^ 2
      = 48 * T ^ 2 / π * ∫ x : ℝ, ∑ f ∈ Finset.Icc 1 ⌊Q⌋₊, Real.log (Q / f) *
          ∑ ψ ∈ primChars f,
            ‖∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
              (a n * ψ ((n : ZMod f)))‖ ^ 2 := by
    have h1 : ∀ f ∈ Finset.Icc 1 ⌊Q⌋₊, Real.log (Q / f) *
          ∑ ψ ∈ primChars f, 48 * T ^ 2 / π * ∫ x : ℝ,
            ‖∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
              (a n * ψ ((n : ZMod f)))‖ ^ 2
        = 48 * T ^ 2 / π * ∫ x : ℝ, Real.log (Q / f) *
            ∑ ψ ∈ primChars f,
              ‖∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
                (a n * ψ ((n : ZMod f)))‖ ^ 2 := by
      intro f _
      rw [← Finset.mul_sum, ← MeasureTheory.integral_finsetSum _ (fun ψ _ => hWint f ψ),
        MeasureTheory.integral_const_mul]
      ring
    have h2 : ∀ f : ℕ, MeasureTheory.Integrable (fun x : ℝ => Real.log (Q / f) *
        ∑ ψ ∈ primChars f,
          ‖∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
            (a n * ψ ((n : ZMod f)))‖ ^ 2) := fun f =>
      (MeasureTheory.integrable_finsetSum _ (fun ψ _ => hWint f ψ)).const_mul _
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
      ← MeasureTheory.integral_finsetSum _ (fun f _ => h2 f)]
  -- Step C: the pointwise sieve under the integral
  have hHint : MeasureTheory.Integrable (fun x : ℝ =>
      ∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
        (Q ^ 2 + 2 * π * ρ * n + 4 * π) * ‖a n‖ ^ 2) :=
    window_sum_integrable s _ _ _
  have hC : (∫ x : ℝ, ∑ f ∈ Finset.Icc 1 ⌊Q⌋₊, Real.log (Q / f) *
        ∑ ψ ∈ primChars f,
          ‖∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
            (a n * ψ ((n : ZMod f)))‖ ^ 2)
      ≤ ∫ x : ℝ, ∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
          (Q ^ 2 + 2 * π * ρ * n + 4 * π) * ‖a n‖ ^ 2 := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ hHint ?_
    · refine Filter.Eventually.of_forall fun x => ?_
      refine Finset.sum_nonneg fun f hf => ?_
      exact mul_nonneg (hlognn f hf) (Finset.sum_nonneg fun ψ _ => by positivity)
    · refine Filter.Eventually.of_forall fun x => ?_
      exact pointwise_window_bound hQ hT s a hsift x
  -- Step D: evaluate the weight integral and close numerically
  have hD : (∫ x : ℝ, ∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
        (Q ^ 2 + 2 * π * ρ * n + 4 * π) * ‖a n‖ ^ 2)
      = (π / (4 * T)) * ∑ n ∈ s, (Q ^ 2 + 2 * π * ρ * n + 4 * π) * ‖a n‖ ^ 2 :=
    integral_window_weight hT s _
  have hconst : 48 * T ^ 2 / π * (π / (4 * T)) = 12 * T := by
    field_simp
    ring
  have hnum : ∀ n ∈ s, 12 * T * ((Q ^ 2 + 2 * π * ρ * n + 4 * π) * ‖a n‖ ^ 2)
      ≤ 100 * (((n : ℝ) + Q ^ 2 * T) * ‖a n‖ ^ 2) := by
    intro n _
    have h91 := exp_ratio_bound hT
    have hρ0 : 0 ≤ ρ := by
      rw [hρdef]
      have := Real.one_le_exp (show (0 : ℝ) ≤ π / (4 * T) by positivity)
      linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hQ4 : (4 : ℝ) ≤ Q ^ 2 := by nlinarith
    have hπd4 : π < 3.1416 := Real.pi_lt_d4
    have e1 : 12 * T * (2 * π * ρ) * n ≤ 91 * n := by
      have h2 : 24 * π * T * ρ ≤ 91 := by
        rw [hρdef]
        exact h91
      nlinarith [mul_le_mul_of_nonneg_right h2 hn0]
    have e2 : 12 * T * (4 * π) ≤ 12 * π * (Q ^ 2 * T) := by
      have h4 : (0 : ℝ) ≤ 12 * π * ((Q ^ 2 - 4) * T) :=
        mul_nonneg (by positivity) (mul_nonneg (by linarith) hT0.le)
      nlinarith [h4]
    have e3 : 12 * π * (Q ^ 2 * T) ≤ 38 * (Q ^ 2 * T) := by
      have h3 : (0 : ℝ) ≤ Q ^ 2 * T := by positivity
      nlinarith
    have hcoef : 12 * T * (Q ^ 2 + 2 * π * ρ * n + 4 * π)
        ≤ 100 * ((n : ℝ) + Q ^ 2 * T) := by
      nlinarith [e1, e2, e3]
    have ha0 : (0 : ℝ) ≤ ‖a n‖ ^ 2 := by positivity
    calc 12 * T * ((Q ^ 2 + 2 * π * ρ * n + 4 * π) * ‖a n‖ ^ 2)
        = (12 * T * (Q ^ 2 + 2 * π * ρ * n + 4 * π)) * ‖a n‖ ^ 2 := by ring
      _ ≤ (100 * ((n : ℝ) + Q ^ 2 * T)) * ‖a n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef ha0
      _ = 100 * (((n : ℝ) + Q ^ 2 * T) * ‖a n‖ ^ 2) := by ring
  calc ∑ f ∈ Finset.Icc 1 ⌊Q⌋₊, Real.log (Q / f) *
        ∑ ψ ∈ primChars f,
          ∫ t in (-T)..T, ‖∑ n ∈ s, a n * ψ n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2
      ≤ ∑ f ∈ Finset.Icc 1 ⌊Q⌋₊, Real.log (Q / f) *
          ∑ ψ ∈ primChars f, 48 * T ^ 2 / π * ∫ x : ℝ,
            ‖∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
              (a n * ψ ((n : ZMod f)))‖ ^ 2 := hB
    _ = 48 * T ^ 2 / π * ∫ x : ℝ, ∑ f ∈ Finset.Icc 1 ⌊Q⌋₊, Real.log (Q / f) *
          ∑ ψ ∈ primChars f,
            ‖∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
              (a n * ψ ((n : ZMod f)))‖ ^ 2 := hswap
    _ ≤ 48 * T ^ 2 / π * ∫ x : ℝ,
          ∑ n ∈ s.filter (fun n : ℕ => |(-Real.log n) - x| ≤ π / (8 * T)),
            (Q ^ 2 + 2 * π * ρ * n + 4 * π) * ‖a n‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hC (by positivity)
    _ = 48 * T ^ 2 / π * ((π / (4 * T)) * ∑ n ∈ s,
          (Q ^ 2 + 2 * π * ρ * n + 4 * π) * ‖a n‖ ^ 2) := by rw [hD]
    _ = 12 * T * ∑ n ∈ s, (Q ^ 2 + 2 * π * ρ * n + 4 * π) * ‖a n‖ ^ 2 := by
        rw [← mul_assoc, hconst]
    _ = ∑ n ∈ s, 12 * T * ((Q ^ 2 + 2 * π * ρ * n + 4 * π) * ‖a n‖ ^ 2) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ n ∈ s, 100 * (((n : ℝ) + Q ^ 2 * T) * ‖a n‖ ^ 2) :=
        Finset.sum_le_sum hnum
    _ = 100 * ∑ n ∈ s, ((n : ℝ) + Q ^ 2 * T) * ‖a n‖ ^ 2 :=
        (Finset.mul_sum _ _ _).symm

end LargeSieve
end Carmichael
