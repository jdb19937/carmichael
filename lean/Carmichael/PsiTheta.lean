/-
Route Z sortie Z3: the π/ψ/θ conversion pack (lean/BVPLAN.md §4 item Z3, feeding
the T2.1 assembly of §1.3 via sortie Z9).

Progression versions of the Chebyshev functions and of the prime-counting
function, and the conversions between them:

* `psiAP a y`  = ψ(y; q, a) = ∑_{n ≤ y, n ≡ a (q)} Λ(n)   (built on Mathlib's
  `ArithmeticFunction.vonMangoldt.residueClass`);
* `thetaAP a y` = θ(y; q, a) = ∑_{p ≤ y prime, p ≡ a (q)} log p;
* `piAP a y`   = π(y; q, a) = #{p ≤ y prime : p ≡ a (q)};
* `psiChar χ y` = ψ(y, χ) = ∑_{n ≤ y} χ(n)·Λ(n)  (ℂ-valued).

Conversion lemmas, with every constant explicit:

* ψ−θ gap in progressions: `0 ≤ psiAP − thetaAP ≤ ψ(y) − θ(y) ≤ 2·√y·log y`
  (`thetaAP_le_psiAP`, `psiAP_sub_thetaAP_le_psi_sub_theta`,
  `psiAP_sub_thetaAP_le_sqrt_mul_log`; the global gap is Mathlib's
  `Chebyshev.psi_sub_theta_le`).
* θ→π lower conversion, partial-summation-free (each log p ≤ log y):
  `thetaAP_le_piAP_mul_log`, `le_piAP_of_le_thetaAP`, and the packaged
  `piAP_lower` (from a ψ-progression lower bound) and
  `piAP_lower_of_psiAP_lower` (the (1−ε) ψ-bound ⇒ (1−2ε) π-bound form of
  BVPLAN §1.3, with the √y-budget threshold as a named hypothesis).
* Chebyshev upper bound π(z) ≤ (log 4 + ε)·z/log z in the repo's `primePi`
  normal form: `eventually_primePi_le` (reusing Mathlib's
  `Chebyshev.eventually_primeCounting_le`, itself Abel summation +
  `Chebyshev.theta_le_log4_mul_x`).
* Orthogonality decomposition ψ(y; q, a) = φ(q)⁻¹·∑_{χ mod q} χ(a)⁻¹·ψ(y, χ):
  `psiAP_eq_inv_totient_mul_sum_psiChar` (engine:
  `DirichletCharacter.sum_char_inv_mul_char_eq` via Mathlib's
  `ArithmeticFunction.vonMangoldt.residueClass_apply`).
* Imprimitive→primitive correction ‖ψ(y,χ) − ψ(y,χ⋆)‖ ≤ ω(q)·log y
  (`psiChar_sub_psiChar_primitive_norm_le`; sharper than the planned
  ω·log y·log q + C — the difference is supported on prime powers p^k, p ∣ q,
  and each p contributes at most (log_p y)·log p ≤ log y).

Reused from Mathlib (NOT duplicated): `Chebyshev.psi`, `Chebyshev.theta`,
`Chebyshev.psi_sub_theta_le`, `Chebyshev.eventually_primeCounting_le`,
`ArithmeticFunction.vonMangoldt.residueClass` and `residueClass_apply`,
`DirichletCharacter.primitiveCharacter` / `conductor` /
`primitiveCharacter_apply_of_isCoprime` / `norm_le_one`.
-/
import Carmichael.PrimeCount

namespace Carmichael

open Finset Filter
open scoped ArithmeticFunction

/-! ## Definitions -/

section Defs

variable {q : ℕ}

/-- `ψ(y; q, a)`: the Chebyshev `ψ`-function restricted to the residue class
`a` mod `q`. -/
noncomputable def psiAP (a : ZMod q) (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt.residueClass a n

lemma psiAP_def (a : ZMod q) (y : ℝ) :
    psiAP a y = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      ArithmeticFunction.vonMangoldt.residueClass a n := rfl

/-- `θ(y; q, a)`: the Chebyshev `θ`-function restricted to the residue class
`a` mod `q`. -/
noncomputable def thetaAP (a : ZMod q) (y : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a),
    Real.log p

lemma thetaAP_def (a : ZMod q) (y : ℝ) :
    thetaAP a y
      = ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a),
          Real.log p := rfl

/-- `π(y; q, a)`: the number of primes `p ≤ y` with `p ≡ a (mod q)`. -/
noncomputable def piAP (a : ZMod q) (y : ℝ) : ℕ :=
  ((Finset.Ioc 0 ⌊y⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a)).card

lemma piAP_def (a : ZMod q) (y : ℝ) :
    piAP a y
      = ((Finset.Ioc 0 ⌊y⌋₊).filter
          (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a)).card := rfl

/-- `ψ(y, χ)`: the character-twisted Chebyshev `ψ`-function
`∑_{n ≤ y} χ(n)·Λ(n)`, with values in `ℂ`. -/
noncomputable def psiChar (χ : DirichletCharacter ℂ q) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

lemma psiChar_def (χ : DirichletCharacter ℂ q) (y : ℝ) :
    psiChar χ y
      = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, χ n * (ArithmeticFunction.vonMangoldt n : ℂ) := rfl

end Defs

/-! ## Basic comparisons -/

section Basic

variable {q : ℕ}

lemma psiAP_nonneg (a : ZMod q) (y : ℝ) : 0 ≤ psiAP a y :=
  Finset.sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt.residueClass_nonneg a n

lemma thetaAP_nonneg (a : ZMod q) (y : ℝ) : 0 ≤ thetaAP a y :=
  Finset.sum_nonneg fun p hp => by
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    exact Real.log_natCast_nonneg p

/-- `ψ(y; q, a)` as a plain filtered sum of `Λ`. -/
lemma psiAP_eq_sum_filter (a : ZMod q) (y : ℝ) :
    psiAP a y
      = ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n : ℕ => (n : ZMod q) = a), Λ n := by
  rw [psiAP_def, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : (n : ZMod q) = a <;>
    simp [ArithmeticFunction.vonMangoldt.residueClass, h]

/-- The progression `ψ` is dominated by the full `ψ`. -/
lemma psiAP_le_psi (a : ZMod q) (y : ℝ) : psiAP a y ≤ Chebyshev.psi y := by
  simp only [psiAP_def, Chebyshev.psi]
  exact Finset.sum_le_sum fun n _ =>
    ArithmeticFunction.vonMangoldt.residueClass_le a n

/-- `θ(y; q, a)` as a sum of `residueClass` over primes: the bridge between
`thetaAP` and `psiAP`. -/
lemma thetaAP_eq_sum_residueClass (a : ZMod q) (y : ℝ) :
    thetaAP a y
      = ∑ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun p : ℕ => p.Prime),
          ArithmeticFunction.vonMangoldt.residueClass a p := by
  rw [thetaAP_def, Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hp : n.Prime
  · by_cases hc : (n : ZMod q) = a
    · simp [hp, hc, ArithmeticFunction.vonMangoldt.residueClass,
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    · simp [hp, hc, ArithmeticFunction.vonMangoldt.residueClass]
  · simp [hp]

lemma thetaAP_le_psiAP (a : ZMod q) (y : ℝ) : thetaAP a y ≤ psiAP a y := by
  rw [thetaAP_eq_sum_residueClass, psiAP_def]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun n _ _ => ArithmeticFunction.vonMangoldt.residueClass_nonneg a n

/-- The progression `θ` is dominated by the full `θ`. -/
lemma thetaAP_le_theta (a : ZMod q) (y : ℝ) : thetaAP a y ≤ Chebyshev.theta y := by
  simp only [thetaAP_def, Chebyshev.theta]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Real.log_natCast_nonneg p
  intro p hp
  simp only [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

/-- The progression `π` is dominated by the full `π` (repo normal form). -/
lemma piAP_le_primePi (a : ZMod q) (y : ℝ) : piAP a y ≤ primePi ⌊y⌋₊ := by
  simp only [piAP_def, primePi]
  refine Finset.card_le_card fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
  obtain ⟨⟨hp0, hple⟩, hprime, _⟩ := hp
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, hprime⟩

/-- Bridge to the `p % d = a % d` normal form used by `BMembership`
(BVPLAN §1.4): for natural `a`, `z`, the progression prime count is the
`Finset.range`-filtered cardinality. -/
lemma piAP_natCast_eq_card (d a z : ℕ) :
    piAP (a : ZMod d) (z : ℝ)
      = ((Finset.range (z + 1)).filter
          (fun p : ℕ => p.Prime ∧ p % d = a % d)).card := by
  simp only [piAP_def, Nat.floor_natCast]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range,
    ZMod.natCast_eq_natCast_iff']
  constructor
  · rintro ⟨⟨hp0, hpz⟩, hp, hmod⟩
    exact ⟨by omega, hp, hmod⟩
  · rintro ⟨hpz, hp, hmod⟩
    exact ⟨⟨hp.pos, by omega⟩, hp, hmod⟩

end Basic

/-! ## The ψ−θ gap in progressions

The difference `ψ(y; q, a) − θ(y; q, a)` is supported on proper prime powers
and is bounded by the *global* gap `ψ(y) − θ(y)`, for which Mathlib supplies
the explicit bound `2·√y·log y` (`Chebyshev.psi_sub_theta_le`). -/

section Gap

variable {q : ℕ}

lemma psiAP_sub_thetaAP_nonneg (a : ZMod q) (y : ℝ) :
    0 ≤ psiAP a y - thetaAP a y :=
  sub_nonneg.mpr (thetaAP_le_psiAP a y)

/-- The progression ψ−θ gap is at most the full ψ−θ gap. -/
lemma psiAP_sub_thetaAP_le_psi_sub_theta (a : ZMod q) (y : ℝ) :
    psiAP a y - thetaAP a y ≤ Chebyshev.psi y - Chebyshev.theta y := by
  have hsplit :
      (∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n : ℕ => n.Prime),
          ArithmeticFunction.vonMangoldt.residueClass a n)
        + ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n : ℕ => ¬n.Prime),
            ArithmeticFunction.vonMangoldt.residueClass a n
      = psiAP a y := by
    rw [psiAP_def]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hle :
      ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n : ℕ => ¬n.Prime),
          ArithmeticFunction.vonMangoldt.residueClass a n
        ≤ ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n : ℕ => ¬n.Prime), Λ n :=
    Finset.sum_le_sum fun n _ => ArithmeticFunction.vonMangoldt.residueClass_le a n
  have hpsith := Chebyshev.psi_sub_theta_eq_sum_not_prime y
  rw [thetaAP_eq_sum_residueClass]
  linarith only [hsplit, hle, hpsith]

/-- Explicit ψ−θ gap in progressions: `ψ(y; q, a) − θ(y; q, a) ≤ 2·√y·log y`.
(Constant 2, from Mathlib's `Chebyshev.psi_sub_theta_le`; this supersedes the
planned `C·√y·log²y`.) -/
lemma psiAP_sub_thetaAP_le_sqrt_mul_log (a : ZMod q) {y : ℝ} (hy : 1 ≤ y) :
    psiAP a y - thetaAP a y ≤ 2 * Real.sqrt y * Real.log y :=
  (psiAP_sub_thetaAP_le_psi_sub_theta a y).trans (Chebyshev.psi_sub_theta_le hy)

end Gap

/-! ## θ → π conversion (lower bounds)

The cheap route: every prime counted by `θ(y; q, a)` satisfies `log p ≤ log y`,
so `θ(y; q, a) ≤ π(y; q, a)·log y` — no Abel summation needed for the lower
direction. -/

section PiLower

variable {q : ℕ}

/-- `θ(y; q, a) ≤ π(y; q, a) · log y`. -/
lemma thetaAP_le_piAP_mul_log (a : ZMod q) (y : ℝ) :
    thetaAP a y ≤ (piAP a y : ℝ) * Real.log y := by
  rw [thetaAP_def, piAP_def]
  have hbound : ∀ p ∈ (Finset.Ioc 0 ⌊y⌋₊).filter
      (fun p : ℕ => p.Prime ∧ (p : ZMod q) = a), Real.log p ≤ Real.log y := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨hp0, hple⟩, hprime, _⟩ := hp
    have h1y : (1 : ℝ) ≤ y :=
      (Nat.one_le_floor_iff y).mp (le_trans hprime.one_lt.le hple)
    have hpy : (p : ℝ) ≤ y :=
      le_trans (Nat.cast_le.mpr hple) (Nat.floor_le (by linarith))
    exact Real.log_le_log (by exact_mod_cast hp0) hpy
  refine le_trans (Finset.sum_le_card_nsmul _ _ (Real.log y) hbound) ?_
  rw [nsmul_eq_mul]

/-- Any lower bound on `θ(y; q, a)` transfers to `π(y; q, a)` after division
by `log y`. -/
lemma le_piAP_of_le_thetaAP (a : ZMod q) {y c : ℝ} (hy : 1 < y)
    (h : c ≤ thetaAP a y) :
    c / Real.log y ≤ (piAP a y : ℝ) := by
  rw [div_le_iff₀ (Real.log_pos hy)]
  exact le_trans h (thetaAP_le_piAP_mul_log a y)

/-- Any lower bound on `ψ(y; q, a)` transfers to `θ(y; q, a)` at the cost of
the explicit gap `2·√y·log y`. -/
lemma le_thetaAP_of_le_psiAP (a : ZMod q) {y c : ℝ} (hy : 1 ≤ y)
    (h : c ≤ psiAP a y) :
    c - 2 * Real.sqrt y * Real.log y ≤ thetaAP a y := by
  have hgap := psiAP_sub_thetaAP_le_sqrt_mul_log a hy
  linarith only [hgap, h]

/-- ψ-form to π-form, fully packaged: a lower bound `c ≤ ψ(y; q, a)` yields
`(c − 2·√y·log y)/log y ≤ π(y; q, a)`. Downstream (Z9) instantiates
`c := (1−ε)·y/φ(q)`. -/
theorem piAP_lower (a : ZMod q) {y c : ℝ} (hy : 1 < y) (hψ : c ≤ psiAP a y) :
    (c - 2 * Real.sqrt y * Real.log y) / Real.log y ≤ (piAP a y : ℝ) :=
  le_piAP_of_le_thetaAP a hy (le_thetaAP_of_le_psiAP a hy.le hψ)

/-- The BVPLAN §1.3 shape: if `ψ(y; q, a) ≥ (1−ε)·y/φ(q)` and the prime-power
correction fits the ε-budget (the named threshold hypothesis `hgap`, i.e.
`2·√y·(log y)·φ(q) ≤ ε·y` — true for all large `y` once `φ(q) = y^{o(1)}`),
then `π(y; q, a) ≥ (1−2ε)·y/(φ(q)·log y)`. -/
theorem piAP_lower_of_psiAP_lower [NeZero q] (a : ZMod q) {y ε : ℝ} (hy : 1 < y)
    (hψ : (1 - ε) * y / q.totient ≤ psiAP a y)
    (hgap : 2 * Real.sqrt y * Real.log y * q.totient ≤ ε * y) :
    (1 - 2 * ε) * y / (q.totient * Real.log y) ≤ (piAP a y : ℝ) := by
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hφ : (0 : ℝ) < q.totient := by
    exact_mod_cast Nat.totient_pos.mpr q.pos_of_neZero
  refine le_trans ?_ (piAP_lower a hy hψ)
  rw [div_le_div_iff₀ (mul_pos hφ hlog) hlog]
  have hexp : ((1 - ε) * y / (q.totient : ℝ) - 2 * Real.sqrt y * Real.log y)
        * ((q.totient : ℝ) * Real.log y)
      = (1 - ε) * y * Real.log y
        - 2 * Real.sqrt y * Real.log y * (q.totient : ℝ) * Real.log y := by
    field_simp
  rw [hexp]
  have hmul := mul_le_mul_of_nonneg_right hgap hlog.le
  nlinarith only [hmul, hlog]

end PiLower

/-! ## The Chebyshev upper bound in repo normal form -/

/-- Chebyshev's upper bound `π(z) ≤ (log 4 + ε)·z / log z` (eventually), in the
repo's `primePi` normal form. Reuses Mathlib's
`Chebyshev.eventually_primeCounting_le`. -/
theorem eventually_primePi_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ z : ℕ in atTop, (primePi z : ℝ) ≤ (Real.log 4 + ε) * z / Real.log z := by
  have h := tendsto_natCast_atTop_atTop.eventually
    (Chebyshev.eventually_primeCounting_le hε)
  filter_upwards [h] with z hz
  rw [primePi_eq_primeCounting]
  simpa using hz

/-! ## Orthogonality decomposition

`ψ(y; q, a) = φ(q)⁻¹ · ∑_{χ mod q} χ(a)⁻¹ · ψ(y, χ)`, as an identity in `ℂ`
with the real `ψ(y; q, a)` coerced. Engine: Mathlib's
`DirichletCharacter.sum_char_inv_mul_char_eq`, prepackaged pointwise as
`ArithmeticFunction.vonMangoldt.residueClass_apply`. -/

section Orthogonality

variable {q : ℕ}

theorem psiAP_eq_inv_totient_mul_sum_psiChar [NeZero q] {a : ZMod q}
    (ha : IsUnit a) (y : ℝ) :
    (psiAP a y : ℂ)
      = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * psiChar χ y := by
  have hstep : (psiAP a y : ℂ)
      = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
          ((ArithmeticFunction.vonMangoldt.residueClass a n : ℝ) : ℂ) := by
    rw [psiAP_def]
    exact Complex.ofReal_sum _ _
  have hpt : ∀ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      ((ArithmeticFunction.vonMangoldt.residueClass a n : ℝ) : ℂ)
        = (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q,
            χ a⁻¹ * χ n * (ArithmeticFunction.vonMangoldt n : ℂ) :=
    fun n _ => ArithmeticFunction.vonMangoldt.residueClass_apply ha n
  rw [hstep, Finset.sum_congr rfl hpt, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [psiChar_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => mul_assoc _ _ _

end Orthogonality

/-! ## Imprimitive → primitive correction

`ψ(y, χ)` and `ψ(y, χ⋆)` (χ⋆ the primitive character inducing χ) differ only
on prime powers `p^k` with `p ∣ q`; each such `p` contributes at most
`(log_p y)·(log p) ≤ log y`, for a total of `ω(q)·log y`. -/

section Primitive

variable {q : ℕ}

/-- The primitive character inducing `χ` agrees with `χ` on naturals coprime
to the level. -/
lemma primitiveCharacter_natCast_eq_of_coprime (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn : n.Coprime q) :
    χ.primitiveCharacter (n : ZMod χ.conductor) = χ (n : ZMod q) := by
  have h : IsCoprime (n : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr hn
  have hval := DirichletCharacter.primitiveCharacter_apply_of_isCoprime χ h
  push_cast at hval
  exact hval

/-- The sum of `Λ(n)` over `n ≤ y` *not* coprime to `d` is at most
`ω(d)·log y` (here `ω(d) = d.primeFactors.card`): only prime powers `p^k`
with `p ∣ d` contribute, and each prime `p ∣ d` contributes
`(Nat.log p ⌊y⌋₊)·log p ≤ log y`. -/
lemma sum_vonMangoldt_not_coprime_le {d : ℕ} (hd : d ≠ 0) {y : ℝ} (hy : 1 ≤ y) :
    ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n : ℕ => ¬n.Coprime d), Λ n
      ≤ (d.primeFactors.card : ℝ) * Real.log y := by
  have hy0 : (0 : ℝ) ≤ y := le_trans zero_le_one hy
  have hM : ⌊y⌋₊ ≠ 0 := by
    have h1 : 1 ≤ ⌊y⌋₊ := (Nat.one_le_floor_iff y).mpr hy
    omega
  have hlogM : Real.log (⌊y⌋₊ : ℝ) ≤ Real.log y :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hM) (Nat.floor_le hy0)
  -- Step 1: the sum is supported on prime powers.
  have h1 : ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n : ℕ => ¬n.Coprime d), Λ n
      = ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter
          (fun n : ℕ => ¬n.Coprime d ∧ IsPrimePow n), Λ n := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hc : n.Coprime d
    · simp [hc]
    · by_cases hpp : IsPrimePow n
      · simp [hc, hpp]
      · simp [hc, hpp, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp]
  -- Step 2: those prime powers live in an explicit biUnion over p ∣ d.
  set X : Finset ℕ := d.primeFactors.biUnion
      (fun p : ℕ => (Finset.Icc 1 (Nat.log p ⌊y⌋₊)).image (fun k : ℕ => p ^ k))
    with hX
  have hsub : (Finset.Ioc 0 ⌊y⌋₊).filter
      (fun n : ℕ => ¬n.Coprime d ∧ IsPrimePow n) ⊆ X := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    obtain ⟨⟨hn0, hnM⟩, hnc, hpp⟩ := hn
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hpd : p ∣ d := by
      by_contra hnd
      exact hnc (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd))
    have hpmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpd, hd⟩
    have hklog : k ≤ Nat.log p ⌊y⌋₊ := Nat.le_log_of_pow_le hp.one_lt hnM
    simp only [hX, Finset.mem_biUnion]
    exact ⟨p, hpmem, Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk, hklog⟩, rfl⟩⟩
  have h2 : ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter
        (fun n : ℕ => ¬n.Coprime d ∧ IsPrimePow n), Λ n
      ≤ ∑ n ∈ X, Λ n :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub
      fun n _ _ => ArithmeticFunction.vonMangoldt_nonneg
  -- Step 3: evaluate the biUnion sum prime by prime.
  have hdisj : (d.primeFactors : Set ℕ).PairwiseDisjoint
      (fun p : ℕ => (Finset.Icc 1 (Nat.log p ⌊y⌋₊)).image (fun k : ℕ => p ^ k)) := by
    intro p hp p' hp' hne
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image,
      Finset.mem_Icc]
    rintro x ⟨k, ⟨hk1, _⟩, rfl⟩ ⟨k', ⟨hk1', _⟩, hx⟩
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hp)
    have hpp' : p'.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_coe.mp hp')
    exact hne (Nat.Prime.pow_inj' hpp' hpp (by omega) (by omega) hx).1.symm
  have h3 : ∑ n ∈ X, Λ n
      = ∑ p ∈ d.primeFactors, ∑ k ∈ Finset.Icc 1 (Nat.log p ⌊y⌋₊), Λ (p ^ k) := by
    rw [hX, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun p hp => ?_
    exact Finset.sum_image fun k _ k' _ h =>
      Nat.pow_right_injective (Nat.prime_of_mem_primeFactors hp).two_le h
  -- Step 4: each prime contributes at most log y.
  have h4 : ∀ p ∈ d.primeFactors,
      ∑ k ∈ Finset.Icc 1 (Nat.log p ⌊y⌋₊), Λ (p ^ k) ≤ Real.log y := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hval : ∀ k ∈ Finset.Icc 1 (Nat.log p ⌊y⌋₊), Λ (p ^ k) = Real.log p := by
      intro k hk
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
        ArithmeticFunction.vonMangoldt_apply_prime hpp]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    simp only [Nat.add_sub_cancel]
    have hpow : ((p ^ Nat.log p ⌊y⌋₊ : ℕ) : ℝ) ≤ (⌊y⌋₊ : ℝ) :=
      Nat.cast_le.mpr (Nat.pow_log_le_self p hM)
    have hp0 : (0 : ℝ) < ((p ^ Nat.log p ⌊y⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast pow_pos hpp.pos _
    have hlog := Real.log_le_log hp0 hpow
    rw [Nat.cast_pow, Real.log_pow] at hlog
    exact le_trans hlog hlogM
  calc ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n : ℕ => ¬n.Coprime d), Λ n
      = ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter
          (fun n : ℕ => ¬n.Coprime d ∧ IsPrimePow n), Λ n := h1
    _ ≤ ∑ n ∈ X, Λ n := h2
    _ = ∑ p ∈ d.primeFactors, ∑ k ∈ Finset.Icc 1 (Nat.log p ⌊y⌋₊), Λ (p ^ k) := h3
    _ ≤ ∑ p ∈ d.primeFactors, Real.log y := Finset.sum_le_sum h4
    _ = (d.primeFactors.card : ℝ) * Real.log y := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Imprimitive→primitive correction:
`‖ψ(y, χ) − ψ(y, χ⋆)‖ ≤ ω(q)·log y`, where `χ⋆ = χ.primitiveCharacter` is the
primitive character inducing `χ` and `ω(q) = q.primeFactors.card`. (Sharper
than the planned `ω(q)·log y·log q + C`.) -/
theorem psiChar_sub_psiChar_primitive_norm_le [NeZero q]
    (χ : DirichletCharacter ℂ q) {y : ℝ} (hy : 1 ≤ y) :
    ‖psiChar χ y - psiChar χ.primitiveCharacter y‖
      ≤ (q.primeFactors.card : ℝ) * Real.log y := by
  have hq : q ≠ 0 := NeZero.ne q
  rw [psiChar_def, psiChar_def, ← Finset.sum_sub_distrib]
  have hpt : ∀ n ∈ Finset.Ioc 0 ⌊y⌋₊,
      ‖χ n * (ArithmeticFunction.vonMangoldt n : ℂ)
          - χ.primitiveCharacter n * (ArithmeticFunction.vonMangoldt n : ℂ)‖
        ≤ (if n.Coprime q then 0 else Λ n) := by
    intro n _
    by_cases hn : n.Coprime q
    · rw [if_pos hn, primitiveCharacter_natCast_eq_of_coprime χ hn, sub_self,
        norm_zero]
    · rw [if_neg hn]
      have hunit : ¬IsUnit ((n : ZMod q)) := fun h =>
        hn ((ZMod.isUnit_iff_coprime n q).mp h)
      rw [MulChar.map_nonunit χ hunit, zero_mul, zero_sub, norm_neg, norm_mul]
      have h1 : ‖χ.primitiveCharacter ((n : ℕ) : ZMod χ.conductor)‖ ≤ 1 :=
        DirichletCharacter.norm_le_one _ _
      have h2 : ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖
          = ArithmeticFunction.vonMangoldt n := by
        rw [Complex.norm_real,
          Real.norm_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      rw [h2]
      calc ‖χ.primitiveCharacter ((n : ℕ) : ZMod χ.conductor)‖
            * ArithmeticFunction.vonMangoldt n
          ≤ 1 * ArithmeticFunction.vonMangoldt n :=
            mul_le_mul_of_nonneg_right h1 ArithmeticFunction.vonMangoldt_nonneg
        _ = ArithmeticFunction.vonMangoldt n := one_mul _
  have hsum : ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, (if n.Coprime q then 0 else Λ n)
      = ∑ n ∈ (Finset.Ioc 0 ⌊y⌋₊).filter (fun n : ℕ => ¬n.Coprime q), Λ n := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n.Coprime q <;> simp [hn]
  refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hpt) ?_)
  rw [hsum]
  exact sum_vonMangoldt_not_coprime_le hq hy

end Primitive

end Carmichael
