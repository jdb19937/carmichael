/-
Route Z, sorties Z9b + Z10: the `𝓑`-membership package at `B = 21/100` from
T2.1 (`Carmichael/T21.lean`), the two elementary hypotheses of
`pigeonhole_of_BMembership`, and AGP Theorem 3.1 (the pigeonhole) at
`B = 21/100`, conditional only on `T21.DensityInputs`.

STATEMENTS

  theorem piLower_of_density (hden : T21.DensityInputs) : PiLower
  theorem brunTitchmarsh_holds : BrunTitchmarsh
  noncomputable def bMembership21 (hden : T21.DensityInputs) : BMembership (21/100)

  theorem pigeonhole_21 (hden : T21.DensityInputs) :
      ∃ D z₃ : ℕ, ∀ x L : ℕ, z₃ < x → 1 < L → Squarefree L →
        (∀ q : ℕ, q.Prime → q ∣ L → (q : ℝ) ≤ (x : ℝ) ^ ((79 : ℝ) / 200)) →
        (∑ q ∈ L.primeFactors, (1 : ℝ) / q) ≤ 79 / 3200 →
        ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ (x : ℝ) ^ ((79 : ℝ) / 100) ∧ k.Coprime L ∧
          (2 : ℝ) ^ (-(D : ℝ) - 2) / Real.log x *
            ((L.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (x : ℝ) ^ ((21 : ℝ) / 100))).card : ℝ)
          ≤ ((L.divisors.filter (fun d => d * k + 1 ≤ x ∧ (d * k + 1).Prime)).card : ℝ)

  theorem pigeonhole_21' (hden : T21.DensityInputs) : same, with the verbatim
      hypothesis `∑ 1/q ≤ 3/160` (`3/160 = 60/3200 ≤ 79/3200`).

DELIVERED
  * T2.1 instantiated once, at ε = 1/12 (`t21D`, `t21x₂`, `t21bad` and their
    specs), shared by `bMembership21` and `piLower_of_density`;
  * `piLower_of_density`: d = 1, a = 1, x := y in T2.1 gives θ(y) ≥ (11/12)y,
    hence π(y) ≥ (11/12)y/log y ≥ y/((11/10) log y) for y ≥ max(⌈x₂⌉, 2);
  * `brunTitchmarsh_holds`: `brunTitchmarsh_progression` with
    y₀ := ⌈exp(2·10⁸)⌉₊;
  * `bMembership21`: D := D(1/12), bad := 𝓓(x), x₂ := ⌈max(x₂(1/12), Y², 2)⌉₊
    where Y is the (ℕ-)threshold of `eventually_primePi_le` at ε' = 1/10;
    `lower` from θ(y;d,a) ≥ (11/12)y/φ(d), π(y;d,a) ≥ θ(y;d,a)/log y and
    Chebyshev π(y) ≤ (log 4 + 1/10)y/log y, since (log 4 + 1/10)/2 < 3/4 < 11/12;
  * `pigeonhole_21`, `pigeonhole_21'`.

DELTAS VS. routez/Z0a-ledger.md §5 / BVPLAN §1.4
  * Step (ii) (π-upper by partial summation from the d = 1 PNT) is replaced by
    Mathlib's Chebyshev bound `Chebyshev.eventually_primeCounting_le` in the
    repo form `eventually_primePi_le`: the factor 2 in the 𝓑-inequality absorbs
    log 4 + 1/10 < 1.4863 ≤ 2·(11/12), so no upper bound on θ is consumed and
    no `e^{13}`/`e^{17}` threshold is needed; the only thresholds are x₂(1/12),
    the Chebyshev threshold Y (absorbed as x ≥ Y², so y ≥ x^{79/100} ≥ Y), and 2.
  * ε = 1/12 (ledger: 1/8) so that one T2.1 instance also supplies `PiLower`
    with constant 11/10 (needs 1 − ε ≥ 10/11).  The generic consumer budget
    only improves with smaller ε.
  * `brunTitchmarsh_progression` already has the quantifier structure of
    `BrunTitchmarsh` (all m ≥ 2, no squarefreeness, `p % m = 1 % m`, real
    threshold `exp 200000000 ≤ y`); the bridge is the ceiling of the threshold.
-/
import Carmichael.T21
import Carmichael.BrunTitchmarsh

set_option autoImplicit false

namespace Carmichael

open Finset Filter

/-! ## T2.1 at ε = 1/12, choice-extracted -/

section T21Choice

variable (hden : T21.DensityInputs)
include hden

/-- T2.1 (`T21.theta_AP_T21`) at `ε = 1/12`. -/
theorem t21_twelfth :
    ∃ D : ℕ, ∃ x₂ : ℝ, ∃ bad : ℕ → Finset ℕ,
      (∀ x, (bad x).card ≤ D) ∧ (∀ x, ∀ m ∈ bad x, 2 ≤ m) ∧
      ∀ (x : ℕ) (d : ℕ) [NeZero d] (a : ZMod d) (y : ℝ), x₂ ≤ x → IsUnit a →
        (d : ℝ) ≤ (x : ℝ) ^ (191/900 : ℝ) → (d : ℝ) * (x : ℝ) ^ (709/900 : ℝ) ≤ y → y ≤ x →
        (∀ m ∈ bad x, ¬ m ∣ d) →
        |thetaAP a y - y / d.totient| ≤ (1 / 12 : ℝ) * y / d.totient :=
  T21.theta_AP_T21 hden (ε := (1 / 12 : ℝ)) (by norm_num) (by norm_num)

/-- The exceptional count `D(1/12)`. -/
noncomputable def t21D : ℕ := (t21_twelfth hden).choose

/-- The threshold `x₂(1/12)` (real). -/
noncomputable def t21x₂ : ℝ := (t21_twelfth hden).choose_spec.choose

/-- The exceptional set `𝓓(x)`. -/
noncomputable def t21bad : ℕ → Finset ℕ :=
  (t21_twelfth hden).choose_spec.choose_spec.choose

lemma t21bad_card : ∀ x, (t21bad hden x).card ≤ t21D hden :=
  (t21_twelfth hden).choose_spec.choose_spec.choose_spec.1

lemma t21bad_ge_two : ∀ x, ∀ m ∈ t21bad hden x, 2 ≤ m :=
  (t21_twelfth hden).choose_spec.choose_spec.choose_spec.2.1

lemma t21_theta : ∀ (x : ℕ) (d : ℕ) [NeZero d] (a : ZMod d) (y : ℝ),
    t21x₂ hden ≤ x → IsUnit a →
    (d : ℝ) ≤ (x : ℝ) ^ (191/900 : ℝ) → (d : ℝ) * (x : ℝ) ^ (709/900 : ℝ) ≤ y → y ≤ x →
    (∀ m ∈ t21bad hden x, ¬ m ∣ d) →
    |thetaAP a y - y / d.totient| ≤ (1 / 12 : ℝ) * y / d.totient :=
  (t21_twelfth hden).choose_spec.choose_spec.choose_spec.2.2

end T21Choice

/-! ## The Chebyshev upper bound, threshold extracted -/

/-- `eventually_primePi_le` at `ε' = 1/10`, with an explicit `ℕ`-threshold. -/
theorem cheb_exists :
    ∃ N : ℕ, ∀ z : ℕ, N ≤ z →
      (primePi z : ℝ) ≤ (Real.log 4 + 1 / 10) * z / Real.log z :=
  Filter.eventually_atTop.mp (eventually_primePi_le (by norm_num))

/-- The Chebyshev threshold. -/
noncomputable def chebY : ℕ := cheb_exists.choose

lemma chebY_spec : ∀ z : ℕ, chebY ≤ z →
    (primePi z : ℝ) ≤ (Real.log 4 + 1 / 10) * z / Real.log z :=
  cheb_exists.choose_spec

lemma log_four_lt : Real.log 4 < 139 / 100 := by
  have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h4, Real.log_pow]
  have := Real.log_two_lt_d9
  push_cast
  linarith

/-! ## `PiLower` from the `d = 1` case of T2.1 -/

/-- Chebyshev/PNT lower bound `π(y) ≥ y/((11/10) log y)` from T2.1 at `d = 1`. -/
theorem piLower_of_density (hden : T21.DensityInputs) : PiLower := by
  refine ⟨max ⌈t21x₂ hden⌉₊ 2, fun y hy => ?_⟩
  have hy2 : 2 ≤ y := le_trans (le_max_right _ _) hy
  have hyR : (2 : ℝ) ≤ y := by exact_mod_cast hy2
  have hx₂ : t21x₂ hden ≤ (y : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast le_trans (le_max_left _ _) hy)
  have hy1 : (1 : ℝ) < y := by linarith
  have hlog : 0 < Real.log y := Real.log_pos hy1
  have hunit : IsUnit ((1 : ℕ) : ZMod 1) := by rw [Nat.cast_one]; exact isUnit_one
  have hθ := t21_theta hden y 1 ((1 : ℕ) : ZMod 1) (y : ℝ) hx₂ hunit
    (by rw [Nat.cast_one]; exact Real.one_le_rpow (by linarith) (by norm_num))
    (by rw [Nat.cast_one, one_mul]; exact Real.rpow_le_self_of_one_le (by linarith) (by norm_num))
    le_rfl
    (fun m hm hdvd => by
      have h2 := t21bad_ge_two hden y m hm
      have h1 := Nat.le_of_dvd one_pos hdvd
      omega)
  simp only [Nat.totient_one, Nat.cast_one, div_one] at hθ
  have hθlow : (11 / 12 : ℝ) * y ≤ thetaAP ((1 : ℕ) : ZMod 1) (y : ℝ) := by
    have := (abs_le.mp hθ).1
    linarith
  have hπ := le_piAP_of_le_thetaAP ((1 : ℕ) : ZMod 1) hy1 hθlow
  rw [piAP_natCast_eq_card] at hπ
  have hcount : ((Finset.range (y + 1)).filter (fun p => p.Prime ∧ p % 1 = 1 % 1)).card
      = primePi y := by
    unfold primePi
    congr 1
    ext p
    simp only [Finset.mem_filter, Nat.mod_one, and_true]
  rw [hcount] at hπ
  calc (y : ℝ) / ((11 : ℝ) / 10 * Real.log y) ≤ (11 / 12 : ℝ) * y / Real.log y := by
        rw [div_le_div_iff₀ (by positivity) hlog]
        nlinarith
    _ ≤ _ := hπ

/-! ## `BrunTitchmarsh` from sortie Z2 -/

/-- Brun--Titchmarsh in the consumer's form, from `brunTitchmarsh_progression`. -/
theorem brunTitchmarsh_holds : BrunTitchmarsh := by
  refine ⟨⌈Real.exp 200000000⌉₊, fun y m hy hm2 hmy => ?_⟩
  exact brunTitchmarsh_progression y m hm2 hmy
    (le_trans (Nat.le_ceil _) (by exact_mod_cast hy))

/-! ## The `𝓑`-membership package at `B = 21/100` -/

/-- `𝓑`-membership at `B = 21/100` (AGP p. 705), from T2.1 at `ε = 1/12` and
Chebyshev's upper bound. -/
noncomputable def bMembership21 (hden : T21.DensityInputs) : BMembership (21 / 100) where
  D := t21D hden
  x₂ := ⌈max (t21x₂ hden) (max (((max chebY 1 : ℕ) : ℝ) ^ 2) 2)⌉₊
  bad := t21bad hden
  bad_card := t21bad_card hden
  bad_ge_two := t21bad_ge_two hden
  lower := by
    intro x y d a hx hd hcop hdB hdy hyx hbad
    have : NeZero d := ⟨hd.ne'⟩
    obtain ⟨Y, hYdef⟩ : ∃ Y : ℕ, Y = max chebY 1 := ⟨_, rfl⟩
    rw [← hYdef] at hx
    have hY1 : (1 : ℝ) ≤ Y := by
      have : 1 ≤ Y := hYdef ▸ le_max_right _ _
      exact_mod_cast this
    have hYcheb : chebY ≤ Y := hYdef ▸ le_max_left _ _
    have hxR : max (t21x₂ hden) (max ((Y : ℝ) ^ 2) 2) ≤ (x : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast hx)
    have hx₂ : t21x₂ hden ≤ (x : ℝ) := le_trans (le_max_left _ _) hxR
    have hxY : (Y : ℝ) ^ 2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hxR
    have hx2 : (2 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hxR
    have hx1 : (1 : ℝ) ≤ x := by linarith
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    -- the T2.1 hypotheses
    have hdB' : (d : ℝ) ≤ (x : ℝ) ^ (191 / 900 : ℝ) :=
      le_trans hdB (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
    have hdy' : (d : ℝ) * (x : ℝ) ^ (709 / 900 : ℝ) ≤ (y : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (by positivity)) hdy
    have hunit : IsUnit (a : ZMod d) := (ZMod.isUnit_iff_coprime a d).mpr hcop
    have hθ := t21_theta hden x d (a : ZMod d) (y : ℝ) hx₂ hunit hdB' hdy' hyx hbad
    -- positivity
    have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
    have hy_ge : (x : ℝ) ^ (1 - 21 / 100 : ℝ) ≤ y :=
      le_trans (le_mul_of_one_le_left (by positivity) hdR) hdy
    have hy1 : (1 : ℝ) < y :=
      lt_of_lt_of_le (Real.one_lt_rpow (by linarith) (by norm_num)) hy_ge
    have hlog : 0 < Real.log y := Real.log_pos hy1
    have hy0 : (0 : ℝ) ≤ y := by linarith
    -- the Chebyshev threshold: `Y ≤ x^{1/2} ≤ x^{79/100} ≤ y`
    have hYy : Y ≤ y := by
      have h1 : (Y : ℝ) ≤ (x : ℝ) ^ (1 - 21 / 100 : ℝ) := by
        calc (Y : ℝ) = (Y : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (Y : ℝ) ^ (2 * (1 - 21 / 100) : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
          _ = ((Y : ℝ) ^ 2) ^ (1 - 21 / 100 : ℝ) := by
              rw [Real.rpow_mul (by linarith), Real.rpow_two]
          _ ≤ (x : ℝ) ^ (1 - 21 / 100 : ℝ) := Real.rpow_le_rpow (by positivity) hxY (by norm_num)
      exact_mod_cast le_trans h1 hy_ge
    have hcheb := chebY_spec y (le_trans hYcheb hYy)
    rw [le_div_iff₀ hlog] at hcheb
    -- θ lower bound → π lower bound in the progression
    have hθlow : (11 / 12 : ℝ) * y / d.totient ≤ thetaAP (a : ZMod d) y := by
      have h := (abs_le.mp hθ).1
      have e : (11 / 12 : ℝ) * y / d.totient = y / d.totient - 1 / 12 * y / d.totient := by
        ring
      linarith
    have hπ := le_piAP_of_le_thetaAP (a : ZMod d) hy1 hθlow
    rw [piAP_natCast_eq_card] at hπ
    -- assemble: `π(y)/(2φ) ≤ (11/12) y/(φ log y) ≤ π(y; d, a)`
    have hmain : (primePi y : ℝ) / (2 * d.totient) ≤ (11 / 12 : ℝ) * y / d.totient / Real.log y := by
      rw [div_le_div_iff₀ (by positivity) hlog]
      have e2 : (11 / 12 : ℝ) * y / d.totient * (2 * d.totient) = 11 / 6 * y := by
        field_simp
        ring
      rw [e2]
      have h4 := log_four_lt
      have : (Real.log 4 + 1 / 10) * y ≤ 11 / 6 * y :=
        mul_le_mul_of_nonneg_right (by linarith) hy0
      linarith
    exact le_trans hmain hπ

/-! ## AGP Theorem 3.1 at `B = 21/100` -/

/-- **AGP Theorem 3.1 at `B = 21/100`**, conditional only on the two zone-density
interfaces `T21.DensityInputs`. -/
theorem pigeonhole_21 (hden : T21.DensityInputs) :
    ∃ D z₃ : ℕ, ∀ x L : ℕ, z₃ < x → 1 < L → Squarefree L →
      (∀ q : ℕ, q.Prime → q ∣ L → (q : ℝ) ≤ (x : ℝ) ^ ((79 : ℝ) / 200)) →
      (∑ q ∈ L.primeFactors, (1 : ℝ) / q) ≤ 79 / 3200 →
      ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ (x : ℝ) ^ ((79 : ℝ) / 100) ∧ k.Coprime L ∧
        (2 : ℝ) ^ (-(D : ℝ) - 2) / Real.log x *
          ((L.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (x : ℝ) ^ ((21 : ℝ) / 100))).card : ℝ)
        ≤ ((L.divisors.filter (fun d => d * k + 1 ≤ x ∧ (d * k + 1).Prime)).card : ℝ) := by
  have h := pigeonhole_of_BMembership (21 / 100) (by norm_num) (by norm_num)
    (bMembership21 hden) brunTitchmarsh_holds (piLower_of_density hden)
  have e1 : ((1 : ℝ) - 21 / 100) / 2 = 79 / 200 := by norm_num
  have e3 : ((1 : ℝ) - 21 / 100) / 32 = 79 / 3200 := by norm_num
  have e2 : ((1 : ℝ) - 21 / 100) = 79 / 100 := by norm_num
  rw [e1, e3, e2] at h
  exact h

/-- AGP Theorem 3.1 at `B = 21/100` with the repo's verbatim hypothesis
`∑_{q ∣ L} 1/q ≤ 3/160` (`AssumptionsWeak.pigeonhole` form with exponents
`79/200`, `79/100`, `21/100`). -/
theorem pigeonhole_21' (hden : T21.DensityInputs) :
    ∃ D z₃ : ℕ, ∀ x L : ℕ, z₃ < x → 1 < L → Squarefree L →
      (∀ q : ℕ, q.Prime → q ∣ L → (q : ℝ) ≤ (x : ℝ) ^ ((79 : ℝ) / 200)) →
      (∑ q ∈ L.primeFactors, (1 : ℝ) / q) ≤ 3 / 160 →
      ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ (x : ℝ) ^ ((79 : ℝ) / 100) ∧ k.Coprime L ∧
        (2 : ℝ) ^ (-(D : ℝ) - 2) / Real.log x *
          ((L.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (x : ℝ) ^ ((21 : ℝ) / 100))).card : ℝ)
        ≤ ((L.divisors.filter (fun d => d * k + 1 ≤ x ∧ (d * k + 1).Prime)).card : ℝ) := by
  obtain ⟨D, z₃, h⟩ := pigeonhole_21 hden
  exact ⟨D, z₃, fun x L hxz hL1 hL hq hS => h x L hxz hL1 hL hq (le_trans hS (by norm_num))⟩

end Carmichael
