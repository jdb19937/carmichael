/-
Route Z, TZ-LITE File 5: the middle-regime census assembly.

STATUS: **DELIVERED.**  Both frozen §5.1 statements are proved, sorry-free and
axiom-clean (`propext`, `Classical.choice`, `Quot.sound`), verified with plain
`lake env lean`.  Namespace `Carmichael.CensusMid`.

DELIVERED (frozen, `routez/Z7-tzlite.md` §5.1, byte-identical):

* `censusCount_le_machine` — the machine bound
  `censusCount σ ν ⌊Z⌋₊ ≤ exp(1.2·10⁸ + 1.2·10⁹·(1−σ)·log(Z(ν+2)))` in the
  middle window.
* `midCensusHyp : Census.MidCensusHyp` — the Z7 discharge, derived from
  `censusCount_le_machine` by the §0.3 absorption arithmetic only
  (`Census.census_contract midCensusHyp` is now unconditional).

This is the only file allowed to reference `Census.censusC₂`.  The numeral
`10^(10⁹)` inside it is never unfolded under an evaluating tactic (§0.5):
`exp_le_tower` compares against it through `Real.exp_one_pow` and
`pow_le_pow_left₀` only, and `midCensusHyp` abstracts it to an opaque real
`Tw` and clears the defining equation before any arithmetic tactic runs.

Proof map (§5.2):

1. In-window facts, inlined in `censusCount_le_machine`: `L > 500` (from
   `1 − σ < 2·10⁻¹²` and `(1−σ)·L > 10⁻⁹`), `W = Z(ν+2) ≥ e⁵⁰⁰`,
   `η₀ = max(1−σ, 1/(12L)) ≤ 1/6000`, `η = 1.01·η₀ ≤ 1/5000`, `1 ≤ 12ηL`,
   `W⁵ ≤ Xone η L`; the `d = 1` term is `≤ 1` (`card_badChars_one`).
2. `perchar_window` — the Φ-trick: one zero `ρ = β + iγ` per bad character,
   `kderiv_detection` pointwise on `τ ∈ (γ − r, γ + r] ⊆ (−(ν+1), ν+1]`
   (with `(1−σ)² + r² ≤ η²`), integrated over `τ` (`setIntegral_mono_on`,
   `setIntegral_mono_set`) and Fubini-swapped (`integral_integral_swap` on
   `(volume.restrict (Ioc (−T) T)).prod (volume.restrict (Ioc X₁ X₂))`;
   integrability by `IntegrableOn.of_bound` from the delivered
   `norm_primeWindowSum_le`, joint measurability by
   `measurable_from_prod_countable_left` through `(τ, ⌊u⌋₊)`).
3. `sieve_at_u` — at each fixed `u ∈ (X₁, X₂]`, the whole family embeds into
   `presifted_large_sieve` (`Q = W²`, `T = ν + 1`, `s` = primes in
   `(X₁, u]`, `a p = log p / p`; `n^{−1−iτ} = n⁻¹·n^{−iτ}` by `cpow_add`);
   the conductor weight `log(W²/d) ≥ L` is divided out (THE log-free
   cancellation, §0.6 item 1); the sieve RHS is bounded by
   `100·∑ 2n·(log n/n)² = 200·∑ (log n)²/n` (`W⁴(ν+1) ≤ W⁵ ≤ X₁ < n`) and
   `sum_log_sq_div_le` (`∑_{p ≤ X₂} (log p)²/p ≤ 3e²(log X₂)²`, from File 4's
   diagonal bound `tsum_vonMangoldt_log_pow_rpow_le'` at `k = 1`,
   `u = 1/log X₂`; no Chebyshev input).
4. `family_bound` — steps 2 + 3 summed over the family
   (`integral_finsetSum` twice, `Integrable.integral_prod_right`), the
   pointwise `u`-bound integrated against `du/u` (`integral_one_div`):
   `2r·R·L ≤ 600e²·(η³·M·e^{6M})·(log X₂)²·(log X₂ − log X₁)`.
5. `budget_close` — the numeric walk (below) to
   `R ≤ exp(118000000 + 1190000000·(1−σ)·L)`.
6. `exp_le_tower` and the three §0.3 budget rows in `midCensusHyp`.

Numeric budget walk (§5.2 step 4), with `r = 0.14·η₀`, `η = 1.01·η₀`,
`η₀ = max(1−σ, 1/(12L))`, `M = Mdet η L = 6·N`, `N = Ndet η L`:

* `log X₂ = 16M/η`, `log X₂ − log X₁ ≤ 16M/η`, so the family bound reads
  `0.28·η₀·R·L ≤ 600e²·η³·M·e^{6M}·(16M/η)³ = 2457600·e²·M⁴·e^{6M}`
  (every `η⁻¹` cancelled against `η³`; no `η⁻¹` survives).
* clamp: `η₀·L ≥ 1/12`, so `(7/300)·R ≤ 2457600·e²·M⁴·e^{6M}`.
* `M⁴ ≤ 24·10⁸·e^{M/100}` (`pow_le_factorial_mul_exp` at `x = M/100`,
  `k = 4`) and `e² < 7.39`, so
  `R ≤ (300/7)·2457600·7.39·2.4·10⁹·e^{6.01M} ≤ 1.87·10¹⁸·e^{6.01M}
  ≤ e^{43 + 6.01M}` (`2.7⁴³ ≥ 1.87·10¹⁸`).
* clamp fold (both regimes of the `max` at once, `max(a,b) ≤ a + b`):
  `η·L ≤ 1.01·((1−σ)·L + 1/12)`, and `N < 7 + 28800000·η·L`, so
  `43 + 6.01·M = 43 + 36.06·N < 87409736 + 1048913280·(1−σ)·L
  ≤ 118000000 + 1190000000·(1−σ)·L`.
* `censusCount = card(badChars 1) + R ≤ 1 + e^{A} ≤ e^{A + 1}` with
  `A = 118000000 + 1190000000·(1−σ)·L`, and `A + 1` is under the frozen
  `120000000 + 1200000000·(1−σ)·L`.
* absorption rows: `1.2·10⁹·(1−σ) < 2.4·10⁻³ ≤ 1` gives
  `(ν+2)^{1.2·10⁹(1−σ)} ≤ ν + 2`; `1.2·10⁹ ≤ 10¹² = censusC₃`;
  `exp(1.2·10⁸) ≤ exp(10⁹) = e^{10⁹} ≤ 10^{10⁹}`.

DELTAS VS. THE SPEC.

1. `hσ : 39/40 ≤ σ` is unused in `censusCount_le_machine` (every window fact
   follows from `hσ1`, `hwin`, `hfloor`); it stays in the signature as frozen,
   with the unused-variable linter silenced by a `set_option ... in` line.
2. The integrals in the internal lemmas are `MeasureTheory` set integrals over
   `Set.Ioc` (`intervalIntegral.integral_of_le` bridges File 4's and File 2's
   `∫ x in a..b` forms); no frozen statement is affected.
3. The sieve RHS constant is `600e²(log X₂)²` (spec: `101(log X₂)²`), from the
   Dirichlet-series bound in place of a Mertens-type prime sum; absorbed in
   the budget walk above.
-/
import Carmichael.KDerivDetect
import Carmichael.LargeSieve
import Carmichael.Census

set_option autoImplicit false

open Complex Finset MeasureTheory Set
open ArithmeticFunction (vonMangoldt)
open scoped Classical

namespace Carmichael.CensusMid

/-! ### §1 The prime-sum bound -/

/-- `∑_{p ∈ s} (log p)²/p ≤ 3e²·(log X₂)²` for any finset `s` of primes bounded
by `X₂ ≥ e²⁰` (File 4's diagonal bound at `u = 1/log X₂`). -/
lemma sum_log_sq_div_le {X₂ : ℝ} (hX₂ : Real.exp 20 ≤ X₂) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ X₂) :
    ∑ p ∈ s, (Real.log p) ^ 2 / (p : ℝ)
      ≤ 3 * Real.exp 1 ^ 2 * (Real.log X₂) ^ 2 := by
  have hX₂pos : 0 < X₂ := lt_of_lt_of_le (Real.exp_pos _) hX₂
  have hℓ : 20 ≤ Real.log X₂ := by
    have := Real.log_le_log (Real.exp_pos 20) hX₂
    rwa [Real.log_exp] at this
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.log X₂ := ⟨_, rfl⟩
  rw [← hℓdef] at hℓ ⊢
  have hℓ0 : 0 < ℓ := by linarith
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = 1 / ℓ := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hudef]; positivity
  have hu20 : u ≤ 1/20 := by
    rw [hudef, div_le_div_iff₀ hℓ0 (by norm_num)]
    linarith
  have huℓ : u * ℓ = 1 := by rw [hudef]; field_simp
  -- the diagonal series
  set f : ℕ → ℝ := fun n =>
    vonMangoldt n * (Real.log n) ^ 1 * (n : ℝ) ^ (-(1 + u)) with hf
  have hfnonneg : ∀ n, 0 ≤ f n := by
    intro n
    simp only [hf]
    have h1 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have h2 := Real.log_natCast_nonneg n
    have h3 : (0:ℝ) ≤ (n : ℝ) ^ (-(1 + u)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    positivity
  have hsum : Summable f := summable_vonMangoldt_log_pow_rpow hu0 1
  have htsum : ∑' n, f n ≤ (Nat.factorial 1 : ℝ) * Real.exp 1 * ((1 : ℕ) + 2) / u ^ (1 + 1) :=
    tsum_vonMangoldt_log_pow_rpow_le' hu0 hu20 1
  have hpart : ∑ p ∈ s, f p ≤ ∑' n, f n :=
    hsum.sum_le_tsum s (fun n _ => hfnonneg n)
  -- termwise comparison
  have hterm : ∀ p ∈ s, (Real.log p) ^ 2 / (p : ℝ) ≤ Real.exp 1 * f p := by
    intro p hp
    obtain ⟨hprime, hpX⟩ := hs p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hΛ : vonMangoldt p = Real.log p := ArithmeticFunction.vonMangoldt_apply_prime hprime
    have hpu : (p : ℝ) ^ u ≤ Real.exp 1 := by
      calc (p : ℝ) ^ u ≤ X₂ ^ u := Real.rpow_le_rpow hp0.le hpX hu0.le
        _ = Real.exp (Real.log X₂ * u) := Real.rpow_def_of_pos hX₂pos u
        _ = Real.exp 1 := by rw [← hℓdef, mul_comm, huℓ]
    have hpu0 : 0 < (p : ℝ) ^ u := Real.rpow_pos_of_pos hp0 u
    have hsplit : (p : ℝ) ^ (-(1 + u)) = (p : ℝ)⁻¹ * ((p : ℝ) ^ u)⁻¹ := by
      rw [show -(1 + u) = (-1) + (-u) by ring, Real.rpow_add hp0, Real.rpow_neg_one,
        Real.rpow_neg hp0.le]
    simp only [hf, hΛ, pow_one, hsplit]
    have hlog0 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hkey : 1 ≤ Real.exp 1 * ((p : ℝ) ^ u)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpu0]
      linarith
    have hL2 : 0 ≤ (Real.log p) ^ 2 / (p : ℝ) := by positivity
    calc (Real.log p) ^ 2 / (p : ℝ) = (Real.log p) ^ 2 / (p : ℝ) * 1 := by ring
      _ ≤ (Real.log p) ^ 2 / (p : ℝ) * (Real.exp 1 * ((p : ℝ) ^ u)⁻¹) :=
          mul_le_mul_of_nonneg_left hkey hL2
      _ = Real.exp 1 * (Real.log p * Real.log p * ((p : ℝ)⁻¹ * ((p : ℝ) ^ u)⁻¹)) := by
          field_simp
  calc ∑ p ∈ s, (Real.log p) ^ 2 / (p : ℝ)
      ≤ ∑ p ∈ s, Real.exp 1 * f p := Finset.sum_le_sum hterm
    _ = Real.exp 1 * ∑ p ∈ s, f p := by rw [Finset.mul_sum]
    _ ≤ Real.exp 1 * ∑' n, f n :=
        mul_le_mul_of_nonneg_left hpart (Real.exp_pos _).le
    _ ≤ Real.exp 1 * ((Nat.factorial 1 : ℝ) * Real.exp 1 * ((1 : ℕ) + 2) / u ^ (1 + 1)) :=
        mul_le_mul_of_nonneg_left htsum (Real.exp_pos _).le
    _ = 3 * Real.exp 1 ^ 2 * ℓ ^ 2 := by
        have hℓne : ℓ ≠ 0 := hℓ0.ne'
        have h1 : (Nat.factorial 1 : ℝ) = 1 := by norm_num [Nat.factorial]
        have h2 : ((1 : ℕ) : ℝ) + 2 = 3 := by norm_num
        rw [h1, h2, hudef, div_pow, one_pow]
        rw [div_div_eq_mul_div]
        ring

/-! ### §2 The `d = 1` term -/

/-- At most one character mod `1`. -/
lemma card_badChars_one (σ ν : ℝ) : (Census.badChars σ ν 1).card ≤ 1 := by
  have h1 : (Census.badChars σ ν 1).card
      ≤ (univ : Finset (DirichletCharacter ℂ 1)).card := by
    rw [Census.badChars, dif_neg (by norm_num : (1:ℕ) ≠ 0)]
    exact Finset.card_filter_le _ _
  have h2 : (univ : Finset (DirichletCharacter ℂ 1)).card = 1 := by
    have h3 := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ 1
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h3, Nat.totient_one]
  omega

/-! ### §3 The numeric budget -/

/-- `e² < 7.39`. -/
lemma exp_one_sq_lt : Real.exp 1 ^ 2 < 7.39 := by
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  nlinarith

/-- `1.87·10¹⁸ ≤ e⁴³`. -/
lemma const_le_exp_43 : (1870000000000000000 : ℝ) ≤ Real.exp 43 := by
  have h := Real.exp_one_gt_d9
  have h27 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith
  have hpow : (2.7 : ℝ) ^ 43 ≤ Real.exp 1 ^ 43 :=
    pow_le_pow_left₀ (by norm_num) h27 43
  rw [Real.exp_one_pow] at hpow
  have h43 : ((43 : ℕ) : ℝ) = 43 := by norm_num
  rw [h43] at hpow
  have hnum : (1870000000000000000 : ℝ) ≤ (2.7 : ℝ) ^ 43 := by norm_num
  linarith

/-- `M⁴ ≤ 24·10⁸·e^{M/100}`. -/
lemma pow_four_le_exp (M : ℝ) (hM : 0 ≤ M) :
    M ^ 4 ≤ 2400000000 * Real.exp (M / 100) := by
  have h := pow_le_factorial_mul_exp (x := M / 100) (by positivity) 4
  have h4 : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h4] at h
  have : (M / 100) ^ 4 = M ^ 4 / 100000000 := by ring
  rw [this] at h
  linarith

/-- **Budget close** (§5.2 step 4): from the family bound, the count of bad
characters with `d ≥ 2` is at most `exp(118000000 + 1190000000·(1−σ)·L)`. -/
lemma budget_close {σ L η₀ η : ℝ} {R : ℕ} (hσ1 : σ ≤ 1) (hL : 500 < L)
    (hη₀ : η₀ = max (1 - σ) (1 / (12 * L))) (hη : η = 101 / 100 * η₀)
    (h : 2 * (7 / 50 * η₀) * (R : ℝ) * L
      ≤ 2457600 * Real.exp 1 ^ 2 * (Mdet η L : ℝ) ^ 4
          * Real.exp (6 * (Mdet η L : ℝ))) :
    (R : ℝ) ≤ Real.exp (118000000 + 1190000000 * (1 - σ) * L) := by
  have hL0 : 0 < L := by linarith
  have hσ0 : 0 ≤ 1 - σ := by linarith
  -- the clamp: `η₀·L ≥ 1/12`
  have hclamp : 1 / 12 ≤ η₀ * L := by
    have h1 : 1 / (12 * L) ≤ η₀ := by rw [hη₀]; exact le_max_right _ _
    calc 1 / 12 = 1 / (12 * L) * L := by field_simp
      _ ≤ η₀ * L := mul_le_mul_of_nonneg_right h1 hL0.le
  have hη₀0 : 0 ≤ η₀ := by
    rw [hη₀]; exact le_trans hσ0 (le_max_left _ _)
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  -- the fold of the clamp: `η₀·L ≤ (1−σ)·L + 1/12`
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (1 - σ) * L := ⟨_, rfl⟩
  have hP0 : 0 ≤ P := by rw [hP]; positivity
  have hfold : η₀ * L ≤ P + 1 / 12 := by
    have h1 : η₀ ≤ (1 - σ) + 1 / (12 * L) := by
      rw [hη₀]
      apply max_le
      · have : 0 ≤ 1 / (12 * L) := by positivity
        linarith
      · linarith
    calc η₀ * L ≤ ((1 - σ) + 1 / (12 * L)) * L := mul_le_mul_of_nonneg_right h1 hL0.le
      _ = P + 1 / 12 := by rw [hP]; field_simp
  have hηL : η * L ≤ 101 / 100 * (P + 1 / 12) := by
    rw [hη]
    calc 101 / 100 * η₀ * L = 101 / 100 * (η₀ * L) := by ring
      _ ≤ 101 / 100 * (P + 1 / 12) := by
          apply mul_le_mul_of_nonneg_left hfold (by norm_num)
  -- the parameters
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = Ndet η L := ⟨_, rfl⟩
  have hM : (Mdet η L : ℝ) = 6 * (N : ℝ) := by rw [Mdet_eq, hN]; push_cast; ring
  have hNlt : (N : ℝ) < 7 + 28800000 * η * L := by rw [hN]; exact Ndet_cast_lt η L hη0 hL0.le
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  rw [hM] at h
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = Real.exp (6 * (6 * (N : ℝ))) := ⟨_, rfl⟩
  rw [← hX] at h
  have hX0 : 0 < X := by rw [hX]; exact Real.exp_pos _
  -- step 1: `R ≤ (300/7)·2457600·e²·M⁴·X`
  have hR1 : (7 / 300 : ℝ) * R ≤ 2457600 * Real.exp 1 ^ 2 * (6 * (N : ℝ)) ^ 4 * X := by
    have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
    have h2 : (7 / 300 : ℝ) * R ≤ 2 * (7 / 50 * η₀) * (R : ℝ) * L := by
      have : (2 : ℝ) * (7 / 50 * η₀) * (R : ℝ) * L = (7 / 25) * (η₀ * L) * R := by ring
      rw [this]
      have h3 : (7 / 25 : ℝ) * (1 / 12) ≤ (7 / 25) * (η₀ * L) :=
        mul_le_mul_of_nonneg_left hclamp (by norm_num)
      nlinarith
    linarith
  -- step 2: `M⁴ ≤ 24·10⁸·e^{M/100}`, `e² < 7.39`
  have hM4 := pow_four_le_exp (6 * (N : ℝ)) (by positivity)
  have he2 := exp_one_sq_lt
  have he2_0 : 0 ≤ Real.exp 1 ^ 2 := by positivity
  have hE0 : 0 < Real.exp (6 * (N : ℝ) / 100) := Real.exp_pos _
  have hM4_0 : 0 ≤ (6 * (N : ℝ)) ^ 4 := by positivity
  have hR2 : (7 / 300 : ℝ) * R
      ≤ 2457600 * 7.39 * (2400000000 * Real.exp (6 * (N : ℝ) / 100)) * X := by
    calc (7 / 300 : ℝ) * R ≤ 2457600 * Real.exp 1 ^ 2 * (6 * (N : ℝ)) ^ 4 * X := hR1
      _ ≤ 2457600 * 7.39 * (6 * (N : ℝ)) ^ 4 * X := by
          apply mul_le_mul_of_nonneg_right _ hX0.le
          apply mul_le_mul_of_nonneg_right _ hM4_0
          apply mul_le_mul_of_nonneg_left he2.le (by norm_num)
      _ ≤ 2457600 * 7.39 * (2400000000 * Real.exp (6 * (N : ℝ) / 100)) * X := by
          apply mul_le_mul_of_nonneg_right _ hX0.le
          apply mul_le_mul_of_nonneg_left hM4 (by norm_num)
  -- step 3: collect into a single exponential
  have hR3 : (R : ℝ) ≤ Real.exp 43 * (Real.exp (6 * (N : ℝ) / 100) * X) := by
    have hc := const_le_exp_43
    have hEX : 0 ≤ Real.exp (6 * (N : ℝ) / 100) * X := by positivity
    have h1 : (R : ℝ) ≤ (300 / 7) * (2457600 * 7.39 * 2400000000)
        * (Real.exp (6 * (N : ℝ) / 100) * X) := by
      have := hR2
      nlinarith
    have h2 : (300 / 7 : ℝ) * (2457600 * 7.39 * 2400000000) ≤ 1870000000000000000 := by
      norm_num
    calc (R : ℝ) ≤ (300 / 7) * (2457600 * 7.39 * 2400000000)
          * (Real.exp (6 * (N : ℝ) / 100) * X) := h1
      _ ≤ 1870000000000000000 * (Real.exp (6 * (N : ℝ) / 100) * X) :=
          mul_le_mul_of_nonneg_right h2 hEX
      _ ≤ Real.exp 43 * (Real.exp (6 * (N : ℝ) / 100) * X) :=
          mul_le_mul_of_nonneg_right hc hEX
  rw [hX, ← Real.exp_add, ← Real.exp_add] at hR3
  -- step 4: the exponent
  refine hR3.trans (Real.exp_le_exp.mpr ?_)
  have hslope : 1190000000 * (1 - σ) * L = 1190000000 * P := by rw [hP]; ring
  rw [hslope]
  nlinarith [hNlt, hηL, hP0, hN0]

/-! ### §4 Measurability and integrability of the window sums -/

section Window

variable {q : ℕ}

/-- Joint measurability of `(τ, u) ↦ primeWindowSum χ τ X u`: the sum is a
function of `(τ, ⌊u⌋₊)`, continuous in `τ` for each floor value. -/
lemma measurable_uncurry_primeWindowSum (χ : DirichletCharacter ℂ q) (X : ℝ) :
    Measurable (fun p : ℝ × ℝ => primeWindowSum χ p.1 X p.2) := by
  have hH : Measurable (fun p : ℝ × ℕ =>
      ∑ n ∈ (Finset.Icc 1 p.2).filter (fun n : ℕ => n.Prime ∧ X < (n : ℝ)),
        χ n * (Real.log n : ℂ) * (n : ℂ) ^ (-(1 : ℂ) - (p.1 : ℂ) * Complex.I)) := by
    refine measurable_from_prod_countable_left fun m => ?_
    show Measurable (fun τ : ℝ =>
      ∑ n ∈ (Finset.Icc 1 m).filter (fun n : ℕ => n.Prime ∧ X < (n : ℝ)),
        χ n * (Real.log n : ℂ) * (n : ℂ) ^ (-(1 : ℂ) - (τ : ℂ) * Complex.I))
    refine Continuous.measurable ?_
    refine continuous_finsetSum _ fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).1
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    refine Continuous.mul continuous_const ?_
    refine Continuous.const_cpow ?_ (Or.inl hn0)
    fun_prop
  have hfl : Measurable (fun p : ℝ × ℝ => (p.1, ⌊p.2⌋₊)) :=
    measurable_fst.prodMk (Nat.measurable_floor.comp measurable_snd)
  have hcomp : (fun p : ℝ × ℝ => primeWindowSum χ p.1 X p.2)
      = (fun p : ℝ × ℕ =>
      ∑ n ∈ (Finset.Icc 1 p.2).filter (fun n : ℕ => n.Prime ∧ X < (n : ℝ)),
        χ n * (Real.log n : ℂ) * (n : ℂ) ^ (-(1 : ℂ) - (p.1 : ℂ) * Complex.I))
        ∘ (fun p : ℝ × ℝ => (p.1, ⌊p.2⌋₊)) := by
    funext p
    simp only [Function.comp, primeWindowSum]
  rw [hcomp]
  exact hH.comp hfl

/-- The integrand `‖S(τ,u)‖²/u` is jointly measurable. -/
lemma measurable_normSq_div (χ : DirichletCharacter ℂ q) (X : ℝ) :
    Measurable (Function.uncurry fun τ u : ℝ => ‖primeWindowSum χ τ X u‖ ^ 2 / u) :=
  ((measurable_uncurry_primeWindowSum χ X).norm.pow_const 2).div measurable_snd

/-- Product integrability of `‖S(τ,u)‖²/u` on `(−T, T] × (X₁, X₂]`. -/
lemma integrable_normSq_div (χ : DirichletCharacter ℂ q) {X₁ X₂ T : ℝ}
    (hX₁ : 0 < X₁) (hX₂ : Real.exp 20 ≤ X₂) :
    Integrable (Function.uncurry fun τ u : ℝ => ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u)
      ((volume.restrict (Ioc (-T) T)).prod (volume.restrict (Ioc X₁ X₂))) := by
  rw [Measure.prod_restrict]
  refine IntegrableOn.of_bound ?_ (measurable_normSq_div χ X₁).aestronglyMeasurable
    ((Real.exp 1 * (Real.log X₂ + 2)) ^ 2 / X₁) ?_
  · rw [Measure.prod_prod, Real.volume_Ioc, Real.volume_Ioc]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  · refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioc) ?_
    rintro ⟨τ, u⟩ ⟨_, hu⟩
    simp only [Function.uncurry_apply_pair]
    have hu0 : 0 < u := lt_trans hX₁ hu.1
    have hS := norm_primeWindowSum_le χ τ X₁ hX₂ hu.2
    have hB0 : 0 ≤ Real.exp 1 * (Real.log X₂ + 2) := le_trans (norm_nonneg _) hS
    have hnn : 0 ≤ ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u
        ≤ (Real.exp 1 * (Real.log X₂ + 2)) ^ 2 / u :=
          div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hS 2) hu0.le
      _ ≤ (Real.exp 1 * (Real.log X₂ + 2)) ^ 2 / X₁ :=
          div_le_div_of_nonneg_left (by positivity) hX₁ hu.1.le

end Window

/-! ### §5 The Φ-trick: one zero per bad character -/

/-- `Mdet ≥ 36`. -/
lemma thirtysix_le_Mdet {η L : ℝ} (hη : 0 ≤ η) (hL : 0 ≤ L) :
    (36 : ℝ) ≤ (Mdet η L : ℝ) := by
  have h := six_le_Ndet η L hη hL
  rw [Mdet_eq]
  exact_mod_cast (by omega : 36 ≤ 6 * Ndet η L)

/-- `Xtwo ≥ e²⁰`. -/
lemma exp_twenty_le_Xtwo {η L : ℝ} (hη0 : 0 < η) (hηup : η ≤ 1/5000) (hL : 0 ≤ L) :
    Real.exp 20 ≤ Xtwo η L := by
  have hM := thirtysix_le_Mdet hη0.le hL
  rw [Xtwo]
  apply Real.exp_le_exp.mpr
  rw [le_div_iff₀ hη0]
  nlinarith

/-- **The Φ-trick** (§5.2 step 2): a bad primitive character mod `d ≥ 2` has a
zero `ρ = β + iγ` in the box; `kderiv_detection` holds at every
`τ ∈ (γ − r, γ + r] ⊆ (−(ν+1), ν+1]`; integrating over `τ` and swapping the
order of integration gives the window lower bound `2r`. -/
lemma perchar_window {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d}
    {σ ν W L η r : ℝ}
    (hχ : χ ∈ Census.badChars σ ν d) (hd : 2 ≤ d)
    (hL : L = Real.log W) (hW : Real.exp 500 ≤ W)
    (hdW : (d : ℝ) ≤ W) (hνW : ν + 3 ≤ W)
    (hη0 : 0 < η) (hηup : η ≤ 1/5000) (hηlow : 1 ≤ 12 * η * L)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hσ1 : σ ≤ 1) (hdist : (1 - σ) ^ 2 + r ^ 2 ≤ η ^ 2) :
    2 * r ≤ η ^ 3 * (Mdet η L : ℝ) * Real.exp (6 * (Mdet η L : ℝ)) *
      ∫ u in Ioc (Xone η L) (Xtwo η L), ∫ τ in Ioc (-(ν + 1)) (ν + 1),
        ‖primeWindowSum χ τ (Xone η L) u‖ ^ 2 / u := by
  classical
  obtain ⟨hprim, hne⟩ := Census.mem_badChars.mp hχ
  obtain ⟨ρ, hρ⟩ := hne
  rw [mem_zeroFinset] at hρ
  obtain ⟨hρσ, hρ1, hρim, -, hρ0⟩ := hρ
  have hL500 : 500 ≤ L := by
    rw [hL]
    have := Real.log_le_log (Real.exp_pos 500) hW
    rwa [Real.log_exp] at this
  have hL0 : 0 < L := by linarith
  -- opaque abbreviations
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℝ, X₁ = Xone η L := ⟨_, rfl⟩
  obtain ⟨X₂, hX₂⟩ : ∃ X₂ : ℝ, X₂ = Xtwo η L := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = η ^ 3 * (Mdet η L : ℝ) * Real.exp (6 * (Mdet η L : ℝ)) :=
    ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ν + 1 := ⟨_, rfl⟩
  rw [← hX₁, ← hX₂, ← hc, ← hT]
  have hX₁pos : 0 < X₁ := by rw [hX₁]; exact Xone_pos _ _
  have hX₁X₂ : X₁ ≤ X₂ := by rw [hX₁, hX₂]; exact (Xone_lt_Xtwo hη0 hL0.le).le
  have hX₂20 : Real.exp 20 ≤ X₂ := by rw [hX₂]; exact exp_twenty_le_Xtwo hη0 hηup hL0.le
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  -- the integrand and its product integrability
  have hint : Integrable (Function.uncurry fun τ u : ℝ => ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u)
      ((volume.restrict (Ioc (-T) T)).prod (volume.restrict (Ioc X₁ X₂))) :=
    integrable_normSq_div χ hX₁pos hX₂20
  -- the inner `u`-integral as a function of `τ`
  have hGint : IntegrableOn
      (fun τ => ∫ u in Ioc X₁ X₂, ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u) (Ioc (-T) T) :=
    hint.integral_prod_left
  have hGnn : ∀ τ, 0 ≤ ∫ u in Ioc X₁ X₂, ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u := by
    intro τ
    refine setIntegral_nonneg measurableSet_Ioc fun u hu => ?_
    exact div_nonneg (by positivity) (le_of_lt (lt_trans hX₁pos hu.1))
  -- the detection at every `τ` of the window
  have hdet : ∀ τ ∈ Ioc (ρ.im - r) (ρ.im + r),
      (1 : ℝ) ≤ c * ∫ u in Ioc X₁ X₂, ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u := by
    intro τ hτ
    have hτγ : |τ - ρ.im| ≤ r := by
      rw [abs_le]; constructor <;> linarith [hτ.1, hτ.2]
    have hτW : |τ| + 2 ≤ W := by
      have h1 : |τ| ≤ |ρ.im| + |τ - ρ.im| := by
        calc |τ| = |ρ.im + (τ - ρ.im)| := by ring_nf
          _ ≤ |ρ.im| + |τ - ρ.im| := abs_add_le _ _
      linarith
    have hdistρ : dist ρ (1 + τ * Complex.I) ≤ η := by
      have hd2 : dist ρ (1 + τ * Complex.I) ^ 2 ≤ η ^ 2 := by
        rw [Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im]
        have h1 : (ρ.re - 1) * (ρ.re - 1) ≤ (1 - σ) ^ 2 := by nlinarith
        have h2 := abs_le.mp hτγ
        have h3 : (ρ.im - τ) * (ρ.im - τ) ≤ r ^ 2 := by nlinarith
        nlinarith
      have hd0 : 0 ≤ dist ρ (1 + τ * Complex.I) := dist_nonneg
      nlinarith
    have hzero : ∃ ρ' : ℂ, DirichletCharacter.LFunction χ ρ' = 0 ∧
        dist ρ' (1 + τ * Complex.I) ≤ η := ⟨ρ, hρ0, hdistρ⟩
    have hηlow' : 1 ≤ 12 * η * Real.log W := by rw [← hL]; exact hηlow
    have := kderiv_detection hprim hd hdW hτW hW hη0 hηup hηlow' hzero
    rw [← hL, ← hX₁, ← hX₂, ← hc, intervalIntegral.integral_of_le hX₁X₂] at this
    exact this
  -- the window sits inside `(−T, T]`
  have hJsub : Ioc (ρ.im - r) (ρ.im + r) ⊆ Ioc (-T) T := by
    intro τ hτ
    rw [hT]
    have := abs_le.mp hρim
    constructor <;> linarith [hτ.1, hτ.2]
  have h1 : ∫ τ in Ioc (ρ.im - r) (ρ.im + r), (1 : ℝ)
      ≤ ∫ τ in Ioc (ρ.im - r) (ρ.im + r),
          c * ∫ u in Ioc X₁ X₂, ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u := by
    refine setIntegral_mono_on (integrableOn_const ?_)
      ((hGint.mono_set hJsub).const_mul c) measurableSet_Ioc hdet
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have h2 : ∫ τ in Ioc (ρ.im - r) (ρ.im + r),
        c * ∫ u in Ioc X₁ X₂, ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u
      ≤ ∫ τ in Ioc (-T) T,
        c * ∫ u in Ioc X₁ X₂, ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u := by
    refine setIntegral_mono_set (hGint.const_mul c)
      (Filter.Eventually.of_forall fun τ => mul_nonneg hc0 (hGnn τ))
      (Filter.Eventually.of_forall fun τ hτ => hJsub hτ)
  have h3 : ∫ τ in Ioc (ρ.im - r) (ρ.im + r), (1 : ℝ) = 2 * r := by
    rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  have h4 : ∫ τ in Ioc (-T) T,
        c * ∫ u in Ioc X₁ X₂, ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u
      = c * ∫ u in Ioc X₁ X₂, ∫ τ in Ioc (-T) T,
          ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u := by
    rw [integral_const_mul]
    congr 1
    exact integral_integral_swap hint
  calc 2 * r = ∫ τ in Ioc (ρ.im - r) (ρ.im + r), (1 : ℝ) := h3.symm
    _ ≤ _ := h1
    _ ≤ _ := h2
    _ = _ := h4

/-! ### §6 The sieve at fixed `u` -/

/-- **The sieve step** (§5.2 step 3): at fixed `u ∈ (X₁, X₂]`, the τ-mean
squares of the family's window sums, weighted by the uniform conductor weight
`L ≤ log(W²/d)`, are bounded by `600e²(log X₂)²`. -/
lemma sieve_at_u {σ ν W L X₁ X₂ : ℝ} {K : ℕ}
    (hL : L = Real.log W) (hW : Real.exp 500 ≤ W) (hν : 1 ≤ ν)
    (hKW : (K : ℝ) ≤ W) (hνW : ν + 3 ≤ W) (hX₁ : W ^ 5 ≤ X₁)
    (hX₂ : Real.exp 20 ≤ X₂) {u : ℝ} (hu : u ∈ Ioc X₁ X₂) :
    L * ∑ d ∈ Finset.Icc 2 K, ∑ χ ∈ Census.badChars σ ν d,
        ∫ τ in Ioc (-(ν + 1)) (ν + 1), ‖primeWindowSum χ τ X₁ u‖ ^ 2
      ≤ 600 * Real.exp 1 ^ 2 * (Real.log X₂) ^ 2 := by
  classical
  have hW0 : 0 < W := lt_of_lt_of_le (Real.exp_pos _) hW
  have hW2 : 2 ≤ W := by
    have := Real.add_one_le_exp (500 : ℝ)
    linarith
  have hW1 : 1 ≤ W := by linarith
  have hL500 : 500 ≤ L := by
    rw [hL]
    have := Real.log_le_log (Real.exp_pos 500) hW
    rwa [Real.log_exp] at this
  have hL0 : 0 < L := by linarith
  have hT : 1 ≤ ν + 1 := by linarith
  have hQ : 2 ≤ W ^ 2 := by nlinarith
  have hW5 : 0 < W ^ 5 := by positivity
  have hX₁pos : 0 < X₁ := lt_of_lt_of_le hW5 hX₁
  have hu0 : 0 < u := lt_trans hX₁pos hu.1
  -- the sieve data
  set s : Finset ℕ :=
    (Finset.Icc 1 ⌊u⌋₊).filter (fun p : ℕ => p.Prime ∧ X₁ < (p : ℝ)) with hs
  set a : ℕ → ℂ := fun n => ((Real.log n / n : ℝ) : ℂ) with ha
  have hsmem : ∀ p ∈ s, p.Prime ∧ X₁ < (p : ℝ) ∧ (p : ℝ) ≤ u := by
    intro p hp
    rw [hs, Finset.mem_filter, Finset.mem_Icc] at hp
    refine ⟨hp.2.1, hp.2.2, ?_⟩
    have h1 : (p : ℝ) ≤ ⌊u⌋₊ := by exact_mod_cast hp.1.2
    exact le_trans h1 (Nat.floor_le hu0.le)
  have hsift : ∀ n ∈ s, W ^ 2 < (n.minFac : ℝ) := by
    intro n hn
    obtain ⟨hp, hX, -⟩ := hsmem n hn
    rw [hp.minFac_eq]
    have : W ^ 2 ≤ W ^ 5 := pow_le_pow_right₀ hW1 (by norm_num)
    linarith
  have hsieve := LargeSieve.presifted_large_sieve hQ hT s a hsift
  -- the integrand identity
  have hid : ∀ (f : ℕ) (ψ : DirichletCharacter ℂ f) (t : ℝ),
      ‖∑ n ∈ s, a n * ψ n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2
        = ‖primeWindowSum ψ t X₁ u‖ ^ 2 := by
    intro f ψ t
    have hsum_eq : ∑ n ∈ s, a n * ψ n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)
        = primeWindowSum ψ t X₁ u := by
      unfold primeWindowSum
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨hprime, -, -⟩ := hsmem p hp
      have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hprime.ne_zero
      rw [show (-(1 : ℂ) - (t : ℂ) * Complex.I) = (-1) + (-(t : ℂ) * Complex.I) by ring,
        Complex.cpow_add _ _ hp0, Complex.cpow_neg_one]
      simp only [ha]
      push_cast
      ring
    rw [hsum_eq]
  -- the sieve LHS dominates the family sum with the uniform weight `L`
  have hlhs : L * ∑ d ∈ Finset.Icc 2 K, ∑ χ ∈ Census.badChars σ ν d,
        ∫ τ in Ioc (-(ν + 1)) (ν + 1), ‖primeWindowSum χ τ X₁ u‖ ^ 2
      ≤ ∑ f ∈ Finset.Icc 1 ⌊W ^ 2⌋₊, Real.log (W ^ 2 / f) *
          ∑ ψ ∈ LargeSieve.primChars f, ∫ t in (-(ν + 1))..(ν + 1),
            ‖∑ n ∈ s, a n * ψ n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2 := by
    rw [Finset.mul_sum]
    have hnn : ∀ f ∈ Finset.Icc 1 ⌊W ^ 2⌋₊, 0 ≤ Real.log (W ^ 2 / f) *
        ∑ ψ ∈ LargeSieve.primChars f, ∫ t in (-(ν + 1))..(ν + 1),
          ‖∑ n ∈ s, a n * ψ n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2 := by
      intro f hf
      apply mul_nonneg
      · apply Real.log_nonneg
        rw [Finset.mem_Icc] at hf
        have hf1 : (1:ℝ) ≤ f := by exact_mod_cast hf.1
        have hfQ : (f : ℝ) ≤ W ^ 2 :=
          le_trans (by exact_mod_cast hf.2) (Nat.floor_le (by positivity))
        rw [le_div_iff₀ (by linarith)]
        linarith
      · apply Finset.sum_nonneg
        intro ψ _
        apply intervalIntegral.integral_nonneg (by linarith)
        intro t _
        positivity
    have hsub : Finset.Icc 2 K ⊆ Finset.Icc 1 ⌊W ^ 2⌋₊ := by
      intro f hf
      rw [Finset.mem_Icc] at hf ⊢
      refine ⟨by omega, ?_⟩
      have h1 : (f : ℝ) ≤ W := le_trans (by exact_mod_cast hf.2) hKW
      have h2 : (f : ℝ) ≤ W ^ 2 := by nlinarith
      exact Nat.le_floor h2
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun f hf _ => hnn f hf))
    refine Finset.sum_le_sum fun f hf => ?_
    rw [Finset.mem_Icc] at hf
    have : NeZero f := ⟨by omega⟩
    have hf0 : (0 : ℝ) < f := by exact_mod_cast (by omega : 0 < f)
    have hwt : L ≤ Real.log (W ^ 2 / f) := by
      rw [hL]
      apply Real.log_le_log hW0
      rw [le_div_iff₀ hf0]
      have hfW : (f : ℝ) ≤ W := le_trans (by exact_mod_cast hf.2) hKW
      nlinarith
    have hlog0 : 0 ≤ Real.log (W ^ 2 / f) := le_trans hL0.le hwt
    have hinner : ∑ χ ∈ Census.badChars σ ν f,
          ∫ τ in Ioc (-(ν + 1)) (ν + 1), ‖primeWindowSum χ τ X₁ u‖ ^ 2
        ≤ ∑ ψ ∈ LargeSieve.primChars f, ∫ t in (-(ν + 1))..(ν + 1),
            ‖∑ n ∈ s, a n * ψ n * (n : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ^ 2 := by
      have hsub' : Census.badChars σ ν f ⊆ LargeSieve.primChars f := by
        intro ψ hψ
        exact LargeSieve.mem_primChars.mpr (Census.mem_badChars.mp hψ).1
      refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub' ?_)
      · refine Finset.sum_congr rfl fun ψ _ => ?_
        rw [intervalIntegral.integral_of_le (by linarith)]
        simp only [hid]
      · intro ψ _ _
        apply intervalIntegral.integral_nonneg (by linarith)
        intro t _
        positivity
    have hinner0 : 0 ≤ ∑ χ ∈ Census.badChars σ ν f,
        ∫ τ in Ioc (-(ν + 1)) (ν + 1), ‖primeWindowSum χ τ X₁ u‖ ^ 2 := by
      apply Finset.sum_nonneg
      intro χ _
      apply setIntegral_nonneg measurableSet_Ioc
      intro t _
      positivity
    calc L * ∑ χ ∈ Census.badChars σ ν f,
          ∫ τ in Ioc (-(ν + 1)) (ν + 1), ‖primeWindowSum χ τ X₁ u‖ ^ 2
        ≤ Real.log (W ^ 2 / f) * ∑ χ ∈ Census.badChars σ ν f,
          ∫ τ in Ioc (-(ν + 1)) (ν + 1), ‖primeWindowSum χ τ X₁ u‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hwt hinner0
      _ ≤ _ := mul_le_mul_of_nonneg_left hinner hlog0
  -- the sieve RHS
  have hrhs : 100 * ∑ n ∈ s, ((n : ℝ) + (W ^ 2) ^ 2 * (ν + 1)) * ‖a n‖ ^ 2
      ≤ 600 * Real.exp 1 ^ 2 * (Real.log X₂) ^ 2 := by
    have h1 : ∀ n ∈ s, ((n : ℝ) + (W ^ 2) ^ 2 * (ν + 1)) * ‖a n‖ ^ 2
        ≤ 2 * ((Real.log n) ^ 2 / n) := by
      intro n hn
      obtain ⟨hp, hX, -⟩ := hsmem n hn
      have hn0 : (0:ℝ) < n := by exact_mod_cast hp.pos
      have hnorm : ‖a n‖ ^ 2 = (Real.log n / n) ^ 2 := by
        simp only [ha]
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      have hQT : (W ^ 2) ^ 2 * (ν + 1) ≤ (n : ℝ) := by
        have h5 : (W ^ 2) ^ 2 * (ν + 1) ≤ W ^ 5 := by
          have e1 : (W ^ 2) ^ 2 * (ν + 1) = W ^ 4 * (ν + 1) := by ring
          have e2 : W ^ 5 = W ^ 4 * W := by ring
          rw [e1, e2]
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
      rw [hnorm]
      calc ((n : ℝ) + (W ^ 2) ^ 2 * (ν + 1)) * (Real.log n / n) ^ 2
          ≤ ((n : ℝ) + n) * (Real.log n / n) ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = 2 * ((Real.log n) ^ 2 / n) := by
            field_simp
            ring
    have h2 : ∑ n ∈ s, (Real.log n) ^ 2 / (n : ℝ) ≤ 3 * Real.exp 1 ^ 2 * (Real.log X₂) ^ 2 :=
      sum_log_sq_div_le hX₂ s (fun p hp => ⟨(hsmem p hp).1, le_trans (hsmem p hp).2.2 hu.2⟩)
    calc 100 * ∑ n ∈ s, ((n : ℝ) + (W ^ 2) ^ 2 * (ν + 1)) * ‖a n‖ ^ 2
        ≤ 100 * ∑ n ∈ s, 2 * ((Real.log n) ^ 2 / n) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum h1) (by norm_num)
      _ = 200 * ∑ n ∈ s, (Real.log n) ^ 2 / (n : ℝ) := by
          rw [← Finset.mul_sum]
          ring
      _ ≤ 200 * (3 * Real.exp 1 ^ 2 * (Real.log X₂) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = 600 * Real.exp 1 ^ 2 * (Real.log X₂) ^ 2 := by ring
  linarith [hlhs, hsieve, hrhs]

/-! ### §7 The family bound -/

/-- **The family bound** (§5.2 steps 2–3 summed over the family): with `R` the
number of bad `(d, χ)`, `d ∈ [2, K]`,
`2r·R·L ≤ 600e²·(η³·M·e^{6M})·(log X₂)²·(log X₂ − log X₁)`. -/
lemma family_bound {σ ν W L η r : ℝ} {K : ℕ}
    (hL : L = Real.log W) (hW : Real.exp 500 ≤ W) (hν : 1 ≤ ν)
    (hKW : (K : ℝ) ≤ W) (hνW : ν + 3 ≤ W)
    (hη0 : 0 < η) (hηup : η ≤ 1/5000) (hηlow : 1 ≤ 12 * η * L)
    (hr0 : 0 < r) (hr1 : r ≤ 1) (hσ1 : σ ≤ 1) (hdist : (1 - σ) ^ 2 + r ^ 2 ≤ η ^ 2)
    (hX₁ : W ^ 5 ≤ Xone η L) :
    2 * r * (∑ d ∈ Finset.Icc 2 K, (Census.badChars σ ν d).card : ℝ) * L
      ≤ 600 * Real.exp 1 ^ 2 * (η ^ 3 * (Mdet η L : ℝ) * Real.exp (6 * (Mdet η L : ℝ)))
          * (Real.log (Xtwo η L)) ^ 2 * (Real.log (Xtwo η L) - Real.log (Xone η L)) := by
  classical
  have hL500 : 500 ≤ L := by
    rw [hL]
    have := Real.log_le_log (Real.exp_pos 500) hW
    rwa [Real.log_exp] at this
  have hL0 : 0 < L := by linarith
  -- opaque abbreviations
  obtain ⟨X₁, hX₁d⟩ : ∃ X₁ : ℝ, X₁ = Xone η L := ⟨_, rfl⟩
  obtain ⟨X₂, hX₂d⟩ : ∃ X₂ : ℝ, X₂ = Xtwo η L := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = η ^ 3 * (Mdet η L : ℝ) * Real.exp (6 * (Mdet η L : ℝ)) :=
    ⟨_, rfl⟩
  rw [← hX₁d, ← hX₂d, ← hc]
  rw [← hX₁d] at hX₁
  have hX₁pos : 0 < X₁ := by rw [hX₁d]; exact Xone_pos _ _
  have hX₁X₂ : X₁ < X₂ := by rw [hX₁d, hX₂d]; exact Xone_lt_Xtwo hη0 hL0.le
  have hX₂20 : Real.exp 20 ≤ X₂ := by rw [hX₂d]; exact exp_twenty_le_Xtwo hη0 hηup hL0.le
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 600 * Real.exp 1 ^ 2 * (Real.log X₂) ^ 2 := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  -- per-character window bounds
  have hper : ∀ d ∈ Finset.Icc 2 K, ∀ χ ∈ Census.badChars σ ν d,
      2 * r ≤ c * ∫ u in Ioc X₁ X₂, ∫ τ in Ioc (-(ν + 1)) (ν + 1),
        ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u := by
    intro d hd χ hχ
    rw [Finset.mem_Icc] at hd
    have : NeZero d := ⟨by omega⟩
    have hdW : (d : ℝ) ≤ W := le_trans (by exact_mod_cast hd.2) hKW
    have := perchar_window hχ hd.1 hL hW hdW hνW hη0 hηup hηlow hr0 hr1 hσ1 hdist
    rw [← hX₁d, ← hX₂d, ← hc] at this
    exact this
  -- integrability of each `u ↦ ∫_τ`
  have hGint : ∀ d ∈ Finset.Icc 2 K, ∀ χ ∈ Census.badChars σ ν d,
      IntegrableOn (fun u => ∫ τ in Ioc (-(ν + 1)) (ν + 1),
        ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u) (Ioc X₁ X₂) := by
    intro d _ χ _
    exact (integrable_normSq_div χ (T := ν + 1) hX₁pos hX₂20).integral_prod_right
  -- sum of the per-character bounds
  have hsum : 2 * r * (∑ d ∈ Finset.Icc 2 K, (Census.badChars σ ν d).card : ℝ)
      ≤ c * ∑ d ∈ Finset.Icc 2 K, ∑ χ ∈ Census.badChars σ ν d,
          ∫ u in Ioc X₁ X₂, ∫ τ in Ioc (-(ν + 1)) (ν + 1),
            ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d hd
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro χ hχ
    simpa using hper d hd χ hχ
  -- swap the finite sums with the `u`-integral
  have hswap : ∑ d ∈ Finset.Icc 2 K, ∑ χ ∈ Census.badChars σ ν d,
        ∫ u in Ioc X₁ X₂, ∫ τ in Ioc (-(ν + 1)) (ν + 1),
          ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u
      = ∫ u in Ioc X₁ X₂, ∑ d ∈ Finset.Icc 2 K, ∑ χ ∈ Census.badChars σ ν d,
          ∫ τ in Ioc (-(ν + 1)) (ν + 1), ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u := by
    rw [integral_finsetSum _ (fun d hd => integrable_finsetSum _ (fun χ hχ => hGint d hd χ hχ))]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [integral_finsetSum _ (fun χ hχ => hGint d hd χ hχ)]
  -- the pointwise bound in `u`
  have hpt : ∀ u ∈ Ioc X₁ X₂,
      ∑ d ∈ Finset.Icc 2 K, ∑ χ ∈ Census.badChars σ ν d,
          ∫ τ in Ioc (-(ν + 1)) (ν + 1), ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u
        ≤ B / L * (1 / u) := by
    intro u hu
    have hu0 : 0 < u := lt_trans hX₁pos hu.1
    have h1 : ∑ d ∈ Finset.Icc 2 K, ∑ χ ∈ Census.badChars σ ν d,
          ∫ τ in Ioc (-(ν + 1)) (ν + 1), ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u
        = (∑ d ∈ Finset.Icc 2 K, ∑ χ ∈ Census.badChars σ ν d,
          ∫ τ in Ioc (-(ν + 1)) (ν + 1), ‖primeWindowSum χ τ X₁ u‖ ^ 2) / u := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun χ _ => ?_
      exact integral_div u _
    rw [h1]
    have h2 := sieve_at_u (σ := σ) (K := K) hL hW hν hKW hνW hX₁ hX₂20 hu
    rw [← hB] at h2
    rw [div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    rw [le_div_iff₀ hL0]
    linarith
  -- integrate the pointwise bound
  have hint2 : ∫ u in Ioc X₁ X₂, ∑ d ∈ Finset.Icc 2 K, ∑ χ ∈ Census.badChars σ ν d,
        ∫ τ in Ioc (-(ν + 1)) (ν + 1), ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u
      ≤ ∫ u in Ioc X₁ X₂, B / L * (1 / u) := by
    refine setIntegral_mono_on
      (integrable_finsetSum _ (fun d hd => integrable_finsetSum _ (fun χ hχ => hGint d hd χ hχ)))
      ?_ measurableSet_Ioc hpt
    have h0 : ∀ x ∈ Set.uIcc X₁ X₂, x ≠ 0 := by
      intro x hx
      rw [Set.uIcc_of_le hX₁X₂.le] at hx
      exact (lt_of_lt_of_le hX₁pos hx.1).ne'
    have hii : IntervalIntegrable (fun x : ℝ => B / L * (1 / x)) volume X₁ X₂ :=
      (intervalIntegral.intervalIntegrable_one_div h0 continuousOn_id).const_mul _
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hX₁X₂.le).mp hii
  have hval : ∫ u in Ioc X₁ X₂, B / L * (1 / u) = B / L * (Real.log X₂ - Real.log X₁) := by
    rw [← intervalIntegral.integral_of_le hX₁X₂.le, intervalIntegral.integral_const_mul]
    have h0 : (0 : ℝ) ∉ Set.uIcc X₁ X₂ := by
      rw [Set.uIcc_of_le hX₁X₂.le]
      intro h
      linarith [h.1]
    rw [integral_one_div h0, Real.log_div (by linarith) hX₁pos.ne']
  -- collect
  have hfin : 2 * r * (∑ d ∈ Finset.Icc 2 K, (Census.badChars σ ν d).card : ℝ)
      ≤ c * (B / L * (Real.log X₂ - Real.log X₁)) := by
    calc 2 * r * (∑ d ∈ Finset.Icc 2 K, (Census.badChars σ ν d).card : ℝ)
        ≤ _ := hsum
      _ = c * ∫ u in Ioc X₁ X₂, ∑ d ∈ Finset.Icc 2 K, ∑ χ ∈ Census.badChars σ ν d,
          ∫ τ in Ioc (-(ν + 1)) (ν + 1), ‖primeWindowSum χ τ X₁ u‖ ^ 2 / u := by
          rw [hswap]
      _ ≤ c * ∫ u in Ioc X₁ X₂, B / L * (1 / u) := mul_le_mul_of_nonneg_left hint2 hc0
      _ = c * (B / L * (Real.log X₂ - Real.log X₁)) := by rw [hval]
  have hL' : L ≠ 0 := hL0.ne'
  calc 2 * r * (∑ d ∈ Finset.Icc 2 K, (Census.badChars σ ν d).card : ℝ) * L
      ≤ c * (B / L * (Real.log X₂ - Real.log X₁)) * L :=
        mul_le_mul_of_nonneg_right hfin hL0.le
    _ = 600 * Real.exp 1 ^ 2 * c * (Real.log X₂) ^ 2 * (Real.log X₂ - Real.log X₁) := by
        rw [hB]
        field_simp

/-! ### §8 The machine bound -/

set_option maxHeartbeats 1000000 in
set_option linter.unusedVariables false in
/-- **The machine bound** (keystone): in the middle window the census is
at most `exp(1.2·10⁸ + 1.2·10⁹·(1−σ)·log(Z(ν+2)))`. -/
theorem censusCount_le_machine {σ ν Z : ℝ}
    (hσ : 39/40 ≤ σ) (hσ1 : σ ≤ 1) (hν : 1 ≤ ν) (hZ : 2 ≤ Z)
    (hwin : 1 - σ < 2/Census.censusC₃)
    (hfloor : 1/1000000000 < (1 - σ) * Real.log (Z * (ν + 2))) :
    (Census.censusCount σ ν ⌊Z⌋₊ : ℝ)
      ≤ Real.exp (120000000 + 1200000000 * (1 - σ) * Real.log (Z * (ν + 2))) := by
  classical
  -- the window facts
  have hwin' : 1 - σ < 2 / 1000000000000 := by
    have h := hwin
    rw [Census.censusC₃] at h
    norm_num at h ⊢
    linarith
  obtain ⟨W, hWd⟩ : ∃ W : ℝ, W = Z * (ν + 2) := ⟨_, rfl⟩
  obtain ⟨L, hLd⟩ : ∃ L : ℝ, L = Real.log W := ⟨_, rfl⟩
  rw [← hWd, ← hLd] at hfloor ⊢
  have hσ0 : 0 ≤ 1 - σ := by linarith
  have hL500 : 500 < L := by
    by_contra h
    push Not at h
    have h1 : (1 - σ) * L ≤ (1 - σ) * 500 := mul_le_mul_of_nonneg_left h hσ0
    have h2 : (1 - σ) * 500 < 2 / 1000000000000 * 500 :=
      mul_lt_mul_of_pos_right hwin' (by norm_num)
    norm_num at h2
    linarith
  have hL0 : 0 < L := by linarith
  have hν2 : 0 < ν + 2 := by linarith
  have hW0 : 0 < W := by rw [hWd]; positivity
  have hW : Real.exp 500 ≤ W := by
    rw [← Real.exp_log hW0, ← hLd]
    exact Real.exp_le_exp.mpr hL500.le
  have hνW : ν + 3 ≤ W := by rw [hWd]; nlinarith
  have hKW : (⌊Z⌋₊ : ℝ) ≤ W := by
    have h1 : (⌊Z⌋₊ : ℝ) ≤ Z := Nat.floor_le (by linarith)
    rw [hWd]
    nlinarith
  -- the clamp `η₀ = max(1−σ, 1/(12L))`, `η = 1.01·η₀`
  obtain ⟨η₀, hη₀⟩ : ∃ η₀ : ℝ, η₀ = max (1 - σ) (1 / (12 * L)) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = 101 / 100 * η₀ := ⟨_, rfl⟩
  have hη₀pos : 0 < η₀ := by
    rw [hη₀]
    exact lt_max_of_lt_right (by positivity)
  have hη₀le : η₀ ≤ 1 / 6000 := by
    rw [hη₀]
    apply max_le
    · linarith
    · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
  have hη0 : 0 < η := by rw [hη]; positivity
  have hηup : η ≤ 1/5000 := by rw [hη]; linarith
  have hηlow : 1 ≤ 12 * η * L := by
    have h1 : 1 / (12 * L) ≤ η₀ := by rw [hη₀]; exact le_max_right _ _
    have h2 : 1 / (12 * L) * (12 * L) = 1 := by field_simp
    have h3 : 1 / (12 * L) * (12 * L) ≤ η₀ * (12 * L) :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    rw [hη]
    nlinarith
  -- the window half-width `r = 0.14·η₀`
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 7 / 50 * η₀ := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; linarith
  have hdist : (1 - σ) ^ 2 + r ^ 2 ≤ η ^ 2 := by
    have h1 : 1 - σ ≤ η₀ := by rw [hη₀]; exact le_max_left _ _
    rw [hr, hη]
    nlinarith
  -- `W⁵ ≤ X₁`
  have hX₁ : W ^ 5 ≤ Xone η L := by
    have hW5 : W ^ 5 = Real.exp (5 * L) := by
      rw [hLd, show (5:ℝ) * Real.log W = ((5:ℕ):ℝ) * Real.log W by norm_num,
        Real.exp_nat_mul, Real.exp_log hW0]
    rw [hW5, Xone]
    apply Real.exp_le_exp.mpr
    rw [le_div_iff₀ (by positivity)]
    have hN := le_Ndet_cast η L
    have hMdet : (Mdet η L : ℝ) = 6 * (Ndet η L : ℝ) := by rw [Mdet_eq]; push_cast; ring
    rw [hMdet]
    nlinarith
  -- the family bound
  have hfam := family_bound (σ := σ) (K := ⌊Z⌋₊) hLd hW hν hKW hνW hη0 hηup hηlow
    hr0 hr1 hσ1 hdist hX₁
  -- fold the window dials
  have hlogX₂ : Real.log (Xtwo η L) = 16 * (Mdet η L : ℝ) / η := by rw [Xtwo, Real.log_exp]
  have hlogX₁ : Real.log (Xone η L) = (Mdet η L : ℝ) / (16 * η) := by rw [Xone, Real.log_exp]
  rw [hlogX₂, hlogX₁] at hfam
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (Mdet η L : ℝ) := ⟨_, rfl⟩
  rw [← hM] at hfam
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℕ, R = ∑ d ∈ Finset.Icc 2 ⌊Z⌋₊, (Census.badChars σ ν d).card :=
    ⟨_, rfl⟩
  have hRcast : (R : ℝ) = ∑ d ∈ Finset.Icc 2 ⌊Z⌋₊, ((Census.badChars σ ν d).card : ℝ) := by
    rw [hR]
    push_cast
    rfl
  rw [← hRcast] at hfam
  have hfam' : 2 * (7 / 50 * η₀) * (R : ℝ) * L
      ≤ 2457600 * Real.exp 1 ^ 2 * M ^ 4 * Real.exp (6 * M) := by
    rw [hr] at hfam
    have h1 : 16 * M / η - M / (16 * η) ≤ 16 * M / η := by
      have : 0 ≤ M / (16 * η) := by positivity
      linarith
    have h2 : 600 * Real.exp 1 ^ 2 * (η ^ 3 * M * Real.exp (6 * M)) * (16 * M / η) ^ 2
          * (16 * M / η - M / (16 * η))
        ≤ 600 * Real.exp 1 ^ 2 * (η ^ 3 * M * Real.exp (6 * M)) * (16 * M / η) ^ 2
          * (16 * M / η) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 600 * Real.exp 1 ^ 2 * (η ^ 3 * M * Real.exp (6 * M)) * (16 * M / η) ^ 2
          * (16 * M / η)
        = 2457600 * Real.exp 1 ^ 2 * M ^ 4 * Real.exp (6 * M) := by
      field_simp
      ring
    linarith
  rw [hM] at hfam'
  have hRexp := budget_close (R := R) hσ1 hL500 hη₀ hη hfam'
  -- decompose the census: `d = 1` plus the tail
  have hK2 : 2 ≤ ⌊Z⌋₊ := Nat.le_floor (by exact_mod_cast hZ : ((2:ℕ):ℝ) ≤ Z)
  have hIcc : Finset.Icc 1 ⌊Z⌋₊ = insert 1 (Finset.Icc 2 ⌊Z⌋₊) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h1notin : (1:ℕ) ∉ Finset.Icc 2 ⌊Z⌋₊ := by
    simp only [Finset.mem_Icc]
    omega
  have hdecomp : Census.censusCount σ ν ⌊Z⌋₊ = (Census.badChars σ ν 1).card + R := by
    rw [Census.censusCount, hIcc, Finset.sum_insert h1notin, hR]
  have hone := card_badChars_one σ ν
  have hcount : (Census.censusCount σ ν ⌊Z⌋₊ : ℝ) ≤ 1 + R := by
    rw [hdecomp]
    push_cast
    have : ((Census.badChars σ ν 1).card : ℝ) ≤ 1 := by exact_mod_cast hone
    linarith
  -- the final exponential
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 118000000 + 1190000000 * (1 - σ) * L := ⟨_, rfl⟩
  rw [← hA] at hRexp
  have hP0 : 0 ≤ (1 - σ) * L := mul_nonneg hσ0 hL0.le
  have hA0 : 0 ≤ A := by rw [hA]; nlinarith
  have hexpA1 : 1 ≤ Real.exp A := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr hA0
  have hfinal : (1:ℝ) + Real.exp A ≤ Real.exp (A + 1) := by
    rw [Real.exp_add]
    have he : 2 ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    nlinarith
  calc (Census.censusCount σ ν ⌊Z⌋₊ : ℝ) ≤ 1 + R := hcount
    _ ≤ 1 + Real.exp A := by linarith
    _ ≤ Real.exp (A + 1) := hfinal
    _ ≤ Real.exp (120000000 + 1200000000 * (1 - σ) * L) := by
        apply Real.exp_le_exp.mpr
        rw [hA]
        nlinarith

/-! ### §9 Absorption: the Z7 discharge -/

/-- `exp(1.2·10⁸) ≤ 10^(10⁹)`, by monotonicity only (§0.5: the tower is never
evaluated). -/
lemma exp_le_tower : Real.exp 120000000 ≤ (10 : ℝ) ^ (1000000000 : ℕ) := by
  have h1 : Real.exp (120000000 : ℝ) ≤ Real.exp ((1000000000 : ℕ) : ℝ) := by
    apply Real.exp_le_exp.mpr
    norm_num
  have h2 : Real.exp ((1000000000 : ℕ) : ℝ) = Real.exp 1 ^ (1000000000 : ℕ) :=
    (Real.exp_one_pow _).symm
  have h3 : Real.exp 1 ^ (1000000000 : ℕ) ≤ (10 : ℝ) ^ (1000000000 : ℕ) := by
    apply pow_le_pow_left₀ (Real.exp_pos 1).le
    have := Real.exp_one_lt_d9
    linarith
  calc Real.exp 120000000 ≤ Real.exp ((1000000000 : ℕ) : ℝ) := h1
    _ = _ := h2
    _ ≤ _ := h3

/-- **Z7 DISCHARGE**: the middle-regime census hypothesis holds. -/
theorem midCensusHyp : Census.MidCensusHyp := by
  unfold Census.MidCensusHyp
  intro σ ν Z hσ hσ1 hν hZ hwin hfloor
  have hmach := censusCount_le_machine hσ hσ1 hν hZ hwin hfloor
  -- abstract the tower to an opaque real, then forget its definition
  have htower := exp_le_tower
  obtain ⟨Tw, hTw⟩ : ∃ Tw : ℝ, Tw = (10 : ℝ) ^ (1000000000 : ℕ) := ⟨_, rfl⟩
  rw [Census.censusC₂, ← hTw]
  rw [← hTw] at htower
  clear hTw
  -- the three budget rows
  have hwin' : 1 - σ < 2 / 1000000000000 := by
    have h := hwin
    rw [Census.censusC₃] at h
    norm_num at h ⊢
    linarith
  have hZ0 : 0 < Z := by linarith
  have hν2 : 0 < ν + 2 := by linarith
  have hσ0 : 0 ≤ 1 - σ := by linarith
  have hsplit : Real.exp (120000000 + 1200000000 * (1 - σ) * Real.log (Z * (ν + 2)))
      = Real.exp 120000000
        * (Z ^ (1200000000 * (1 - σ)) * (ν + 2) ^ (1200000000 * (1 - σ))) := by
    rw [Real.log_mul hZ0.ne' hν2.ne', Real.rpow_def_of_pos hZ0, Real.rpow_def_of_pos hν2,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hZpow : Z ^ (1200000000 * (1 - σ)) ≤ Z ^ (Census.censusC₃ * (1 - σ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    rw [Census.censusC₃]
    have : (1200000000 : ℝ) ≤ 10 ^ 12 := by norm_num
    exact mul_le_mul_of_nonneg_right this hσ0
  have hνpow : (ν + 2) ^ (1200000000 * (1 - σ)) ≤ ν + 2 := by
    have h1 : 1200000000 * (1 - σ) ≤ 1 := by linarith
    calc (ν + 2) ^ (1200000000 * (1 - σ)) ≤ (ν + 2) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) h1
      _ = ν + 2 := Real.rpow_one _
  have hZpow0 : 0 ≤ Z ^ (1200000000 * (1 - σ)) := Real.rpow_nonneg hZ0.le _
  have hνpow0 : 0 ≤ (ν + 2) ^ (1200000000 * (1 - σ)) := Real.rpow_nonneg hν2.le _
  have hZpow0' : 0 ≤ Z ^ (Census.censusC₃ * (1 - σ)) := Real.rpow_nonneg hZ0.le _
  have hTw0 : 0 ≤ Tw := le_trans (Real.exp_pos _).le htower
  calc (Census.censusCount σ ν ⌊Z⌋₊ : ℝ)
      ≤ Real.exp (120000000 + 1200000000 * (1 - σ) * Real.log (Z * (ν + 2))) := hmach
    _ = Real.exp 120000000
        * (Z ^ (1200000000 * (1 - σ)) * (ν + 2) ^ (1200000000 * (1 - σ))) := hsplit
    _ ≤ Tw * (Z ^ (Census.censusC₃ * (1 - σ)) * (ν + 2)) := by
        apply mul_le_mul htower _ (mul_nonneg hZpow0 hνpow0) hTw0
        exact mul_le_mul hZpow hνpow hνpow0 hZpow0'
    _ = Tw * (ν + 2) * Z ^ (Census.censusC₃ * (1 - σ)) := by ring

end Carmichael.CensusMid
