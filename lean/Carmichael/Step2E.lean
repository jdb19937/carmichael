/-
Lemma 4.1 of the paper (Step 2 succeeds), generic in the AGP smoothness
parameter `E`. Proved from the AGP smooth-shifted hypothesis `hsmooth`
(AGP Theorem 3 at parameter `E`) and `chebyshev_lower`.
-/
import Carmichael.Defs
import Carmichael.PrimeCount

namespace Carmichael

open Filter Finset

/-! ### Elementary real inequalities -/

/-- `log x ≤ 2√x` for `0 ≤ x`. -/
private lemma log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]
    simp
  · have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr h
    have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
      conv_lhs => rw [← Real.sq_sqrt hx]
      rw [Real.log_pow]
      norm_num
    have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
      Real.log_le_sub_one_of_pos hs
    linarith

/-! ### Growth of the scales -/

private lemma tendsto_ell2 : Tendsto ell2 atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma tendsto_ell3 : Tendsto ell3 atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_ell2

private lemma tendsto_zreal (C₁ : ℝ) (h1000 : (1000 : ℝ) ≤ C₁) :
    Tendsto (fun n : ℕ => C₁ * ell2 n * ell3 n) atTop atTop := by
  apply tendsto_atTop_mono' atTop ?_ tendsto_ell3
  filter_upwards [tendsto_ell2.eventually_ge_atTop 1,
    tendsto_ell3.eventually_ge_atTop 0] with n h2 h3
  have hC : (0 : ℝ) < C₁ := lt_of_lt_of_le (by norm_num) h1000
  have hCℓ₂ : C₁ * 1 ≤ C₁ * ell2 n := mul_le_mul_of_nonneg_left h2 hC.le
  have h1 : (1 : ℝ) ≤ C₁ * ell2 n := by linarith
  have := mul_le_mul_of_nonneg_right h1 h3
  linarith

private lemma zscale_eventually_ge (C₁ : ℝ) (h1000 : (1000 : ℝ) ≤ C₁) (m : ℕ) :
    ∀ᶠ n : ℕ in atTop, m ≤ zscale C₁ n := by
  filter_upwards [(tendsto_zreal C₁ h1000).eventually_ge_atTop (m : ℝ)] with n h
  have h2 : (m : ℝ) ≤ (zscale C₁ n : ℝ) := h.trans (Nat.le_ceil _)
  exact_mod_cast h2

/-! ### The main lemma -/

open Classical in
/-- Lemma 4.1 (Step 2 succeeds), generic in `E`: for `n` large, the reservoir
of primes `q ∈ (z^{99/100}, z]` with `q - 1` smooth up to `yscaleE C₁ n E`
has at least `T` elements. -/
theorem step2_succeedsE (C₁ γ E : ℝ) (x₁ : ℕ)
    (hE : 0 < E) (hE2 : E ≤ 1 / 2) (hγ : 0 < γ)
    (h48 : 48 ≤ C₁ * γ) (h1000 : (1000 : ℝ) ≤ C₁)
    (hsmooth : ∀ x : ℕ, x₁ ≤ x →
      γ * (primePi x : ℝ) ≤
        (((Finset.range (x + 1)).filter (fun p => p.Prime ∧
          ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) - E))).card : ℝ)) :
    ∀ᶠ n : ℕ in Filter.atTop, Tscale n ≤ (goodPrimesE C₁ n E).card := by
  have hC₁ : (0 : ℝ) < C₁ := lt_of_lt_of_le (by norm_num) h1000
  have hγC₁' : (48 : ℝ) ≤ C₁ * γ := h48
  -- extract a concrete threshold from the proved Chebyshev bound
  obtain ⟨z₀', hz₀'⟩ := Filter.eventually_atTop.mp chebyshev_lower
  -- `2 C₁ log u ≤ u^{1/99}` for `u` large, pulled back along `u = ℓ₂(n)`
  have hlog_rpow : ∀ᶠ u : ℝ in atTop,
      2 * C₁ * Real.log u ≤ u ^ ((1 : ℝ) / 99) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 99)).def
      (by positivity : (0 : ℝ) < 1 / (2 * C₁))
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with u hu hu1
    have hu0 : (0 : ℝ) ≤ u := by linarith
    have hlog0 : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
    have hr0 : (0 : ℝ) ≤ u ^ ((1 : ℝ) / 99) := Real.rpow_nonneg hu0 _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg hr0] at hu
    have := mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 2 * C₁)
    calc 2 * C₁ * Real.log u
        ≤ 2 * C₁ * (1 / (2 * C₁) * u ^ ((1 : ℝ) / 99)) := this
      _ = u ^ ((1 : ℝ) / 99) := by field_simp
  filter_upwards [tendsto_ell2.eventually_ge_atTop 1,
    tendsto_ell2.eventually hlog_rpow,
    tendsto_ell3.eventually_ge_atTop 1,
    tendsto_ell3.eventually_ge_atTop (8 * C₁),
    zscale_eventually_ge C₁ h1000 x₁,
    zscale_eventually_ge C₁ h1000 z₀',
    zscale_eventually_ge C₁ h1000 2] with n h1 h2 h3 h4 hx₁ hz₀ hz2
  -- basic positivity facts
  have hℓ₂0 : (0 : ℝ) ≤ ell2 n := by linarith
  have hℓ₃0 : (0 : ℝ) ≤ ell3 n := by linarith
  have hC₁ℓ₂ : C₁ * 1 ≤ C₁ * ell2 n := mul_le_mul_of_nonneg_left h1 hC₁.le
  have hCℓ' : (1 : ℝ) ≤ C₁ * ell2 n := by linarith [h1000]
  have hCℓ : (1 : ℝ) ≤ C₁ * ell2 n * ell3 n := by
    have := mul_le_mul_of_nonneg_right hCℓ' hℓ₃0
    linarith
  have hzlb : C₁ * ell2 n * ell3 n ≤ (zscale C₁ n : ℝ) := Nat.le_ceil _
  have hzub : (zscale C₁ n : ℝ) ≤ C₁ * ell2 n * ell3 n + 1 :=
    (Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ C₁ * ell2 n * ell3 n)).le
  have hz1 : (1 : ℝ) < (zscale C₁ n : ℝ) := by
    have h2' : (2 : ℝ) ≤ (zscale C₁ n : ℝ) := by exact_mod_cast hz2
    linarith
  have hzpos : (0 : ℝ) < (zscale C₁ n : ℝ) := by linarith
  have hlogzpos : 0 < Real.log (zscale C₁ n : ℝ) := Real.log_pos hz1
  -- `log z ≤ 2 ℓ₃`
  have hlogz : Real.log (zscale C₁ n : ℝ) ≤ 2 * ell3 n := by
    have hstep : (zscale C₁ n : ℝ) ≤ ell2 n * (2 * C₁ * ell3 n) := by nlinarith
    have hpos2 : (0 : ℝ) < 2 * C₁ * ell3 n := by nlinarith
    have hlog1 : Real.log (zscale C₁ n : ℝ)
        ≤ Real.log (ell2 n * (2 * C₁ * ell3 n)) := Real.log_le_log hzpos hstep
    rw [Real.log_mul (by linarith) (ne_of_gt hpos2)] at hlog1
    have hlog2 : Real.log (ell2 n) = ell3 n := rfl
    have hlog3 : Real.log (2 * C₁ * ell3 n) ≤ 2 * Real.sqrt (2 * C₁ * ell3 n) :=
      log_le_two_sqrt hpos2.le
    have hsq : Real.sqrt (2 * C₁ * ell3 n) ≤ ell3 n / 2 := by
      have h' : 2 * C₁ * ell3 n ≤ (ell3 n / 2) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right h4 hℓ₃0]
      calc Real.sqrt (2 * C₁ * ell3 n) ≤ Real.sqrt ((ell3 n / 2) ^ 2) :=
            Real.sqrt_le_sqrt h'
        _ = ell3 n / 2 := Real.sqrt_sq (by linarith)
    linarith
  -- `z^{99/100} ≤ ℓ₂`
  have hrpz : (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) ≤ ell2 n := by
    have hℓ₂pos : (0 : ℝ) < ell2 n := by linarith
    have hll : 2 * C₁ * ell3 n ≤ ell2 n ^ ((1 : ℝ) / 99) := h2
    have hz2C : (zscale C₁ n : ℝ) ≤ 2 * (C₁ * ell2 n * ell3 n) := by linarith
    have hb0 : (0 : ℝ) ≤ 2 * (C₁ * ell2 n * ell3 n) := by
      have := mul_nonneg (mul_nonneg hC₁.le hℓ₂0) hℓ₃0
      linarith
    have step2 : 2 * (C₁ * ell2 n * ell3 n) ≤ ell2 n ^ ((100 : ℝ) / 99) := by
      have hshape : 2 * (C₁ * ell2 n * ell3 n) = ell2 n * (2 * C₁ * ell3 n) := by
        ring
      have h100 : ell2 n ^ ((100 : ℝ) / 99) = ell2 n * ell2 n ^ ((1 : ℝ) / 99) := by
        rw [show (100 : ℝ) / 99 = 1 + 1 / 99 by norm_num, Real.rpow_add hℓ₂pos,
          Real.rpow_one]
      rw [hshape, h100]
      exact mul_le_mul_of_nonneg_left hll (by linarith)
    have step4 : (ell2 n ^ ((100 : ℝ) / 99)) ^ ((99 : ℝ) / 100) = ell2 n := by
      rw [← Real.rpow_mul hℓ₂pos.le,
        show (100 : ℝ) / 99 * (99 / 100) = 1 by norm_num, Real.rpow_one]
    calc (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100)
        ≤ (2 * (C₁ * ell2 n * ell3 n)) ^ ((99 : ℝ) / 100) :=
          Real.rpow_le_rpow (by positivity) hz2C (by norm_num)
      _ ≤ (ell2 n ^ ((100 : ℝ) / 99)) ^ ((99 : ℝ) / 100) :=
          Real.rpow_le_rpow hb0 step2 (by norm_num)
      _ = ell2 n := step4
  -- `(C₁/2) ℓ₂ ≤ z / log z`
  have hzdiv : C₁ / 2 * ell2 n
      ≤ (zscale C₁ n : ℝ) / Real.log (zscale C₁ n : ℝ) := by
    rw [le_div_iff₀ hlogzpos]
    have e1 : C₁ / 2 * ell2 n * Real.log (zscale C₁ n : ℝ)
        ≤ C₁ / 2 * ell2 n * (2 * ell3 n) :=
      mul_le_mul_of_nonneg_left hlogz (mul_nonneg (by linarith) hℓ₂0)
    nlinarith
  -- `(C₁/6) ℓ₂ ≤ z / (3 log z)`
  have hzdiv3 : C₁ / 6 * ell2 n
      ≤ (zscale C₁ n : ℝ) / (3 * Real.log (zscale C₁ n : ℝ)) := by
    rw [mul_comm (3 : ℝ), ← div_div]
    linarith
  -- package the AGP smooth-shifted count so that no `Finset.filter`
  -- decidability instances need to be matched syntactically
  obtain ⟨S, hS1, hS2⟩ : ∃ S : Finset ℕ,
      γ * (primePi (zscale C₁ n) : ℝ) ≤ (S.card : ℝ) ∧
      ∀ p ∈ S, p < zscale C₁ n + 1 ∧ p.Prime ∧
        ∀ q : ℕ, q.Prime → q ∣ p - 1 →
          (q : ℝ) ≤ (zscale C₁ n : ℝ) ^ ((1 : ℝ) - E) := by
    refine ⟨_, hsmooth (zscale C₁ n) hx₁, ?_⟩
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact hp
  -- every prime counted by AGP is either good or at most `z^{99/100}`
  have hsub : S ⊆ goodPrimesE C₁ n E
      ∪ Finset.range (⌊(zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100)⌋₊ + 1) := by
    intro p hp
    obtain ⟨hpz, hpp, hps⟩ := hS2 p hp
    by_cases hbig : (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) < (p : ℝ)
    · apply Finset.mem_union_left
      simp only [goodPrimesE, Finset.mem_filter, Finset.mem_range]
      refine ⟨hpz, hpp, hbig, ?_⟩
      intro q hq hqd
      have hy : (q : ℝ) ≤ (yscaleE C₁ n E : ℝ) := (hps q hq hqd).trans (Nat.le_ceil _)
      exact_mod_cast hy
    · apply Finset.mem_union_right
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Nat.le_floor (not_lt.mp hbig)
  have hcard : S.card ≤ (goodPrimesE C₁ n E).card
      + (⌊(zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100)⌋₊ + 1) := by
    have hu := Finset.card_union_le (goodPrimesE C₁ n E)
      (Finset.range (⌊(zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100)⌋₊ + 1))
    rw [Finset.card_range] at hu
    exact (Finset.card_le_card hsub).trans hu
  -- combine: `γ π(z) ≤ |goodPrimesE| + z^{99/100} + 1`
  have hkey : γ * (primePi (zscale C₁ n) : ℝ)
      ≤ ((goodPrimesE C₁ n E).card : ℝ)
        + (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) + 1 := by
    have hcardR : (S.card : ℝ) ≤ ((goodPrimesE C₁ n E).card : ℝ)
        + (⌊(zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100)⌋₊ : ℝ) + 1 := by
      exact_mod_cast hcard
    have hfl : ((⌊(zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100)⌋₊ : ℕ) : ℝ)
        ≤ (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) :=
      Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    linarith
  -- Chebyshev: `γ π(z) ≥ γ (C₁/6) ℓ₂ ≥ 8 ℓ₂`
  have hcheb3 := hz₀' (zscale C₁ n) hz₀
  have hπ8 : (8 : ℝ) * ell2 n ≤ γ * (primePi (zscale C₁ n) : ℝ) := by
    have hg1 : γ * ((zscale C₁ n : ℝ) / (3 * Real.log (zscale C₁ n : ℝ)))
        ≤ γ * (primePi (zscale C₁ n) : ℝ) :=
      mul_le_mul_of_nonneg_left hcheb3 hγ.le
    have hg2 : γ * (C₁ / 6 * ell2 n)
        ≤ γ * ((zscale C₁ n : ℝ) / (3 * Real.log (zscale C₁ n : ℝ))) :=
      mul_le_mul_of_nonneg_left hzdiv3 hγ.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hγC₁') hℓ₂0]
  -- `T ≤ 3 ℓ₂ + 1`
  have hTle : (Tscale n : ℝ) ≤ 3 * ell2 n + 1 := by
    have h := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 3 * ell2 n)
    exact h.le
  -- conclude
  have hfin : (Tscale n : ℝ) ≤ ((goodPrimesE C₁ n E).card : ℝ) := by
    linarith
  exact_mod_cast hfin

end Carmichael
