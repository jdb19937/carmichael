/-
Lemma 4.1 of the paper (Step 2 succeeds) at windowed scales (Route T):
for `n` large and any scales `z w y T` in the window `InWindow C₁ E n z w y T`,
the reservoir `goodPrimesW z w y` (primes `q ∈ (w, z]` with `q - 1` smooth
up to `y`) has at least `T` elements. Proved from the AGP smooth-shifted
hypothesis `hsmooth` (AGP Theorem 3 at parameter `E`) and `chebyshev_lower`.

The constant `60 ≤ C₁ γ` (Step2E used 48) absorbs `T ≤ 5 ℓ₂` and the
reservoir floor `w ≤ 4 z^{99/100} ≤ 4 ℓ₂`: the count is
`γ π(z) ≥ (γ C₁ / 6) ℓ₂ ≥ 10 ℓ₂ ≥ 5 ℓ₂ + 4 ℓ₂ + 1 ≥ T + w + 1`.
-/
import Carmichael.DefsW
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

/-! ### The main lemma -/

open Classical in
/-- Lemma 4.1 (Step 2 succeeds) at windowed scales: for `n` large and any
`z w y T` in the window, the reservoir of primes `q ∈ (w, z]` with `q - 1`
smooth up to `y` has at least `T` elements. -/
theorem step2_succeedsW (C₁ γ E : ℝ) (x₁ : ℕ)
    (hE : 0 < E) (hE2 : E ≤ 1 / 2) (hγ : 0 < γ)
    (h60 : 60 ≤ C₁ * γ) (h1000 : (1000 : ℝ) ≤ C₁)
    (hsmooth : ∀ x : ℕ, x₁ ≤ x →
      γ * (primePi x : ℝ) ≤
        (((Finset.range (x + 1)).filter (fun p => p.Prime ∧
          ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) - E))).card : ℝ)) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ z w y T : ℕ, InWindow C₁ E n z w y T →
      T ≤ (goodPrimesW z w y).card := by
  have hC₁ : (0 : ℝ) < C₁ := lt_of_lt_of_le (by norm_num) h1000
  have hγC₁' : (60 : ℝ) ≤ C₁ * γ := h60
  -- extract a concrete threshold from the proved Chebyshev bound
  obtain ⟨z₀', hz₀'⟩ := Filter.eventually_atTop.mp chebyshev_lower
  -- `4 C₁ log u ≤ u^{1/99}` for `u` large, pulled back along `u = ℓ₂(n)`
  have hlog_rpow : ∀ᶠ u : ℝ in atTop,
      4 * C₁ * Real.log u ≤ u ^ ((1 : ℝ) / 99) := by
    have h := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 99)).def
      (by positivity : (0 : ℝ) < 1 / (4 * C₁))
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with u hu hu1
    have hu0 : (0 : ℝ) ≤ u := by linarith
    have hlog0 : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
    have hr0 : (0 : ℝ) ≤ u ^ ((1 : ℝ) / 99) := Real.rpow_nonneg hu0 _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog0,
      abs_of_nonneg hr0] at hu
    have := mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ 4 * C₁)
    calc 4 * C₁ * Real.log u
        ≤ 4 * C₁ * (1 / (4 * C₁) * u ^ ((1 : ℝ) / 99)) := this
      _ = u ^ ((1 : ℝ) / 99) := by field_simp
  filter_upwards [tendsto_ell2.eventually_ge_atTop 1,
    tendsto_ell2.eventually hlog_rpow,
    tendsto_ell3.eventually_ge_atTop 1,
    tendsto_ell3.eventually_ge_atTop (16 * C₁),
    (tendsto_zreal C₁ h1000).eventually_ge_atTop (x₁ : ℝ),
    (tendsto_zreal C₁ h1000).eventually_ge_atTop (z₀' : ℝ),
    (tendsto_zreal C₁ h1000).eventually_ge_atTop (2 : ℝ)]
    with n h1 h2 h3 h4 hx₁' hz₀'' hz2'
  intro z w y T hw
  -- basic positivity facts
  have hℓ₂0 : (0 : ℝ) ≤ ell2 n := by linarith only [h1]
  have hℓ₃0 : (0 : ℝ) ≤ ell3 n := by linarith only [h3]
  have hC₁ℓ₂ : C₁ * 1 ≤ C₁ * ell2 n := mul_le_mul_of_nonneg_left h1 hC₁.le
  have hCℓ' : (1 : ℝ) ≤ C₁ * ell2 n := by linarith only [hC₁ℓ₂, h1000]
  have hCℓ : (1 : ℝ) ≤ C₁ * ell2 n * ell3 n := by
    have := mul_le_mul_of_nonneg_right hCℓ' hℓ₃0
    linarith only [this, h3]
  -- scale facts from the window
  have hzlb : C₁ * ell2 n * ell3 n ≤ (z : ℝ) := hw.z_lo
  have hzub : (z : ℝ) ≤ 4 * (C₁ * ell2 n * ell3 n) := hw.z_hi
  have hx₁ : x₁ ≤ z := by
    have h : (x₁ : ℝ) ≤ (z : ℝ) := hx₁'.trans hzlb
    exact_mod_cast h
  have hz₀ : z₀' ≤ z := by
    have h : (z₀' : ℝ) ≤ (z : ℝ) := hz₀''.trans hzlb
    exact_mod_cast h
  have hz1 : (1 : ℝ) < (z : ℝ) := by linarith only [hz2', hzlb]
  have hzpos : (0 : ℝ) < (z : ℝ) := by linarith only [hz1]
  have hz0 : (0 : ℝ) ≤ (z : ℝ) := hzpos.le
  have hlogzpos : 0 < Real.log (z : ℝ) := Real.log_pos hz1
  -- `log z ≤ 2 ℓ₃`
  have hlogz : Real.log (z : ℝ) ≤ 2 * ell3 n := by
    have hshape : ell2 n * (4 * C₁ * ell3 n) = 4 * (C₁ * ell2 n * ell3 n) := by ring
    have hstep : (z : ℝ) ≤ ell2 n * (4 * C₁ * ell3 n) := by
      linarith only [hzub, hshape]
    have h4C : (0 : ℝ) < 4 * C₁ := by linarith only [hC₁]
    have hpos2 : (0 : ℝ) < 4 * C₁ * ell3 n := mul_pos h4C (by linarith only [h3])
    have hlog1 : Real.log (z : ℝ)
        ≤ Real.log (ell2 n * (4 * C₁ * ell3 n)) := Real.log_le_log hzpos hstep
    rw [Real.log_mul (by linarith only [h1]) (ne_of_gt hpos2)] at hlog1
    have hlog2 : Real.log (ell2 n) = ell3 n := rfl
    have hlog3 : Real.log (4 * C₁ * ell3 n) ≤ 2 * Real.sqrt (4 * C₁ * ell3 n) :=
      log_le_two_sqrt hpos2.le
    have hsq : Real.sqrt (4 * C₁ * ell3 n) ≤ ell3 n / 2 := by
      have h' : 4 * C₁ * ell3 n ≤ (ell3 n / 2) ^ 2 := by
        nlinarith [mul_le_mul_of_nonneg_right h4 hℓ₃0]
      calc Real.sqrt (4 * C₁ * ell3 n) ≤ Real.sqrt ((ell3 n / 2) ^ 2) :=
            Real.sqrt_le_sqrt h'
        _ = ell3 n / 2 := Real.sqrt_sq (by linarith only [hℓ₃0])
    linarith only [hlog1, hlog2, hlog3, hsq]
  -- `z^{99/100} ≤ ℓ₂`
  have hrpz : (z : ℝ) ^ ((99 : ℝ) / 100) ≤ ell2 n := by
    have hℓ₂pos : (0 : ℝ) < ell2 n := by linarith only [h1]
    have hll : 4 * C₁ * ell3 n ≤ ell2 n ^ ((1 : ℝ) / 99) := h2
    have hb0 : (0 : ℝ) ≤ 4 * (C₁ * ell2 n * ell3 n) := by
      have := mul_nonneg (mul_nonneg hC₁.le hℓ₂0) hℓ₃0
      linarith only [this]
    have step2 : 4 * (C₁ * ell2 n * ell3 n) ≤ ell2 n ^ ((100 : ℝ) / 99) := by
      have hshape : 4 * (C₁ * ell2 n * ell3 n) = ell2 n * (4 * C₁ * ell3 n) := by
        ring
      have h100 : ell2 n ^ ((100 : ℝ) / 99) = ell2 n * ell2 n ^ ((1 : ℝ) / 99) := by
        rw [show (100 : ℝ) / 99 = 1 + 1 / 99 by norm_num, Real.rpow_add hℓ₂pos,
          Real.rpow_one]
      rw [hshape, h100]
      exact mul_le_mul_of_nonneg_left hll hℓ₂0
    have step4 : (ell2 n ^ ((100 : ℝ) / 99)) ^ ((99 : ℝ) / 100) = ell2 n := by
      rw [← Real.rpow_mul hℓ₂pos.le,
        show (100 : ℝ) / 99 * (99 / 100) = 1 by norm_num, Real.rpow_one]
    calc (z : ℝ) ^ ((99 : ℝ) / 100)
        ≤ (4 * (C₁ * ell2 n * ell3 n)) ^ ((99 : ℝ) / 100) :=
          Real.rpow_le_rpow hz0 hzub (by norm_num)
      _ ≤ (ell2 n ^ ((100 : ℝ) / 99)) ^ ((99 : ℝ) / 100) :=
          Real.rpow_le_rpow hb0 step2 (by norm_num)
      _ = ell2 n := step4
  -- `(C₁/2) ℓ₂ ≤ z / log z`
  have hzdiv : C₁ / 2 * ell2 n ≤ (z : ℝ) / Real.log (z : ℝ) := by
    rw [le_div_iff₀ hlogzpos]
    have e1 : C₁ / 2 * ell2 n * Real.log (z : ℝ)
        ≤ C₁ / 2 * ell2 n * (2 * ell3 n) :=
      mul_le_mul_of_nonneg_left hlogz (mul_nonneg (by linarith only [hC₁]) hℓ₂0)
    have e2 : C₁ / 2 * ell2 n * (2 * ell3 n) = C₁ * ell2 n * ell3 n := by ring
    linarith only [e1, e2, hzlb]
  -- `(C₁/6) ℓ₂ ≤ z / (3 log z)`
  have hzdiv3 : C₁ / 6 * ell2 n ≤ (z : ℝ) / (3 * Real.log (z : ℝ)) := by
    rw [mul_comm (3 : ℝ), ← div_div]
    linarith only [hzdiv]
  -- package the AGP smooth-shifted count so that no `Finset.filter`
  -- decidability instances need to be matched syntactically
  obtain ⟨S, hS1, hS2⟩ : ∃ S : Finset ℕ,
      γ * (primePi z : ℝ) ≤ (S.card : ℝ) ∧
      ∀ p ∈ S, p < z + 1 ∧ p.Prime ∧
        ∀ q : ℕ, q.Prime → q ∣ p - 1 →
          (q : ℝ) ≤ (z : ℝ) ^ ((1 : ℝ) - E) := by
    refine ⟨_, hsmooth z hx₁, ?_⟩
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    exact hp
  -- every prime counted by AGP is either in the reservoir or at most `w`
  have hsub : S ⊆ goodPrimesW z w y ∪ Finset.range (w + 1) := by
    intro p hp
    obtain ⟨hpz, hpp, hps⟩ := hS2 p hp
    by_cases hbig : w < p
    · apply Finset.mem_union_left
      simp only [goodPrimesW, Finset.mem_filter, Finset.mem_range]
      refine ⟨hpz, hpp, hbig, ?_⟩
      intro q hq hqd
      have hy : (q : ℝ) ≤ (y : ℝ) := (hps q hq hqd).trans hw.y_lo
      exact_mod_cast hy
    · apply Finset.mem_union_right
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact not_lt.mp hbig
  have hcard : S.card ≤ (goodPrimesW z w y).card + (w + 1) := by
    have hu := Finset.card_union_le (goodPrimesW z w y) (Finset.range (w + 1))
    rw [Finset.card_range] at hu
    exact (Finset.card_le_card hsub).trans hu
  -- combine: `γ π(z) ≤ |goodPrimesW| + 4 ℓ₂ + 1`
  have hkey : γ * (primePi z : ℝ) ≤ ((goodPrimesW z w y).card : ℝ) + 4 * ell2 n + 1 := by
    have hcardR : (S.card : ℝ) ≤ ((goodPrimesW z w y).card : ℝ) + ((w : ℝ) + 1) := by
      exact_mod_cast hcard
    have hw4 : (w : ℝ) ≤ 4 * ell2 n := by
      have := hw.w_hi
      linarith only [this, hrpz]
    linarith only [hS1, hcardR, hw4]
  -- Chebyshev: `γ π(z) ≥ γ (C₁/6) ℓ₂ ≥ 10 ℓ₂`
  have hcheb3 := hz₀' z hz₀
  have hπ10 : (10 : ℝ) * ell2 n ≤ γ * (primePi z : ℝ) := by
    have hg1 : γ * ((z : ℝ) / (3 * Real.log (z : ℝ))) ≤ γ * (primePi z : ℝ) :=
      mul_le_mul_of_nonneg_left hcheb3 hγ.le
    have hg2 : γ * (C₁ / 6 * ell2 n) ≤ γ * ((z : ℝ) / (3 * Real.log (z : ℝ))) :=
      mul_le_mul_of_nonneg_left hzdiv3 hγ.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hγC₁') hℓ₂0]
  -- conclude: `T ≤ 5 ℓ₂ ≤ 10 ℓ₂ - 4 ℓ₂ - 1 ≤ |goodPrimesW|` (using `ℓ₂ ≥ 1`)
  have hTle : (T : ℝ) ≤ 5 * ell2 n := hw.T_hi
  have hfin : (T : ℝ) ≤ ((goodPrimesW z w y).card : ℝ) := by
    linarith only [hTle, hπ10, hkey, h1]
  exact_mod_cast hfin

end Carmichael
