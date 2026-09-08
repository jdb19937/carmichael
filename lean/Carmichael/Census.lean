/-
Route Z, sortie Z7: exceptional-zero census, aggregated over conductors.

TARGET (routez/Z0a-ledger.md §7, frozen contract; character-count form):
for `σ ∈ [39/40, 1]`, `ν ≥ 1`, `Z ≥ 2`,

  `∑_{d′ ≤ Z} #{χ mod d′ primitive : L(·,χ) has a zero in [σ,1]×[−ν,ν]}
      ≤ c₂(ν) · Z^{c₃(1−σ)}`

with `c₂(ν) := 10^{10⁹}·(ν+2)` and the fixed numeral `c₃ := 10¹²`.  This is the
**multiplicity-one (distinct bad character) version** of the census: the ledger
consumes the census only through "each member of 𝓓(x) carries at least one
primitive character with at least one zero in the box", and that consumption
shape is provided verbatim by `card_badConductors_le` below.

ARCHITECTURE (three regimes in `1−σ`, with `𝓛 := log(Z(ν+2))`):
* **Small regime** `(1−σ)·𝓛 ≤ 10⁻⁹`: a Landau–Page-style positivity census,
  proved here in full.  For a family of 13 pairwise-distinct nontrivial
  characters `χ_j mod M_j ≤ Z`, each with a zero `ρ_j = β_j+iγ_j`,
  `β_j ≥ 1−δ`, `|γ_j| ≤ ν`, expand
    `0 ≤ ∑_n Λ(n) n^{−(1+2δ)} |1 + ∑_j χ_j(n) n^{−iγ_j}|²`
  into `−L′/L` values (Mathlib `LSeries_twist_vonMangoldt_eq`), bound every
  term by the Landau partial-fraction expansion (Z4c,
  `norm_logDeriv_sub_sum_zeroDiskFinset_le`, constant `C₆ = 520000`), harvest
  the gain `−1/(3δ)` per bad character from its zero, and contradict.  Hence
  at most 12 bad characters of modulus ≥ 2 (plus possibly the mod-1 ζ
  character): census ≤ 13.
* **Trivial regime** `1−σ ≥ 2/c₃`: there are at most `Z²` characters of
  modulus ≤ Z in total, and `Z² ≤ Z^{c₃(1−σ)}`.
* **Middle regime** (`(1−σ)𝓛 > 10⁻⁹` and `1−σ < 2/c₃`): the genuinely
  log-free Gallagher/Turán mechanism (Thorner–Zaman arXiv:2208.11123).  NOT
  proved in this sortie; isolated as the single documented hypothesis
  `MidCensusHyp` consumed by the top-level `census_contract`.  Everything
  else in this file is unconditional.

MAIN DECLARATIONS:
* `Census.primBadCount`, `Census.censusCount` — the census counting function.
* `Census.no_thirteen_bad` — the positivity core (unconditional).
* `Census.censusCount_le_of_small` — small regime, census ≤ 13 (unconditional).
* `Census.censusCount_le_sq` — trivial regime (unconditional).
* `Census.MidCensusHyp` — the middle-regime hypothesis (documented debt).
* `Census.census_contract` — THE Z7 CONTRACT, conditional on `MidCensusHyp`.
* `Census.card_badConductors_le` — the ledger's 𝓓(x)-consumption shape.
-/
import Carmichael.PartialFractions
import Carmichael.ZeroCount
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality

set_option autoImplicit false

open Complex Finset Metric Filter Carmichael
open ArithmeticFunction (vonMangoldt)
open scoped Classical

namespace Census

noncomputable section

/-! ### §1 Elementary real Dirichlet-series bounds at `s = 1 + u`

We prove, with completely elementary telescoping/mean-value arguments:
* `∑ n^{−(1+u)} ≥ 1/u`;
* `∑ (log n)·n^{−(1+u)} ≤ 1/u² + 1.4/u + 0.9`;
* hence via `Λ ⋆ 1 = log` (Mathlib convolution) `∑ Λ(n) n^{−(1+u)} ≤ 1/u + 2`
  for `0 < u ≤ 1/20`. -/

/-- Downward mean-value bound: `x^{−u} − (x+1)^{−u} ≤ u·x^{−u−1}` for `x ≥ 1`. -/
lemma rpow_diff_le {u : ℝ} (hu : 0 < u) {x : ℝ} (hx : 1 ≤ x) :
    x ^ (-u) - (x + 1) ^ (-u) ≤ u * x ^ (-u - 1) := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
  have hderiv : ∀ y ∈ Set.Ioo x (x + 1),
      HasDerivAt (fun y : ℝ => -(y ^ (-u))) (u * y ^ (-u - 1)) y := by
    intro y hy
    have hy0 : y ≠ 0 := by nlinarith [hy.1]
    have h0 := (Real.hasDerivAt_rpow_const (p := -u) (x := y) (Or.inl hy0)).neg
    rw [show -(-u * y ^ (-u - 1)) = u * y ^ (-u - 1) from by ring] at h0
    exact h0
  have hcont : ContinuousOn (fun y : ℝ => -(y ^ (-u))) (Set.Icc x (x + 1)) := by
    intro y hy
    have hy0 : y ≠ 0 := by nlinarith [hy.1]
    exact ((Real.hasDerivAt_rpow_const (p := -u)
      (Or.inl hy0)).neg).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (fun y : ℝ => -(y ^ (-u)))
    (fun y => u * y ^ (-u - 1)) (by linarith : x < x + 1) hcont hderiv
  have hmono : c ^ (-u - 1) ≤ x ^ (-u - 1) :=
    Real.rpow_le_rpow_of_nonpos hx0 hc.1.le (by linarith)
  have heq : u * c ^ (-u - 1) = x ^ (-u) - (x + 1) ^ (-u) := by
    rw [hc', show x + 1 - x = 1 from by ring, div_one]
    ring
  nlinarith [hmono, hu.le]

/-- Summability of `n^{−(1+u)}`. -/
lemma summable_zeta_rpow {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => (n:ℝ) ^ (-(1+u))) :=
  Real.summable_nat_rpow.mpr (by linarith)

/-- `ζ(1+u) ≥ 1/u`, by telescoping the mean-value bound. -/
lemma one_div_le_tsum_zeta {u : ℝ} (hu : 0 < u) :
    1 / u ≤ ∑' n : ℕ, (n:ℝ) ^ (-(1+u)) := by
  set T : ℝ := ∑' n : ℕ, (n:ℝ) ^ (-(1+u)) with hT
  have hsum := summable_zeta_rpow hu
  have hnonneg : ∀ n : ℕ, 0 ≤ (n:ℝ) ^ (-(1+u)) :=
    fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  -- partial-sum lower bound: `1 − (N+1)^{−u} ≤ u·T` for every `N`
  have key : ∀ N : ℕ, 1 - ((N:ℝ)+1) ^ (-u) ≤ u * T := by
    intro N
    have htel : ∑ i ∈ range N,
        ((((i:ℕ):ℝ)+1) ^ (-u) - (((i+1:ℕ):ℝ)+1) ^ (-u))
        = (((0:ℕ):ℝ)+1) ^ (-u) - (((N:ℕ):ℝ)+1) ^ (-u) :=
      Finset.sum_range_sub' (fun i : ℕ => (((i:ℕ):ℝ)+1) ^ (-u)) N
    have hstep : ∀ i ∈ range N,
        (((i:ℕ):ℝ)+1) ^ (-u) - (((i+1:ℕ):ℝ)+1) ^ (-u)
          ≤ u * (((i+1 : ℕ):ℕ):ℝ) ^ (-(1+u)) := by
      intro i _
      have h1 : (1:ℝ) ≤ (i:ℝ)+1 := by
        have := Nat.cast_nonneg (α := ℝ) i; linarith
      have h2 := rpow_diff_le hu h1
      push_cast
      calc ((i:ℝ)+1) ^ (-u) - ((i:ℝ)+1+1) ^ (-u)
          ≤ u * ((i:ℝ)+1) ^ (-u-1) := h2
        _ = u * ((i:ℝ)+1) ^ (-(1+u)) := by
            rw [show (-u-1 : ℝ) = -(1+u) from by ring]
    have hsum_le : ∑ i ∈ range N,
        ((((i:ℕ):ℝ)+1) ^ (-u) - (((i+1:ℕ):ℝ)+1) ^ (-u))
          ≤ u * ∑ i ∈ range N, (((i+1 : ℕ):ℕ):ℝ) ^ (-(1+u)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hstep
    have hinj : ∀ x ∈ range N, ∀ y ∈ range N, x + 1 = y + 1 → x = y := by
      intro a _ b _ h; omega
    have himg : ∑ n ∈ (range N).image (fun i : ℕ => i + 1), (n:ℝ) ^ (-(1+u))
        = ∑ i ∈ range N, (((i+1 : ℕ):ℕ):ℝ) ^ (-(1+u)) := Finset.sum_image hinj
    have hle_T : ∑ n ∈ (range N).image (fun i : ℕ => i + 1),
        (n:ℝ) ^ (-(1+u)) ≤ T :=
      Summable.sum_le_tsum _ (fun n _ => hnonneg n) hsum
    have h01 : (((0:ℕ):ℝ)+1) ^ (-u) = 1 := by
      norm_num
    have hfin : ∑ i ∈ range N, (((i+1 : ℕ):ℕ):ℝ) ^ (-(1+u)) ≤ T := by
      rw [← himg]; exact hle_T
    have := htel
    nlinarith [hsum_le, hfin, hu.le, htel, h01]
  -- pass to the limit `N → ∞`
  have hlim0 : Tendsto (fun N : ℕ => ((N:ℝ)+1) ^ (-u)) atTop (nhds 0) := by
    have h1 : Tendsto (fun N : ℕ => (N:ℝ)+1) atTop atTop :=
      Filter.tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    exact (tendsto_rpow_neg_atTop hu).comp h1
  have hlim : Tendsto (fun N : ℕ => 1 - ((N:ℝ)+1) ^ (-u)) atTop (nhds 1) := by
    have := hlim0.const_sub 1
    simpa using this
  have h1uT : 1 ≤ u * T := le_of_tendsto' hlim key
  rw [div_le_iff₀ hu]
  linarith [h1uT]

/-- `log x ≤ (2/u)·x^{u/2}` for `x ≥ 1`, `u > 0`. -/
lemma log_le_rpow_half {u : ℝ} (hu : 0 < u) {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ (2/u) * x ^ (u/2) := by
  have h0 : (0:ℝ) < x := by linarith
  have h1 : Real.log (x ^ (u/2)) ≤ x ^ (u/2) - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos h0 _)
  rw [Real.log_rpow h0] at h1
  have h2 : (u/2) * Real.log x ≤ x ^ (u/2) := by
    nlinarith [Real.rpow_pos_of_pos h0 (u/2)]
  have h3 : Real.log x = (2/u) * ((u/2) * Real.log x) := by
    field_simp
  rw [h3]
  have h4 : (0:ℝ) < 2/u := by positivity
  nlinarith [h2, h4]

/-- Summability of `(log n)·n^{−(1+u)}`. -/
lemma summable_log_rpow {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => Real.log n * (n:ℝ) ^ (-(1+u))) := by
  have hmaj : Summable (fun n : ℕ => (2/u) * (n:ℝ) ^ (-(1+u/2))) := by
    exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have := Real.log_nonneg h1
      have := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1+u))
      positivity
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
      positivity
    · have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have h0 : (0:ℝ) < (n:ℝ) := by linarith
      have h2 := log_le_rpow_half hu h1
      have h3 : Real.log n * (n:ℝ) ^ (-(1+u))
          ≤ ((2/u) * (n:ℝ) ^ (u/2)) * (n:ℝ) ^ (-(1+u)) := by
        have := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1+u))
        nlinarith
      have h4 : ((2/u) * (n:ℝ) ^ (u/2)) * (n:ℝ) ^ (-(1+u))
          = (2/u) * (n:ℝ) ^ (-(1+u/2)) := by
        rw [mul_assoc, ← Real.rpow_add h0,
          show u/2 + -(1+u) = -(1+u/2) from by ring]
      linarith [h3, h4.le, h4.ge]

/-- `t ↦ (log t)·t^{−(1+u)}` is decreasing on `[3, ∞)`. -/
lemma log_mul_rpow_decreasing {u a b : ℝ} (hu : 0 < u) (ha : 3 ≤ a) (hab : a ≤ b) :
    Real.log b * b ^ (-(1+u)) ≤ Real.log a * a ^ (-(1+u)) := by
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hla : 1 ≤ Real.log a := by
    rw [Real.le_log_iff_exp_le ha0]
    have := Real.exp_one_lt_d9
    linarith
  have hba1 : 1 ≤ b / a := (one_le_div ha0).mpr hab
  have h1 : Real.log b ≤ Real.log a * (b / a) := by
    have h2 : Real.log b = Real.log a + Real.log (b/a) := by
      rw [← Real.log_mul ha0.ne' (by positivity : (b/a : ℝ) ≠ 0)]
      congr 1
      field_simp
    have h3 : Real.log (b/a) ≤ b/a - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    nlinarith [hla, hba1]
  have h5 : b ^ (-u) ≤ a ^ (-u) :=
    Real.rpow_le_rpow_of_nonpos ha0 hab (by linarith)
  have h6 : (b/a) * b ^ (-(1+u)) ≤ a ^ (-(1+u)) := by
    have hbrw : b ^ (-(1+u)) = b ^ (-u) * b⁻¹ := by
      rw [← Real.rpow_neg_one b, ← Real.rpow_add hb0]
      congr 1; ring
    have harw : a ^ (-(1+u)) = a ^ (-u) * a⁻¹ := by
      rw [← Real.rpow_neg_one a, ← Real.rpow_add ha0]
      congr 1; ring
    rw [hbrw, harw]
    have hrw : (b/a) * (b ^ (-u) * b⁻¹) = b ^ (-u) * a⁻¹ := by
      field_simp
    rw [hrw]
    exact mul_le_mul_of_nonneg_right h5 (by positivity)
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
  have hrpb : 0 ≤ b ^ (-(1+u)) := Real.rpow_nonneg hb0.le _
  calc Real.log b * b ^ (-(1+u))
      ≤ (Real.log a * (b/a)) * b ^ (-(1+u)) :=
        mul_le_mul_of_nonneg_right h1 hrpb
    _ = Real.log a * ((b/a) * b ^ (-(1+u))) := by ring
    _ ≤ Real.log a * a ^ (-(1+u)) :=
        mul_le_mul_of_nonneg_left h6 (by linarith)

/-- Exact antiderivative for the log-series telescope:
`d/dt [t^{−u}(log t/u + 1/u²)] = −(log t)·t^{−(1+u)}`. -/
lemma Gfun_hasDerivAt {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => t ^ (-u) * (Real.log t / u + 1/u^2))
      (-(Real.log t * t ^ (-(1+u)))) t := by
  have hu' : u ≠ 0 := hu.ne'
  have h1 : HasDerivAt (fun t : ℝ => t ^ (-u)) (-u * t ^ (-u - 1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have h2 : HasDerivAt (fun t : ℝ => Real.log t / u + 1/u^2) (t⁻¹ / u) t :=
    ((Real.hasDerivAt_log ht.ne').div_const u).add_const _
  have h3 := h1.mul h2
  have e1 : t ^ (-u - 1) = t ^ (-u) * t⁻¹ := by
    rw [show (-u - 1 : ℝ) = -u + (-1) from by ring, Real.rpow_add ht,
      Real.rpow_neg_one]
  have e2 : t ^ (-(1+u)) = t ^ (-u) * t⁻¹ := by
    rw [show (-(1 + u) : ℝ) = -u + (-1) from by ring, Real.rpow_add ht,
      Real.rpow_neg_one]
  have hval : -u * t ^ (-u - 1) * (Real.log t / u + 1 / u ^ 2) + t ^ (-u) * (t⁻¹ / u)
      = -(Real.log t * t ^ (-(1+u))) := by
    rw [e1, e2]
    field_simp
    ring
  have hfun : ((fun t : ℝ => t ^ (-u)) * fun t : ℝ => Real.log t / u + 1 / u ^ 2)
      = (fun t : ℝ => t ^ (-u) * (Real.log t / u + 1/u^2)) := rfl
  rw [hfun, hval] at h3
  exact h3

/-- One telescoping step for the log series, `n ≥ 4`. -/
lemma log_rpow_le_G_diff {u : ℝ} (hu : 0 < u) {n : ℕ} (hn : 4 ≤ n) :
    Real.log n * (n:ℝ) ^ (-(1+u))
      ≤ ((n:ℝ)-1) ^ (-u) * (Real.log ((n:ℝ)-1) / u + 1/u^2)
          - (n:ℝ) ^ (-u) * (Real.log (n:ℝ) / u + 1/u^2) := by
  have hn4 : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hab : (n:ℝ) - 1 < (n:ℝ) := by linarith
  set G : ℝ → ℝ := fun t => t ^ (-u) * (Real.log t / u + 1/u^2) with hG
  have hcont : ContinuousOn G (Set.Icc ((n:ℝ)-1) (n:ℝ)) := by
    intro y hy
    have hy0 : (0:ℝ) < y := by have := hy.1; linarith
    exact (Gfun_hasDerivAt hu hy0).continuousAt.continuousWithinAt
  have hderiv : ∀ y ∈ Set.Ioo ((n:ℝ)-1) (n:ℝ),
      HasDerivAt G (-(Real.log y * y ^ (-(1+u)))) y := by
    intro y hy
    have hy0 : (0:ℝ) < y := by have := hy.1; linarith
    exact Gfun_hasDerivAt hu hy0
  obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope G
    (fun y => -(Real.log y * y ^ (-(1+u)))) hab hcont hderiv
  have hc3 : (3:ℝ) ≤ c := by have := hc.1; linarith
  have hmono := log_mul_rpow_decreasing hu hc3 hc.2.le
  have heq : G ((n:ℝ)-1) - G (n:ℝ) = Real.log c * c ^ (-(1+u)) := by
    have h := hc'
    rw [show (n:ℝ) - ((n:ℝ)-1) = 1 from by ring, div_one] at h
    have h' : -(Real.log c * c ^ (-(1+u))) = G (n:ℝ) - G ((n:ℝ)-1) := h
    linarith [h'.le, h'.ge]
  calc Real.log n * (n:ℝ) ^ (-(1+u))
      ≤ Real.log c * c ^ (-(1+u)) := hmono
    _ = G ((n:ℝ)-1) - G (n:ℝ) := heq.symm

/-- Upper bound for the log series: `∑ (log n)·n^{−(1+u)} ≤ 1/u² + 1.4/u + 0.9`. -/
lemma tsum_log_rpow_le {u : ℝ} (hu : 0 < u) (_hu1 : u ≤ 1) :
    ∑' n : ℕ, Real.log n * (n:ℝ) ^ (-(1+u)) ≤ 1/u^2 + 1.4/u + 0.9 := by
  have hnn : ∀ n : ℕ, 0 ≤ Real.log n * (n:ℝ) ^ (-(1+u)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      have := Real.log_nonneg h1
      have := Real.rpow_nonneg (Nat.cast_nonneg n) (-(1+u))
      positivity
  have hu2 : (0:ℝ) < u^2 := by positivity
  have hB0 : (0:ℝ) ≤ 1/u^2 + 1.4/u := by positivity
  -- small terms
  have hlog2 : Real.log 2 ≤ 0.6931472 := by linarith [Real.log_two_lt_d9]
  have hlog3 : Real.log 3 ≤ 1.3862944 := by
    calc Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
      _ = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2^(2:ℕ) from by norm_num, Real.log_pow]
          push_cast; ring
      _ ≤ 1.3862944 := by linarith
  have e2 : Real.log 2 * (2:ℝ) ^ (-(1+u)) ≤ 0.3465736 := by
    have h1 : (2:ℝ) ^ (-(1+u)) ≤ 2 ^ (-(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2:ℝ) ^ (-(1:ℝ)) = 1/2 := by
      rw [Real.rpow_neg_one]; norm_num
    have h3 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    calc Real.log 2 * (2:ℝ) ^ (-(1+u))
        ≤ Real.log 2 * (1/2) := by
          apply mul_le_mul_of_nonneg_left _ h3
          rw [← h2]; exact h1
      _ ≤ 0.6931472 * (1/2) := by linarith
      _ ≤ 0.3465736 := by norm_num
  have e3 : Real.log 3 * (3:ℝ) ^ (-(1+u)) ≤ 0.4620982 := by
    have h1 : (3:ℝ) ^ (-(1+u)) ≤ 3 ^ (-(1:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (3:ℝ) ^ (-(1:ℝ)) = 1/3 := by
      rw [Real.rpow_neg_one]; norm_num
    have h3 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    calc Real.log 3 * (3:ℝ) ^ (-(1+u))
        ≤ Real.log 3 * (1/3) := by
          apply mul_le_mul_of_nonneg_left _ h3
          rw [← h2]; exact h1
      _ ≤ 1.3862944 * (1/3) := by linarith
      _ ≤ 0.4620982 := by norm_num
  -- the tail telescopes against `G`
  set G : ℝ → ℝ := fun t => t ^ (-u) * (Real.log t / u + 1/u^2) with hG
  have hGnonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ G t := by
    intro t ht
    have h1 : (0:ℝ) ≤ t ^ (-u) := Real.rpow_nonneg (by linarith) _
    have h2 : (0:ℝ) ≤ Real.log t := Real.log_nonneg ht
    have h3 : (0:ℝ) ≤ Real.log t / u + 1/u^2 := by positivity
    exact mul_nonneg h1 h3
  have hG3 : G 3 ≤ 1.4/u + 1/u^2 := by
    have h1 : (3:ℝ) ^ (-u) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
    have hl3 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h2 : (0:ℝ) ≤ Real.log 3 / u + 1/u^2 := by positivity
    have h3 : G 3 ≤ Real.log 3 / u + 1/u^2 := by
      calc G 3 = (3:ℝ) ^ (-u) * (Real.log 3 / u + 1/u^2) := rfl
        _ ≤ 1 * (Real.log 3 / u + 1/u^2) := mul_le_mul_of_nonneg_right h1 h2
        _ = Real.log 3 / u + 1/u^2 := one_mul _
    have h4 : Real.log 3 / u ≤ 1.4/u := by gcongr; linarith
    linarith
  -- head bound
  have hhead : ∑ n ∈ range 4, Real.log n * (n:ℝ) ^ (-(1+u)) ≤ 0.9 := by
    have hz : Real.log 0 * (0:ℝ) ^ (-(1+u)) = 0 := by rw [Real.log_zero]; ring
    have ho : Real.log 1 * (1:ℝ) ^ (-(1+u)) = 0 := by rw [Real.log_one]; ring
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_one]
    push_cast
    rw [hz, ho]
    linarith [e2, e3]
  -- partial-sum bound
  have hrange : ∀ N : ℕ, ∑ n ∈ range N, Real.log n * (n:ℝ) ^ (-(1+u))
      ≤ 1/u^2 + 1.4/u + 0.9 := by
    intro N
    rcases le_or_gt N 4 with hN | hN
    · have hsub : range N ⊆ range 4 := by
        intro x hx
        rw [Finset.mem_range] at *
        omega
      have h1 : ∑ n ∈ range N, Real.log n * (n:ℝ) ^ (-(1+u))
          ≤ ∑ n ∈ range 4, Real.log n * (n:ℝ) ^ (-(1+u)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hnn n)
      linarith
    · -- split at 4
      have h4N : (4:ℕ) ≤ N := hN.le
      have hsplit := Finset.sum_Ico_consecutive
        (f := fun n : ℕ => Real.log n * (n:ℝ) ^ (-(1+u)))
        (by norm_num : (0:ℕ) ≤ 4) h4N
      rw [← Finset.range_eq_Ico, ← Finset.range_eq_Ico] at hsplit
      -- tail bound via telescoping
      have htail : ∑ n ∈ Finset.Ico 4 N, Real.log n * (n:ℝ) ^ (-(1+u)) ≤ G 3 := by
        rw [Finset.sum_Ico_eq_sum_range]
        set K : ℕ → ℝ := fun i => G ((i:ℝ)+3) with hK
        have hstep : ∀ i ∈ range (N-4),
            Real.log ((4+i : ℕ)) * ((4+i:ℕ):ℝ) ^ (-(1+u)) ≤ K i - K (i+1) := by
          intro i _
          have h := log_rpow_le_G_diff hu (n := 4+i) (by omega)
          have hc : ((4+i : ℕ):ℝ) = (i:ℝ)+4 := by push_cast; ring
          rw [hc, show (i:ℝ)+4-1 = (i:ℝ)+3 from by ring] at h
          have hKi : K i = ((i:ℝ)+3) ^ (-u) * (Real.log ((i:ℝ)+3) / u + 1/u^2) := rfl
          have hKi1 : K (i+1) = ((i:ℝ)+4) ^ (-u) * (Real.log ((i:ℝ)+4) / u + 1/u^2) := by
            simp only [hK, hG]
            push_cast
            ring_nf
          rw [hKi, hKi1]
          calc Real.log ((4+i : ℕ)) * ((4+i:ℕ):ℝ) ^ (-(1+u))
              = Real.log ((i:ℝ)+4) * ((i:ℝ)+4) ^ (-(1+u)) := by rw [hc]
            _ ≤ _ := h
        have htel : ∑ i ∈ range (N-4), (K i - K (i+1)) = K 0 - K (N-4) :=
          Finset.sum_range_sub' K (N-4)
        have hK0 : K 0 = G 3 := by
          simp only [hK]
          norm_num
        have hKN : 0 ≤ K (N-4) := by
          apply hGnonneg
          have : (0:ℝ) ≤ ((N-4 : ℕ):ℝ) := Nat.cast_nonneg _
          linarith
        calc ∑ i ∈ range (N-4), Real.log ((4+i : ℕ)) * ((4+i:ℕ):ℝ) ^ (-(1+u))
            ≤ ∑ i ∈ range (N-4), (K i - K (i+1)) := Finset.sum_le_sum hstep
          _ = K 0 - K (N-4) := htel
          _ ≤ G 3 := by rw [hK0]; linarith
      have := hsplit
      linarith [hhead, htail, hG3]
  exact Real.tsum_le_of_sum_range_le hnn hrange

/-- Summability of `Λ(n)·n^{−(1+u)}`. -/
lemma summable_vonMangoldt_rpow {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => vonMangoldt n * (n:ℝ) ^ (-(1+u))) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (summable_log_rpow hu)
  · have h1 : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have h2 : (0:ℝ) ≤ (n:ℝ) ^ (-(1+u)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    positivity
  · exact mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-! ### §2 Complex/real interface for `LSeries` at a real point -/

/-- `LSeries` of a real-coefficient sequence at a real point `x > 0` is the
(complexified) real Dirichlet series. -/
lemma LSeries_ofReal_eq {f : ℕ → ℝ} {x : ℝ} (hx : 0 < x) :
    LSeries (fun n => (f n : ℂ)) ((x : ℝ) : ℂ)
      = ((∑' n : ℕ, f n * (n:ℝ) ^ (-x) : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero]
    rw [show ((0:ℕ):ℝ) = (0:ℝ) from by norm_num, Real.zero_rpow (by linarith : -x ≠ 0)]
    norm_num
  · rw [LSeries.term_of_ne_zero hn]
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h1 : (n:ℂ) ^ ((x:ℝ):ℂ) = (((n:ℝ) ^ x : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hn0 x]
      norm_num
    rw [h1, show ((f n : ℂ)) / (((n:ℝ)^x : ℝ):ℂ) = ((f n / (n:ℝ)^x : ℝ) : ℂ) from by
      push_cast; ring]
    congr 1
    rw [Real.rpow_neg hn0]
    ring

/-- `∑ Λ(n)·n^{−(1+u)} ≤ 1/u + 2` for `0 < u ≤ 1/20`: the sharp-coefficient
`−ζ′/ζ(1+u)` bound, obtained from `Λ ⋆ 1 = log` at the level of absolutely
convergent series. -/
lemma tsum_vonMangoldt_rpow_le {u : ℝ} (hu : 0 < u) (hu' : u ≤ 1/20) :
    ∑' n : ℕ, vonMangoldt n * (n:ℝ) ^ (-(1+u)) ≤ 1/u + 2 := by
  have hx0 : (0:ℝ) < 1 + u := by linarith
  have hxre : 1 < (((1+u : ℝ)):ℂ).re := by
    rw [Complex.ofReal_re]; linarith
  -- the three series
  set a : ℝ := ∑' n : ℕ, vonMangoldt n * (n:ℝ) ^ (-(1+u)) with ha
  set z : ℝ := ∑' n : ℕ, (1:ℝ) * (n:ℝ) ^ (-(1+u)) with hz
  set w : ℝ := ∑' n : ℕ, Real.log n * (n:ℝ) ^ (-(1+u)) with hw
  -- complex identifications
  have hA : LSeries (fun n => (vonMangoldt n : ℂ)) (((1+u:ℝ)):ℂ) = (a:ℂ) :=
    LSeries_ofReal_eq hx0
  have hZfun : (fun n : ℕ => ((1:ℝ) : ℂ)) = (1 : ℕ → ℂ) := by
    funext n; norm_num
  have hZ : LSeries (1 : ℕ → ℂ) (((1+u:ℝ)):ℂ) = (z:ℂ) := by
    rw [← hZfun]
    exact LSeries_ofReal_eq hx0
  have hW : LSeries (fun n => ((Real.log n : ℝ) : ℂ)) (((1+u:ℝ)):ℂ) = (w:ℂ) :=
    LSeries_ofReal_eq hx0
  -- convolution identity `L(Λ)·L(1) = L(log)`
  have hΛs : LSeriesSummable (fun n => (vonMangoldt n : ℂ)) (((1+u:ℝ)):ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hxre
  have h1s : LSeriesSummable (1 : ℕ → ℂ) (((1+u:ℝ)):ℂ) :=
    LSeriesSummable_one_iff.mpr hxre
  have hconv := LSeries_convolution' hΛs h1s
  have hlogeq : LSeries (LSeries.convolution (fun n => (vonMangoldt n : ℂ)) 1)
      (((1+u:ℝ)):ℂ) = LSeries (fun n => ((Real.log n : ℝ) : ℂ)) (((1+u:ℝ)):ℂ) := by
    apply LSeries_congr
    intro n _
    rw [LSeries.convolution_def]
    simp only [Pi.one_apply, mul_one]
    rw [show (∑ p ∈ n.divisorsAntidiagonal, (vonMangoldt p.1 : ℂ))
        = ((∑ p ∈ n.divisorsAntidiagonal, vonMangoldt p.1 : ℝ) : ℂ) from by
      push_cast; rfl]
    congr 1
    rw [show (∑ p ∈ n.divisorsAntidiagonal, vonMangoldt p.1)
        = ∑ i ∈ n.divisors, vonMangoldt i from
      Nat.sum_divisorsAntidiagonal (fun i _ => vonMangoldt i)]
    exact ArithmeticFunction.vonMangoldt_sum
  -- real identity `a·z = w`
  have hreal : a * z = w := by
    have h := hconv
    rw [hlogeq, hA, hZ, hW, ← Complex.ofReal_mul] at h
    exact_mod_cast h.symm
  -- bounds
  have ha0 : 0 ≤ a := by
    rw [ha]
    apply tsum_nonneg
    intro n
    have h1 : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have h2 : (0:ℝ) ≤ (n:ℝ) ^ (-(1+u)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    positivity
  have hzlow : 1/u ≤ z := by
    rw [hz]
    calc 1/u ≤ ∑' n : ℕ, (n:ℝ) ^ (-(1+u)) := one_div_le_tsum_zeta hu
      _ = ∑' n : ℕ, (1:ℝ) * (n:ℝ) ^ (-(1+u)) := by
          apply tsum_congr; intro n; ring
  have hwup : w ≤ 1/u^2 + 1.4/u + 0.9 := tsum_log_rpow_le hu (by linarith)
  -- combine: `a ≤ u·w ≤ 1/u + 1.4 + 0.9u ≤ 1/u + 2`
  have hz0 : 0 < z := lt_of_lt_of_le (by positivity) hzlow
  have haz : a * (1/u) ≤ a * z := mul_le_mul_of_nonneg_left hzlow ha0
  have hauw : a ≤ u * w := by
    rw [hreal] at haz
    have h2 : a * (1/u) = a / u := by ring
    rw [h2] at haz
    calc a = (a / u) * u := by field_simp
      _ ≤ w * u := mul_le_mul_of_nonneg_right haz hu.le
      _ = u * w := by ring
  have hfin : u * w ≤ 1/u + 2 := by
    have h1 : u * w ≤ u * (1/u^2 + 1.4/u + 0.9) :=
      mul_le_mul_of_nonneg_left hwup hu.le
    have h2 : u * (1/u^2 + 1.4/u + 0.9) = 1/u + 1.4 + 0.9*u := by
      field_simp
    rw [h2] at h1
    linarith
  linarith

/-! ### §3 Character algebra: conjugate and product characters -/

/-- The complex-conjugate Dirichlet character. -/
def conjChar {N : ℕ} (χ : DirichletCharacter ℂ N) : DirichletCharacter ℂ N :=
  χ.ringHomComp (starRingEnd ℂ)

lemma conjChar_apply {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ZMod N) :
    conjChar χ x = (starRingEnd ℂ) (χ x) :=
  MulChar.ringHomComp_apply χ _ x

/-- On `ℂ`, conjugation of a Dirichlet character is its group inverse. -/
lemma conjChar_eq_inv {N : ℕ} (χ : DirichletCharacter ℂ N) :
    conjChar χ = χ⁻¹ := by
  apply MulChar.ext
  intro x
  rw [conjChar_apply, MulChar.inv_apply_eq_inv']
  exact (Complex.inv_eq_conj (DirichletCharacter.unit_norm_eq_one χ x)).symm

/-- Value of the product character `χ₁·conj χ₂ mod M₁M₂` at a natural number. -/
lemma prodChar_apply {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂]
    (χ₁ : DirichletCharacter ℂ M₁) (χ₂ : DirichletCharacter ℂ M₂) (n : ℕ) :
    (DirichletCharacter.changeLevel (dvd_mul_right M₁ M₂) χ₁
      * DirichletCharacter.changeLevel (dvd_mul_left M₂ M₁) (conjChar χ₂))
      ((n : ZMod (M₁ * M₂)))
    = χ₁ ((n : ZMod M₁)) * (starRingEnd ℂ) (χ₂ ((n : ZMod M₂))) := by
  have : NeZero (M₁ * M₂) := ⟨Nat.mul_ne_zero (NeZero.ne M₁) (NeZero.ne M₂)⟩
  rw [MulChar.mul_apply]
  by_cases hn : IsUnit ((n : ZMod (M₁ * M₂)))
  · have hu : ((hn.unit : (ZMod (M₁ * M₂))ˣ) : ZMod (M₁ * M₂)) = (n : ZMod (M₁ * M₂)) :=
      hn.unit_spec
    rw [← hu, DirichletCharacter.changeLevel_eq_cast_of_dvd χ₁ _ hn.unit,
      DirichletCharacter.changeLevel_eq_cast_of_dvd (conjChar χ₂) _ hn.unit,
      conjChar_apply]
    rw [hu]
    rw [ZMod.cast_natCast (dvd_mul_right M₁ M₂), ZMod.cast_natCast (dvd_mul_left M₂ M₁)]
  · -- not a unit mod `M₁M₂`: both sides vanish
    have hcop : ¬ (Nat.Coprime n (M₁ * M₂)) := by
      intro hc
      exact hn ((ZMod.isUnit_iff_coprime n (M₁ * M₂)).mpr hc)
    rw [Nat.coprime_mul_iff_right] at hcop
    have h0 : χ₁ ((n : ZMod M₁)) = 0 ∨ χ₂ ((n : ZMod M₂)) = 0 := by
      by_cases h1 : Nat.Coprime n M₁
      · by_cases h2 : Nat.Coprime n M₂
        · exact absurd ⟨h1, h2⟩ hcop
        · exact Or.inr (MulChar.map_nonunit χ₂
            (fun hu => h2 ((ZMod.isUnit_iff_coprime n M₂).mp hu)))
      · exact Or.inl (MulChar.map_nonunit χ₁
          (fun hu => h1 ((ZMod.isUnit_iff_coprime n M₁).mp hu)))
    have hL1 : (DirichletCharacter.changeLevel (dvd_mul_right M₁ M₂) χ₁)
        ((n : ZMod (M₁ * M₂))) = 0 := MulChar.map_nonunit _ hn
    rw [hL1, zero_mul]
    rcases h0 with h | h
    · rw [h, zero_mul]
    · rw [h, map_zero, mul_zero]

/-- Distinct primitive characters have a nonprincipal product `χ₁·conj χ₂`. -/
lemma prodChar_ne_one {M₁ M₂ : ℕ} [NeZero M₁] [NeZero M₂]
    {χ₁ : DirichletCharacter ℂ M₁} {χ₂ : DirichletCharacter ℂ M₂}
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (hne : (⟨M₁, χ₁⟩ : Σ d : ℕ, DirichletCharacter ℂ d) ≠ ⟨M₂, χ₂⟩) :
    DirichletCharacter.changeLevel (dvd_mul_right M₁ M₂) χ₁
      * DirichletCharacter.changeLevel (dvd_mul_left M₂ M₁) (conjChar χ₂) ≠ 1 := by
  intro heq
  have : NeZero (M₁ * M₂) := ⟨Nat.mul_ne_zero (NeZero.ne M₁) (NeZero.ne M₂)⟩
  have h3 : DirichletCharacter.changeLevel (dvd_mul_right M₁ M₂) χ₁
      = (DirichletCharacter.changeLevel (dvd_mul_left M₂ M₁) (conjChar χ₂))⁻¹ :=
    eq_inv_of_mul_eq_one_left heq
  have h4 : (DirichletCharacter.changeLevel (dvd_mul_left M₂ M₁) (conjChar χ₂))⁻¹
      = DirichletCharacter.changeLevel (dvd_mul_left M₂ M₁) χ₂ := by
    rw [conjChar_eq_inv, map_inv, inv_inv]
  have h5 : DirichletCharacter.changeLevel (dvd_mul_right M₁ M₂) χ₁
      = DirichletCharacter.changeLevel (dvd_mul_left M₂ M₁) χ₂ := h3.trans h4
  have hM : M₁ = M₂ := by
    have hc1 : (DirichletCharacter.changeLevel (dvd_mul_right M₁ M₂) χ₁).conductor
        = M₁ := by
      rw [DirichletCharacter.conductor_changeLevel]
      exact h₁
    have hc2 : (DirichletCharacter.changeLevel (dvd_mul_left M₂ M₁) χ₂).conductor
        = M₂ := by
      rw [DirichletCharacter.conductor_changeLevel]
      exact h₂
    rw [h5] at hc1
    rw [hc1] at hc2
    exact hc2
  subst hM
  have hχ : χ₁ = χ₂ := DirichletCharacter.changeLevel_injective (dvd_mul_right M₁ M₁) h5
  subst hχ
  exact hne rfl

/-- A primitive character of modulus `≥ 2` is nontrivial. -/
lemma prim_ne_one {M : ℕ} [NeZero M] (hM : 2 ≤ M) {χ : DirichletCharacter ℂ M}
    (hprim : χ.IsPrimitive) : χ ≠ 1 := by
  intro h
  subst h
  rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hprim
  omega

/-! ### §4 Partial-fraction consequences for `Re(−L′/L)` at `Re s = 1 + a` -/

/-- `Re((m:ℂ)/w) ≥ 0` when `Re w ≥ 0`. -/
lemma re_natCast_div_nonneg {m : ℕ} {w : ℂ} (hw : 0 ≤ w.re) :
    0 ≤ ((m:ℂ) / w).re := by
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
  have h1 : (0:ℝ) ≤ Complex.normSq w := Complex.normSq_nonneg w
  positivity

/-- `Re((m:ℂ)/x) = m/x` for real `x`. -/
lemma re_natCast_div_real (m : ℕ) (x : ℝ) :
    (((m:ℂ)) / ((x:ℝ):ℂ)).re = (m:ℝ) / x := by
  rw [show ((m:ℂ)) = (((m:ℝ)):ℂ) from by push_cast; rfl, ← Complex.ofReal_div,
    Complex.ofReal_re]

/-- **PF upper bound**: `Re(−L′/L(s,χ)) ≤ 520000·log(N(|t|+2))` at
`s = (1+a) + it`, any `0 < a ≤ 1/2`, `χ ≠ 1`. -/
lemma re_neg_logDeriv_le {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (t : ℝ) {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 1/2) :
    (-(deriv (DirichletCharacter.LFunction χ) (((1+a : ℝ):ℂ) + t * I)
        / DirichletCharacter.LFunction χ (((1+a : ℝ):ℂ) + t * I))).re
      ≤ 520000 * Real.log (N * (|t| + 2)) := by
  set s : ℂ := ((1+a : ℝ):ℂ) + t * I with hs
  have hsre : s.re = 1 + a := by
    simp [hs]
  have hmem : s ∈ closedBall ((2:ℂ) + t * I) (3/2 : ℝ) := by
    rw [mem_closedBall, Complex.dist_eq]
    have hdiff : s - ((2:ℂ) + t * I) = ((1 + a - 2 : ℝ) : ℂ) := by
      rw [hs]; push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hL0 : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by rw [hsre]; linarith)
  have hpf := norm_logDeriv_sub_sum_zeroDiskFinset_le hχ t hmem hL0
  have hsum_nonneg : 0 ≤ (∑ ρ ∈ zeroDiskFinset χ t,
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_nonneg
    intro ρ hρ
    have hρz := (mem_zeroDiskFinset hχ).mp hρ
    have hρre : ρ.re < 1 := by
      by_contra hcon
      push Not at hcon
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hcon)
        hρz.2
    apply re_natCast_div_nonneg
    rw [Complex.sub_re, hsre]
    linarith
  have habs := Complex.abs_re_le_norm
    (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
      - ∑ ρ ∈ zeroDiskFinset χ t,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ))
  rw [Complex.sub_re] at habs
  have h1 := abs_le.mp (le_trans habs hpf)
  rw [Complex.neg_re]
  linarith [hsum_nonneg, h1.1]

/-- **PF gain bound**: if `L(ρ,χ) = 0` with `1−δ ≤ Re ρ ≤ 1`, then at
`s = (1+2δ) + i·Im ρ`,
`Re(−L′/L(s,χ)) ≤ 520000·log(N(|Im ρ|+2)) − 1/(3δ)`. -/
lemma re_neg_logDeriv_le_of_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1/40) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0)
    (hre1 : 1 - δ ≤ ρ.re) (hre2 : ρ.re ≤ 1) :
    (-(deriv (DirichletCharacter.LFunction χ) (((1+2*δ : ℝ):ℂ) + ρ.im * I)
        / DirichletCharacter.LFunction χ (((1+2*δ : ℝ):ℂ) + ρ.im * I))).re
      ≤ 520000 * Real.log (N * (|ρ.im| + 2)) - 1/(3*δ) := by
  set t : ℝ := ρ.im with ht
  set s : ℂ := ((1+2*δ : ℝ):ℂ) + t * I with hs
  have hsre : s.re = 1 + 2*δ := by
    simp [hs]
  have hsim : s.im = t := by
    simp [hs]
  have hmem : s ∈ closedBall ((2:ℂ) + t * I) (3/2 : ℝ) := by
    rw [mem_closedBall, Complex.dist_eq]
    have hdiff : s - ((2:ℂ) + t * I) = ((1 + 2*δ - 2 : ℝ) : ℂ) := by
      rw [hs]; push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hL0 : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by rw [hsre]; linarith)
  have hpf := norm_logDeriv_sub_sum_zeroDiskFinset_le hχ t hmem hL0
  -- `ρ` is a disk zero
  have hρmem : ρ ∈ zeroDiskFinset χ t := by
    rw [mem_zeroDiskFinset hχ]
    refine ⟨?_, hzero⟩
    rw [mem_closedBall, Complex.dist_eq]
    have hdiff : ρ - ((2:ℂ) + t * I) = ((ρ.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp [ht]
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  -- the sum has a real term `≥ 1/(3δ)`, everything else `≥ 0`
  have hsum_ge : 1/(3*δ) ≤ (∑ ρ' ∈ zeroDiskFinset χ t,
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ' : ℂ) / (s - ρ')).re := by
    rw [Complex.re_sum]
    have hterm : 1/(3*δ) ≤
        ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)).re := by
      have hdiff : s - ρ = ((1 + 2*δ - ρ.re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp [hsre]
        · simp [hsim, ht]
      rw [hdiff, re_natCast_div_real]
      have hm1 : 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ :=
        one_le_ord_of_mem_zeroDiskFinset hχ hρmem
      have hm1' : (1:ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) := by
        exact_mod_cast hm1
      have hx0 : 0 < 1 + 2*δ - ρ.re := by linarith
      have hx3 : 1 + 2*δ - ρ.re ≤ 3*δ := by linarith
      calc 1/(3*δ) ≤ 1/(1 + 2*δ - ρ.re) := by
            apply one_div_le_one_div_of_le hx0 hx3
        _ ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)
              / (1 + 2*δ - ρ.re) := by
            gcongr
    have hrest : ∀ ρ' ∈ zeroDiskFinset χ t,
        0 ≤ ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ' : ℂ)
          / (s - ρ')).re := by
      intro ρ' hρ'
      have hρz := (mem_zeroDiskFinset hχ).mp hρ'
      have hρre : ρ'.re < 1 := by
        by_contra hcon
        push Not at hcon
        exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hcon)
          hρz.2
      apply re_natCast_div_nonneg
      rw [Complex.sub_re, hsre]
      linarith
    calc 1/(3*δ)
        ≤ ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / (s - ρ)).re :=
          hterm
      _ ≤ ∑ ρ' ∈ zeroDiskFinset χ t,
            ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ' : ℂ)
              / (s - ρ')).re :=
          Finset.single_le_sum hrest hρmem
  have habs := Complex.abs_re_le_norm
    (deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
      - ∑ ρ' ∈ zeroDiskFinset χ t,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ' : ℂ) / (s - ρ'))
  rw [Complex.sub_re] at habs
  have h1 := abs_le.mp (le_trans habs hpf)
  rw [Complex.neg_re]
  linarith [hsum_ge, h1.1]

/-! ### §5 Helpers for the positivity core -/

/-- `(n:ℂ)^w ≠ 0` for `n ≠ 0`. -/
lemma natCast_cpow_ne_zero {n : ℕ} (hn : n ≠ 0) (w : ℂ) : ((n:ℂ)) ^ w ≠ 0 := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn)]
  exact Complex.exp_ne_zero _

/-- Conjugation of a purely-imaginary power of a natural number. -/
lemma conj_natCast_cpow_mul_I (n : ℕ) (θ : ℝ) :
    (starRingEnd ℂ) ((n:ℂ) ^ ((θ:ℂ) * I)) = (n:ℂ) ^ (-(θ:ℂ) * I) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rcases eq_or_ne θ 0 with rfl | hθ
    · norm_num
    · have h1 : ((θ:ℂ)) * I ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr hθ) Complex.I_ne_zero
      have h2 : (-(θ:ℂ)) * I ≠ 0 :=
        mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hθ)) Complex.I_ne_zero
      rw [show ((0:ℕ):ℂ) = 0 from by norm_num, Complex.zero_cpow h1,
        Complex.zero_cpow h2, map_zero]
  · have harg : ((n:ℂ)).arg ≠ Real.pi := by
      rw [show ((n:ℂ)) = (((n:ℝ)):ℂ) from by push_cast; rfl,
        Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact fun h => Real.pi_ne_zero h.symm
    have hcx : (starRingEnd ℂ) ((n:ℂ)) = (n:ℂ) := by
      exact map_natCast _ n
    have h := Complex.conj_cpow ((n:ℂ)) (-(θ:ℂ) * I) harg
    rw [hcx] at h
    have hconjexp : (starRingEnd ℂ) (-(θ:ℂ) * I) = (θ:ℂ) * I := by
      rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [hconjexp] at h
    exact h.symm

/-- `(n:ℂ)^s` is fixed by conjugation for real `s`. -/
lemma conj_natCast_cpow_ofReal (n : ℕ) (x : ℝ) :
    (starRingEnd ℂ) ((n:ℂ) ^ ((x:ℝ):ℂ)) = (n:ℂ) ^ ((x:ℝ):ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rcases eq_or_ne x 0 with rfl | hx
    · norm_num
    · have h1 : ((x:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
      rw [show ((0:ℕ):ℂ) = 0 from by norm_num, Complex.zero_cpow h1, map_zero]
  · have h1 : (n:ℂ) ^ ((x:ℝ):ℂ) = (((n:ℝ) ^ x : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n) x]
      norm_num
    rw [h1, Complex.conj_ofReal]

/-- The finite `|1 + Σ|²` expansion with denominators. -/
lemma mul_conj_expand {R : ℕ} (v : Fin R → ℂ) (a D : ℂ) :
    a * ((1 + ∑ j, v j) * (starRingEnd ℂ) (1 + ∑ j, v j)) / D
      = a / D + (∑ j, a * v j / D) + (∑ j, a * (starRingEnd ℂ) (v j) / D)
        + (∑ j, a * (v j * (starRingEnd ℂ) (v j)) / D)
        + ∑ p ∈ (univ : Finset (Fin R)).offDiag,
            a * (v p.1 * (starRingEnd ℂ) (v p.2)) / D := by
  have hconj : (starRingEnd ℂ) (1 + ∑ j, v j)
      = 1 + ∑ j, (starRingEnd ℂ) (v j) := by
    rw [map_add, map_one, map_sum]
  rw [hconj]
  have hsplit : (∑ j, v j) * (∑ j, (starRingEnd ℂ) (v j))
      = (∑ j, v j * (starRingEnd ℂ) (v j))
        + ∑ p ∈ (univ : Finset (Fin R)).offDiag,
            v p.1 * (starRingEnd ℂ) (v p.2) := by
    rw [Finset.sum_mul_sum]
    rw [← Finset.sum_product' (s := (univ : Finset (Fin R)))
      (t := (univ : Finset (Fin R)))
      (f := fun i j => v i * (starRingEnd ℂ) (v j))]
    rw [← Finset.diag_union_offDiag (univ : Finset (Fin R)),
      Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag]
  have hnum : a * ((1 + ∑ j, v j) * (1 + ∑ j, (starRingEnd ℂ) (v j)))
      = a + (∑ j, a * v j) + (∑ j, a * (starRingEnd ℂ) (v j))
        + ((∑ j, a * (v j * (starRingEnd ℂ) (v j)))
          + ∑ p ∈ (univ : Finset (Fin R)).offDiag,
              a * (v p.1 * (starRingEnd ℂ) (v p.2))) := by
    have h1 : a * ((1 + ∑ j, v j) * (1 + ∑ j, (starRingEnd ℂ) (v j)))
        = a + a * (∑ j, v j) + a * (∑ j, (starRingEnd ℂ) (v j))
          + a * ((∑ j, v j) * (∑ j, (starRingEnd ℂ) (v j))) := by ring
    rw [h1, hsplit, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
  calc a * ((1 + ∑ j, v j) * (1 + ∑ j, (starRingEnd ℂ) (v j))) / D
      = (a + (∑ j, a * v j) + (∑ j, a * (starRingEnd ℂ) (v j))
          + ((∑ j, a * (v j * (starRingEnd ℂ) (v j)))
            + ∑ p ∈ (univ : Finset (Fin R)).offDiag,
                a * (v p.1 * (starRingEnd ℂ) (v p.2)))) / D := by rw [hnum]
    _ = _ := by
        simp only [add_div, Finset.sum_div]
        ring

/-- Summability of `LSeries.term f s` from a von Mangoldt majorant on the
coefficients, at any point with `Re s = s₀`. -/
lemma summable_term_of_le {f : ℕ → ℂ} {s : ℂ} {s₀ C : ℝ} (hre : s.re = s₀)
    (h : ∀ n : ℕ, n ≠ 0 → ‖f n‖ ≤ C * vonMangoldt n)
    (hbase : Summable (fun n : ℕ => vonMangoldt n * (n:ℝ) ^ (-s₀))) :
    Summable (fun n => LSeries.term f s n) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ (hbase.mul_left C)
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, norm_zero]
    have h0 : vonMangoldt 0 = 0 := ArithmeticFunction.map_zero
    rw [h0]
    norm_num
  · rw [LSeries.term_of_ne_zero hn, norm_div,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), hre,
      div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]
    calc ‖f n‖ * (n:ℝ) ^ (-s₀)
        ≤ (C * vonMangoldt n) * (n:ℝ) ^ (-s₀) :=
          mul_le_mul_of_nonneg_right (h n hn)
            (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ = C * (vonMangoldt n * (n:ℝ) ^ (-s₀)) := by ring

/-- Real parts of a summable family are summable. -/
lemma summable_re {f : ℕ → ℂ} (hf : Summable f) :
    Summable (fun n => (f n).re) := by
  have := hf.map Complex.reCLM Complex.reCLM.continuous
  exact this.congr (fun n => rfl)

/-- Conjugation of the negative purely-imaginary power. -/
lemma conj_natCast_cpow_neg_mul_I (n : ℕ) (θ : ℝ) :
    (starRingEnd ℂ) ((n:ℂ) ^ (-(θ:ℂ) * I)) = (n:ℂ) ^ ((θ:ℂ) * I) := by
  have h := conj_natCast_cpow_mul_I n (-θ)
  rw [show (((-θ : ℝ)):ℂ) = -(θ:ℂ) from by push_cast; ring] at h
  rw [show (-(-(θ:ℂ))) = (θ:ℂ) from by ring] at h
  exact h

/-! ### §6 The positivity core: no 13 bad characters in the small regime -/

set_option maxHeartbeats 2000000 in
/-- **Landau–Page positivity core.**  There is no family of 13 pairwise-distinct
nontrivial Dirichlet characters `χ_j mod M_j` with `2 ≤ M_j ≤ Z′`, pairwise
nonprincipal products `χ_j·conj χ_k`, each carrying a zero `ρ_j` of `L(·,χ_j)`
in `[1−δ,1] × [−ν,ν]`, once `δ·log(Z′(ν+2)) ≤ 10⁻⁹` (with `0 < δ ≤ 1/40`,
`ν ≥ 1`, `Z′ ≥ 2`). -/
theorem no_thirteen_bad {Z' ν δ : ℝ} (hδ0 : 0 < δ) (hδ : δ ≤ 1/40) (hν : 1 ≤ ν)
    (hZ : 2 ≤ Z') (hsmall : δ * Real.log (Z' * (ν + 2)) ≤ 1/1000000000)
    (M : Fin 13 → ℕ) [inst : ∀ j, NeZero (M j)]
    (χ : ∀ j, DirichletCharacter ℂ (M j))
    (hM2 : ∀ j, 2 ≤ M j) (hMZ : ∀ j, (M j : ℝ) ≤ Z')
    (hne1 : ∀ j, χ j ≠ 1)
    (hprod : ∀ j k : Fin 13, j ≠ k →
      DirichletCharacter.changeLevel (dvd_mul_right (M j) (M k)) (χ j)
        * DirichletCharacter.changeLevel (dvd_mul_left (M k) (M j))
            (conjChar (χ k)) ≠ 1)
    (ρ : Fin 13 → ℂ)
    (hzero : ∀ j, DirichletCharacter.LFunction (χ j) (ρ j) = 0)
    (hre1 : ∀ j, 1 - δ ≤ (ρ j).re) (hre2 : ∀ j, (ρ j).re ≤ 1)
    (him : ∀ j, |(ρ j).im| ≤ ν) : False := by
  have hδ20 : (0:ℝ) < 2*δ := by linarith
  have hν0 : (0:ℝ) < ν + 2 := by linarith
  set 𝓛 : ℝ := Real.log (Z' * (ν + 2)) with h𝓛
  have h𝓛1 : 1 ≤ 𝓛 := by
    rw [h𝓛, Real.le_log_iff_exp_le (by nlinarith)]
    have h := Real.exp_one_lt_d9
    nlinarith
  -- the point on the real axis
  set sC : ℂ := ((1 + 2*δ : ℝ) : ℂ) with hsC
  have hsCre : sC.re = 1 + 2*δ := by rw [hsC, Complex.ofReal_re]
  have hsCre1 : 1 < sC.re := by rw [hsCre]; linarith
  -- the twisted coefficient functions and evaluation points
  set ph : Fin 13 → ℕ → ℂ := fun j n => (n : ℂ) ^ (-((ρ j).im:ℂ) * I) with hph
  set uf : Fin 13 → ℕ → ℂ :=
    fun j n => (χ j) ((n : ZMod (M j))) * ph j n with huf
  set tw : Fin 13 → ℕ → ℂ := fun j =>
    (fun n : ℕ => (χ j) ((n : ZMod (M j)))) * (fun n : ℕ => (vonMangoldt n : ℂ))
    with htw
  set Ψ : (j : Fin 13) → (k : Fin 13) → DirichletCharacter ℂ (M j * M k) :=
    fun j k => DirichletCharacter.changeLevel (dvd_mul_right (M j) (M k)) (χ j)
      * DirichletCharacter.changeLevel (dvd_mul_left (M k) (M j)) (conjChar (χ k))
    with hΨ
  set tw2 : Fin 13 → Fin 13 → ℕ → ℂ := fun j k =>
    (fun n : ℕ => (Ψ j k) ((n : ZMod (M j * M k))))
      * (fun n : ℕ => (vonMangoldt n : ℂ)) with htw2
  set spt : Fin 13 → ℂ := fun j => sC + ((ρ j).im : ℂ) * I with hspt
  set spt2 : Fin 13 → Fin 13 → ℂ :=
    fun j k => sC + (((ρ j).im - (ρ k).im : ℝ) : ℂ) * I with hspt2
  set F : ℕ → ℂ := fun n => 1 + ∑ j, uf j n with hF
  set Gc : ℕ → ℂ :=
    fun n => (vonMangoldt n : ℂ) * (F n * (starRingEnd ℂ) (F n)) with hGc
  -- elementary norm facts
  have hΛnorm : ∀ n : ℕ, ‖((vonMangoldt n : ℝ) : ℂ)‖ = vonMangoldt n := by
    intro n
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have hph_le : ∀ j n, ‖ph j n‖ ≤ 1 := by
    intro j n
    simp only [hph]
    rcases eq_or_ne n 0 with rfl | hn
    · rcases eq_or_ne (-((ρ j).im : ℂ) * I) 0 with h | h
      · rw [h, Complex.cpow_zero, norm_one]
      · rw [show ((0:ℕ):ℂ) = 0 from by norm_num, Complex.zero_cpow h, norm_zero]
        norm_num
    · rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      have hre0 : (-((ρ j).im : ℂ) * I).re = 0 := by simp
      rw [hre0, Real.rpow_zero]
  have huf_le : ∀ j n, ‖uf j n‖ ≤ 1 := by
    intro j n
    simp only [huf]
    rw [norm_mul]
    have h1 := DirichletCharacter.norm_le_one (χ j) ((n : ZMod (M j)))
    have h2 := hph_le j n
    nlinarith [norm_nonneg (ph j n), norm_nonneg ((χ j) ((n : ZMod (M j))))]
  have hF_le : ∀ n, ‖F n‖ ≤ 14 := by
    intro n
    simp only [hF]
    calc ‖1 + ∑ j, uf j n‖ ≤ ‖(1:ℂ)‖ + ‖∑ j, uf j n‖ := norm_add_le _ _
      _ ≤ 1 + ∑ j, ‖uf j n‖ := by
          rw [norm_one]
          have := norm_sum_le (univ : Finset (Fin 13)) (fun j => uf j n)
          linarith
      _ ≤ 1 + ∑ _j : Fin 13, (1:ℝ) := by
          have := Finset.sum_le_sum
            (fun j (_ : j ∈ (univ : Finset (Fin 13))) => huf_le j n)
          linarith
      _ = 14 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          norm_num
  -- base summability
  have hbase : Summable (fun n : ℕ => vonMangoldt n * (n:ℝ) ^ (-(1 + 2*δ))) :=
    summable_vonMangoldt_rpow hδ20
  -- summability of the five groups
  have hsum0 : Summable
      (fun n => LSeries.term (fun n : ℕ => (vonMangoldt n : ℂ)) sC n) := by
    refine summable_term_of_le (C := 1) hsCre (fun n _ => ?_) hbase
    rw [hΛnorm, one_mul]
  have hsptre : ∀ j, (spt j).re = 1 + 2*δ := by
    intro j
    simp only [hspt]
    rw [Complex.add_re, hsCre]
    simp
  have hspt2re : ∀ j k, (spt2 j k).re = 1 + 2*δ := by
    intro j k
    simp only [hspt2]
    rw [Complex.add_re, hsCre]
    simp
  have hsum1 : ∀ j, Summable (fun n => LSeries.term (tw j) (spt j) n) := by
    intro j
    refine summable_term_of_le (C := 1) (hsptre j) (fun n _ => ?_) hbase
    simp only [htw, Pi.mul_apply]
    rw [norm_mul, hΛnorm, one_mul]
    have h1 := DirichletCharacter.norm_le_one (χ j) ((n : ZMod (M j)))
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n),
      norm_nonneg ((χ j) ((n : ZMod (M j))))]
  have hsum2 : ∀ j, Summable
      (fun n => (starRingEnd ℂ) (LSeries.term (tw j) (spt j) n)) := by
    intro j
    exact ((hsum1 j).map (starRingEnd ℂ) Complex.continuous_conj).congr
      (fun n => rfl)
  have hsum3 : ∀ j, Summable (fun n => LSeries.term
      (fun n => (vonMangoldt n : ℂ) * (uf j n * (starRingEnd ℂ) (uf j n))) sC n) := by
    intro j
    refine summable_term_of_le (C := 1) hsCre (fun n _ => ?_) hbase
    rw [norm_mul, hΛnorm, norm_mul, RCLike.norm_conj, one_mul]
    have hsq : ‖uf j n‖ * ‖uf j n‖ ≤ 1 := by
      nlinarith [huf_le j n, norm_nonneg (uf j n)]
    calc vonMangoldt n * (‖uf j n‖ * ‖uf j n‖) ≤ vonMangoldt n * 1 :=
        mul_le_mul_of_nonneg_left hsq ArithmeticFunction.vonMangoldt_nonneg
      _ = vonMangoldt n := mul_one _
  have hsum4 : ∀ j k, Summable
      (fun n => LSeries.term (tw2 j k) (spt2 j k) n) := by
    intro j k
    refine summable_term_of_le (C := 1) (hspt2re j k) (fun n _ => ?_) hbase
    simp only [htw2, Pi.mul_apply]
    rw [norm_mul, hΛnorm, one_mul]
    have h1 := DirichletCharacter.norm_le_one (Ψ j k) ((n : ZMod (M j * M k)))
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n),
      norm_nonneg ((Ψ j k) ((n : ZMod (M j * M k))))]
  have hsumG : Summable (fun n => LSeries.term Gc sC n) := by
    refine summable_term_of_le (C := 196) hsCre (fun n _ => ?_) hbase
    simp only [hGc]
    rw [norm_mul, hΛnorm, norm_mul, RCLike.norm_conj]
    have hsq : ‖F n‖ * ‖F n‖ ≤ 196 := by
      nlinarith [hF_le n, norm_nonneg (F n)]
    calc vonMangoldt n * (‖F n‖ * ‖F n‖) ≤ vonMangoldt n * 196 :=
        mul_le_mul_of_nonneg_left hsq ArithmeticFunction.vonMangoldt_nonneg
      _ = 196 * vonMangoldt n := by ring
  -- the master pointwise expansion
  have hmaster : ∀ n : ℕ, LSeries.term Gc sC n
      = LSeries.term (fun n : ℕ => (vonMangoldt n : ℂ)) sC n
        + (∑ j, LSeries.term (tw j) (spt j) n)
        + (∑ j, (starRingEnd ℂ) (LSeries.term (tw j) (spt j) n))
        + (∑ j, LSeries.term
            (fun n => (vonMangoldt n : ℂ) * (uf j n * (starRingEnd ℂ) (uf j n))) sC n)
        + ∑ p ∈ (univ : Finset (Fin 13)).offDiag,
            LSeries.term (tw2 p.1 p.2) (spt2 p.1 p.2) n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · have hn0 : ((n:ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hg1 : ∀ j, LSeries.term (tw j) (spt j) n
          = (vonMangoldt n : ℂ) * uf j n / (n:ℂ) ^ sC := by
        intro j
        rw [LSeries.term_of_ne_zero hn]
        simp only [htw, hspt, huf, hph, Pi.mul_apply]
        rw [Complex.cpow_add _ _ hn0]
        rw [show (-((ρ j).im:ℂ) * I) = -(((ρ j).im:ℂ) * I) from by ring,
          Complex.cpow_neg]
        have hz := natCast_cpow_ne_zero hn (((ρ j).im:ℂ) * I)
        have hz2 := natCast_cpow_ne_zero hn sC
        field_simp
      have hg2 : ∀ j, (starRingEnd ℂ) (LSeries.term (tw j) (spt j) n)
          = (vonMangoldt n : ℂ) * (starRingEnd ℂ) (uf j n) / (n:ℂ) ^ sC := by
        intro j
        rw [hg1 j, map_div₀, map_mul]
        rw [show ((vonMangoldt n : ℂ)) = (((vonMangoldt n : ℝ)):ℂ) from rfl,
          Complex.conj_ofReal, hsC, conj_natCast_cpow_ofReal]
      have hg3 : ∀ j, LSeries.term
          (fun n => (vonMangoldt n : ℂ) * (uf j n * (starRingEnd ℂ) (uf j n))) sC n
          = (vonMangoldt n : ℂ) * (uf j n * (starRingEnd ℂ) (uf j n)) / (n:ℂ) ^ sC := by
        intro j
        rw [LSeries.term_of_ne_zero hn]
      have hg4 : ∀ p : Fin 13 × Fin 13,
          LSeries.term (tw2 p.1 p.2) (spt2 p.1 p.2) n
          = (vonMangoldt n : ℂ) * (uf p.1 n * (starRingEnd ℂ) (uf p.2 n))
              / (n:ℂ) ^ sC := by
        intro p
        rw [LSeries.term_of_ne_zero hn]
        simp only [htw2, hspt2, Pi.mul_apply]
        have : NeZero (M p.1 * M p.2) :=
          ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
        simp only [hΨ]
        rw [prodChar_apply (χ p.1) (χ p.2) n]
        rw [show ((((ρ p.1).im - (ρ p.2).im : ℝ)):ℂ) * I
            = ((ρ p.1).im:ℂ) * I + -(((ρ p.2).im:ℂ) * I) from by push_cast; ring]
        rw [Complex.cpow_add _ _ hn0, Complex.cpow_add _ _ hn0, Complex.cpow_neg]
        simp only [huf, hph]
        rw [map_mul]
        rw [conj_natCast_cpow_neg_mul_I]
        rw [show (-((ρ p.1).im:ℂ) * I) = -(((ρ p.1).im:ℂ) * I) from by ring,
          Complex.cpow_neg]
        have hz1 := natCast_cpow_ne_zero hn (((ρ p.1).im:ℂ) * I)
        have hz2 := natCast_cpow_ne_zero hn (((ρ p.2).im:ℂ) * I)
        have hz3 := natCast_cpow_ne_zero hn sC
        field_simp
      calc LSeries.term Gc sC n
          = (vonMangoldt n : ℂ)
              * ((1 + ∑ j, uf j n) * (starRingEnd ℂ) (1 + ∑ j, uf j n))
              / (n:ℂ) ^ sC := by
            rw [LSeries.term_of_ne_zero hn]
        _ = (vonMangoldt n : ℂ) / (n:ℂ) ^ sC
            + (∑ j, (vonMangoldt n : ℂ) * uf j n / (n:ℂ) ^ sC)
            + (∑ j, (vonMangoldt n : ℂ) * (starRingEnd ℂ) (uf j n) / (n:ℂ) ^ sC)
            + (∑ j, (vonMangoldt n : ℂ)
                * (uf j n * (starRingEnd ℂ) (uf j n)) / (n:ℂ) ^ sC)
            + ∑ p ∈ (univ : Finset (Fin 13)).offDiag,
                (vonMangoldt n : ℂ)
                  * (uf p.1 n * (starRingEnd ℂ) (uf p.2 n)) / (n:ℂ) ^ sC :=
          mul_conj_expand (fun j => uf j n) _ _
        _ = _ := by
            rw [LSeries.term_of_ne_zero hn (fun n : ℕ => (vonMangoldt n : ℂ)) sC,
              Finset.sum_congr rfl (fun j (_ : j ∈ (univ : Finset (Fin 13))) => hg1 j),
              Finset.sum_congr rfl (fun j (_ : j ∈ (univ : Finset (Fin 13))) => hg2 j),
              Finset.sum_congr rfl (fun j (_ : j ∈ (univ : Finset (Fin 13))) => hg3 j),
              Finset.sum_congr rfl
                (fun p (_ : p ∈ (univ : Finset (Fin 13)).offDiag) => hg4 p)]
  -- sum the master identity
  have hsumE1 : Summable (fun n => ∑ j, LSeries.term (tw j) (spt j) n) :=
    summable_sum (fun j _ => hsum1 j)
  have hsumE2 : Summable
      (fun n => ∑ j, (starRingEnd ℂ) (LSeries.term (tw j) (spt j) n)) :=
    summable_sum (fun j _ => hsum2 j)
  have hsumE3 : Summable (fun n => ∑ j, LSeries.term
      (fun n => (vonMangoldt n : ℂ) * (uf j n * (starRingEnd ℂ) (uf j n))) sC n) :=
    summable_sum (fun j _ => hsum3 j)
  have hsumE4 : Summable (fun n => ∑ p ∈ (univ : Finset (Fin 13)).offDiag,
      LSeries.term (tw2 p.1 p.2) (spt2 p.1 p.2) n) :=
    summable_sum (fun p _ => hsum4 p.1 p.2)
  have htsum : LSeries Gc sC
      = LSeries (fun n : ℕ => (vonMangoldt n : ℂ)) sC
        + (∑ j, LSeries (tw j) (spt j))
        + (∑ j, ∑' n, (starRingEnd ℂ) (LSeries.term (tw j) (spt j) n))
        + (∑ j, ∑' n, LSeries.term
            (fun n => (vonMangoldt n : ℂ) * (uf j n * (starRingEnd ℂ) (uf j n))) sC n)
        + ∑ p ∈ (univ : Finset (Fin 13)).offDiag,
            LSeries (tw2 p.1 p.2) (spt2 p.1 p.2) := by
    have h0 : LSeries Gc sC = ∑' n, (LSeries.term (fun n : ℕ => (vonMangoldt n : ℂ)) sC n
        + (∑ j, LSeries.term (tw j) (spt j) n)
        + (∑ j, (starRingEnd ℂ) (LSeries.term (tw j) (spt j) n))
        + (∑ j, LSeries.term
            (fun n => (vonMangoldt n : ℂ) * (uf j n * (starRingEnd ℂ) (uf j n))) sC n)
        + ∑ p ∈ (univ : Finset (Fin 13)).offDiag,
            LSeries.term (tw2 p.1 p.2) (spt2 p.1 p.2) n) := tsum_congr hmaster
    rw [h0]
    rw [Summable.tsum_add ((((hsum0.add hsumE1).add hsumE2).add hsumE3)) hsumE4]
    rw [Summable.tsum_add (((hsum0.add hsumE1).add hsumE2)) hsumE3]
    rw [Summable.tsum_add ((hsum0.add hsumE1)) hsumE2]
    rw [Summable.tsum_add hsum0 hsumE1]
    rw [Summable.tsum_finsetSum
        (f := fun (j : Fin 13) (n : ℕ) => LSeries.term (tw j) (spt j) n)
        (fun j _ => hsum1 j),
      Summable.tsum_finsetSum
        (f := fun (j : Fin 13) (n : ℕ) =>
          (starRingEnd ℂ) (LSeries.term (tw j) (spt j) n))
        (fun j _ => hsum2 j),
      Summable.tsum_finsetSum
        (f := fun (j : Fin 13) (n : ℕ) => LSeries.term
          (fun n => (vonMangoldt n : ℂ) * (uf j n * (starRingEnd ℂ) (uf j n))) sC n)
        (fun j _ => hsum3 j),
      Summable.tsum_finsetSum
        (f := fun (p : Fin 13 × Fin 13) (n : ℕ) =>
          LSeries.term (tw2 p.1 p.2) (spt2 p.1 p.2) n)
        (fun p _ => hsum4 p.1 p.2)]
    rfl
  -- positivity of the total
  have hpos : 0 ≤ (LSeries Gc sC).re := by
    have h1 : (LSeries Gc sC).re = ∑' n, (LSeries.term Gc sC n).re :=
      Complex.re_tsum hsumG
    rw [h1]
    apply tsum_nonneg
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero]
      norm_num
    · rw [LSeries.term_of_ne_zero hn]
      simp only [hGc]
      rw [Complex.mul_conj]
      have hD : (n:ℂ) ^ sC = (((n:ℝ) ^ (1+2*δ) : ℝ) : ℂ) := by
        rw [hsC, Complex.ofReal_cpow (Nat.cast_nonneg n)]
        norm_num
      rw [hD]
      rw [show ((vonMangoldt n : ℂ)) * ((Complex.normSq (F n) : ℝ):ℂ)
          / (((n:ℝ) ^ (1+2*δ) : ℝ) : ℂ)
          = (((vonMangoldt n * Complex.normSq (F n) / (n:ℝ) ^ (1+2*δ) : ℝ)) : ℂ)
          from by push_cast; ring]
      rw [Complex.ofReal_re]
      have h2 : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      have h3 := Complex.normSq_nonneg (F n)
      have h4 : (0:ℝ) ≤ (n:ℝ) ^ (1+2*δ) :=
        Real.rpow_nonneg (Nat.cast_nonneg n) _
      positivity
  -- bound the constant term
  have hbound0 : (LSeries (fun n : ℕ => (vonMangoldt n : ℂ)) sC).re
      ≤ 1/(2*δ) + 2 := by
    rw [hsC, LSeries_ofReal_eq (by linarith : (0:ℝ) < 1 + 2*δ), Complex.ofReal_re]
    exact tsum_vonMangoldt_rpow_le hδ20 (by linarith)
  -- bound the linear (gain) terms
  have hbound1 : ∀ j, (LSeries (tw j) (spt j)).re ≤ 520000 * 𝓛 - 1/(3*δ) := by
    intro j
    have := inst j
    have hsre : 1 < (spt j).re := by rw [hsptre j]; linarith
    have h1 : LSeries (tw j) (spt j)
        = -deriv (LSeries (fun n : ℕ => (χ j) ((n : ZMod (M j))))) (spt j)
          / LSeries (fun n : ℕ => (χ j) ((n : ZMod (M j)))) (spt j) := by
      simp only [htw]
      exact DirichletCharacter.LSeries_twist_vonMangoldt_eq (χ j) hsre
    have h2 : deriv (LSeries (fun n : ℕ => (χ j) ((n : ZMod (M j))))) (spt j)
        = deriv (DirichletCharacter.LFunction (χ j)) (spt j) :=
      (DirichletCharacter.deriv_LFunction_eq_deriv_LSeries (χ j) hsre).symm
    have h3 : LSeries (fun n : ℕ => (χ j) ((n : ZMod (M j)))) (spt j)
        = DirichletCharacter.LFunction (χ j) (spt j) :=
      (DirichletCharacter.LFunction_eq_LSeries (χ j) hsre).symm
    have h5 : spt j = ((1+2*δ:ℝ):ℂ) + ((ρ j).im : ℂ) * I := by
      simp only [hspt, hsC]
    rw [h1, h2, h3, neg_div, h5]
    have h4 := re_neg_logDeriv_le_of_zero (hne1 j) hδ0 hδ (hzero j)
      (hre1 j) (hre2 j)
    refine le_trans h4 ?_
    have h9 : (2:ℝ) ≤ (M j : ℝ) := by exact_mod_cast hM2 j
    have h6 : (M j : ℝ) * (|(ρ j).im| + 2) ≤ Z' * (ν + 2) := by
      have h7 := hMZ j
      have h8 := him j
      nlinarith [abs_nonneg (ρ j).im]
    have h10 : (0:ℝ) < (M j : ℝ) * (|(ρ j).im| + 2) := by
      nlinarith [abs_nonneg (ρ j).im]
    have h11 : Real.log ((M j : ℝ) * (|(ρ j).im| + 2)) ≤ 𝓛 := by
      rw [h𝓛]
      exact Real.log_le_log h10 h6
    linarith
  -- the conjugate group has the same real parts
  have hbound2 : ∀ j, (∑' n, (starRingEnd ℂ) (LSeries.term (tw j) (spt j) n)).re
      = (LSeries (tw j) (spt j)).re := by
    intro j
    have h1 : LSeries (tw j) (spt j) = ∑' n, LSeries.term (tw j) (spt j) n := rfl
    rw [h1, Complex.re_tsum (hsum2 j), Complex.re_tsum (hsum1 j)]
    apply tsum_congr
    intro n
    exact Complex.conj_re _
  -- bound the diagonal terms
  have hbound3 : ∀ j, (∑' n, LSeries.term
      (fun n => (vonMangoldt n : ℂ) * (uf j n * (starRingEnd ℂ) (uf j n))) sC n).re
      ≤ 1/(2*δ) + 2 := by
    intro j
    rw [Complex.re_tsum (hsum3 j)]
    have hle : ∀ n : ℕ, (LSeries.term
        (fun n => (vonMangoldt n : ℂ) * (uf j n * (starRingEnd ℂ) (uf j n))) sC n).re
        ≤ vonMangoldt n * (n:ℝ) ^ (-(1+2*δ)) := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [LSeries.term_zero]
        have h0 : vonMangoldt 0 = 0 := ArithmeticFunction.map_zero
        rw [h0]
        norm_num
      · rw [LSeries.term_of_ne_zero hn, Complex.mul_conj]
        have hD : (n:ℂ) ^ sC = (((n:ℝ) ^ (1+2*δ) : ℝ) : ℂ) := by
          rw [hsC, Complex.ofReal_cpow (Nat.cast_nonneg n)]
          norm_num
        rw [hD]
        rw [show ((vonMangoldt n : ℂ)) * ((Complex.normSq (uf j n) : ℝ):ℂ)
            / (((n:ℝ) ^ (1+2*δ) : ℝ) : ℂ)
            = (((vonMangoldt n * Complex.normSq (uf j n) / (n:ℝ) ^ (1+2*δ) : ℝ)) : ℂ)
            from by push_cast; ring]
        rw [Complex.ofReal_re]
        have h1 : Complex.normSq (uf j n) ≤ 1 := by
          rw [Complex.normSq_eq_norm_sq]
          have := huf_le j n
          nlinarith [norm_nonneg (uf j n)]
        have h2 : (0:ℝ) ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
        have h3 : (0:ℝ) < (n:ℝ) ^ (1+2*δ) :=
          Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) _
        have h4 : vonMangoldt n * Complex.normSq (uf j n) / (n:ℝ) ^ (1+2*δ)
            ≤ vonMangoldt n / (n:ℝ) ^ (1+2*δ) := by
          have hnum : vonMangoldt n * Complex.normSq (uf j n) ≤ vonMangoldt n := by
            nlinarith [Complex.normSq_nonneg (uf j n)]
          exact div_le_div_of_nonneg_right hnum h3.le
        have h5 : vonMangoldt n / (n:ℝ) ^ (1+2*δ)
            = vonMangoldt n * (n:ℝ) ^ (-(1+2*δ)) := by
          rw [Real.rpow_neg (Nat.cast_nonneg n)]
          ring
        linarith [h4, h5.le, h5.ge]
    calc ∑' n, (LSeries.term
        (fun n => (vonMangoldt n : ℂ) * (uf j n * (starRingEnd ℂ) (uf j n))) sC n).re
        ≤ ∑' n, vonMangoldt n * (n:ℝ) ^ (-(1+2*δ)) :=
          (summable_re (hsum3 j)).tsum_le_tsum hle hbase
      _ ≤ 1/(2*δ) + 2 := tsum_vonMangoldt_rpow_le hδ20 (by linarith)
  -- bound the cross terms
  have hbound4 : ∀ p ∈ (univ : Finset (Fin 13)).offDiag,
      (LSeries (tw2 p.1 p.2) (spt2 p.1 p.2)).re ≤ 2 * (520000 * 𝓛) := by
    intro p hp
    have hpne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    have : NeZero (M p.1 * M p.2) :=
      ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
    have hΨne1 : Ψ p.1 p.2 ≠ 1 := by
      simp only [hΨ]
      exact hprod p.1 p.2 hpne
    have hsre : 1 < (spt2 p.1 p.2).re := by rw [hspt2re p.1 p.2]; linarith
    have h1 : LSeries (tw2 p.1 p.2) (spt2 p.1 p.2)
        = -deriv (LSeries (fun n : ℕ => (Ψ p.1 p.2) ((n : ZMod (M p.1 * M p.2)))))
              (spt2 p.1 p.2)
          / LSeries (fun n : ℕ => (Ψ p.1 p.2) ((n : ZMod (M p.1 * M p.2))))
              (spt2 p.1 p.2) := by
      simp only [htw2]
      exact DirichletCharacter.LSeries_twist_vonMangoldt_eq (Ψ p.1 p.2) hsre
    have h2 : deriv (LSeries (fun n : ℕ => (Ψ p.1 p.2) ((n : ZMod (M p.1 * M p.2)))))
          (spt2 p.1 p.2)
        = deriv (DirichletCharacter.LFunction (Ψ p.1 p.2)) (spt2 p.1 p.2) :=
      (DirichletCharacter.deriv_LFunction_eq_deriv_LSeries (Ψ p.1 p.2) hsre).symm
    have h3 : LSeries (fun n : ℕ => (Ψ p.1 p.2) ((n : ZMod (M p.1 * M p.2))))
          (spt2 p.1 p.2)
        = DirichletCharacter.LFunction (Ψ p.1 p.2) (spt2 p.1 p.2) :=
      (DirichletCharacter.LFunction_eq_LSeries (Ψ p.1 p.2) hsre).symm
    have h5 : spt2 p.1 p.2
        = ((1+2*δ:ℝ):ℂ) + (((ρ p.1).im - (ρ p.2).im : ℝ) : ℂ) * I := by
      simp only [hspt2, hsC]
    rw [h1, h2, h3, neg_div, h5]
    have h4 := re_neg_logDeriv_le hΨne1 ((ρ p.1).im - (ρ p.2).im)
      (a := 2*δ) hδ20 (by linarith)
    refine le_trans h4 ?_
    -- log bound: `(M₁M₂)(|γ₁−γ₂|+2) ≤ (Z′(ν+2))²`
    have h9a : (2:ℝ) ≤ (M p.1 : ℝ) := by exact_mod_cast hM2 p.1
    have h9b : (2:ℝ) ≤ (M p.2 : ℝ) := by exact_mod_cast hM2 p.2
    have habs : |(ρ p.1).im - (ρ p.2).im| ≤ 2*ν := by
      have := abs_sub ((ρ p.1).im) ((ρ p.2).im)
      have := him p.1
      have := him p.2
      linarith [abs_sub ((ρ p.1).im) ((ρ p.2).im)]
    have hcast : ((M p.1 * M p.2 : ℕ) : ℝ) = (M p.1 : ℝ) * (M p.2 : ℝ) := by
      push_cast
      ring
    have h6 : ((M p.1 * M p.2 : ℕ) : ℝ) * (|(ρ p.1).im - (ρ p.2).im| + 2)
        ≤ (Z' * (ν + 2))^2 := by
      rw [hcast]
      have h7a := hMZ p.1
      have h7b := hMZ p.2
      have habs0 : (0:ℝ) ≤ |(ρ p.1).im - (ρ p.2).im| := abs_nonneg _
      have s1 : (M p.1 : ℝ) * (M p.2 : ℝ) ≤ Z' * Z' := by nlinarith
      have s2 : |(ρ p.1).im - (ρ p.2).im| + 2 ≤ 2*ν + 2 := by linarith
      have s3 : (M p.1 : ℝ) * (M p.2 : ℝ) * (|(ρ p.1).im - (ρ p.2).im| + 2)
          ≤ (Z' * Z') * (2*ν + 2) :=
        mul_le_mul s1 s2 (by linarith) (by nlinarith)
      have s5 : (0:ℝ) ≤ Z' * Z' * (ν*ν + 2*ν + 2) := by positivity
      nlinarith [s3, s5]
    have h10 : (0:ℝ) < ((M p.1 * M p.2 : ℕ) : ℝ) * (|(ρ p.1).im - (ρ p.2).im| + 2) := by
      rw [hcast]
      nlinarith [abs_nonneg ((ρ p.1).im - (ρ p.2).im)]
    have h11 : Real.log (((M p.1 * M p.2 : ℕ) : ℝ)
        * (|(ρ p.1).im - (ρ p.2).im| + 2)) ≤ 2 * 𝓛 := by
      calc Real.log (((M p.1 * M p.2 : ℕ) : ℝ) * (|(ρ p.1).im - (ρ p.2).im| + 2))
          ≤ Real.log ((Z' * (ν + 2))^2) := Real.log_le_log h10 h6
        _ = 2 * 𝓛 := by
            rw [Real.log_pow, h𝓛]
            push_cast
            ring
    linarith
  -- assemble the real-part inequality
  have hre_eq : (LSeries Gc sC).re
      = (LSeries (fun n : ℕ => (vonMangoldt n : ℂ)) sC).re
        + (∑ j, (LSeries (tw j) (spt j)).re)
        + (∑ j, (∑' n, (starRingEnd ℂ) (LSeries.term (tw j) (spt j) n)).re)
        + (∑ j, (∑' n, LSeries.term
            (fun n => (vonMangoldt n : ℂ)
              * (uf j n * (starRingEnd ℂ) (uf j n))) sC n).re)
        + ∑ p ∈ (univ : Finset (Fin 13)).offDiag,
            (LSeries (tw2 p.1 p.2) (spt2 p.1 p.2)).re := by
    rw [htsum]
    rw [Complex.add_re, Complex.add_re, Complex.add_re, Complex.add_re,
      Complex.re_sum, Complex.re_sum, Complex.re_sum, Complex.re_sum]
  -- final numeric contradiction
  have hcard : ((univ : Finset (Fin 13)).offDiag).card = 156 := by
    rw [Finset.offDiag_card, Finset.card_univ, Fintype.card_fin]
  have hsum_b1 : (∑ j, (LSeries (tw j) (spt j)).re)
      ≤ 13 * (520000 * 𝓛 - 1/(3*δ)) := by
    calc (∑ j, (LSeries (tw j) (spt j)).re)
        ≤ ∑ _j : Fin 13, (520000 * 𝓛 - 1/(3*δ)) :=
          Finset.sum_le_sum (fun j _ => hbound1 j)
      _ = 13 * (520000 * 𝓛 - 1/(3*δ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
  have hsum_b2 : (∑ j, (∑' n, (starRingEnd ℂ) (LSeries.term (tw j) (spt j) n)).re)
      ≤ 13 * (520000 * 𝓛 - 1/(3*δ)) := by
    calc (∑ j, (∑' n, (starRingEnd ℂ) (LSeries.term (tw j) (spt j) n)).re)
        = ∑ j, (LSeries (tw j) (spt j)).re :=
          Finset.sum_congr rfl (fun j _ => hbound2 j)
      _ ≤ 13 * (520000 * 𝓛 - 1/(3*δ)) := hsum_b1
  have hsum_b3 : (∑ j, (∑' n, LSeries.term
      (fun n => (vonMangoldt n : ℂ) * (uf j n * (starRingEnd ℂ) (uf j n))) sC n).re)
      ≤ 13 * (1/(2*δ) + 2) := by
    calc (∑ j, (∑' n, LSeries.term
        (fun n => (vonMangoldt n : ℂ) * (uf j n * (starRingEnd ℂ) (uf j n))) sC n).re)
        ≤ ∑ _j : Fin 13, (1/(2*δ) + 2) :=
          Finset.sum_le_sum (fun j _ => hbound3 j)
      _ = 13 * (1/(2*δ) + 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
  have hsum_b4 : (∑ p ∈ (univ : Finset (Fin 13)).offDiag,
      (LSeries (tw2 p.1 p.2) (spt2 p.1 p.2)).re) ≤ 156 * (2 * (520000 * 𝓛)) := by
    calc (∑ p ∈ (univ : Finset (Fin 13)).offDiag,
        (LSeries (tw2 p.1 p.2) (spt2 p.1 p.2)).re)
        ≤ ∑ _p ∈ (univ : Finset (Fin 13)).offDiag, (2 * (520000 * 𝓛)) :=
          Finset.sum_le_sum hbound4
      _ = 156 * (2 * (520000 * 𝓛)) := by
          rw [Finset.sum_const, hcard]
          ring
  have hfinal : (0:ℝ) ≤ (1/(2*δ) + 2) + 13 * (520000 * 𝓛 - 1/(3*δ))
      + 13 * (520000 * 𝓛 - 1/(3*δ)) + 13 * (1/(2*δ) + 2)
      + 156 * (2 * (520000 * 𝓛)) := by
    rw [hre_eq] at hpos
    linarith [hbound0, hsum_b1, hsum_b2, hsum_b3, hsum_b4]
  -- multiply through by `δ > 0` and contradict
  have hmul : (0:ℝ) ≤ δ * ((1/(2*δ) + 2) + 13 * (520000 * 𝓛 - 1/(3*δ))
      + 13 * (520000 * 𝓛 - 1/(3*δ)) + 13 * (1/(2*δ) + 2)
      + 156 * (2 * (520000 * 𝓛))) := mul_nonneg hδ0.le hfinal
  have hexp : δ * ((1/(2*δ) + 2) + 13 * (520000 * 𝓛 - 1/(3*δ))
      + 13 * (520000 * 𝓛 - 1/(3*δ)) + 13 * (1/(2*δ) + 2)
      + 156 * (2 * (520000 * 𝓛)))
      = 7 + 28 * δ + 175760000 * (δ * 𝓛) - 26/3 := by
    field_simp
    ring
  rw [hexp] at hmul
  -- `δ𝓛 ≤ 10⁻⁹`, `δ ≤ 1/40`: RHS `< 0`, contradiction
  linarith [hsmall, hδ]

/-! ### §7 The census -/

/-- The bad primitive characters mod `d`: primitive with at least one zero of
`L(·,χ)` in the box `[σ,1] × [−ν,ν]` (junk value `∅` at `d = 0`). -/
def badChars (σ ν : ℝ) (d : ℕ) : Finset (DirichletCharacter ℂ d) :=
  if h : d = 0 then ∅ else
    haveI : NeZero d := ⟨h⟩
    ((univ : Finset (DirichletCharacter ℂ d)).filter
      (fun χ => χ.IsPrimitive ∧ (zeroFinset χ σ ν).Nonempty))

lemma mem_badChars {σ ν : ℝ} {d : ℕ} [NeZero d] {χ : DirichletCharacter ℂ d} :
    χ ∈ badChars σ ν d ↔ χ.IsPrimitive ∧ (zeroFinset χ σ ν).Nonempty := by
  rw [badChars, dif_neg (NeZero.ne d)]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The census count**: the number of pairs `(d′, χ)` with `1 ≤ d′ ≤ K`,
`χ` primitive mod `d′`, and `L(·,χ)` vanishing somewhere in
`[σ,1] × [−ν,ν]` (multiplicity-one version of the Z7 contract). -/
def censusCount (σ ν : ℝ) (K : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 K, (badChars σ ν d).card

/-- **Small regime** `(1−σ)·log(Z(ν+2)) ≤ 10⁻⁹`: the census is at most 13
(Landau–Page positivity; 12 characters of modulus ≥ 2, plus possibly the
modulus-1 character = ζ). Unconditional. -/
theorem censusCount_le_of_small {σ ν Z : ℝ} (hσ : 39/40 ≤ σ) (_hσ1 : σ ≤ 1)
    (hν : 1 ≤ ν) (hZ : 2 ≤ Z)
    (hsmall : (1 - σ) * Real.log (Z * (ν + 2)) ≤ 1/1000000000) :
    censusCount σ ν ⌊Z⌋₊ ≤ 13 := by
  set K : ℕ := ⌊Z⌋₊ with hK
  have hK2 : 2 ≤ K := by
    rw [hK]
    exact_mod_cast Nat.le_floor (by exact_mod_cast hZ : ((2:ℕ):ℝ) ≤ Z)
  set 𝓛 : ℝ := Real.log (Z * (ν + 2)) with h𝓛
  have hν0 : (0:ℝ) < ν + 2 := by linarith
  have h𝓛1 : 1 ≤ 𝓛 := by
    rw [h𝓛, Real.le_log_iff_exp_le (by nlinarith)]
    have h := Real.exp_one_lt_d9
    nlinarith
  have h𝓛0 : 0 < 𝓛 := by linarith
  -- the working width
  set δc : ℝ := min (1/40) ((1/1000000000)/𝓛) with hδc
  have hδc0 : 0 < δc := by
    rw [hδc]
    apply lt_min (by norm_num)
    positivity
  have hδc40 : δc ≤ 1/40 := min_le_left _ _
  have hδcL : δc * 𝓛 ≤ 1/1000000000 := by
    have h1 : δc ≤ (1/1000000000)/𝓛 := min_le_right _ _
    calc δc * 𝓛 ≤ ((1/1000000000)/𝓛) * 𝓛 := by
          exact mul_le_mul_of_nonneg_right h1 h𝓛0.le
      _ = 1/1000000000 := by field_simp
  have hσδ : 1 - σ ≤ δc := by
    rw [hδc]
    apply le_min (by linarith)
    rw [le_div_iff₀ h𝓛0]
    linarith [hsmall]
  -- decompose the census: `d = 1` plus the tail
  have hIcc : Finset.Icc 1 K = insert 1 (Finset.Icc 2 K) := by
    ext a
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have h1notin : (1:ℕ) ∉ Finset.Icc 2 K := by
    simp only [Finset.mem_Icc]
    omega
  have hdecomp : censusCount σ ν K
      = (badChars σ ν 1).card + ∑ d ∈ Finset.Icc 2 K, (badChars σ ν d).card := by
    rw [censusCount, hIcc, Finset.sum_insert h1notin]
  -- the `d = 1` term is at most 1
  have hone : (badChars σ ν 1).card ≤ 1 := by
    have h1 : (badChars σ ν 1).card ≤ (univ : Finset (DirichletCharacter ℂ 1)).card := by
      rw [badChars, dif_neg (by norm_num : (1:ℕ) ≠ 0)]
      exact Finset.card_filter_le _ _
    have h2 : (univ : Finset (DirichletCharacter ℂ 1)).card = 1 := by
      have h3 := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ 1
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h3, Nat.totient_one]
    omega
  -- the tail is at most 12
  have htail : ∑ d ∈ Finset.Icc 2 K, (badChars σ ν d).card ≤ 12 := by
    by_contra hcon
    push Not at hcon
    have h13 : 13 ≤ ∑ d ∈ Finset.Icc 2 K, (badChars σ ν d).card := hcon
    -- package as a sigma Finset and extract 13 members
    set S : Finset ((d : ℕ) × DirichletCharacter ℂ d) :=
      (Finset.Icc 2 K).sigma (fun d => badChars σ ν d) with hS
    have hScard : 13 ≤ S.card := by
      rw [hS, Finset.card_sigma]
      exact h13
    obtain ⟨S', hS'sub, hS'card⟩ := Finset.exists_subset_card_eq hScard
    let e : Fin 13 ≃ ↥S' := (finCongr hS'card.symm).trans S'.equivFin.symm
    set idx : Fin 13 → ((d : ℕ) × DirichletCharacter ℂ d) :=
      fun i => ((e i) : ((d : ℕ) × DirichletCharacter ℂ d)) with hidx
    have hidx_inj : Function.Injective idx := by
      intro i j hij
      exact e.injective (Subtype.ext hij)
    have hidx_mem : ∀ i, idx i ∈ S := fun i => hS'sub (e i).2
    -- unpack the family
    set Mf : Fin 13 → ℕ := fun i => (idx i).1 with hMf
    set χf : (i : Fin 13) → DirichletCharacter ℂ (Mf i) := fun i => (idx i).2 with hχf
    have hMf2 : ∀ i, 2 ≤ Mf i := by
      intro i
      have := (Finset.mem_sigma.mp (hidx_mem i)).1
      exact (Finset.mem_Icc.mp this).1
    have hMfne : ∀ i, NeZero (Mf i) := fun i => ⟨by have := hMf2 i; omega⟩
    have hMfK : ∀ i, Mf i ≤ K := by
      intro i
      have := (Finset.mem_sigma.mp (hidx_mem i)).1
      exact (Finset.mem_Icc.mp this).2
    have hMfZ : ∀ i, (Mf i : ℝ) ≤ Z := by
      intro i
      calc (Mf i : ℝ) ≤ (K : ℝ) := by exact_mod_cast hMfK i
        _ ≤ Z := by rw [hK]; exact Nat.floor_le (by linarith)
    have hbad : ∀ i, (χf i).IsPrimitive ∧ (zeroFinset (χf i) σ ν).Nonempty := by
      intro i
      have := (Finset.mem_sigma.mp (hidx_mem i)).2
      exact mem_badChars.mp this
    -- the zeros
    have hzf : ∀ i, ∃ z : ℂ, z ∈ zeroFinset (χf i) σ ν := by
      intro i
      obtain ⟨z, hz⟩ := (hbad i).2
      exact ⟨z, hz⟩
    set ρf : Fin 13 → ℂ := fun i => (hzf i).choose with hρf
    have hρf_mem : ∀ i, ρf i ∈ zeroFinset (χf i) σ ν := fun i => (hzf i).choose_spec
    have hρf_prop : ∀ i, σ ≤ (ρf i).re ∧ (ρf i).re ≤ 1 ∧ |(ρf i).im| ≤ ν
        ∧ ρf i ≠ 1 ∧ DirichletCharacter.LFunction (χf i) (ρf i) = 0 := by
      intro i
      exact mem_zeroFinset.mp (hρf_mem i)
    -- distinctness of the products
    have hprod : ∀ i j : Fin 13, i ≠ j →
        DirichletCharacter.changeLevel (dvd_mul_right (Mf i) (Mf j)) (χf i)
          * DirichletCharacter.changeLevel (dvd_mul_left (Mf j) (Mf i))
              (conjChar (χf j)) ≠ 1 := by
      intro i j hij
      apply prodChar_ne_one (hbad i).1 (hbad j).1
      intro hEq
      apply hij
      apply hidx_inj
      calc idx i = ⟨Mf i, χf i⟩ := rfl
        _ = ⟨Mf j, χf j⟩ := hEq
        _ = idx j := rfl
    -- nontriviality
    have hne1 : ∀ i, χf i ≠ 1 := fun i => prim_ne_one (hMf2 i) (hbad i).1
    -- contradiction via the positivity core
    exact no_thirteen_bad hδc0 hδc40 hν hZ hδcL Mf χf hMf2 hMfZ hne1 hprod ρf
      (fun i => (hρf_prop i).2.2.2.2)
      (fun i => by linarith [(hρf_prop i).1, hσδ])
      (fun i => (hρf_prop i).2.1)
      (fun i => (hρf_prop i).2.2.1)
  omega

/-- **Trivial regime**: the census is at most `K²` (there are at most `d`
characters mod `d`). Unconditional. -/
theorem censusCount_le_sq (σ ν : ℝ) (K : ℕ) : censusCount σ ν K ≤ K * K := by
  have hstep : ∀ d ∈ Finset.Icc 1 K, (badChars σ ν d).card ≤ K := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdK : d ≤ K := (Finset.mem_Icc.mp hd).2
    have : NeZero d := ⟨by omega⟩
    have h1 : (badChars σ ν d).card ≤ (univ : Finset (DirichletCharacter ℂ d)).card := by
      rw [badChars, dif_neg (NeZero.ne d)]
      exact Finset.card_filter_le _ _
    have h2 : (univ : Finset (DirichletCharacter ℂ d)).card = d.totient := by
      have h3 := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ d
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card, h3]
    have h4 := Nat.totient_le d
    omega
  calc censusCount σ ν K = ∑ d ∈ Finset.Icc 1 K, (badChars σ ν d).card := rfl
    _ ≤ ∑ _d ∈ Finset.Icc 1 K, K := Finset.sum_le_sum hstep
    _ = (Finset.Icc 1 K).card * K := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ K * K := by
        have h5 : (Finset.Icc 1 K).card ≤ K := by
          rw [Nat.card_Icc]
          omega
        exact Nat.mul_le_mul_right K h5

/-! ### §8 The Z7 contract -/

/-- The census constant `c₂(ν) := 10^{10⁹}·(ν+2)`.  The ledger requires only
that `c₂` be absolute in `x` (its size is harmless downstream: it enters
`D = ⌈c₂·e^{(191/900)·c₃·ρ}⌉` only); the astronomical numeral is what lets the
middle-regime machine's constant `e^{κ·C₆ + C₂/(3A)}` fit under `c₂` outright.
WARNING: never unfold this def under `norm_num`/`nlinarith`/`positivity`/
`decide` — the kernel would evaluate the `10^{10⁹}` numeral (a ~415 MB
integer).  Compare against it only through monotonicity lemmas. -/
def censusC₂ (ν : ℝ) : ℝ := (10:ℝ) ^ (1000000000 : ℕ) * (ν + 2)

/-- The census exponent `c₃ := 10¹²` (any explicit numeral is admissible per
the Z0a ledger; the trivial regime needs `c₃(1−σ) ≥ 2` on its range, and the
free choice here fixes the middle-regime window to `1−σ < 2·10⁻¹²`, which
forces `log(Z·(ν+2)) > 500` in-window and thereby deletes all small-parameter
inputs from the middle-regime machine). -/
def censusC₃ : ℝ := 10 ^ 12

/-- **The middle-regime census hypothesis** — the single unproved analytic
input of this file.  It is the genuinely log-free zero census aggregated over
conductors (Gallagher's method with Turán power sums; explicit-constant form:
Thorner–Zaman, arXiv:2208.11123, with maximal loss-taking), restricted to the
window where neither the Landau–Page positivity argument (which needs
`(1−σ)·log(Z(ν+2)) ≤ 10⁻⁹`) nor the trivial count (which needs
`1−σ ≥ 2/c₃`) applies.  Everything else in this file is unconditional;
`census_contract` consumes exactly this hypothesis.  Note the downstream
consumption point of the Z0a ledger (`σ = 1 − ρ/log x`, `Z = x^{191/900}`,
`x → ∞`) sits in this window, so discharging `MidCensusHyp` is the remaining
content of sortie Z7. -/
def MidCensusHyp : Prop :=
  ∀ σ ν Z : ℝ, 39/40 ≤ σ → σ ≤ 1 → 1 ≤ ν → 2 ≤ Z →
    1 - σ < 2/censusC₃ →
    1/1000000000 < (1 - σ) * Real.log (Z * (ν + 2)) →
    (censusCount σ ν ⌊Z⌋₊ : ℝ) ≤ censusC₂ ν * Z ^ (censusC₃ * (1 - σ))

/-- **THE Z7 CONTRACT** (routez/Z0a-ledger.md §7, character-count form):
for `σ ∈ [39/40, 1]`, `ν ≥ 1`, `Z ≥ 2`,
`∑_{d′ ≤ Z} #{χ mod d′ primitive with a zero in [σ,1]×[−ν,ν]}
  ≤ c₂(ν)·Z^{c₃(1−σ)}`,
conditional on the middle-regime hypothesis `MidCensusHyp`. -/
theorem census_contract (hmid : MidCensusHyp) {σ ν Z : ℝ}
    (hσ : 39/40 ≤ σ) (hσ1 : σ ≤ 1) (hν : 1 ≤ ν) (hZ : 2 ≤ Z) :
    (censusCount σ ν ⌊Z⌋₊ : ℝ) ≤ censusC₂ ν * Z ^ (censusC₃ * (1 - σ)) := by
  have hZ1 : (1:ℝ) ≤ Z := by linarith
  have hexp0 : 0 ≤ censusC₃ * (1 - σ) := by
    rw [censusC₃]
    nlinarith
  have hrpow1 : (1:ℝ) ≤ Z ^ (censusC₃ * (1 - σ)) := by
    have h1 : Z ^ (0:ℝ) ≤ Z ^ (censusC₃ * (1 - σ)) :=
      Real.rpow_le_rpow_of_exponent_le hZ1 hexp0
    rwa [Real.rpow_zero] at h1
  have hc2_13 : (13:ℝ) ≤ censusC₂ ν := by
    have h10 : (13:ℝ) ≤ (10:ℝ) ^ (1000000000 : ℕ) :=
      le_trans (by norm_num : (13:ℝ) ≤ (10:ℝ) ^ (2:ℕ))
        (pow_le_pow_right₀ (by norm_num) (by norm_num))
    have hν2 : (1:ℝ) ≤ ν + 2 := by linarith
    calc (13:ℝ) ≤ (10:ℝ) ^ (1000000000 : ℕ) * 1 := by rw [mul_one]; exact h10
      _ ≤ (10:ℝ) ^ (1000000000 : ℕ) * (ν + 2) :=
          mul_le_mul_of_nonneg_left hν2 (pow_nonneg (by norm_num) _)
      _ = censusC₂ ν := by rw [censusC₂]
  by_cases hsm : (1 - σ) * Real.log (Z * (ν + 2)) ≤ 1/1000000000
  · -- small regime: Landau–Page positivity
    have h13 := censusCount_le_of_small hσ hσ1 hν hZ hsm
    have h13' : (censusCount σ ν ⌊Z⌋₊ : ℝ) ≤ 13 := by exact_mod_cast h13
    calc (censusCount σ ν ⌊Z⌋₊ : ℝ) ≤ 13 := h13'
      _ = 13 * 1 := by ring
      _ ≤ censusC₂ ν * Z ^ (censusC₃ * (1 - σ)) := by
          apply mul_le_mul hc2_13 hrpow1 (by norm_num) (by linarith)
  · push Not at hsm
    by_cases htriv : 2/censusC₃ ≤ 1 - σ
    · -- trivial regime: at most `Z²` characters in total
      have h1 : censusCount σ ν ⌊Z⌋₊ ≤ ⌊Z⌋₊ * ⌊Z⌋₊ := censusCount_le_sq σ ν ⌊Z⌋₊
      have hfl : (⌊Z⌋₊:ℝ) ≤ Z := Nat.floor_le (by linarith)
      have hfl0 : (0:ℝ) ≤ (⌊Z⌋₊:ℝ) := Nat.cast_nonneg _
      have h2 : (censusCount σ ν ⌊Z⌋₊ : ℝ) ≤ Z * Z := by
        have h3 : (censusCount σ ν ⌊Z⌋₊ : ℝ) ≤ (⌊Z⌋₊:ℝ) * (⌊Z⌋₊:ℝ) := by
          exact_mod_cast h1
        nlinarith
      have h4 : Z * Z = Z ^ ((2:ℕ):ℝ) := by
        rw [Real.rpow_natCast]
        ring
      have h5 : Z ^ ((2:ℕ):ℝ) ≤ Z ^ (censusC₃ * (1 - σ)) := by
        apply Real.rpow_le_rpow_of_exponent_le hZ1
        rw [censusC₃] at htriv ⊢
        rw [show (((2:ℕ):ℝ)) = 2 from by norm_num]
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10 ^ 12)] at htriv
        linarith
      have h6 : (1:ℝ) ≤ censusC₂ ν := by linarith
      calc (censusCount σ ν ⌊Z⌋₊ : ℝ) ≤ Z * Z := h2
        _ = Z ^ ((2:ℕ):ℝ) := h4
        _ ≤ Z ^ (censusC₃ * (1 - σ)) := h5
        _ = 1 * Z ^ (censusC₃ * (1 - σ)) := by ring
        _ ≤ censusC₂ ν * Z ^ (censusC₃ * (1 - σ)) := by
            apply mul_le_mul_of_nonneg_right h6 (by linarith)
    · push Not at htriv
      exact hmid σ ν Z hσ hσ1 hν hZ htriv hsm

/-- **The 𝓓(x) consumption shape** (Z0a ledger §3.4): any set `D` of
conductors in `[2, Z]`, each carrying a primitive character with a zero in
`[σ,1] × [−ν,ν]`, has size at most `c₂(ν)·Z^{c₃(1−σ)}`. -/
theorem card_badConductors_le (hmid : MidCensusHyp) {σ ν Z : ℝ}
    (hσ : 39/40 ≤ σ) (hσ1 : σ ≤ 1) (hν : 1 ≤ ν) (hZ : 2 ≤ Z)
    (D : Finset ℕ)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ (d:ℝ) ≤ Z ∧ (badChars σ ν d).Nonempty) :
    (D.card : ℝ) ≤ censusC₂ ν * Z ^ (censusC₃ * (1 - σ)) := by
  have hsub : D ⊆ Finset.Icc 1 ⌊Z⌋₊ := by
    intro d hd
    obtain ⟨h2, hZd, _⟩ := hD d hd
    rw [Finset.mem_Icc]
    exact ⟨by omega, Nat.le_floor hZd⟩
  have h1 : D.card ≤ censusCount σ ν ⌊Z⌋₊ := by
    calc D.card = ∑ _d ∈ D, 1 := by rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ d ∈ D, (badChars σ ν d).card :=
          Finset.sum_le_sum (fun d hd => Finset.card_pos.mpr (hD d hd).2.2)
      _ ≤ ∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, (badChars σ ν d).card :=
          Finset.sum_le_sum_of_subset hsub
      _ = censusCount σ ν ⌊Z⌋₊ := rfl
  calc (D.card : ℝ) ≤ (censusCount σ ν ⌊Z⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ censusC₂ ν * Z ^ (censusC₃ * (1 - σ)) :=
      census_contract hmid hσ hσ1 hν hZ

end

end Census
