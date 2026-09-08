/-
Route Z, TZ-LITE File 3: zero mass in `η`-scale disks touching the 1-line.

MAIN RESULT:

* `sum_ord_smallDisk_le` — for nontrivial `χ mod N`, every `τ : ℝ` and every
  radius `0 < w ≤ 1/20`, the total multiplicity of the zeros of `L(·,χ)` in
  the closed `w`-disk around `1 + iτ` is at most
    `5 + 2400000·w·log(N(|τ|+2))`.

PROOF SHAPE (Z7-tzlite §3.3): evaluate the Landau partial-fraction expansion
`norm_logDeriv_sub_sum_zeroDiskFinset_le` (constant `C₆ = 520000`) at
`s₀ = (1+w) + iτ`.  Every disk zero contributes a nonnegative real part to
`∑_ρ m_ρ/(s₀−ρ)`, and every zero inside the `w`-disk of `1+iτ` contributes at
least `m_ρ/(4w)` (numerator `Re(s₀−ρ) ≥ w`, modulus `‖s₀−ρ‖ ≤ 2w`).  On the
other side `‖L′/L(s₀)‖ = ‖LSeries(χ·Λ)(s₀)‖ ≤ ∑ Λ(n)n^{−(1+w)} ≤ 1/w + 2`
(`Census.tsum_vonMangoldt_rpow_le`, the source of `w ≤ 1/20`).  Multiplying
by `4w`: mass `≤ 4 + 8w + 2080000·w·log(N(|τ|+2))`, which the frozen
coefficient `2400000` covers with 15% headroom.

Consumed by TZ-LITE File 4 (`KDerivDetect.lean`) at radius `w = 2η`.
-/
import Carmichael.PartialFractions
import Carmichael.Census
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option autoImplicit false

open Complex Finset Metric
open ArithmeticFunction (vonMangoldt)
open scoped Classical

namespace Carmichael

noncomputable section

/-! ### Elementary complex-arithmetic helpers -/

/-- Lower bound for `Re((m:ℂ)/z)` when `z` has real part at least `w` and
squared modulus at most `4w²`: the disk-zero contribution `m/(4w)`. -/
lemma re_natCast_div_ge {m : ℕ} {z : ℂ} {w : ℝ} (hw : 0 < w)
    (hre : w ≤ z.re) (hns : Complex.normSq z ≤ 4 * w ^ 2) :
    (m : ℝ) / (4 * w) ≤ ((m : ℂ) / z).re := by
  have hns0 : 0 < Complex.normSq z := by
    have h1 : Complex.normSq z = z.re * z.re + z.im * z.im := Complex.normSq_apply z
    nlinarith [sq_nonneg z.im, sq_nonneg z.re]
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  rw [div_le_div_iff₀ (by positivity) hns0]
  have ha : (m : ℝ) * Complex.normSq z ≤ (m : ℝ) * (4 * w ^ 2) :=
    mul_le_mul_of_nonneg_left hns hm
  have hb : (m : ℝ) * w ≤ (m : ℝ) * z.re := mul_le_mul_of_nonneg_left hre hm
  nlinarith [ha, hb, hw]

/-- `‖z‖ ≤ r` gives `normSq z ≤ r²`. -/
lemma normSq_le_of_norm_le {z : ℂ} {r : ℝ} (h : ‖z‖ ≤ r) :
    Complex.normSq z ≤ r ^ 2 := by
  have h0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have h1 : Complex.normSq z = ‖z‖ ^ 2 := (Complex.normSq_eq_norm_sq z)
  nlinarith

/-! ### The Dirichlet-series bound on `‖L′/L‖` at `Re s = 1 + w` -/

section Series

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
/-- Termwise bound for the twisted von Mangoldt L-series. -/
lemma norm_term_twist_le (χ : DirichletCharacter ℂ N) {s : ℂ} {x : ℝ}
    (hre : s.re = x) (n : ℕ) :
    ‖LSeries.term ((fun n : ℕ => χ ((n : ZMod N)))
        * (fun n : ℕ => (vonMangoldt n : ℂ))) s n‖
      ≤ vonMangoldt n * (n : ℝ) ^ (-x) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, norm_zero,
      show vonMangoldt 0 = 0 from ArithmeticFunction.map_zero]
    simp
  · rw [LSeries.term_of_ne_zero hn, norm_div,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), hre,
      div_eq_mul_inv, ← Real.rpow_neg (Nat.cast_nonneg n)]
    refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    simp only [Pi.mul_apply]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have h1 := DirichletCharacter.norm_le_one χ ((n : ZMod N))
    nlinarith [ArithmeticFunction.vonMangoldt_nonneg (n := n),
      norm_nonneg (χ ((n : ZMod N)))]

/-- **`‖L′/L‖ ≤ 1/w + 2` on the line `Re s = 1 + w`**, `0 < w ≤ 1/20`.
The Dirichlet-series side of the small-disk count. -/
lemma norm_logDeriv_le_of_re_eq {χ : DirichletCharacter ℂ N} {w : ℝ}
    (hw0 : 0 < w) (hw : w ≤ 1/20) {s : ℂ} (hsre : s.re = 1 + w) :
    ‖deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖
      ≤ 1/w + 2 := by
  have hsre1 : 1 < s.re := by rw [hsre]; linarith
  set twf : ℕ → ℂ := (fun n : ℕ => χ ((n : ZMod N)))
    * (fun n : ℕ => (vonMangoldt n : ℂ)) with htwf
  -- the twisted series computes `−L′/L`
  have h1 : LSeries twf s
      = -deriv (LSeries (fun n : ℕ => χ ((n : ZMod N)))) s
        / LSeries (fun n : ℕ => χ ((n : ZMod N))) s := by
    simp only [htwf]
    exact DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hsre1
  have h2 : deriv (LSeries (fun n : ℕ => χ ((n : ZMod N)))) s
      = deriv (DirichletCharacter.LFunction χ) s :=
    (DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hsre1).symm
  have h3 : LSeries (fun n : ℕ => χ ((n : ZMod N))) s
      = DirichletCharacter.LFunction χ s :=
    (DirichletCharacter.LFunction_eq_LSeries χ hsre1).symm
  have hEq : deriv (DirichletCharacter.LFunction χ) s
      / DirichletCharacter.LFunction χ s = -LSeries twf s := by
    rw [h1, h2, h3, neg_div, neg_neg]
  rw [hEq, norm_neg]
  -- comparison with `∑ Λ(n) n^{−(1+w)}`
  have hbase : Summable (fun n : ℕ => vonMangoldt n * (n : ℝ) ^ (-(1 + w))) :=
    Census.summable_vonMangoldt_rpow hw0
  have hterm := norm_term_twist_le χ (x := 1 + w) hsre
  have hsummN : Summable (fun n : ℕ => ‖LSeries.term twf s n‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hbase
    exact hterm n
  calc ‖LSeries twf s‖ = ‖∑' n : ℕ, LSeries.term twf s n‖ := by rw [LSeries]
    _ ≤ ∑' n : ℕ, ‖LSeries.term twf s n‖ := norm_tsum_le_tsum_norm hsummN
    _ ≤ ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-(1 + w)) :=
        hsummN.tsum_le_tsum hterm hbase
    _ ≤ 1/w + 2 := Census.tsum_vonMangoldt_rpow_le hw0 hw

end Series

/-! ### The small-disk zero count -/

open Complex Finset Metric Carmichael in
/-- Zero mass of `L(·,χ)` in the closed `w`-disk around `1 + iτ`:
at most `5 + 2400000·w·log(N(|τ|+2))` counting multiplicity, for
`0 < w ≤ 1/20`.  (True coefficient 2080000 = 4·C₆; 15% headroom.) -/
theorem sum_ord_smallDisk_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (τ : ℝ)
    {w : ℝ} (hw0 : 0 < w) (hw : w ≤ 1/20) :
    ((∑ ρ ∈ (zeroDiskFinset χ τ).filter
        (fun ρ => dist ρ (1 + τ * Complex.I) ≤ w),
      analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℕ) : ℝ)
      ≤ 5 + 2400000 * w * Real.log (N * (|τ| + 2)) := by
  -- the evaluation point `s₀ = (1+w) + iτ`
  have hs₀re : (((1 + w : ℝ) : ℂ) + τ * I).re = 1 + w := by simp
  -- the size parameter and its logarithm
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hX2 : (2 : ℝ) ≤ (N : ℝ) * (|τ| + 2) := by nlinarith [abs_nonneg τ]
  have hlog0 : 0 ≤ Real.log ((N : ℝ) * (|τ| + 2)) := Real.log_nonneg (by linarith)
  -- `s₀` lies in the Landau `3/2`-disk and is not a zero
  have hmem : ((1 + w : ℝ) : ℂ) + τ * I ∈ closedBall ((2 : ℂ) + τ * I) (3/2 : ℝ) := by
    rw [mem_closedBall, Complex.dist_eq]
    have hdiff : ((1 + w : ℝ) : ℂ) + τ * I - ((2 : ℂ) + τ * I) = ((1 + w - 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hL0 : DirichletCharacter.LFunction χ (((1 + w : ℝ) : ℂ) + τ * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by rw [hs₀re]; linarith)
  have hpf := norm_logDeriv_sub_sum_zeroDiskFinset_le hχ τ hmem hL0
  -- every disk zero has real part `< 1`
  have hzre : ∀ ρ ∈ zeroDiskFinset χ τ, ρ.re < 1 := by
    intro ρ hρ
    by_contra hcon
    push Not at hcon
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hcon)
      ((mem_zeroDiskFinset hχ).mp hρ).2
  -- every disk zero contributes a nonnegative real part
  have hnonneg : ∀ ρ ∈ zeroDiskFinset χ τ,
      0 ≤ ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
        / (((1 + w : ℝ) : ℂ) + τ * I - ρ)).re := by
    intro ρ hρ
    apply Census.re_natCast_div_nonneg
    rw [Complex.sub_re, hs₀re]
    linarith [hzre ρ hρ]
  -- zeros inside the `w`-disk of `1 + iτ` contribute at least `m/(4w)`
  have hstrong : ∀ ρ ∈ (zeroDiskFinset χ τ).filter
        (fun ρ => dist ρ (1 + τ * Complex.I) ≤ w),
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ) / (4 * w)
        ≤ ((analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
            / (((1 + w : ℝ) : ℂ) + τ * I - ρ)).re := by
    intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨hρD, hρd⟩ := hρ
    refine re_natCast_div_ge hw0 ?_ ?_
    · rw [Complex.sub_re, hs₀re]
      linarith [hzre ρ hρD]
    · have hdd : ((1 + w : ℝ) : ℂ) + τ * I - ρ
          = ((w : ℝ) : ℂ) + ((1 + (τ : ℂ) * Complex.I) - ρ) := by
        push_cast; ring
      have hin : ‖(1 + (τ : ℂ) * Complex.I) - ρ‖ ≤ w := by
        rw [norm_sub_rev, ← Complex.dist_eq]
        exact hρd
      have hnorm : ‖((1 + w : ℝ) : ℂ) + τ * I - ρ‖ ≤ 2 * w := by
        rw [hdd]
        refine le_trans (norm_add_le _ _) ?_
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
        linarith
      have h3 := normSq_le_of_norm_le hnorm
      nlinarith [h3]
  -- chain: filtered mass / (4w) ≤ Re of the full partial-fraction sum
  have hchain : (∑ ρ ∈ (zeroDiskFinset χ τ).filter
        (fun ρ => dist ρ (1 + τ * Complex.I) ≤ w),
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) / (4 * w)
      ≤ (∑ ρ ∈ zeroDiskFinset χ τ,
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
            / (((1 + w : ℝ) : ℂ) + τ * I - ρ)).re := by
    rw [Finset.sum_div, Complex.re_sum]
    refine le_trans (Finset.sum_le_sum hstrong) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun ρ hρ _ => hnonneg ρ hρ)
  -- the analytic upper bound on that real part
  have hPFside : (∑ ρ ∈ zeroDiskFinset χ τ,
      (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
        / (((1 + w : ℝ) : ℂ) + τ * I - ρ)).re
      ≤ (1/w + 2) + 520000 * Real.log ((N : ℝ) * (|τ| + 2)) := by
    have hnormLD := norm_logDeriv_le_of_re_eq (χ := χ) hw0 hw hs₀re
    have habs := Complex.abs_re_le_norm
      (deriv (DirichletCharacter.LFunction χ) (((1 + w : ℝ) : ℂ) + τ * I)
          / DirichletCharacter.LFunction χ (((1 + w : ℝ) : ℂ) + τ * I)
        - ∑ ρ ∈ zeroDiskFinset χ τ,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ)
              / (((1 + w : ℝ) : ℂ) + τ * I - ρ))
    rw [Complex.sub_re] at habs
    have h1 := abs_le.mp (le_trans habs hpf)
    have h2 := abs_le.mp (Complex.abs_re_le_norm
      (deriv (DirichletCharacter.LFunction χ) (((1 + w : ℝ) : ℂ) + τ * I)
        / DirichletCharacter.LFunction χ (((1 + w : ℝ) : ℂ) + τ * I)))
    linarith [h1.1, h2.2]
  -- multiply by `4w` and round
  have hmass := le_trans hchain hPFside
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * w)] at hmass
  push_cast
  have hwinv : w * (1/w) = 1 := by field_simp
  nlinarith [hmass, hlog0, hw0, hw, hwinv]

end

end Carmichael
