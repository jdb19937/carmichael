/-
Route Z, sortie Z6c′: discharging the interface hypotheses of the zero detector.
Blueprint: routez/Z0b-density.md §2 (I8, I9), §4 (Lemmas 4.1–4.3, Prop. 4.4),
§12.3 (frozen Z6c statement).  Consumes `Carmichael.Detector` (Z6c) and
`Carmichael.LGrowth`/`Carmichael.LConvexity` (Z4a′).

DELIVERED (fully proved, no sorry/axioms):

* I8(b) (`norm_Gamma_le_exp_neg_im`): `‖Γ(z)‖ ≤ 60·e^{−|Im z|}` on the strip
  `0 ≤ Re z ≤ 1`, `|Im z| ≥ 1/2`.  Explicit constant `CΓ' = 60`.  Route: the
  LGrowth reflection/Phragmén–Lindelöf strip bound
  `‖Γ(1−s)·sin(π(s+a)/2)‖ ≤ 3(2+‖s‖)` divided by the sine lower bound
  `‖sin w‖ ≥ |sinh (Im w)|` (mid-strip constant `30`,
  `norm_Gamma_le_exp_neg_im_mid`), then one `Γ(z) = Γ(z+1)/z` shift.  (Pinned
  Mathlib has no complex Stirling; none is needed.)
* I9(b) (`P1_lower_log`, `P1_lower`): `(1/2)·(φ(N)/N)·log R ≤ P(1)`, in the
  `Rpar` form `(1/200)·(φ(N)/N)·log D ≤ P1 N (Rpar D)` demanded by
  `Detector.detector_lower_bound`.  No `R ≥ R₀` threshold is needed.
* I9(c) replacement (`sum_totient_div_sq_le_P1`): `Φ_R ≤ P(1)`.  See DELTA 1.
* Z6c-Q (blueprint §12.3), the sifted arithmetic factor `Q_R = φ(q_R)/q_R` with
  `q_R = ∏_{p ∣ N, p ≤ R} p`: `P1_lower_log_QR` (`(1/2)·Q_R·log R ≤ P(1)`),
  `P1_lower_QR` (its `Rpar` corollary `(1/200)·Q_R·log D ≤ P(1)`) and
  `P1_le_QR_mul_MertensProd` (`P(1) ≤ Q_R·∏_{p ≤ R}(1 − 1/p)⁻¹`).  The
  structural key is `coprime_qR_iff`: every `r ≤ R` has all its prime factors
  `≤ R`, so `(r,N) = 1 ↔ (r,q_R) = 1` and both sums are the old ones read at
  the modulus `q_R`.  `φ(N)/N ≤ Q_R` is `totient_div_le_QR`, so the `φ(N)/N`
  forms above are corollaries.
* Blueprint Lemma 4.3 in the corrected form (`norm_Epole_le'`): the pole term
  is `≤ P(1)/8` at height `≥ Λ₀`, proved from `Φ_R ≤ P(1)` instead of I9(c);
  the frozen `Λ₀` (i.e. `C₆ = log(3200·e·CΓ')`) is unchanged.
* `detector_lower_bound_of_P1` and `detector_lower_bound_uncond`: blueprint
  Proposition 4.4 with I8(b), I9(b), I9(c) all discharged — the frozen
  conclusion `(1/400)·(φ(d)/d)·log D ≤ ‖F(ρ,χ)‖` under the frozen range
  hypotheses and the frozen `Λ₀`-clause, with `CΓ' = 60` substituted.

DELTAS vs the blueprint:

1. **I9(c) AS FROZEN IS FALSE** and is *not* delivered.  Blueprint §2 I9(c) /
   Lemma 3.4(b) claim `Φ_R := ∑'_{r ≤ R, (r,d)=1} μ²(r)φ(r)/r²
   ≤ (π²/6)(φ(d)/d)(1+log R)`.
   Counterexample: `d = 30030 = 2·3·5·7·11·13`, `log D = 200`, so
   `R = D^{1/100} = e² = 7.389…`; the only squarefree `r ≤ 7` coprime to `d`
   is `r = 1`, so `Φ_R = 1`, while the right-hand side is
   `(π²/6)·(5760/30030)·3 = 0.946535… < 1`.  The failure is not an edge case:
   for `d = ∏_{p ≤ R} p` the right-hand side tends to `(π²/6)e^{−γ} = 0.9236…`
   while `Φ_R = 1` (already `< 1` at `log R = 20`).  The blueprint's own proof
   sketch removes only the primes `p ∣ d` with `p ≤ R` from the Euler product,
   which is `∏_{p∣d, p≤R}(1−1/p)`, not `φ(d)/d`; the primes `p ∣ d` with
   `p > R` shrink the right-hand side without shrinking `Φ_R`.
   DELIVERED INSTEAD: the trivial `Φ_R ≤ P(1)` (from `φ(r) ≤ r`), which is
   *stronger where it is used*: in Lemma 4.3 the `P(1)` cancels against the
   target `P(1)/8`, so the pole bound no longer needs I9(b) at all and the
   surviving numeric demand is `8(1 + (63/100)𝓛) ≤ 3200·e·𝓛`, satisfied at
   `𝓛 ≥ 200` with a factor `> 10⁵` of slack.  Consequence: `Λ₀` and every
   downstream statement are UNCHANGED; only the (false) intermediate I9(c)
   disappears.  `Detector.detector_lower_bound` is therefore *bypassed*, not
   used: its final assembly (triangle inequality) is reproved here from
   `norm_Epole_le'`.  Blueprint §12.3's own dependency list for the frozen
   Z6c statement names I8 and I9(b,d) only — I9(c) entered solely through the
   chain in Lemma 3.4(d), which this file replaces.
2. `detector_lower_bound_uncond` still carries the `hdet : DetectionEstimate …`
   hypothesis (blueprint Lemmas 4.1 + 4.2, the Mellin rectangle shift).  That
   is `Detector.lean`'s header delta 1 and is NOT discharged here; it is the
   only remaining input.  Pinned Mathlib has `Analysis/MellinInversion.lean`
   but no residue calculus on rectangles (PNT+'s `ResidueCalcOnRectangles` is
   the crib named by the blueprint), and Lemma 4.2 additionally consumes I8(d)
   (the weighted Γ line moment), which is not delivered either.
3. Threshold `200 ≤ log D` as in `Detector.lean` (blueprint D₀ clause (v) says
   `100 ≤ log D`; the blueprint's D₀ is far larger anyway).
-/
import Carmichael.Detector
import Carmichael.LConvexity

set_option autoImplicit false

namespace Carmichael

open Complex Finset
open scoped Real

namespace Detector

/-! ### I8(b): Γ-decay on the strip `0 ≤ Re z ≤ 1` -/

/-- From `A² ≤ B²` and `0 ≤ B` conclude `A ≤ B`. -/
private lemma le_of_sq_le_sq'' {A B : ℝ} (hB : 0 ≤ B) (h : A ^ 2 ≤ B ^ 2) : A ≤ B := by
  nlinarith

/-- Lower bound for the complex sine: `‖sin w‖ ≥ |sinh (Im w)|`.
(`‖sin w‖² = sin²(Re w) + sinh²(Im w)`.) -/
lemma abs_sinh_im_le_norm_sin (w : ℂ) : |Real.sinh w.im| ≤ ‖Complex.sin w‖ := by
  have hsq : Real.sinh w.im ^ 2 ≤ ‖Complex.sin w‖ ^ 2 := by
    have hre : (Complex.sin w).re = Real.sin w.re * Real.cosh w.im := by
      rw [Complex.sin_eq]
      simp [Complex.add_re, Complex.mul_re, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
        ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
    have him : (Complex.sin w).im = Real.cos w.re * Real.sinh w.im := by
      rw [Complex.sin_eq]
      simp [Complex.add_im, Complex.mul_im, ← Complex.ofReal_sin, ← Complex.ofReal_cosh,
        ← Complex.ofReal_cos, ← Complex.ofReal_sinh]
    have hn : ‖Complex.sin w‖ ^ 2 = (Complex.sin w).re ^ 2 + (Complex.sin w).im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [hn, hre, him]
    have hpyth : Real.sin w.re ^ 2 + Real.cos w.re ^ 2 = 1 := Real.sin_sq_add_cos_sq _
    have hcosh : Real.sinh w.im ^ 2 ≤ Real.cosh w.im ^ 2 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq w.im]
    nlinarith [sq_nonneg (Real.sin w.re), sq_nonneg (Real.cos w.re),
      sq_nonneg (Real.sinh w.im)]
  exact le_of_sq_le_sq'' (norm_nonneg _) (by rwa [sq_abs])


/-- **I8(b) on the middle strip**: `‖Γ(z)‖ ≤ 30·e^{−|Im z|}` for
`1/2 ≤ Re z ≤ 3/2` and `|Im z| ≥ 1/2`. -/
lemma norm_Gamma_le_exp_neg_im_mid {z : ℂ} (h1 : 1/2 ≤ z.re) (h2 : z.re ≤ 3/2)
    (hy : 1/2 ≤ |z.im|) : ‖Complex.Gamma z‖ ≤ 30 * Real.exp (-|z.im|) := by
  set u : ℝ := |z.im| with hu
  have hu0 : (1:ℝ)/2 ≤ u := hy
  -- the LGrowth reflection/Phragmén–Lindelöf strip bound at `s = 1 − z`
  have hs1 : -(1/2 : ℝ) ≤ (1 - z).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hs2 : (1 - z).re ≤ 1/2 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hstrip := Carmichael.norm_Gamma_one_sub_mul_sin_le 0 hs1 hs2
  rw [show (1 : ℂ) - (1 - z) = z from by ring] at hstrip
  -- the sine factor is at least `sinh (π u / 2)`
  set w : ℂ := (↑π * ((1 - z) + ↑(0:ℝ)) / 2) with hwdef
  have him : |w.im| = π * u / 2 := by
    have h : w = ((π/2 : ℝ) : ℂ) * (1 - z) := by rw [hwdef]; push_cast; ring
    rw [h, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      Complex.one_im, zero_mul, add_zero, zero_sub, abs_mul, abs_neg,
      abs_of_pos (by positivity : (0:ℝ) < π/2), ← hu]
    ring
  have hsinlow : Real.sinh (π * u / 2) ≤ ‖Complex.sin w‖ := by
    have h := abs_sinh_im_le_norm_sin w
    rwa [Real.abs_sinh, him] at h
  -- the right-hand side
  have hnorm1z : ‖1 - z‖ ≤ 1/2 + u := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : |(1 - z).re| ≤ 1/2 := by
      rw [Complex.sub_re, Complex.one_re, abs_le]; constructor <;> linarith
    have him2 : |(1 - z).im| = u := by
      rw [Complex.sub_im, Complex.one_im, zero_sub, abs_neg, hu]
    linarith [him2.le, him2.ge]
  -- assemble: `‖Γ(z)‖·sinh(πu/2) ≤ 3(5/2 + u)`
  have hΓ0 : (0:ℝ) ≤ ‖Complex.Gamma z‖ := norm_nonneg _
  have hkey : ‖Complex.Gamma z‖ * Real.sinh (π * u / 2) ≤ 3 * (5/2 + u) := by
    calc ‖Complex.Gamma z‖ * Real.sinh (π * u / 2)
        ≤ ‖Complex.Gamma z‖ * ‖Complex.sin w‖ :=
          mul_le_mul_of_nonneg_left hsinlow hΓ0
      _ = ‖Complex.Gamma z * Complex.sin w‖ := (norm_mul _ _).symm
      _ ≤ 3 * (2 + ‖1 - z‖) := hstrip
      _ ≤ 3 * (5/2 + u) := by linarith
  -- `sinh(3u/2) ≥ (1/4)·e^{3u/2}` for `u ≥ 1/2`
  have hpi : (3:ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hmono : Real.sinh (3 * u / 2) ≤ Real.sinh (π * u / 2) :=
    Real.sinh_le_sinh.mpr (by nlinarith)
  have hE0 : (0:ℝ) < Real.exp (3 * u / 2) := Real.exp_pos _
  have hlow : (1/4 : ℝ) * Real.exp (3 * u / 2) ≤ Real.sinh (3 * u / 2) := by
    rw [Real.sinh_eq]
    have h1 : Real.exp (-(3 * u / 2)) = (Real.exp (3 * u / 2))⁻¹ := Real.exp_neg _
    have h2 : (2:ℝ) ≤ Real.exp (3 * u) := by
      have ha : (3:ℝ)/2 ≤ 3 * u := by linarith
      have hb : Real.exp (3/2 : ℝ) ≤ Real.exp (3 * u) := Real.exp_le_exp.mpr ha
      have hc : (1:ℝ) + 3/2 ≤ Real.exp (3/2 : ℝ) := by
        have := Real.add_one_le_exp (3/2 : ℝ); linarith
      linarith
    have h3 : Real.exp (3 * u) = Real.exp (3 * u / 2) * Real.exp (3 * u / 2) := by
      rw [← Real.exp_add]; ring_nf
    have hinv : (Real.exp (3 * u / 2))⁻¹ ≤ (1:ℝ)/2 * Real.exp (3 * u / 2) := by
      rw [inv_le_iff_one_le_mul₀ hE0]
      nlinarith
    rw [h1]; linarith
  have hexpsplit : Real.exp (3 * u / 2) = Real.exp u * Real.exp (u/2) := by
    rw [← Real.exp_add]; ring_nf
  have hhalf : (1:ℝ) + u/2 ≤ Real.exp (u/2) := by
    have := Real.add_one_le_exp (u/2); linarith
  have hEu : (0:ℝ) < Real.exp u := Real.exp_pos _
  -- conclude `‖Γ(z)‖·e^{u} ≤ 30`
  have hfinal : ‖Complex.Gamma z‖ * Real.exp u ≤ 30 := by
    have h1 : ‖Complex.Gamma z‖ * ((1/4 : ℝ) * (Real.exp u * (1 + u/2)))
        ≤ 3 * (5/2 + u) := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hΓ0) hkey
      calc (1/4 : ℝ) * (Real.exp u * (1 + u/2))
          ≤ (1/4 : ℝ) * (Real.exp u * Real.exp (u/2)) := by
            have : Real.exp u * (1 + u/2) ≤ Real.exp u * Real.exp (u/2) :=
              mul_le_mul_of_nonneg_left hhalf hEu.le
            linarith
        _ = (1/4 : ℝ) * Real.exp (3 * u / 2) := by rw [hexpsplit]
        _ ≤ Real.sinh (3 * u / 2) := hlow
        _ ≤ Real.sinh (π * u / 2) := hmono
    nlinarith [mul_nonneg hΓ0 hEu.le]
  calc ‖Complex.Gamma z‖ = (‖Complex.Gamma z‖ * Real.exp u) * (Real.exp u)⁻¹ := by
        field_simp
    _ ≤ 30 * (Real.exp u)⁻¹ := mul_le_mul_of_nonneg_right hfinal (by positivity)
    _ = 30 * Real.exp (-u) := by rw [Real.exp_neg]

/-- **Blueprint interface I8(b)**, with explicit constant `CΓ' = 60`:
`‖Γ(z)‖ ≤ 60·e^{−|Im z|}` on the strip `0 ≤ Re z ≤ 1` for `|Im z| ≥ 1/2`.
This is the form consumed by `Detector.norm_Epole_le` / `detector_lower_bound`
(the `hGamma` argument).  Proved from the reflection/Phragmén–Lindelöf strip
bound of `Carmichael.LGrowth` plus one `Γ(z) = Γ(z+1)/z` shift; no complex
Stirling is used. -/
theorem norm_Gamma_le_exp_neg_im (z : ℂ) (h0 : 0 ≤ z.re) (h1 : z.re ≤ 1)
    (hy : 1/2 ≤ |z.im|) : ‖Complex.Gamma z‖ ≤ 60 * Real.exp (-|z.im|) := by
  have hexp : (0:ℝ) < Real.exp (-|z.im|) := Real.exp_pos _
  rcases le_or_gt (1/2 : ℝ) z.re with hhalf | hhalf
  · have := norm_Gamma_le_exp_neg_im_mid hhalf (by linarith) hy
    linarith
  · -- shift: `Γ(z) = Γ(z+1)/z`
    have hz0 : z ≠ 0 := by
      intro h
      rw [h] at hy
      simp at hy
      linarith
    have hzn : ‖z‖ ≠ 0 := by simpa using hz0
    have hshift : Complex.Gamma (z + 1) = z * Complex.Gamma z :=
      Complex.Gamma_add_one z hz0
    have hre1 : (1/2 : ℝ) ≤ (z + 1).re := by
      rw [Complex.add_re, Complex.one_re]; linarith
    have hre2 : (z + 1).re ≤ 3/2 := by
      rw [Complex.add_re, Complex.one_re]; linarith
    have him : (z + 1).im = z.im := by rw [Complex.add_im, Complex.one_im, add_zero]
    have hmid : ‖Complex.Gamma (z + 1)‖ ≤ 30 * Real.exp (-|z.im|) := by
      have := norm_Gamma_le_exp_neg_im_mid hre1 hre2 (by rwa [him])
      rwa [him] at this
    have hznorm : (1/2 : ℝ) ≤ ‖z‖ := le_trans hy (Complex.abs_im_le_norm z)
    have hprod : ‖z‖ * ‖Complex.Gamma z‖ ≤ 30 * Real.exp (-|z.im|) := by
      rw [← norm_mul, ← hshift]; exact hmid
    have hG0 : (0:ℝ) ≤ ‖Complex.Gamma z‖ := norm_nonneg _
    nlinarith

/-! ### I9(c): the frozen form is FALSE; the replacement `Φ_R ≤ P(1)`

Blueprint §2 I9(c) asserts
`Φ_R := ∑'_{r ≤ R, (r,d)=1} μ²(r)φ(r)/r² ≤ (π²/6)·(φ(d)/d)·(1 + log R)`.
This is false: take `d = 30030 = 2·3·5·7·11·13` and `log D = 200`, so
`R = D^{1/100} = e² = 7.389…` and `⌊R⌋ = 7`.  Every squarefree `r ≤ 7` other
than `r = 1` has a prime factor in `{2,3,5,7}`, all of which divide `d`, so
`Rset d R = {1}` and `Φ_R = φ(1)/1 = 1`.  The right-hand side is
`(π²/6)·(5760/30030)·(1 + 2) = 1.644934…·0.1918081…·3 = 0.946545… < 1`.

The blueprint's own sketch only removes the primes `p ∣ d` with `p ≤ R` from
the Euler product, i.e. produces `∏_{p ∣ d, p ≤ R}(1 − 1/p)`, which is not
`φ(d)/d`; the two differ by exactly the primes `p ∣ d` with `p > R`, and those
are the ones that make the claim fail.

What Lemma 4.3 actually needs is an upper bound for `Φ_R` against `P(1)`, and
the trivial `φ(r) ≤ r` supplies one that is *stronger where it is used*: see
`norm_Epole_le'`. -/

/-- **I9(c) replacement**: `Φ_R ≤ P(1)`, from `φ(r) ≤ r`. -/
theorem sum_totient_div_sq_le_P1 (N : ℕ) (R : ℝ) :
    ∑ r ∈ Rset N R, (r.totient : ℝ) / (r : ℝ) ^ 2 ≤ P1 N R := by
  refine Finset.sum_le_sum fun r hr => ?_
  obtain ⟨⟨hr1, -⟩, -, -⟩ := mem_Rset.mp hr
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
  have hφ : (r.totient : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.totient_le r
  have hrne : (r : ℝ) ≠ 0 := ne_of_gt hrR
  calc (r.totient : ℝ) / (r : ℝ) ^ 2 ≤ (r : ℝ) / (r : ℝ) ^ 2 := by
        gcongr
    _ = (r : ℝ)⁻¹ := by field_simp

/-! ### Blueprint Lemma 4.3 in its corrected form -/

set_option maxHeartbeats 2000000 in
/-- **Blueprint Lemma 4.3, corrected** (pole term small at height `≥ Λ₀`).
Identical statement to `Detector.norm_Epole_le`, but proved from the true
`Φ_R ≤ P(1)` (`sum_totient_div_sq_le_P1`) instead of the false I9(c); as a
consequence it needs neither I9(b) (`hP1`) nor I9(c) (`hPhi`).  The frozen
`Λ₀`, i.e. `C₆ = log(3200·e·CΓ')`, is unchanged (the argument leaves a factor
`400·e·L/(1 + (63/100)L) ≥ 10⁵` of slack). -/
theorem norm_Epole_le' {N : ℕ} [NeZero N] {D σ : ℝ} (hD1 : 1 < D)
    (hL : 200 ≤ Real.log D) (hσ1 : σ ≤ 1) (hσ0 : 0 ≤ σ)
    {CΓ' : ℝ} (hCΓ' : 1 ≤ CΓ')
    (hGamma : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1/2 ≤ |z.im| →
      ‖Complex.Gamma z‖ ≤ CΓ' * Real.exp (-|z.im|))
    {ρ : ℂ} (hβ : σ ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hγ : Lambda0 D σ (Real.log (3200 * Real.exp 1 * CΓ')) ≤ |ρ.im|) :
    ‖Epole (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖
      ≤ P1 N (Rpar D) / 8 := by
  have hD0 : (0 : ℝ) < D := by linarith
  set L := Real.log D with hLdef
  have hL0 : (0 : ℝ) < L := by rw [hLdef]; linarith
  set lam := (1 - σ) * L with hlamdef
  have hlam0 : 0 ≤ lam := by
    rw [hlamdef]
    have : 0 ≤ 1 - σ := by linarith
    positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have := Nat.pos_of_ne_zero (NeZero.ne N)
    exact_mod_cast this
  have hφ0 : (0 : ℝ) ≤ (N.totient : ℝ) / N := by positivity
  have hφ1 : (N.totient : ℝ) / N ≤ 1 := by
    rw [div_le_one hNpos]
    exact_mod_cast Nat.totient_le N
  have hP0 : (0 : ℝ) ≤ P1 N (Rpar D) := P1_nonneg N (Rpar D)
  -- parameter facts
  have hz1pos : 0 < z1par D := Real.rpow_pos_of_pos hD0 _
  have hz12 : z1par D < z2par D := by
    rw [z1par, z2par]
    exact Real.rpow_lt_rpow_of_exponent_lt hD1 (by norm_num)
  have hz2ge1 : 1 ≤ z2par D := by
    rw [z2par]
    calc (1 : ℝ) = D ^ (0 : ℝ) := (Real.rpow_zero D).symm
      _ ≤ D ^ (63/100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by norm_num)
  have hlogz2 : Real.log (z2par D) = 63 / 100 * L := by
    rw [z2par, Real.log_rpow hD0]
  -- Γ factor
  have hΓ : ‖Complex.Gamma (1 - ρ)‖ ≤ CΓ' * Real.exp (-|ρ.im|) := by
    have him : |(1 - ρ).im| = |ρ.im| := by
      simp [Complex.sub_im, Complex.one_im]
    have hC6pos : (0 : ℝ) ≤ Real.log (3200 * Real.exp 1 * CΓ') := by
      refine Real.log_nonneg ?_
      have := Real.exp_pos (1 : ℝ)
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    have hloglog : (1 : ℝ) ≤ Real.log L := by
      rw [Real.le_log_iff_exp_le hL0]
      have := Real.exp_one_lt_d9
      linarith
    have him2 : 1/2 ≤ |ρ.im| := by
      have h1 : Real.log (Real.log D) + (6/5) * ((1 - σ) * Real.log D)
          + Real.log (3200 * Real.exp 1 * CΓ') ≤ |ρ.im| := hγ
      have h2 : 0 ≤ (6/5) * ((1 - σ) * Real.log D) := by
        rw [← hLdef]
        rw [show (6/5) * ((1 - σ) * L) = (6/5) * lam from by rw [hlamdef]]
        positivity
      rw [← hLdef] at h1
      linarith
    have := hGamma (1 - ρ) (by simp [Complex.sub_re]; linarith)
      (by simp [Complex.sub_re]; linarith) (by rwa [him])
    rwa [him] at this
  -- X factor
  have hXpos : 0 < Xpar D := Real.rpow_pos_of_pos hD0 _
  have hXnorm : ‖((Xpar D : ℝ) : ℂ) ^ ((1 : ℂ) - ρ)‖ ≤ Real.exp (6/5 * lam) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    have hre : ((1 : ℂ) - ρ).re = 1 - ρ.re := by simp [Complex.sub_re]
    rw [hre]
    have hX1 : 1 ≤ Xpar D := by
      rw [Xpar]
      calc (1 : ℝ) = D ^ (0 : ℝ) := (Real.rpow_zero D).symm
        _ ≤ D ^ (6/5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by norm_num)
    calc Xpar D ^ (1 - ρ.re) ≤ Xpar D ^ (1 - σ) :=
          Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
      _ = Real.exp (6/5 * lam) := by
          rw [Xpar, ← Real.rpow_mul hD0.le, Real.rpow_def_of_pos hD0]
          congr 1
          rw [hlamdef, ← hLdef]
          ring
  -- the `M_r` sum, via 3.4(d)-summed and `Φ_R ≤ P(1)`
  have hMr : ‖∑ r ∈ Rset N (Rpar D),
        ((r : ℂ))⁻¹ * Mr (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) r 1‖
      ≤ P1 N (Rpar D) * (1 + 63/100 * L) := by
    calc ‖∑ r ∈ Rset N (Rpar D),
          ((r : ℂ))⁻¹ * Mr (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) r 1‖
        ≤ ∑ r ∈ Rset N (Rpar D),
            (r : ℝ)⁻¹ * ‖Mr (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) r 1‖ := by
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun r _ => ?_))
          rw [norm_mul, norm_inv, Complex.norm_natCast]
      _ ≤ (∑ r ∈ Rset N (Rpar D), (r.totient : ℝ) / (r : ℝ) ^ 2)
            * (1 + Real.log (z2par D)) :=
          sum_inv_mul_norm_Mr_one_le (Rpar D) hz1pos hz12 hz2ge1
      _ ≤ P1 N (Rpar D) * (1 + 63/100 * L) := by
          rw [hlogz2]
          refine mul_le_mul_of_nonneg_right (sum_totient_div_sq_le_P1 N (Rpar D)) ?_
          positivity
  -- exponential suppression from `|γ| ≥ Λ₀`
  have hKpos : (0 : ℝ) < 3200 * Real.exp 1 * CΓ' := by
    have := Real.exp_pos (1 : ℝ)
    nlinarith
  have hexpγ : Real.exp (-|ρ.im|)
      ≤ (L * Real.exp (6/5 * lam) * (3200 * Real.exp 1 * CΓ'))⁻¹ := by
    have hΛ : Real.exp (Lambda0 D σ (Real.log (3200 * Real.exp 1 * CΓ')))
        = L * Real.exp (6/5 * lam) * (3200 * Real.exp 1 * CΓ') := by
      rw [Lambda0, Real.exp_add, Real.exp_add, ← hLdef, Real.exp_log hL0,
        Real.exp_log hKpos]
    calc Real.exp (-|ρ.im|) = (Real.exp |ρ.im|)⁻¹ := Real.exp_neg _
      _ ≤ (Real.exp (Lambda0 D σ (Real.log (3200 * Real.exp 1 * CΓ'))))⁻¹ := by
          gcongr
      _ = _ := by rw [hΛ]
  -- assemble
  rw [Epole, if_pos rfl, norm_mul, norm_mul, norm_mul]
  have hφnorm : ‖((N.totient : ℂ) / N)‖ = (N.totient : ℝ) / N := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast]
  rw [hφnorm]
  have hE : (0 : ℝ) < Real.exp (6/5 * lam) := Real.exp_pos _
  have hCΓ'0 : (0 : ℝ) < CΓ' := by linarith
  have h0b1 : (0 : ℝ) ≤ CΓ' * Real.exp (-|ρ.im|) := by positivity
  have h0b2 : (0 : ℝ) ≤ CΓ' * Real.exp (-|ρ.im|) * Real.exp (6/5 * lam) := by positivity
  have h0b3 : (0 : ℝ) ≤ CΓ' * Real.exp (-|ρ.im|) * Real.exp (6/5 * lam) * 1 := by
    positivity
  have hstep1 : ‖Complex.Gamma (1 - ρ)‖ * ‖((Xpar D : ℝ) : ℂ) ^ ((1 : ℂ) - ρ)‖
      * ((N.totient : ℝ) / N)
      * ‖∑ r ∈ Rset N (Rpar D),
          ((r : ℂ))⁻¹ * Mr (1 : DirichletCharacter ℂ N) (z1par D) (z2par D) r 1‖
      ≤ CΓ' * Real.exp (-|ρ.im|) * Real.exp (6/5 * lam) * 1
        * (P1 N (Rpar D) * (1 + 63/100 * L)) :=
    mul_le_mul
      (mul_le_mul
        (mul_le_mul hΓ hXnorm (norm_nonneg _) h0b1)
        hφ1 hφ0 h0b2)
      hMr (norm_nonneg _) h0b3
  refine hstep1.trans ?_
  have hb : CΓ' * Real.exp (-|ρ.im|)
      ≤ CΓ' * (L * Real.exp (6/5 * lam) * (3200 * Real.exp 1 * CΓ'))⁻¹ :=
    mul_le_mul_of_nonneg_left hexpγ hCΓ'0.le
  have hinv0 : (0 : ℝ) ≤ (L * Real.exp (6/5 * lam) * (3200 * Real.exp 1 * CΓ'))⁻¹ := by
    positivity
  have hlast : (1 + 63/100 * L) / (3200 * Real.exp 1 * L) ≤ 1/8 := by
    have he2 : (2 : ℝ) ≤ Real.exp 1 := by
      nlinarith [Real.add_one_le_exp (1/2 : ℝ), Real.exp_pos (1/2 : ℝ),
        Real.exp_add (1/2 : ℝ) (1/2 : ℝ)]
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 3200 * Real.exp 1 * L)]
    nlinarith [hL0, hL, he2]
  calc CΓ' * Real.exp (-|ρ.im|) * Real.exp (6/5 * lam) * 1
        * (P1 N (Rpar D) * (1 + 63/100 * L))
      ≤ CΓ' * (L * Real.exp (6/5 * lam) * (3200 * Real.exp 1 * CΓ'))⁻¹
        * Real.exp (6/5 * lam) * 1 * (P1 N (Rpar D) * (1 + 63/100 * L)) := by
        have hnn : (0 : ℝ) ≤ Real.exp (6/5 * lam) * 1
            * (P1 N (Rpar D) * (1 + 63/100 * L)) := by positivity
        nlinarith [hb, hnn]
    _ = P1 N (Rpar D) * ((1 + 63/100 * L) / (3200 * Real.exp 1 * L)) := by
        field_simp
    _ ≤ P1 N (Rpar D) * (1/8) := mul_le_mul_of_nonneg_left hlast hP0
    _ = P1 N (Rpar D) / 8 := by ring

/-! ### Blueprint Proposition 4.4, reassembled over the corrected Lemma 4.3 -/

/-- **Blueprint Proposition 4.4** with I8(b) and I9(c) discharged.  Same frozen
conclusion and same frozen `Λ₀` as `Detector.detector_lower_bound`, with
`CΓ' = 60` substituted; only I9(b) (`hP1`) and the detection estimate
(`hdet`, blueprint Lemmas 4.1+4.2) remain as hypotheses.  The proof is
`Detector.detector_lower_bound`'s final triangle-inequality assembly rerun
over `norm_Epole_le'`. -/
theorem detector_lower_bound_of_P1 {N : ℕ} [NeZero N] {D σ : ℝ} (hD1 : 1 < D)
    (hL : 200 ≤ Real.log D) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    {χ : DirichletCharacter ℂ N}
    (hP1 : (1/200) * ((N.totient : ℝ) / N) * Real.log D ≤ P1 N (Rpar D))
    {ρ : ℂ} (hβ : σ ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hγ : χ = 1 → Lambda0 D σ (Real.log (3200 * Real.exp 1 * 60)) ≤ |ρ.im|)
    (hdet : DetectionEstimate χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ) :
    (1/400) * ((N.totient : ℝ) / N) * Real.log D
      ≤ ‖Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖ := by
  have hD0 : (0 : ℝ) < D := by linarith
  have hP0 : 0 ≤ P1 N (Rpar D) := P1_nonneg N (Rpar D)
  -- pole bound: corrected Lemma 4.3 when `χ = χ₀`, trivial otherwise
  have hEp : ‖Epole χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖
      ≤ P1 N (Rpar D) / 8 := by
    by_cases h1 : χ = 1
    · subst h1
      exact norm_Epole_le' hD1 hL hσ1 hσ0 (by norm_num)
        (fun z hz0 hz1 hz2 => norm_Gamma_le_exp_neg_im z hz0 hz1 hz2) hβ hβ1 (hγ rfl)
    · rw [Epole_eq_zero h1, norm_zero]
      linarith only [hP0]
  have hdet' : ‖Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ
      + ((Real.exp (-1 / Xpar D) * P1 N (Rpar D) : ℝ) : ℂ)
      - Epole χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖
      ≤ P1 N (Rpar D) / 8 := hdet
  have hX4 : (4 : ℝ) ≤ Xpar D := by
    have hD4 : (4 : ℝ) ≤ D := by
      have h1 : Real.exp 200 ≤ Real.exp (Real.log D) := Real.exp_le_exp.mpr hL
      rw [Real.exp_log hD0] at h1
      have h2 : (201 : ℝ) ≤ Real.exp 200 := by
        have := Real.add_one_le_exp (200 : ℝ)
        linarith
      linarith
    calc (4 : ℝ) ≤ D := hD4
      _ = D ^ (1 : ℝ) := (Real.rpow_one D).symm
      _ ≤ D ^ (6/5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by norm_num)
  have hXpos : (0 : ℝ) < Xpar D := by linarith
  have hexp : (3/4 : ℝ) ≤ Real.exp (-1 / Xpar D) := by
    have h1 : -1 / Xpar D + 1 ≤ Real.exp (-1 / Xpar D) := Real.add_one_le_exp _
    have h2 : 1 / Xpar D ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hX4
    have h3 : -1 / Xpar D = -(1 / Xpar D) := by ring
    linarith
  have hc : ‖((Real.exp (-1 / Xpar D) * P1 N (Rpar D) : ℝ) : ℂ)‖
      = Real.exp (-1 / Xpar D) * P1 N (Rpar D) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg (Real.exp_pos _).le hP0
  set F := Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ with hFdef
  set E := Epole χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ with hEdef
  set c := ((Real.exp (-1 / Xpar D) * P1 N (Rpar D) : ℝ) : ℂ) with hcdef
  have htri : ‖c‖ ≤ ‖F + c - E‖ + ‖F‖ + ‖E‖ := by
    calc ‖c‖ = ‖((F + c - E) - F) + E‖ := by
          rw [show ((F + c - E) - F) + E = c from by ring]
      _ ≤ ‖(F + c - E) - F‖ + ‖E‖ := norm_add_le _ _
      _ ≤ (‖F + c - E‖ + ‖F‖) + ‖E‖ := add_le_add (norm_sub_le _ _) le_rfl
  have h34 : (3/4 : ℝ) * P1 N (Rpar D)
      ≤ Real.exp (-1 / Xpar D) * P1 N (Rpar D) :=
    mul_le_mul_of_nonneg_right hexp hP0
  linarith only [htri, hc, h34, hdet', hEp, hP1]

/-! ### I9(b): the lower bound `P(1) ≥ (1/2)(φ(d)/d)·log R`

Blueprint §2 I9(b), in the `Rpar` form demanded by `detector_lower_bound`.
The route is the blueprint's own sketch: squarefree `r ≤ R` factors as
`r = a·b` with `a ∣ rad(d)` and `(b,d) = 1`, and `∑_{n ≤ R} 1/n ≤ ζ(2)·∑'_{r ≤ R}`
by writing `n = k²·r` with `r` squarefree. -/

/-- Transfer along a map into a product of two index sets: if `n ↦ (g n).1`,
`(g n).2` is injective, lands in `A ×ˢ B`, and splits the summand as
`u·v`, then `∑ w ≤ (∑ u)·(∑ v)`. -/
private lemma sum_le_mul_sum_of_split {s A B : Finset ℕ} {u v w : ℕ → ℝ}
    (hu : ∀ a, 0 ≤ u a) (hv : ∀ b, 0 ≤ v b) (g : ℕ → ℕ × ℕ)
    (hmem : ∀ n ∈ s, (g n).1 ∈ A ∧ (g n).2 ∈ B)
    (hval : ∀ n ∈ s, w n = u (g n).1 * v (g n).2)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, g x = g y → x = y) :
    ∑ n ∈ s, w n ≤ (∑ a ∈ A, u a) * ∑ b ∈ B, v b := by
  classical
  calc ∑ n ∈ s, w n = ∑ n ∈ s, u (g n).1 * v (g n).2 := Finset.sum_congr rfl hval
    _ = ∑ p ∈ s.image g, u p.1 * v p.2 :=
        (Finset.sum_image (f := fun p : ℕ × ℕ => u p.1 * v p.2) hinj).symm
    _ ≤ ∑ p ∈ A ×ˢ B, u p.1 * v p.2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun p _ _ => mul_nonneg (hu _) (hv _))
        intro p hp
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hp
        exact Finset.mem_product.mpr (hmem n hn)
    _ = (∑ a ∈ A, u a) * ∑ b ∈ B, v b := by
        rw [Finset.sum_product, Finset.sum_mul]
        exact Finset.sum_congr rfl fun a _ => by simp [Finset.mul_sum]

/-- `∑_{1 ≤ k ≤ M} k^{-2} ≤ 2 − 1/M` for `M ≥ 1`; in particular `≤ 2`. -/
private lemma sum_inv_sq_Icc_le (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, ((k : ℝ) ^ 2)⁻¹ ≤ 2 := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  · have key : ∀ m : ℕ, 1 ≤ m → ∑ k ∈ Finset.Icc 1 m, ((k : ℝ) ^ 2)⁻¹ ≤ 2 - 1/(m : ℝ) := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base => norm_num
      | succ n hn ih =>
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
        have hn1 : (0 : ℝ) < ((n : ℝ) + 1) := by linarith
        have hstep : (((n : ℕ) + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        rw [hstep]
        have hkey : (((n : ℝ) + 1) ^ 2)⁻¹ ≤ 1/(n : ℝ) - 1/((n : ℝ) + 1) := by
          rw [div_sub_div _ _ (ne_of_gt hn0) (ne_of_gt hn1)]
          rw [inv_le_iff_one_le_mul₀ (by positivity)]
          field_simp
          nlinarith
        linarith
    have h1 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have := key M hM
    have h2 : (0 : ℝ) < 1/(M : ℝ) := by positivity
    linarith

/-- `harmonic M` as a real `Finset.Icc` sum. -/
private lemma harmonic_eq_sum_Icc (M : ℕ) :
    ((harmonic M : ℚ) : ℝ) = ∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ := by
  induction M with
  | zero => simp
  | succ m ih =>
    rw [harmonic_succ, Finset.sum_Icc_succ_top (by omega)]
    push_cast
    rw [← ih]

/-- `∑_{n ≤ M} 1/n ≤ (∑_{k ≤ M} k^{-2})·∑'_{r ≤ M} 1/r`, from `n = k²·r`
with `r` squarefree. -/
private lemma sum_inv_Icc_le_sq_mul_squarefree (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹
      ≤ (∑ k ∈ Finset.Icc 1 M, ((k : ℝ) ^ 2)⁻¹)
        * ∑ r ∈ (Finset.Icc 1 M).filter (fun r => Squarefree r), (r : ℝ)⁻¹ := by
  classical
  have hchoice : ∀ n : ℕ, ∃ p : ℕ × ℕ, p.1 ^ 2 * p.2 = n ∧ Squarefree p.2 := by
    intro n
    obtain ⟨a, b, hab, ha⟩ := Nat.sq_mul_squarefree n
    exact ⟨(b, a), hab, ha⟩
  choose g hg1 hg2 using hchoice
  refine sum_le_mul_sum_of_split (u := fun k : ℕ => ((k : ℝ) ^ 2)⁻¹)
    (v := fun r : ℕ => (r : ℝ)⁻¹) (fun a => by positivity) (fun b => by positivity)
    g ?_ ?_ ?_
  · intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hg1n : (g n).1 ^ 2 * (g n).2 = n := hg1 n
    have hg2n : Squarefree (g n).2 := hg2 n
    set k := (g n).1 with hkdef
    set r := (g n).2 with hrdef
    clear_value k r
    have hn0 : 0 < n := hn1
    have hrne : r ≠ 0 := hg2n.ne_zero
    have hkne : k ≠ 0 := by
      intro h
      rw [h] at hg1n
      simp at hg1n
      omega
    have hd1 : k ∣ n := ⟨k * r, by rw [← hg1n]; ring⟩
    have hd2 : r ∣ n := ⟨k ^ 2, by rw [← hg1n]; ring⟩
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hkne,
      le_trans (Nat.le_of_dvd hn0 hd1) hn2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hrne,
        le_trans (Nat.le_of_dvd hn0 hd2) hn2⟩, hg2n⟩⟩
  · intro n _
    have h : ((g n).1 : ℝ) ^ 2 * ((g n).2 : ℝ) = (n : ℝ) := by
      have hc := congrArg (fun m : ℕ => (m : ℝ)) (hg1 n)
      push_cast at hc
      exact hc
    rw [← h, mul_inv]
  · intro x _ y _ h
    rw [← hg1 x, ← hg1 y, h]

open scoped Classical in
/-- Blueprint I9(b), splitting step (pointwise): a squarefree `r` factors as
`r = a·b` with `a ∣ N` squarefree and `b` squarefree coprime to `N`. -/
private lemma exists_split_coprime (N : ℕ) (hN : N ≠ 0) : ∀ r : ℕ, ∃ p : ℕ × ℕ,
    Squarefree r → (p.1 * p.2 = r ∧ p.1 ∣ N ∧ Squarefree p.1 ∧ Squarefree p.2 ∧
      p.2.Coprime N) := by
  classical
  intro r
  by_cases hr : Squarefree r
  · refine ⟨(∏ p ∈ r.primeFactors.filter (fun p => p ∣ N), p,
      ∏ p ∈ r.primeFactors.filter (fun p => ¬ p ∣ N), p), fun _ => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
    · simpa using
        (Finset.prod_filter_mul_prod_filter_not r.primeFactors (fun p => p ∣ N)
          (fun p => p)).trans (Nat.prod_primeFactors_of_squarefree hr)
    · refine dvd_trans ?_ (Nat.prod_primeFactors_dvd N)
      refine Finset.prod_dvd_prod_of_subset (r.primeFactors.filter (fun p => p ∣ N))
        N.primeFactors (fun p : ℕ => p) ?_
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp1, hp2, hN⟩
    · exact squarefree_prod_primes fun p hp =>
        Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    · exact squarefree_prod_primes fun p hp =>
        Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
    · show (∏ p ∈ r.primeFactors.filter (fun p => ¬ p ∣ N), p).Coprime N
      refine Nat.Coprime.prod_left ?_
      intro p hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
      exact (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors hp1)).mpr hp2
  · exact ⟨(1, 1), fun h => absurd h hr⟩

open scoped Classical in
/-- Blueprint I9(b), splitting step: `∑'_{r ≤ M} 1/r ≤ (∑_{a ∣ N} μ²(a)/a)·P(1)`. -/
private lemma sum_inv_squarefree_le_split (N M : ℕ) (hN : N ≠ 0) :
    ∑ r ∈ (Finset.Icc 1 M).filter (fun r => Squarefree r), (r : ℝ)⁻¹
      ≤ (∑ a ∈ N.divisors.filter (fun a => Squarefree a), (a : ℝ)⁻¹)
        * ∑ b ∈ (Finset.Icc 1 M).filter (fun b => Squarefree b ∧ b.Coprime N),
            (b : ℝ)⁻¹ := by
  classical
  choose g hg using exists_split_coprime N hN
  refine sum_le_mul_sum_of_split (u := fun a : ℕ => (a : ℝ)⁻¹)
    (v := fun b : ℕ => (b : ℝ)⁻¹) (fun a => by positivity) (fun b => by positivity)
    g ?_ ?_ ?_
  · intro r hr
    obtain ⟨hrI, hrsf⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_Icc.mp hrI
    obtain ⟨hab, hdvdN, hsfa, hsfb, hcop⟩ := hg r hrsf
    set a := (g r).1 with hadef
    set b := (g r).2 with hbdef
    clear_value a b
    have hb0 : b ≠ 0 := hsfb.ne_zero
    have hbdvd : b ∣ r := ⟨a, by rw [← hab]; ring⟩
    exact ⟨Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvdN, hN⟩, hsfa⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hb0, le_trans (Nat.le_of_dvd hr1 hbdvd) hr2⟩,
        hsfb, hcop⟩⟩
  · intro r hr
    obtain ⟨-, hrsf⟩ := Finset.mem_filter.mp hr
    obtain ⟨hab, -⟩ := hg r hrsf
    have h : ((g r).1 : ℝ) * ((g r).2 : ℝ) = (r : ℝ) := by
      have hc := congrArg (fun m : ℕ => (m : ℝ)) hab
      push_cast at hc
      exact hc
    rw [← h, mul_inv]
  · intro x hx y hy h
    obtain ⟨-, hxsf⟩ := Finset.mem_filter.mp hx
    obtain ⟨-, hysf⟩ := Finset.mem_filter.mp hy
    obtain ⟨habx, -⟩ := hg x hxsf
    obtain ⟨haby, -⟩ := hg y hysf
    rw [← habx, ← haby, h]

open scoped Classical in
/-- `∑_{a ∣ N} μ²(a)/a = ∏_{p ∣ N}(1 + 1/p) ≤ N/φ(N)`. -/
private lemma sum_inv_squarefree_divisors_le (N : ℕ) (hN : N ≠ 0) :
    ∑ a ∈ N.divisors.filter (fun a => Squarefree a), (a : ℝ)⁻¹
      ≤ (N : ℝ) / (N.totient : ℝ) := by
  classical
  set P : ℝ := ∏ p ∈ N.primeFactors, (p : ℝ) with hPdef
  set Pm : ℝ := ∏ p ∈ N.primeFactors, ((p : ℝ) - 1) with hPmdef
  set Pp : ℝ := ∏ p ∈ N.primeFactors, ((p : ℝ) + 1) with hPpdef
  have hp2 : ∀ p ∈ N.primeFactors, (2 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hPpos : (0 : ℝ) < P := by
    rw [hPdef]
    exact Finset.prod_pos fun p hp => by linarith [hp2 p hp]
  have hPmpos : (0 : ℝ) < Pm := by
    rw [hPmdef]
    exact Finset.prod_pos fun p hp => by linarith [hp2 p hp]
  have hφpos : (0 : ℝ) < (N.totient : ℝ) := by
    have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN)
    exact_mod_cast this
  -- Euler product for the divisor sum
  have hEuler : ∑ a ∈ N.divisors.filter (fun a => Squarefree a), (a : ℝ)⁻¹
      = ∏ p ∈ N.primeFactors, (1 + (p : ℝ)⁻¹) := by
    rw [← sum_divisors_ite_squarefree_prod hN (fun p => (p : ℝ)⁻¹), Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hsf : Squarefree a
    · rw [if_pos hsf, if_pos hsf, Finset.prod_inv_distrib]
      congr 1
      have h : ((∏ p ∈ a.primeFactors, p : ℕ) : ℝ) = (a : ℝ) := by
        exact_mod_cast congrArg (fun m : ℕ => (m : ℝ))
          (Nat.prod_primeFactors_of_squarefree hsf)
      rw [← h, Nat.cast_prod]
    · rw [if_neg hsf, if_neg hsf]
  -- `∏(1+1/p) = Pp/P`
  have hprod : ∏ p ∈ N.primeFactors, (1 + (p : ℝ)⁻¹) = Pp / P := by
    rw [hPpdef, hPdef, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith [hp2 p hp]
    field_simp
  -- Euler's totient identity
  have hid : (N.totient : ℝ) * P = (N : ℝ) * Pm := by
    have hnat := Nat.totient_mul_prod_primeFactors N
    have hc := congrArg (fun m : ℕ => (m : ℝ)) hnat
    simp only [Nat.cast_mul, Nat.cast_prod] at hc
    rw [hPdef, hPmdef]
    rw [hc]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have h1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    rw [Nat.cast_sub h1, Nat.cast_one]
  -- `Pm·Pp ≤ P²`
  have hPmPp : Pm * Pp ≤ P * P := by
    rw [hPmdef, hPpdef, hPdef, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun p hp => by nlinarith [hp2 p hp]) ?_
    intro p hp
    nlinarith [hp2 p hp]
  rw [hEuler, hprod, div_le_div_iff₀ hPpos hφpos]
  nlinarith [hPmPp, hPmpos, hPpos, hφpos, hid, mul_pos hPpos hφpos]

open scoped Classical in
/-- **Blueprint interface I9(b)**: `P(1) ≥ (1/2)·(φ(N)/N)·log R`.
No threshold `R ≥ R₀` is needed (for `R < 1` the left side is `≤ 0`). -/
theorem P1_lower_log (N : ℕ) [NeZero N] {R : ℝ} (hR : 0 ≤ R) :
    (1/2) * ((N.totient : ℝ) / N) * Real.log R ≤ P1 N R := by
  classical
  set M := ⌊R⌋₊ with hM
  have hN : N ≠ 0 := NeZero.ne N
  have hNr : (0 : ℝ) < (N : ℝ) := by
    have := Nat.pos_of_ne_zero hN; exact_mod_cast this
  have hφr : (0 : ℝ) < (N.totient : ℝ) := by
    have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hN); exact_mod_cast this
  have hP0 : (0 : ℝ) ≤ P1 N R := P1_nonneg N R
  have hSFnn : (0 : ℝ) ≤ ∑ r ∈ (Finset.Icc 1 M).filter (fun r => Squarefree r), (r : ℝ)⁻¹ :=
    Finset.sum_nonneg fun r _ => by positivity
  -- `Rset` is exactly the coprime squarefree filter
  have hRset : (Finset.Icc 1 M).filter (fun b => Squarefree b ∧ b.Coprime N) = Rset N R := rfl
  -- log R ≤ harmonic ⌊R⌋
  have h1 : Real.log R ≤ ∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹ := by
    rw [← harmonic_eq_sum_Icc]
    exact log_le_harmonic_floor R hR
  -- squarefree extraction
  have h2 : ∑ n ∈ Finset.Icc 1 M, (n : ℝ)⁻¹
      ≤ 2 * ∑ r ∈ (Finset.Icc 1 M).filter (fun r => Squarefree r), (r : ℝ)⁻¹ := by
    refine (sum_inv_Icc_le_sq_mul_squarefree M).trans ?_
    exact mul_le_mul_of_nonneg_right (sum_inv_sq_Icc_le M) hSFnn
  -- coprime extraction
  have h3 : ∑ r ∈ (Finset.Icc 1 M).filter (fun r => Squarefree r), (r : ℝ)⁻¹
      ≤ ((N : ℝ) / (N.totient : ℝ)) * P1 N R := by
    refine (sum_inv_squarefree_le_split N M hN).trans ?_
    rw [hRset]
    exact mul_le_mul_of_nonneg_right (sum_inv_squarefree_divisors_le N hN) hP0
  have hfin : Real.log R ≤ 2 * ((N : ℝ) / (N.totient : ℝ)) * P1 N R := by
    have := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have hc0 : (0 : ℝ) ≤ 1/2 * ((N.totient : ℝ) / N) := by positivity
  have hkey := mul_le_mul_of_nonneg_left hfin hc0
  have hsimp : 1/2 * ((N.totient : ℝ) / N) * (2 * ((N : ℝ) / (N.totient : ℝ)) * P1 N R)
      = P1 N R := by
    field_simp
  linarith [hkey, hsimp.le, hsimp.ge]

/-- **I9(b) in the `Rpar` form consumed by `detector_lower_bound`**:
`(1/200)·(φ(N)/N)·log D ≤ P(1)`. -/
theorem P1_lower (N : ℕ) [NeZero N] {D : ℝ} (hD : 0 < D) :
    (1/200) * ((N.totient : ℝ) / N) * Real.log D ≤ P1 N (Rpar D) := by
  have hR0 : (0 : ℝ) ≤ Rpar D := (Real.rpow_pos_of_pos hD _).le
  have hlog : Real.log (Rpar D) = Real.log D / 100 := by
    rw [Rpar, Real.log_rpow hD]; ring
  have := P1_lower_log N hR0
  rw [hlog] at this
  calc (1/200) * ((N.totient : ℝ) / N) * Real.log D
      = 1/2 * ((N.totient : ℝ) / N) * (Real.log D / 100) := by ring
    _ ≤ P1 N (Rpar D) := this

/-! ### The unconditional detector lower bound -/

/-- **THE DELIVERABLE**: blueprint Proposition 4.4 with all three interface
hypotheses of `Detector.detector_lower_bound` discharged — I8(b) by
`norm_Gamma_le_exp_neg_im` (`CΓ' = 60`), I9(b) by `P1_lower`, and I9(c) by its
corrected replacement `sum_totient_div_sq_le_P1` (see the I9(c) discussion
above: the frozen I9(c) is false, and the replacement is stronger where used).
`Λ₀` and the conclusion are the frozen ones.  The only remaining hypothesis is
`hdet`, i.e. blueprint Lemmas 4.1+4.2 (the Mellin rectangle shift); the fact
that `ρ` is a zero of `L(·,χ)` enters only there. -/
theorem detector_lower_bound_uncond {N : ℕ} [NeZero N] {D σ : ℝ} (hD1 : 1 < D)
    (hL : 200 ≤ Real.log D) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    {χ : DirichletCharacter ℂ N} {ρ : ℂ} (hβ : σ ≤ ρ.re) (hβ1 : ρ.re ≤ 1)
    (hγ : χ = 1 → Lambda0 D σ (Real.log (3200 * Real.exp 1 * 60)) ≤ |ρ.im|)
    (hdet : DetectionEstimate χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ) :
    (1/400) * ((N.totient : ℝ) / N) * Real.log D
      ≤ ‖Fdet χ (z1par D) (z2par D) (Rpar D) (Xpar D) ρ‖ :=
  detector_lower_bound_of_P1 hD1 hL hσ0 hσ1 (P1_lower N (by linarith)) hβ hβ1 hγ hdet
/-! ### Z6c-Q: the sifted arithmetic factor `Q_R`

Blueprint §12.3 (frozen `Z6c-Q`) and §2 I9(b), I9(c).  The arithmetic factor
carried by `P(1)` is *not* `φ(N)/N` but the sifted factor
`Q_R = φ(q_R)/q_R`, where `q_R = ∏_{p ∣ N, p ≤ R} p`: every `r ≤ R` has all
its prime factors `≤ R`, so for such `r`, `(r,N) = 1 ↔ (r,q_R) = 1`, and both
`P(1)` and `Φ_R` are the old sums read at the modulus `q_R`.  The primes
`p ∣ N` with `p > R` are invisible to them.  Since `φ(N)/N ≤ Q_R`
(`totient_div_le_QR`), the `φ(N)/N` statements above are corollaries. -/

/-- `q_R(N) := ∏_{p ∣ N, p ≤ R} p`, the `R`-smooth radical of `N`. -/
noncomputable def qR (N : ℕ) (R : ℝ) : ℕ :=
  ∏ p ∈ N.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ R), p

/-- The sifted arithmetic factor `Q_R := φ(q_R)/q_R = ∏_{p ∣ N, p ≤ R}(1 − 1/p)`. -/
noncomputable def QR (N : ℕ) (R : ℝ) : ℝ := ((qR N R).totient : ℝ) / (qR N R : ℝ)

/-- The set of primes `≤ R`. -/
noncomputable def primesLe (R : ℝ) : Finset ℕ := (Finset.Icc 1 ⌊R⌋₊).filter Nat.Prime

/-- The finite Euler product `∏_{p ≤ R}(1 − 1/p)⁻¹`. -/
noncomputable def MertensProd (R : ℝ) : ℝ := ∏ p ∈ primesLe R, (1 - (p : ℝ)⁻¹)⁻¹

lemma qR_squarefree (N : ℕ) (R : ℝ) : Squarefree (qR N R) := by
  rw [qR]
  exact squarefree_prod_primes fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma qR_ne_zero (N : ℕ) (R : ℝ) : qR N R ≠ 0 := (qR_squarefree N R).ne_zero

lemma qR_pos (N : ℕ) (R : ℝ) : 0 < qR N R := Nat.pos_of_ne_zero (qR_ne_zero N R)

lemma qR_primeFactors (N : ℕ) (R : ℝ) :
    (qR N R).primeFactors = N.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ R) := by
  rw [qR]
  exact Nat.primeFactors_prod fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1

lemma qR_dvd (N : ℕ) (R : ℝ) : qR N R ∣ N := by
  refine dvd_trans ?_ (Nat.prod_primeFactors_dvd N)
  rw [qR]
  exact Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ => p) (Finset.filter_subset _ _)

/-- `1/p ≤ 1/2 < 1` for a prime `p`. -/
private lemma inv_prime_le_half {p : ℕ} (hp : (2 : ℝ) ≤ (p : ℝ)) :
    0 < (p : ℝ)⁻¹ ∧ (p : ℝ)⁻¹ ≤ 1/2 := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hinv : (p : ℝ)⁻¹ * (p : ℝ) = 1 := inv_mul_cancel₀ hp0.ne'
  have hipos : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  refine ⟨hipos, ?_⟩
  nlinarith

/-- `φ(n)/n = ∏_{p ∣ n}(1 − 1/p)`. -/
private lemma totient_div_eq_prod (n : ℕ) (hn : n ≠ 0) :
    (n.totient : ℝ) / (n : ℝ) = ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have hp2 : ∀ p ∈ n.primeFactors, (2 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  set P : ℝ := ∏ p ∈ n.primeFactors, (p : ℝ) with hPdef
  set Pm : ℝ := ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) with hPmdef
  have hPpos : (0 : ℝ) < P := by
    rw [hPdef]; exact Finset.prod_pos fun p hp => by linarith [hp2 p hp]
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have := Nat.pos_of_ne_zero hn; exact_mod_cast this
  have hid : (n.totient : ℝ) * P = (n : ℝ) * Pm := by
    have hnat := Nat.totient_mul_prod_primeFactors n
    have hc := congrArg (fun m : ℕ => (m : ℝ)) hnat
    simp only [Nat.cast_mul, Nat.cast_prod] at hc
    rw [hPdef, hPmdef, hc]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    have h1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    rw [Nat.cast_sub h1, Nat.cast_one]
  have hprod : ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) = Pm / P := by
    rw [hPmdef, hPdef, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < (p : ℝ) := by linarith [hp2 p hp]
    field_simp
  rw [hprod, div_eq_div_iff hn0.ne' hPpos.ne']
  linear_combination hid

/-- `Q_R = ∏_{p ∣ N, p ≤ R}(1 − 1/p)`. -/
lemma QR_eq_prod (N : ℕ) (R : ℝ) :
    QR N R = ∏ p ∈ N.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ R), (1 - (p : ℝ)⁻¹) := by
  rw [QR, totient_div_eq_prod _ (qR_ne_zero N R), qR_primeFactors]

/-- Product over a subset dominates the product over the whole set, when all
factors lie in `[0,1]`. -/
private lemma prod_le_prod_subset_of_le_one {s t : Finset ℕ} (h : s ⊆ t) (f : ℕ → ℝ)
    (h0 : ∀ p ∈ t, 0 ≤ f p) (h1 : ∀ p ∈ t, f p ≤ 1) :
    ∏ p ∈ t, f p ≤ ∏ p ∈ s, f p := by
  classical
  rw [← Finset.prod_sdiff h]
  have hA : (0 : ℝ) ≤ ∏ p ∈ t \ s, f p :=
    Finset.prod_nonneg fun p hp => h0 p (Finset.mem_sdiff.mp hp).1
  have hA1 : ∏ p ∈ t \ s, f p ≤ 1 :=
    Finset.prod_le_one (fun p hp => h0 p (Finset.mem_sdiff.mp hp).1)
      (fun p hp => h1 p (Finset.mem_sdiff.mp hp).1)
  have hB : (0 : ℝ) ≤ ∏ p ∈ s, f p := Finset.prod_nonneg fun p hp => h0 p (h hp)
  nlinarith

lemma QR_pos (N : ℕ) (R : ℝ) : 0 < QR N R := by
  rw [QR]
  have h1 : (0 : ℝ) < ((qR N R).totient : ℝ) := by
    have := Nat.totient_pos.mpr (qR_pos N R); exact_mod_cast this
  have h2 : (0 : ℝ) < ((qR N R : ℕ) : ℝ) := by
    have := qR_pos N R; exact_mod_cast this
  positivity

lemma QR_le_one (N : ℕ) (R : ℝ) : QR N R ≤ 1 := by
  rw [QR, div_le_one]
  · exact_mod_cast Nat.totient_le _
  · have := qR_pos N R; exact_mod_cast this

/-- `φ(N)/N ≤ Q_R`: the sifted factor is the larger one, so every `Q_R` bound
implies the corresponding `φ(N)/N` bound. -/
theorem totient_div_le_QR (N : ℕ) (hN : N ≠ 0) (R : ℝ) :
    (N.totient : ℝ) / (N : ℝ) ≤ QR N R := by
  rw [totient_div_eq_prod N hN, QR_eq_prod]
  refine prod_le_prod_subset_of_le_one (Finset.filter_subset _ _) _ ?_ ?_ <;>
    · intro p hp
      have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      obtain ⟨h1, h2⟩ := inv_prime_le_half hp2
      linarith

/-- **The structural key**: every `b ≤ R` sees only primes `≤ R`, so being
coprime to `N` is the same as being coprime to `q_R`. -/
lemma coprime_qR_iff {N : ℕ} (hN : N ≠ 0) {R : ℝ} {b : ℕ} (hb0 : b ≠ 0)
    (hb : (b : ℝ) ≤ R) : b.Coprime (qR N R) ↔ b.Coprime N := by
  constructor
  · intro h
    have h' : Nat.gcd b (qR N R) = 1 := h
    by_contra hcon
    have hne : Nat.gcd b N ≠ 1 := hcon
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpb : p ∣ b := hpd.trans (Nat.gcd_dvd_left _ _)
    have hpN : p ∣ N := hpd.trans (Nat.gcd_dvd_right _ _)
    have hple : (p : ℝ) ≤ R := by
      have hpleb : p ≤ b := Nat.le_of_dvd (Nat.pos_of_ne_zero hb0) hpb
      have : (p : ℝ) ≤ (b : ℝ) := by exact_mod_cast hpleb
      linarith
    have hmem : p ∈ N.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ R) :=
      Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpN, hN⟩, hple⟩
    have hpq : p ∣ qR N R := by
      rw [qR]; exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hmem
    have hdg : p ∣ Nat.gcd b (qR N R) := Nat.dvd_gcd hpb hpq
    rw [h'] at hdg
    exact hp.one_lt.ne' (Nat.dvd_one.mp hdg)
  · intro h
    exact Nat.Coprime.coprime_dvd_right (qR_dvd N R) h


/-- **Blueprint interface I9(b), `Q_R` form** (frozen `Z6c-Q`, first display):
`(1/2)·Q_R·log R ≤ P(1)`.  No threshold `R ≥ R₀` is needed.  `P1_lower_log` is
the `φ(N)/N` corollary via `totient_div_le_QR`. -/
theorem P1_lower_log_QR (N : ℕ) [NeZero N] {R : ℝ} (hR : 0 ≤ R) :
    (1/2) * QR N R * Real.log R ≤ P1 N R := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  have hqne : qR N R ≠ 0 := qR_ne_zero N R
  have hqr : (0 : ℝ) < (qR N R : ℝ) := by exact_mod_cast qR_pos N R
  have hφq : (0 : ℝ) < ((qR N R).totient : ℝ) := by
    have := Nat.totient_pos.mpr (qR_pos N R); exact_mod_cast this
  have hqne' : (qR N R : ℝ) ≠ 0 := ne_of_gt hqr
  have hφne : ((qR N R).totient : ℝ) ≠ 0 := ne_of_gt hφq
  have hP0 : (0 : ℝ) ≤ P1 N R := P1_nonneg N R
  have hble : ∀ b : ℕ, b ≤ ⌊R⌋₊ → (b : ℝ) ≤ R := by
    intro b hb
    have h1 : (b : ℝ) ≤ (⌊R⌋₊ : ℝ) := by exact_mod_cast hb
    exact h1.trans (Nat.floor_le hR)
  have hSFnn : (0 : ℝ) ≤
      ∑ r ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r), (r : ℝ)⁻¹ :=
    Finset.sum_nonneg fun r _ => by positivity
  -- `Rset` read at the modulus `q_R`: the structural key.
  have hRsetq : (Finset.Icc 1 ⌊R⌋₊).filter (fun b => Squarefree b ∧ b.Coprime (qR N R))
      = Rset N R := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc, mem_Rset]
    constructor
    · rintro ⟨⟨hb1, hb2⟩, hsf, hcop⟩
      exact ⟨⟨hb1, hb2⟩, hsf, (coprime_qR_iff hN (by omega) (hble b hb2)).mp hcop⟩
    · rintro ⟨⟨hb1, hb2⟩, hsf, hcop⟩
      exact ⟨⟨hb1, hb2⟩, hsf, (coprime_qR_iff hN (by omega) (hble b hb2)).mpr hcop⟩
  have h1 : Real.log R ≤ ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, (n : ℝ)⁻¹ := by
    rw [← harmonic_eq_sum_Icc]
    exact log_le_harmonic_floor R hR
  have h2 : ∑ n ∈ Finset.Icc 1 ⌊R⌋₊, (n : ℝ)⁻¹
      ≤ 2 * ∑ r ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r), (r : ℝ)⁻¹ := by
    refine (sum_inv_Icc_le_sq_mul_squarefree ⌊R⌋₊).trans ?_
    exact mul_le_mul_of_nonneg_right (sum_inv_sq_Icc_le ⌊R⌋₊) hSFnn
  have h3 : ∑ r ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Squarefree r), (r : ℝ)⁻¹
      ≤ ((qR N R : ℝ) / ((qR N R).totient : ℝ)) * P1 N R := by
    refine (sum_inv_squarefree_le_split (qR N R) ⌊R⌋₊ hqne).trans ?_
    rw [hRsetq]
    exact mul_le_mul_of_nonneg_right (sum_inv_squarefree_divisors_le _ hqne) hP0
  have hfin : Real.log R ≤ 2 * ((qR N R : ℝ) / ((qR N R).totient : ℝ)) * P1 N R := by
    have := mul_le_mul_of_nonneg_left h3 (by norm_num : (0:ℝ) ≤ 2)
    linarith
  have hc0 : (0 : ℝ) ≤ 1/2 * (((qR N R).totient : ℝ) / (qR N R : ℝ)) := by positivity
  have hkey := mul_le_mul_of_nonneg_left hfin hc0
  have hsimp : 1/2 * (((qR N R).totient : ℝ) / (qR N R : ℝ))
      * (2 * ((qR N R : ℝ) / ((qR N R).totient : ℝ)) * P1 N R) = P1 N R := by
    field_simp
  rw [QR]
  linarith [hkey, hsimp.le, hsimp.ge]

/-- **`Q_R` form of `P1_lower`** (frozen `Z6c-Q`, `Rpar` corollary):
`(1/200)·Q_R(N, R(D))·log D ≤ P(1)`. -/
theorem P1_lower_QR (N : ℕ) [NeZero N] {D : ℝ} (hD : 0 < D) :
    (1/200) * QR N (Rpar D) * Real.log D ≤ P1 N (Rpar D) := by
  have hR0 : (0 : ℝ) ≤ Rpar D := (Real.rpow_pos_of_pos hD _).le
  have hlog : Real.log (Rpar D) = Real.log D / 100 := by
    rw [Rpar, Real.log_rpow hD]; ring
  have h := P1_lower_log_QR N hR0
  rw [hlog] at h
  calc (1/200) * QR N (Rpar D) * Real.log D
      = 1/2 * QR N (Rpar D) * (Real.log D / 100) := by ring
    _ ≤ P1 N (Rpar D) := h

lemma mem_primesLe {R : ℝ} {p : ℕ} : p ∈ primesLe R ↔ p.Prime ∧ p ≤ ⌊R⌋₊ := by
  rw [primesLe, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, h2⟩, hp⟩; exact ⟨hp, h2⟩
  · rintro ⟨hp, h2⟩; exact ⟨⟨hp.one_lt.le, h2⟩, hp⟩

/-- Euler-product majorisation: a set of squarefree integers all of whose prime
factors lie in `S` has `∑ 1/r ≤ ∏_{p ∈ S}(1 + 1/p)`. -/
private lemma sum_inv_le_prod_of_primeFactors_subset {s S : Finset ℕ}
    (hsf : ∀ r ∈ s, Squarefree r) (hsub : ∀ r ∈ s, r.primeFactors ⊆ S) :
    ∑ r ∈ s, (r : ℝ)⁻¹ ≤ ∏ p ∈ S, (1 + (p : ℝ)⁻¹) := by
  classical
  have hinj : ∀ x ∈ s, ∀ y ∈ s, x.primeFactors = y.primeFactors → x = y := by
    intro x hx y hy h
    rw [← Nat.prod_primeFactors_of_squarefree (hsf x hx),
      ← Nat.prod_primeFactors_of_squarefree (hsf y hy), h]
  have hval : ∀ r ∈ s, (r : ℝ)⁻¹ = ∏ p ∈ r.primeFactors, (p : ℝ)⁻¹ := by
    intro r hr
    have hc : ((∏ p ∈ r.primeFactors, p : ℕ) : ℝ) = (r : ℝ) := by
      exact_mod_cast congrArg (fun m : ℕ => (m : ℝ))
        (Nat.prod_primeFactors_of_squarefree (hsf r hr))
    rw [← hc, Nat.cast_prod, ← Finset.prod_inv_distrib]
  calc ∑ r ∈ s, (r : ℝ)⁻¹ = ∑ r ∈ s, ∏ p ∈ r.primeFactors, (p : ℝ)⁻¹ :=
        Finset.sum_congr rfl hval
    _ = ∑ t ∈ s.image Nat.primeFactors, ∏ p ∈ t, (p : ℝ)⁻¹ := by
        rw [Finset.sum_image hinj]
    _ ≤ ∑ t ∈ S.powerset, ∏ p ∈ t, (p : ℝ)⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun t _ _ => Finset.prod_nonneg fun p _ => by positivity)
        intro t ht
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
        exact Finset.mem_powerset.mpr (hsub r hr)
    _ = ∏ p ∈ S, ((p : ℝ)⁻¹ + 1) := by
        rw [Finset.prod_add]
        exact Finset.sum_congr rfl fun t _ => by simp
    _ = ∏ p ∈ S, (1 + (p : ℝ)⁻¹) := Finset.prod_congr rfl fun p _ => by ring

/-- `∏_{p ∈ S}(1 + 1/p) ≤ ∏_{p ∈ S}(1 − 1/p)⁻¹`, from `(1+x)(1−x) ≤ 1`. -/
private lemma prod_one_add_le_prod_inv_one_sub {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, (1 + (p : ℝ)⁻¹) ≤ ∏ p ∈ S, (1 - (p : ℝ)⁻¹)⁻¹ := by
  refine Finset.prod_le_prod (fun p hp => ?_) (fun p hp => ?_)
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
    obtain ⟨h1, h2⟩ := inv_prime_le_half hp2
    linarith
  · have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hS p hp).two_le
    obtain ⟨h1, h2⟩ := inv_prime_le_half hp2
    have hden : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by linarith
    have hmul : (1 - (p : ℝ)⁻¹) * (1 - (p : ℝ)⁻¹)⁻¹ = 1 := mul_inv_cancel₀ hden.ne'
    have hinvpos : (0 : ℝ) < (1 - (p : ℝ)⁻¹)⁻¹ := by positivity
    nlinarith [hmul, hinvpos, hden, h1, h2]

/-- The primes `≤ R` dividing `q_R` are exactly the prime factors of `q_R`. -/
lemma primesLe_filter_dvd_qR (N : ℕ) (R : ℝ) :
    (primesLe R).filter (fun p => p ∣ qR N R) = (qR N R).primeFactors := by
  classical
  ext p
  rw [Finset.mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hd⟩
    exact ⟨(mem_primesLe.mp hp).1, hd, qR_ne_zero N R⟩
  · rintro ⟨hp, hd, -⟩
    refine ⟨mem_primesLe.mpr ⟨hp, ?_⟩, hd⟩
    have hmem : p ∈ N.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ R) := by
      rw [← qR_primeFactors N R]
      exact Nat.mem_primeFactors.mpr ⟨hp, hd, qR_ne_zero N R⟩
    exact Nat.le_floor (Finset.mem_filter.mp hmem).2

set_option maxHeartbeats 1000000 in
/-- **Blueprint interface I9(c) upper bound, `Q_R` form** (frozen `Z6c-Q`,
third display): `P(1) ≤ Q_R · ∏_{p ≤ R}(1 − 1/p)⁻¹`.  Finite Euler-product
majorisation; no Mertens input, no threshold. -/
theorem P1_le_QR_mul_MertensProd (N : ℕ) [NeZero N] (R : ℝ) :
    P1 N R ≤ QR N R * MertensProd R := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  -- every `r ∈ Rset N R` has its prime factors among the primes `≤ R` off `q_R`
  have hsub : ∀ r ∈ Rset N R,
      r.primeFactors ⊆ (primesLe R).filter (fun p => ¬ p ∣ qR N R) := by
    intro r hr p hp
    obtain ⟨⟨hr1, hr2⟩, hrsf, hrcop⟩ := mem_Rset.mp hr
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpr : p ∣ r := Nat.dvd_of_mem_primeFactors hp
    have hple : p ≤ ⌊R⌋₊ := le_trans (Nat.le_of_dvd (by omega) hpr) hr2
    refine Finset.mem_filter.mpr ⟨mem_primesLe.mpr ⟨hpp, hple⟩, ?_⟩
    intro hdq
    have hpN : p ∣ N := hdq.trans (qR_dvd N R)
    have hdg : p ∣ Nat.gcd r N := Nat.dvd_gcd hpr hpN
    have hg : Nat.gcd r N = 1 := hrcop
    rw [hg] at hdg
    exact hpp.one_lt.ne' (Nat.dvd_one.mp hdg)
  have hSprime : ∀ p ∈ (primesLe R).filter (fun p => ¬ p ∣ qR N R), p.Prime :=
    fun p hp => (mem_primesLe.mp (Finset.mem_filter.mp hp).1).1
  have hstep1 : P1 N R ≤ ∏ p ∈ (primesLe R).filter (fun p => ¬ p ∣ qR N R),
      (1 + (p : ℝ)⁻¹) := by
    rw [P1]
    exact sum_inv_le_prod_of_primeFactors_subset
      (fun r hr => (mem_Rset.mp hr).2.1) hsub
  have hstep2 := prod_one_add_le_prod_inv_one_sub hSprime
  -- the Euler product splits along `p ∣ q_R`
  have hsplit : MertensProd R
      = (∏ p ∈ (primesLe R).filter (fun p => p ∣ qR N R), (1 - (p : ℝ)⁻¹)⁻¹)
        * ∏ p ∈ (primesLe R).filter (fun p => ¬ p ∣ qR N R), (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [MertensProd]
    exact (Finset.prod_filter_mul_prod_filter_not (primesLe R)
      (fun p => p ∣ qR N R) _).symm
  have hQRT : QR N R
      = ∏ p ∈ (primesLe R).filter (fun p => p ∣ qR N R), (1 - (p : ℝ)⁻¹) := by
    rw [primesLe_filter_dvd_qR, qR_primeFactors]
    exact QR_eq_prod N R
  have hTcancel : (∏ p ∈ (primesLe R).filter (fun p => p ∣ qR N R), (1 - (p : ℝ)⁻¹))
      * (∏ p ∈ (primesLe R).filter (fun p => p ∣ qR N R), (1 - (p : ℝ)⁻¹)⁻¹) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun p hp => ?_
    have hpp : p.Prime := (mem_primesLe.mp (Finset.mem_filter.mp hp).1).1
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    obtain ⟨h1, h2⟩ := inv_prime_le_half hp2
    exact mul_inv_cancel₀ (by linarith)
  have hstep3 : QR N R * MertensProd R
      = ∏ p ∈ (primesLe R).filter (fun p => ¬ p ∣ qR N R), (1 - (p : ℝ)⁻¹)⁻¹ := by
    rw [hsplit, hQRT, ← mul_assoc, hTcancel, one_mul]
  linarith [hstep1, hstep2, hstep3.le, hstep3.ge]

end Detector
end Carmichael
