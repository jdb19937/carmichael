/-
Route Z, Z6-logged: the shared parameters and definitions of the logged
zero detector (routez/Z6-logged.md §1, §6.1, with the audit's F1 fix in
routez/Z6-logged-audit.md).  Definitions only; the lemmas live in
`DetectionShiftHalf.lean` (half-line contour shift, identity, pole term) and
`LoggedDetector.lean` (truncation, blocks, Taylor split, class-II mean square).

The detector is Z6c's `Detector.Fdet` at pseudocharacter modulus `R = 1`
(`Rset N 1 = {1}`, `Pfun N 1 n = 1`), Barban–Vehov cuts `(D, 2D)`, smoothing
length `Y = D^{151/100}`, contour shifted to `Re (ρ + w) = 1/2`.
-/
import Carmichael.DetectionShift

set_option autoImplicit false

namespace Carmichael.LoggedDetector

open Real

/-- Smoothing length `Y = D^{151/100}`. -/
noncomputable def Ypar (D : ℝ) : ℝ := D ^ (151/100 : ℝ)

/-- Truncation length of the detector's Dirichlet series. -/
noncomputable def Nmax (D : ℝ) : ℕ := ⌈8 * Ypar D * Real.log D⌉₊

/-- Taylor order / number of dyadic blocks: `J = ⌈log D⌉`. -/
noncomputable def Jpar (D : ℝ) : ℕ := ⌈Real.log D⌉₊

/-- The contour term on the half-line `Re (ρ + w) = 1/2` (the `R = 1` collapse of
`DetectionShift.Ectr`: the `Rset` sum has the single term `r = 1`). -/
noncomputable def EctrHalf {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (D Y : ℝ) (ρ : ℂ) : ℂ :=
  (((1 / (2 * π) : ℝ)) : ℂ) *
    ∫ u : ℝ, DetectionShift.ectrInt χ D (2 * D) Y 1 ρ (1/2 - ρ.re) u

/-- The `(j, k)` coefficient vectors of the Taylor split (Z6-logged Lemma 2.7):
block `2^j D < n ≤ 2^{j+1} D`, `n ≤ Nmax`, weight
`a(n) e^{−n/Y} (−log(n/(2^j D)))^k n^{−σ}`; independent of the zero `ρ`. -/
noncomputable def coeffJK (D σ : ℝ) (j k : ℕ) (n : ℕ) : ℂ :=
  if 2 ^ j * D < (n : ℝ) ∧ (n : ℝ) ≤ 2 ^ (j + 1) * D ∧ n ≤ Nmax D then
    ((Detector.bvA D (2 * D) n * Real.exp (-(n : ℝ) / Ypar D)
        * (-(Real.log ((n : ℝ) / (2 ^ j * D)))) ^ k * (n : ℝ) ^ (-σ) : ℝ) : ℂ)
  else 0

/-- Summation range of the `j`-th block (audit F1: `⌈2^{j+1} D⌉₊`, covering the
whole support of `coeffJK D σ j k`). -/
noncomputable def blockRange (D : ℝ) (j : ℕ) : Finset ℕ :=
  Finset.Icc 1 ⌈2 ^ (j + 1) * D⌉₊

end Carmichael.LoggedDetector
