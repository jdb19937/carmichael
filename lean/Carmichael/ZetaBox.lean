/-
Route Z, sortie Z8: ζ box clearance.

For every ν > 0 there is a σ₁ < 1 such that the Riemann zeta function has no
zero in the box [σ₁, 1] × [−ν, ν].  Proof: the zeros of ζ inside the compact
box [1/2, 1] × [−ν, ν] form a finite set
(`IsCompact.inter_riemannZetaZeros_finite`); each has real part < 1
(`riemannZeta_ne_zero_of_one_le_re`, which covers s = 1 since Mathlib's
`riemannZeta 1` is a finite nonzero value, `riemannZeta_one_ne_zero`); so the
maximum real part over that finite set is < 1, and any σ₁ strictly between
that maximum and 1 works.  No `s ≠ 1` side condition is needed.

The bridge `LFunction_box_clearance` restates the clearance for the Dirichlet
L-function of any character mod 1 via `DirichletCharacter.LFunction_modOne_eq`,
so the conductor-1 case of the Route Z zero-density bookkeeping can consume it
directly.
-/
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace Carmichael

open Complex Set

/-- **ζ box clearance.**  For every ν > 0 there is a σ₁ < 1 such that ζ has no
zero `s` with σ₁ ≤ Re s ≤ 1 and |Im s| ≤ ν.  (At `s = 1`, Mathlib's junk value
`riemannZeta 1` is nonzero, so the pole point needs no exclusion.) -/
theorem zeta_box_clearance (ν : ℝ) (_hν : 0 < ν) :
    ∃ σ₁ : ℝ, σ₁ < 1 ∧ ∀ s : ℂ, σ₁ ≤ s.re → s.re ≤ 1 → |s.im| ≤ ν →
      riemannZeta s ≠ 0 := by
  -- The compact box [1/2, 1] × [−ν, ν] and its finitely many ζ-zeros.
  have hbox : IsCompact (Icc (1 / 2 : ℝ) 1 ×ℂ Icc (-ν) ν) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hfin : ((Icc (1 / 2 : ℝ) 1 ×ℂ Icc (-ν) ν) ∩ riemannZetaZeros).Finite :=
    hbox.inter_riemannZetaZeros_finite
  -- The real parts of the zeros in the box: a finite set of reals, all < 1.
  set T : Set ℝ :=
    Complex.re '' ((Icc (1 / 2 : ℝ) 1 ×ℂ Icc (-ν) ν) ∩ riemannZetaZeros) with hT
  have hTfin : T.Finite := hfin.image _
  have hTlt : ∀ r ∈ T, r < 1 := by
    rintro r ⟨z, ⟨_, hz⟩, rfl⟩
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) (mem_riemannZetaZeros.mp hz)
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · -- No zeros in the box at all: σ₁ = 1/2 works.
    refine ⟨1 / 2, by norm_num, fun s hs1 hs2 hs3 hzero => ?_⟩
    have hsT : s.re ∈ T :=
      ⟨s, ⟨mem_reProdIm.mpr ⟨⟨hs1, hs2⟩, abs_le.mp hs3⟩,
        mem_riemannZetaZeros.mpr hzero⟩, rfl⟩
    rw [hTe] at hsT
    exact hsT
  · -- Take the maximum real part m < 1 and split the gap: σ₁ = (m + 1)/2.
    have hmem : sSup T ∈ T := hTne.csSup_mem hTfin
    have hmlt : sSup T < 1 := hTlt _ hmem
    -- Zeros in the box have real part ≥ 1/2, so sSup T ≥ 1/2.
    have hmge : 1 / 2 ≤ sSup T := by
      obtain ⟨z, ⟨hzbox, _⟩, hzre⟩ := hmem
      exact hzre ▸ (mem_reProdIm.mp hzbox).1.1
    refine ⟨(sSup T + 1) / 2, by linarith only [hmlt], fun s hs1 hs2 hs3 hzero => ?_⟩
    have hsT : s.re ∈ T :=
      ⟨s, ⟨mem_reProdIm.mpr ⟨⟨by linarith only [hs1, hmge], hs2⟩, abs_le.mp hs3⟩,
        mem_riemannZetaZeros.mpr hzero⟩, rfl⟩
    have hle : s.re ≤ sSup T := le_csSup hTfin.bddAbove hsT
    linarith only [hs1, hle, hmlt]

/-- **Conductor-1 bridge.**  The box clearance for the Dirichlet L-function of
any (necessarily trivial) character mod 1, via `LFunction_modOne_eq`. -/
theorem LFunction_box_clearance (ν : ℝ) (hν : 0 < ν) :
    ∃ σ₁ : ℝ, σ₁ < 1 ∧ ∀ (χ : DirichletCharacter ℂ 1) (s : ℂ),
      σ₁ ≤ s.re → s.re ≤ 1 → |s.im| ≤ ν → DirichletCharacter.LFunction χ s ≠ 0 := by
  obtain ⟨σ₁, hσ₁, hclear⟩ := zeta_box_clearance ν hν
  refine ⟨σ₁, hσ₁, fun χ s hs1 hs2 hs3 => ?_⟩
  rw [DirichletCharacter.LFunction_modOne_eq]
  exact hclear s hs1 hs2 hs3

end Carmichael
