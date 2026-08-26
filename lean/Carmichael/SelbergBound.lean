/-
The fundamental theorem of the Selberg sieve.

Given Mathlib's `SelbergSieve` (a sifting problem: support `A` with weights,
squarefree prime product `P`, density `ν`, total mass `X`, and level `y`),
this file constructs the Selberg weights `λ_d`, proves `|λ_d| ≤ 1`, evaluates
the main term of the associated Λ² sieve as `1/S` where
`S = ∑_{l ∣ P, l² ≤ y} g(l)` is the Selberg bounding sum, bounds the error
term by `∑_{d ∣ P, d ≤ y} 3^{ω(d)} |R_d|`, and combines these into the
fundamental theorem (`selberg_bound`):

  `siftedSum ≤ X / S + ∑_{d ∣ P, d ≤ y} 3^{ω(d)} |R_d|`.

The proof structure follows Arend Mellendijk's selberg-sieve development
(Lean 3, Apache 2.0, github.com/FLDutchmann/selberg-sieve, and its Lean 4
port), re-derived here against Mathlib's `Mathlib.NumberTheory.SelbergSieve`
(the same author's partial upstreaming), which provides the sieve structures,
`selbergTerms`, the Λ² construction, and the diagonalisation of its main
term. The mathematical treatment is that of Heath-Brown's lecture notes on
sieves.
-/
import Mathlib

namespace Carmichael

noncomputable section

open Finset Nat ArithmeticFunction BoundingSieve

open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega

/-! ### Auxiliary Moebius sums

A truncated Moebius inversion: summing `μ` over the divisors of a squarefree
`m` that are multiples of `l` detects `l = m`. -/

theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then (μ d : ℤ) else 0) = if l = m then μ l else 0 := by
  have h : ∀ n > 0, n ∈ {n : ℕ | Squarefree n} →
      (∑ x ∈ n.divisorsAntidiagonal, μ x.fst • (if l = x.snd then (μ l : ℤ) else 0)) =
        (if l ∣ n then (μ n : ℤ) else 0) := by
    intro n hn_pos hn
    rw [Nat.sum_divisorsAntidiagonal' (f := fun x y => μ x • if l = y then (μ l : ℤ) else 0)]
    by_cases hl : l ∣ n
    · rw [if_pos hl, Finset.sum_eq_single l]
      · have hmul : n / l * l = n := Nat.div_mul_cancel hl
        rw [if_pos rfl, smul_eq_mul,
          ← isMultiplicative_moebius.map_mul_of_coprime
            (coprime_of_squarefree_mul (by rw [hmul]; exact hn)), hmul]
      · intro d _ hdl
        rw [if_neg fun hld => hdl hld.symm, smul_zero]
      · intro hl'
        exact absurd (Nat.mem_divisors.mpr ⟨hl, hn_pos.ne'⟩) hl'
    · rw [if_neg hl, Finset.sum_eq_zero]
      intro d hd
      rw [if_neg fun hld => hl (by rw [hld]; exact dvd_of_mem_divisors hd), smul_zero]
  exact (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on
    (f := fun i => if l ∣ i then (μ i : ℤ) else 0)
    (g := fun n => if l = n then (μ l : ℤ) else 0)
    {n | Squarefree n} (fun _ _ hmn hn => hn.squarefree_of_dvd hmn)).mpr h m
    (Nat.pos_of_ne_zero hm.ne_zero) hm

theorem moebius_inv_dvd_lower_bound' {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℤ) else 0) = if l = m then μ l else 0 := by
  calc (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℤ) else 0)
      = ∑ d ∈ P.divisors, if d ∣ m then (if l ∣ d then (μ d : ℤ) else 0) else 0 := by
        refine sum_congr rfl fun d _ => ?_
        rw [← ite_and]
        exact if_congr and_comm rfl rfl
    _ = ∑ d ∈ P.divisors.filter (· ∣ m), if l ∣ d then (μ d : ℤ) else 0 :=
        (sum_filter _ _).symm
    _ = ∑ d ∈ m.divisors, if l ∣ d then (μ d : ℤ) else 0 := by
        rw [Nat.divisors_filter_dvd_of_dvd hP.ne_zero hm]
    _ = if l = m then μ l else 0 :=
        moebius_inv_dvd_lower_bound l m (hP.squarefree_of_dvd hm)

theorem moebius_inv_dvd_lower_bound_real {P : ℕ} (hP : Squarefree P) (l m : ℕ) (hm : m ∣ P) :
    (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0) =
      if l = m then (μ l : ℝ) else 0 := by
  have h := moebius_inv_dvd_lower_bound' hP l m hm
  calc (∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℝ) else 0)
      = ((∑ d ∈ P.divisors, if l ∣ d ∧ d ∣ m then (μ d : ℤ) else 0 : ℤ) : ℝ) := by
        rw [Int.cast_sum]
        refine sum_congr rfl fun d _ => ?_
        split_ifs <;> simp
    _ = ((if l = m then μ l else 0 : ℤ) : ℝ) := by rw [h]
    _ = if l = m then (μ l : ℝ) else 0 := by split_ifs <;> simp

/-! ### The Selberg bounding sum -/

variable (s : SelbergSieve)

/-- The Selberg bounding sum at the level of the sieve,
`S = ∑_{l ∣ P, l² ≤ y} g(l)`. The fundamental theorem bounds the sifted sum
by `X/S` plus an error term. -/
def selbergBoundingSum : ℝ :=
  ∑ l ∈ divisors s.prodPrimes, if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0

theorem selbergBoundingSum_eq_sum_filter :
    selbergBoundingSum s =
      ∑ l ∈ (divisors s.prodPrimes).filter (fun l : ℕ => (l : ℝ) ^ 2 ≤ s.level),
        s.selbergTerms l :=
  (sum_filter _ _).symm

theorem selbergBoundingSum_pos : 0 < selbergBoundingSum s := by
  unfold selbergBoundingSum
  rw [← sum_filter]
  apply sum_pos
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    exact selbergTerms_pos hl.1.1
  · refine ⟨1, ?_⟩
    simp only [mem_filter, Nat.one_mem_divisors, Nat.cast_one, one_pow]
    exact ⟨prodPrimes_ne_zero, s.one_le_level⟩

theorem selbergBoundingSum_ne_zero : selbergBoundingSum s ≠ 0 :=
  (selbergBoundingSum_pos s).ne'

theorem selbergBoundingSum_nonneg : 0 ≤ selbergBoundingSum s :=
  (selbergBoundingSum_pos s).le

/-! ### The Selberg weights -/

/-- The Selberg weights `λ_d`, the coefficients of the Λ² sieve that minimise
its main term subject to the level constraint. -/
def selbergWeights : ℕ → ℝ := fun d =>
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * s.selbergTerms d * μ d * (selbergBoundingSum s)⁻¹ *
      ∑ m ∈ divisors s.prodPrimes,
        if ((d : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0
  else 0

theorem selbergWeights_eq_zero_of_not_dvd {d : ℕ} (hd : ¬d ∣ s.prodPrimes) :
    selbergWeights s d = 0 := by
  rw [selbergWeights, if_neg hd]

theorem selbergWeights_eq_zero (d : ℕ) (hd : ¬(d : ℝ) ^ 2 ≤ s.level) :
    selbergWeights s d = 0 := by
  unfold selbergWeights
  split_ifs with h
  · rw [mul_eq_zero_of_right]
    apply Finset.sum_eq_zero
    refine fun m hm => if_neg fun hyp => hd ?_
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast Nat.pos_of_mem_divisors hm
    calc (d : ℝ) ^ 2 = (d : ℝ) ^ 2 * 1 := by ring
      _ ≤ (d : ℝ) ^ 2 * (m : ℝ) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          exact one_le_pow₀ hm1
      _ = ((d : ℝ) * m) ^ 2 := by ring
      _ ≤ s.level := hyp.1
  · rfl

theorem selbergWeights_mul_mu_nonneg (d : ℕ) (hdP : d ∣ s.prodPrimes) :
    0 ≤ selbergWeights s d * μ d := by
  have h1 : (0 : ℝ) ≤ (s.nu d)⁻¹ := inv_nonneg.mpr (nu_pos_of_dvd_prodPrimes hdP).le
  have h2 : (0 : ℝ) ≤ s.selbergTerms d := (selbergTerms_pos hdP).le
  have h3 : (0 : ℝ) ≤ (selbergBoundingSum s)⁻¹ :=
    inv_nonneg.mpr (selbergBoundingSum_nonneg s)
  have h4 : (0 : ℝ) ≤ ∑ m ∈ divisors s.prodPrimes,
      if ((d : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0 := by
    apply sum_nonneg
    intro m hm
    split_ifs with h
    · exact (selbergTerms_pos (dvd_of_mem_divisors hm)).le
    · rfl
  unfold selbergWeights
  rw [if_pos hdP]
  calc (0 : ℝ)
      ≤ ((μ d : ℝ) * μ d) *
          ((s.nu d)⁻¹ * s.selbergTerms d * (selbergBoundingSum s)⁻¹ *
            ∑ m ∈ divisors s.prodPrimes,
              if ((d : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0) := by
        apply mul_nonneg (mul_self_nonneg _)
        exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
    _ = (s.nu d)⁻¹ * s.selbergTerms d * μ d * (selbergBoundingSum s)⁻¹ *
          (∑ m ∈ divisors s.prodPrimes,
            if ((d : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0) *
          μ d := by ring

/-- Change of variables `l = k * m` in a sum over divisors of `n`, valid when
the summand vanishes on divisors not divisible by `k`. -/
theorem sum_mul_subst (k n : ℕ) {f : ℕ → ℝ} (h : ∀ l, l ∣ n → ¬k ∣ l → f l = 0) :
    (∑ l ∈ n.divisors, f l) = ∑ m ∈ n.divisors, if k * m ∣ n then f (k * m) else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hkn : k ∣ n
  swap
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · exact fun m _ => if_neg fun hkmn => hkn ((Nat.dvd_mul_right k m).trans hkmn)
    · intro l hl
      by_cases hkl : k ∣ l
      · exact absurd (hkl.trans (dvd_of_mem_divisors hl)) hkn
      · exact h l (dvd_of_mem_divisors hl) hkl
  have hk_pos : 0 < k := Nat.pos_of_ne_zero fun hk => hn (zero_dvd_iff.mp (hk ▸ hkn))
  calc (∑ l ∈ n.divisors, f l)
      = ∑ l ∈ n.divisors, ∑ m ∈ n.divisors, if l = k * m then f l else 0 := by
        refine sum_congr rfl fun l hl => ?_
        by_cases hkl : k ∣ l
        · rw [Finset.sum_eq_single (l / k)]
          · rw [if_pos (Nat.mul_div_cancel' hkl).symm]
          · intro m _ hmlk
            refine if_neg fun hlkm => hmlk ?_
            rw [hlkm, Nat.mul_div_cancel_left m hk_pos]
          · intro hnk
            exact absurd (Nat.mem_divisors.mpr
              ⟨(Nat.div_dvd_of_dvd hkl).trans (dvd_of_mem_divisors hl), hn⟩) hnk
        · rw [h l (dvd_of_mem_divisors hl) hkl]
          exact (Finset.sum_eq_zero fun m _ => ite_self 0).symm
    _ = ∑ m ∈ n.divisors, if k * m ∣ n then f (k * m) else 0 := by
        rw [sum_comm]
        refine sum_congr rfl fun m _ => ?_
        by_cases hdvd : k * m ∣ n
        · rw [if_pos hdvd,
            Finset.sum_ite_eq_of_mem' n.divisors (k * m) f (Nat.mem_divisors.mpr ⟨hdvd, hn⟩)]
        · rw [if_neg hdvd, Finset.sum_eq_zero]
          intro l hl
          exact if_neg fun hlkm => hdvd (by rw [← hlkm]; exact dvd_of_mem_divisors hl)

/-- The key identity satisfied by the Selberg weights:
`ν(d)·λ_d = S⁻¹·μ(d)·∑_{d ∣ l ∣ P, l² ≤ y} g(l)`. -/
theorem selbergWeights_eq_dvds_sum (d : ℕ) :
    s.nu d * selbergWeights s d =
      (selbergBoundingSum s)⁻¹ * μ d *
        ∑ l ∈ divisors s.prodPrimes,
          if d ∣ l ∧ (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0 := by
  by_cases h_dvd : d ∣ s.prodPrimes
  swap
  · rw [selbergWeights_eq_zero_of_not_dvd s h_dvd, mul_zero, Finset.sum_eq_zero, mul_zero]
    intro l hl
    exact if_neg fun h => h_dvd (h.1.trans (dvd_of_mem_divisors hl))
  have hnu_ne : s.nu d ≠ 0 := nu_ne_zero h_dvd
  apply symm
  calc ((selbergBoundingSum s)⁻¹ * μ d *
        ∑ l ∈ divisors s.prodPrimes,
          if d ∣ l ∧ (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0)
      = ∑ l ∈ divisors s.prodPrimes,
          (selbergBoundingSum s)⁻¹ * μ d *
            (if d ∣ l ∧ (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0) := by
        rw [mul_sum]
    _ = ∑ m ∈ divisors s.prodPrimes,
          if d * m ∣ s.prodPrimes then
            (selbergBoundingSum s)⁻¹ * μ d *
              (if d ∣ d * m ∧ ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level then
                s.selbergTerms (d * m) else 0)
          else 0 := by
        apply sum_mul_subst d s.prodPrimes
        intro l _ hdl
        rw [if_neg fun hc => hdl hc.1, mul_zero]
    _ = ∑ m ∈ divisors s.prodPrimes,
          s.nu d * ((s.nu d)⁻¹ * s.selbergTerms d * μ d * (selbergBoundingSum s)⁻¹ *
            (if ((d : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0)) := by
        refine sum_congr rfl fun m hm => ?_
        rw [mul_ite_zero, ← ite_and,
          show s.nu d * ((s.nu d)⁻¹ * s.selbergTerms d * μ d * (selbergBoundingSum s)⁻¹ *
            (if ((d : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0)) =
            if ((d : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then
              s.nu d * ((s.nu d)⁻¹ * s.selbergTerms d * μ d * (selbergBoundingSum s)⁻¹ *
                s.selbergTerms m)
            else 0 from by split_ifs <;> ring]
        refine if_ctx_congr ⟨fun hc => ?_, fun hc => ?_⟩ (fun hc => ?_) fun _ => rfl
        · refine ⟨?_, (coprime_of_squarefree_mul
            (squarefree_of_dvd_prodPrimes hc.1)).symm⟩
          have := hc.2.2
          push_cast at this ⊢
          exact this
        · refine ⟨Nat.Coprime.mul_dvd_of_dvd_of_dvd hc.2.symm h_dvd
            (dvd_of_mem_divisors hm), dvd_mul_right d m, ?_⟩
          push_cast
          exact hc.1
        · have hcop : Nat.Coprime d m := hc.2.symm
          rw [selbergTerms_isMultiplicative.map_mul_of_coprime hcop]
          calc (selbergBoundingSum s)⁻¹ * (μ d : ℝ) *
                (s.selbergTerms d * s.selbergTerms m)
              = (s.nu d * (s.nu d)⁻¹) *
                  (s.selbergTerms d * μ d * (selbergBoundingSum s)⁻¹ * s.selbergTerms m) := by
                rw [mul_inv_cancel₀ hnu_ne]
                ring
            _ = _ := by ring
    _ = s.nu d * ((s.nu d)⁻¹ * s.selbergTerms d * μ d * (selbergBoundingSum s)⁻¹ *
          ∑ m ∈ divisors s.prodPrimes,
            if ((d : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0) := by
        rw [mul_sum, mul_sum]
    _ = s.nu d * selbergWeights s d := by
        unfold selbergWeights
        rw [if_pos h_dvd]

/-- Diagonalisation of the Selberg weights: the inner sums appearing in the
diagonalised Λ² main term collapse to a single `g(l)·μ(l)/S` term. -/
theorem selbergWeights_diagonalisation (l : ℕ) (hl : l ∈ divisors s.prodPrimes) :
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * selbergWeights s d else 0) =
      if (l : ℝ) ^ 2 ≤ s.level then
        s.selbergTerms l * μ l * (selbergBoundingSum s)⁻¹ else 0 := by
  calc (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * selbergWeights s d else 0)
      = ∑ d ∈ divisors s.prodPrimes, ∑ k ∈ divisors s.prodPrimes,
          if l ∣ d ∧ d ∣ k ∧ (k : ℝ) ^ 2 ≤ s.level then
            s.selbergTerms k * (selbergBoundingSum s)⁻¹ * (μ d : ℝ) else 0 := by
        refine sum_congr rfl fun d _ => ?_
        rw [selbergWeights_eq_dvds_sum, mul_sum, ite_sum_zero]
        refine sum_congr rfl fun k _ => ?_
        rw [mul_ite_zero, ← ite_and]
        exact if_ctx_congr Iff.rfl (fun _ => by ring) fun _ => rfl
    _ = ∑ k ∈ divisors s.prodPrimes,
          if (k : ℝ) ^ 2 ≤ s.level then
            (∑ d ∈ divisors s.prodPrimes, if l ∣ d ∧ d ∣ k then (μ d : ℝ) else 0) *
              s.selbergTerms k * (selbergBoundingSum s)⁻¹
          else 0 := by
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        apply symm
        rw [← boole_mul, sum_mul, sum_mul, mul_sum]
        refine sum_congr rfl fun d _ => ?_
        rw [ite_zero_mul, ite_zero_mul, ite_zero_mul, one_mul, ← ite_and]
        exact if_ctx_congr (by tauto) (fun _ => by ring) fun _ => rfl
    _ = ∑ k ∈ divisors s.prodPrimes,
          if k = l then
            (if (k : ℝ) ^ 2 ≤ s.level then
              s.selbergTerms k * μ k * (selbergBoundingSum s)⁻¹ else 0)
          else 0 := by
        refine sum_congr rfl fun k hk => ?_
        rw [moebius_inv_dvd_lower_bound_real s.prodPrimes_squarefree l k
            (dvd_of_mem_divisors hk),
          ite_zero_mul, ite_zero_mul, ← ite_and, ← ite_and]
        exact if_ctx_congr ⟨fun hc => ⟨hc.2.symm, hc.1⟩, fun hc => ⟨hc.2, hc.1.symm⟩⟩
          (fun hc => by rw [hc.1]; ring) fun _ => rfl
    _ = if (l : ℝ) ^ 2 ≤ s.level then
          s.selbergTerms l * μ l * (selbergBoundingSum s)⁻¹ else 0 := by
        rw [Finset.sum_ite_eq_of_mem' (divisors s.prodPrimes) l _ hl]

/-! ### The Selberg Λ² coefficients -/

/-- The Λ² coefficients built from the Selberg weights. -/
def selbergMuPlus : ℕ → ℝ := lambdaSquared (selbergWeights s)

theorem selbergWeights_one : selbergWeights s 1 = 1 := by
  unfold selbergWeights
  rw [if_pos (one_dvd _), s.nu_mult.map_one, selbergTerms_isMultiplicative.map_one]
  simp only [inv_one, one_mul, ArithmeticFunction.moebius_apply_one, Int.cast_one, mul_one,
    Nat.cast_one, Nat.coprime_one_right_iff, and_true]
  exact inv_mul_cancel₀ (selbergBoundingSum_ne_zero s)

theorem upperMoebius_selbergMuPlus : IsUpperMoebius (selbergMuPlus s) :=
  upperMoebius_lambdaSquared (selbergWeights s) (selbergWeights_one s)

/-- Evaluation of the Λ² main term at the Selberg weights: it is exactly
`1/S`. -/
theorem mainSum_selbergMuPlus : s.mainSum (selbergMuPlus s) = (selbergBoundingSum s)⁻¹ := by
  rw [selbergMuPlus, mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  calc (∑ l ∈ divisors s.prodPrimes, (s.selbergTerms l)⁻¹ *
        (∑ d ∈ divisors s.prodPrimes,
          if l ∣ d then s.nu d * selbergWeights s d else 0) ^ 2)
      = ∑ l ∈ divisors s.prodPrimes,
          (if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0) *
            ((selbergBoundingSum s)⁻¹) ^ 2 := by
        refine sum_congr rfl fun l hl => ?_
        rw [selbergWeights_diagonalisation s l hl, apply_ite (· ^ 2),
          zero_pow (two_ne_zero), mul_ite_zero, ite_zero_mul]
        refine if_ctx_congr Iff.rfl (fun _ => ?_) fun _ => rfl
        have hgl : s.selbergTerms l ≠ 0 := (selbergTerms_pos (dvd_of_mem_divisors hl)).ne'
        have hmu : (μ l : ℝ) ^ 2 = 1 := by
          rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree
            (squarefree_of_mem_divisors_prodPrimes hl), Int.cast_one]
        calc (s.selbergTerms l)⁻¹ *
              (s.selbergTerms l * μ l * (selbergBoundingSum s)⁻¹) ^ 2
            = ((s.selbergTerms l)⁻¹ * s.selbergTerms l) * s.selbergTerms l *
                (μ l : ℝ) ^ 2 * ((selbergBoundingSum s)⁻¹) ^ 2 := by ring
          _ = s.selbergTerms l * ((selbergBoundingSum s)⁻¹) ^ 2 := by
              rw [inv_mul_cancel₀ hgl, hmu]
              ring
    _ = (selbergBoundingSum s)⁻¹ := by
        rw [← sum_mul,
          show (∑ l ∈ divisors s.prodPrimes,
              if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0) =
            selbergBoundingSum s from rfl,
          sq, ← mul_assoc, mul_inv_cancel₀ (selbergBoundingSum_ne_zero s), one_mul]

/-! ### The bound `|λ_d| ≤ 1` -/

theorem eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d) (hmd : m.Coprime d) :
    k = d.gcd (k * m) := by
  obtain ⟨r, rfl⟩ := hkd
  have hrm : r.Coprime m := (hmd.coprime_dvd_right (dvd_mul_left r k)).symm
  have hrm1 : r.gcd m = 1 := hrm
  rw [Nat.gcd_mul_left, hrm1, mul_one]

/-- The condition rewrite at the heart of the weight bound: for `k ∣ d ∣ P`
and `k, m ∣ P`, membership of `k·m` in the `k = gcd(d, l)` fibre of the
bounding sum is equivalent to the condition in the Selberg weight of `d`. -/
theorem gcd_fibre_iff {d k m : ℕ} (hdP : d ∣ s.prodPrimes) (hkd : k ∣ d)
    (hk : k ∈ divisors s.prodPrimes) (hm : m ∈ divisors s.prodPrimes) :
    (k * m ∣ s.prodPrimes ∧ k = d.gcd (k * m) ∧ ((k * m : ℕ) : ℝ) ^ 2 ≤ s.level) ↔
      (((k : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d) := by
  have hk0 : k ≠ 0 := (Nat.pos_of_mem_divisors hk).ne'
  constructor
  · rintro ⟨hkmP, hgcd, hy⟩
    refine ⟨by push_cast at hy ⊢; exact hy, ?_⟩
    obtain ⟨r, rfl⟩ := hkd
    have hmk : m.Coprime k :=
      (coprime_of_squarefree_mul (squarefree_of_dvd_prodPrimes hkmP)).symm
    have hrm1 : r.gcd m = 1 := by
      rw [Nat.gcd_mul_left] at hgcd
      have hcancel : k * 1 = k * r.gcd m := by rw [mul_one, ← hgcd]
      exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk0) hcancel).symm
    have hmr : m.Coprime r := Nat.Coprime.symm hrm1
    exact Nat.Coprime.mul_right hmk hmr
  · rintro ⟨hy, hcop⟩
    refine ⟨?_, eq_gcd_mul_of_dvd_of_coprime hkd hcop, by push_cast; exact hy⟩
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (hcop.coprime_dvd_right hkd).symm
      (dvd_of_mem_divisors hk) (dvd_of_mem_divisors hm)

/-- The `k = gcd(d, l)` fibre of the bounding sum, for `k ∣ d`, is the inner
sum of the Selberg weight of `d` taken at `k`. -/
theorem gcd_fibre_sum_eq {d k : ℕ} (hdP : d ∣ s.prodPrimes) (hkd : k ∣ d)
    (hk : k ∈ divisors s.prodPrimes) :
    (∑ l ∈ divisors s.prodPrimes,
        if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0) =
      s.selbergTerms k *
        ∑ m ∈ divisors s.prodPrimes,
          if ((k : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0 := by
  calc (∑ l ∈ divisors s.prodPrimes,
        if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0)
      = ∑ m ∈ divisors s.prodPrimes,
          if k * m ∣ s.prodPrimes then
            (if k = d.gcd (k * m) ∧ ((k * m : ℕ) : ℝ) ^ 2 ≤ s.level then
              s.selbergTerms (k * m) else 0)
          else 0 := by
        apply sum_mul_subst k s.prodPrimes
        intro l _ hkl
        apply if_neg
        rintro ⟨hgcd, -⟩
        exact hkl (by rw [hgcd]; exact Nat.gcd_dvd_right d l)
    _ = ∑ m ∈ divisors s.prodPrimes,
          s.selbergTerms k *
            (if ((k : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0) := by
        refine sum_congr rfl fun m hm => ?_
        rw [← ite_and, mul_ite_zero]
        refine if_ctx_congr (gcd_fibre_iff s hdP hkd hk hm) (fun hc => ?_) fun _ => rfl
        have hkm : k.Coprime m := ((hc.2).coprime_dvd_right hkd).symm
        rw [selbergTerms_isMultiplicative.map_mul_of_coprime hkm]
    _ = s.selbergTerms k *
          ∑ m ∈ divisors s.prodPrimes,
            if ((k : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0 := by
        rw [mul_sum]

/-- The heart of the weight bound: `λ_d · μ(d) · S ≤ S`. -/
theorem selbergWeights_mul_mu_mul_le_selbergBoundingSum {d : ℕ} (hdP : d ∣ s.prodPrimes) :
    selbergWeights s d * μ d * selbergBoundingSum s ≤ selbergBoundingSum s := by
  have hd_ne : d ≠ 0 := ne_zero_of_dvd_ne_zero prodPrimes_ne_zero hdP
  calc selbergWeights s d * ↑(μ d) * selbergBoundingSum s
      = ∑ k ∈ divisors s.prodPrimes,
          if k ∣ d then
            s.selbergTerms k *
              ∑ m ∈ divisors s.prodPrimes,
                if ((d : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0
          else 0 := by
        have hmu : (μ d : ℝ) ^ 2 = 1 := by
          rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree
            (squarefree_of_dvd_prodPrimes hdP), Int.cast_one]
        calc selbergWeights s d * ↑(μ d) * selbergBoundingSum s
            = (s.nu d)⁻¹ * s.selbergTerms d * ((μ d : ℝ) ^ 2) *
                ((selbergBoundingSum s)⁻¹ * selbergBoundingSum s) *
                ∑ m ∈ divisors s.prodPrimes,
                  if ((d : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then
                    s.selbergTerms m else 0 := by
              unfold selbergWeights
              rw [if_pos hdP]
              ring
          _ = (∑ k ∈ divisors s.prodPrimes, if k ∣ d then s.selbergTerms k else 0) *
                ∑ m ∈ divisors s.prodPrimes,
                  if ((d : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then
                    s.selbergTerms m else 0 := by
              rw [hmu, inv_mul_cancel₀ (selbergBoundingSum_ne_zero s),
                sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP]
              ring
          _ = ∑ k ∈ divisors s.prodPrimes,
                if k ∣ d then
                  s.selbergTerms k *
                    ∑ m ∈ divisors s.prodPrimes,
                      if ((d : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then
                        s.selbergTerms m else 0
                else 0 := by
              rw [sum_mul]
              exact sum_congr rfl fun k _ => by rw [ite_zero_mul]
    _ ≤ ∑ k ∈ divisors s.prodPrimes,
          if k ∣ d then
            s.selbergTerms k *
              ∑ m ∈ divisors s.prodPrimes,
                if ((k : ℝ) * m) ^ 2 ≤ s.level ∧ m.Coprime d then s.selbergTerms m else 0
          else 0 := by
        apply sum_le_sum
        intro k _
        split_ifs with hkd
        swap
        · exact le_refl 0
        apply mul_le_mul_of_nonneg_left _ (selbergTerms_pos (hkd.trans hdP)).le
        apply sum_le_sum
        intro m hm
        split_ifs with h1 h2 h2
        · exact le_refl _
        · exfalso
          apply h2
          refine ⟨le_trans ?_ h1.1, h1.2⟩
          have hkd' : (k : ℝ) ≤ (d : ℝ) := by
            exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hd_ne) hkd
          have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          have hbase : (k : ℝ) * m ≤ (d : ℝ) * m := mul_le_mul_of_nonneg_right hkd' hm0
          have hk0 : (0 : ℝ) ≤ (k : ℝ) * m := mul_nonneg (Nat.cast_nonneg k) hm0
          exact pow_le_pow_left₀ hk0 hbase 2
        · exact (selbergTerms_pos (dvd_of_mem_divisors hm)).le
        · exact le_refl _
    _ = ∑ k ∈ divisors s.prodPrimes, ∑ l ∈ divisors s.prodPrimes,
          if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0 := by
        refine sum_congr rfl fun k hk => ?_
        by_cases hkd : k ∣ d
        swap
        · rw [if_neg hkd, eq_comm, Finset.sum_eq_zero]
          intro l _
          apply if_neg
          rintro ⟨hgcd, -⟩
          exact hkd (by rw [hgcd]; exact Nat.gcd_dvd_left d l)
        rw [if_pos hkd]
        exact (gcd_fibre_sum_eq s hdP hkd hk).symm
    _ = selbergBoundingSum s := by
        rw [sum_comm]
        calc (∑ l ∈ divisors s.prodPrimes, ∑ k ∈ divisors s.prodPrimes,
              if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0)
            = ∑ l ∈ divisors s.prodPrimes,
                if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0 := by
              refine sum_congr rfl fun l _ => ?_
              have hmem : d.gcd l ∈ divisors s.prodPrimes :=
                Nat.mem_divisors.mpr
                  ⟨(Nat.gcd_dvd_left d l).trans hdP, prodPrimes_ne_zero⟩
              calc (∑ k ∈ divisors s.prodPrimes,
                    if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0)
                  = ∑ k ∈ divisors s.prodPrimes,
                      if k = d.gcd l then
                        (if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0)
                      else 0 := by
                    refine sum_congr rfl fun k _ => ?_
                    rw [ite_and]
                _ = if (l : ℝ) ^ 2 ≤ s.level then s.selbergTerms l else 0 :=
                    Finset.sum_ite_eq_of_mem' _ _ _ hmem
          _ = selbergBoundingSum s := rfl

/-- The Selberg weights are bounded by `1` in absolute value. -/
theorem selberg_bound_weights (d : ℕ) : |selbergWeights s d| ≤ 1 := by
  by_cases hdP : d ∣ s.prodPrimes
  swap
  · rw [selbergWeights_eq_zero_of_not_dvd s hdP, abs_zero]
    exact zero_le_one
  have hle : selbergWeights s d * μ d ≤ 1 := by
    apply le_of_mul_le_mul_right _ (selbergBoundingSum_pos s)
    rw [one_mul]
    exact selbergWeights_mul_mu_mul_le_selbergBoundingSum s hdP
  calc |selbergWeights s d|
      = |selbergWeights s d| * |(μ d : ℝ)| := by
        rw [← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree
          (squarefree_of_dvd_prodPrimes hdP), Int.cast_one, mul_one]
    _ = |selbergWeights s d * μ d| := (abs_mul _ _).symm
    _ = selbergWeights s d * μ d := abs_of_nonneg (selbergWeights_mul_mu_nonneg s d hdP)
    _ ≤ 1 := hle

/-! ### Support of the Λ² coefficients -/

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {y : ℝ}
    (hw : ∀ d : ℕ, ¬(d : ℝ) ^ 2 ≤ y → w d = 0) {d : ℕ} (hd : ¬(d : ℝ) ≤ y)
    (d1 d2 : ℕ) (h : d = d1.lcm d2) (hle : d1 ≤ d2) : w d1 * w d2 = 0 := by
  by_cases hyp : (d2 : ℝ) ^ 2 ≤ y
  swap
  · rw [hw d2 hyp, mul_zero]
  exfalso
  apply hd
  have hy0 : (0 : ℝ) ≤ y := le_trans (sq_nonneg _) hyp
  rcases Nat.eq_zero_or_pos d1 with h0 | h1_pos
  · rw [h, h0, Nat.lcm_zero_left, Nat.cast_zero]
    exact hy0
  have h2_pos : 0 < d2 := lt_of_lt_of_le h1_pos hle
  have hdvd : d ∣ d1 * d2 := by
    rw [h]
    exact Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1)
  have hle_nat : d ≤ d1 * d2 := Nat.le_of_dvd (Nat.mul_pos h1_pos h2_pos) hdvd
  calc (d : ℝ) ≤ ((d1 * d2 : ℕ) : ℝ) := by exact_mod_cast hle_nat
    _ ≤ (d2 : ℝ) ^ 2 := by
        push_cast
        rw [sq]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (Nat.cast_nonneg d2)
    _ ≤ y := hyp

/-- Λ² coefficients built from weights supported on `d² ≤ y` are themselves
supported on `d ≤ y`. -/
theorem lambdaSquared_eq_zero_of_support (w : ℕ → ℝ) (y : ℝ)
    (hw : ∀ d : ℕ, ¬(d : ℝ) ^ 2 ≤ y → w d = 0) (d : ℕ) (hd : ¬(d : ℝ) ≤ y) :
    lambdaSquared w d = 0 := by
  unfold lambdaSquared
  apply Finset.sum_eq_zero
  intro d1 _
  apply Finset.sum_eq_zero
  intro d2 _
  split_ifs with h
  · rcases le_total d1 d2 with hle | hle
    · exact lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
    · rw [mul_comm]
      exact lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1
        (h.trans (Nat.lcm_comm d1 d2)) hle
  · rfl

theorem selbergMuPlus_eq_zero (d : ℕ) (hd : ¬(d : ℝ) ≤ s.level) : selbergMuPlus s d = 0 :=
  lambdaSquared_eq_zero_of_support (selbergWeights s) s.level
    (fun _ h => selbergWeights_eq_zero s _ h) d hd

/-! ### Counting divisor pairs by lcm: the `3^ω` bound -/

theorem cardDistinctFactors_eq_card_primeFactors (n : ℕ) : ω n = #n.primeFactors := by
  rw [ArithmeticFunction.cardDistinctFactors_apply]
  exact (List.card_toFinset _).symm

/-- For squarefree `n` and `d1 ∣ n`, the divisors `d2` of `n` with
`lcm(d1, d2) = n` are in bijection with the divisors of `d1` (namely
`d2 = a · (n/d1)` for `a ∣ d1`). -/
theorem card_lcm_fibre {n : ℕ} (hn : Squarefree n) {d1 : ℕ} (hd1 : d1 ∣ n) :
    #{d2 ∈ n.divisors | n = d1.lcm d2} = #d1.divisors := by
  have hn0 : n ≠ 0 := hn.ne_zero
  have hc : d1 * (n / d1) = n := Nat.mul_div_cancel' hd1
  set c := n / d1 with hc_def
  have hd10 : d1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hc
    exact hn0 hc.symm
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, mul_zero] at hc
    exact hn0 hc.symm
  have hcop : d1.Coprime c := coprime_of_squarefree_mul (by rw [hc]; exact hn)
  have hcd2 : ∀ d2 ∈ {d2 ∈ n.divisors | n = d1.lcm d2}, c ∣ d2 := by
    intro d2 hd2
    rw [mem_filter, Nat.mem_divisors] at hd2
    have hn_dvd : n ∣ d1 * d2 := by
      rw [hd2.2]
      exact Nat.lcm_dvd (dvd_mul_right d1 d2) (dvd_mul_left d2 d1)
    rw [← hc] at hn_dvd
    exact (mul_dvd_mul_iff_left hd10).mp hn_dvd
  apply Finset.card_bij' (fun d2 _ => d2 / c) (fun a _ => a * c)
  · -- maps into divisors d1
    intro d2 hd2
    have hcd := hcd2 d2 hd2
    rw [mem_filter, Nat.mem_divisors] at hd2
    have hd2n : d2 ∣ n := hd2.1.1
    rw [Nat.mem_divisors]
    refine ⟨?_, hd10⟩
    have : d2 / c * c ∣ d1 * c := by
      rw [Nat.div_mul_cancel hcd, hc]
      exact hd2n
    exact (mul_dvd_mul_iff_right hc0).mp this
  · -- maps into the fibre
    intro a ha
    rw [Nat.mem_divisors] at ha
    have hacn : a * c ∣ n := by
      rw [← hc]
      exact mul_dvd_mul_right ha.1 c
    rw [mem_filter, Nat.mem_divisors]
    refine ⟨⟨hacn, hn0⟩, ?_⟩
    apply Nat.dvd_antisymm
    · rw [← hc]
      apply hcop.mul_dvd_of_dvd_of_dvd (Nat.dvd_lcm_left d1 (a * c))
      exact (dvd_mul_left c a).trans (Nat.dvd_lcm_right _ _)
    · exact Nat.lcm_dvd hd1 hacn
  · -- left inverse
    intro d2 hd2
    exact Nat.div_mul_cancel (hcd2 d2 hd2)
  · -- right inverse
    intro a _
    exact Nat.mul_div_cancel a (Nat.pos_of_ne_zero hc0)

/-- The number of pairs of divisors of a squarefree `n` with lcm equal to
`n`, counted as an indicator double sum, is `3^ω(n)`: each prime of `n` must
divide the first component, the second, or both. -/
theorem sum_sum_ite_lcm_eq {n : ℕ} (hn : Squarefree n) :
    (∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (1 : ℝ) else 0) =
      3 ^ ω n := by
  calc (∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (1 : ℝ) else 0)
      = ∑ d1 ∈ n.divisors, ((ArithmeticFunction.sigma 0 d1 : ℕ) : ℝ) := by
        refine sum_congr rfl fun d1 hd1 => ?_
        rw [Finset.sum_boole, card_lcm_fibre hn (dvd_of_mem_divisors hd1),
          ArithmeticFunction.sigma_zero_apply]
    _ = ∑ d1 ∈ n.divisors,
          ((ArithmeticFunction.sigma 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) d1 := by
        exact sum_congr rfl fun d1 _ => by rw [ArithmeticFunction.natCoe_apply]
    _ = ∏ p ∈ n.primeFactors,
          (1 + ((ArithmeticFunction.sigma 0 : ArithmeticFunction ℕ) :
            ArithmeticFunction ℝ) p) :=
        (ArithmeticFunction.isMultiplicative_sigma.natCast.prodPrimeFactors_one_add_of_squarefree
          hn).symm
    _ = ∏ _p ∈ n.primeFactors, (3 : ℝ) := by
        refine prod_congr rfl fun p hp => ?_
        have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
        rw [ArithmeticFunction.natCoe_apply,
          show ArithmeticFunction.sigma 0 p = 2 by
            rw [← pow_one p, ArithmeticFunction.sigma_zero_apply_prime_pow hp']]
        norm_num
    _ = 3 ^ ω n := by
        rw [prod_const, cardDistinctFactors_eq_card_primeFactors]

/-- The Selberg Λ² coefficients are bounded by `3^ω`. -/
theorem selberg_bound_muPlus (n : ℕ) (hn : n ∈ divisors s.prodPrimes) :
    |selbergMuPlus s n| ≤ (3 : ℝ) ^ ω n := by
  calc |selbergMuPlus s n|
      = |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
          if n = d1.lcm d2 then selbergWeights s d1 * selbergWeights s d2 else 0| := rfl
    _ ≤ ∑ d1 ∈ n.divisors, |∑ d2 ∈ n.divisors,
          if n = d1.lcm d2 then selbergWeights s d1 * selbergWeights s d2 else 0| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
          |if n = d1.lcm d2 then selbergWeights s d1 * selbergWeights s d2 else 0| :=
        sum_le_sum fun d1 _ => abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, if n = d1.lcm d2 then (1 : ℝ) else 0 := by
        refine sum_le_sum fun d1 _ => sum_le_sum fun d2 _ => ?_
        rw [apply_ite abs, abs_zero]
        split_ifs
        · rw [abs_mul]
          exact mul_le_one₀ (selberg_bound_weights s d1) (abs_nonneg _)
            (selberg_bound_weights s d2)
        · exact le_refl 0
    _ = (3 : ℝ) ^ ω n := sum_sum_ite_lcm_eq (squarefree_of_mem_divisors_prodPrimes hn)

/-! ### The fundamental theorem -/

/-- The error term of the Selberg sieve: only levels `d ≤ y` contribute, and
each contributes at most `3^ω(d) · |R_d|`. -/
theorem selberg_bound_errSum :
    s.errSum (selbergMuPlus s) ≤
      ∑ d ∈ divisors s.prodPrimes,
        if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0 := by
  unfold errSum
  apply sum_le_sum
  intro d hd
  split_ifs with h
  · exact mul_le_mul_of_nonneg_right (selberg_bound_muPlus s d hd) (abs_nonneg _)
  · rw [selbergMuPlus_eq_zero s d h, abs_zero, zero_mul]

/-- **The fundamental theorem of the Selberg sieve.** The weight of the
elements of the support not divisible by any prime of `P` is at most
`X / S` plus an error controlled by the remainders `R_d = A_d - ν(d)·X` for
`d ∣ P` up to the level `y`:

  `siftedSum ≤ X / S + ∑_{d ∣ P, d ≤ y} 3^{ω(d)} · |R_d|`

where `S = ∑_{l ∣ P, l² ≤ y} g(l)` is the Selberg bounding sum. -/
theorem selberg_bound :
    s.siftedSum ≤
      s.totalMass / selbergBoundingSum s +
        ∑ d ∈ divisors s.prodPrimes,
          if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.rem d| else 0 := by
  calc s.siftedSum
      ≤ s.totalMass * s.mainSum (selbergMuPlus s) + s.errSum (selbergMuPlus s) :=
        siftedSum_le_mainSum_errSum_of_upperMoebius _ (upperMoebius_selbergMuPlus s)
    _ ≤ _ := by
        apply _root_.add_le_add
        · rw [mainSum_selbergMuPlus s, div_eq_mul_inv]
        · exact selberg_bound_errSum s

end

end Carmichael
