import Carmichael.TM.PrimTD
import Carmichael.TM.PrimList
import Carmichael.TM.Lists
import Carmichael.Algorithm

/-!
# Route T: steps 2 and 3 (`Alg.reservoir`, the `search` prelude, `Alg.poolAlg`, `Alg.scan`)

Machine fragments refining, EXACTLY, the Route A functions `Alg.resGo`,
`Alg.reservoir`, the step-2 tail of `Alg.search` (`len`, the `len < T` test,
`Q`, `L`, `x`), `Alg.poolGo`, `Alg.poolAlg` and `Alg.scan`
(`Carmichael/Algorithm.lean`).  Lists are `encList` in the Lean order, ℕ
results are `encodeNatΓ' value`, Bool results are in `St.flag`; every loop
keeps the Lean fuel counter on a stack and has the same control flow.

## Stack allocation (concrete)

The fragments of this file are written on CONCRETE stacks `0, …, 7`
(`K = Fin 8`): `resGo` and `scan` use all eight, so a parametrised version
would only be a permutation, and literal stacks let every distinctness side
condition be `by decide` in either orientation and every invariant list all
eight stacks explicitly.  Numbers are `encodeNatΓ' a ++ comma :: rest`, lists
`encList l ++ rest`; whatever sits BELOW a stated number/list is preserved,
so a caller may park its own data under any stack.

Step 2 (`resGoF`, `reservoirF`, `step2F`):

| stack | `resGoF` | `reservoirF` | `step2F` entry | `step2F` exit (success) |
|---|---|---|---|---|
| 0 | `y` (peeked) | `y` (peeked) | `z :: z99 :: y :: T :: θ :: r0` | `x :: θ :: r0` |
| 1 | `z99` (peeked) | `z99` (peeked) | `r1` | `z :: x :: r1` |
| 2 | `q` (counter) | scratch | `r2` | `1 :: r2` |
| 3 | `fuel` (counter) | `z` (consumed) | `r3` | `L :: r3` |
| 4 | scratch → result `encList res` | result | `r4` | `encList Q ++ r4` |
| 5 | open list (`bra :: r5` → `r5`) | scratch | `r5` | `r5` |
| 6, 7 | scratch | scratch | `r6`, `r7` | `r6`, `r7` |

Step 3 (`poolGoF`, `poolAlgF`, `scanF`):

| stack | `poolGoF` | `poolAlgF` | `scanF` |
|---|---|---|---|
| 0 | `x` (peeked) | `x` (peeked) | `x :: θ :: r0` (`θ` read by moving `x` aside) |
| 1 | `z` (peeked) | `z` (peeked) | `z :: fuel :: r1` (`fuel` read by moving `z` aside) |
| 2 | `k` (peeked) | `k` (peeked) | `k` (counter) |
| 3 | open list of kept primes | scratch | scratch |
| 4 | scratch | `encList Q` (restored) | `encList Q` (restored) |
| 5 | `encList ds` (consumed) | scratch (the divisor list) | scratch |
| 6 | scratch → result `encList P` | result | result `encList P` (success only) |
| 7 | `p = d k + 1` | scratch | scratch |

## Registers

`resGoF`: loop test `!flag`, `flag` set by `isZero` on the fuel at the end of
the body.  `scanF`: loop test `carry` ("continue"), result `flag`
("success"); both set by the `Frag.load'` ending every branch of the body.
`step2F`: `flag = decide (T ≤ len)`.  Nothing else is claimed about the final
state.

## Step bounds

All in the form `((Alg.f args).2 + 1) * B (…)` with `B` from `Cost.lean`;
the `(…)` are affine in the input bit bounds (`b` for the scale-sized
numbers, `bq` for the elements of `Q`) and recorded per fragment in the
docstrings.  Data-dependent loop bodies use the budget rules
`Frag.loop_runs_budget` (T3a) and `forEntriesN_runs_budget` (here).
-/

namespace Carmichael.TM

open Turing Turing.TM2 Turing.TM2.Stmt Computability

/-! ### Small helpers -/

/-- Two stack assignments agreeing on all eight stacks are equal. -/
theorem stacks_ext {S S' : Stacks} (h0 : S' 0 = S 0) (h1 : S' 1 = S 1) (h2 : S' 2 = S 2)
    (h3 : S' 3 = S 3) (h4 : S' 4 = S 4) (h5 : S' 5 = S 5) (h6 : S' 6 = S 6) (h7 : S' 7 = S 7) :
    S' = S := by
  funext k
  fin_cases k
  exacts [h0, h1, h2, h3, h4, h5, h6, h7]

theorem B_eight (m : ℕ) : 8 * B m = B (2 * m + 2) := by
  rw [show 8 = (1 + 1) ^ 3 by norm_num, B_scale]

theorem B_twentyseven (m : ℕ) : 27 * B m = B (3 * m + 4) := by
  rw [show 27 = (2 + 1) ^ 3 by norm_num, B_scale]

/-! ### Route A facts: `resGo`, `reservoir` -/

/-- The keep decision of one `resGo` iteration. -/
def resKeep (z99 y q : ℕ) : Bool :=
  if z99 < q then (Alg.isPrimeTD q).1 && (Alg.smoothTD y (q - 1)).1 else false

theorem resKeep_eq_true {z99 y q : ℕ} :
    resKeep z99 y q = true ↔
      z99 < q ∧ (Alg.isPrimeTD q).1 = true ∧ (Alg.smoothTD y (q - 1)).1 = true := by
  unfold resKeep; split_ifs with h <;> simp [h]

theorem resGo_zero (z99 y q : ℕ) : Alg.resGo z99 y q 0 = ([], 0) := rfl

theorem resGo_succ (z99 y q f : ℕ) :
    Alg.resGo z99 y q (f + 1) =
      ((if resKeep z99 y q then q :: (Alg.resGo z99 y (q + 1) f).1
          else (Alg.resGo z99 y (q + 1) f).1),
        (Alg.resGo z99 y (q + 1) f).2 + (Alg.isPrimeTD q).2 + (Alg.smoothTD y (q - 1)).2 + 1) :=
  rfl

/-- The first `i` iterations of `resGo` are `resGo … q i`; the rest start at
`q + i` with fuel `fuel - i`. -/
theorem resGo_shift (z99 y q fuel i : ℕ) (hi : i ≤ fuel) :
    (Alg.resGo z99 y q fuel).1 =
        (Alg.resGo z99 y q i).1 ++ (Alg.resGo z99 y (q + i) (fuel - i)).1 ∧
      (Alg.resGo z99 y q fuel).2 =
        (Alg.resGo z99 y q i).2 + (Alg.resGo z99 y (q + i) (fuel - i)).2 := by
  induction i generalizing q fuel with
  | zero => simp [resGo_zero]
  | succ i ih =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨h1, h2⟩ := ih (q + 1) f (by omega)
    rw [show q + (i + 1) = q + 1 + i by ring, show f + 1 - (i + 1) = f - i by omega]
    simp only [resGo_succ]
    constructor
    · split_ifs <;> simp [h1]
    · omega

theorem resGo_one (z99 y q : ℕ) :
    Alg.resGo z99 y q 1 = ((if resKeep z99 y q then [q] else []),
      (Alg.isPrimeTD q).2 + (Alg.smoothTD y (q - 1)).2 + 1) := by
  rw [resGo_succ, resGo_zero]; simp

theorem resGo_mem {z99 y q fuel p : ℕ} (h : p ∈ (Alg.resGo z99 y q fuel).1) :
    q ≤ p ∧ p < q + fuel ∧ z99 < p ∧ (Alg.isPrimeTD p).1 = true ∧
      (Alg.smoothTD y (p - 1)).1 = true := by
  induction fuel generalizing q with
  | zero => simp [resGo_zero] at h
  | succ f ih =>
    rw [resGo_succ] at h
    dsimp only at h
    by_cases hk : resKeep z99 y q = true
    · rw [if_pos hk, List.mem_cons] at h
      rcases h with rfl | h
      · obtain ⟨h1, h2, h3⟩ := resKeep_eq_true.1 hk
        exact ⟨le_rfl, by omega, h1, h2, h3⟩
      · obtain ⟨h1, h2, h3, h4, h5⟩ := ih h
        exact ⟨by omega, by omega, h3, h4, h5⟩
    · rw [if_neg hk] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih h
      exact ⟨by omega, by omega, h3, h4, h5⟩

theorem resGo_length_le_fuel (z99 y q fuel : ℕ) : (Alg.resGo z99 y q fuel).1.length ≤ fuel := by
  induction fuel generalizing q with
  | zero => simp [resGo_zero]
  | succ f ih =>
    rw [resGo_succ]; dsimp only
    have := ih (q + 1)
    split_ifs
    · simp only [List.length_cons]; omega
    · omega

theorem fuel_le_resGo_cost (z99 y q fuel : ℕ) : fuel ≤ (Alg.resGo z99 y q fuel).2 := by
  induction fuel generalizing q with
  | zero => simp
  | succ f ih => rw [resGo_succ]; dsimp only; have := ih (q + 1); omega

theorem resGo_length_le_cost (z99 y q fuel : ℕ) :
    (Alg.resGo z99 y q fuel).1.length ≤ (Alg.resGo z99 y q fuel).2 :=
  (resGo_length_le_fuel _ _ _ _).trans (fuel_le_resGo_cost _ _ _ _)

theorem isPrimeTD_cost_pos (m : ℕ) : 1 ≤ (Alg.isPrimeTD m).2 := by
  unfold Alg.isPrimeTD; split_ifs <;> simp

theorem smoothTD_cost_pos (y k : ℕ) : 1 ≤ (Alg.smoothTD y k).2 := by
  simp [Alg.smoothTD]

theorem reservoir_eq (z z99 y : ℕ) : Alg.reservoir z z99 y = Alg.resGo z99 y 2 (z - 1) := rfl

theorem reservoir_mem {z z99 y p : ℕ} (h : p ∈ (Alg.reservoir z z99 y).1) :
    2 ≤ p ∧ p ≤ z ∧ z99 < p ∧ (Alg.isPrimeTD p).1 = true ∧
      (Alg.smoothTD y (p - 1)).1 = true := by
  rw [reservoir_eq] at h
  obtain ⟨h1, h2, h3, h4, h5⟩ := resGo_mem h
  exact ⟨h1, by omega, h3, h4, h5⟩

theorem reservoir_length_le_cost (z z99 y : ℕ) :
    (Alg.reservoir z z99 y).1.length ≤ (Alg.reservoir z z99 y).2 :=
  resGo_length_le_cost _ _ _ _

theorem reservoir_length_lt (z z99 y : ℕ) (hz : 1 ≤ z) :
    (Alg.reservoir z z99 y).1.length < z := by
  have := resGo_length_le_fuel z99 y 2 (z - 1)
  rw [reservoir_eq]; omega

/-! ### `resGo`: the reservoir loop

Stacks: `y` on `0` (peeked), `z99` on `1` (peeked), `q` on `2`, `fuel` on `3`,
the open list of kept `q`s on `5`; scratch `4`, `6`, `7`.  One iteration:
`keepF` computes `flag := resKeep z99 y q` (`z99 < q` by `cmpFrag` on copies;
if so `isPrimeTDF q`; if prime, `smoothTDF y (q - 1)` on a decremented copy
of `q`), `resTestF` pushes `q` on the open list iff the flag is set, and the
body ends with `incr q`, `predNum fuel`, `isZero fuel` (loop test `!flag`).
The tests are short-circuited (the Lean function evaluates both; the result
is the same and the machine only gets cheaper). -/

/-- `flag := resKeep z99 y q`; all stacks restored.  Uses `1 6 7` for the
comparison copies, `isPrimeTDF 2 4 6 7 3 1`, `smoothTDF 0 6 4 7 1 2 3`. -/
def keepF : Frag :=
  (dup 1 6 7).seq ((dup 2 7 6).seq ((cmpFrag 6 7).seq
    (Frag.ite (fun v => decide (v.cmp = .lt))
      ((isPrimeTDF 2 4 6 7 3 1).seq
        (Frag.ite (fun v => v.flag)
          ((dup 2 6 7).seq ((predNum 6 7).seq (smoothTDF 0 6 4 7 1 2 3)))
          Frag.skip))
      (Frag.load' (fun v => { v with flag := false })))))

theorem keepF_runs (z99 y q' b : ℕ) (hb : 2 ≤ b) (hz : z99 < 2 ^ b) (hy : y < 2 ^ b)
    (hq : q' < 2 ^ b) (r0 r1 r2 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' y ++ .comma :: r0) (h1 : S 1 = encodeNatΓ' z99 ++ .comma :: r1)
    (h2 : S 2 = encodeNatΓ' q' ++ .comma :: r2) :
    keepF.Runs v S (fun v' S' => v'.flag = resKeep z99 y q' ∧ S' = S)
      (((Alg.isPrimeTD q').2 + 1) * B (3 * b + 7) +
        ((Alg.smoothTD y (q' - 1)).2 + 1) * B (4 * b + 10) + 5 * B b + 2) := by
  have hB1 := one_le_B b
  have hlq := log_le_of_lt_pow hq
  have hlz := log_le_of_lt_pow hz
  have hlin : 8 * b + 40 ≤ B b := le_B_of_le_linear (by omega)
  have hP1 : 1 ≤ ((Alg.isPrimeTD q').2 + 1) * B (3 * b + 7) :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by have := one_le_B (3 * b + 7); omega))
  have hS1 : 1 ≤ ((Alg.smoothTD y (q' - 1)).2 + 1) * B (4 * b + 10) :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by have := one_le_B (4 * b + 10); omega))
  obtain ⟨P, hP⟩ : ∃ P, ((Alg.isPrimeTD q').2 + 1) * B (3 * b + 7) = P := ⟨_, rfl⟩
  obtain ⟨SM, hSM⟩ : ∃ SM, ((Alg.smoothTD y (q' - 1)).2 + 1) * B (4 * b + 10) = SM := ⟨_, rfl⟩
  rw [hP] at hP1 ⊢
  rw [hSM] at hS1 ⊢
  -- stage 1: dup 1 6 7 : 6 := z99
  have ha := dup_le_B (x := 1) (y := 6) (s := 7) (by decide) (by decide) (by decide) z99 b hz r1 v S h1
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B b + (P + (2 * B b + SM + 1) + 1)) ha
    fun v₁ S₁ ⟨h1₁, h6₁, h7₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 2: dup 2 7 6 : 7 := q'
  have h2₁ : S₁ 2 = encodeNatΓ' q' ++ .comma :: r2 := by
    rw [hF₁ 2 (by decide) (by decide) (by decide), h2]
  have hb2 := dup_le_B (x := 2) (y := 7) (s := 6) (by decide) (by decide) (by decide) q' b hq r2 v₁ S₁ h2₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + (P + (2 * B b + SM + 1) + 1)) hb2
    fun v₂ S₂ ⟨h2₂, h7₂, h6₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: cmpFrag 6 7 : cmp := compare z99 q'
  have h6₂' : S₂ 6 = encodeNatΓ' z99 ++ .comma :: S 6 := by rw [h6₂, h6₁]
  have h7₂' : S₂ 7 = encodeNatΓ' q' ++ .comma :: S 7 := by rw [h7₂, h7₁]
  have hc := cmp_correct (x := 6) (y := 7) (by decide) z99 q' (S 6) (S 7) v₂ S₂ h6₂' h7₂'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := P + (2 * B b + SM + 1) + 1) hc
    fun v₃ S₃ ⟨hcmp₃, h6₃, h7₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  have hS₃ : S₃ = S := by
    refine stacks_ext ?_ ?_ ?_ ?_ ?_ ?_ h6₃ h7₃
    · rw [hF₃ 0 (by decide) (by decide), hF₂ 0 (by decide) (by decide) (by decide),
        hF₁ 0 (by decide) (by decide) (by decide)]
    · rw [hF₃ 1 (by decide) (by decide), hF₂ 1 (by decide) (by decide) (by decide), h1₁]
    · rw [hF₃ 2 (by decide) (by decide), h2₂, h2₁, h2]
    · rw [hF₃ 3 (by decide) (by decide), hF₂ 3 (by decide) (by decide) (by decide),
        hF₁ 3 (by decide) (by decide) (by decide)]
    · rw [hF₃ 4 (by decide) (by decide), hF₂ 4 (by decide) (by decide) (by decide),
        hF₁ 4 (by decide) (by decide) (by decide)]
    · rw [hF₃ 5 (by decide) (by decide), hF₂ 5 (by decide) (by decide) (by decide),
        hF₁ 5 (by decide) (by decide) (by decide)]
  -- stage 4: branch on `z99 < q'`
  refine Frag.runs_mono (Frag.ite_runs (t := P + (2 * B b + SM + 1)) (fun hlt => ?_) (fun hlt => ?_))
    (fun _ _ h => h) le_rfl
  · have hlt' : z99 < q' := by simpa [hcmp₃, compare_lt_iff_lt] using hlt
    -- isPrimeTDF 2 4 6 7 3 1
    have hp := isPrimeTDF_le_B (xm := 2) (xd := 4) (xf := 6) (s := 7) (t := 3) (u := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      q' b hq r2 v₃ S₃ (by rw [hS₃, h2])
    rw [hP] at hp
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B b + SM + 1) hp
      fun v₄ S₄ ⟨hfl₄, h2₄, h4₄, h6₄, h7₄, h3₄, h1₄, hF₄⟩ => ?_) (fun _ _ h => h) le_rfl
    have hS₄ : S₄ = S := by
      rw [← hS₃]
      exact stacks_ext (hF₄ 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        h1₄ h2₄ h3₄ h4₄ (hF₄ 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        h6₄ h7₄
    refine Frag.ite_runs (t := 2 * B b + SM) (fun hpr => ?_) (fun hpr => ?_)
    · have hpr' : (Alg.isPrimeTD q').1 = true := by rw [← hfl₄]; exact hpr
      -- dup 2 6 7 : 6 := q'
      have hd := dup_le_B (x := 2) (y := 6) (s := 7) (by decide) (by decide) (by decide) q' b hq r2 v₄ S₄
        (by rw [hS₄, h2])
      refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + SM) hd
        fun v₅ S₅ ⟨h2₅, h6₅, h7₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
      -- predNum 6 7 : 6 := q' - 1
      have hpd := predNum_correct' (x := 6) (s := 7) (by decide) q' (S₄ 6) v₅ S₅ h6₅
      refine Frag.runs_mono (Frag.seq_runs (t₂ := SM) hpd
        fun v₆ S₆ ⟨_, _, h6₆, h7₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
      -- smoothTDF 0 6 4 7 1 2 3
      have h0₆ : S₆ 0 = encodeNatΓ' y ++ .comma :: r0 := by
        rw [hF₆ 0 (by decide) (by decide), hF₅ 0 (by decide) (by decide) (by decide), hS₄, h0]
      have h6₆' : S₆ 6 = encodeNatΓ' (q' - 1) ++ .comma :: S 6 := by rw [h6₆, hS₄]
      have hsm := smoothTDF_le_B (xy := 0) (xr := 6) (xd := 4) (xf := 7) (s := 1) (t := 2) (u := 3)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)
        y (q' - 1) b hb hy (by omega) r0 (S 6) v₆ S₆ h0₆ h6₆'
      rw [hSM] at hsm
      refine Frag.runs_mono hsm (fun v₇ S₇ ⟨hfl₇, h0₇, h6₇, h4₇, h7₇, h1₇, h2₇, h3₇, hF₇⟩ => ⟨?_, ?_⟩)
        le_rfl
      · rw [hfl₇]; simp [resKeep, hlt', hpr']
      · refine stacks_ext ?_ ?_ ?_ ?_ ?_ ?_ h6₇ ?_
        · rw [h0₇, h0₆, h0]
        · rw [h1₇, hF₆ 1 (by decide) (by decide), hF₅ 1 (by decide) (by decide) (by decide), hS₄]
        · rw [h2₇, hF₆ 2 (by decide) (by decide), h2₅, hS₄]
        · rw [h3₇, hF₆ 3 (by decide) (by decide), hF₅ 3 (by decide) (by decide) (by decide), hS₄]
        · rw [h4₇, hF₆ 4 (by decide) (by decide), hF₅ 4 (by decide) (by decide) (by decide), hS₄]
        · rw [hF₇ 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            hF₆ 5 (by decide) (by decide), hF₅ 5 (by decide) (by decide) (by decide), hS₄]
        · rw [h7₇, h7₆, h7₅, hS₄]
    · have hpr' : (Alg.isPrimeTD q').1 = false := by rw [← hfl₄]; exact hpr
      refine Frag.runs_mono (Frag.skip_runs v₄ S₄) (fun v' S' ⟨hv', hS'⟩ => ⟨?_, ?_⟩) (by omega)
      · rw [hv', hfl₄, hpr']; simp [resKeep, hlt', hpr']
      · rw [hS', hS₄]
  · have hlt' : ¬ z99 < q' := by simpa [hcmp₃, compare_lt_iff_lt] using hlt
    refine Frag.runs_mono (Frag.load'_runs _ v₃ S₃) (fun v' S' ⟨hv', hS'⟩ => ⟨?_, ?_⟩) (by omega)
    · rw [hv']; simp [resKeep, hlt']
    · rw [hS', hS₃]

/-- Push `q` on the open list on `5` iff `resKeep z99 y q`. -/
def resTestF : Frag := keepF.seq (Frag.ite (fun v => v.flag) (dup 2 5 6) Frag.skip)

theorem resTestF_runs (z99 y q' b : ℕ) (hb : 2 ≤ b) (hz : z99 < 2 ^ b) (hy : y < 2 ^ b)
    (hq : q' < 2 ^ b) (r0 r1 r2 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' y ++ .comma :: r0) (h1 : S 1 = encodeNatΓ' z99 ++ .comma :: r1)
    (h2 : S 2 = encodeNatΓ' q' ++ .comma :: r2) :
    resTestF.Runs v S (fun _ S' =>
        S' 0 = S 0 ∧ S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = S 3 ∧ S' 4 = S 4 ∧
        S' 5 = (if resKeep z99 y q' then encodeNatΓ' q' ++ .comma :: S 5 else S 5) ∧
        S' 6 = S 6 ∧ S' 7 = S 7)
      (((Alg.isPrimeTD q').2 + 1) * B (3 * b + 7) +
        ((Alg.smoothTD y (q' - 1)).2 + 1) * B (4 * b + 10) + 6 * B b + 3) := by
  have hB1 := one_le_B b
  have hk := keepF_runs z99 y q' b hb hz hy hq r0 r1 r2 v S h0 h1 h2
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + 1) hk fun v₁ S₁ ⟨hfl₁, hS₁⟩ => ?_)
    (fun _ _ h => h) (by omega)
  rw [hS₁]
  refine Frag.ite_runs (t := B b) (fun hc => ?_) (fun hc => ?_)
  · have hkeep : resKeep z99 y q' = true := by rw [← hfl₁]; exact hc
    have hd := dup_le_B (x := 2) (y := 5) (s := 6) (by decide) (by decide) (by decide) q' b hq r2 v₁ S h2
    refine Frag.runs_mono hd (fun _ S' ⟨h2', h5', h6', hF'⟩ => ?_) le_rfl
    rw [if_pos hkeep]
    exact ⟨hF' 0 (by decide) (by decide) (by decide), hF' 1 (by decide) (by decide) (by decide), h2',
      hF' 3 (by decide) (by decide) (by decide), hF' 4 (by decide) (by decide) (by decide), h5', h6',
      hF' 7 (by decide) (by decide) (by decide)⟩
  · have hkeep : resKeep z99 y q' = false := by rw [← hfl₁]; exact hc
    refine Frag.runs_mono (Frag.skip_runs v₁ S) (fun _ S' ⟨_, hS'⟩ => ?_) (by omega)
    rw [hS', if_neg (by simp [hkeep])]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- One iteration of `resGo`: the test, then `incr q`, `predNum fuel`, `isZero fuel`. -/
def resGoBody : Frag :=
  resTestF.seq ((incr 2 6).seq ((predNum 3 6).seq (isZero 3 6)))

/-- `resGo z99 y q fuel` on the machine (see the section header); the open
list must be `bra :: r5` on `5` at entry; the result `encList (Alg.resGo …).1`
is pushed on `4` (`revList` at the end), `5` is popped back to `r5`. -/
def resGoF : Frag :=
  (isZero 3 6).seq ((Frag.loop (fun v => !v.flag) resGoBody).seq (revList 5 4 6))

/-- Loop invariant of `resGoF` after `i` iterations with remaining budget `β`. -/
def RGInv (z99 y q fuel b : ℕ) (r0 r1 r2 r3 r5 : List Γ') (S₀ : Stacks)
    (i β : ℕ) (v : St) (S : Stacks) : Prop :=
  i ≤ fuel ∧
  S 0 = encodeNatΓ' y ++ .comma :: r0 ∧ S 1 = encodeNatΓ' z99 ++ .comma :: r1 ∧
  S 2 = encodeNatΓ' (q + i) ++ .comma :: r2 ∧ S 3 = encodeNatΓ' (fuel - i) ++ .comma :: r3 ∧
  S 4 = S₀ 4 ∧ S 5 = encList (Alg.resGo z99 y q i).1.reverse ++ r5 ∧ S 6 = S₀ 6 ∧ S 7 = S₀ 7 ∧
  v.flag = decide (fuel - i = 0) ∧
  β = (Alg.resGo z99 y (q + i) (fuel - i)).2 * (8 * B (4 * b + 10))

theorem resGoBody_runs (z99 y q fuel b : ℕ) (hb : 2 ≤ b) (hz : z99 < 2 ^ b) (hy : y < 2 ^ b)
    (hqf : q + fuel < 2 ^ b) (r0 r1 r2 r3 r5 : List Γ') (S₀ : Stacks) (i : ℕ) (hi : i < fuel)
    (β : ℕ) (v : St) (S : Stacks) (hI : RGInv z99 y q fuel b r0 r1 r2 r3 r5 S₀ i β v S) :
    ∃ t β', t + 1 + β' ≤ β ∧
      resGoBody.Runs v S (RGInv z99 y q fuel b r0 r1 r2 r3 r5 S₀ (i + 1) β') t := by
  obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7, -, hβ⟩ := hI
  obtain ⟨f, hf⟩ : ∃ f, fuel - i = f + 1 := ⟨fuel - i - 1, by omega⟩
  rw [hf] at h3 hβ
  have hfi : fuel - (i + 1) = f := by omega
  have hq' : q + i < 2 ^ b := by omega
  have hf1 : f + 1 < 2 ^ b := by omega
  have hB1 := one_le_B b
  have hX1 := one_le_B (4 * b + 10)
  have hBb : B b ≤ B (4 * b + 10) := B_mono (by omega)
  have hB37 : B (3 * b + 7) ≤ B (4 * b + 10) := B_mono (by omega)
  have hpr := isPrimeTD_cost_pos (q + i)
  obtain ⟨X, hX⟩ : ∃ X, B (4 * b + 10) = X := ⟨_, rfl⟩
  rw [hX] at hβ hX1 hBb hB37
  obtain ⟨a, ha⟩ : ∃ a, (Alg.isPrimeTD (q + i)).2 = a := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, (Alg.smoothTD y (q + i - 1)).2 = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, (Alg.resGo z99 y (q + i + 1) f).2 = d := ⟨_, rfl⟩
  rw [ha] at hpr
  refine ⟨(a + 1) * B (3 * b + 7) + (c + 1) * X + 6 * B b + 3 + 3 * B b, d * (8 * X), ?_, ?_⟩
  · -- the budget
    rw [hβ, resGo_succ]
    dsimp only
    rw [ha, hc, hd]
    have e1 : (a + 1) * B (3 * b + 7) ≤ (a + 1) * X := Nat.mul_le_mul_left _ hB37
    have e2 : 1 * X ≤ a * X := Nat.mul_le_mul_right X hpr
    nlinarith
  · -- the machine
    have hT := resTestF_runs z99 y (q + i) b hb hz hy hq' r0 r1 r2 v S h0 h1 h2
    rw [ha, hc, hX] at hT
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * B b) hT
      fun v₁ S₁ ⟨h0₁, h1₁, h2₁, h3₁, h4₁, h5₁, h6₁, h7₁⟩ => ?_) (fun _ _ h => h) (by omega)
    -- incr 2 6
    have hI := incr_le_B (y := 2) (s := 6) (by decide) (q + i) b hq' r2 v₁ S₁ (by rw [h2₁, h2])
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B b) hI
      fun v₂ S₂ ⟨_, _, _, h2₂, h6₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
    -- predNum 3 6
    have h3₂ : S₂ 3 = encodeNatΓ' (f + 1) ++ .comma :: r3 := by
      rw [hF₂ 3 (by decide) (by decide), h3₁, h3]
    have hPd := predNum_le_B (x := 3) (s := 6) (by decide) (f + 1) b (by omega) hf1 r3 v₂ S₂ h3₂
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B b) hPd
      fun v₃ S₃ ⟨_, _, h3₃, h6₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
    rw [Nat.add_sub_cancel] at h3₃
    -- isZero 3 6
    have hZ := isZero_le_B (x := 3) (s := 6) (by decide) f b (by omega) r3 v₃ S₃ h3₃
    refine Frag.runs_mono hZ (fun v₄ S₄ ⟨hfl₄, _, h3₄, h6₄, hF₄⟩ => ?_) le_rfl
    refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hF₄ 0 (by decide) (by decide), hF₃ 0 (by decide) (by decide), hF₂ 0 (by decide) (by decide),
        h0₁, h0]
    · rw [hF₄ 1 (by decide) (by decide), hF₃ 1 (by decide) (by decide), hF₂ 1 (by decide) (by decide),
        h1₁, h1]
    · rw [hF₄ 2 (by decide) (by decide), hF₃ 2 (by decide) (by decide), h2₂, Nat.add_assoc]
    · rw [h3₄, h3₃, hfi]
    · rw [hF₄ 4 (by decide) (by decide), hF₃ 4 (by decide) (by decide), hF₂ 4 (by decide) (by decide),
        h4₁, h4]
    · rw [hF₄ 5 (by decide) (by decide), hF₃ 5 (by decide) (by decide), hF₂ 5 (by decide) (by decide),
        h5₁, h5]
      obtain ⟨hs, -⟩ := resGo_shift z99 y q (i + 1) i (by omega)
      rw [Nat.add_sub_cancel_left] at hs
      rw [hs, resGo_one]
      dsimp only
      split_ifs <;> simp [encList_cons]
    · rw [h6₄, h6₃, h6₂, h6₁, h6]
    · rw [hF₄ 7 (by decide) (by decide), hF₃ 7 (by decide) (by decide), hF₂ 7 (by decide) (by decide),
        h7₁, h7]
    · rw [hfl₄, hfi]
    · rw [hfi, ← Nat.add_assoc, hd, hX]

theorem resGoF_runs (z99 y q fuel b : ℕ) (hb : 2 ≤ b) (hz : z99 < 2 ^ b) (hy : y < 2 ^ b)
    (hqf : q + fuel < 2 ^ b) (r0 r1 r2 r3 r5 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' y ++ .comma :: r0) (h1 : S 1 = encodeNatΓ' z99 ++ .comma :: r1)
    (h2 : S 2 = encodeNatΓ' q ++ .comma :: r2) (h3 : S 3 = encodeNatΓ' fuel ++ .comma :: r3)
    (h5 : S 5 = .bra :: r5) :
    resGoF.Runs v S (fun _ S' =>
        S' 0 = S 0 ∧ S' 1 = S 1 ∧ S' 2 = encodeNatΓ' (q + fuel) ++ .comma :: r2 ∧
        S' 3 = encodeNatΓ' 0 ++ .comma :: r3 ∧
        S' 4 = encList (Alg.resGo z99 y q fuel).1 ++ S 4 ∧ S' 5 = r5 ∧ S' 6 = S 6 ∧ S' 7 = S 7)
      (((Alg.resGo z99 y q fuel).2 + 1) * (11 * B (4 * b + 10))) := by
  have hfb : fuel < 2 ^ b := by omega
  have hB1 := one_le_B b
  have hBb : B b ≤ B (4 * b + 10) := B_mono (by omega)
  have hlen := resGo_length_le_cost z99 y q fuel
  obtain ⟨n, hn⟩ : ∃ n, (Alg.resGo z99 y q fuel).2 = n := ⟨_, rfl⟩
  obtain ⟨len, hl⟩ : ∃ len, (Alg.resGo z99 y q fuel).1.length = len := ⟨_, rfl⟩
  rw [hn, hl] at hlen
  rw [hn]
  -- stage 1: isZero 3 6
  have hZ := isZero_le_B (x := 3) (s := 6) (by decide) fuel b hfb r3 v S h3
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := n * (8 * B (4 * b + 10)) + 1 + (len + 1) * B b) hZ
    fun v₁ S₁ ⟨hfl₁, _, h3₁, h6₁, hF₁⟩ => ?_) (fun _ _ h => h) ?_
  swap
  · have := Nat.mul_le_mul (Nat.add_le_add_right hlen 1) hBb
    nlinarith
  -- stage 2: the loop
  have hI0 : RGInv z99 y q fuel b r0 r1 r2 r3 r5 S 0 (n * (8 * B (4 * b + 10))) v₁ S₁ :=
    ⟨Nat.zero_le _, by rw [hF₁ 0 (by decide) (by decide), h0],
      by rw [hF₁ 1 (by decide) (by decide), h1],
      by rw [hF₁ 2 (by decide) (by decide), h2, Nat.add_zero], by rw [h3₁, h3, Nat.sub_zero],
      hF₁ 4 (by decide) (by decide), by rw [hF₁ 5 (by decide) (by decide), h5, resGo_zero]; rfl,
      h6₁, hF₁ 7 (by decide) (by decide), by rw [hfl₁, Nat.sub_zero],
      by simp [hn]⟩
  have hloop := Frag.loop_runs_budget (c := fun v => !v.flag) (B := resGoBody)
    (RGInv z99 y q fuel b r0 r1 r2 r3 r5 S) fuel (n * (8 * B (4 * b + 10))) (v := v₁) (S := S₁) hI0
    (fun i hi β w T ⟨_, _, _, _, _, _, _, _, _, hfl, _⟩ => by
      have : fuel - i ≠ 0 := by omega
      simp [hfl, this])
    (fun β w T ⟨_, _, _, _, _, _, _, _, _, hfl, _⟩ => by simp [hfl])
    (fun i hi β w T hI => resGoBody_runs z99 y q fuel b hb hz hy hqf r0 r1 r2 r3 r5 S i hi β w T hI)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (len + 1) * B b) hloop
    fun v₂ S₂ ⟨⟨β, _, h0₂, h1₂, h2₂, h3₂, h4₂, h5₂, h6₂, h7₂, _, _⟩, _⟩ => ?_) (fun _ _ h => h)
    (by omega)
  -- stage 3: revList 5 4 6
  rw [Nat.sub_self] at h3₂
  have hmem : ∀ a ∈ (Alg.resGo z99 y q fuel).1.reverse, a < 2 ^ b := by
    intro a ha
    rw [List.mem_reverse] at ha
    have := resGo_mem ha
    omega
  have hR := revList_le_B (x := 5) (y := 4) (s := 6) (by decide) (by decide) (by decide) _ b hmem r5
    v₂ S₂ h5₂
  refine Frag.runs_mono hR (fun _ S₃ ⟨h5₃, h4₃, h6₃, hF₃⟩ => ?_)
    (by simp only [List.length_reverse, hl]; exact le_rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_, h5₃, ?_, ?_⟩
  · rw [hF₃ 0 (by decide) (by decide) (by decide), h0₂, h0]
  · rw [hF₃ 1 (by decide) (by decide) (by decide), h1₂, h1]
  · rw [hF₃ 2 (by decide) (by decide) (by decide), h2₂]
  · rw [hF₃ 3 (by decide) (by decide) (by decide), h3₂]
  · rw [h4₃, h4₂, List.reverse_reverse]
  · rw [h6₃, h6₂]
  · rw [hF₃ 7 (by decide) (by decide) (by decide), h7₂]

/-- `resGoF` in `B`-form: `((Alg.resGo z99 y q fuel).2 + 1) * B (12 b + 34)`
for `z99, y, q + fuel < 2 ^ b`, `2 ≤ b`. -/
theorem resGoF_le_B (z99 y q fuel b : ℕ) (hb : 2 ≤ b) (hz : z99 < 2 ^ b) (hy : y < 2 ^ b)
    (hqf : q + fuel < 2 ^ b) (r0 r1 r2 r3 r5 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' y ++ .comma :: r0) (h1 : S 1 = encodeNatΓ' z99 ++ .comma :: r1)
    (h2 : S 2 = encodeNatΓ' q ++ .comma :: r2) (h3 : S 3 = encodeNatΓ' fuel ++ .comma :: r3)
    (h5 : S 5 = .bra :: r5) :
    resGoF.Runs v S (fun _ S' =>
        S' 0 = S 0 ∧ S' 1 = S 1 ∧ S' 2 = encodeNatΓ' (q + fuel) ++ .comma :: r2 ∧
        S' 3 = encodeNatΓ' 0 ++ .comma :: r3 ∧
        S' 4 = encList (Alg.resGo z99 y q fuel).1 ++ S 4 ∧ S' 5 = r5 ∧ S' 6 = S 6 ∧ S' 7 = S 7)
      (((Alg.resGo z99 y q fuel).2 + 1) * B (12 * b + 34)) := by
  refine Frag.runs_mono (resGoF_runs z99 y q fuel b hb hz hy hqf r0 r1 r2 r3 r5 v S h0 h1 h2 h3 h5)
    (fun _ _ h => h) ?_
  rw [show 12 * b + 34 = 3 * (4 * b + 10) + 4 by ring, ← B_twentyseven]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by norm_num))

/-! ### `reservoir` -/

/-- `reservoir z z99 y`: `z` on `3` (consumed), `z99` on `1`, `y` on `0`
(both peeked); the list `encList (Alg.reservoir z z99 y).1` is pushed on `4`;
`2`, `5`, `6`, `7` are scratch (restored). -/
def reservoirF : Frag :=
  (predNum 3 6).seq ((pushNum 2 2).seq ((Frag.pushSym 5 .bra).seq
    (resGoF.seq ((dropNum 2).seq (dropNum 3)))))

theorem reservoirF_runs (z z99 y b : ℕ) (hb : 2 ≤ b) (hz : z < 2 ^ b) (hz99 : z99 < 2 ^ b)
    (hy : y < 2 ^ b) (r0 r1 r3 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' y ++ .comma :: r0) (h1 : S 1 = encodeNatΓ' z99 ++ .comma :: r1)
    (h3 : S 3 = encodeNatΓ' z ++ .comma :: r3) :
    reservoirF.Runs v S (fun _ S' =>
        S' 0 = S 0 ∧ S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = r3 ∧
        S' 4 = encList (Alg.reservoir z z99 y).1 ++ S 4 ∧ S' 5 = S 5 ∧ S' 6 = S 6 ∧ S' 7 = S 7)
      (((Alg.reservoir z z99 y).2 + 1) * (11 * B (4 * b + 14)) + 3 * B (4 * b + 14) + 7) := by
  have hB1 := one_le_B b
  have hBb : B b ≤ B (4 * b + 14) := B_mono (by omega)
  have hBb1 : B (b + 1) ≤ B (4 * b + 14) := B_mono (by omega)
  have hlz := log_le_of_lt_pow hz
  have hl2 : Nat.log 2 2 ≤ 2 := log_le_of_lt_pow (by norm_num)
  have hl0 : Nat.log 2 0 = 0 := Nat.log_zero_right 2
  have hlin : 4 * b + 40 ≤ B b := le_B_of_le_linear (by omega)
  have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
  have h4 : 4 ≤ 2 ^ b := by
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hb
    simpa using this
  rw [reservoir_eq]
  obtain ⟨n, hn⟩ : ∃ n, (Alg.resGo z99 y 2 (z - 1)).2 = n := ⟨_, rfl⟩
  rw [hn]
  -- stage 1: predNum 3 6 : 3 := z - 1
  have hp := predNum_correct' (x := 3) (s := 6) (by decide) z r3 v S h3
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (Nat.log 2 2 + 2) + 1 + (n + 1) * (11 * B (4 * b + 14)) + B (b + 1) + (Nat.log 2 0 + 2))
    hp fun v₁ S₁ ⟨_, _, h3₁, h6₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 2: pushNum 2 2
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := 1 + (n + 1) * (11 * B (4 * b + 14)) + B (b + 1) + (Nat.log 2 0 + 2))
    (pushNum_runs 2 2 v₁ S₁) fun v₂ S₂ ⟨hv₂, h2₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: pushSym 5 bra
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (n + 1) * (11 * B (4 * b + 14)) + B (b + 1) + (Nat.log 2 0 + 2))
    (Frag.pushSym_runs 5 .bra v₂ S₂) fun v₃ S₃ ⟨hv₃, hS₃⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₃]; subst hS₃
  -- stage 4: resGoF at b + 1
  have h0₂ : S₂ 0 = encodeNatΓ' y ++ .comma :: r0 := by
    rw [hF₂ 0 (by decide), hF₁ 0 (by decide) (by decide), h0]
  have h1₂ : S₂ 1 = encodeNatΓ' z99 ++ .comma :: r1 := by
    rw [hF₂ 1 (by decide), hF₁ 1 (by decide) (by decide), h1]
  have h2₂' : S₂ 2 = encodeNatΓ' 2 ++ .comma :: S 2 := by
    rw [h2₂, hF₁ 2 (by decide) (by decide)]
  have h3₂ : S₂ 3 = encodeNatΓ' (z - 1) ++ .comma :: r3 := by rw [hF₂ 3 (by decide), h3₁]
  have hg := resGoF_runs z99 y 2 (z - 1) (b + 1) (by omega) (lt_pow_succ hz99) (lt_pow_succ hy)
    (by omega) r0 r1 (S 2) r3 (S₂ 5) v₂ (Function.update S₂ 5 (Γ'.bra :: S₂ 5))
    (by rw [Function.update_of_ne (by decide), h0₂]) (by rw [Function.update_of_ne (by decide), h1₂])
    (by rw [Function.update_of_ne (by decide), h2₂']) (by rw [Function.update_of_ne (by decide), h3₂])
    (by rw [Function.update_self])
  rw [show 4 * (b + 1) + 10 = 4 * b + 14 by ring, hn] at hg
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B (b + 1) + (Nat.log 2 0 + 2)) hg
    fun v₄ S₄ ⟨h0₄, h1₄, h2₄, h3₄, h4₄, h5₄, h6₄, h7₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 5: dropNum 2
  have hd := dropNum_le_B (x := 2) (2 + (z - 1)) (b + 1) (by omega) (S 2) v₄ S₄ h2₄
  refine Frag.runs_mono (Frag.seq_runs (t₂ := Nat.log 2 0 + 2) hd
    fun v₅ S₅ ⟨_, _, _, h2₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 6: dropNum 3
  have hd3 := dropNum_correct (x := 3) 0 r3 v₅ S₅ (by rw [hF₅ 3 (by decide), h3₄])
  refine Frag.runs_mono hd3 (fun _ S₆ ⟨_, _, _, h3₆, hF₆⟩ => ?_) le_rfl
  refine ⟨?_, ?_, ?_, h3₆, ?_, ?_, ?_, ?_⟩
  · rw [hF₆ 0 (by decide), hF₅ 0 (by decide), h0₄, Function.update_of_ne (by decide), h0₂, h0]
  · rw [hF₆ 1 (by decide), hF₅ 1 (by decide), h1₄, Function.update_of_ne (by decide), h1₂, h1]
  · rw [hF₆ 2 (by decide), h2₅]
  · rw [hF₆ 4 (by decide), hF₅ 4 (by decide), h4₄, Function.update_of_ne (by decide), hF₂ 4 (by decide),
      hF₁ 4 (by decide) (by decide)]
  · rw [hF₆ 5 (by decide), hF₅ 5 (by decide), h5₄, hF₂ 5 (by decide), hF₁ 5 (by decide) (by decide)]
  · rw [hF₆ 6 (by decide), hF₅ 6 (by decide), h6₄, Function.update_of_ne (by decide), hF₂ 6 (by decide),
      h6₁]
  · rw [hF₆ 7 (by decide), hF₅ 7 (by decide), h7₄, Function.update_of_ne (by decide), hF₂ 7 (by decide),
      hF₁ 7 (by decide) (by decide)]

/-- `reservoirF` in `B`-form: `((Alg.reservoir z z99 y).2 + 1) * B (12 b + 46)`
for `z, z99, y < 2 ^ b`, `2 ≤ b`. -/
theorem reservoirF_le_B (z z99 y b : ℕ) (hb : 2 ≤ b) (hz : z < 2 ^ b) (hz99 : z99 < 2 ^ b)
    (hy : y < 2 ^ b) (r0 r1 r3 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' y ++ .comma :: r0) (h1 : S 1 = encodeNatΓ' z99 ++ .comma :: r1)
    (h3 : S 3 = encodeNatΓ' z ++ .comma :: r3) :
    reservoirF.Runs v S (fun _ S' =>
        S' 0 = S 0 ∧ S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = r3 ∧
        S' 4 = encList (Alg.reservoir z z99 y).1 ++ S 4 ∧ S' 5 = S 5 ∧ S' 6 = S 6 ∧ S' 7 = S 7)
      (((Alg.reservoir z z99 y).2 + 1) * B (12 * b + 46)) := by
  refine Frag.runs_mono (reservoirF_runs z z99 y b hb hz hz99 hy r0 r1 r3 v S h0 h1 h3)
    (fun _ _ h => h) ?_
  rw [show 12 * b + 46 = 3 * (4 * b + 14) + 4 by ring, ← B_twentyseven]
  have := one_le_B (4 * b + 14)
  nlinarith


/-! ### Canonical in-place subtraction -/

/-- `subCx x y z`: `a` on `x`, `b` on `y` (both consumed); `encodeNatΓ' (a - b)`
pushed on `x`; `z` scratch (restored). -/
def subCx (x y z : K) : Frag := (sub x y z x).seq (canonNum x z)

theorem subCx_correct {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (a b : ℕ) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' b ++ .comma :: yr) :
    (subCx x y z).Runs v S (fun _ S' =>
        S' x = encodeNatΓ' (a - b) ++ .comma :: xr ∧ S' y = yr ∧ S' z = S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → S' k = S k)
      (6 * (Nat.log 2 a + Nat.log 2 b) + 22) := by
  have hla := encodeNat_length_le a
  have hlb := encodeNat_length_le b
  have h1 := sub_runs_x hxy hxz hyz (Computability.encodeNat a) (Computability.encodeNat b) xr yr
    v S hSx hSy
  have hlen := subTrunc_length (Computability.encodeNat a) (Computability.encodeNat b) false
  have hmax : max (Computability.encodeNat a).length (Computability.encodeNat b).length ≤
      Nat.log 2 a + Nat.log 2 b + 2 := max_le (by omega) (by omega)
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := 3 * max (Computability.encodeNat a).length (Computability.encodeNat b).length + 5) h1
    fun v₁ S₁ ⟨hx₁, hy₁, hz₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  have h2 := canonNum_runs hxz _ xr v₁ S₁ hx₁
  refine Frag.runs_mono h2 (fun _ S₂ ⟨_, _, _, hx₂, hz₂, hF₂⟩ => ⟨?_, ?_, ?_, ?_⟩) (by omega)
  · rw [hx₂, toNat_subTrunc]; simp [toNat_encodeNat]
  · rw [hF₂ y hxy.symm hyz, hy₁]
  · rw [hz₂, hz₁]
  · intro k hkx hky hkz; rw [hF₂ k hkx hkz, hF₁ k hkx hky hkz]

theorem subCx_le_B {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (a b m : ℕ) (ha : a < 2 ^ m) (hb : b < 2 ^ m) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' b ++ .comma :: yr) :
    (subCx x y z).Runs v S (fun _ S' =>
        S' x = encodeNatΓ' (a - b) ++ .comma :: xr ∧ S' y = yr ∧ S' z = S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → S' k = S k)
      (B m) := by
  refine Frag.runs_mono (subCx_correct hxy hxz hyz a b xr yr v S hSx hSy) (fun _ _ h => h) ?_
  have := log_le_of_lt_pow ha
  have := log_le_of_lt_pow hb
  exact le_B_of_le_linear (by omega)

/-! ### The step-2 tail of `search`: `len`, `len < T`, `Q`, `L`, `x`

Entry layout: stack `0` holds the five scales `z :: z99 :: y :: T :: θ` (top
first) above `r0`; the other stacks are arbitrary and restored (the
success branch pushes its results on `1`, `2`, `3`, `4`).  `step2Pre`
computes the reservoir and `cmp := compare len T`; `step2Succ` (run iff
`T ≤ len`) computes `Q`, `L`, `x` and lays them out for `scanF`. -/

theorem pow_lt_two_pow {L m n : ℕ} (h : L < 2 ^ m) (hn : n ≠ 0) : L ^ n < 2 ^ (n * m) := by
  rw [mul_comm, pow_mul]; exact Nat.pow_lt_pow_left h hn

theorem reservoir_length_lt_pow {z z99 y b : ℕ} (hz : z < 2 ^ b) :
    (Alg.reservoir z z99 y).1.length < 2 ^ b := by
  have := resGo_length_le_fuel z99 y 2 (z - 1)
  rw [reservoir_eq]; omega

theorem reservoir_mem_lt_pow {z z99 y b : ℕ} (hz : z < 2 ^ b) :
    ∀ p ∈ (Alg.reservoir z z99 y).1, p < 2 ^ b := by
  intro p hp
  have := reservoir_mem hp
  omega

/-- `L ^ 5` on `6` from `L` on `3` (peeked): four `mulC`s on copies. -/
def pow5F : Frag :=
  (dup 3 5 6).seq ((dup 3 6 5).seq ((mulC 5 6 7 2 4).seq ((dup 3 5 6).seq ((mulC 7 5 6 2 4).seq
    ((dup 3 5 7).seq ((mulC 6 5 7 2 4).seq ((dup 3 5 6).seq (mulC 7 5 6 2 4))))))))

theorem pow5F_le_B (L m : ℕ) (hL : L < 2 ^ m) (r3 : List Γ') (v : St) (S : Stacks)
    (h3 : S 3 = encodeNatΓ' L ++ .comma :: r3) :
    pow5F.Runs v S (fun _ S' =>
        S' 0 = S 0 ∧ S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = S 3 ∧ S' 4 = S 4 ∧ S' 5 = S 5 ∧
        S' 6 = encodeNatΓ' (L ^ 5) ++ .comma :: S 6 ∧ S' 7 = S 7)
      (9 * B (4 * m)) := by
  have hm1 : B m ≤ B (4 * m) := B_mono (by omega)
  have hm2 : B (2 * m) ≤ B (4 * m) := B_mono (by omega)
  have hm3 : B (3 * m) ≤ B (4 * m) := B_mono (by omega)
  have hL1 : L < 2 ^ (1 * m) := by rwa [one_mul]
  have hL2 : L * L < 2 ^ (2 * m) := by rw [← pow_two]; exact pow_lt_two_pow hL (by norm_num)
  have hL3 : L * L * L < 2 ^ (3 * m) := by
    rw [show L * L * L = L ^ 3 by ring]; exact pow_lt_two_pow hL (by norm_num)
  have hL4 : L * L * L * L < 2 ^ (4 * m) := by
    rw [show L * L * L * L = L ^ 4 by ring]; exact pow_lt_two_pow hL (by norm_num)
  have hLm2 : L < 2 ^ (2 * m) := lt_of_lt_of_le hL (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hLm3 : L < 2 ^ (3 * m) := lt_of_lt_of_le hL (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hLm4 : L < 2 ^ (4 * m) := lt_of_lt_of_le hL (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- 1. dup 3 5 6
  have ha := dup_le_B (x := 3) (y := 5) (s := 6) (by decide) (by decide) (by decide) L m hL r3 v S h3
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 8 * B (4 * m)) ha
    fun v₁ S₁ ⟨h3₁, h5₁, h6₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 2. dup 3 6 5
  have hb := dup_le_B (x := 3) (y := 6) (s := 5) (by decide) (by decide) (by decide) L m hL r3 v₁ S₁
    (by rw [h3₁, h3])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 7 * B (4 * m)) hb
    fun v₂ S₂ ⟨h3₂, h6₂, h5₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. mulC 5 6 7 2 4 : 7 := L * L
  have h5₂' : S₂ 5 = encodeNatΓ' L ++ .comma :: S 5 := by rw [h5₂, h5₁]
  have h6₂' : S₂ 6 = encodeNatΓ' L ++ .comma :: S 6 := by rw [h6₂, h6₁]
  have hc := mulC_le_B (x := 5) (y := 6) (w := 7) (s := 2) (t := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    L L m hL hL (S 5) (S 6) v₂ S₂ h5₂' h6₂'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 6 * B (4 * m)) hc
    fun v₃ S₃ ⟨h5₃, h6₃, h7₃, h2₃, h4₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 4. dup 3 5 6
  have h3₃ : S₃ 3 = encodeNatΓ' L ++ .comma :: r3 := by
    rw [hF₃ 3 (by decide) (by decide) (by decide) (by decide) (by decide), h3₂, h3₁, h3]
  have hd := dup_le_B (x := 3) (y := 5) (s := 6) (by decide) (by decide) (by decide) L m hL r3 v₃ S₃ h3₃
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * B (4 * m)) hd
    fun v₄ S₄ ⟨h3₄, h5₄, h6₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 5. mulC 7 5 6 2 4 : 6 := L * L * L
  have h7₄ : S₄ 7 = encodeNatΓ' (L * L) ++ .comma :: S 7 := by
    rw [hF₄ 7 (by decide) (by decide) (by decide), h7₃, hF₂ 7 (by decide) (by decide) (by decide),
      hF₁ 7 (by decide) (by decide) (by decide)]
  have h5₄' : S₄ 5 = encodeNatΓ' L ++ .comma :: S 5 := by rw [h5₄, h5₃]
  have he := mulC_le_B (x := 7) (y := 5) (w := 6) (s := 2) (t := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (L * L) L (2 * m) hL2 hLm2 (S 7) (S 5) v₄ S₄ h7₄ h5₄'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * B (4 * m)) he
    fun v₅ S₅ ⟨h7₅, h5₅, h6₅, h2₅, h4₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 6. dup 3 5 7
  have h3₅ : S₅ 3 = encodeNatΓ' L ++ .comma :: r3 := by
    rw [hF₅ 3 (by decide) (by decide) (by decide) (by decide) (by decide), h3₄, h3₃]
  have hf := dup_le_B (x := 3) (y := 5) (s := 7) (by decide) (by decide) (by decide) L m hL r3 v₅ S₅ h3₅
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * B (4 * m)) hf
    fun v₆ S₆ ⟨h3₆, h5₆, h7₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 7. mulC 6 5 7 2 4 : 7 := L * L * L * L
  have h6₆ : S₆ 6 = encodeNatΓ' (L * L * L) ++ .comma :: S 6 := by
    rw [hF₆ 6 (by decide) (by decide) (by decide), h6₅, h6₄, h6₃]
  have h5₆' : S₆ 5 = encodeNatΓ' L ++ .comma :: S 5 := by rw [h5₆, h5₅]
  have hg := mulC_le_B (x := 6) (y := 5) (w := 7) (s := 2) (t := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (L * L * L) L (3 * m) hL3 hLm3 (S 6) (S 5) v₆ S₆ h6₆ h5₆'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B (4 * m)) hg
    fun v₇ S₇ ⟨h6₇, h5₇, h7₇, h2₇, h4₇, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 8. dup 3 5 6
  have h3₇ : S₇ 3 = encodeNatΓ' L ++ .comma :: r3 := by
    rw [hF₇ 3 (by decide) (by decide) (by decide) (by decide) (by decide), h3₆, h3₅]
  have hh := dup_le_B (x := 3) (y := 5) (s := 6) (by decide) (by decide) (by decide) L m hL r3 v₇ S₇ h3₇
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B (4 * m)) hh
    fun v₈ S₈ ⟨h3₈, h5₈, h6₈, hF₈⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 9. mulC 7 5 6 2 4 : 6 := L ^ 5
  have h7₈ : S₈ 7 = encodeNatΓ' (L * L * L * L) ++ .comma :: S 7 := by
    rw [hF₈ 7 (by decide) (by decide) (by decide), h7₇, h7₆, h7₅]
  have h5₈' : S₈ 5 = encodeNatΓ' L ++ .comma :: S 5 := by rw [h5₈, h5₇]
  have hi := mulC_le_B (x := 7) (y := 5) (w := 6) (s := 2) (t := 4) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (L * L * L * L) L (4 * m) hL4 hLm4 (S 7) (S 5) v₈ S₈ h7₈ h5₈'
  refine Frag.runs_mono hi (fun _ S₉ ⟨h7₉, h5₉, h6₉, h2₉, h4₉, hF₉⟩ => ⟨?_, ?_, ?_, ?_, ?_, h5₉, ?_, h7₉⟩)
    le_rfl
  · rw [hF₉ 0 (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₈ 0 (by decide) (by decide) (by decide), hF₇ 0 (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₆ 0 (by decide) (by decide) (by decide), hF₅ 0 (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₄ 0 (by decide) (by decide) (by decide), hF₃ 0 (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₂ 0 (by decide) (by decide) (by decide), hF₁ 0 (by decide) (by decide) (by decide)]
  · rw [hF₉ 1 (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₈ 1 (by decide) (by decide) (by decide), hF₇ 1 (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₆ 1 (by decide) (by decide) (by decide), hF₅ 1 (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₄ 1 (by decide) (by decide) (by decide), hF₃ 1 (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₂ 1 (by decide) (by decide) (by decide), hF₁ 1 (by decide) (by decide) (by decide)]
  · rw [h2₉, hF₈ 2 (by decide) (by decide) (by decide), h2₇, hF₆ 2 (by decide) (by decide) (by decide),
      h2₅, hF₄ 2 (by decide) (by decide) (by decide), h2₃, hF₂ 2 (by decide) (by decide) (by decide),
      hF₁ 2 (by decide) (by decide) (by decide)]
  · rw [hF₉ 3 (by decide) (by decide) (by decide) (by decide) (by decide), h3₈, h3₇, h3]
  · rw [h4₉, hF₈ 4 (by decide) (by decide) (by decide), h4₇, hF₆ 4 (by decide) (by decide) (by decide),
      h4₅, hF₄ 4 (by decide) (by decide) (by decide), h4₃, hF₂ 4 (by decide) (by decide) (by decide),
      hF₁ 4 (by decide) (by decide) (by decide)]
  · rw [h6₉, h6₈, h6₇, show L * L * L * L * L = L ^ 5 by ring]

/-- The step-2 charge of `Alg.search`: `res.2 + 1` on the `len < T` failure,
`res.2 + T + (prodL Q).2 + 2 = res.2 + 2 T + 2` on success. -/
def step2Cost (z z99 y T : ℕ) : ℕ :=
  if (Alg.reservoir z z99 y).1.length < T then (Alg.reservoir z z99 y).2 + 1
  else (Alg.reservoir z z99 y).2 + 2 * T + 2

/-- Prelude: the reservoir on `4`, `len` on `2`, `cmp := compare len T`;
`z` is moved to `1`, `z99` and `y` are dropped, `0` keeps `T :: θ`. -/
def step2Pre : Frag :=
  (dup 0 3 5).seq ((moveEntry 0 1 5).seq ((moveEntry 0 1 5).seq (reservoirF.seq
    ((dropNum 1).seq ((dropNum 0).seq ((listLen 4 2 5 6).seq
      ((dup 2 5 6).seq ((dup 0 6 5).seq (cmpFrag 5 6)))))))))

theorem step2Pre_runs (z z99 y T θ b : ℕ) (hb : 2 ≤ b) (hz : z < 2 ^ b) (hz99 : z99 < 2 ^ b)
    (hy : y < 2 ^ b) (hT : T < 2 ^ b) (r0 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' z ++ .comma :: (encodeNatΓ' z99 ++ .comma :: (encodeNatΓ' y ++ .comma ::
      (encodeNatΓ' T ++ .comma :: (encodeNatΓ' θ ++ .comma :: r0))))) :
    step2Pre.Runs v S (fun v' S' =>
        v'.cmp = compare (Alg.reservoir z z99 y).1.length T ∧
        S' 0 = encodeNatΓ' T ++ .comma :: (encodeNatΓ' θ ++ .comma :: r0) ∧
        S' 1 = encodeNatΓ' z ++ .comma :: S 1 ∧
        S' 2 = encodeNatΓ' (Alg.reservoir z z99 y).1.length ++ .comma :: S 2 ∧
        S' 3 = S 3 ∧ S' 4 = encList (Alg.reservoir z z99 y).1 ++ S 4 ∧
        S' 5 = S 5 ∧ S' 6 = S 6 ∧ S' 7 = S 7)
      (((Alg.reservoir z z99 y).2 + 2) * (12 * B (4 * b + 14))) := by
  have hB1 := one_le_B b
  have hBb : B b ≤ B (4 * b + 14) := B_mono (by omega)
  have hX7 : 7 ≤ B (4 * b + 14) := le_B_of_le_linear (by omega)
  have hlz := log_le_of_lt_pow hz
  have hlz99 := log_le_of_lt_pow hz99
  have hlT := log_le_of_lt_pow hT
  have hlin : 8 * b + 40 ≤ B b := le_B_of_le_linear (by omega)
  have hlen := reservoir_length_le_cost z z99 y
  have hlenb := reservoir_length_lt_pow (z99 := z99) (y := y) hz
  have hllen := log_le_of_lt_pow hlenb
  have hmem := reservoir_mem_lt_pow (z99 := z99) (y := y) hz
  obtain ⟨X, hX⟩ : ∃ X, B (4 * b + 14) = X := ⟨_, rfl⟩
  rw [hX] at hBb hX7 ⊢
  obtain ⟨n, hn⟩ : ∃ n, (Alg.reservoir z z99 y).2 = n := ⟨_, rfl⟩
  obtain ⟨len, hl⟩ : ∃ len, (Alg.reservoir z z99 y).1.length = len := ⟨_, rfl⟩
  rw [hn, hl] at hlen
  rw [hn]
  -- 1. dup 0 3 5 : 3 := z
  have ha := dup_le_B (x := 0) (y := 3) (s := 5) (by decide) (by decide) (by decide) z b hz _ v S h0
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := 2 * B b + ((n + 1) * (11 * X) + 3 * X + 7) + 2 * B b + (len + 1) * B b + 3 * B b) ha
    fun v₁ S₁ ⟨h0₁, h3₁, h5₁, hF₁⟩ => ?_) (fun _ _ h => h) (by nlinarith)
  -- 2. moveEntry 0 1 5 : z to 1
  have hb2 := moveEntry_correct (src := 0) (dst := 1) (s := 5) (by decide) (by decide) (by decide) z _ v₁ S₁
    (by rw [h0₁, h0])
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := B b + ((n + 1) * (11 * X) + 3 * X + 7) + 2 * B b + (len + 1) * B b + 3 * B b) hb2
    fun v₂ S₂ ⟨_, _, _, h0₂, h1₂, h5₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. moveEntry 0 1 5 : z99 to 1
  have hc := moveEntry_correct (src := 0) (dst := 1) (s := 5) (by decide) (by decide) (by decide) z99 _ v₂ S₂
    h0₂
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := ((n + 1) * (11 * X) + 3 * X + 7) + 2 * B b + (len + 1) * B b + 3 * B b) hc
    fun v₃ S₃ ⟨_, _, _, h0₃, h1₃, h5₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 4. reservoirF
  have h3₃ : S₃ 3 = encodeNatΓ' z ++ .comma :: S 3 := by
    rw [hF₃ 3 (by decide) (by decide) (by decide), hF₂ 3 (by decide) (by decide) (by decide), h3₁]
  have hd := reservoirF_runs z z99 y b hb hz hz99 hy _ _ (S 3) v₃ S₃ h0₃ h1₃ h3₃
  rw [hn, hX] at hd
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B b + (len + 1) * B b + 3 * B b) hd
    fun v₄ S₄ ⟨h0₄, h1₄, h2₄, h3₄, h4₄, h5₄, h6₄, h7₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 5. dropNum 1 : z99
  have he := dropNum_le_B (x := 1) z99 b hz99 _ v₄ S₄ (by rw [h1₄, h1₃])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + (len + 1) * B b + 3 * B b) he
    fun v₅ S₅ ⟨_, _, _, h1₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 6. dropNum 0 : y
  have hf := dropNum_le_B (x := 0) y b hy _ v₅ S₅ (by rw [hF₅ 0 (by decide), h0₄, h0₃])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (len + 1) * B b + 3 * B b) hf
    fun v₆ S₆ ⟨_, _, _, h0₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 7. listLen 4 2 5 6
  have h4₆ : S₆ 4 = encList (Alg.reservoir z z99 y).1 ++ S 4 := by
    rw [hF₆ 4 (by decide), hF₅ 4 (by decide), h4₄, hF₃ 4 (by decide) (by decide) (by decide),
      hF₂ 4 (by decide) (by decide) (by decide), hF₁ 4 (by decide) (by decide) (by decide)]
  have hg := listLen_le_B (x := 4) (y := 2) (s := 5) (z := 6) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) _ b hmem hlenb (S 4) v₆ S₆ h4₆
  rw [hl] at hg
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * B b) hg
    fun v₇ S₇ ⟨h4₇, h2₇, h5₇, h6₇, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 8. dup 2 5 6 : 5 := len
  have h2₇' : S₇ 2 = encodeNatΓ' len ++ .comma :: S 2 := by
    rw [h2₇, hF₆ 2 (by decide), hF₅ 2 (by decide), h2₄, hF₃ 2 (by decide) (by decide) (by decide),
      hF₂ 2 (by decide) (by decide) (by decide), hF₁ 2 (by decide) (by decide) (by decide)]
  rw [hl] at hlenb
  have hh := dup_le_B (x := 2) (y := 5) (s := 6) (by decide) (by decide) (by decide) len b hlenb _ v₇ S₇ h2₇'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B b) hh
    fun v₈ S₈ ⟨h2₈, h5₈, h6₈, hF₈⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 9. dup 0 6 5 : 6 := T
  have h0₈ : S₈ 0 = encodeNatΓ' T ++ .comma :: (encodeNatΓ' θ ++ .comma :: r0) := by
    rw [hF₈ 0 (by decide) (by decide) (by decide), hF₇ 0 (by decide) (by decide) (by decide) (by decide),
      h0₆]
  have hi := dup_le_B (x := 0) (y := 6) (s := 5) (by decide) (by decide) (by decide) T b hT _ v₈ S₈ h0₈
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b) hi
    fun v₉ S₉ ⟨h0₉, h6₉, h5₉, hF₉⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 10. cmpFrag 5 6
  have h5₉' : S₉ 5 = encodeNatΓ' len ++ .comma :: S 5 := by
    rw [h5₉, h5₈, h5₇, hF₆ 5 (by decide), hF₅ 5 (by decide), h5₄, h5₃, h5₂, h5₁]
  have h6₉' : S₉ 6 = encodeNatΓ' T ++ .comma :: S 6 := by
    rw [h6₉, h6₈, h6₇, hF₆ 6 (by decide), hF₅ 6 (by decide), h6₄, hF₃ 6 (by decide) (by decide) (by decide),
      hF₂ 6 (by decide) (by decide) (by decide), hF₁ 6 (by decide) (by decide) (by decide)]
  rw [hl] at hllen
  have hj := cmp_correct (x := 5) (y := 6) (by decide) len T (S 5) (S 6) v₉ S₉ h5₉' h6₉'
  refine Frag.runs_mono hj (fun v' S' ⟨hcmp, h5', h6', hF'⟩ => ?_) (by omega)
  refine ⟨by rw [hcmp, hl], ?_, ?_, ?_, ?_, ?_, h5', h6', ?_⟩
  · rw [hF' 0 (by decide) (by decide), h0₉, h0₈]
  · rw [hF' 1 (by decide) (by decide), hF₉ 1 (by decide) (by decide) (by decide),
      hF₈ 1 (by decide) (by decide) (by decide), hF₇ 1 (by decide) (by decide) (by decide) (by decide),
      hF₆ 1 (by decide), h1₅, h1₂, hF₁ 1 (by decide) (by decide) (by decide)]
  · rw [hF' 2 (by decide) (by decide), hF₉ 2 (by decide) (by decide) (by decide), h2₈, h2₇', hl]
  · rw [hF' 3 (by decide) (by decide), hF₉ 3 (by decide) (by decide) (by decide),
      hF₈ 3 (by decide) (by decide) (by decide), hF₇ 3 (by decide) (by decide) (by decide) (by decide),
      hF₆ 3 (by decide), hF₅ 3 (by decide), h3₄]
  · rw [hF' 4 (by decide) (by decide), hF₉ 4 (by decide) (by decide) (by decide),
      hF₈ 4 (by decide) (by decide) (by decide), h4₇, h4₆]
  · rw [hF' 7 (by decide) (by decide), hF₉ 7 (by decide) (by decide) (by decide),
      hF₈ 7 (by decide) (by decide) (by decide), hF₇ 7 (by decide) (by decide) (by decide) (by decide),
      hF₆ 7 (by decide), hF₅ 7 (by decide), h7₄, hF₃ 7 (by decide) (by decide) (by decide),
      hF₂ 7 (by decide) (by decide) (by decide), hF₁ 7 (by decide) (by decide) (by decide)]

/-- Success branch (run iff `T ≤ len`): `Q := res.drop (len - T)` on `4`,
`L := prodL Q` on `3`, `x := L ^ 5` on `0` (above `θ`) and under `z` on `1`
(the scan fuel), `k := 1` on `2`; `flag := true`. -/
def step2Succ : Frag :=
  (dup 2 5 6).seq ((dup 0 6 5).seq ((subCx 5 6 7).seq ((dropN 4 5 6).seq ((dropNum 2).seq
    ((prodLF 4 3 5 6 7).seq (pow5F.seq ((dropNum 0).seq ((moveEntry 1 5 7).seq ((dup 6 1 7).seq
      ((moveEntry 5 1 7).seq ((moveEntry 6 0 5).seq ((pushNum 2 1).seq
        (Frag.load' (fun v => { v with flag := true }))))))))))))))

theorem step2Succ_runs (res : List ℕ) (z T θ b : ℕ) (hb : 2 ≤ b) (hres : ∀ p ∈ res, p < 2 ^ b)
    (hlen : res.length < 2 ^ b) (hT : T < 2 ^ b) (hTl : T ≤ res.length) (hz : z < 2 ^ b)
    (r0 r1 r2 r4 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' T ++ .comma :: (encodeNatΓ' θ ++ .comma :: r0))
    (h1 : S 1 = encodeNatΓ' z ++ .comma :: r1)
    (h2 : S 2 = encodeNatΓ' res.length ++ .comma :: r2)
    (h4 : S 4 = encList res ++ r4) :
    step2Succ.Runs v S (fun v' S' =>
        v'.flag = true ∧
        S' 0 = encodeNatΓ' ((Alg.prodL (res.drop (res.length - T))).1 ^ 5) ++ .comma ::
          (encodeNatΓ' θ ++ .comma :: r0) ∧
        S' 1 = encodeNatΓ' z ++ .comma ::
          (encodeNatΓ' ((Alg.prodL (res.drop (res.length - T))).1 ^ 5) ++ .comma :: r1) ∧
        S' 2 = encodeNatΓ' 1 ++ .comma :: r2 ∧
        S' 3 = encodeNatΓ' (Alg.prodL (res.drop (res.length - T))).1 ++ .comma :: S 3 ∧
        S' 4 = encList (res.drop (res.length - T)) ++ r4 ∧
        S' 5 = S 5 ∧ S' 6 = S 6 ∧ S' 7 = S 7)
      ((res.length + T + 21) * B (5 * (T + 1) * b + 14)) := by
  obtain ⟨len, hl⟩ : ∃ len, res.length = len := ⟨_, rfl⟩
  rw [hl] at hlen hTl h2 ⊢
  obtain ⟨Q, hQ⟩ : ∃ Q, res.drop (len - T) = Q := ⟨_, rfl⟩
  rw [hQ]
  have hQlen : Q.length = T := by rw [← hQ, List.length_drop]; omega
  have hQmem : ∀ p ∈ Q, p < 2 ^ b := fun p hp => hres p (by rw [← hQ] at hp; exact List.mem_of_mem_drop hp)
  obtain ⟨L, hLdef⟩ : ∃ L, (Alg.prodL Q).1 = L := ⟨_, rfl⟩
  rw [hLdef]
  have hLb : L < 2 ^ (T * b + 1) := by
    have := prodL_le_two_pow hQmem
    rw [hLdef, hQlen] at this
    calc L ≤ 2 ^ (T * b) := this
      _ < 2 ^ (T * b + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hx : L ^ 5 < 2 ^ (5 * (T * b + 1)) := pow_lt_two_pow hLb (by norm_num)
  obtain ⟨M, hM⟩ : ∃ M, 5 * (T + 1) * b + 14 = M := ⟨_, rfl⟩
  have hB1 := one_le_B b
  have hBb : B b ≤ B M := B_mono (by rw [← hM]; nlinarith)
  have hBp : B (2 * (T + 1) * b + 4) ≤ B M := B_mono (by rw [← hM]; nlinarith)
  have hB4 : B (4 * (T * b + 1)) ≤ B M := B_mono (by rw [← hM]; nlinarith)
  have hB5 : B (5 * (T * b + 1)) ≤ B M := B_mono (by rw [← hM]; nlinarith)
  have hlx := log_le_of_lt_pow hx
  have hlz := log_le_of_lt_pow hz
  have hlin : 8 * b + 40 ≤ B b := le_B_of_le_linear (by omega)
  have hlinM : 10 * (T * b + 1) + 40 ≤ B M := le_B_of_le_linear (by rw [← hM]; nlinarith)
  have hl1 : Nat.log 2 1 = 0 := Nat.log_one_right 2
  rw [hM]
  -- 1. dup 2 5 6 : 5 := len
  have ha := dup_le_B (x := 2) (y := 5) (s := 6) (by decide) (by decide) (by decide) len b hlen r2 v S h2
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := B b + B b + (len + 1) * B b + B b + (T + 1) * B M + 9 * B M + B b + B b + B M + B b +
      B M + 2 + 1) ha
    fun v₁ S₁ ⟨h2₁, h5₁, h6₁, hF₁⟩ => ?_) (fun _ _ h => h) (by nlinarith)
  -- 2. dup 0 6 5 : 6 := T
  have hb2 := dup_le_B (x := 0) (y := 6) (s := 5) (by decide) (by decide) (by decide) T b hT _ v₁ S₁
    (by rw [hF₁ 0 (by decide) (by decide) (by decide), h0])
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := B b + (len + 1) * B b + B b + (T + 1) * B M + 9 * B M + B b + B b + B M + B b +
      B M + 2 + 1) hb2
    fun v₂ S₂ ⟨h0₂, h6₂, h5₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. subCx 5 6 7 : 5 := len - T
  have h5₂' : S₂ 5 = encodeNatΓ' len ++ .comma :: S 5 := by rw [h5₂, h5₁]
  have h6₂' : S₂ 6 = encodeNatΓ' T ++ .comma :: S 6 := by rw [h6₂, h6₁]
  have hc := subCx_le_B (x := 5) (y := 6) (z := 7) (by decide) (by decide) (by decide) len T b hlen hT
    _ _ v₂ S₂ h5₂' h6₂'
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (len + 1) * B b + B b + (T + 1) * B M + 9 * B M + B b + B b + B M + B b + B M + 2 + 1) hc
    fun v₃ S₃ ⟨h5₃, h6₃, h7₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 4. dropN 4 5 6 : 4 := Q
  have h4₃ : S₃ 4 = encList res ++ r4 := by
    rw [hF₃ 4 (by decide) (by decide) (by decide), hF₂ 4 (by decide) (by decide) (by decide),
      hF₁ 4 (by decide) (by decide) (by decide), h4]
  have hd := dropN_le_B (x := 4) (c := 5) (s := 6) (by decide) (by decide) (by decide) res b hres (len - T)
    (by omega) r4 (S 5) v₃ S₃ h4₃ h5₃
  rw [hl, hQ] at hd
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := B b + (T + 1) * B M + 9 * B M + B b + B b + B M + B b + B M + 2 + 1) hd
    fun v₄ S₄ ⟨h4₄, h5₄, h6₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 5. dropNum 2 : len
  have h2₄ : S₄ 2 = encodeNatΓ' len ++ .comma :: r2 := by
    rw [hF₄ 2 (by decide) (by decide) (by decide), hF₃ 2 (by decide) (by decide) (by decide),
      hF₂ 2 (by decide) (by decide) (by decide), h2₁, h2]
  have he := dropNum_le_B (x := 2) len b hlen r2 v₄ S₄ h2₄
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (T + 1) * B M + 9 * B M + B b + B b + B M + B b + B M + 2 + 1) he
    fun v₅ S₅ ⟨_, _, _, h2₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 6. prodLF 4 3 5 6 7 : 3 := L
  have h4₅ : S₅ 4 = encList Q ++ r4 := by rw [hF₅ 4 (by decide), h4₄]
  have hf := prodLF_le_B (x := 4) (w := 3) (c := 5) (s := 6) (t := 7) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    Q b hQmem r4 v₅ S₅ h4₅
  rw [prodL_snd, hQlen, hLdef] at hf
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := 9 * B M + B b + B b + B M + B b + B M + 2 + 1) hf
    fun v₆ S₆ ⟨h4₆, h3₆, h5₆, h6₆, h7₆, hF₆⟩ => ?_) (fun _ _ h => h)
    (by have := Nat.mul_le_mul_left (T + 1) hBp; omega)
  -- 7. pow5F : 6 := L ^ 5
  have hg := pow5F_le_B L (T * b + 1) hLb (S₅ 3) v₆ S₆ h3₆
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + B b + B M + B b + B M + 2 + 1) hg
    fun v₇ S₇ ⟨h0₇, h1₇, h2₇, h3₇, h4₇, h5₇, h6₇, h7₇⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 8. dropNum 0 : T
  have h0₇' : S₇ 0 = encodeNatΓ' T ++ .comma :: (encodeNatΓ' θ ++ .comma :: r0) := by
    rw [h0₇, hF₆ 0 (by decide) (by decide) (by decide) (by decide) (by decide), hF₅ 0 (by decide),
      hF₄ 0 (by decide) (by decide) (by decide), hF₃ 0 (by decide) (by decide) (by decide), h0₂,
      hF₁ 0 (by decide) (by decide) (by decide), h0]
  have hh := dropNum_le_B (x := 0) T b hT _ v₇ S₇ h0₇'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + B M + B b + B M + 2 + 1) hh
    fun v₈ S₈ ⟨_, _, _, h0₈, hF₈⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 9. moveEntry 1 5 7 : z to 5
  have h1₈ : S₈ 1 = encodeNatΓ' z ++ .comma :: r1 := by
    rw [hF₈ 1 (by decide), h1₇, hF₆ 1 (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₅ 1 (by decide), hF₄ 1 (by decide) (by decide) (by decide), hF₃ 1 (by decide) (by decide) (by decide),
      hF₂ 1 (by decide) (by decide) (by decide), hF₁ 1 (by decide) (by decide) (by decide), h1]
  have hi := moveEntry_correct (src := 1) (dst := 5) (s := 7) (by decide) (by decide) (by decide) z r1 v₈ S₈ h1₈
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B M + B b + B M + 2 + 1) hi
    fun v₉ S₉ ⟨_, _, _, h1₉, h5₉, h7₉, hF₉⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 10. dup 6 1 7 : 1 := x
  have h6₉ : S₉ 6 = encodeNatΓ' (L ^ 5) ++ .comma :: S 6 := by
    rw [hF₉ 6 (by decide) (by decide) (by decide), hF₈ 6 (by decide), h6₇, h6₆,
      hF₅ 6 (by decide), h6₄, h6₃]
  have hj := dup_le_B (x := 6) (y := 1) (s := 7) (by decide) (by decide) (by decide) (L ^ 5) (5 * (T * b + 1)) hx
    _ v₉ S₉ h6₉
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + B M + 2 + 1) hj
    fun v₁₀ S₁₀ ⟨h6₁₀, h1₁₀, h7₁₀, hF₁₀⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 11. moveEntry 5 1 7 : z back on 1
  have h5₁₀ : S₁₀ 5 = encodeNatΓ' z ++ .comma :: S₈ 5 := by
    rw [hF₁₀ 5 (by decide) (by decide) (by decide), h5₉]
  have hk := moveEntry_correct (src := 5) (dst := 1) (s := 7) (by decide) (by decide) (by decide) z _ v₁₀ S₁₀
    h5₁₀
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B M + 2 + 1) hk
    fun v₁₁ S₁₁ ⟨_, _, _, h5₁₁, h1₁₁, h7₁₁, hF₁₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 12. moveEntry 6 0 5 : x on 0
  have h6₁₁' : S₁₁ 6 = encodeNatΓ' (L ^ 5) ++ .comma :: S 6 := by
    rw [hF₁₁ 6 (by decide) (by decide) (by decide), h6₁₀, h6₉]
  have hm2 := moveEntry_correct (src := 6) (dst := 0) (s := 5) (by decide) (by decide) (by decide) (L ^ 5) _ v₁₁
    S₁₁ h6₁₁'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 + 1) hm2
    fun v₁₂ S₁₂ ⟨_, _, _, h6₁₂, h0₁₂, h5₁₂, hF₁₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 13. pushNum 2 1
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) (pushNum_runs 2 1 v₁₂ S₁₂)
    fun v₁₃ S₁₃ ⟨hv₁₃, h2₁₃, hF₁₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 14. load' flag := true
  refine Frag.runs_mono (Frag.load'_runs _ v₁₃ S₁₃) (fun v' S' ⟨hv', hS'⟩ => ?_) le_rfl
  rw [hv', hS']
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF₁₃ 0 (by decide), h0₁₂, hF₁₁ 0 (by decide) (by decide) (by decide),
      hF₁₀ 0 (by decide) (by decide) (by decide), hF₉ 0 (by decide) (by decide) (by decide), h0₈]
  · rw [hF₁₃ 1 (by decide), hF₁₂ 1 (by decide) (by decide) (by decide), h1₁₁, h1₁₀, h1₉]
  · rw [h2₁₃, hF₁₂ 2 (by decide) (by decide) (by decide), hF₁₁ 2 (by decide) (by decide) (by decide),
      hF₁₀ 2 (by decide) (by decide) (by decide), hF₉ 2 (by decide) (by decide) (by decide),
      hF₈ 2 (by decide), h2₇, hF₆ 2 (by decide) (by decide) (by decide) (by decide) (by decide), h2₅]
  · rw [hF₁₃ 3 (by decide), hF₁₂ 3 (by decide) (by decide) (by decide),
      hF₁₁ 3 (by decide) (by decide) (by decide), hF₁₀ 3 (by decide) (by decide) (by decide),
      hF₉ 3 (by decide) (by decide) (by decide), hF₈ 3 (by decide), h3₇, h3₆, hF₅ 3 (by decide),
      hF₄ 3 (by decide) (by decide) (by decide), hF₃ 3 (by decide) (by decide) (by decide),
      hF₂ 3 (by decide) (by decide) (by decide), hF₁ 3 (by decide) (by decide) (by decide)]
  · rw [hF₁₃ 4 (by decide), hF₁₂ 4 (by decide) (by decide) (by decide),
      hF₁₁ 4 (by decide) (by decide) (by decide), hF₁₀ 4 (by decide) (by decide) (by decide),
      hF₉ 4 (by decide) (by decide) (by decide), hF₈ 4 (by decide), h4₇, h4₆, h4₅]
  · rw [hF₁₃ 5 (by decide), h5₁₂, h5₁₁, hF₈ 5 (by decide), h5₇, h5₆, hF₅ 5 (by decide), h5₄]
  · rw [hF₁₃ 6 (by decide), h6₁₂]
  · rw [hF₁₃ 7 (by decide), hF₁₂ 7 (by decide) (by decide) (by decide), h7₁₁, h7₁₀, h7₉,
      hF₈ 7 (by decide), h7₇, h7₆, hF₅ 7 (by decide), hF₄ 7 (by decide) (by decide) (by decide), h7₃,
      hF₂ 7 (by decide) (by decide) (by decide), hF₁ 7 (by decide) (by decide) (by decide)]

/-- Step 2 of `search`: `step2Pre`, then branch on `len < T`. -/
def step2F : Frag :=
  step2Pre.seq (Frag.ite (fun v => decide (v.cmp = .lt))
    (Frag.load' (fun v => { v with flag := false })) step2Succ)

theorem step2F_le_B (z z99 y T θ b : ℕ) (hb : 2 ≤ b) (hz : z < 2 ^ b) (hz99 : z99 < 2 ^ b)
    (hy : y < 2 ^ b) (hT : T < 2 ^ b) (r0 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' z ++ .comma :: (encodeNatΓ' z99 ++ .comma :: (encodeNatΓ' y ++ .comma ::
      (encodeNatΓ' T ++ .comma :: (encodeNatΓ' θ ++ .comma :: r0))))) :
    step2F.Runs v S (fun v' S' =>
        ((Alg.reservoir z z99 y).1.length < T ∧ v'.flag = false ∧
          S' 0 = encodeNatΓ' T ++ .comma :: (encodeNatΓ' θ ++ .comma :: r0) ∧
          S' 1 = encodeNatΓ' z ++ .comma :: S 1 ∧
          S' 2 = encodeNatΓ' (Alg.reservoir z z99 y).1.length ++ .comma :: S 2 ∧
          S' 3 = S 3 ∧ S' 4 = encList (Alg.reservoir z z99 y).1 ++ S 4 ∧
          S' 5 = S 5 ∧ S' 6 = S 6 ∧ S' 7 = S 7) ∨
        (T ≤ (Alg.reservoir z z99 y).1.length ∧ v'.flag = true ∧
          S' 0 = encodeNatΓ' ((Alg.prodL ((Alg.reservoir z z99 y).1.drop
            ((Alg.reservoir z z99 y).1.length - T))).1 ^ 5) ++ .comma ::
            (encodeNatΓ' θ ++ .comma :: r0) ∧
          S' 1 = encodeNatΓ' z ++ .comma :: (encodeNatΓ' ((Alg.prodL ((Alg.reservoir z z99 y).1.drop
            ((Alg.reservoir z z99 y).1.length - T))).1 ^ 5) ++ .comma :: S 1) ∧
          S' 2 = encodeNatΓ' 1 ++ .comma :: S 2 ∧
          S' 3 = encodeNatΓ' (Alg.prodL ((Alg.reservoir z z99 y).1.drop
            ((Alg.reservoir z z99 y).1.length - T))).1 ++ .comma :: S 3 ∧
          S' 4 = encList ((Alg.reservoir z z99 y).1.drop
            ((Alg.reservoir z z99 y).1.length - T)) ++ S 4 ∧
          S' 5 = S 5 ∧ S' 6 = S 6 ∧ S' 7 = S 7))
      ((step2Cost z z99 y T + 1) * B (15 * (T + 1) * b + 46)) := by
  have hlen := reservoir_length_le_cost z z99 y
  have hlenb := reservoir_length_lt_pow (z99 := z99) (y := y) hz
  have hmem := reservoir_mem_lt_pow (z99 := z99) (y := y) hz
  obtain ⟨n, hn⟩ : ∃ n, (Alg.reservoir z z99 y).2 = n := ⟨_, rfl⟩
  obtain ⟨len, hl⟩ : ∃ len, (Alg.reservoir z z99 y).1.length = len := ⟨_, rfl⟩
  rw [hn, hl] at hlen
  have hM : B (15 * (T + 1) * b + 46) = 27 * B (5 * (T + 1) * b + 14) := by
    rw [B_twentyseven]; congr 1; ring
  have hBX : B (4 * b + 14) ≤ B (5 * (T + 1) * b + 14) := B_mono (by nlinarith)
  have hB1 := one_le_B (5 * (T + 1) * b + 14)
  obtain ⟨Y, hY⟩ : ∃ Y, B (5 * (T + 1) * b + 14) = Y := ⟨_, rfl⟩
  rw [hM, hY]
  rw [hY] at hBX hB1
  have hp := step2Pre_runs z z99 y T θ b hb hz hz99 hy hT r0 v S h0
  rw [hn, hl] at hp
  unfold step2Cost
  rw [hn, hl]
  by_cases hlt : len < T
  · rw [if_pos hlt]
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 2) hp
      fun v₁ S₁ ⟨hcmp, h0₁, h1₁, h2₁, h3₁, h4₁, h5₁, h6₁, h7₁⟩ => ?_) (fun _ _ h => h) (by nlinarith)
    have hc : decide (v₁.cmp = Ordering.lt) = true := by simp [hcmp, compare_lt_iff_lt, hlt]
    refine Frag.runs_mono (Frag.ite_runs_true (t := 1) hc (Frag.load'_runs _ v₁ S₁))
      (fun v' S' ⟨hv', hS'⟩ => ?_) le_rfl
    rw [hv', hS']
    exact Or.inl ⟨hlt, rfl, h0₁, h1₁, h2₁, h3₁, h4₁, h5₁, h6₁, h7₁⟩
  · rw [if_neg hlt]
    refine Frag.runs_mono (Frag.seq_runs (t₂ := (len + T + 21) * Y + 1) hp
      fun v₁ S₁ ⟨hcmp, h0₁, h1₁, h2₁, h3₁, h4₁, h5₁, h6₁, h7₁⟩ => ?_) (fun _ _ h => h) (by nlinarith)
    have hc : decide (v₁.cmp = Ordering.lt) = false := by simp [hcmp, compare_lt_iff_lt, hlt]
    have hs := step2Succ_runs (Alg.reservoir z z99 y).1 z T θ b hb hmem hlenb hT (by rw [hl]; omega) hz
      r0 (S 1) (S 2) (S 4) v₁ S₁ h0₁ h1₁ (by rw [h2₁, hl]) h4₁
    rw [hl, hY] at hs
    refine Frag.runs_mono (Frag.ite_runs_false (t := (len + T + 21) * Y) hc hs)
      (fun v' S' ⟨hfl, h0', h1', h2', h3', h4', h5', h6', h7'⟩ => ?_) le_rfl
    exact Or.inr ⟨by omega, hfl, h0', h1', h2', by rw [h3', h3₁], h4', h5'.trans h5₁, h6'.trans h6₁,
      h7'.trans h7₁⟩


/-! ### Route A facts: `poolGo`, `poolAlg` -/

/-- The keep decision of one `poolGo` entry: `p := d k + 1` with `p ≤ x`,
`z < p`, `isPrimeTD p`. -/
def poolKeep (x z k d : ℕ) : Bool :=
  decide (d * k + 1 ≤ x ∧ z < d * k + 1) && (Alg.isPrimeTD (d * k + 1)).1

/-- The charge of one `poolGo` entry: `isPrimeTD p + 1` when `p ≤ x ∧ z < p`,
else `1`. -/
def pgc (x z k d : ℕ) : ℕ :=
  if d * k + 1 ≤ x ∧ z < d * k + 1 then (Alg.isPrimeTD (d * k + 1)).2 + 1 else 1

theorem pgc_pos (x z k d : ℕ) : 1 ≤ pgc x z k d := by
  unfold pgc; split_ifs <;> omega

theorem poolGo_nil (x z k : ℕ) : Alg.poolGo x z k [] = ([], 0) := rfl

theorem poolGo_cons_raw (x z k d : ℕ) (ds : List ℕ) :
    Alg.poolGo x z k (d :: ds) =
      (if d * k + 1 ≤ x ∧ z < d * k + 1 then
        ((if (Alg.isPrimeTD (d * k + 1)).1 then (d * k + 1) :: (Alg.poolGo x z k ds).1
            else (Alg.poolGo x z k ds).1),
          (Alg.poolGo x z k ds).2 + (Alg.isPrimeTD (d * k + 1)).2 + 1)
      else ((Alg.poolGo x z k ds).1, (Alg.poolGo x z k ds).2 + 1)) := rfl

theorem poolGo_cons (x z k d : ℕ) (ds : List ℕ) :
    Alg.poolGo x z k (d :: ds) =
      ((if poolKeep x z k d then (d * k + 1) :: (Alg.poolGo x z k ds).1
          else (Alg.poolGo x z k ds).1),
        (Alg.poolGo x z k ds).2 + pgc x z k d) := by
  rw [poolGo_cons_raw]
  unfold poolKeep pgc
  by_cases hc : d * k + 1 ≤ x ∧ z < d * k + 1
  · simp only [hc, if_true, decide_true, Bool.true_and, and_self]
    rw [Nat.add_assoc]
  · rw [if_neg hc, decide_eq_false hc, Bool.false_and, if_neg Bool.false_ne_true, if_neg hc]

theorem poolGo_append (x z k : ℕ) (l₁ l₂ : List ℕ) :
    Alg.poolGo x z k (l₁ ++ l₂) =
      ((Alg.poolGo x z k l₁).1 ++ (Alg.poolGo x z k l₂).1,
        (Alg.poolGo x z k l₁).2 + (Alg.poolGo x z k l₂).2) := by
  induction l₁ with
  | nil => simp [poolGo_nil]
  | cons d l ih =>
    rw [List.cons_append, poolGo_cons, poolGo_cons, ih]
    dsimp only
    refine Prod.ext ?_ ?_
    · dsimp only; split_ifs <;> simp
    · dsimp only; omega

theorem poolGo_single (x z k d : ℕ) :
    Alg.poolGo x z k [d] = ((if poolKeep x z k d then [d * k + 1] else []), pgc x z k d) := by
  rw [poolGo_cons, poolGo_nil]; simp

theorem poolKeep_eq_true {x z k d : ℕ} :
    poolKeep x z k d = true ↔
      (d * k + 1 ≤ x ∧ z < d * k + 1) ∧ (Alg.isPrimeTD (d * k + 1)).1 = true := by
  unfold poolKeep; simp

theorem poolGo_mem {x z k : ℕ} {ds : List ℕ} {p : ℕ} (h : p ∈ (Alg.poolGo x z k ds).1) :
    p ≤ x ∧ z < p := by
  induction ds with
  | nil => simp [poolGo_nil] at h
  | cons d ds ih =>
    rw [poolGo_cons] at h
    dsimp only at h
    by_cases hk : poolKeep x z k d = true
    · rw [if_pos hk, List.mem_cons] at h
      rcases h with rfl | h
      · exact (poolKeep_eq_true.1 hk).1
      · exact ih h
    · rw [if_neg hk] at h
      exact ih h

theorem poolGo_length_le_cost (x z k : ℕ) (ds : List ℕ) :
    (Alg.poolGo x z k ds).1.length ≤ (Alg.poolGo x z k ds).2 := by
  induction ds with
  | nil => simp [poolGo_nil]
  | cons d ds ih =>
    rw [poolGo_cons]
    dsimp only
    have := pgc_pos x z k d
    split_ifs
    · simp only [List.length_cons]; omega
    · omega

theorem poolAlg_eq (Q : List ℕ) (x z k : ℕ) :
    Alg.poolAlg Q x z k = ((Alg.poolGo x z k (Alg.divisorsOf Q).1).1,
      (Alg.divisorsOf Q).2 + (Alg.poolGo x z k (Alg.divisorsOf Q).1).2) := rfl

theorem poolAlg_length_le (Q : List ℕ) (x z k : ℕ) :
    (Alg.poolAlg Q x z k).1.length ≤ (Alg.poolAlg Q x z k).2 + 1 := by
  rw [poolAlg_eq]
  dsimp only
  have := poolGo_length_le_cost x z k (Alg.divisorsOf Q).1
  omega

theorem poolAlg_mem {Q : List ℕ} {x z k p : ℕ} (h : p ∈ (Alg.poolAlg Q x z k).1) : p ≤ x ∧ z < p := by
  rw [poolAlg_eq] at h
  exact poolGo_mem h

/-! ### A budgeted `forEntries` rule -/

theorem flag_encList_drop (l : List ℕ) (i : ℕ) (r : List Γ') :
    decide ((encList (l.drop i) ++ r).head? = some Γ'.bra) = decide (l.length ≤ i) := by
  rw [encList_eq, List.map_drop, flag_encListB_drop, List.length_map]

/-- Loop invariant of the budgeted `forEntries` rule. -/
def ForInvB (x : K) (l : List ℕ) (xr : List Γ') (P : ℕ → ℕ → Stacks → Prop)
    (i β : ℕ) (w : St) (T : Stacks) : Prop :=
  i ≤ l.length ∧ P i β T ∧ T x = encList (l.drop i) ++ xr ∧ w.flag = decide (l.length ≤ i)

/-- ℕ-level `forEntries` rule with a per-entry budget: the invariant carries
the remaining budget `β`, each entry must fit in `t + 2 ≤ β - β'`, total
`β₀ + 2`. -/
theorem forEntriesN_runs_budget {x : K} {body : Frag} (l : List ℕ) (xr : List Γ')
    (P : ℕ → ℕ → Stacks → Prop) (β₀ : ℕ) (v : St) (S : Stacks)
    (hS : S x = encList l ++ xr) (h0 : P 0 β₀ S)
    (hb : ∀ (i : ℕ) (a : ℕ) (l' : List ℕ), l.drop i = a :: l' →
      ∀ (β : ℕ) (v : St) (S : Stacks), P i β S → S x = encodeNatΓ' a ++ .comma :: (encList l' ++ xr) →
      ∃ t β', t + 2 + β' ≤ β ∧
        body.Runs v S (fun _ S' => P (i + 1) β' S' ∧ S' x = encList l' ++ xr) t) :
    (forEntries x body).Runs v S
      (fun v' S' => v'.flag = true ∧ (∃ β, P l.length β S') ∧ S' x = .bra :: xr)
      (β₀ + 2) := by
  refine Frag.runs_mono (Frag.seq_runs (t₂ := β₀ + 1) (peekBra_runs x v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₁, hS₁]
  have hloop := Frag.loop_runs_budget (c := fun v => !v.flag) (B := body.seq (peekBra x))
    (ForInvB x l xr P) l.length β₀
    (v := { v with flag := decide ((S x).head? = some Γ'.bra) }) (S := S)
    ⟨Nat.zero_le _, h0, by simpa using hS, by simp only [hS]; exact flag_encList_drop l 0 xr⟩
    (fun i hi β w T ⟨_, _, _, hfl⟩ => by simp [hfl]; omega)
    (fun β w T ⟨_, _, _, hfl⟩ => by simp [hfl])
    (fun i hi β w T ⟨_, hP, hT, _⟩ => by
      have hdrop := List.drop_eq_getElem_cons hi
      have hT' : T x = encodeNatΓ' l[i] ++ .comma :: (encList (l.drop (i + 1)) ++ xr) := by
        rw [hT, hdrop, encList_cons]; simp
      obtain ⟨t, β', hβ, hrun⟩ := hb i l[i] (l.drop (i + 1)) hdrop β w T hP hT'
      refine ⟨t + 1, β', by omega, ?_⟩
      refine Frag.seq_runs (t₂ := 1) hrun fun v₂ S₂ ⟨hP₂, hS₂⟩ => ?_
      refine Frag.runs_mono (peekBra_runs x v₂ S₂) (fun v₃ S₃ ⟨hv₃, hS₃⟩ => ?_) le_rfl
      rw [hv₃, hS₃]
      exact ⟨by omega, hP₂, hS₂, by simp only [hS₂]; exact flag_encList_drop l (i + 1) xr⟩)
  refine Frag.runs_mono hloop (fun v' S' ⟨⟨β, _, hP, hx, _⟩, hc⟩ => ⟨?_, ⟨β, hP⟩, ?_⟩) le_rfl
  · simpa using hc
  · rw [hx, List.drop_length]; rfl

/-! ### Dropping a whole list -/

/-- Pop the list on top of `x` (entries and the closing `bra`). -/
def dropListQ (x : K) : Frag := (forEntries x (dropNum x)).seq (popTop x)

theorem dropList_le_B {x : K} (l : List ℕ) (b : ℕ) (hb : ∀ a ∈ l, a < 2 ^ b) (xr : List Γ')
    (v : St) (S : Stacks) (hS : S x = encList l ++ xr) :
    (dropListQ x).Runs v S (fun _ S' => S' x = xr ∧ ∀ k, k ≠ x → S' k = S k)
      ((l.length + 1) * B b) := by
  have hloop := forEntriesN_runs (x := x) (body := dropNum x) l xr (fun _ T => ∀ k, k ≠ x → T k = S k)
    (b + 2) v S hS (fun _ _ => rfl)
    (fun i a l' hdrop w T hP hT => by
      have ha : a < 2 ^ b := hb a (mem_of_drop_eq_cons hdrop)
      refine Frag.runs_mono (dropNum_correct a _ w T hT)
        (fun _ T' ⟨_, _, _, hx', hF'⟩ => ⟨fun k hk => by rw [hF' k hk, hP k hk], hx'⟩) ?_
      have := log_le_of_lt_pow ha
      omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) hloop fun v₁ S₁ ⟨_, hP₁, hx₁⟩ => ?_)
    (fun _ _ h => h) ?_
  · refine Frag.runs_mono (popTop_runs x v₁ S₁) (fun _ S₂ ⟨_, hS₂⟩ => ⟨?_, ?_⟩) le_rfl
    · rw [hS₂, Function.update_self, hx₁]; rfl
    · intro k hk; rw [hS₂, Function.update_of_ne hk, hP₁ k hk]
  · have := list_le_B (n := l.length) (c := b + 2 + 2) (d := 3) (b := b) (by omega) (by omega)
    omega

/-! ### `poolGo`: the pool loop

Stacks: `ds` on `5` (consumed), `x` on `0`, `z` on `1`, `k` on `2` (peeked),
the open list of kept primes on `3` (reversed, `revList` at the end onto
`6`); `p = d k + 1` is built on `7`; scratch `4`, `6`.  Per entry:
`p := d * k + 1` (`mulC` consumes the entry), `cmp := compare p x`; if
`p ≤ x`: `cmp := compare z p`; if `z < p`: `isPrimeTDF p`, and `p` is moved
onto the open list iff prime, dropped otherwise.  The primality test runs
ONLY when `p ≤ x ∧ z < p`, as the Lean charge does. -/

/-- `p := d k + 1` on `7`, `cmp := compare p x`; the entry `d` is consumed from `5`. -/
def poolPre : Frag :=
  (dup 2 4 6).seq ((mulC 5 4 7 6 3).seq ((incr 7 4).seq ((dup 7 4 6).seq ((dup 0 6 4).seq
    (cmpFrag 4 6)))))

/-- `cmp := compare z p` for `z` on `1`, `p` on `7`; all stacks restored. -/
def poolCmpZ : Frag := (dup 1 4 6).seq ((dup 7 6 4).seq (cmpFrag 4 6))

def poolGoBody : Frag :=
  poolPre.seq (Frag.ite (fun v => !decide (v.cmp = .gt))
    (poolCmpZ.seq (Frag.ite (fun v => decide (v.cmp = .lt))
      ((isPrimeTDF 7 4 6 0 1 2).seq (Frag.ite (fun v => v.flag) (moveEntry 7 3 4) (dropNum 7)))
      (dropNum 7)))
    (dropNum 7))

theorem poolPre_runs (x k d bd b : ℕ) (hx : x < 2 ^ b) (hk : k < 2 ^ b) (hd : d < 2 ^ bd)
    (r0 r2 r5 : List Γ') (v : St) (T : Stacks)
    (h0 : T 0 = encodeNatΓ' x ++ .comma :: r0) (h2 : T 2 = encodeNatΓ' k ++ .comma :: r2)
    (h5 : T 5 = encodeNatΓ' d ++ .comma :: r5) :
    poolPre.Runs v T (fun v' T' =>
        v'.cmp = compare (d * k + 1) x ∧
        T' 0 = T 0 ∧ T' 1 = T 1 ∧ T' 2 = T 2 ∧ T' 3 = T 3 ∧ T' 4 = T 4 ∧ T' 5 = r5 ∧ T' 6 = T 6 ∧
        T' 7 = encodeNatΓ' (d * k + 1) ++ .comma :: T 7)
      (6 * B (3 * (bd + b) + 10)) := by
  obtain ⟨m, hm⟩ : ∃ m, bd + b = m := ⟨_, rfl⟩
  rw [hm]
  have hdm : d < 2 ^ m := lt_of_lt_of_le hd (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hkm : k < 2 ^ m := lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hdk : d * k < 2 ^ m := by rw [← hm, pow_add]; exact Nat.mul_lt_mul'' hd hk
  have hp1 : d * k + 1 < 2 ^ (m + 1) := by rw [pow_succ]; omega
  have hBb : B b ≤ B (3 * m + 10) := B_mono (by omega)
  have hBm : B m ≤ B (3 * m + 10) := B_mono (by omega)
  have hBm1 : B (m + 1) ≤ B (3 * m + 10) := B_mono (by omega)
  have hlp := log_le_of_lt_pow hp1
  have hlx := log_le_of_lt_pow hx
  have hcmp : 4 * (Nat.log 2 (d * k + 1) + Nat.log 2 x + 1) ≤ B (3 * m + 10) :=
    le_B_of_le_linear (by omega)
  -- 1. dup 2 4 6 : 4 := k
  have ha := dup_le_B (x := 2) (y := 4) (s := 6) (by decide) (by decide) (by decide) k b hk r2 v T h2
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * B (3 * m + 10)) ha
    fun v₁ T₁ ⟨h2₁, h4₁, h6₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 2. mulC 5 4 7 6 3 : 7 := d * k
  have h5₁ : T₁ 5 = encodeNatΓ' d ++ .comma :: r5 := by
    rw [hF₁ 5 (by decide) (by decide) (by decide), h5]
  have hb2 := mulC_le_B (x := 5) (y := 4) (w := 7) (s := 6) (t := 3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    d k m hdm hkm r5 (T 4) v₁ T₁ h5₁ h4₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * B (3 * m + 10)) hb2
    fun v₂ T₂ ⟨h5₂, h4₂, h7₂, h6₂, h3₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. incr 7 4 : 7 := d * k + 1
  have h7₂' : T₂ 7 = encodeNatΓ' (d * k) ++ .comma :: T 7 := by
    rw [h7₂, hF₁ 7 (by decide) (by decide) (by decide)]
  have hc := incr_le_B (y := 7) (s := 4) (by decide) (d * k) m hdk (T 7) v₂ T₂ h7₂'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * B (3 * m + 10)) hc
    fun v₃ T₃ ⟨_, _, _, h7₃, h4₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 4. dup 7 4 6 : 4 := p
  have hd4 := dup_le_B (x := 7) (y := 4) (s := 6) (by decide) (by decide) (by decide) (d * k + 1) (m + 1) hp1
    (T 7) v₃ T₃ h7₃
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B (3 * m + 10)) hd4
    fun v₄ T₄ ⟨h7₄, h4₄, h6₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 5. dup 0 6 4 : 6 := x
  have h0₄ : T₄ 0 = encodeNatΓ' x ++ .comma :: r0 := by
    rw [hF₄ 0 (by decide) (by decide) (by decide), hF₃ 0 (by decide) (by decide),
      hF₂ 0 (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₁ 0 (by decide) (by decide) (by decide), h0]
  have he := dup_le_B (x := 0) (y := 6) (s := 4) (by decide) (by decide) (by decide) x b hx r0 v₄ T₄ h0₄
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B (3 * m + 10)) he
    fun v₅ T₅ ⟨h0₅, h6₅, h4₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 6. cmpFrag 4 6
  have h4₅' : T₅ 4 = encodeNatΓ' (d * k + 1) ++ .comma :: T 4 := by
    rw [h4₅, h4₄, h4₃, h4₂]
  have h6₄' : T₄ 6 = T 6 := by
    rw [h6₄, hF₃ 6 (by decide) (by decide), h6₂, h6₁]
  have h6₅' : T₅ 6 = encodeNatΓ' x ++ .comma :: T 6 := by rw [h6₅, h6₄']
  have hf := cmp_correct (x := 4) (y := 6) (by decide) (d * k + 1) x (T 4) (T 6) v₅ T₅ h4₅' h6₅'
  refine Frag.runs_mono hf (fun v' T' ⟨hcmp', h4', h6', hF'⟩ => ⟨hcmp', ?_, ?_, ?_, ?_, h4', ?_, h6', ?_⟩)
    (by omega)
  · rw [hF' 0 (by decide) (by decide), h0₅, h0₄, h0]
  · rw [hF' 1 (by decide) (by decide), hF₅ 1 (by decide) (by decide) (by decide),
      hF₄ 1 (by decide) (by decide) (by decide), hF₃ 1 (by decide) (by decide),
      hF₂ 1 (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₁ 1 (by decide) (by decide) (by decide)]
  · rw [hF' 2 (by decide) (by decide), hF₅ 2 (by decide) (by decide) (by decide),
      hF₄ 2 (by decide) (by decide) (by decide), hF₃ 2 (by decide) (by decide),
      hF₂ 2 (by decide) (by decide) (by decide) (by decide) (by decide), h2₁]
  · rw [hF' 3 (by decide) (by decide), hF₅ 3 (by decide) (by decide) (by decide),
      hF₄ 3 (by decide) (by decide) (by decide), hF₃ 3 (by decide) (by decide), h3₂,
      hF₁ 3 (by decide) (by decide) (by decide)]
  · rw [hF' 5 (by decide) (by decide), hF₅ 5 (by decide) (by decide) (by decide),
      hF₄ 5 (by decide) (by decide) (by decide), hF₃ 5 (by decide) (by decide), h5₂]
  · rw [hF' 7 (by decide) (by decide), hF₅ 7 (by decide) (by decide) (by decide), h7₄, h7₃]

theorem poolCmpZ_runs (z p b bp : ℕ) (hz : z < 2 ^ b) (hp : p < 2 ^ bp) (r1 r7 : List Γ')
    (v : St) (T : Stacks) (h1 : T 1 = encodeNatΓ' z ++ .comma :: r1)
    (h7 : T 7 = encodeNatΓ' p ++ .comma :: r7) :
    poolCmpZ.Runs v T (fun v' T' => v'.cmp = compare z p ∧ T' = T) (3 * B (b + bp)) := by
  have hBb : B b ≤ B (b + bp) := B_mono (by omega)
  have hBp : B bp ≤ B (b + bp) := B_mono (by omega)
  have hlz := log_le_of_lt_pow hz
  have hlp := log_le_of_lt_pow hp
  have hcmp : 4 * (Nat.log 2 z + Nat.log 2 p + 1) ≤ B (b + bp) := le_B_of_le_linear (by omega)
  -- 1. dup 1 4 6 : 4 := z
  have ha := dup_le_B (x := 1) (y := 4) (s := 6) (by decide) (by decide) (by decide) z b hz r1 v T h1
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B (b + bp)) ha
    fun v₁ T₁ ⟨h1₁, h4₁, h6₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 2. dup 7 6 4 : 6 := p
  have h7₁ : T₁ 7 = encodeNatΓ' p ++ .comma :: r7 := by
    rw [hF₁ 7 (by decide) (by decide) (by decide), h7]
  have hb2 := dup_le_B (x := 7) (y := 6) (s := 4) (by decide) (by decide) (by decide) p bp hp r7 v₁ T₁ h7₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B (b + bp)) hb2
    fun v₂ T₂ ⟨h7₂, h6₂, h4₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. cmpFrag 4 6
  have h4₂' : T₂ 4 = encodeNatΓ' z ++ .comma :: T 4 := by rw [h4₂, h4₁]
  have h6₂' : T₂ 6 = encodeNatΓ' p ++ .comma :: T 6 := by rw [h6₂, h6₁]
  have hc := cmp_correct (x := 4) (y := 6) (by decide) z p (T 4) (T 6) v₂ T₂ h4₂' h6₂'
  refine Frag.runs_mono hc (fun v' T' ⟨hcmp', h4', h6', hF'⟩ => ⟨hcmp', ?_⟩) (by omega)
  refine stacks_ext ?_ ?_ ?_ ?_ h4' ?_ h6' ?_
  · rw [hF' 0 (by decide) (by decide), hF₂ 0 (by decide) (by decide) (by decide),
      hF₁ 0 (by decide) (by decide) (by decide)]
  · rw [hF' 1 (by decide) (by decide), hF₂ 1 (by decide) (by decide) (by decide), h1₁]
  · rw [hF' 2 (by decide) (by decide), hF₂ 2 (by decide) (by decide) (by decide),
      hF₁ 2 (by decide) (by decide) (by decide)]
  · rw [hF' 3 (by decide) (by decide), hF₂ 3 (by decide) (by decide) (by decide),
      hF₁ 3 (by decide) (by decide) (by decide)]
  · rw [hF' 5 (by decide) (by decide), hF₂ 5 (by decide) (by decide) (by decide),
      hF₁ 5 (by decide) (by decide) (by decide)]
  · rw [hF' 7 (by decide) (by decide), h7₂, h7₁, h7]

/-- Loop invariant of `poolGoF` (stack-only, with the remaining budget `β`). -/
def PLInv (x z k : ℕ) (ds : List ℕ) (r3 : List Γ') (BP : ℕ) (S₀ : Stacks)
    (i β : ℕ) (T : Stacks) : Prop :=
  T 0 = S₀ 0 ∧ T 1 = S₀ 1 ∧ T 2 = S₀ 2 ∧
  T 3 = encList (Alg.poolGo x z k (ds.take i)).1.reverse ++ r3 ∧
  T 4 = S₀ 4 ∧ T 6 = S₀ 6 ∧ T 7 = S₀ 7 ∧
  β = (Alg.poolGo x z k (ds.drop i)).2 * BP

theorem poolGoBody_runs (x z k bd b : ℕ) (hx : x < 2 ^ b) (hz : z < 2 ^ b) (hk : k < 2 ^ b)
    (ds : List ℕ) (hd : ∀ d ∈ ds, d < 2 ^ bd) (r0 r1 r2 r3 r5 : List Γ') (S₀ : Stacks)
    (h0 : S₀ 0 = encodeNatΓ' x ++ .comma :: r0) (h1 : S₀ 1 = encodeNatΓ' z ++ .comma :: r1)
    (h2 : S₀ 2 = encodeNatΓ' k ++ .comma :: r2)
    (i d : ℕ) (ds' : List ℕ) (hdrop : ds.drop i = d :: ds') (β : ℕ) (w : St) (T : Stacks)
    (hP : PLInv x z k ds r3 (14 * B (3 * (bd + b) + 10)) S₀ i β T)
    (hT : T 5 = encodeNatΓ' d ++ .comma :: (encList ds' ++ r5)) :
    ∃ t β', t + 2 + β' ≤ β ∧
      poolGoBody.Runs w T (fun _ T' =>
        PLInv x z k ds r3 (14 * B (3 * (bd + b) + 10)) S₀ (i + 1) β' T' ∧ T' 5 = encList ds' ++ r5) t := by
  obtain ⟨hT0, hT1, hT2, hT3, hT4, hT6, hT7, hβ⟩ := hP
  have hdd : d < 2 ^ bd := hd d (mem_of_drop_eq_cons hdrop)
  have hdrop' : ds.drop (i + 1) = ds' := by rw [← List.tail_drop, hdrop]; rfl
  have htake := take_succ_of_drop_eq_cons hdrop
  obtain ⟨m, hm⟩ : ∃ m, bd + b = m := ⟨_, rfl⟩
  have hdk : d * k < 2 ^ m := by rw [← hm, pow_add]; exact Nat.mul_lt_mul'' hdd hk
  have hp1 : d * k + 1 < 2 ^ (m + 1) := by rw [pow_succ]; omega
  obtain ⟨BB, hBB⟩ : ∃ BB, B (3 * m + 10) = BB := ⟨_, rfl⟩
  have hB1 : 1 ≤ BB := hBB ▸ one_le_B _
  have hBb : B b ≤ BB := hBB ▸ B_mono (by omega)
  have hBm1 : B (m + 1) ≤ BB := hBB ▸ B_mono (by omega)
  have hB37 : B (3 * b + 7) ≤ BB := hBB ▸ B_mono (by omega)
  have hBbm : B (b + (m + 1)) ≤ BB := hBB ▸ B_mono (by omega)
  have hβ' : β = ((Alg.poolGo x z k ds').2 + pgc x z k d) * (14 * BB) := by
    rw [hβ, hdrop, poolGo_cons, hm, hBB]
  rw [hm, hBB]
  have hpre := poolPre_runs x k d bd b hx hk hdd r0 r2 (encList ds' ++ r5) w T
    (by rw [hT0, h0]) (by rw [hT2, h2]) hT
  rw [hm, hBB] at hpre
  -- the common post-processing: the final stack facts
  have hfin : ∀ (T' : Stacks), T' 0 = T 0 → T' 1 = T 1 → T' 2 = T 2 →
      T' 3 = (if poolKeep x z k d then encodeNatΓ' (d * k + 1) ++ .comma :: T 3 else T 3) →
      T' 4 = T 4 → T' 5 = encList ds' ++ r5 → T' 6 = T 6 → T' 7 = T 7 →
      PLInv x z k ds r3 (14 * BB) S₀ (i + 1) ((Alg.poolGo x z k ds').2 * (14 * BB)) T' ∧
        T' 5 = encList ds' ++ r5 := by
    intro T' e0 e1 e2 e3 e4 e5 e6 e7
    refine ⟨⟨e0.trans hT0, e1.trans hT1, e2.trans hT2, ?_, e4.trans hT4, e6.trans hT6, e7.trans hT7,
      by rw [hdrop']⟩, e5⟩
    rw [e3, hT3, htake, poolGo_append, poolGo_single]
    dsimp only
    rw [List.reverse_append]
    split_ifs <;> simp [encList_cons]
  by_cases hpx : d * k + 1 ≤ x
  · have hc1 : ∀ v' : St, v'.cmp = compare (d * k + 1) x → (!decide (v'.cmp = Ordering.gt)) = true := by
      intro v' hv'; simp [hv', compare_gt_iff_gt, not_lt.mpr hpx]
    by_cases hzp : z < d * k + 1
    · -- both tests pass: primality test
      have hpgc : pgc x z k d = (Alg.isPrimeTD (d * k + 1)).2 + 1 := by
        unfold pgc; rw [if_pos ⟨hpx, hzp⟩]
      have hpb : d * k + 1 < 2 ^ b := lt_of_le_of_lt hpx hx
      have hlp := log_le_of_lt_pow hpb
      have hmv : 2 * Nat.log 2 (d * k + 1) + 6 ≤ B b := le_B_of_le_linear (by omega)
      refine ⟨6 * BB + (3 * BB + (((Alg.isPrimeTD (d * k + 1)).2 + 1) * BB + (BB + 1) + 1) + 1),
        (Alg.poolGo x z k ds').2 * (14 * BB), ?_, ?_⟩
      · rw [hβ', hpgc]; nlinarith
      refine Frag.seq_runs (t₂ := 3 * BB + (((Alg.isPrimeTD (d * k + 1)).2 + 1) * BB + (BB + 1) + 1) + 1)
        hpre fun v₁ T₁ ⟨hcmp₁, e0, e1, e2, e3, e4, e5, e6, e7⟩ => ?_
      refine Frag.ite_runs_true (hc1 v₁ hcmp₁) ?_
      have hq := poolCmpZ_runs z (d * k + 1) b (m + 1) hz hp1 r1 (T 7) v₁ T₁ (by rw [e1, hT1, h1]) e7
      refine Frag.runs_mono (Frag.seq_runs (t₂ := ((Alg.isPrimeTD (d * k + 1)).2 + 1) * BB + (BB + 1) + 1)
        hq fun v₂ T₂ ⟨hcmp₂, hT₂⟩ => ?_) (fun _ _ h => h) (by omega)
      rw [hT₂]
      have hc2 : decide (v₂.cmp = Ordering.lt) = true := by simp [hcmp₂, compare_lt_iff_lt, hzp]
      refine Frag.ite_runs_true hc2 ?_
      have hpr := isPrimeTDF_le_B (xm := 7) (xd := 4) (xf := 6) (s := 0) (t := 1) (u := 2)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (d * k + 1) b hpb (T 7) v₂ T₁ e7
      refine Frag.runs_mono (Frag.seq_runs (t₂ := BB + 1) hpr
        fun v₃ T₃ ⟨hfl₃, f7, f4, f6, f0, f1, f2, hF₃⟩ => ?_) (fun _ _ h => h)
        (by have := Nat.mul_le_mul_left ((Alg.isPrimeTD (d * k + 1)).2 + 1) hB37; omega)
      have hT₃ : T₃ = T₁ := stacks_ext f0 f1 f2 (hF₃ 3 (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)) f4 (hF₃ 5 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)) f6 f7
      rw [hT₃]
      refine Frag.ite_runs (t := BB) (fun hfl => ?_) (fun hfl => ?_)
      · have hpr' : (Alg.isPrimeTD (d * k + 1)).1 = true := by rw [← hfl₃]; exact hfl
        have hkeep : poolKeep x z k d = true := poolKeep_eq_true.2 ⟨⟨hpx, hzp⟩, hpr'⟩
        have hmv' := moveEntry_correct (src := 7) (dst := 3) (s := 4) (by decide) (by decide) (by decide)
          (d * k + 1) (T 7) v₃ T₁ e7
        refine Frag.runs_mono hmv' (fun _ T' ⟨_, _, _, g7, g3, g4, hF'⟩ => hfin T' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          (by omega)
        · rw [hF' 0 (by decide) (by decide) (by decide), e0]
        · rw [hF' 1 (by decide) (by decide) (by decide), e1]
        · rw [hF' 2 (by decide) (by decide) (by decide), e2]
        · rw [g3, e3, if_pos hkeep]
        · rw [g4, e4]
        · rw [hF' 5 (by decide) (by decide) (by decide), e5]
        · rw [hF' 6 (by decide) (by decide) (by decide), e6]
        · rw [g7]
      · have hpr' : (Alg.isPrimeTD (d * k + 1)).1 = false := by rw [← hfl₃]; exact hfl
        have hkeep : poolKeep x z k d = false := by
          unfold poolKeep; rw [hpr']; simp
        have hdr := dropNum_le_B (x := 7) (d * k + 1) (m + 1) hp1 (T 7) v₃ T₁ e7
        refine Frag.runs_mono hdr (fun _ T' ⟨_, _, _, g7, hF'⟩ => hfin T' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_)
          (by omega)
        · rw [hF' 0 (by decide), e0]
        · rw [hF' 1 (by decide), e1]
        · rw [hF' 2 (by decide), e2]
        · rw [hF' 3 (by decide), e3, if_neg (by simp [hkeep])]
        · rw [hF' 4 (by decide), e4]
        · rw [hF' 5 (by decide), e5]
        · rw [hF' 6 (by decide), e6]
        · rw [g7]
    · -- `p ≤ x` but not `z < p`
      have hpgc : pgc x z k d = 1 := by
        unfold pgc; rw [if_neg (by tauto)]
      have hkeep : poolKeep x z k d = false := by
        unfold poolKeep; simp [hzp]
      refine ⟨6 * BB + (3 * BB + (BB + 1)) + 1, (Alg.poolGo x z k ds').2 * (14 * BB), ?_, ?_⟩
      · rw [hβ', hpgc]; nlinarith
      refine Frag.seq_runs (t₂ := 3 * BB + (BB + 1) + 1) hpre
        fun v₁ T₁ ⟨hcmp₁, e0, e1, e2, e3, e4, e5, e6, e7⟩ => ?_
      refine Frag.ite_runs_true (hc1 v₁ hcmp₁) ?_
      have hq := poolCmpZ_runs z (d * k + 1) b (m + 1) hz hp1 r1 (T 7) v₁ T₁ (by rw [e1, hT1, h1]) e7
      refine Frag.runs_mono (Frag.seq_runs (t₂ := BB + 1) hq fun v₂ T₂ ⟨hcmp₂, hT₂⟩ => ?_)
        (fun _ _ h => h) (by omega)
      rw [hT₂]
      have hc2 : decide (v₂.cmp = Ordering.lt) = false := by simp [hcmp₂, compare_lt_iff_lt, hzp]
      refine Frag.ite_runs_false hc2 ?_
      have hdr := dropNum_le_B (x := 7) (d * k + 1) (m + 1) hp1 (T 7) v₂ T₁ e7
      refine Frag.runs_mono hdr (fun _ T' ⟨_, _, _, g7, hF'⟩ => hfin T' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by omega)
      · rw [hF' 0 (by decide), e0]
      · rw [hF' 1 (by decide), e1]
      · rw [hF' 2 (by decide), e2]
      · rw [hF' 3 (by decide), e3, if_neg (by simp [hkeep])]
      · rw [hF' 4 (by decide), e4]
      · rw [hF' 5 (by decide), e5]
      · rw [hF' 6 (by decide), e6]
      · rw [g7]
  · -- not `p ≤ x`
    have hpgc : pgc x z k d = 1 := by
      unfold pgc; rw [if_neg (by tauto)]
    have hkeep : poolKeep x z k d = false := by
      unfold poolKeep; simp [hpx]
    refine ⟨6 * BB + (BB + 1), (Alg.poolGo x z k ds').2 * (14 * BB), ?_, ?_⟩
    · rw [hβ', hpgc]; nlinarith
    refine Frag.seq_runs (t₂ := BB + 1) hpre fun v₁ T₁ ⟨hcmp₁, e0, e1, e2, e3, e4, e5, e6, e7⟩ => ?_
    have hc1 : (!decide (v₁.cmp = Ordering.gt)) = false := by
      simp [hcmp₁, compare_gt_iff_gt, not_le.mp hpx]
    refine Frag.ite_runs_false hc1 ?_
    have hdr := dropNum_le_B (x := 7) (d * k + 1) (m + 1) hp1 (T 7) v₁ T₁ e7
    refine Frag.runs_mono hdr (fun _ T' ⟨_, _, _, g7, hF'⟩ => hfin T' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) (by omega)
    · rw [hF' 0 (by decide), e0]
    · rw [hF' 1 (by decide), e1]
    · rw [hF' 2 (by decide), e2]
    · rw [hF' 3 (by decide), e3, if_neg (by simp [hkeep])]
    · rw [hF' 4 (by decide), e4]
    · rw [hF' 5 (by decide), e5]
    · rw [hF' 6 (by decide), e6]
    · rw [g7]

/-- `poolGo x z k ds` on the machine: `ds` on `5` (consumed), `x` on `0`, `z`
on `1`, `k` on `2` (peeked); `encList (Alg.poolGo x z k ds).1` pushed on `6`;
`3`, `4`, `7` scratch (restored). -/
def poolGoF : Frag :=
  (Frag.pushSym 3 .bra).seq ((forEntries 5 poolGoBody).seq ((popTop 5).seq (revList 3 6 4)))

theorem poolGoF_runs (x z k bd b : ℕ) (hx : x < 2 ^ b) (hz : z < 2 ^ b) (hk : k < 2 ^ b)
    (ds : List ℕ) (hd : ∀ d ∈ ds, d < 2 ^ bd) (r0 r1 r2 r5 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' x ++ .comma :: r0) (h1 : S 1 = encodeNatΓ' z ++ .comma :: r1)
    (h2 : S 2 = encodeNatΓ' k ++ .comma :: r2) (h5 : S 5 = encList ds ++ r5) :
    poolGoF.Runs v S (fun _ S' =>
        S' 0 = S 0 ∧ S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = S 3 ∧ S' 4 = S 4 ∧ S' 5 = r5 ∧
        S' 6 = encList (Alg.poolGo x z k ds).1 ++ S 6 ∧ S' 7 = S 7)
      (((Alg.poolGo x z k ds).2 + 1) * (16 * B (3 * (bd + b) + 10))) := by
  obtain ⟨BB, hBB⟩ : ∃ BB, B (3 * (bd + b) + 10) = BB := ⟨_, rfl⟩
  have hB1 : 1 ≤ BB := hBB ▸ one_le_B _
  have hBb : B b ≤ BB := hBB ▸ B_mono (by omega)
  have hlen := poolGo_length_le_cost x z k ds
  obtain ⟨n, hn⟩ : ∃ n, (Alg.poolGo x z k ds).2 = n := ⟨_, rfl⟩
  obtain ⟨len, hl⟩ : ∃ len, (Alg.poolGo x z k ds).1.length = len := ⟨_, rfl⟩
  rw [hn, hl] at hlen
  rw [hn, hBB]
  -- 1. pushSym 3 bra
  refine Frag.runs_mono (Frag.seq_runs (t₂ := n * (14 * BB) + 2 + 1 + (len + 1) * B b)
    (Frag.pushSym_runs 3 .bra v S) fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) ?_
  swap
  · have := Nat.mul_le_mul (Nat.add_le_add_right hlen 1) hBb
    nlinarith
  rw [hv₁]; subst hS₁
  -- 2. the loop
  have hloop := forEntriesN_runs_budget (x := 5) (body := poolGoBody) ds r5
    (PLInv x z k ds (S 3) (14 * BB) S) (n * (14 * BB)) v (Function.update S 3 (Γ'.bra :: S 3))
    (by rw [Function.update_of_ne (by decide), h5])
    ⟨by simp, by simp, by simp, by simp [poolGo_nil], by simp, by simp, by simp, by simp [hn]⟩
    (fun i d ds' hdrop β w T hP hT => by
      have := poolGoBody_runs x z k bd b hx hz hk ds hd r0 r1 r2 (S 3) r5 S h0 h1 h2 i d ds' hdrop β w T
        (by rwa [← hBB] at hP) hT
      rwa [hBB] at this)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1 + (len + 1) * B b) hloop
    fun v₂ S₂ ⟨_, ⟨β, e0, e1, e2, e3, e4, e6, e7, _⟩, e5⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. popTop 5
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (len + 1) * B b) (popTop_runs 5 v₂ S₂)
    fun v₃ S₃ ⟨hv₃, hS₃⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₃]; subst hS₃
  -- 4. revList 3 6 4
  rw [List.take_length] at e3
  have hmem : ∀ a ∈ (Alg.poolGo x z k ds).1.reverse, a < 2 ^ b := by
    intro a ha
    rw [List.mem_reverse] at ha
    exact lt_of_le_of_lt (poolGo_mem ha).1 hx
  have e3' : Function.update S₂ 5 (S₂ 5).tail 3 = encList (Alg.poolGo x z k ds).1.reverse ++ S 3 := by
    rw [Function.update_of_ne (by decide), e3]
  have hR := revList_le_B (x := 3) (y := 6) (s := 4) (by decide) (by decide) (by decide) _ b hmem (S 3)
    v₂ _ e3'
  refine Frag.runs_mono hR (fun _ S₄ ⟨g3, g6, g4, hF₄⟩ => ⟨?_, ?_, ?_, g3, ?_, ?_, ?_, ?_⟩)
    (by simp only [List.length_reverse, hl]; exact le_rfl)
  · rw [hF₄ 0 (by decide) (by decide) (by decide), Function.update_of_ne (by decide), e0]
  · rw [hF₄ 1 (by decide) (by decide) (by decide), Function.update_of_ne (by decide), e1]
  · rw [hF₄ 2 (by decide) (by decide) (by decide), Function.update_of_ne (by decide), e2]
  · rw [g4, Function.update_of_ne (by decide), e4]
  · rw [hF₄ 5 (by decide) (by decide) (by decide), Function.update_self, e5]; rfl
  · rw [g6, Function.update_of_ne (by decide), e6, List.reverse_reverse]
  · rw [hF₄ 7 (by decide) (by decide) (by decide), Function.update_of_ne (by decide), e7]

/-- `poolGoF` in `B`-form: `((Alg.poolGo x z k ds).2 + 1) * B (9 (bd + b) + 34)`
for `∀ d ∈ ds, d < 2 ^ bd` and `x, z, k < 2 ^ b`. -/
theorem poolGoF_le_B (x z k bd b : ℕ) (hx : x < 2 ^ b) (hz : z < 2 ^ b) (hk : k < 2 ^ b)
    (ds : List ℕ) (hd : ∀ d ∈ ds, d < 2 ^ bd) (r0 r1 r2 r5 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' x ++ .comma :: r0) (h1 : S 1 = encodeNatΓ' z ++ .comma :: r1)
    (h2 : S 2 = encodeNatΓ' k ++ .comma :: r2) (h5 : S 5 = encList ds ++ r5) :
    poolGoF.Runs v S (fun _ S' =>
        S' 0 = S 0 ∧ S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = S 3 ∧ S' 4 = S 4 ∧ S' 5 = r5 ∧
        S' 6 = encList (Alg.poolGo x z k ds).1 ++ S 6 ∧ S' 7 = S 7)
      (((Alg.poolGo x z k ds).2 + 1) * B (9 * (bd + b) + 34)) := by
  refine Frag.runs_mono (poolGoF_runs x z k bd b hx hz hk ds hd r0 r1 r2 r5 v S h0 h1 h2 h5)
    (fun _ _ h => h) ?_
  rw [show 9 * (bd + b) + 34 = 3 * (3 * (bd + b) + 10) + 4 by ring, ← B_twentyseven]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by norm_num))

/-! ### `poolAlg` -/

/-- `poolAlg Q x z k`: `Q` on `4` (restored; copied to `5`), `divisorsOfF`
on the copy, then `poolGoF`.  `x` on `0`, `z` on `1`, `k` on `2` (peeked);
result `encList (Alg.poolAlg Q x z k).1` pushed on `6`; `3`, `5`, `7`
scratch (restored). -/
def poolAlgF : Frag := (copyList 4 5 7 3).seq ((divisorsOfF 5 3 7 6 0 1).seq poolGoF)

theorem poolAlgF_runs (Q : List ℕ) (x z k bq b : ℕ) (hQ : ∀ q ∈ Q, q < 2 ^ bq)
    (hx : x < 2 ^ b) (hz : z < 2 ^ b) (hk : k < 2 ^ b) (r0 r1 r2 r4 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' x ++ .comma :: r0) (h1 : S 1 = encodeNatΓ' z ++ .comma :: r1)
    (h2 : S 2 = encodeNatΓ' k ++ .comma :: r2) (h4 : S 4 = encList Q ++ r4) :
    poolAlgF.Runs v S (fun _ S' =>
        S' 0 = S 0 ∧ S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = S 3 ∧ S' 4 = S 4 ∧ S' 5 = S 5 ∧
        S' 6 = encList (Alg.poolAlg Q x z k).1 ++ S 6 ∧ S' 7 = S 7)
      (((Alg.poolAlg Q x z k).2 + 1) * (32 * B (12 * (Q.length + 1) * bq + 3 * b + 22))) := by
  obtain ⟨MP, hMP⟩ : ∃ MP, 12 * (Q.length + 1) * bq + 3 * b + 22 = MP := ⟨_, rfl⟩
  have hB1 := one_le_B MP
  have hBq : B bq ≤ B MP := B_mono (by rw [← hMP]; nlinarith)
  have hBd : B (12 * Q.length * bq + 22) ≤ B MP := B_mono (by rw [← hMP]; nlinarith)
  have hBp : B (3 * (Q.length * bq + 1 + b) + 10) ≤ B MP := B_mono (by rw [← hMP]; nlinarith)
  have hQ1 : Q.length + 1 ≤ 2 ^ Q.length := two_pow_mul_le _
  have hds : ∀ d ∈ (Alg.divisorsOf Q).1, d < 2 ^ (Q.length * bq + 1) := by
    intro d hd
    have := divisorsOf_mem_le hQ d hd
    calc d ≤ 2 ^ (Q.length * bq) := this
      _ < 2 ^ (Q.length * bq + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [poolAlg_eq, hMP]
  dsimp only
  obtain ⟨n, hn⟩ : ∃ n, (Alg.poolGo x z k (Alg.divisorsOf Q).1).2 = n := ⟨_, rfl⟩
  rw [hn, divisorsOf_snd]
  have h2Q := Nat.one_le_two_pow (n := Q.length)
  -- 1. copyList 4 5 7 3
  have ha := copyList_le_B (x := 4) (y := 5) (s := 7) (z := 3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) Q bq hQ r4 v S h4
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := 2 ^ Q.length * B (12 * Q.length * bq + 22) + (n + 1) * (16 * B (3 * (Q.length * bq + 1 + b) + 10)))
    ha fun v₁ S₁ ⟨e4, e5, e7, e3, hF₁⟩ => ?_) (fun _ _ h => h) ?_
  swap
  · have t1 : (Q.length + 1) * B bq ≤ 2 ^ Q.length * B MP := Nat.mul_le_mul hQ1 hBq
    have t2 : 2 ^ Q.length * B (12 * Q.length * bq + 22) ≤ 2 ^ Q.length * B MP :=
      Nat.mul_le_mul_left _ hBd
    have t3 : (n + 1) * (16 * B (3 * (Q.length * bq + 1 + b) + 10)) ≤ (n + 1) * (16 * B MP) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hBp)
    have t4 : 2 ^ Q.length - 1 + n + 1 = 2 ^ Q.length + n := by omega
    rw [t4]
    nlinarith
  -- 2. divisorsOfF 5 3 7 6 0 1
  have hb := divisorsOfF_le_B (x := 5) (z := 3) (a := 7) (c := 6) (s := 0) (t := 1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) Q bq hQ (S 5) v₁ S₁ e5
  rw [divisorsOf_snd, Nat.sub_add_cancel h2Q] at hb
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (n + 1) * (16 * B (3 * (Q.length * bq + 1 + b) + 10))) hb
    fun v₂ S₂ ⟨f5, f3, f7, f6, f0, f1, hF₂⟩ => ?_) (fun _ _ h => h) le_rfl
  -- 3. poolGoF
  have g0 : S₂ 0 = encodeNatΓ' x ++ .comma :: r0 := by
    rw [f0, hF₁ 0 (by decide) (by decide) (by decide) (by decide), h0]
  have g1 : S₂ 1 = encodeNatΓ' z ++ .comma :: r1 := by
    rw [f1, hF₁ 1 (by decide) (by decide) (by decide) (by decide), h1]
  have g2 : S₂ 2 = encodeNatΓ' k ++ .comma :: r2 := by
    rw [hF₂ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₁ 2 (by decide) (by decide) (by decide) (by decide), h2]
  have hc := poolGoF_runs x z k (Q.length * bq + 1) b hx hz hk (Alg.divisorsOf Q).1 hds r0 r1 r2 (S 5)
    v₂ S₂ g0 g1 g2 f5
  rw [hn] at hc
  refine Frag.runs_mono hc (fun _ S₃ ⟨g0', g1', g2', g3', g4', g5', g6', g7'⟩ =>
    ⟨?_, ?_, ?_, ?_, ?_, g5', ?_, ?_⟩) le_rfl
  · rw [g0', f0, hF₁ 0 (by decide) (by decide) (by decide) (by decide)]
  · rw [g1', f1, hF₁ 1 (by decide) (by decide) (by decide) (by decide)]
  · rw [g2', hF₂ 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₁ 2 (by decide) (by decide) (by decide) (by decide)]
  · rw [g3', f3, e3]
  · rw [g4', hF₂ 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), e4]
  · rw [g6', f6, hF₁ 6 (by decide) (by decide) (by decide) (by decide)]
  · rw [g7', f7, e7]

/-- `poolAlgF` in `B`-form: `((Alg.poolAlg Q x z k).2 + 1) * B (48 (|Q| + 1) bq + 12 b + 94)`
for `∀ q ∈ Q, q < 2 ^ bq` and `x, z, k < 2 ^ b`. -/
theorem poolAlgF_le_B (Q : List ℕ) (x z k bq b : ℕ) (hQ : ∀ q ∈ Q, q < 2 ^ bq)
    (hx : x < 2 ^ b) (hz : z < 2 ^ b) (hk : k < 2 ^ b) (r0 r1 r2 r4 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' x ++ .comma :: r0) (h1 : S 1 = encodeNatΓ' z ++ .comma :: r1)
    (h2 : S 2 = encodeNatΓ' k ++ .comma :: r2) (h4 : S 4 = encList Q ++ r4) :
    poolAlgF.Runs v S (fun _ S' =>
        S' 0 = S 0 ∧ S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = S 3 ∧ S' 4 = S 4 ∧ S' 5 = S 5 ∧
        S' 6 = encList (Alg.poolAlg Q x z k).1 ++ S 6 ∧ S' 7 = S 7)
      (((Alg.poolAlg Q x z k).2 + 1) * B (48 * (Q.length + 1) * bq + 12 * b + 94)) := by
  refine Frag.runs_mono (poolAlgF_runs Q x z k bq b hQ hx hz hk r0 r1 r2 r4 v S h0 h1 h2 h4)
    (fun _ _ h => h) ?_
  have h64 : 64 * B (12 * (Q.length + 1) * bq + 3 * b + 22) =
      B (48 * (Q.length + 1) * bq + 12 * b + 94) := by
    rw [show 64 = (3 + 1) ^ 3 by norm_num, B_scale]; congr 1; ring
  rw [← h64]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by norm_num))


/-! ### Route A facts: `scan` -/

theorem poolGo_length_le_length (x z k : ℕ) (ds : List ℕ) :
    (Alg.poolGo x z k ds).1.length ≤ ds.length := by
  induction ds with
  | nil => simp [poolGo_nil]
  | cons d ds ih =>
    rw [poolGo_cons]
    dsimp only
    split_ifs
    · simp only [List.length_cons]; omega
    · simp only [List.length_cons]; omega

theorem poolAlg_length_le_two_pow (Q : List ℕ) (x z k : ℕ) :
    (Alg.poolAlg Q x z k).1.length ≤ 2 ^ Q.length := by
  rw [poolAlg_eq]
  dsimp only
  rw [← divisorsOf_length Q]
  exact poolGo_length_le_length _ _ _ _

theorem scan_zero (Q : List ℕ) (x z θ k : ℕ) : Alg.scan Q x z θ k 0 = (none, 0) := rfl

theorem scan_succ_raw (Q : List ℕ) (x z θ k f : ℕ) :
    Alg.scan Q x z θ k (f + 1) =
      (if (Alg.coprimeTo Q k).1 then
        (if θ ≤ (Alg.poolAlg Q x z k).1.length then
          (some (k, (Alg.poolAlg Q x z k).1), (Alg.coprimeTo Q k).2 + (Alg.poolAlg Q x z k).2 + 1)
         else ((Alg.scan Q x z θ (k + 1) f).1,
          (Alg.scan Q x z θ (k + 1) f).2 + (Alg.coprimeTo Q k).2 + (Alg.poolAlg Q x z k).2 + 1))
      else ((Alg.scan Q x z θ (k + 1) f).1,
        (Alg.scan Q x z θ (k + 1) f).2 + (Alg.coprimeTo Q k).2 + 1)) := rfl

/-- Number of body executions of the `scan` loop (the recursion of `scan`
with the counting only). -/
def scanIters (Q : List ℕ) (x z θ : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | k, fuel + 1 =>
    if (Alg.coprimeTo Q k).1 then
      (if θ ≤ (Alg.poolAlg Q x z k).1.length then 1 else scanIters Q x z θ (k + 1) fuel + 1)
    else scanIters Q x z θ (k + 1) fuel + 1

theorem scanIters_zero (Q : List ℕ) (x z θ k : ℕ) : scanIters Q x z θ k 0 = 0 := rfl

theorem scanIters_succ (Q : List ℕ) (x z θ k f : ℕ) :
    scanIters Q x z θ k (f + 1) =
      if (Alg.coprimeTo Q k).1 then
        (if θ ≤ (Alg.poolAlg Q x z k).1.length then 1 else scanIters Q x z θ (k + 1) f + 1)
      else scanIters Q x z θ (k + 1) f + 1 := rfl

theorem scanIters_le_fuel (Q : List ℕ) (x z θ k fuel : ℕ) : scanIters Q x z θ k fuel ≤ fuel := by
  induction fuel generalizing k with
  | zero => simp [scanIters_zero]
  | succ f ih =>
    rw [scanIters_succ]
    have := ih (k + 1)
    split_ifs <;> omega

theorem scanIters_pos (Q : List ℕ) (x z θ k : ℕ) {fuel : ℕ} (h : 0 < fuel) :
    0 < scanIters Q x z θ k fuel := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  rw [scanIters_succ]
  split_ifs <;> omega

theorem scanIters_le_cost (Q : List ℕ) (x z θ k fuel : ℕ) :
    scanIters Q x z θ k fuel ≤ (Alg.scan Q x z θ k fuel).2 + 1 := by
  induction fuel generalizing k with
  | zero => simp [scanIters_zero]
  | succ f ih =>
    rw [scanIters_succ, scan_succ_raw]
    have := ih (k + 1)
    split_ifs <;> dsimp only <;> omega

/-! ### `scan`: the search for `k`

Stacks: `x :: θ` on `0`, `z :: fuel` on `1`, `k` on `2`, `Q` on `4`; the
pool of the current `k` is built on `6`; `3`, `5`, `7` scratch.  Loop test
`carry` ("continue"), result `flag` ("success"), both set by the `load'`
ending every branch.  Body: `coprimeToF Q k`; if coprime, `poolAlgF`,
`listLen`, `θ ≤ |P|` by `cmpFrag` on copies (`x` is moved aside to reach
`θ`); success stops with `carry := false, flag := true`, else the pool is
dropped and `scanNext` runs (`incr k`, `predNum fuel` with `z` moved aside,
`isZero fuel`, `carry := !flag, flag := false`). -/

/-- The continue step: `k := k + 1`, `fuel := fuel - 1`, `carry := (fuel ≠ 0)`,
`flag := false`. -/
def scanNext : Frag :=
  (incr 2 5).seq ((moveEntry 1 7 5).seq ((predNum 1 5).seq ((isZero 1 5).seq ((moveEntry 7 1 5).seq
    (Frag.load' (fun v => { v with carry := !v.flag, flag := false }))))))

theorem scanNext_runs (z k' f b : ℕ) (hz : z < 2 ^ b) (hk : k' + 1 < 2 ^ b) (hf : f + 1 < 2 ^ b)
    (r1 r2 : List Γ') (v : St) (S : Stacks)
    (h1 : S 1 = encodeNatΓ' z ++ .comma :: (encodeNatΓ' (f + 1) ++ .comma :: r1))
    (h2 : S 2 = encodeNatΓ' k' ++ .comma :: r2) :
    scanNext.Runs v S (fun v' S' =>
        v'.carry = !decide (f = 0) ∧ v'.flag = false ∧
        S' 0 = S 0 ∧ S' 1 = encodeNatΓ' z ++ .comma :: (encodeNatΓ' f ++ .comma :: r1) ∧
        S' 2 = encodeNatΓ' (k' + 1) ++ .comma :: r2 ∧ S' 3 = S 3 ∧ S' 4 = S 4 ∧ S' 5 = S 5 ∧
        S' 6 = S 6 ∧ S' 7 = S 7)
      (5 * B b + 1) := by
  have hlz := log_le_of_lt_pow hz
  have hmv : 2 * Nat.log 2 z + 6 ≤ B b := le_B_of_le_linear (by omega)
  -- 1. incr 2 5
  have ha := incr_le_B (y := 2) (s := 5) (by decide) k' b (by omega) r2 v S h2
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * B b + 1) ha
    fun v₁ S₁ ⟨_, _, _, h2₁, h5₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 2. moveEntry 1 7 5 : z to 7
  have hb := moveEntry_correct (src := 1) (dst := 7) (s := 5) (by decide) (by decide) (by decide) z _ v₁ S₁
    (by rw [hF₁ 1 (by decide) (by decide), h1])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * B b + 1) hb
    fun v₂ S₂ ⟨_, _, _, h1₂, h7₂, h5₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. predNum 1 5
  have hc := predNum_le_B (x := 1) (s := 5) (by decide) (f + 1) b (by omega) hf r1 v₂ S₂ h1₂
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B b + 1) hc
    fun v₃ S₃ ⟨_, _, h1₃, h5₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [Nat.add_sub_cancel] at h1₃
  -- 4. isZero 1 5
  have hd := isZero_le_B (x := 1) (s := 5) (by decide) f b (by omega) r1 v₃ S₃ h1₃
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + 1) hd
    fun v₄ S₄ ⟨hfl₄, _, h1₄, h5₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 5. moveEntry 7 1 5 : z back
  have h7₄ : S₄ 7 = encodeNatΓ' z ++ .comma :: S 7 := by
    rw [hF₄ 7 (by decide) (by decide), hF₃ 7 (by decide) (by decide), h7₂,
      hF₁ 7 (by decide) (by decide)]
  have he := moveEntry_correct (src := 7) (dst := 1) (s := 5) (by decide) (by decide) (by decide) z _ v₄ S₄ h7₄
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) he
    fun v₅ S₅ ⟨hfl₅, _, _, h7₅, h1₅, h5₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 6. load'
  refine Frag.runs_mono (Frag.load'_runs _ v₅ S₅) (fun v' S' ⟨hv', hS'⟩ => ?_) le_rfl
  rw [hv', hS']
  refine ⟨by simp [hfl₅, hfl₄], rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h7₅⟩
  · rw [hF₅ 0 (by decide) (by decide) (by decide), hF₄ 0 (by decide) (by decide),
      hF₃ 0 (by decide) (by decide), hF₂ 0 (by decide) (by decide) (by decide),
      hF₁ 0 (by decide) (by decide)]
  · rw [h1₅, h1₄, h1₃]
  · rw [hF₅ 2 (by decide) (by decide) (by decide), hF₄ 2 (by decide) (by decide),
      hF₃ 2 (by decide) (by decide), hF₂ 2 (by decide) (by decide) (by decide), h2₁]
  · rw [hF₅ 3 (by decide) (by decide) (by decide), hF₄ 3 (by decide) (by decide),
      hF₃ 3 (by decide) (by decide), hF₂ 3 (by decide) (by decide) (by decide),
      hF₁ 3 (by decide) (by decide)]
  · rw [hF₅ 4 (by decide) (by decide) (by decide), hF₄ 4 (by decide) (by decide),
      hF₃ 4 (by decide) (by decide), hF₂ 4 (by decide) (by decide) (by decide),
      hF₁ 4 (by decide) (by decide)]
  · rw [h5₅, h5₄, h5₃, h5₂, h5₁]
  · rw [hF₅ 6 (by decide) (by decide) (by decide), hF₄ 6 (by decide) (by decide),
      hF₃ 6 (by decide) (by decide), hF₂ 6 (by decide) (by decide) (by decide),
      hF₁ 6 (by decide) (by decide)]

/-- The pool test of one `scan` iteration: `poolAlgF` (pool on `6`),
`listLen` (`|P|` on `3`), `θ` copied to `5` (with `x` moved aside and back),
`cmp := compare θ |P|`.  Everything but the pool is restored. -/
def scanTest : Frag :=
  poolAlgF.seq ((listLen 6 3 7 5).seq ((moveEntry 0 7 5).seq ((dup 0 5 4).seq
    ((moveEntry 7 0 5).seq (cmpFrag 5 3)))))

theorem scanTest_runs (Q : List ℕ) (x z θ k' bq b : ℕ) (hQ : ∀ q ∈ Q, q < 2 ^ bq)
    (hx : x < 2 ^ b) (hz : z < 2 ^ b) (hθ : θ < 2 ^ b) (hk : k' < 2 ^ b)
    (r0 r1 r2 r4 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' x ++ .comma :: (encodeNatΓ' θ ++ .comma :: r0))
    (h1 : S 1 = encodeNatΓ' z ++ .comma :: r1) (h2 : S 2 = encodeNatΓ' k' ++ .comma :: r2)
    (h4 : S 4 = encList Q ++ r4) :
    scanTest.Runs v S (fun v' S' =>
        v'.cmp = compare θ (Alg.poolAlg Q x z k').1.length ∧
        S' 0 = S 0 ∧ S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = S 3 ∧ S' 4 = S 4 ∧ S' 5 = S 5 ∧
        S' 6 = encList (Alg.poolAlg Q x z k').1 ++ S 6 ∧ S' 7 = S 7)
      (((Alg.poolAlg Q x z k').2 + 1) * (32 * B (12 * (Q.length + 1) * (bq + b) + Q.length + 24)) +
        ((Alg.poolAlg Q x z k').1.length + 1) * B (12 * (Q.length + 1) * (bq + b) + Q.length + 24) +
        4 * B (12 * (Q.length + 1) * (bq + b) + Q.length + 24)) := by
  obtain ⟨MS, hMS⟩ : ∃ MS, 12 * (Q.length + 1) * (bq + b) + Q.length + 24 = MS := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, B MS = U := ⟨_, rfl⟩
  rw [hMS, hU]
  have hU1 : 1 ≤ U := hU ▸ one_le_B _
  have hUb : B b ≤ U := hU ▸ B_mono (by rw [← hMS]; nlinarith)
  have hUpa : B (12 * (Q.length + 1) * bq + 3 * b + 22) ≤ U := hU ▸ B_mono (by rw [← hMS]; nlinarith)
  have hUll : B (b + Q.length + 1) ≤ U := hU ▸ B_mono (by rw [← hMS]; nlinarith)
  have hPmem : ∀ p ∈ (Alg.poolAlg Q x z k').1, p < 2 ^ b := fun p hp =>
    lt_of_le_of_lt (poolAlg_mem hp).1 hx
  have hPl2 : (Alg.poolAlg Q x z k').1.length < 2 ^ (Q.length + 1) :=
    lt_of_le_of_lt (poolAlg_length_le_two_pow Q x z k') (Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hlP := log_le_of_lt_pow hPl2
  have hlθ := log_le_of_lt_pow hθ
  have hlx := log_le_of_lt_pow hx
  have hmvx : 2 * Nat.log 2 x + 6 ≤ B b := le_B_of_le_linear (by omega)
  have hcmpb : 4 * (Nat.log 2 θ + Nat.log 2 (Alg.poolAlg Q x z k').1.length + 1) ≤
      B (b + Q.length + 1) := le_B_of_le_linear (by omega)
  obtain ⟨c, hc⟩ : ∃ c, (Alg.poolAlg Q x z k').2 = c := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, (Alg.poolAlg Q x z k').1.length = e := ⟨_, rfl⟩
  rw [hc, he]
  rw [he] at hcmpb hlP
  -- 1. poolAlgF
  have hpa := poolAlgF_runs Q x z k' bq b hQ hx hz hk _ _ r2 r4 v S h0 h1 h2 h4
  rw [hc] at hpa
  have hpa' := Frag.runs_mono hpa (fun _ _ h => h)
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hUpa))
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (e + 1) * U + U + U + U + U) hpa'
    fun v₂ S₂ ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 2. listLen 6 3 7 5
  have hll := listLen_correct (x := 6) (y := 3) (s := 7) (z := 5) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (Alg.poolAlg Q x z k').1 b hPmem (S 6) v₂ S₂ g6
  rw [he] at hll
  have hll' := Frag.runs_mono hll (fun _ _ h => h)
    (show e * (4 * b + 2 * Nat.log 2 e + 17) + 10 ≤ (e + 1) * U from
      le_trans (list_le_B (b := b + Q.length + 1) (by omega) (by omega))
        (Nat.mul_le_mul_left _ hUll))
  refine Frag.runs_mono (Frag.seq_runs (t₂ := U + U + U + U) hll'
    fun v₃ S₃ ⟨i6, i3, i7, i5, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. moveEntry 0 7 5 : x aside
  have i0 : S₃ 0 = encodeNatΓ' x ++ .comma :: (encodeNatΓ' θ ++ .comma :: r0) := by
    rw [hF₃ 0 (by decide) (by decide) (by decide) (by decide), g0, h0]
  have hmv := moveEntry_correct (src := 0) (dst := 7) (s := 5) (by decide) (by decide) (by decide) x _ v₃ S₃ i0
  refine Frag.runs_mono (Frag.seq_runs (t₂ := U + U + U) hmv
    fun v₄ S₄ ⟨_, _, _, j0, j7, j5, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 4. dup 0 5 4 : θ
  have hdθ := dup_le_B (x := 0) (y := 5) (s := 4) (by decide) (by decide) (by decide) θ b hθ r0 v₄ S₄ j0
  refine Frag.runs_mono (Frag.seq_runs (t₂ := U + U) hdθ
    fun v₅ S₅ ⟨l0, l5, l4, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 5. moveEntry 7 0 5 : x back
  have l7 : S₅ 7 = encodeNatΓ' x ++ .comma :: S₃ 7 := by rw [hF₅ 7 (by decide) (by decide) (by decide), j7]
  have hmv2 := moveEntry_correct (src := 7) (dst := 0) (s := 5) (by decide) (by decide) (by decide) x _ v₅ S₅ l7
  refine Frag.runs_mono (Frag.seq_runs (t₂ := U) hmv2
    fun v₆ S₆ ⟨_, _, _, m7, m0, m5, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 6. cmpFrag 5 3
  have m5' : S₆ 5 = encodeNatΓ' θ ++ .comma :: S₄ 5 := by rw [m5, l5]
  have m3 : S₆ 3 = encodeNatΓ' e ++ .comma :: S₂ 3 := by
    rw [hF₆ 3 (by decide) (by decide) (by decide), hF₅ 3 (by decide) (by decide) (by decide),
      hF₄ 3 (by decide) (by decide) (by decide), i3]
  have hcm := cmp_correct (x := 5) (y := 3) (by decide) θ e _ _ v₆ S₆ m5' m3
  refine Frag.runs_mono hcm (fun v₇ S₇ ⟨hcmp₇, n5, n3, hF₇⟩ => ⟨hcmp₇, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    (by omega)
  · rw [hF₇ 0 (by decide) (by decide), m0, l0, j0, h0]
  · rw [hF₇ 1 (by decide) (by decide), hF₆ 1 (by decide) (by decide) (by decide),
      hF₅ 1 (by decide) (by decide) (by decide), hF₄ 1 (by decide) (by decide) (by decide),
      hF₃ 1 (by decide) (by decide) (by decide) (by decide), g1]
  · rw [hF₇ 2 (by decide) (by decide), hF₆ 2 (by decide) (by decide) (by decide),
      hF₅ 2 (by decide) (by decide) (by decide), hF₄ 2 (by decide) (by decide) (by decide),
      hF₃ 2 (by decide) (by decide) (by decide) (by decide), g2]
  · rw [n3, g3]
  · rw [hF₇ 4 (by decide) (by decide), hF₆ 4 (by decide) (by decide) (by decide), l4,
      hF₄ 4 (by decide) (by decide) (by decide), hF₃ 4 (by decide) (by decide) (by decide) (by decide), g4]
  · rw [n5, j5, i5, g5]
  · rw [hF₇ 6 (by decide) (by decide), hF₆ 6 (by decide) (by decide) (by decide),
      hF₅ 6 (by decide) (by decide) (by decide), hF₄ 6 (by decide) (by decide) (by decide), i6, g6]
  · rw [hF₇ 7 (by decide) (by decide), m7, i7, g7]

/-! The three per-iteration budget inequalities of the `scan` loop, over
bare naturals (`U` the unit `B MS`, `Bb = B b ≤ U`, `a` the `coprimeTo`
charge, `c` the `poolAlg` charge, `e = |P| ≤ c + 1`, `g` the remaining
charge). -/

theorem scan_budget_succ (a c e U : ℕ) (hU : 1 ≤ U) (he : e ≤ c + 1) :
    (a + 1) * U + ((c + 1) * (32 * U) + (e + 1) * U + 4 * U + (1 + 1) + 1) + 1 + 0 ≤
      (a + c + 1) * (64 * U) := by
  have := Nat.mul_le_mul_right U he
  nlinarith

theorem scan_budget_cont (a c e g U Bb : ℕ) (hU : 1 ≤ U) (hBb : Bb ≤ U) (he : e ≤ c + 1) :
    (a + 1) * U + ((c + 1) * (32 * U) + (e + 1) * U + 4 * U +
        ((e + 1) * Bb + (5 * Bb + 1) + 1) + 1) + 1 + g * (64 * U) ≤
      (g + a + c + 1) * (64 * U) := by
  have := Nat.mul_le_mul_right U he
  have := Nat.mul_le_mul_left (e + 1) hBb
  nlinarith

theorem scan_budget_skip (a g U Bb : ℕ) (hU : 1 ≤ U) (hBb : Bb ≤ U) :
    (a + 1) * U + (5 * Bb + 1 + 1) + 1 + g * (64 * U) ≤ (g + a + 1) * (64 * U) := by
  nlinarith

theorem scan_budget_total (n U Bb : ℕ) (hU : 1 ≤ U) (hBb : Bb ≤ U) :
    Bb + (Bb + Bb + 1 + (n * (64 * U) + 1) + (Bb + Bb + Bb)) ≤ (n + 1) * (64 * U) := by
  nlinarith

def scanBody : Frag :=
  (coprimeToF 4 2 3 5 6 7).seq
    (Frag.ite (fun v => v.flag)
      (scanTest.seq (Frag.ite (fun v => !decide (v.cmp = .gt))
        (Frag.load' (fun v => { v with carry := false, flag := true }))
        ((dropListQ 6).seq scanNext)))
      scanNext)

/-- `scan Q x z θ k fuel` on the machine (see the section header): the
leftover fuel is dropped at the end, so `1` is back to `z :: r1`. -/
def scanF : Frag :=
  (moveEntry 1 7 5).seq ((isZero 1 5).seq ((moveEntry 7 1 5).seq
    ((Frag.load' (fun v => { v with carry := !v.flag, flag := false })).seq
      ((Frag.loop (fun v => v.carry) scanBody).seq
        ((moveEntry 1 7 5).seq ((dropNum 1).seq (moveEntry 7 1 5)))))))

/-- Two-phase loop invariant of `scanF`: while running (`i < scanIters`)
`carry = true` and the stacks hold `k + i`, `fuel - i`, no pool; at the exit
(`i = scanIters`) `carry = false`, `flag` is the success bit, and the stacks
hold the result of `Alg.scan`. -/
def SCInv (Q : List ℕ) (x z θ k fuel : ℕ) (r0 r1 r2 r6 : List Γ') (S₀ : Stacks) (BS : ℕ)
    (i β : ℕ) (v : St) (S : Stacks) : Prop :=
  i ≤ scanIters Q x z θ k fuel ∧
  S 3 = S₀ 3 ∧ S 4 = S₀ 4 ∧ S 5 = S₀ 5 ∧ S 7 = S₀ 7 ∧
  S 0 = encodeNatΓ' x ++ .comma :: (encodeNatΓ' θ ++ .comma :: r0) ∧
  ((i < scanIters Q x z θ k fuel ∧ v.carry = true ∧
      S 1 = encodeNatΓ' z ++ .comma :: (encodeNatΓ' (fuel - i) ++ .comma :: r1) ∧
      S 2 = encodeNatΓ' (k + i) ++ .comma :: r2 ∧ S 6 = r6 ∧
      (∃ c', Alg.scan Q x z θ k fuel =
        ((Alg.scan Q x z θ (k + i) (fuel - i)).1, (Alg.scan Q x z θ (k + i) (fuel - i)).2 + c')) ∧
      scanIters Q x z θ k fuel = scanIters Q x z θ (k + i) (fuel - i) + i ∧
      β = (Alg.scan Q x z θ (k + i) (fuel - i)).2 * BS) ∨
   (i = scanIters Q x z θ k fuel ∧ v.carry = false ∧
      (∃ f', f' ≤ fuel ∧ S 1 = encodeNatΓ' z ++ .comma :: (encodeNatΓ' f' ++ .comma :: r1)) ∧
      ((∃ k' P, (Alg.scan Q x z θ k fuel).1 = some (k', P) ∧ v.flag = true ∧
          S 2 = encodeNatΓ' k' ++ .comma :: r2 ∧ S 6 = encList P ++ r6) ∨
       ((Alg.scan Q x z θ k fuel).1 = none ∧ v.flag = false ∧
          S 2 = encodeNatΓ' (k + fuel) ++ .comma :: r2 ∧ S 6 = r6))))

theorem scanBody_runs (Q : List ℕ) (x z θ k fuel bq b : ℕ) (hQ : ∀ q ∈ Q, q < 2 ^ bq)
    (hQ1 : ∀ q ∈ Q, 1 ≤ q) (hx : x < 2 ^ b) (hz : z < 2 ^ b) (hθ : θ < 2 ^ b) (hkf : k + fuel < 2 ^ b)
    (r0 r1 r2 r4 r6 : List Γ') (S₀ : Stacks) (h4Q : S₀ 4 = encList Q ++ r4)
    (i : ℕ) (hi : i < scanIters Q x z θ k fuel) (β : ℕ) (v : St) (S : Stacks)
    (hI : SCInv Q x z θ k fuel r0 r1 r2 r6 S₀
      (64 * B (12 * (Q.length + 1) * (bq + b) + Q.length + 24)) i β v S) :
    ∃ t β', t + 1 + β' ≤ β ∧
      scanBody.Runs v S (SCInv Q x z θ k fuel r0 r1 r2 r6 S₀
        (64 * B (12 * (Q.length + 1) * (bq + b) + Q.length + 24)) (i + 1) β') t := by
  obtain ⟨-, h3, h4, h5, h7, h0, hph⟩ := hI
  rcases hph with ⟨-, hcarry, h1, h2, h6, ⟨c', hrel⟩, hit, hβ⟩ | ⟨heq, -⟩
  swap
  · omega
  have hle := scanIters_le_fuel Q x z θ (k + i) (fuel - i)
  obtain ⟨f, hf⟩ : ∃ f, fuel - i = f + 1 := ⟨fuel - i - 1, by omega⟩
  rw [hf] at h1 hrel hit hβ
  have hfi : fuel - (i + 1) = f := by omega
  obtain ⟨k', hk'⟩ : ∃ k', k + i = k' := ⟨_, rfl⟩
  rw [hk'] at h2 hrel hit hβ
  have hk'b : k' < 2 ^ b := by omega
  have hk'1 : k' + 1 < 2 ^ b := by omega
  have hf1 : f + 1 < 2 ^ b := by omega
  obtain ⟨MS, hMS⟩ : ∃ MS, 12 * (Q.length + 1) * (bq + b) + Q.length + 24 = MS := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, B MS = U := ⟨_, rfl⟩
  rw [hMS, hU] at hβ ⊢
  have hU1 : 1 ≤ U := hU ▸ one_le_B _
  have hUb : B b ≤ U := hU ▸ B_mono (by rw [← hMS]; nlinarith)
  have hUcp : B (2 * (bq + b) + 2) ≤ U := hU ▸ B_mono (by rw [← hMS]; nlinarith)
  have hQb : ∀ q ∈ Q, q < 2 ^ (bq + b) := fun q hq =>
    lt_of_lt_of_le (hQ q hq) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hk'bb : k' < 2 ^ (bq + b) :=
    lt_of_lt_of_le hk'b (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h4' : S 4 = encList Q ++ r4 := by rw [h4, h4Q]
  -- the state after a continue step
  have hafter : ∀ (c'' : ℕ),
      Alg.scan Q x z θ k fuel =
        ((Alg.scan Q x z θ (k' + 1) f).1, (Alg.scan Q x z θ (k' + 1) f).2 + c'') →
      scanIters Q x z θ k fuel = scanIters Q x z θ (k' + 1) f + (i + 1) →
      ∀ (v' : St) (S' : Stacks), v'.carry = !decide (f = 0) → v'.flag = false →
        S' 0 = S 0 → S' 1 = encodeNatΓ' z ++ .comma :: (encodeNatΓ' f ++ .comma :: r1) →
        S' 2 = encodeNatΓ' (k' + 1) ++ .comma :: r2 → S' 3 = S 3 → S' 4 = S 4 → S' 5 = S 5 →
        S' 6 = r6 → S' 7 = S 7 →
        SCInv Q x z θ k fuel r0 r1 r2 r6 S₀ (64 * U) (i + 1)
          ((Alg.scan Q x z θ (k' + 1) f).2 * (64 * U)) v' S' := by
    intro c'' hrel' hit' v' S' hc hfl e0 e1 e2 e3 e4 e5 e6 e7
    refine ⟨by omega, e3.trans h3, e4.trans h4, e5.trans h5, e7.trans h7, e0.trans h0, ?_⟩
    by_cases hf0 : f = 0
    · subst hf0
      rw [scanIters_zero] at hit'
      refine Or.inr ⟨by omega, by simp [hc], ⟨0, Nat.zero_le _, e1⟩, Or.inr ⟨?_, hfl, ?_, e6⟩⟩
      · rw [congrArg Prod.fst hrel', scan_zero]
      · rw [e2, show k' + 1 = k + fuel by omega]
    · have hpos := scanIters_pos Q x z θ (k' + 1) (Nat.pos_of_ne_zero hf0)
      refine Or.inl ⟨by omega, by simp [hc, hf0], ?_, ?_, e6, ⟨c'', ?_⟩, ?_, ?_⟩
      · rw [e1, hfi]
      · rw [e2, ← hk', Nat.add_assoc]
      · rw [hrel', ← hk', hfi, Nat.add_assoc]
      · rw [hit', ← hk', hfi, Nat.add_assoc]
      · rw [← hk', hfi, Nat.add_assoc]
  -- 1. coprimeToF 4 2 3 5 6 7
  have hcpr := coprimeToF_le_B (x := 4) (y := 2) (z := 3) (s := 5) (t := 6) (u := 7) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) Q k' (bq + b) hQb hQ1 hk'bb r4 r2 v S h4' h2
  have hcp' := Frag.runs_mono hcpr (fun _ _ h => h) (Nat.mul_le_mul_left _ hUcp)
  obtain ⟨a, ha⟩ : ∃ a, (Alg.coprimeTo Q k').2 = a := ⟨_, rfl⟩
  rw [ha] at hcp'
  have hsc := scan_succ_raw Q x z θ k' f
  have hsi := scanIters_succ Q x z θ k' f
  rw [ha] at hsc
  by_cases hcp : (Alg.coprimeTo Q k').1 = true
  · rw [if_pos hcp] at hsc hsi
    have hPmem : ∀ p ∈ (Alg.poolAlg Q x z k').1, p < 2 ^ b := fun p hp =>
      lt_of_le_of_lt (poolAlg_mem hp).1 hx
    have hPlen := poolAlg_length_le Q x z k'
    obtain ⟨c, hc⟩ : ∃ c, (Alg.poolAlg Q x z k').2 = c := ⟨_, rfl⟩
    obtain ⟨e, he⟩ : ∃ e, (Alg.poolAlg Q x z k').1.length = e := ⟨_, rfl⟩
    rw [hc, he] at hsc hPlen
    rw [he] at hsi
    by_cases hθl : θ ≤ e
    · -- success
      rw [if_pos hθl] at hsc hsi
      refine ⟨(a + 1) * U + ((c + 1) * (32 * U) + (e + 1) * U + 4 * U + (1 + 1) + 1), 0, ?_, ?_⟩
      · rw [hβ, hsc]; exact scan_budget_succ a c e U hU1 hPlen
      refine Frag.runs_mono (Frag.seq_runs (t₂ := (c + 1) * (32 * U) + (e + 1) * U + 4 * U + (1 + 1) + 1)
        hcp' fun v₁ S₁ ⟨hfl₁, f4, f2, f3, f5, f6, f7, hF₁⟩ => ?_) (fun _ _ h => h) le_rfl
      have hS₁ : S₁ = S := stacks_ext (hF₁ 0 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)) (hF₁ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        f2 f3 f4 f5 f6 f7
      rw [hS₁]
      refine Frag.ite_runs_true (by rw [hfl₁, hcp]) ?_
      have htest := scanTest_runs Q x z θ k' bq b hQ hx hz hθ hk'b r0 _ r2 r4 v₁ S h0 h1 h2 h4'
      rw [hc, he, hMS, hU] at htest
      refine Frag.seq_runs (t₂ := 1 + 1) htest fun v₂ S₂ ⟨hcmp₂, g0, g1, g2, g3, g4, g5, g6, g7⟩ => ?_
      have hcnd : (!decide (v₂.cmp = Ordering.gt)) = true := by
        simp [hcmp₂, compare_gt_iff_gt, not_lt.mpr hθl]
      refine Frag.ite_runs_true hcnd ?_
      refine Frag.runs_mono (Frag.load'_runs _ v₂ S₂) (fun v' S' ⟨hv', hS'⟩ => ?_) le_rfl
      rw [hv', hS']
      refine ⟨by omega, g3.trans h3, g4.trans h4, g5.trans h5, g7.trans h7, g0.trans h0,
        Or.inr ⟨by omega, rfl, ⟨f + 1, by omega, g1.trans h1⟩,
          Or.inl ⟨k', (Alg.poolAlg Q x z k').1, ?_, rfl, g2.trans h2, by rw [g6, h6]⟩⟩⟩
      rw [congrArg Prod.fst hrel, hsc]
    · -- coprime, pool too small: drop the pool and continue
      rw [if_neg hθl] at hsc hsi
      refine ⟨(a + 1) * U + ((c + 1) * (32 * U) + (e + 1) * U + 4 * U +
        ((e + 1) * B b + (5 * B b + 1) + 1) + 1), (Alg.scan Q x z θ (k' + 1) f).2 * (64 * U), ?_, ?_⟩
      · rw [hβ, hsc]; exact scan_budget_cont a c e _ U (B b) hU1 hUb hPlen
      refine Frag.runs_mono (Frag.seq_runs (t₂ := (c + 1) * (32 * U) + (e + 1) * U + 4 * U +
        ((e + 1) * B b + (5 * B b + 1) + 1) + 1) hcp'
        fun v₁ S₁ ⟨hfl₁, f4, f2, f3, f5, f6, f7, hF₁⟩ => ?_) (fun _ _ h => h) le_rfl
      have hS₁ : S₁ = S := stacks_ext (hF₁ 0 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide)) (hF₁ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        f2 f3 f4 f5 f6 f7
      rw [hS₁]
      refine Frag.ite_runs_true (by rw [hfl₁, hcp]) ?_
      have htest := scanTest_runs Q x z θ k' bq b hQ hx hz hθ hk'b r0 _ r2 r4 v₁ S h0 h1 h2 h4'
      rw [hc, he, hMS, hU] at htest
      refine Frag.seq_runs (t₂ := (e + 1) * B b + (5 * B b + 1) + 1) htest
        fun v₂ S₂ ⟨hcmp₂, g0, g1, g2, g3, g4, g5, g6, g7⟩ => ?_
      have hcnd : (!decide (v₂.cmp = Ordering.gt)) = false := by
        simp [hcmp₂, compare_gt_iff_gt, not_le.mp hθl]
      refine Frag.ite_runs_false hcnd ?_
      -- dropListQ 6
      have o6 : S₂ 6 = encList (Alg.poolAlg Q x z k').1 ++ r6 := by rw [g6, h6]
      have hdl := dropList_le_B (x := 6) (Alg.poolAlg Q x z k').1 b hPmem r6 v₂ S₂ o6
      rw [he] at hdl
      refine Frag.seq_runs (t₂ := 5 * B b + 1) hdl fun v₃ S₃ ⟨p6, hF₃⟩ => ?_
      -- scanNext
      have p1 : S₃ 1 = encodeNatΓ' z ++ .comma :: (encodeNatΓ' (f + 1) ++ .comma :: r1) := by
        rw [hF₃ 1 (by decide), g1, h1]
      have p2 : S₃ 2 = encodeNatΓ' k' ++ .comma :: r2 := by rw [hF₃ 2 (by decide), g2, h2]
      have hsn := scanNext_runs z k' f b hz hk'1 hf1 r1 r2 v₃ S₃ p1 p2
      refine Frag.runs_mono hsn (fun v' S' ⟨q1, q2, q0, q1', q2', q3, q4, q5, q6, q7⟩ =>
        hafter (c' + a + c + 1) ?_ ?_ v' S' q1 q2 ?_ q1' q2' ?_ ?_ ?_ ?_ ?_) le_rfl
      · rw [hrel, hsc]; simp only [Prod.mk.injEq, true_and]; omega
      · rw [hit, hsi]; omega
      · rw [q0, hF₃ 0 (by decide), g0]
      · rw [q3, hF₃ 3 (by decide), g3]
      · rw [q4, hF₃ 4 (by decide), g4]
      · rw [q5, hF₃ 5 (by decide), g5]
      · rw [q6, p6]
      · rw [q7, hF₃ 7 (by decide), g7]
  · -- not coprime: continue
    rw [if_neg hcp] at hsc hsi
    refine ⟨(a + 1) * U + (5 * B b + 1 + 1), (Alg.scan Q x z θ (k' + 1) f).2 * (64 * U), ?_, ?_⟩
    · rw [hβ, hsc]; exact scan_budget_skip a _ U (B b) hU1 hUb
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * B b + 1 + 1) hcp'
      fun v₁ S₁ ⟨hfl₁, f4, f2, f3, f5, f6, f7, hF₁⟩ => ?_) (fun _ _ h => h) le_rfl
    have hS₁ : S₁ = S := stacks_ext (hF₁ 0 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)) (hF₁ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      f2 f3 f4 f5 f6 f7
    rw [hS₁]
    refine Frag.ite_runs_false (by rw [hfl₁]; simpa using hcp) ?_
    have hsn := scanNext_runs z k' f b hz hk'1 hf1 r1 r2 v₁ S h1 h2
    refine Frag.runs_mono hsn (fun v' S' ⟨q1, q2, q0, q1', q2', q3, q4, q5, q6, q7⟩ =>
      hafter (c' + a + 1) ?_ ?_ v' S' q1 q2 q0 q1' q2' q3 q4 q5 (q6.trans h6) q7) le_rfl
    · rw [hrel, hsc]; simp only [Prod.mk.injEq, true_and]; omega
    · rw [hit, hsi]; omega

theorem scanF_le_B (Q : List ℕ) (x z θ k fuel bq b : ℕ) (hQ : ∀ q ∈ Q, q < 2 ^ bq)
    (hQ1 : ∀ q ∈ Q, 1 ≤ q) (hx : x < 2 ^ b) (hz : z < 2 ^ b) (hθ : θ < 2 ^ b) (hkf : k + fuel < 2 ^ b)
    (r0 r1 r2 r4 : List Γ') (v : St) (S : Stacks)
    (h0 : S 0 = encodeNatΓ' x ++ .comma :: (encodeNatΓ' θ ++ .comma :: r0))
    (h1 : S 1 = encodeNatΓ' z ++ .comma :: (encodeNatΓ' fuel ++ .comma :: r1))
    (h2 : S 2 = encodeNatΓ' k ++ .comma :: r2) (h4 : S 4 = encList Q ++ r4) :
    scanF.Runs v S (fun v' S' =>
        S' 0 = S 0 ∧ S' 1 = encodeNatΓ' z ++ .comma :: r1 ∧ S' 3 = S 3 ∧ S' 4 = S 4 ∧
        S' 5 = S 5 ∧ S' 7 = S 7 ∧
        ((∃ k' P, (Alg.scan Q x z θ k fuel).1 = some (k', P) ∧ v'.flag = true ∧
            S' 2 = encodeNatΓ' k' ++ .comma :: r2 ∧ S' 6 = encList P ++ S 6) ∨
         ((Alg.scan Q x z θ k fuel).1 = none ∧ v'.flag = false ∧
            S' 2 = encodeNatΓ' (k + fuel) ++ .comma :: r2 ∧ S' 6 = S 6)))
      (((Alg.scan Q x z θ k fuel).2 + 1) * B (48 * (Q.length + 1) * (bq + b) + 4 * Q.length + 102)) := by
  obtain ⟨MS, hMS⟩ : ∃ MS, 12 * (Q.length + 1) * (bq + b) + Q.length + 24 = MS := ⟨_, rfl⟩
  have h64 : B (48 * (Q.length + 1) * (bq + b) + 4 * Q.length + 102) = 64 * B MS := by
    rw [show 64 = (3 + 1) ^ 3 by norm_num, B_scale, ← hMS]; congr 1; ring
  rw [h64]
  obtain ⟨U, hU⟩ : ∃ U, B MS = U := ⟨_, rfl⟩
  rw [hU]
  have hU1 : 1 ≤ U := hU ▸ one_le_B _
  have hUb : B b ≤ U := hU ▸ B_mono (by rw [← hMS]; nlinarith)
  have hlz := log_le_of_lt_pow hz
  have hmv : 2 * Nat.log 2 z + 6 ≤ B b := le_B_of_le_linear (by omega)
  have hfb : fuel < 2 ^ b := by omega
  obtain ⟨n, hn⟩ : ∃ n, (Alg.scan Q x z θ k fuel).2 = n := ⟨_, rfl⟩
  rw [hn]
  -- 1. moveEntry 1 7 5 : z aside
  have ha := moveEntry_correct (src := 1) (dst := 7) (s := 5) (by decide) (by decide) (by decide) z _ v S h1
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + B b + 1 + (n * (64 * U) + 1) + (B b + B b + B b)) ha
    fun v₁ S₁ ⟨_, _, _, h1₁, h7₁, h5₁, hF₁⟩ => ?_) (fun _ _ h => h)
    (le_trans (by omega) (scan_budget_total n U (B b) hU1 hUb))
  -- 2. isZero 1 5
  have hb := isZero_le_B (x := 1) (s := 5) (by decide) fuel b hfb r1 v₁ S₁ h1₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + 1 + (n * (64 * U) + 1) + (B b + B b + B b)) hb
    fun v₂ S₂ ⟨hfl₂, _, h1₂, h5₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. moveEntry 7 1 5 : z back
  have h7₂ : S₂ 7 = encodeNatΓ' z ++ .comma :: S 7 := by rw [hF₂ 7 (by decide) (by decide), h7₁]
  have hc := moveEntry_correct (src := 7) (dst := 1) (s := 5) (by decide) (by decide) (by decide) z _ v₂ S₂ h7₂
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1 + (n * (64 * U) + 1) + (B b + B b + B b)) hc
    fun v₃ S₃ ⟨hfl₃, _, _, h7₃, h1₃, h5₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 4. load'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (n * (64 * U) + 1) + (B b + B b + B b))
    (Frag.load'_runs _ v₃ S₃) fun v₄ S₄ ⟨hv₄, hS₄⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₄, hS₄]
  -- the state before the loop
  have e0 : S₃ 0 = encodeNatΓ' x ++ .comma :: (encodeNatΓ' θ ++ .comma :: r0) := by
    rw [hF₃ 0 (by decide) (by decide) (by decide), hF₂ 0 (by decide) (by decide),
      hF₁ 0 (by decide) (by decide) (by decide), h0]
  have e1 : S₃ 1 = encodeNatΓ' z ++ .comma :: (encodeNatΓ' fuel ++ .comma :: r1) := by
    rw [h1₃, h1₂, h1₁]
  have e2 : S₃ 2 = encodeNatΓ' k ++ .comma :: r2 := by
    rw [hF₃ 2 (by decide) (by decide) (by decide), hF₂ 2 (by decide) (by decide),
      hF₁ 2 (by decide) (by decide) (by decide), h2]
  have e3 : S₃ 3 = S 3 := by
    rw [hF₃ 3 (by decide) (by decide) (by decide), hF₂ 3 (by decide) (by decide),
      hF₁ 3 (by decide) (by decide) (by decide)]
  have e4 : S₃ 4 = S 4 := by
    rw [hF₃ 4 (by decide) (by decide) (by decide), hF₂ 4 (by decide) (by decide),
      hF₁ 4 (by decide) (by decide) (by decide)]
  have e5 : S₃ 5 = S 5 := by rw [h5₃, h5₂, h5₁]
  have e6 : S₃ 6 = S 6 := by
    rw [hF₃ 6 (by decide) (by decide) (by decide), hF₂ 6 (by decide) (by decide),
      hF₁ 6 (by decide) (by decide) (by decide)]
  have e7 : S₃ 7 = S 7 := h7₃
  have hflag : v₃.flag = decide (fuel = 0) := by rw [hfl₃, hfl₂]
  -- 5. the loop
  have hI0 : SCInv Q x z θ k fuel r0 r1 r2 (S 6) S (64 * U) 0 (n * (64 * U))
      { v₃ with carry := !v₃.flag, flag := false } S₃ := by
    refine ⟨Nat.zero_le _, e3, e4, e5, e7, e0, ?_⟩
    by_cases hf0 : fuel = 0
    · subst hf0
      refine Or.inr ⟨by rw [scanIters_zero], by simp [hflag], ⟨0, le_rfl, e1⟩,
        Or.inr ⟨by rw [scan_zero], rfl, by simp [e2], e6⟩⟩
    · have hpos := scanIters_pos Q x z θ k (Nat.pos_of_ne_zero hf0)
      refine Or.inl ⟨hpos, by simp [hflag, hf0], by simp [e1], by simp [e2], e6,
        ⟨0, by simp⟩, by simp, by simp [hn]⟩
  have hloop := Frag.loop_runs_budget (c := fun v => v.carry) (B := scanBody)
    (SCInv Q x z θ k fuel r0 r1 r2 (S 6) S (64 * U)) (scanIters Q x z θ k fuel) (n * (64 * U))
    (v := { v₃ with carry := !v₃.flag, flag := false }) (S := S₃) hI0
    (fun i hi β w T ⟨_, _, _, _, _, _, hph⟩ => by
      rcases hph with ⟨_, hc, _⟩ | ⟨heq, _⟩
      · exact hc
      · omega)
    (fun β w T ⟨_, _, _, _, _, _, hph⟩ => by
      rcases hph with ⟨hlt, _⟩ | ⟨_, hc, _⟩
      · omega
      · exact hc)
    (fun i hi β w T hI => by
      have := scanBody_runs Q x z θ k fuel bq b hQ hQ1 hx hz hθ hkf r0 r1 r2 r4 (S 6) S h4 i hi β w T
        (by rwa [hMS, hU])
      rwa [hMS, hU] at this)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + B b + B b) hloop
    fun v₅ S₅ ⟨⟨β, _, f3, f4, f5, f7, f0, hph⟩, hc₅⟩ => ?_) (fun _ _ h => h) (by omega)
  rcases hph with ⟨_, hcarry, _⟩ | ⟨_, _, ⟨f', hf', f1⟩, hres⟩
  · simp [hcarry] at hc₅
  -- 6. moveEntry 1 7 5
  have hd := moveEntry_correct (src := 1) (dst := 7) (s := 5) (by decide) (by decide) (by decide) z _ v₅ S₅ f1
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + B b) hd
    fun v₆ S₆ ⟨hfl₆, _, _, g1, g7, g5, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 7. dropNum 1
  have he := dropNum_le_B (x := 1) f' b (by omega) r1 v₆ S₆ g1
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b) he
    fun v₇ S₇ ⟨hfl₇, _, _, i1, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 8. moveEntry 7 1 5
  have i7 : S₇ 7 = encodeNatΓ' z ++ .comma :: S₅ 7 := by rw [hF₇ 7 (by decide), g7]
  have hf8 := moveEntry_correct (src := 7) (dst := 1) (s := 5) (by decide) (by decide) (by decide) z _ v₇ S₇ i7
  refine Frag.runs_mono hf8 (fun v' S' ⟨hfl', _, _, j7, j1, j5, hF'⟩ => ?_) (by omega)
  refine ⟨?_, by rw [j1, i1], ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF' 0 (by decide) (by decide) (by decide), hF₇ 0 (by decide), hF₆ 0 (by decide) (by decide) (by decide),
      f0, h0]
  · rw [hF' 3 (by decide) (by decide) (by decide), hF₇ 3 (by decide), hF₆ 3 (by decide) (by decide) (by decide),
      f3]
  · rw [hF' 4 (by decide) (by decide) (by decide), hF₇ 4 (by decide), hF₆ 4 (by decide) (by decide) (by decide),
      f4]
  · rw [j5, hF₇ 5 (by decide), g5, f5]
  · rw [j7, f7]
  · have hfl : v'.flag = v₅.flag := by rw [hfl', hfl₇, hfl₆]
    have i2 : S' 2 = S₅ 2 := by
      rw [hF' 2 (by decide) (by decide) (by decide), hF₇ 2 (by decide),
        hF₆ 2 (by decide) (by decide) (by decide)]
    have i6 : S' 6 = S₅ 6 := by
      rw [hF' 6 (by decide) (by decide) (by decide), hF₇ 6 (by decide),
        hF₆ 6 (by decide) (by decide) (by decide)]
    rcases hres with ⟨k', P, hsome, hfl₅, s2, s6⟩ | ⟨hnone, hfl₅, s2, s6⟩
    · exact Or.inl ⟨k', P, hsome, by rw [hfl, hfl₅], by rw [i2, s2], by rw [i6, s6]⟩
    · exact Or.inr ⟨hnone, by rw [hfl, hfl₅], by rw [i2, s2], by rw [i6, s6]⟩

end Carmichael.TM
