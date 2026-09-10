import Carmichael.TM.Steps23
import Carmichael.TM.Step4
import Carmichael.ScalesTM

/-!
# Route T: step 5 and the search assembly (sortie T6)

Machine fragments refining `Alg.notMemTD`, `Alg.nodupTD`, `Alg.allPrimeTD`,
`Alg.korseltTD`, `Alg.verify` (Algorithm.lean) and `scalesTM` (ScalesTM.lean)
EXACTLY, and the whole machine body `searchF C₁ K` refining `Alg.search`:
from the raw input `encodeNatΓ' n` on stack 0 it leaves EXACTLY
`encodeOutput ((Alg.search (scalesTM C₁ K n) n).1.getD (0, []))` on stack 1
with every other stack empty.

## Stack allocation (`K = Fin 8`, concrete stacks throughout, as in T4)

The step-5 fragments take `S` (the factor list) on stack 4 and `m` on stack 7
(both restored) and use the six other stacks as restored scratch (whatever
they hold beneath is preserved: every stack fact is `S' k = S k` or
`S' k = … ++ S k`):

| fragment | operands | result | scratch (restored) | registers |
|---|---|---|---|---|
| `nodupTDF` | list `S` on 4 | `flag := (Alg.nodupTD S).1` | 0, 1 (accumulator), 2, 3, 5 (copy), 6, 7 | `flag`, `cmp` |
| `allPrimeTDF` | list `S` on 4 | `flag := (Alg.allPrimeTD S).1` | 0, 1 (accumulator), 2, 3, 5 (copy), 6, 7 | `flag`, `cmp` |
| `korseltTDF` | list `S` on 4, `m` on 7 | `flag := (Alg.korseltTD m S).1` | 0, 1 (accumulator), 2, 3, 5 (copy), 6 | `flag`, `cmp` |
| `verifyF` | list `S` on 4, `m` on 7 | `flag := (Alg.verify m S).1` | 0 (accumulator), 1, 2, 3, 5, 6 | `flag`, `cmp` |

Inside the three list loops the current copy of `S` is walked on stack 5
(`forEntries`), the Boolean accumulator is the number `0`/`1` on stack 1
(registers do not survive the sub-fragments), and the invariant is
`acc && (f (S.drop i)).1 = (f S).1` with budget `(f (S.drop i)).2 * C`
(`forEntriesN_runs_budget`).

`scalesF C₁ K` takes `n` on stack 7 (restored) and leaves the five scales
packed on stack 0, top first: `z :: z99 :: y :: T :: θ` (the entry layout
of T4's `step2F`), stacks 1–6 restored.

`searchF C₁ K` (the machine body): input adapter (stack 0 = raw `encodeNatΓ' n`
without terminator → terminated `n` on stack 7), `scalesF`, `step2F` (T4),
`scanF` (T4), `extractF 6 3 0 5 1 2 7 4` (T5b: pool on 6, `L` on 3, table on 5,
`m` above `n` on 7, witnesses on 4 above `Q`), `verifyF`, then either the
output fragment (`encodeOutput (m, S)` on stack 1, everything else cleared)
or `failAll` (clear everything, `[comma] = encodeOutput (0, [])` on stack 1).

## Step bounds

`nodupTDF`, `allPrimeTDF`, `korseltTDF`, `verifyF`: `((Alg.f args).2 + 1) * B (…)`.
`scalesF`: `50 * B (3 b + 8)` for `n, C₁, K < 2 ^ b`.  `searchF`:
`((Alg.search sc n).2 + 1) * searchPoly sc bs bn` for scale-sized numbers
`< 2 ^ bs` and `n, θ < 2 ^ bn`, and the unconditional `searchBound C₁ K n`.
-/

namespace Carmichael.TM

open Turing Turing.TM2 Turing.TM2.Stmt Computability

set_option linter.unusedVariables false

/-- Close a stack-frame goal `S_j k = …` from the stage facts in context: every
`S_j k = S_{j-1} k`-style fact (conditional on stack distinctness, discharged on
`Fin 8` literals) is a rewrite rule, and both sides normalise to the original stacks. -/
macro "tm_fr" : tactic => `(tactic| simp only [*, ne_eq, Fin.reduceEq, not_false_eq_true])

/-! ### Lean side: the step-5 functions -/

theorem notMemTD_fst (p : ℕ) (S : List ℕ) : (Alg.notMemTD p S).1 = !decide (p ∈ S) := by
  induction S with
  | nil => simp [Alg.notMemTD]
  | cons q S ih =>
    simp only [Alg.notMemTD, ih, List.mem_cons]
    by_cases h : p = q <;> simp [h]

theorem notMemTD_snd (p : ℕ) (S : List ℕ) : (Alg.notMemTD p S).2 = S.length := by
  induction S with
  | nil => rfl
  | cons q S ih => simp [Alg.notMemTD, ih]

theorem nodupTD_nil : Alg.nodupTD [] = (true, 0) := rfl

theorem nodupTD_cons (p : ℕ) (S : List ℕ) :
    Alg.nodupTD (p :: S) =
      ((Alg.notMemTD p S).1 && (Alg.nodupTD S).1, (Alg.notMemTD p S).2 + (Alg.nodupTD S).2 + 1) := rfl

theorem length_le_nodupTD_cost (S : List ℕ) : S.length ≤ (Alg.nodupTD S).2 := by
  induction S with
  | nil => simp [nodupTD_nil]
  | cons p S ih => rw [nodupTD_cons]; simp only [List.length_cons]; omega

theorem allPrimeTD_nil : Alg.allPrimeTD [] = (true, 0) := rfl

theorem allPrimeTD_cons (p : ℕ) (S : List ℕ) :
    Alg.allPrimeTD (p :: S) =
      ((Alg.isPrimeTD p).1 && (Alg.allPrimeTD S).1, (Alg.isPrimeTD p).2 + (Alg.allPrimeTD S).2 + 1) := rfl

theorem length_le_allPrimeTD_cost (S : List ℕ) : S.length ≤ (Alg.allPrimeTD S).2 := by
  induction S with
  | nil => simp [allPrimeTD_nil]
  | cons p S ih => rw [allPrimeTD_cons]; simp only [List.length_cons]; omega

theorem korseltTD_nil (m : ℕ) : Alg.korseltTD m [] = (true, 0) := rfl

theorem korseltTD_cons (m p : ℕ) (S : List ℕ) :
    Alg.korseltTD m (p :: S) =
      ((if (m - 1) % (p - 1) = 0 then (Alg.korseltTD m S).1 else false), (Alg.korseltTD m S).2 + 1) := rfl

theorem korseltTD_cons' (m p : ℕ) (S : List ℕ) :
    (Alg.korseltTD m (p :: S)).1 = (decide ((m - 1) % (p - 1) = 0) && (Alg.korseltTD m S).1) := by
  rw [korseltTD_cons]; by_cases h : (m - 1) % (p - 1) = 0 <;> simp [h]

theorem korseltTD_snd (m : ℕ) (S : List ℕ) : (Alg.korseltTD m S).2 = S.length := by
  induction S with
  | nil => rfl
  | cons p S ih => rw [korseltTD_cons]; simp [ih]

theorem verify_eq (m : ℕ) (S : List ℕ) :
    Alg.verify m S =
      ((Alg.nodupTD S).1 && (Alg.allPrimeTD S).1 && ((Alg.prodL S).1 == m) && (Alg.korseltTD m S).1 &&
          decide (3 ≤ S.length),
        (Alg.nodupTD S).2 + (Alg.allPrimeTD S).2 + (Alg.prodL S).2 + (Alg.korseltTD m S).2 + 2) := by
  unfold Alg.verify
  by_cases h : 3 ≤ S.length <;> simp [h]

theorem beq_eq_decide_eq (a b : ℕ) : (a == b) = decide (a = b) := by
  by_cases h : a = b <;> simp [h]

/-! ### The output encoding (verbatim from `routet/MainTM-frozen.lean`) -/

/-- Output encoding over Mathlib's alphabet `Γ'`: `m`, then its prime factors,
each number in binary least-significant bit first (Mathlib's `encodeNat`),
each followed by a comma. -/
def encodeOutput : ℕ × List ℕ → List Γ'
  | (m, S) => (encodeNat m).map inclusionBoolΓ' ++ Γ'.comma ::
      S.flatMap (fun p => (encodeNat p).map inclusionBoolΓ' ++ [Γ'.comma])

theorem encodeOutput_eq (m : ℕ) (S : List ℕ) :
    encodeOutput (m, S) = encodeNatΓ' m ++ .comma :: entries (S.map Computability.encodeNat) := by
  simp only [encodeOutput, entries, List.flatMap_map]
  rfl

theorem encodeOutput_default : encodeOutput (0, []) = [.comma] := rfl

/-! ### `Alg.nodupTD` -/

/-- A `B`-form of `moveEntry_correct`. -/
theorem moveEntry_le_B {src dst s : K} (hsd : src ≠ dst) (hss : src ≠ s) (hds : dst ≠ s)
    (a b : ℕ) (ha : a < 2 ^ b) (sr : List Γ') (v : St) (S : Stacks)
    (hS : S src = encodeNatΓ' a ++ .comma :: sr) :
    (moveEntry src dst s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' src = sr ∧ S' dst = encodeNatΓ' a ++ .comma :: S dst ∧ S' s = S s ∧
        ∀ k, k ≠ src → k ≠ dst → k ≠ s → S' k = S k)
      (B b) := by
  refine Frag.runs_mono (moveEntry_correct hsd hss hds a sr v S hS) (fun _ _ h => h) ?_
  have := log_le_of_lt_pow ha
  exact le_B_of_le_linear (by omega)

/-! ### The accumulator loop shared by the three step-5 list checks -/

/-- Invariant of an AND-accumulating walk over the copy of `l` on stack 5:
the accumulator `acc` (a `0`/`1` number on stack 1, above the original stack 1)
satisfies `acc && (f (l.drop i)).1 = (f l).1`; the budget is `(f (l.drop i)).2 * C`. -/
def AccInv (f : List ℕ → Bool × ℕ) (l : List ℕ) (S₀ : Stacks) (C : ℕ) (i β : ℕ) (T : Stacks) :
    Prop :=
  (∃ acc : Bool, T 1 = encodeNatΓ' acc.toNat ++ .comma :: S₀ 1 ∧
    (acc && (f (l.drop i)).1) = (f l).1) ∧
  T 0 = S₀ 0 ∧ T 2 = S₀ 2 ∧ T 3 = S₀ 3 ∧ T 4 = S₀ 4 ∧ T 6 = S₀ 6 ∧ T 7 = S₀ 7 ∧
  β = (f (l.drop i)).2 * C

theorem log_toNat_bool (acc : Bool) : Nat.log 2 acc.toNat = 0 := by cases acc <;> simp

/-- Dropping a `0`/`1` accumulator. -/
theorem dropNum_acc (x : K) (acc : Bool) (b : ℕ) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encodeNatΓ' acc.toNat ++ .comma :: xr) :
    (dropNum x).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' x = xr ∧ ∀ k, k ≠ x → S' k = S k)
      (B b) :=
  Frag.runs_mono (dropNum_correct acc.toNat xr v S hS) (fun _ _ h => h)
    (by rw [log_toNat_bool]; exact le_B_of_le_linear (by omega))

/-- Testing a `0`/`1` accumulator. -/
theorem isZero_acc {x s : K} (hxs : x ≠ s) (acc : Bool) (b : ℕ) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encodeNatΓ' acc.toNat ++ .comma :: xr) :
    (isZero x s).Runs v S (fun v' S' =>
        v'.flag = decide (acc.toNat = 0) ∧ v'.cmp = v.cmp ∧
        S' x = S x ∧ S' s = S s ∧ ∀ k, k ≠ x → k ≠ s → S' k = S k)
      (B b) :=
  Frag.runs_mono (isZero_correct hxs acc.toNat xr v S hS) (fun _ _ h => h)
    (by rw [log_toNat_bool]; exact le_B_of_le_linear (by omega))

/-- `acc := acc && flag`: reset the accumulator on stack 1 to `0` unless `flag`. -/
def accAnd : Frag := Frag.ite (fun v => v.flag) Frag.skip ((dropNum 1).seq (pushNum 1 0))

theorem accAnd_runs (acc : Bool) (b : ℕ) (r1 : List Γ') (v : St) (S : Stacks)
    (h1 : S 1 = encodeNatΓ' acc.toNat ++ .comma :: r1) :
    accAnd.Runs v S (fun _ S' =>
        S' 1 = encodeNatΓ' (acc && v.flag).toNat ++ .comma :: r1 ∧ ∀ k, k ≠ 1 → S' k = S k)
      (B b + B b + 1) := by
  refine Frag.ite_runs (t := B b + B b) (fun hc => ?_) (fun hc => ?_)
  · have hc' : v.flag = true := hc
    refine Frag.runs_mono (Frag.skip_runs v S) (fun _ S' ⟨_, hS'⟩ => ⟨?_, ?_⟩) (by have := one_le_B b; omega)
    · rw [hS', h1, hc', Bool.and_true]
    · intro k _; rw [hS']
  · have hc' : v.flag = false := hc
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B b) (dropNum_acc 1 acc b _ v S h1)
      fun v₁ S₁ ⟨_, _, _, h1₁, hF₁⟩ => ?_) (fun _ _ h => h) le_rfl
    refine Frag.runs_mono (pushNum_le_B 1 0 b Nat.one_le_two_pow v₁ S₁)
      (fun _ S₂ ⟨_, h1₂, hF₂⟩ => ⟨?_, ?_⟩) le_rfl
    · rw [h1₂, h1₁, hc', Bool.and_false]; rfl
    · intro k hk; rw [hF₂ k hk, hF₁ k hk]

/-- Push the accumulator `1` on stack 1, walk the list on stack 5 with `body`
(which must maintain `AccInv f`), pop the list's `bra`, and read the
accumulator into `flag`. -/
def accLoopF (body : Frag) : Frag :=
  (pushNum 1 1).seq ((forEntries 5 body).seq ((popTop 5).seq
    ((isZero 1 2).seq ((Frag.load' (fun v => { v with flag := !v.flag })).seq (dropNum 1)))))

theorem accLoopF_runs (f : List ℕ → Bool × ℕ) (hf : f [] = (true, 0)) (body : Frag) (l : List ℕ)
    (C b : ℕ) (xr : List Γ') (v : St) (S₀ : Stacks) (h5 : S₀ 5 = encList l ++ xr)
    (hbody : ∀ (i a : ℕ) (l' : List ℕ), l.drop i = a :: l' →
      ∀ (β : ℕ) (w : St) (T : Stacks), AccInv f l S₀ C i β T →
        T 5 = encodeNatΓ' a ++ .comma :: (encList l' ++ xr) →
        ∃ t β', t + 2 + β' ≤ β ∧
          body.Runs w T (fun _ T' => AccInv f l S₀ C (i + 1) β' T' ∧ T' 5 = encList l' ++ xr) t) :
    (accLoopF body).Runs v S₀ (fun v' S' =>
        v'.flag = (f l).1 ∧ S' 5 = xr ∧ ∀ k, k ≠ 5 → S' k = S₀ k)
      ((f l).2 * C + 2 * B b + 6) := by
  -- 1. pushNum 1 1
  refine Frag.runs_mono (Frag.seq_runs (t₂ := ((f l).2 * C + 2) + 1 + B b + 1 + B b) (pushNum_runs 1 1 v S₀)
    fun v₂ S₂ ⟨_, h1₂, hF₂⟩ => ?_) (fun _ _ h => h) (by simp only [Nat.log_one_right]; omega)
  -- 2. the loop
  have hloop := forEntriesN_runs_budget (x := 5) (body := body) l xr (AccInv f l S₀ C)
    ((f l).2 * C) v₂ S₂ (by rw [hF₂ 5 (by decide), h5])
    ⟨⟨true, by rw [h1₂]; rfl, by simp⟩, hF₂ 0 (by decide), hF₂ 2 (by decide), hF₂ 3 (by decide),
      hF₂ 4 (by decide), hF₂ 6 (by decide), hF₂ 7 (by decide), by simp⟩
    hbody
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1 + B b + 1 + B b) hloop
    fun v₃ S₃ ⟨_, ⟨β, ⟨acc, h1₃, hacc⟩, h0₃, h2₃, h3₃, h4₃, h6₃, h7₃, _⟩, h5₃⟩ => ?_) (fun _ _ h => h)
    (by omega)
  rw [List.drop_length, hf, Bool.and_true] at hacc
  -- 3. popTop 5
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + 1 + B b) (popTop_runs 5 v₃ S₃)
    fun v₄ S₄ ⟨_, hS₄⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₄
  -- 4. isZero 1 2
  have h1₄ : Function.update S₃ 5 (S₃ 5).tail 1 = encodeNatΓ' acc.toNat ++ .comma :: S₀ 1 := by
    rw [Function.update_of_ne (by decide), h1₃]
  have hz := isZero_acc (x := 1) (s := 2) (by decide) acc b _ v₄ _ h1₄
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1 + B b) hz
    fun v₅ S₅ ⟨hf₅, _, h1₅, h2₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 5. flag := !flag
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b) (Frag.load'_runs _ v₅ S₅)
    fun v₆ S₆ ⟨hv₆, hS₆⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hS₆]
  -- 6. dropNum 1
  have h1₅' : S₅ 1 = encodeNatΓ' acc.toNat ++ .comma :: S₀ 1 := by rw [h1₅, h1₄]
  refine Frag.runs_mono (dropNum_acc 1 acc b _ v₆ S₅ h1₅')
    (fun v₇ S₇ ⟨hf₇, _, _, h1₇, hF₇⟩ => ⟨?_, ?_, ?_⟩) le_rfl
  · rw [hf₇, hv₆, hf₅, ← hacc]
    cases acc <;> simp
  · rw [hF₇ 5 (by decide), hF₅ 5 (by decide) (by decide), Function.update_self, h5₃]; rfl
  · intro k hk5
    by_cases hk1 : k = 1
    · subst hk1; exact h1₇
    by_cases hk2 : k = 2
    · subst hk2; rw [hF₇ 2 (by decide), h2₅, Function.update_of_ne (by decide), h2₃]
    rw [hF₇ k hk1, hF₅ k hk1 hk2, Function.update_of_ne hk5]
    fin_cases k
    · exact h0₃
    · exact absurd rfl hk1
    · exact absurd rfl hk2
    · exact h3₃
    · exact h4₃
    · exact absurd rfl hk5
    · exact h6₃
    · exact h7₃

/-! ### `Alg.nodupTD` -/

/-- A `B`-form of `predNum_correct'` (no side condition, `0 ↦ 0`). -/
theorem predNum_le_B' {x s : K} (hxs : x ≠ s) (a b : ℕ) (ha : a < 2 ^ b) (xr : List Γ') (v : St)
    (S : Stacks) (hS : S x = encodeNatΓ' a ++ .comma :: xr) :
    (predNum x s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧
        S' x = encodeNatΓ' (a - 1) ++ .comma :: xr ∧ S' s = S s ∧ ∀ k, k ≠ x → k ≠ s → S' k = S k)
      (B b) := by
  refine Frag.runs_mono (predNum_correct' hxs a xr v S hS) (fun _ _ h => h) ?_
  have := log_le_of_lt_pow ha
  exact le_B_of_le_linear (by omega)

theorem drop_succ_of_drop_eq_cons {α : Type*} {l : List α} {i : ℕ} {a : α} {l' : List α}
    (h : l.drop i = a :: l') : l.drop (i + 1) = l' := by
  rw [← List.tail_drop, h]; rfl

theorem mem_tail_of_drop_eq_cons {l : List ℕ} {i a : ℕ} {l' : List ℕ} (h : l.drop i = a :: l')
    {p : ℕ} (hp : p ∈ l') : p ∈ l :=
  List.mem_of_mem_drop (by rw [h]; exact List.mem_cons_of_mem _ hp)

/-- One entry `p` (top of the copy on 5, above the tail `l'`) of `nodupTDF`:
move `p` to stack 1 (above the accumulator), `memList` against the tail, drop
`p`, and `acc := acc && (p ∉ l')`. -/
def ndBody : Frag :=
  (moveEntry 5 1 2).seq ((memList 5 1 2 3 6).seq ((dropNum 1).seq
    ((Frag.load' (fun v => { v with flag := !v.flag })).seq accAnd)))

theorem ndBody_runs (l : List ℕ) (b : ℕ) (hb : ∀ p ∈ l, p < 2 ^ b) (xr : List Γ') (S₀ : Stacks)
    (i a : ℕ) (l' : List ℕ) (hdrop : l.drop i = a :: l') (β : ℕ) (w : St) (T : Stacks)
    (hP : AccInv Alg.nodupTD l S₀ (8 * B b) i β T)
    (hT : T 5 = encodeNatΓ' a ++ .comma :: (encList l' ++ xr)) :
    ∃ t β', t + 2 + β' ≤ β ∧
      ndBody.Runs w T (fun _ T' =>
        AccInv Alg.nodupTD l S₀ (8 * B b) (i + 1) β' T' ∧ T' 5 = encList l' ++ xr) t := by
  obtain ⟨⟨acc, h1, hacc⟩, h0, h2, h3, h4, h6, h7, hβ⟩ := hP
  have ha : a < 2 ^ b := hb a (mem_of_drop_eq_cons hdrop)
  have hl' : ∀ p ∈ l', p < 2 ^ b := fun p hp => hb p (mem_tail_of_drop_eq_cons hdrop hp)
  have hdrop' : l.drop (i + 1) = l' := drop_succ_of_drop_eq_cons hdrop
  have hB1 := one_le_B b
  refine ⟨B b + (l'.length + 1) * B b + B b + 1 + (B b + B b + 1), (Alg.nodupTD l').2 * (8 * B b), ?_, ?_⟩
  · rw [hβ, hdrop, nodupTD_cons, notMemTD_snd]
    simp only
    have hX : (l'.length + (Alg.nodupTD l').2 + 1) * (8 * B b) =
        8 * ((l'.length + 1) * B b) + (Alg.nodupTD l').2 * (8 * B b) := by ring
    have hX1 : B b ≤ (l'.length + 1) * B b := Nat.le_mul_of_pos_left _ (by omega)
    have hB8 : 8 ≤ B b := le_B_of_le_linear (by omega)
    rw [hX]; omega
  -- 1. moveEntry 5 1 2
  have hm := moveEntry_le_B (src := 5) (dst := 1) (s := 2) (by decide) (by decide) (by decide) a b ha _ w T hT
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (l'.length + 1) * B b + B b + 1 + (B b + B b + 1)) hm
    fun v₁ S₁ ⟨_, _, _, h5₁, h1₁, h2₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 2. memList 5 1 2 3 6
  have h1₁' : S₁ 1 = encodeNatΓ' a ++ .comma :: (encodeNatΓ' acc.toNat ++ .comma :: S₀ 1) := by
    rw [h1₁, h1]
  have hmem := memList_le_B (x := 5) (y := 1) (s := 2) (t := 3) (z := 6) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) l' a b hl' ha xr _ v₁ S₁
    h5₁ h1₁'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + 1 + (B b + B b + 1)) hmem
    fun v₂ S₂ ⟨hf₂, h5₂, h1₂, h2₂, h3₂, h6₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. dropNum 1
  have h1₂' : S₂ 1 = encodeNatΓ' a ++ .comma :: (encodeNatΓ' acc.toNat ++ .comma :: S₀ 1) := by
    rw [h1₂, h1₁']
  have hd := dropNum_le_B (x := 1) a b ha _ v₂ S₂ h1₂'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1 + (B b + B b + 1)) hd
    fun v₃ S₃ ⟨hf₃, _, _, h1₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 4. flag := !flag
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + B b + 1) (Frag.load'_runs _ v₃ S₃)
    fun v₄ S₄ ⟨hv₄, hS₄⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hS₄]
  -- 5. accAnd
  have h1₃' : S₃ 1 = encodeNatΓ' acc.toNat ++ .comma :: S₀ 1 := by rw [h1₃]
  refine Frag.runs_mono (accAnd_runs acc b _ v₄ S₃ h1₃') (fun _ S' ⟨hS1, hF⟩ => ?_) le_rfl
  have hv₄' : v₄.flag = !decide (a ∈ l') := by rw [hv₄, hf₃, hf₂]
  refine ⟨⟨⟨acc && v₄.flag, hS1, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hdrop']⟩, ?_⟩
  · rw [hv₄', hdrop', ← hacc, hdrop, nodupTD_cons, notMemTD_fst]
    simp only [Bool.and_assoc]
  · rw [hF 0 (by decide), hF₃ 0 (by decide), hF₂ 0 (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₁ 0 (by decide) (by decide) (by decide), h0]
  · rw [hF 2 (by decide), hF₃ 2 (by decide), h2₂, h2₁, h2]
  · rw [hF 3 (by decide), hF₃ 3 (by decide), h3₂, hF₁ 3 (by decide) (by decide) (by decide), h3]
  · rw [hF 4 (by decide), hF₃ 4 (by decide), hF₂ 4 (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₁ 4 (by decide) (by decide) (by decide), h4]
  · rw [hF 6 (by decide), hF₃ 6 (by decide), h6₂, hF₁ 6 (by decide) (by decide) (by decide), h6]
  · rw [hF 7 (by decide), hF₃ 7 (by decide), hF₂ 7 (by decide) (by decide) (by decide) (by decide) (by decide),
      hF₁ 7 (by decide) (by decide) (by decide), h7]
  · rw [hF 5 (by decide), hF₃ 5 (by decide), h5₂, h5₁]

/-- `Alg.nodupTD S` for the list `S` on stack 4: copy `S` to 5, then the
accumulator loop with `ndBody`.  All eight stacks are restored. -/
def nodupTDF : Frag := (copyList 4 5 2 3).seq (accLoopF ndBody)

theorem nodupTDF_runs (S : List ℕ) (b : ℕ) (hb : ∀ p ∈ S, p < 2 ^ b) (r4 : List Γ') (v : St)
    (St : Stacks) (h4 : St 4 = encList S ++ r4) :
    nodupTDF.Runs v St (fun v' S' => v'.flag = (Alg.nodupTD S).1 ∧ S' = St)
      (((Alg.nodupTD S).2 + 1) * (16 * B b)) := by
  have hB1 := one_le_B b
  have hlen := length_le_nodupTD_cost S
  obtain ⟨n, hn⟩ : ∃ n, (Alg.nodupTD S).2 = n := ⟨_, rfl⟩
  rw [hn] at hlen ⊢
  -- 1. copyList 4 5 2 3
  have hc := copyList_le_B (x := 4) (y := 5) (s := 2) (z := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) S b hb r4 v St h4
  refine Frag.runs_mono (Frag.seq_runs (t₂ := n * (8 * B b) + 2 * B b + 6) hc
    fun v₁ S₁ ⟨h4₁, h5₁, h2₁, h3₁, hF₁⟩ => ?_) (fun _ _ h => h) ?_
  swap
  · have h1 : (S.length + 1) * B b ≤ (n + 1) * B b := Nat.mul_le_mul_right _ (by omega)
    have hB8 : 8 ≤ B b := le_B_of_le_linear (by omega)
    nlinarith [h1, hB8]
  -- 2. the accumulator loop
  have hl := accLoopF_runs Alg.nodupTD nodupTD_nil ndBody S (8 * B b) b (St 5) v₁ S₁ h5₁
    (fun i a l' hdrop β w T hP hT => ndBody_runs S b hb (St 5) S₁ i a l' hdrop β w T hP hT)
  rw [hn] at hl
  refine Frag.runs_mono hl (fun v' S' ⟨hf, h5, hF⟩ => ⟨hf, ?_⟩) le_rfl
  refine stacks_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hF 0 (by decide), hF₁ 0 (by decide) (by decide) (by decide) (by decide)]
  · rw [hF 1 (by decide), hF₁ 1 (by decide) (by decide) (by decide) (by decide)]
  · rw [hF 2 (by decide), h2₁]
  · rw [hF 3 (by decide), h3₁]
  · rw [hF 4 (by decide), h4₁]
  · exact h5
  · rw [hF 6 (by decide), hF₁ 6 (by decide) (by decide) (by decide) (by decide)]
  · rw [hF 7 (by decide), hF₁ 7 (by decide) (by decide) (by decide) (by decide)]

theorem nodupTDF_le_B (S : List ℕ) (b : ℕ) (hb : ∀ p ∈ S, p < 2 ^ b) (r4 : List Γ') (v : St)
    (St : Stacks) (h4 : St 4 = encList S ++ r4) :
    nodupTDF.Runs v St (fun v' S' => v'.flag = (Alg.nodupTD S).1 ∧ S' = St)
      (((Alg.nodupTD S).2 + 1) * B (3 * b + 4)) := by
  refine Frag.runs_mono (nodupTDF_runs S b hb r4 v St h4) (fun _ _ h => h) ?_
  rw [B_three_add_four]
  exact Nat.mul_le_mul_left _ (by omega)

/-! ### `Alg.allPrimeTD` -/

/-- One entry `p` of `allPrimeTDF`: `isPrimeTDF` on the top of stack 5 (peeked),
`acc := acc && flag`, drop `p`. -/
def apBody : Frag :=
  (isPrimeTDF 5 2 3 6 0 1).seq (accAnd.seq (dropNum 5))

theorem apBody_runs (l : List ℕ) (b : ℕ) (hb : ∀ p ∈ l, p < 2 ^ b) (xr : List Γ') (S₀ : Stacks)
    (i a : ℕ) (l' : List ℕ) (hdrop : l.drop i = a :: l') (β : ℕ) (w : St) (T : Stacks)
    (hP : AccInv Alg.allPrimeTD l S₀ (2 * B (3 * b + 7)) i β T)
    (hT : T 5 = encodeNatΓ' a ++ .comma :: (encList l' ++ xr)) :
    ∃ t β', t + 2 + β' ≤ β ∧
      apBody.Runs w T (fun _ T' =>
        AccInv Alg.allPrimeTD l S₀ (2 * B (3 * b + 7)) (i + 1) β' T' ∧ T' 5 = encList l' ++ xr) t := by
  obtain ⟨⟨acc, h1, hacc⟩, h0, h2, h3, h4, h6, h7, hβ⟩ := hP
  have ha : a < 2 ^ b := hb a (mem_of_drop_eq_cons hdrop)
  have hdrop' : l.drop (i + 1) = l' := drop_succ_of_drop_eq_cons hdrop
  have hB1 := one_le_B b
  have hBb : B b ≤ B (3 * b + 7) := B_mono (by omega)
  have hpr := isPrimeTD_cost_pos a
  refine ⟨((Alg.isPrimeTD a).2 + 1) * B (3 * b + 7) + (B b + B b + 1) + B b,
    (Alg.allPrimeTD l').2 * (2 * B (3 * b + 7)), ?_, ?_⟩
  · rw [hβ, hdrop, allPrimeTD_cons]
    simp only
    have hX : ((Alg.isPrimeTD a).2 + (Alg.allPrimeTD l').2 + 1) * (2 * B (3 * b + 7)) =
        ((Alg.isPrimeTD a).2 + 1) * B (3 * b + 7) + ((Alg.isPrimeTD a).2 + 1) * B (3 * b + 7) +
          (Alg.allPrimeTD l').2 * (2 * B (3 * b + 7)) := by ring
    have hX1 : 2 * B (3 * b + 7) ≤ ((Alg.isPrimeTD a).2 + 1) * B (3 * b + 7) :=
      Nat.mul_le_mul_right _ (by omega)
    have hB8 : 8 ≤ B b := le_B_of_le_linear (by omega)
    have hB27 : B (3 * b + 7) = 27 * B (b + 1) := B_three_add_seven b
    have hBs : B b ≤ B (b + 1) := B_succ_le b
    rw [hX]; omega
  -- 1. isPrimeTDF 5 2 3 6 0 1
  have hp := isPrimeTDF_le_B (xm := 5) (xd := 2) (xf := 3) (s := 6) (t := 0) (u := 1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) a b ha _ w T hT
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (B b + B b + 1) + B b) hp
    fun v₁ S₁ ⟨hf₁, h5₁, h2₁, h3₁, h6₁, h0₁, h1₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 2. accAnd
  have h1₁' : S₁ 1 = encodeNatΓ' acc.toNat ++ .comma :: S₀ 1 := by rw [h1₁, h1]
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b) (accAnd_runs acc b _ v₁ S₁ h1₁')
    fun v₂ S₂ ⟨h1₂, hF₂⟩ => ?_) (fun _ _ h => h) le_rfl
  -- 3. dropNum 5
  have h5₂ : S₂ 5 = encodeNatΓ' a ++ .comma :: (encList l' ++ xr) := by
    rw [hF₂ 5 (by decide), h5₁, hT]
  refine Frag.runs_mono (dropNum_le_B (x := 5) a b ha _ v₂ S₂ h5₂)
    (fun _ S' ⟨_, _, _, h5', hF'⟩ => ?_) le_rfl
  refine ⟨⟨⟨acc && v₁.flag, by rw [hF' 1 (by decide), h1₂], ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hdrop']⟩, h5'⟩
  · rw [hf₁, hdrop', ← hacc, hdrop, allPrimeTD_cons]
    simp only [Bool.and_assoc]
  · rw [hF' 0 (by decide), hF₂ 0 (by decide), h0₁, h0]
  · rw [hF' 2 (by decide), hF₂ 2 (by decide), h2₁, h2]
  · rw [hF' 3 (by decide), hF₂ 3 (by decide), h3₁, h3]
  · rw [hF' 4 (by decide), hF₂ 4 (by decide), hF₁ 4 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h4]
  · rw [hF' 6 (by decide), hF₂ 6 (by decide), h6₁, h6]
  · rw [hF' 7 (by decide), hF₂ 7 (by decide), hF₁ 7 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide), h7]

/-- `Alg.allPrimeTD S` for the list `S` on stack 4.  All eight stacks restored. -/
def allPrimeTDF : Frag := (copyList 4 5 2 3).seq (accLoopF apBody)

theorem allPrimeTDF_runs (S : List ℕ) (b : ℕ) (hb : ∀ p ∈ S, p < 2 ^ b) (r4 : List Γ') (v : St)
    (St : Stacks) (h4 : St 4 = encList S ++ r4) :
    allPrimeTDF.Runs v St (fun v' S' => v'.flag = (Alg.allPrimeTD S).1 ∧ S' = St)
      (((Alg.allPrimeTD S).2 + 1) * (4 * B (3 * b + 7))) := by
  have hB1 := one_le_B b
  have hBb : B b ≤ B (3 * b + 7) := B_mono (by omega)
  have hlen := length_le_allPrimeTD_cost S
  obtain ⟨n, hn⟩ : ∃ n, (Alg.allPrimeTD S).2 = n := ⟨_, rfl⟩
  rw [hn] at hlen ⊢
  have hc := copyList_le_B (x := 4) (y := 5) (s := 2) (z := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) S b hb r4 v St h4
  refine Frag.runs_mono (Frag.seq_runs (t₂ := n * (2 * B (3 * b + 7)) + 2 * B b + 6) hc
    fun v₁ S₁ ⟨h4₁, h5₁, h2₁, h3₁, hF₁⟩ => ?_) (fun _ _ h => h) ?_
  swap
  · have h1 : (S.length + 1) * B b ≤ (n + 1) * B (3 * b + 7) :=
      Nat.mul_le_mul (by omega) hBb
    have hB8 : 8 ≤ B b := le_B_of_le_linear (by omega)
    nlinarith [h1, hB8, hBb]
  have hl := accLoopF_runs Alg.allPrimeTD allPrimeTD_nil apBody S (2 * B (3 * b + 7)) b (St 5) v₁ S₁ h5₁
    (fun i a l' hdrop β w T hP hT => apBody_runs S b hb (St 5) S₁ i a l' hdrop β w T hP hT)
  rw [hn] at hl
  refine Frag.runs_mono hl (fun v' S' ⟨hf, h5, hF⟩ => ⟨hf, ?_⟩) le_rfl
  refine stacks_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hF 0 (by decide), hF₁ 0 (by decide) (by decide) (by decide) (by decide)]
  · rw [hF 1 (by decide), hF₁ 1 (by decide) (by decide) (by decide) (by decide)]
  · rw [hF 2 (by decide), h2₁]
  · rw [hF 3 (by decide), h3₁]
  · rw [hF 4 (by decide), h4₁]
  · exact h5
  · rw [hF 6 (by decide), hF₁ 6 (by decide) (by decide) (by decide) (by decide)]
  · rw [hF 7 (by decide), hF₁ 7 (by decide) (by decide) (by decide) (by decide)]

theorem allPrimeTDF_le_B (S : List ℕ) (b : ℕ) (hb : ∀ p ∈ S, p < 2 ^ b) (r4 : List Γ') (v : St)
    (St : Stacks) (h4 : St 4 = encList S ++ r4) :
    allPrimeTDF.Runs v St (fun v' S' => v'.flag = (Alg.allPrimeTD S).1 ∧ S' = St)
      (((Alg.allPrimeTD S).2 + 1) * B (9 * b + 25)) := by
  refine Frag.runs_mono (allPrimeTDF_runs S b hb r4 v St h4) (fun _ _ h => h) ?_
  have : B (9 * b + 25) = 27 * B (3 * b + 7) := by
    rw [show 9 * b + 25 = 3 * (3 * b + 7) + 4 by ring, B_three_add_four]
  rw [this]
  exact Nat.mul_le_mul_left _ (by omega)

/-! ### `Alg.korseltTD` -/

/-- The test `(m - 1) % (p - 1) = 0` into `flag`, for `p` on top of stack 5 and
`m` on top of stack 7 (both peeked, restored): `p - 1` on 3; if it is `0` the
test is `m - 1 = 0` (Lean's `x % 0 = x`), else `modC` on a copy of `m - 1`. -/
def koTest : Frag :=
  (dup 5 3 2).seq ((predNum 3 2).seq ((isZero 3 2).seq
    (Frag.ite (fun v => v.flag)
      ((dropNum 3).seq ((dup 7 6 2).seq ((predNum 6 2).seq ((isZero 6 2).seq (dropNum 6)))))
      ((dup 7 6 2).seq ((predNum 6 2).seq ((modC 6 3 5 4 1 2).seq ((isZero 6 2).seq (dropNum 6))))))))

theorem koTest_runs (p m b bM : ℕ) (hp : p < 2 ^ b) (hm : m < 2 ^ bM) (hbM : b ≤ bM)
    (r5 r7 : List Γ') (v : St) (S : Stacks)
    (h5 : S 5 = encodeNatΓ' p ++ .comma :: r5) (h7 : S 7 = encodeNatΓ' m ++ .comma :: r7) :
    koTest.Runs v S (fun v' S' => v'.flag = decide ((m - 1) % (p - 1) = 0) ∧ S' = S)
      (8 * B bM + 1) := by
  have hBb : B b ≤ B bM := B_mono hbM
  have hp1 : p - 1 < 2 ^ b := by omega
  have hm1 : m - 1 < 2 ^ bM := by omega
  have hpM : p - 1 < 2 ^ bM := lt_of_lt_of_le hp1 (Nat.pow_le_pow_right (by norm_num) hbM)
  -- 1. dup 5 3 2
  have h1 := dup_le_B (x := 5) (y := 3) (s := 2) (by decide) (by decide) (by decide) p b hp r5 v S h5
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + B b + (5 * B bM + 1)) h1
    fun v₁ S₁ ⟨h5₁, h3₁, h2₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 2. predNum 3 2
  have h2 := predNum_le_B' (x := 3) (s := 2) (by decide) p b hp _ v₁ S₁ h3₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + (5 * B bM + 1)) h2
    fun v₂ S₂ ⟨_, _, h3₂, h2₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. isZero 3 2
  have h3 := isZero_le_B (x := 3) (s := 2) (by decide) (p - 1) b hp1 _ v₂ S₂ h3₂
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * B bM + 1) h3
    fun v₃ S₃ ⟨hf₃, _, h3₃, h2₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  have h7₃ : S₃ 7 = encodeNatΓ' m ++ .comma :: r7 := by
    rw [hF₃ 7 (by decide) (by decide), hF₂ 7 (by decide) (by decide), hF₁ 7 (by decide) (by decide) (by decide),
      h7]
  have h3₃' : S₃ 3 = encodeNatΓ' (p - 1) ++ .comma :: S 3 := by rw [h3₃, h3₂]
  have hpost : ∀ (v' : St) (S' : Stacks), v'.flag = decide ((m - 1) % (p - 1) = 0) →
      S' 3 = S 3 → S' 2 = S 2 → S' 6 = S 6 → S' 7 = S 7 →
      (∀ k, k ≠ 3 → k ≠ 2 → k ≠ 6 → k ≠ 7 → S' k = S₃ k) →
      v'.flag = decide ((m - 1) % (p - 1) = 0) ∧ S' = S := by
    intro v' S' hf e3 e2 e6 e7 hF
    refine ⟨hf, stacks_ext ?_ ?_ e2 e3 ?_ ?_ e6 e7⟩
    · rw [hF 0 (by decide) (by decide) (by decide) (by decide), hF₃ 0 (by decide) (by decide),
        hF₂ 0 (by decide) (by decide), hF₁ 0 (by decide) (by decide) (by decide)]
    · rw [hF 1 (by decide) (by decide) (by decide) (by decide), hF₃ 1 (by decide) (by decide),
        hF₂ 1 (by decide) (by decide), hF₁ 1 (by decide) (by decide) (by decide)]
    · rw [hF 4 (by decide) (by decide) (by decide) (by decide), hF₃ 4 (by decide) (by decide),
        hF₂ 4 (by decide) (by decide), hF₁ 4 (by decide) (by decide) (by decide)]
    · rw [hF 5 (by decide) (by decide) (by decide) (by decide), hF₃ 5 (by decide) (by decide),
        hF₂ 5 (by decide) (by decide), h5₁]
  refine Frag.ite_runs (t := 5 * B bM) (fun hc => ?_) (fun hc => ?_)
  · -- p - 1 = 0: the test is m - 1 = 0
    have hc' : p - 1 = 0 := by
      have : decide (p - 1 = 0) = true := by rw [← hf₃]; exact hc
      simpa using this
    -- dropNum 3
    have hd := dropNum_le_B (x := 3) (p - 1) bM hpM _ v₃ S₃ h3₃'
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B bM + B bM + B bM + B bM) hd
      fun v₄ S₄ ⟨_, _, _, h3₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
    -- dup 7 6 2
    have h7₄ : S₄ 7 = encodeNatΓ' m ++ .comma :: r7 := by rw [hF₄ 7 (by decide), h7₃]
    have hd2 := dup_le_B (x := 7) (y := 6) (s := 2) (by decide) (by decide) (by decide) m bM hm r7 v₄ S₄ h7₄
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B bM + B bM + B bM) hd2
      fun v₅ S₅ ⟨h7₅, h6₅, h2₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
    -- predNum 6 2
    have hp2 := predNum_le_B' (x := 6) (s := 2) (by decide) m bM hm _ v₅ S₅ h6₅
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B bM + B bM) hp2
      fun v₆ S₆ ⟨_, _, h6₆, h2₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
    -- isZero 6 2
    have hz := isZero_le_B (x := 6) (s := 2) (by decide) (m - 1) bM hm1 _ v₆ S₆ h6₆
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B bM) hz
      fun v₇ S₇ ⟨hf₇, _, h6₇, h2₇, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
    -- dropNum 6
    have h6₇' : S₇ 6 = encodeNatΓ' (m - 1) ++ .comma :: S₄ 6 := by rw [h6₇, h6₆]
    refine Frag.runs_mono (dropNum_le_B (x := 6) (m - 1) bM hm1 _ v₇ S₇ h6₇')
      (fun v' S' ⟨hf', _, _, h6', hF'⟩ => hpost v' S' ?_ ?_ ?_ ?_ ?_ ?_) le_rfl
    · rw [hf', hf₇, hc', Nat.mod_zero]
    · rw [hF' 3 (by decide), hF₇ 3 (by decide) (by decide), hF₆ 3 (by decide) (by decide),
        hF₅ 3 (by decide) (by decide) (by decide), h3₄]
    · rw [hF' 2 (by decide), h2₇, h2₆, h2₅, hF₄ 2 (by decide), h2₃, h2₂, h2₁]
    · rw [h6', hF₄ 6 (by decide), hF₃ 6 (by decide) (by decide), hF₂ 6 (by decide) (by decide),
        hF₁ 6 (by decide) (by decide) (by decide)]
    · rw [hF' 7 (by decide), hF₇ 7 (by decide) (by decide), hF₆ 7 (by decide) (by decide), h7₅, h7₄, h7]
    · intro k hk3 hk2 hk6 hk7
      rw [hF' k hk6, hF₇ k hk6 hk2, hF₆ k hk6 hk2, hF₅ k hk7 hk6 hk2, hF₄ k hk3]
  · -- 1 ≤ p - 1: modC
    have hc' : ¬ p - 1 = 0 := by
      have : decide (p - 1 = 0) = false := by rw [← hf₃]; exact hc
      simpa using this
    -- dup 7 6 2
    have hd2 := dup_le_B (x := 7) (y := 6) (s := 2) (by decide) (by decide) (by decide) m bM hm r7 v₃ S₃ h7₃
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B bM + B bM + B bM + B bM) hd2
      fun v₄ S₄ ⟨h7₄, h6₄, h2₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
    -- predNum 6 2
    have hp2 := predNum_le_B' (x := 6) (s := 2) (by decide) m bM hm _ v₄ S₄ h6₄
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B bM + B bM + B bM) hp2
      fun v₅ S₅ ⟨_, _, h6₅, h2₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
    -- modC 6 3 5 4 1 2
    have h3₅ : S₅ 3 = encodeNatΓ' (p - 1) ++ .comma :: S 3 := by
      rw [hF₅ 3 (by decide) (by decide), hF₄ 3 (by decide) (by decide) (by decide), h3₃']
    have hmod := modC_le_B (x := 6) (y := 3) (q := 5) (j := 4) (s := 1) (t := 2) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (m - 1) (p - 1) bM (by omega) hm1 hpM _ _ v₅ S₅ h6₅ h3₅
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B bM + B bM) hmod
      fun v₆ S₆ ⟨h6₆, h3₆, h5₆, h4₆, h1₆, h2₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
    -- isZero 6 2
    have hmm : (m - 1) % (p - 1) < 2 ^ bM := lt_of_le_of_lt (Nat.mod_le _ _) hm1
    have hz := isZero_le_B (x := 6) (s := 2) (by decide) ((m - 1) % (p - 1)) bM hmm _ v₆ S₆ h6₆
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B bM) hz
      fun v₇ S₇ ⟨hf₇, _, h6₇, h2₇, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
    -- dropNum 6
    have h6₇' : S₇ 6 = encodeNatΓ' ((m - 1) % (p - 1)) ++ .comma :: S₃ 6 := by rw [h6₇, h6₆]
    refine Frag.runs_mono (dropNum_le_B (x := 6) ((m - 1) % (p - 1)) bM hmm _ v₇ S₇ h6₇')
      (fun v' S' ⟨hf', _, _, h6', hF'⟩ => hpost v' S' ?_ ?_ ?_ ?_ ?_ ?_) le_rfl
    · rw [hf', hf₇]
    · rw [hF' 3 (by decide), hF₇ 3 (by decide) (by decide), h3₆]
    · rw [hF' 2 (by decide), h2₇, h2₆, h2₅, h2₄, h2₃, h2₂, h2₁]
    · rw [h6', hF₃ 6 (by decide) (by decide), hF₂ 6 (by decide) (by decide),
        hF₁ 6 (by decide) (by decide) (by decide)]
    · rw [hF' 7 (by decide), hF₇ 7 (by decide) (by decide),
        hF₆ 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hF₅ 7 (by decide) (by decide), h7₄, h7₃, h7]
    · intro k hk3 hk2 hk6 hk7
      rw [hF' k hk6, hF₇ k hk6 hk2]
      by_cases hk5 : k = 5
      · subst hk5; rw [h5₆, hF₅ 5 (by decide) (by decide), hF₄ 5 (by decide) (by decide) (by decide)]
      by_cases hk4 : k = 4
      · subst hk4; rw [h4₆, hF₅ 4 (by decide) (by decide), hF₄ 4 (by decide) (by decide) (by decide)]
      by_cases hk1 : k = 1
      · subst hk1; rw [h1₆, hF₅ 1 (by decide) (by decide), hF₄ 1 (by decide) (by decide) (by decide)]
      rw [hF₆ k hk6 hk3 hk5 hk4 hk1 hk2, hF₅ k hk6 hk2, hF₄ k hk7 hk6 hk2]


/-- One entry `p` of `korseltTDF`: `koTest` (peeks `p` on 5 and `m` on 7),
`acc := acc && flag`, drop `p`. -/
def koBody : Frag := koTest.seq (accAnd.seq (dropNum 5))

theorem koBody_runs (m : ℕ) (l : List ℕ) (b bM : ℕ) (hb : ∀ p ∈ l, p < 2 ^ b) (hm : m < 2 ^ bM)
    (hbM : b ≤ bM) (xr r7 : List Γ') (S₀ : Stacks) (h7 : S₀ 7 = encodeNatΓ' m ++ .comma :: r7)
    (i a : ℕ) (l' : List ℕ) (hdrop : l.drop i = a :: l') (β : ℕ) (w : St) (T : Stacks)
    (hP : AccInv (Alg.korseltTD m) l S₀ (12 * B bM) i β T)
    (hT : T 5 = encodeNatΓ' a ++ .comma :: (encList l' ++ xr)) :
    ∃ t β', t + 2 + β' ≤ β ∧
      koBody.Runs w T (fun _ T' =>
        AccInv (Alg.korseltTD m) l S₀ (12 * B bM) (i + 1) β' T' ∧ T' 5 = encList l' ++ xr) t := by
  obtain ⟨⟨acc, h1, hacc⟩, h0, h2, h3, h4, h6, h7', hβ⟩ := hP
  have ha : a < 2 ^ b := hb a (mem_of_drop_eq_cons hdrop)
  have hdrop' : l.drop (i + 1) = l' := drop_succ_of_drop_eq_cons hdrop
  have hBb : B b ≤ B bM := B_mono hbM
  have hB8 : 8 ≤ B bM := le_B_of_le_linear (by omega)
  refine ⟨8 * B bM + 1 + (B bM + B bM + 1) + B bM, (Alg.korseltTD m l').2 * (12 * B bM), ?_, ?_⟩
  · rw [hβ, hdrop, korseltTD_cons]
    simp only
    have hX : ((Alg.korseltTD m l').2 + 1) * (12 * B bM) =
        (Alg.korseltTD m l').2 * (12 * B bM) + 12 * B bM := by ring
    rw [hX]; omega
  -- 1. koTest
  have h7T : T 7 = encodeNatΓ' m ++ .comma :: r7 := by rw [h7', h7]
  have hk := koTest_runs a m b bM ha hm hbM _ r7 w T hT h7T
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (B bM + B bM + 1) + B bM) hk
    fun v₁ S₁ ⟨hf₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hS₁]
  -- 2. accAnd
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B bM) (accAnd_runs acc bM _ v₁ T h1)
    fun v₂ S₂ ⟨h1₂, hF₂⟩ => ?_) (fun _ _ h => h) le_rfl
  -- 3. dropNum 5
  have h5₂ : S₂ 5 = encodeNatΓ' a ++ .comma :: (encList l' ++ xr) := by rw [hF₂ 5 (by decide), hT]
  refine Frag.runs_mono (dropNum_le_B (x := 5) a bM (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by norm_num) hbM))
    _ v₂ S₂ h5₂) (fun _ S' ⟨_, _, _, h5', hF'⟩ => ?_) le_rfl
  refine ⟨⟨⟨acc && v₁.flag, by rw [hF' 1 (by decide), h1₂], ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, by rw [hdrop']⟩, h5'⟩
  · rw [hf₁, hdrop', ← hacc, hdrop, korseltTD_cons']
    simp only [Bool.and_assoc]
  · rw [hF' 0 (by decide), hF₂ 0 (by decide), h0]
  · rw [hF' 2 (by decide), hF₂ 2 (by decide), h2]
  · rw [hF' 3 (by decide), hF₂ 3 (by decide), h3]
  · rw [hF' 4 (by decide), hF₂ 4 (by decide), h4]
  · rw [hF' 6 (by decide), hF₂ 6 (by decide), h6]
  · rw [hF' 7 (by decide), hF₂ 7 (by decide), h7']

/-- `Alg.korseltTD m S` for the list `S` on stack 4 and `m` on stack 7.  All eight
stacks restored. -/
def korseltTDF : Frag := (copyList 4 5 2 3).seq (accLoopF koBody)

theorem korseltTDF_runs (m : ℕ) (S : List ℕ) (b bM : ℕ) (hb : ∀ p ∈ S, p < 2 ^ b) (hm : m < 2 ^ bM)
    (hbM : b ≤ bM) (r4 r7 : List Γ') (v : St) (St : Stacks) (h4 : St 4 = encList S ++ r4)
    (h7 : St 7 = encodeNatΓ' m ++ .comma :: r7) :
    korseltTDF.Runs v St (fun v' S' => v'.flag = (Alg.korseltTD m S).1 ∧ S' = St)
      (((Alg.korseltTD m S).2 + 1) * (16 * B bM)) := by
  have hBb : B b ≤ B bM := B_mono hbM
  have hB8 : 8 ≤ B bM := le_B_of_le_linear (by omega)
  rw [korseltTD_snd]
  have hc := copyList_le_B (x := 4) (y := 5) (s := 2) (z := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) S b hb r4 v St h4
  refine Frag.runs_mono (Frag.seq_runs (t₂ := S.length * (12 * B bM) + 2 * B bM + 6) hc
    fun v₁ S₁ ⟨h4₁, h5₁, h2₁, h3₁, hF₁⟩ => ?_) (fun _ _ h => h) ?_
  swap
  · have h1 : (S.length + 1) * B b ≤ (S.length + 1) * B bM := Nat.mul_le_mul_left _ hBb
    nlinarith [h1, hB8]
  have h7₁ : S₁ 7 = encodeNatΓ' m ++ .comma :: r7 := by
    rw [hF₁ 7 (by decide) (by decide) (by decide) (by decide), h7]
  have hl := accLoopF_runs (Alg.korseltTD m) (korseltTD_nil m) koBody S (12 * B bM) bM (St 5) v₁ S₁ h5₁
    (fun i a l' hdrop β w T hP hT => koBody_runs m S b bM hb hm hbM (St 5) r7 S₁ h7₁ i a l' hdrop β w T hP hT)
  rw [korseltTD_snd] at hl
  refine Frag.runs_mono hl (fun v' S' ⟨hf, h5, hF⟩ => ⟨hf, ?_⟩) le_rfl
  refine stacks_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hF 0 (by decide), hF₁ 0 (by decide) (by decide) (by decide) (by decide)]
  · rw [hF 1 (by decide), hF₁ 1 (by decide) (by decide) (by decide) (by decide)]
  · rw [hF 2 (by decide), h2₁]
  · rw [hF 3 (by decide), h3₁]
  · rw [hF 4 (by decide), h4₁]
  · exact h5
  · rw [hF 6 (by decide), hF₁ 6 (by decide) (by decide) (by decide) (by decide)]
  · rw [hF 7 (by decide), hF₁ 7 (by decide) (by decide) (by decide) (by decide)]

/-! ### `Alg.verify` -/

/-- A `B`-form of `cmp_correct`. -/
theorem cmp_le_B {x y : K} (hxy : x ≠ y) (a b m : ℕ) (ha : a < 2 ^ m) (hb : b < 2 ^ m)
    (xr yr : List Γ') (v : St) (S : Stacks) (hSx : S x = encodeNatΓ' a ++ .comma :: xr)
    (hSy : S y = encodeNatΓ' b ++ .comma :: yr) :
    (cmpFrag x y).Runs v S (fun v' S' =>
        v'.cmp = compare a b ∧ S' x = xr ∧ S' y = yr ∧ ∀ k, k ≠ x → k ≠ y → S' k = S k)
      (B m) := by
  refine Frag.runs_mono (cmp_correct hxy a b xr yr v S hSx hSy) (fun _ _ h => h) ?_
  have := log_le_of_lt_pow ha
  have := log_le_of_lt_pow hb
  exact le_B_of_le_linear (by omega)

/-- The bit-length argument of `verifyF`'s budget: `2 (|S| + 1) b + 3 b + bM + 8`. -/
def verifyX (l b bM : ℕ) : ℕ := 2 * (l + 1) * b + 3 * b + bM + 8

/-- `Alg.verify m S` for the list `S` on stack 4 and `m` on stack 7: the
accumulator `1` on stack 1, then `nodupTDF`, `allPrimeTDF`, `prodLF` compared
with `m`, `korseltTDF`, `3 ≤ |S|`, each ANDed into the accumulator, which is
read into `flag` at the end.  All eight stacks restored. -/
def verifyF : Frag :=
  (pushNum 1 1).seq ((nodupTDF).seq ((accAnd).seq ((allPrimeTDF).seq ((accAnd).seq ((prodLF 4 5 6 2 3).seq ((dup 7 6 2).seq ((cmpFrag 5 6).seq ((Frag.load' (fun v => { v with flag := decide (v.cmp = .eq) })).seq ((accAnd).seq ((korseltTDF).seq ((accAnd).seq ((listLen 4 5 2 3).seq ((pushNum 6 3).seq ((cmpFrag 6 5).seq ((Frag.load' (fun v => { v with flag := !decide (v.cmp = .gt) })).seq ((accAnd).seq ((isZero 1 2).seq ((Frag.load' (fun v => { v with flag := !v.flag })).seq (dropNum 1)))))))))))))))))))

theorem verifyF_runs (m : ℕ) (S : List ℕ) (b bM : ℕ) (hb : ∀ p ∈ S, p < 2 ^ b) (hlen : S.length < 2 ^ b)
    (hm : m < 2 ^ bM) (hbM : b ≤ bM) (r4 r7 : List Γ') (v : St) (St : Stacks)
    (h4 : St 4 = encList S ++ r4) (h7 : St 7 = encodeNatΓ' m ++ .comma :: r7) :
    verifyF.Runs v St (fun v' S' => v'.flag = (Alg.verify m S).1 ∧ S' = St)
      (((Alg.verify m S).2 + 1) * (32 * B (verifyX S.length b bM))) := by
  obtain ⟨X, hX⟩ : ∃ X, verifyX S.length b bM = X := ⟨_, rfl⟩
  have hXdef : X = 2 * (S.length + 1) * b + 3 * b + bM + 8 := by rw [← hX]; rfl
  have hB8 : 8 ≤ B X := le_B_of_le_linear (by omega)
  have hBb : B b ≤ B X := B_mono (by omega)
  have hBM : B bM ≤ B X := B_mono (by omega)
  have hB34 : B (3 * b + 4) ≤ B X := B_mono (by omega)
  have hB37 : B (3 * b + 7) ≤ B X := B_mono (by omega)
  have hBp : B (2 * (S.length + 1) * b + 4) ≤ B X := B_mono (by omega)
  have hpd : (Alg.prodL S).1 < 2 ^ X := by
    have := prodL_le_two_pow hb
    calc (Alg.prodL S).1 ≤ 2 ^ (S.length * b) := this
      _ < 2 ^ X := Nat.pow_lt_pow_right (by norm_num) (by rw [hXdef]; nlinarith)
  have hmX : m < 2 ^ X := lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h3X : 3 < 2 ^ X := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ X))
  have hlX : S.length < 2 ^ X := lt_of_lt_of_le hlen (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [hX, verify_eq]
  simp only
  obtain ⟨nd, hnd⟩ : ∃ nd, (Alg.nodupTD S).2 = nd := ⟨_, rfl⟩
  obtain ⟨pr, hpr⟩ : ∃ pr, (Alg.allPrimeTD S).2 = pr := ⟨_, rfl⟩
  obtain ⟨ko, hko⟩ : ∃ ko, (Alg.korseltTD m S).2 = ko := ⟨_, rfl⟩
  rw [hnd, hpr, hko, prodL_snd]
  have hbud : B X + ((nd + 1) * (16 * B b) + (B X + B X + 1 + ((pr + 1) * (4 * B (3 * b + 7)) + (B X + B X + 1 + ((S.length + 1) * B (2 * (S.length + 1) * b + 4) + (B X + (B X + (1 + (B X + B X + 1 + ((ko + 1) * (16 * B bM) + (B X + B X + 1 + ((S.length + 1) * B b + (B X + (B X + (1 + (B X + B X + 1 + (B X + (1 + (B X))))))))))))))))))) ≤ (nd + pr + S.length + ko + 2 + 1) * (32 * B X) := by
    have e1 : (nd + 1) * (16 * B b) ≤ (nd + 1) * (16 * B X) := Nat.mul_le_mul_left _ (by omega)
    have e2 : (pr + 1) * (4 * B (3 * b + 7)) ≤ (pr + 1) * (4 * B X) := Nat.mul_le_mul_left _ (by omega)
    have e3 : (S.length + 1) * B (2 * (S.length + 1) * b + 4) ≤ (S.length + 1) * B X :=
      Nat.mul_le_mul_left _ hBp
    have e4 : (ko + 1) * (16 * B bM) ≤ (ko + 1) * (16 * B X) := Nat.mul_le_mul_left _ (by omega)
    have e5 : (S.length + 1) * B b ≤ (S.length + 1) * B X := Nat.mul_le_mul_left _ hBb
    nlinarith [e1, e2, e3, e4, e5, hB8]
  refine Frag.runs_mono ?_ (fun _ _ h => h) hbud
  -- 1. pushNum 1 1
  have h1X : 1 < 2 ^ X := Nat.one_lt_two_pow (by omega)
  refine Frag.seq_runs (t₂ := (nd + 1) * (16 * B b) + (B X + B X + 1 + ((pr + 1) * (4 * B (3 * b + 7)) + (B X + B X + 1 + ((S.length + 1) * B (2 * (S.length + 1) * b + 4) + (B X + (B X + (1 + (B X + B X + 1 + ((ko + 1) * (16 * B bM) + (B X + B X + 1 + ((S.length + 1) * B b + (B X + (B X + (1 + (B X + B X + 1 + (B X + (1 + (B X))))))))))))))))))) (pushNum_le_B 1 1 X h1X v St) fun v₁ S₁ ⟨_, h1₁, hF₁⟩ => ?_
  -- 2. nodupTDF
  have h4₁ : S₁ 4 = encList S ++ r4 := by rw [hF₁ 4 (by decide), h4]
  have hnd' := nodupTDF_runs S b hb r4 v₁ S₁ h4₁
  rw [hnd] at hnd'
  refine Frag.seq_runs (t₂ := B X + B X + 1 + ((pr + 1) * (4 * B (3 * b + 7)) + (B X + B X + 1 + ((S.length + 1) * B (2 * (S.length + 1) * b + 4) + (B X + (B X + (1 + (B X + B X + 1 + ((ko + 1) * (16 * B bM) + (B X + B X + 1 + ((S.length + 1) * B b + (B X + (B X + (1 + (B X + B X + 1 + (B X + (1 + (B X)))))))))))))))))) hnd' fun v₂ S₂ ⟨hf₂, hS₂⟩ => ?_
  rw [hS₂]
  -- 3. accAnd
  refine Frag.seq_runs (t₂ := (pr + 1) * (4 * B (3 * b + 7)) + (B X + B X + 1 + ((S.length + 1) * B (2 * (S.length + 1) * b + 4) + (B X + (B X + (1 + (B X + B X + 1 + ((ko + 1) * (16 * B bM) + (B X + B X + 1 + ((S.length + 1) * B b + (B X + (B X + (1 + (B X + B X + 1 + (B X + (1 + (B X))))))))))))))))) (accAnd_runs true X _ v₂ S₁ h1₁) fun v₃ S₃ ⟨h1₃, hF₃⟩ => ?_
  rw [hf₂, Bool.true_and] at h1₃
  -- 4. allPrimeTDF
  have h4₃ : S₃ 4 = encList S ++ r4 := by rw [hF₃ 4 (by decide), h4₁]
  have hpr' := allPrimeTDF_runs S b hb r4 v₃ S₃ h4₃
  rw [hpr] at hpr'
  refine Frag.seq_runs (t₂ := B X + B X + 1 + ((S.length + 1) * B (2 * (S.length + 1) * b + 4) + (B X + (B X + (1 + (B X + B X + 1 + ((ko + 1) * (16 * B bM) + (B X + B X + 1 + ((S.length + 1) * B b + (B X + (B X + (1 + (B X + B X + 1 + (B X + (1 + (B X)))))))))))))))) hpr' fun v₄ S₄ ⟨hf₄, hS₄⟩ => ?_
  rw [hS₄]
  -- 5. accAnd
  refine Frag.seq_runs (t₂ := (S.length + 1) * B (2 * (S.length + 1) * b + 4) + (B X + (B X + (1 + (B X + B X + 1 + ((ko + 1) * (16 * B bM) + (B X + B X + 1 + ((S.length + 1) * B b + (B X + (B X + (1 + (B X + B X + 1 + (B X + (1 + (B X))))))))))))))) (accAnd_runs _ X _ v₄ S₃ h1₃) fun v₅ S₅ ⟨h1₅, hF₅⟩ => ?_
  rw [hf₄] at h1₅
  -- 6. prodLF 4 5 6 2 3
  have h4₅ : S₅ 4 = encList S ++ r4 := by rw [hF₅ 4 (by decide), h4₃]
  have hpl := prodLF_le_B (x := 4) (w := 5) (c := 6) (s := 2) (t := 3) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) S b hb r4 v₅ S₅ h4₅
  rw [prodL_snd] at hpl
  refine Frag.seq_runs (t₂ := B X + (B X + (1 + (B X + B X + 1 + ((ko + 1) * (16 * B bM) + (B X + B X + 1 + ((S.length + 1) * B b + (B X + (B X + (1 + (B X + B X + 1 + (B X + (1 + (B X)))))))))))))) hpl fun v₆ S₆ ⟨h4₆, h5₆, h6₆, h2₆, h3₆, hF₆⟩ => ?_
  -- 7. dup 7 6 2
  have h7₆ : S₆ 7 = encodeNatΓ' m ++ .comma :: r7 := by
    rw [hF₆ 7 (by decide) (by decide) (by decide) (by decide) (by decide), hF₅ 7 (by decide),
      hF₃ 7 (by decide), hF₁ 7 (by decide), h7]
  refine Frag.seq_runs (t₂ := B X + (1 + (B X + B X + 1 + ((ko + 1) * (16 * B bM) + (B X + B X + 1 + ((S.length + 1) * B b + (B X + (B X + (1 + (B X + B X + 1 + (B X + (1 + (B X))))))))))))) (dup_le_B (x := 7) (y := 6) (s := 2) (by decide) (by decide) (by decide) m X hmX r7 v₆ S₆
    h7₆) fun v₇ S₇ ⟨h7₇, h6₇, h2₇, hF₇⟩ => ?_
  -- 8. cmpFrag 5 6
  have h5₇ : S₇ 5 = encodeNatΓ' (Alg.prodL S).1 ++ .comma :: S₅ 5 := by
    rw [hF₇ 5 (by decide) (by decide) (by decide), h5₆]
  have h6₇' : S₇ 6 = encodeNatΓ' m ++ .comma :: S₆ 6 := by rw [h6₇]
  refine Frag.seq_runs (t₂ := 1 + (B X + B X + 1 + ((ko + 1) * (16 * B bM) + (B X + B X + 1 + ((S.length + 1) * B b + (B X + (B X + (1 + (B X + B X + 1 + (B X + (1 + (B X)))))))))))) (cmp_le_B (x := 5) (y := 6) (by decide) _ m X hpd hmX _ _ v₇ S₇ h5₇ h6₇')
    fun v₈ S₈ ⟨hc₈, h5₈, h6₈, hF₈⟩ => ?_
  -- 9. flag := (cmp = eq)
  refine Frag.seq_runs (t₂ := B X + B X + 1 + ((ko + 1) * (16 * B bM) + (B X + B X + 1 + ((S.length + 1) * B b + (B X + (B X + (1 + (B X + B X + 1 + (B X + (1 + (B X))))))))))) (Frag.load'_runs _ v₈ S₈) fun v₉ S₉ ⟨hv₉, hS₉⟩ => ?_
  rw [hS₉]
  -- 10. accAnd
  have h1₈ : S₈ 1 = encodeNatΓ' ((Alg.nodupTD S).1 && (Alg.allPrimeTD S).1).toNat ++ .comma :: St 1 := by
    rw [hF₈ 1 (by decide) (by decide), hF₇ 1 (by decide) (by decide) (by decide),
      hF₆ 1 (by decide) (by decide) (by decide) (by decide) (by decide), h1₅]
  refine Frag.seq_runs (t₂ := (ko + 1) * (16 * B bM) + (B X + B X + 1 + ((S.length + 1) * B b + (B X + (B X + (1 + (B X + B X + 1 + (B X + (1 + (B X)))))))))) (accAnd_runs _ X _ v₉ S₈ h1₈) fun v₁₀ S₁₀ ⟨h1₁₀, hF₁₀⟩ => ?_
  have hv₉' : v₉.flag = decide ((Alg.prodL S).1 = m) := by
    rw [hv₉]; simp only [hc₈, compare_eq_iff_eq]
  rw [hv₉'] at h1₁₀
  -- 11. korseltTDF
  have h4₁₀ : S₁₀ 4 = encList S ++ r4 := by
    rw [hF₁₀ 4 (by decide), hF₈ 4 (by decide) (by decide), hF₇ 4 (by decide) (by decide) (by decide), h4₆, h4₅]
  have h7₁₀ : S₁₀ 7 = encodeNatΓ' m ++ .comma :: r7 := by
    rw [hF₁₀ 7 (by decide), hF₈ 7 (by decide) (by decide), h7₇, h7₆]
  have hko' := korseltTDF_runs m S b bM hb hm hbM r4 r7 v₁₀ S₁₀ h4₁₀ h7₁₀
  rw [hko] at hko'
  refine Frag.seq_runs (t₂ := B X + B X + 1 + ((S.length + 1) * B b + (B X + (B X + (1 + (B X + B X + 1 + (B X + (1 + (B X))))))))) hko' fun v₁₁ S₁₁ ⟨hf₁₁, hS₁₁⟩ => ?_
  rw [hS₁₁]
  -- 12. accAnd
  refine Frag.seq_runs (t₂ := (S.length + 1) * B b + (B X + (B X + (1 + (B X + B X + 1 + (B X + (1 + (B X)))))))) (accAnd_runs _ X _ v₁₁ S₁₀ h1₁₀) fun v₁₂ S₁₂ ⟨h1₁₂, hF₁₂⟩ => ?_
  rw [hf₁₁] at h1₁₂
  -- 13. listLen 4 5 2 3
  have h4₁₂ : S₁₂ 4 = encList S ++ r4 := by rw [hF₁₂ 4 (by decide), h4₁₀]
  have hll := listLen_le_B (x := 4) (y := 5) (s := 2) (z := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) S b hb hlen r4 v₁₂ S₁₂ h4₁₂
  refine Frag.seq_runs (t₂ := B X + (B X + (1 + (B X + B X + 1 + (B X + (1 + (B X))))))) hll fun v₁₃ S₁₃ ⟨h4₁₃, h5₁₃, h2₁₃, h3₁₃, hF₁₃⟩ => ?_
  -- 14. pushNum 6 3
  refine Frag.seq_runs (t₂ := B X + (1 + (B X + B X + 1 + (B X + (1 + (B X)))))) (pushNum_le_B 6 3 X h3X v₁₃ S₁₃) fun v₁₄ S₁₄ ⟨_, h6₁₄, hF₁₄⟩ => ?_
  -- 15. cmpFrag 6 5
  have h5₁₄ : S₁₄ 5 = encodeNatΓ' S.length ++ .comma :: S₁₂ 5 := by rw [hF₁₄ 5 (by decide), h5₁₃]
  refine Frag.seq_runs (t₂ := 1 + (B X + B X + 1 + (B X + (1 + (B X))))) (cmp_le_B (x := 6) (y := 5) (by decide) 3 S.length X h3X hlX _ _ v₁₄ S₁₄ h6₁₄ h5₁₄)
    fun v₁₅ S₁₅ ⟨hc₁₅, h6₁₅, h5₁₅, hF₁₅⟩ => ?_
  -- 16. flag := !(cmp = gt)
  refine Frag.seq_runs (t₂ := B X + B X + 1 + (B X + (1 + (B X)))) (Frag.load'_runs _ v₁₅ S₁₅) fun v₁₆ S₁₆ ⟨hv₁₆, hS₁₆⟩ => ?_
  rw [hS₁₆]
  -- 17. accAnd
  have h1₁₅ : S₁₅ 1 = encodeNatΓ' ((Alg.nodupTD S).1 && (Alg.allPrimeTD S).1 &&
      decide ((Alg.prodL S).1 = m) && (Alg.korseltTD m S).1).toNat ++ .comma :: St 1 := by
    rw [hF₁₅ 1 (by decide) (by decide), hF₁₄ 1 (by decide), hF₁₃ 1 (by decide) (by decide) (by decide) (by decide),
      h1₁₂]
  refine Frag.seq_runs (t₂ := B X + (1 + (B X))) (accAnd_runs _ X _ v₁₆ S₁₅ h1₁₅) fun v₁₇ S₁₇ ⟨h1₁₇, hF₁₇⟩ => ?_
  have hv₁₆' : v₁₆.flag = decide (3 ≤ S.length) := by
    rw [hv₁₆]; simp only [hc₁₅, compare_gt_iff_gt]
    by_cases h : 3 ≤ S.length
    · simp [h]
    · simp [h, not_le.mp h]
  rw [hv₁₆'] at h1₁₇
  -- 18. isZero 1 2
  refine Frag.seq_runs (t₂ := 1 + (B X)) (isZero_acc (x := 1) (s := 2) (by decide) _ X _ v₁₇ S₁₇ h1₁₇)
    fun v₁₈ S₁₈ ⟨hf₁₈, _, h1₁₈, h2₁₈, hF₁₈⟩ => ?_
  -- 19. flag := !flag
  refine Frag.seq_runs (t₂ := B X) (Frag.load'_runs _ v₁₈ S₁₈) fun v₁₉ S₁₉ ⟨hv₁₉, hS₁₉⟩ => ?_
  rw [hS₁₉]
  -- 20. dropNum 1
  have h1₁₈' : S₁₈ 1 = encodeNatΓ' ((Alg.nodupTD S).1 && (Alg.allPrimeTD S).1 &&
      decide ((Alg.prodL S).1 = m) && (Alg.korseltTD m S).1 && decide (3 ≤ S.length)).toNat ++
      .comma :: St 1 := by rw [h1₁₈, h1₁₇]
  refine Frag.runs_mono (dropNum_acc 1 _ X _ v₁₉ S₁₈ h1₁₈') (fun v' S' ⟨hf', _, _, h1', hF'⟩ => ⟨?_, ?_⟩) le_rfl
  · rw [hf', hv₁₉, hf₁₈, beq_eq_decide_eq]
    generalize ((Alg.nodupTD S).1 && (Alg.allPrimeTD S).1 && decide ((Alg.prodL S).1 = m) &&
      (Alg.korseltTD m S).1 && decide (3 ≤ S.length)) = acc
    cases acc <;> simp
  · refine stacks_ext ?_ h1' ?_ ?_ ?_ ?_ ?_ ?_
    · rw [hF' 0 (by decide), hF₁₈ 0 (by decide) (by decide), hF₁₇ 0 (by decide), hF₁₅ 0 (by decide) (by decide),
        hF₁₄ 0 (by decide), hF₁₃ 0 (by decide) (by decide) (by decide) (by decide), hF₁₂ 0 (by decide),
        hF₁₀ 0 (by decide), hF₈ 0 (by decide) (by decide), hF₇ 0 (by decide) (by decide) (by decide),
        hF₆ 0 (by decide) (by decide) (by decide) (by decide) (by decide), hF₅ 0 (by decide), hF₃ 0 (by decide),
        hF₁ 0 (by decide)]
    · rw [hF' 2 (by decide), h2₁₈, hF₁₇ 2 (by decide), hF₁₅ 2 (by decide) (by decide), hF₁₄ 2 (by decide),
        h2₁₃, hF₁₂ 2 (by decide), hF₁₀ 2 (by decide), hF₈ 2 (by decide) (by decide), h2₇, h2₆,
        hF₅ 2 (by decide), hF₃ 2 (by decide), hF₁ 2 (by decide)]
    · rw [hF' 3 (by decide), hF₁₈ 3 (by decide) (by decide), hF₁₇ 3 (by decide), hF₁₅ 3 (by decide) (by decide),
        hF₁₄ 3 (by decide), h3₁₃, hF₁₂ 3 (by decide), hF₁₀ 3 (by decide), hF₈ 3 (by decide) (by decide),
        hF₇ 3 (by decide) (by decide) (by decide), h3₆, hF₅ 3 (by decide), hF₃ 3 (by decide), hF₁ 3 (by decide)]
    · rw [hF' 4 (by decide), hF₁₈ 4 (by decide) (by decide), hF₁₇ 4 (by decide), hF₁₅ 4 (by decide) (by decide),
        hF₁₄ 4 (by decide), h4₁₃, h4₁₂, h4]
    · rw [hF' 5 (by decide), hF₁₈ 5 (by decide) (by decide), hF₁₇ 5 (by decide), h5₁₅, hF₁₂ 5 (by decide),
        hF₁₀ 5 (by decide), h5₈, hF₅ 5 (by decide), hF₃ 5 (by decide), hF₁ 5 (by decide)]
    · rw [hF' 6 (by decide), hF₁₈ 6 (by decide) (by decide), hF₁₇ 6 (by decide), h6₁₅,
        hF₁₃ 6 (by decide) (by decide) (by decide) (by decide), hF₁₂ 6 (by decide),
        hF₁₀ 6 (by decide), h6₈, h6₆, hF₅ 6 (by decide), hF₃ 6 (by decide), hF₁ 6 (by decide)]
    · rw [hF' 7 (by decide), hF₁₈ 7 (by decide) (by decide), hF₁₇ 7 (by decide), hF₁₅ 7 (by decide) (by decide),
        hF₁₄ 7 (by decide), hF₁₃ 7 (by decide) (by decide) (by decide) (by decide), hF₁₂ 7 (by decide), h7₁₀,
        h7]

theorem verifyF_le_B (m : ℕ) (S : List ℕ) (b bM : ℕ) (hb : ∀ p ∈ S, p < 2 ^ b) (hlen : S.length < 2 ^ b)
    (hm : m < 2 ^ bM) (hbM : b ≤ bM) (r4 r7 : List Γ') (v : St) (St : Stacks)
    (h4 : St 4 = encList S ++ r4) (h7 : St 7 = encodeNatΓ' m ++ .comma :: r7) :
    verifyF.Runs v St (fun v' S' => v'.flag = (Alg.verify m S).1 ∧ S' = St)
      (((Alg.verify m S).2 + 1) * B (4 * verifyX S.length b bM + 6)) := by
  refine Frag.runs_mono (verifyF_runs m S b bM hb hlen hm hbM r4 r7 v St h4 h7) (fun _ _ h => h) ?_
  have : B (4 * verifyX S.length b bM + 6) = 64 * B (verifyX S.length b bM) := by
    rw [show 4 * verifyX S.length b bM + 6 = (3 + 1) * verifyX S.length b bM + 2 * 3 by ring, ← B_scale]
    norm_num
  rw [this]
  exact Nat.mul_le_mul_left _ (by omega)


/-! ### `scalesTM`: the scales from bit lengths -/

theorem bl_pred (a : ℕ) : bl a - 1 = Nat.log 2 a := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rw [bl_of_pos ha]; rfl

theorem bl_le_log_succ (a : ℕ) : bl a ≤ Nat.log 2 a + 1 := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rw [bl_of_pos ha]

/-- Small linear quantities are below `2 ^ m` once `8 ≤ m`. -/
theorem lin_lt_two_pow (m : ℕ) (hm : 8 ≤ m) : 8 * m + 100 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have : 8 ≤ 2 ^ k := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hk)
    rw [pow_succ]; omega

/-- `Nat.log 2` of a number below `2 ^ m` is below `2 ^ m` (for `8 ≤ m`). -/
theorem log_lt_two_pow {a m : ℕ} (hm : 8 ≤ m) (ha : a < 2 ^ m) : Nat.log 2 a < 2 ^ m := by
  have := log_le_of_lt_pow ha
  have := lin_lt_two_pow m hm
  omega

/-- Step 1a: `M := log n`, `a := log M`, `b := log a` from `n` on stack 7 (peeked),
pushed on stacks 1, 2, 3. -/
def scLogs : Frag :=
  (bitlen 7 1 2 3).seq ((predNum 1 2).seq ((bitlen 1 2 3 4).seq ((predNum 2 3).seq
    ((bitlen 2 3 4 5).seq (predNum 3 4)))))

theorem scLogs_runs (n m : ℕ) (hm8 : 8 ≤ m) (hn : n < 2 ^ m) (r7 : List Γ') (v : St) (S : Stacks)
    (h7 : S 7 = encodeNatΓ' n ++ .comma :: r7) :
    scLogs.Runs v S (fun _ S' =>
        S' 0 = S 0 ∧ S' 1 = encodeNatΓ' (Nat.log 2 n) ++ .comma :: S 1 ∧
        S' 2 = encodeNatΓ' (Nat.log 2 (Nat.log 2 n)) ++ .comma :: S 2 ∧
        S' 3 = encodeNatΓ' (Nat.log 2 (Nat.log 2 (Nat.log 2 n))) ++ .comma :: S 3 ∧
        S' 4 = S 4 ∧ S' 5 = S 5 ∧ S' 6 = S 6 ∧ S' 7 = S 7)
      (6 * B m) := by
  have hlin := lin_lt_two_pow m hm8
  have hbl : ∀ a, a < 2 ^ m → bl a < 2 ^ m := fun a ha => by
    have := bl_le_log_succ a; have := log_le_of_lt_pow ha; omega
  have hM : Nat.log 2 n < 2 ^ m := log_lt_two_pow hm8 hn
  have ha : Nat.log 2 (Nat.log 2 n) < 2 ^ m := log_lt_two_pow hm8 hM
  -- 1. bitlen 7 1 2 3
  have h1 := bitlen_le_B (x := 7) (y := 1) (s := 2) (s' := 3) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) n m hn r7 v S h7
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B m + (B m + (B m + (B m + B m)))) h1
    fun v₁ S₁ ⟨h7₁, h1₁, h2₁, h3₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 2. predNum 1 2
  have h2 := predNum_le_B' (x := 1) (s := 2) (by decide) (bl n) m (hbl n hn) _ v₁ S₁ h1₁
  rw [bl_pred] at h2
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B m + (B m + (B m + B m))) h2
    fun v₂ S₂ ⟨_, _, h1₂, h2₂, hF₂⟩ => ?_) (fun _ _ h => h) le_rfl
  -- 3. bitlen 1 2 3 4
  have h3 := bitlen_le_B (x := 1) (y := 2) (s := 3) (s' := 4) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (Nat.log 2 n) m hM _ v₂ S₂ h1₂
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B m + (B m + B m)) h3
    fun v₃ S₃ ⟨h1₃, h2₃, h3₃, h4₃, hF₃⟩ => ?_) (fun _ _ h => h) le_rfl
  -- 4. predNum 2 3
  have h4 := predNum_le_B' (x := 2) (s := 3) (by decide) (bl (Nat.log 2 n)) m (hbl _ hM) _ v₃ S₃ h2₃
  rw [bl_pred] at h4
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B m + B m) h4
    fun v₄ S₄ ⟨_, _, h2₄, h3₄, hF₄⟩ => ?_) (fun _ _ h => h) le_rfl
  -- 5. bitlen 2 3 4 5
  have h5 := bitlen_le_B (x := 2) (y := 3) (s := 4) (s' := 5) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) _ m ha _ v₄ S₄ h2₄
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B m) h5
    fun v₅ S₅ ⟨h2₅, h3₅, h4₅, h5₅, hF₅⟩ => ?_) (fun _ _ h => h) le_rfl
  -- 6. predNum 3 4
  have h6 := predNum_le_B' (x := 3) (s := 4) (by decide) (bl (Nat.log 2 (Nat.log 2 n))) m (hbl _ ha) _ v₅ S₅ h3₅
  rw [bl_pred] at h6
  refine Frag.runs_mono h6 (fun _ S₆ ⟨_, _, h3₆, h4₆, hF₆⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
  all_goals tm_fr

/-- Step 1b: `θ := 2 ^ ((6 (log (M + 1) + 1) + 4) / 5)` from `M` on stack 1 (peeked),
pushed on stack 0. -/
def scTheta : Frag :=
  (dup 1 4 5).seq ((incr 4 5).seq ((bitlen 4 5 6 0).seq ((dropNum 4).seq ((pushNum 4 6).seq
    ((mulC 4 5 6 0 2).seq ((incr 6 0).seq ((incr 6 0).seq ((incr 6 0).seq ((incr 6 0).seq
      ((pushNum 4 5).seq ((divC 6 4 5 0 1 2).seq (pow2 5 0 4 6))))))))))))

theorem scTheta_runs (M m : ℕ) (hm8 : 8 ≤ m) (hM1 : M + 1 < 2 ^ m)
    (he : (6 * (Nat.log 2 (M + 1) + 1) + 4) / 5 < m) (r1 : List Γ') (v : St) (S : Stacks)
    (h1 : S 1 = encodeNatΓ' M ++ .comma :: r1) :
    scTheta.Runs v S (fun _ S' =>
        S' 0 = encodeNatΓ' (2 ^ ((6 * (Nat.log 2 (M + 1) + 1) + 4) / 5)) ++ .comma :: S 0 ∧
        S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = S 3 ∧ S' 4 = S 4 ∧ S' 5 = S 5 ∧ S' 6 = S 6 ∧ S' 7 = S 7)
      (13 * B m) := by
  have hlin := lin_lt_two_pow m hm8
  have hM : M < 2 ^ m := by omega
  have hlM := log_le_of_lt_pow hM1
  have hbl : bl (M + 1) = Nat.log 2 (M + 1) + 1 := bl_of_pos (by omega)
  obtain ⟨L, hL⟩ : ∃ L, Nat.log 2 (M + 1) + 1 = L := ⟨_, rfl⟩
  rw [hL] at hbl he ⊢
  have hLm : L < 2 ^ m := by omega
  have h6 : 6 < 2 ^ m := by omega
  have h5 : 5 < 2 ^ m := by omega
  have h6L : 6 * L < 2 ^ m := by omega
  have h6L1 : 6 * L + 1 < 2 ^ m := by omega
  have h6L2 : 6 * L + 1 + 1 < 2 ^ m := by omega
  have h6L3 : 6 * L + 1 + 1 + 1 < 2 ^ m := by omega
  have h6L4 : 6 * L + 1 + 1 + 1 + 1 < 2 ^ m := by omega
  have hB1 := one_le_B m
  -- 1. dup 1 4 5
  have s1 := dup_le_B (x := 1) (y := 4) (s := 5) (by decide) (by decide) (by decide) M m hM r1 v S h1
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 12 * B m) s1
    fun v₁ S₁ ⟨h1₁, h4₁, h5₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 2. incr 4 5
  have s2 := incr_le_B (y := 4) (s := 5) (by decide) M m hM _ v₁ S₁ h4₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 11 * B m) s2
    fun v₂ S₂ ⟨_, _, _, h4₂, h5₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. bitlen 4 5 6 0
  have s3 := bitlen_le_B (x := 4) (y := 5) (s := 6) (s' := 0) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (M + 1) m hM1 _ v₂ S₂ h4₂
  rw [hbl] at s3
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 10 * B m) s3
    fun v₃ S₃ ⟨h4₃, h5₃, h6₃, h0₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 4. dropNum 4
  have h4₃' : S₃ 4 = encodeNatΓ' (M + 1) ++ .comma :: S 4 := by tm_fr
  have s4 := dropNum_le_B (x := 4) (M + 1) m hM1 _ v₃ S₃ h4₃'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 9 * B m) s4
    fun v₄ S₄ ⟨_, _, _, h4₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 5. pushNum 4 6
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 8 * B m) (pushNum_le_B 4 6 m h6 v₄ S₄)
    fun v₅ S₅ ⟨_, h4₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 6. mulC 4 5 6 0 2
  have h5₅ : S₅ 5 = encodeNatΓ' L ++ .comma :: S 5 := by tm_fr
  have s6 := mulC_le_B (x := 4) (y := 5) (w := 6) (s := 0) (t := 2) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 6 L m h6 hLm _ _ v₅ S₅
    h4₅ h5₅
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 7 * B m) s6
    fun v₆ S₆ ⟨h4₆, h5₆, h6₆, h0₆, h2₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 7-10. incr 6 0 four times
  have s7 := incr_le_B (y := 6) (s := 0) (by decide) (6 * L) m h6L _ v₆ S₆ h6₆
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 6 * B m) s7
    fun v₇ S₇ ⟨_, _, _, h6₇, h0₇, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
  have s8 := incr_le_B (y := 6) (s := 0) (by decide) (6 * L + 1) m h6L1 _ v₇ S₇ h6₇
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * B m) s8
    fun v₈ S₈ ⟨_, _, _, h6₈, h0₈, hF₈⟩ => ?_) (fun _ _ h => h) (by omega)
  have s9 := incr_le_B (y := 6) (s := 0) (by decide) (6 * L + 1 + 1) m h6L2 _ v₈ S₈ h6₈
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * B m) s9
    fun v₉ S₉ ⟨_, _, _, h6₉, h0₉, hF₉⟩ => ?_) (fun _ _ h => h) (by omega)
  have s10 := incr_le_B (y := 6) (s := 0) (by decide) (6 * L + 1 + 1 + 1) m h6L3 _ v₉ S₉ h6₉
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * B m) s10
    fun v₁₀ S₁₀ ⟨_, _, _, h6₁₀, h0₁₀, hF₁₀⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 11. pushNum 4 5
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B m) (pushNum_le_B 4 5 m h5 v₁₀ S₁₀)
    fun v₁₁ S₁₁ ⟨_, h4₁₁, hF₁₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 12. divC 6 4 5 0 1 2
  have h6₁₁ : S₁₁ 6 = encodeNatΓ' (6 * L + 1 + 1 + 1 + 1) ++ .comma :: S 6 := by tm_fr
  have s12 := divC_le_B (x := 6) (y := 4) (q := 5) (j := 0) (s := 1) (t := 2) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (6 * L + 1 + 1 + 1 + 1) 5 m (by norm_num) h6L4 h5 _ _ v₁₁
    S₁₁ h6₁₁ h4₁₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B m) s12
    fun v₁₂ S₁₂ ⟨h6₁₂, h4₁₂, h5₁₂, h0₁₂, h1₁₂, h2₁₂, hF₁₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 13. pow2 5 0 4 6
  have hee : (6 * L + 1 + 1 + 1 + 1) / 5 = (6 * L + 4) / 5 := by
    rw [show 6 * L + 1 + 1 + 1 + 1 = 6 * L + 4 by ring]
  rw [hee] at s12 h5₁₂
  have s13 := pow2_le_B (x := 5) (y := 0) (s := 4) (s' := 6) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) ((6 * L + 4) / 5) m he _ v₁₂ S₁₂ h5₁₂
  refine Frag.runs_mono s13 (fun _ S₁₃ ⟨h5₁₃, h0₁₃, h4₁₃, h6₁₃, hF₁₃⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
  all_goals tm_fr

/-- Step 1c: `T := 3 a` from `a` on stack 2 (peeked), pushed on stack 0. -/
def scT : Frag := (pushNum 4 3).seq ((dup 2 5 6).seq ((mulC 4 5 6 1 3).seq (moveEntry 6 0 4)))

theorem scT_runs (a m : ℕ) (hm8 : 8 ≤ m) (ha : a < 2 ^ m) (h3a : 3 * a < 2 ^ m) (r2 : List Γ') (v : St)
    (S : Stacks) (h2 : S 2 = encodeNatΓ' a ++ .comma :: r2) :
    scT.Runs v S (fun _ S' =>
        S' 0 = encodeNatΓ' (3 * a) ++ .comma :: S 0 ∧ S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = S 3 ∧
        S' 4 = S 4 ∧ S' 5 = S 5 ∧ S' 6 = S 6 ∧ S' 7 = S 7)
      (4 * B m) := by
  have hlin := lin_lt_two_pow m hm8
  have h3 : 3 < 2 ^ m := by omega
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * B m) (pushNum_le_B 4 3 m h3 v S)
    fun v₁ S₁ ⟨_, h4₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  have h2₁ : S₁ 2 = encodeNatΓ' a ++ .comma :: r2 := by tm_fr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B m)
    (dup_le_B (x := 2) (y := 5) (s := 6) (by decide) (by decide) (by decide) a m ha r2 v₁ S₁ h2₁)
    fun v₂ S₂ ⟨h2₂, h5₂, h6₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  have h4₂ : S₂ 4 = encodeNatΓ' 3 ++ .comma :: S 4 := by tm_fr
  have h5₂' : S₂ 5 = encodeNatΓ' a ++ .comma :: S 5 := by tm_fr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B m)
    (mulC_le_B (x := 4) (y := 5) (w := 6) (s := 1) (t := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 3 a m h3 ha _ _ v₂ S₂ h4₂ h5₂')
    fun v₃ S₃ ⟨h4₃, h5₃, h6₃, h1₃, h3₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  have h6₃' : S₃ 6 = encodeNatΓ' (3 * a) ++ .comma :: S 6 := by tm_fr
  refine Frag.runs_mono (moveEntry_le_B (src := 6) (dst := 0) (s := 4) (by decide) (by decide) (by decide)
    (3 * a) m h3a _ v₃ S₃ h6₃') (fun _ S₄ ⟨_, _, _, h6₄, h0₄, h4₄, hF₄⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    le_rfl
  all_goals tm_fr

/-- Step 1d: `z := C₁ a b` from `a` on stack 2 and `b` on stack 3, pushed on stack 5;
`M` (stack 1), `a`, `b` are then dropped. -/
def scZ (C₁ : ℕ) : Frag :=
  (pushNum 4 C₁).seq ((dup 2 5 6).seq ((mulC 4 5 6 1 3).seq ((dup 3 4 5).seq ((mulC 6 4 5 1 2).seq
    ((dropNum 1).seq ((dropNum 2).seq (dropNum 3)))))))

theorem scZ_runs (C₁ M a b m : ℕ) (hm8 : 8 ≤ m) (hC : C₁ < 2 ^ m) (hM : M < 2 ^ m) (ha : a < 2 ^ m)
    (hb : b < 2 ^ m) (hCa : C₁ * a < 2 ^ m) (r1 r2 r3 : List Γ') (v : St) (S : Stacks)
    (h1 : S 1 = encodeNatΓ' M ++ .comma :: r1) (h2 : S 2 = encodeNatΓ' a ++ .comma :: r2)
    (h3 : S 3 = encodeNatΓ' b ++ .comma :: r3) :
    (scZ C₁).Runs v S (fun _ S' =>
        S' 0 = S 0 ∧ S' 1 = r1 ∧ S' 2 = r2 ∧ S' 3 = r3 ∧ S' 4 = S 4 ∧
        S' 5 = encodeNatΓ' (C₁ * a * b) ++ .comma :: S 5 ∧ S' 6 = S 6 ∧ S' 7 = S 7)
      (8 * B m) := by
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 7 * B m) (pushNum_le_B 4 C₁ m hC v S)
    fun v₁ S₁ ⟨_, h4₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  have h2₁ : S₁ 2 = encodeNatΓ' a ++ .comma :: r2 := by tm_fr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 6 * B m)
    (dup_le_B (x := 2) (y := 5) (s := 6) (by decide) (by decide) (by decide) a m ha r2 v₁ S₁ h2₁)
    fun v₂ S₂ ⟨h2₂, h5₂, h6₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  have h4₂ : S₂ 4 = encodeNatΓ' C₁ ++ .comma :: S 4 := by tm_fr
  have h5₂' : S₂ 5 = encodeNatΓ' a ++ .comma :: S 5 := by tm_fr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * B m)
    (mulC_le_B (x := 4) (y := 5) (w := 6) (s := 1) (t := 3) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) C₁ a m hC ha _ _ v₂ S₂ h4₂ h5₂')
    fun v₃ S₃ ⟨h4₃, h5₃, h6₃, h1₃, h3₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  have h3₃' : S₃ 3 = encodeNatΓ' b ++ .comma :: r3 := by tm_fr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * B m)
    (dup_le_B (x := 3) (y := 4) (s := 5) (by decide) (by decide) (by decide) b m hb r3 v₃ S₃ h3₃')
    fun v₄ S₄ ⟨h3₄, h4₄, h5₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  have h6₄ : S₄ 6 = encodeNatΓ' (C₁ * a) ++ .comma :: S 6 := by tm_fr
  have h4₄' : S₄ 4 = encodeNatΓ' b ++ .comma :: S 4 := by tm_fr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * B m)
    (mulC_le_B (x := 6) (y := 4) (w := 5) (s := 1) (t := 2) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (C₁ * a) b m hCa hb _ _ v₄ S₄ h6₄
      h4₄')
    fun v₅ S₅ ⟨h6₅, h4₅, h5₅, h1₅, h2₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  have h1₅' : S₅ 1 = encodeNatΓ' M ++ .comma :: r1 := by tm_fr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B m) (dropNum_le_B (x := 1) M m hM r1 v₅ S₅ h1₅')
    fun v₆ S₆ ⟨_, _, _, h1₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
  have h2₆ : S₆ 2 = encodeNatΓ' a ++ .comma :: r2 := by tm_fr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B m) (dropNum_le_B (x := 2) a m ha r2 v₆ S₆ h2₆)
    fun v₇ S₇ ⟨_, _, _, h2₇, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
  have h3₇ : S₇ 3 = encodeNatΓ' b ++ .comma :: r3 := by tm_fr
  refine Frag.runs_mono (dropNum_le_B (x := 3) b m hb r3 v₇ S₇ h3₇)
    (fun _ S₈ ⟨_, _, _, h3₈, hF₈⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
  all_goals tm_fr

/-- Step 1e: `bz := log z + 1` from `z` on stack 5 (peeked), pushed on stack 4. -/
def scBz : Frag := (bitlen 5 4 6 1).seq ((predNum 4 6).seq (incr 4 6))

theorem scBz_runs (z m : ℕ) (hm8 : 8 ≤ m) (hz : z < 2 ^ m) (r5 : List Γ') (v : St) (S : Stacks)
    (h5 : S 5 = encodeNatΓ' z ++ .comma :: r5) :
    scBz.Runs v S (fun _ S' =>
        S' 0 = S 0 ∧ S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = S 3 ∧
        S' 4 = encodeNatΓ' (Nat.log 2 z + 1) ++ .comma :: S 4 ∧ S' 5 = S 5 ∧ S' 6 = S 6 ∧ S' 7 = S 7)
      (3 * B m) := by
  have hlin := lin_lt_two_pow m hm8
  have hbl : bl z < 2 ^ m := by have := bl_le_log_succ z; have := log_le_of_lt_pow hz; omega
  have hlz : Nat.log 2 z < 2 ^ m := log_lt_two_pow hm8 hz
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B m)
    (bitlen_le_B (x := 5) (y := 4) (s := 6) (s' := 1) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) z m hz r5 v S h5)
    fun v₁ S₁ ⟨h5₁, h4₁, h6₁, h1₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  have s2 := predNum_le_B' (x := 4) (s := 6) (by decide) (bl z) m hbl _ v₁ S₁ h4₁
  rw [bl_pred] at s2
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B m) s2
    fun v₂ S₂ ⟨_, _, h4₂, h6₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  refine Frag.runs_mono (incr_le_B (y := 4) (s := 6) (by decide) (Nat.log 2 z) m hlz _ v₂ S₂ h4₂)
    (fun _ S₃ ⟨_, _, _, h4₃, h6₃, hF₃⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
  all_goals tm_fr

/-- Division by a constant `c` (total: `a / 0 = 0` as in Lean): `pushNum` the divisor
and `divC`, or drop the dividend and push `0` when `c = 0`.  `a` on `x` is consumed,
`a / c` is pushed on `q`. -/
def divK (x y q j s t : K) (c : ℕ) : Frag :=
  if c = 0 then (dropNum x).seq (pushNum q 0) else (pushNum y c).seq (divC x y q j s t)

theorem divK_le_B {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (a c m : ℕ) (ha : a < 2 ^ m) (hc : c < 2 ^ m) (xr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) :
    (divK x y q j s t c).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = S y ∧ S' q = encodeNatΓ' (a / c) ++ .comma :: S q ∧
        S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      (2 * B m) := by
  by_cases hc0 : c = 0
  · subst hc0
    unfold divK
    rw [if_pos rfl]
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B m) (dropNum_le_B a m ha xr v S hSx)
      fun v₁ S₁ ⟨_, _, _, hx₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
    refine Frag.runs_mono (pushNum_le_B q 0 m Nat.one_le_two_pow v₁ S₁)
      (fun _ S₂ ⟨_, hq₂, hF₂⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
    · rw [hF₂ x hxq, hx₁]
    · rw [hF₂ y hyq, hF₁ y hxy.symm]
    · rw [hq₂, hF₁ q hxq.symm, Nat.div_zero]
    · rw [hF₂ j hqj.symm, hF₁ j hxj.symm]
    · rw [hF₂ s hqs.symm, hF₁ s hxs.symm]
    · rw [hF₂ t hqt.symm, hF₁ t hxt.symm]
    · intro k hkx hky hkq hkj hks hkt; rw [hF₂ k hkq, hF₁ k hkx]
  · unfold divK
    rw [if_neg hc0]
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B m) (pushNum_le_B y c m hc v S)
      fun v₁ S₁ ⟨_, hy₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
    have hx₁ : S₁ x = encodeNatΓ' a ++ .comma :: xr := by rw [hF₁ x hxy, hSx]
    refine Frag.runs_mono (divC_le_B hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst a c m
      (by omega) ha hc _ _ v₁ S₁ hx₁ hy₁) (fun _ S₂ ⟨hx₂, hy₂, hq₂, hj₂, hs₂, ht₂, hF₂⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
      le_rfl
    · exact hx₂
    · exact hy₂
    · rw [hq₂, hF₁ q hyq.symm]
    · rw [hj₂, hF₁ j hyj.symm]
    · rw [hs₂, hF₁ s hys.symm]
    · rw [ht₂, hF₁ t hyt.symm]
    · intro k hkx hky hkq hkj hks hkt; rw [hF₂ k hkx hky hkq hkj hks hkt, hF₁ k hky]

theorem Ksub_mul (K bz : ℕ) : (K - 1) * bz + K - 1 = (K - 1) * (bz + 1) := by
  rcases K with _ | K
  · simp
  · rw [Nat.add_sub_cancel, show K * bz + (K + 1) - 1 = K * bz + K by omega]; ring

/-- Step 1f: `y := 2 ^ (((K - 1) bz + K - 1) / K)` from `bz` on stack 4 (peeked), pushed on
stack 0 (the machine computes `(K - 1) (bz + 1)`, equal to the numerator). -/
def scY (K : ℕ) : Frag :=
  (dup 4 6 1).seq ((incr 6 1).seq ((pushNum 1 (K - 1)).seq ((mulC 1 6 2 3 4).seq
    ((divK 2 1 3 6 4 5 K).seq ((pow2 3 6 1 2).seq (moveEntry 6 0 1))))))

theorem scY_runs (K bz m : ℕ) (hm8 : 8 ≤ m) (hbz1 : bz + 1 < 2 ^ m) (hK : K < 2 ^ m)
    (hKb : (K - 1) * (bz + 1) < 2 ^ m) (he : ((K - 1) * bz + K - 1) / K < m) (r4 : List Γ') (v : St)
    (S : Stacks) (h4 : S 4 = encodeNatΓ' bz ++ .comma :: r4) :
    (scY K).Runs v S (fun _ S' =>
        S' 0 = encodeNatΓ' (2 ^ (((K - 1) * bz + K - 1) / K)) ++ .comma :: S 0 ∧
        S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = S 3 ∧ S' 4 = S 4 ∧ S' 5 = S 5 ∧ S' 6 = S 6 ∧ S' 7 = S 7)
      (8 * B m) := by
  have hbz : bz < 2 ^ m := by omega
  have hK1 : K - 1 < 2 ^ m := by omega
  rw [Ksub_mul] at he ⊢
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 7 * B m)
    (dup_le_B (x := 4) (y := 6) (s := 1) (by decide) (by decide) (by decide) bz m hbz r4 v S h4)
    fun v₁ S₁ ⟨h4₁, h6₁, h1₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 6 * B m) (incr_le_B (y := 6) (s := 1) (by decide) bz m hbz _ v₁ S₁ h6₁)
    fun v₂ S₂ ⟨_, _, _, h6₂, h1₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * B m) (pushNum_le_B 1 (K - 1) m hK1 v₂ S₂)
    fun v₃ S₃ ⟨_, h1₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  have h1₃' : S₃ 1 = encodeNatΓ' (K - 1) ++ .comma :: S 1 := by tm_fr
  have h6₃ : S₃ 6 = encodeNatΓ' (bz + 1) ++ .comma :: S 6 := by tm_fr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * B m)
    (mulC_le_B (x := 1) (y := 6) (w := 2) (s := 3) (t := 4) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (K - 1) (bz + 1) m hK1 hbz1 _ _ v₃ S₃
      h1₃' h6₃)
    fun v₄ S₄ ⟨h1₄, h6₄, h2₄, h3₄, h4₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  have h2₄' : S₄ 2 = encodeNatΓ' ((K - 1) * (bz + 1)) ++ .comma :: S 2 := by tm_fr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B m)
    (divK_le_B (x := 2) (y := 1) (q := 3) (j := 6) (s := 4) (t := 5) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) ((K - 1) * (bz + 1)) K m hKb hK _ v₄ S₄ h2₄')
    fun v₅ S₅ ⟨h2₅, h1₅, h3₅, h6₅, h4₅, h5₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  have h3₅' : S₅ 3 = encodeNatΓ' ((K - 1) * (bz + 1) / K) ++ .comma :: S 3 := by tm_fr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B m)
    (pow2_le_B (x := 3) (y := 6) (s := 1) (s' := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) _ m he _ v₅ S₅ h3₅')
    fun v₆ S₆ ⟨h3₆, h6₆, h1₆, h2₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
  have h6₆' : S₆ 6 = encodeNatΓ' (2 ^ ((K - 1) * (bz + 1) / K)) ++ .comma :: S 6 := by tm_fr
  have hy : 2 ^ ((K - 1) * (bz + 1) / K) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) he
  refine Frag.runs_mono (moveEntry_le_B (src := 6) (dst := 0) (s := 1) (by decide) (by decide) (by decide)
    _ m hy _ v₆ S₆ h6₆') (fun _ S₇ ⟨_, _, _, h6₇, h0₇, h1₇, hF₇⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
  all_goals tm_fr

/-- Step 1g: `z99 := 2 ^ ((99 bz + 99) / 100)` from `bz` on stack 4 (consumed), then `z`
(stack 5, consumed) and `z99` pushed on stack 0: `0 := z :: z99 :: S 0`. -/
def scZ99 : Frag :=
  (incr 4 1).seq ((pushNum 1 99).seq ((mulC 1 4 2 3 6).seq ((pushNum 1 100).seq
    ((divC 2 1 3 4 6 5).seq ((pow2 3 6 1 2).seq ((moveEntry 6 0 1).seq (moveEntry 5 0 1)))))))

theorem scZ99_runs (z bz m : ℕ) (hm8 : 8 ≤ m) (hz : z < 2 ^ m) (hbz1 : bz + 1 < 2 ^ m)
    (h99 : 99 * (bz + 1) < 2 ^ m) (he : (99 * bz + 99) / 100 < m) (r4 r5 : List Γ') (v : St)
    (S : Stacks) (h4 : S 4 = encodeNatΓ' bz ++ .comma :: r4) (h5 : S 5 = encodeNatΓ' z ++ .comma :: r5) :
    scZ99.Runs v S (fun _ S' =>
        S' 0 = encodeNatΓ' z ++ .comma :: (encodeNatΓ' (2 ^ ((99 * bz + 99) / 100)) ++ .comma :: S 0) ∧
        S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = S 3 ∧ S' 4 = r4 ∧ S' 5 = r5 ∧ S' 6 = S 6 ∧ S' 7 = S 7)
      (8 * B m) := by
  have hlin := lin_lt_two_pow m hm8
  have hbz : bz < 2 ^ m := by omega
  have h99' : 99 < 2 ^ m := by omega
  have h100 : 100 < 2 ^ m := by omega
  have hmul : 99 * bz + 99 = 99 * (bz + 1) := by ring
  rw [hmul] at he ⊢
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 7 * B m) (incr_le_B (y := 4) (s := 1) (by decide) bz m hbz r4 v S h4)
    fun v₁ S₁ ⟨_, _, _, h4₁, h1₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 6 * B m) (pushNum_le_B 1 99 m h99' v₁ S₁)
    fun v₂ S₂ ⟨_, h1₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  have h1₂' : S₂ 1 = encodeNatΓ' 99 ++ .comma :: S 1 := by tm_fr
  have h4₂ : S₂ 4 = encodeNatΓ' (bz + 1) ++ .comma :: r4 := by tm_fr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * B m)
    (mulC_le_B (x := 1) (y := 4) (w := 2) (s := 3) (t := 6) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) 99 (bz + 1) m h99' hbz1 _ _ v₂ S₂
      h1₂' h4₂)
    fun v₃ S₃ ⟨h1₃, h4₃, h2₃, h3₃, h6₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * B m) (pushNum_le_B 1 100 m h100 v₃ S₃)
    fun v₄ S₄ ⟨_, h1₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  have h2₄ : S₄ 2 = encodeNatΓ' (99 * (bz + 1)) ++ .comma :: S 2 := by tm_fr
  have h1₄' : S₄ 1 = encodeNatΓ' 100 ++ .comma :: S 1 := by tm_fr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * B m)
    (divC_le_B (x := 2) (y := 1) (q := 3) (j := 4) (s := 6) (t := 5) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (99 * (bz + 1)) 100 m (by norm_num) h99 h100 _ _ v₄ S₄ h2₄ h1₄')
    fun v₅ S₅ ⟨h2₅, h1₅, h3₅, h4₅, h6₅, h5₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  have h3₅' : S₅ 3 = encodeNatΓ' (99 * (bz + 1) / 100) ++ .comma :: S 3 := by tm_fr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B m)
    (pow2_le_B (x := 3) (y := 6) (s := 1) (s' := 2) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) _ m he _ v₅ S₅ h3₅')
    fun v₆ S₆ ⟨h3₆, h6₆, h1₆, h2₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
  have h6₆' : S₆ 6 = encodeNatΓ' (2 ^ (99 * (bz + 1) / 100)) ++ .comma :: S 6 := by tm_fr
  have hz99 : 2 ^ (99 * (bz + 1) / 100) < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) he
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B m)
    (moveEntry_le_B (src := 6) (dst := 0) (s := 1) (by decide) (by decide) (by decide) _ m hz99 _ v₆ S₆ h6₆')
    fun v₇ S₇ ⟨_, _, _, h6₇, h0₇, h1₇, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
  have h5₇ : S₇ 5 = encodeNatΓ' z ++ .comma :: r5 := by tm_fr
  refine Frag.runs_mono (moveEntry_le_B (src := 5) (dst := 0) (s := 1) (by decide) (by decide) (by decide)
    z m hz _ v₇ S₇ h5₇) (fun _ S₈ ⟨_, _, _, h5₈, h0₈, h1₈, hF₈⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
  all_goals tm_fr


theorem ninetynine_lt (b : ℕ) : 99 * (3 * b + 2) < 2 ^ (3 * b + 8) := by
  induction b with
  | zero => norm_num
  | succ b ih =>
    have : 2 ^ (3 * (b + 1) + 8) = 8 * 2 ^ (3 * b + 8) := by
      rw [show 3 * (b + 1) + 8 = 3 * b + 8 + 3 by ring, pow_add]; norm_num; ring
    rw [this]; omega

/-- The scales fragment: from `n` on stack 7 (restored) to the five scales packed on
stack 0, top first `z :: z99 :: y :: T :: θ` (T4's `step2F` entry layout); stacks 1–6
restored. -/
def scalesF (C₁ K : ℕ) : Frag :=
  scLogs.seq (scTheta.seq (scT.seq ((scZ C₁).seq (scBz.seq ((scY K).seq scZ99)))))

theorem scalesF_runs (C₁ K n b : ℕ) (hn : n < 2 ^ b) (hC : C₁ < 2 ^ b) (hK : K < 2 ^ b)
    (r7 : List Γ') (v : St) (S : Stacks) (h7 : S 7 = encodeNatΓ' n ++ .comma :: r7) :
    (scalesF C₁ K).Runs v S (fun _ S' =>
        S' 0 = encodeNatΓ' (scalesTM C₁ K n).z ++ .comma :: (encodeNatΓ' (scalesTM C₁ K n).z99 ++ .comma ::
          (encodeNatΓ' (scalesTM C₁ K n).y ++ .comma :: (encodeNatΓ' (scalesTM C₁ K n).T ++ .comma ::
            (encodeNatΓ' (scalesTM C₁ K n).θ ++ .comma :: S 0)))) ∧
        S' 1 = S 1 ∧ S' 2 = S 2 ∧ S' 3 = S 3 ∧ S' 4 = S 4 ∧ S' 5 = S 5 ∧ S' 6 = S 6 ∧ S' 7 = S 7)
      (50 * B (3 * b + 8)) := by
  -- the bit bounds at `m := 3 b + 8`
  obtain ⟨m, hm⟩ : ∃ m, 3 * b + 8 = m := ⟨_, rfl⟩
  have hm8 : 8 ≤ m := by omega
  have hlin := lin_lt_two_pow m hm8
  have hbm : 2 ^ b ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2b : 2 ^ (2 * b) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h3b : 2 ^ (3 * b) ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hnm : n < 2 ^ m := lt_of_lt_of_le hn hbm
  have hCm : C₁ < 2 ^ m := lt_of_lt_of_le hC hbm
  have hKm : K < 2 ^ m := lt_of_lt_of_le hK hbm
  obtain ⟨M, hM⟩ : ∃ M, Nat.log 2 n = M := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, Nat.log 2 M = a := ⟨_, rfl⟩
  obtain ⟨bb, hbb⟩ : ∃ bb, Nat.log 2 a = bb := ⟨_, rfl⟩
  have hMb : M ≤ b := hM ▸ log_le_of_lt_pow hn
  have haM : a ≤ M := ha ▸ log_le_of_lt_pow Nat.lt_two_pow_self
  have hba : bb ≤ a := hbb ▸ log_le_of_lt_pow Nat.lt_two_pow_self
  have hb2 : b < 2 ^ b := Nat.lt_two_pow_self
  have hMm : M < 2 ^ m := by omega
  have hM1 : M + 1 < 2 ^ m := by omega
  have ham : a < 2 ^ m := by omega
  have hbbm : bb < 2 ^ m := by omega
  have h3a : 3 * a < 2 ^ m := by omega
  have hab : a < 2 ^ b := by omega
  have hbbb : bb < 2 ^ b := by omega
  have hCa : C₁ * a < 2 ^ m := by
    calc C₁ * a < 2 ^ b * 2 ^ b := mul_lt_mul'' hC hab (Nat.zero_le _) (Nat.zero_le _)
      _ = 2 ^ (2 * b) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ m := h2b
  have hCa2 : C₁ * a < 2 ^ (2 * b) := by
    calc C₁ * a < 2 ^ b * 2 ^ b := mul_lt_mul'' hC hab (Nat.zero_le _) (Nat.zero_le _)
      _ = 2 ^ (2 * b) := by rw [← pow_add]; ring_nf
  obtain ⟨z, hz⟩ : ∃ z, C₁ * a * bb = z := ⟨_, rfl⟩
  have hz3 : z < 2 ^ (3 * b) := by
    rw [← hz]
    calc C₁ * a * bb < 2 ^ (2 * b) * 2 ^ b := mul_lt_mul'' hCa2 hbbb (Nat.zero_le _) (Nat.zero_le _)
      _ = 2 ^ (3 * b) := by rw [← pow_add]; ring_nf
  have hzm : z < 2 ^ m := lt_of_lt_of_le hz3 h3b
  have hlz : Nat.log 2 z ≤ 3 * b := log_le_of_lt_pow hz3
  obtain ⟨bz, hbz⟩ : ∃ bz, Nat.log 2 z + 1 = bz := ⟨_, rfl⟩
  have hbz1 : bz + 1 < 2 ^ m := by omega
  have hKb : (K - 1) * (bz + 1) < 2 ^ m := by
    have h1 : K - 1 < 2 ^ b := by omega
    have h2 : bz + 1 < 2 ^ (2 * b + 8) := by
      have := lin_lt_two_pow (2 * b + 8) (by omega); omega
    calc (K - 1) * (bz + 1) < 2 ^ b * 2 ^ (2 * b + 8) := mul_lt_mul'' h1 h2 (Nat.zero_le _) (Nat.zero_le _)
      _ = 2 ^ m := by rw [← pow_add, ← hm]; ring_nf
  have hey : ((K - 1) * bz + K - 1) / K < m := by
    rw [Ksub_mul]
    have : (K - 1) * (bz + 1) / K ≤ bz + 1 :=
      Nat.div_le_of_le_mul (Nat.mul_le_mul_right _ (Nat.sub_le K 1))
    omega
  have h99 : 99 * (bz + 1) < 2 ^ m := by
    have := ninetynine_lt b; rw [hm] at this
    have : 99 * (bz + 1) ≤ 99 * (3 * b + 2) := Nat.mul_le_mul_left _ (by omega)
    omega
  have he99 : (99 * bz + 99) / 100 < m := by omega
  have heθ : (6 * (Nat.log 2 (M + 1) + 1) + 4) / 5 < m := by
    have : Nat.log 2 (M + 1) ≤ b + 1 := log_le_of_lt_pow (by
      calc M + 1 ≤ b + 1 := by omega
        _ < 2 ^ (b + 1) := Nat.lt_two_pow_self)
    omega
  -- the target in explicit form
  have hgoal : ∀ S' : Stacks,
      S' 0 = encodeNatΓ' z ++ .comma :: (encodeNatΓ' (2 ^ ((99 * bz + 99) / 100)) ++ .comma ::
        (encodeNatΓ' (2 ^ (((K - 1) * bz + K - 1) / K)) ++ .comma :: (encodeNatΓ' (3 * a) ++ .comma ::
          (encodeNatΓ' (2 ^ ((6 * (Nat.log 2 (M + 1) + 1) + 4) / 5)) ++ .comma :: S 0)))) →
      S' 0 = encodeNatΓ' (scalesTM C₁ K n).z ++ .comma :: (encodeNatΓ' (scalesTM C₁ K n).z99 ++ .comma ::
        (encodeNatΓ' (scalesTM C₁ K n).y ++ .comma :: (encodeNatΓ' (scalesTM C₁ K n).T ++ .comma ::
          (encodeNatΓ' (scalesTM C₁ K n).θ ++ .comma :: S 0)))) := by
    intro S' h
    simp only [scalesTM, hM, ha, hbb, hz, hbz]
    exact h
  rw [hm]
  -- 1. scLogs
  have s1 := scLogs_runs n m hm8 hnm r7 v S h7
  rw [hM, ha, hbb] at s1
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 44 * B m) s1
    fun v₁ S₁ ⟨h0₁, h1₁, h2₁, h3₁, h4₁, h5₁, h6₁, h7₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 2. scTheta
  have s2 := scTheta_runs M m hm8 hM1 heθ _ v₁ S₁ h1₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 31 * B m) s2
    fun v₂ S₂ ⟨h0₂, h1₂, h2₂, h3₂, h4₂, h5₂, h6₂, h7₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. scT
  have h2₂' : S₂ 2 = encodeNatΓ' a ++ .comma :: S 2 := by tm_fr
  have s3 := scT_runs a m hm8 ham h3a _ v₂ S₂ h2₂'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 27 * B m) s3
    fun v₃ S₃ ⟨h0₃, h1₃, h2₃, h3₃, h4₃, h5₃, h6₃, h7₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 4. scZ
  have h1₃' : S₃ 1 = encodeNatΓ' M ++ .comma :: S 1 := by tm_fr
  have h2₃' : S₃ 2 = encodeNatΓ' a ++ .comma :: S 2 := by tm_fr
  have h3₃' : S₃ 3 = encodeNatΓ' bb ++ .comma :: S 3 := by tm_fr
  have s4 := scZ_runs C₁ M a bb m hm8 hCm hMm ham hbbm hCa _ _ _ v₃ S₃ h1₃' h2₃' h3₃'
  rw [hz] at s4
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 19 * B m) s4
    fun v₄ S₄ ⟨h0₄, h1₄, h2₄, h3₄, h4₄, h5₄, h6₄, h7₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 5. scBz
  have s5 := scBz_runs z m hm8 hzm _ v₄ S₄ h5₄
  rw [hbz] at s5
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 16 * B m) s5
    fun v₅ S₅ ⟨h0₅, h1₅, h2₅, h3₅, h4₅, h5₅, h6₅, h7₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 6. scY
  have s6 := scY_runs K bz m hm8 hbz1 hKm hKb hey _ v₅ S₅ h4₅
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 8 * B m) s6
    fun v₆ S₆ ⟨h0₆, h1₆, h2₆, h3₆, h4₆, h5₆, h6₆, h7₆⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 7. scZ99
  have h4₆' : S₆ 4 = encodeNatΓ' bz ++ .comma :: S 4 := by tm_fr
  have h5₆' : S₆ 5 = encodeNatΓ' z ++ .comma :: S 5 := by tm_fr
  have s7 := scZ99_runs z bz m hm8 hzm hbz1 h99 he99 _ _ v₆ S₆ h4₆' h5₆'
  refine Frag.runs_mono s7 (fun _ S₇ ⟨h0₇, h1₇, h2₇, h3₇, h4₇, h5₇, h6₇, h7₇⟩ =>
    ⟨hgoal S₇ ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
  all_goals tm_fr

/-! ### The input adapter: the raw `encodeNatΓ' n` (no terminator) on stack 0 -/

/-- `moveNum` on an UNTERMINATED number (the whole stack `src` is `bits l`): the pop
on the empty stack reads `none`, which `readA` treats like the terminator. -/
theorem moveNum_loop_raw {src dst : K} (hsd : src ≠ dst)
    {Λ : Type} {M : Λ → Stmt' Λ} {ι : Unit → Λ} {e : Λ} (hI : (moveNum src dst).Installed M ι e)
    {S₀ : Stacks} (l : List Bool) :
    ∀ (v : St) (S : Stacks) (dr : List Γ'), S src = bits l → S dst = dr →
      (∀ k, k ≠ src → k ≠ dst → S k = S₀ k) →
    ∃ n, n ≤ l.length + 1 ∧ ∃ v' S',
      RunsTo M n ⟨some (ι ()), v, S⟩ ⟨some e, v', S'⟩ ∧
      S' src = [] ∧ S' dst = (bits l).reverse ++ dr ∧ ∀ k, k ≠ src → k ≠ dst → S' k = S₀ k := by
  have hds := hsd.symm
  induction l with
  | nil =>
    intro v S dr hS hD hF
    refine ⟨1, by simp, { v with ra := none, da := true }, Function.update S src [],
      runsTo_succ ?_ (runsTo_zero M _), by simp, by simp [Function.update_of_ne hds, hD],
      fun k hks hkd => by simp [Function.update_of_ne hks, hF k hks hkd]⟩
    tm_step () [moveNum, moveBody, hS]
  | cons b l ih =>
    intro v S dr hS hD hF
    obtain ⟨n, hn, v', S', hr, hs', hd', hf'⟩ :=
      ih { v with ra := some b }
        (Function.update (Function.update S src (bits l)) dst (.bit b :: dr))
        (.bit b :: dr) (by simp [Function.update_of_ne hsd]) (by simp)
        (fun k hks hkd => by
          simp [Function.update_of_ne hks, Function.update_of_ne hkd, hF k hks hkd])
    refine ⟨n + 1, ?_, v', S', runsTo_succ ?_ hr, hs', ?_, hf'⟩
    · simp only [List.length_cons] at hn ⊢; omega
    · tm_step () [moveNum, moveBody, hS, hD, hsd, hds]
    · rw [hd']; simp

theorem moveNum_runs_raw {src dst : K} (hsd : src ≠ dst) (l : List Bool) (v : St) (S : Stacks)
    (hS : S src = bits l) :
    (moveNum src dst).Runs v S (fun _ S' =>
        S' src = [] ∧ S' dst = (bits l).reverse ++ S dst ∧ ∀ k, k ≠ src → k ≠ dst → S' k = S k)
      (l.length + 1) := by
  constructor
  intro Λ M ι e hI
  exact moveNum_loop_raw hsd hI (S₀ := S) l v S (S dst) hS rfl (fun _ _ _ => rfl)

/-- The input adapter: stack 0 holds the raw `encodeNatΓ' n`; the number is moved
(reversed) onto a terminator on stack 2, then back (reversed again) onto a
terminator on stack 7: stack 7 becomes `encodeNatΓ' n ++ [comma]`, stack 0 and 2
are empty. -/
def inputF : Frag :=
  (Frag.pushSym 2 .comma).seq ((moveNum 0 2).seq ((Frag.pushSym 7 .comma).seq (moveNum 2 7)))

theorem inputF_runs (n : ℕ) (v : St) :
    inputF.Runs v (Frag.initStacks 0 (encodeNatΓ' n))
      (fun _ S' => S' = Frag.initStacks 7 (encodeNatΓ' n ++ [Γ'.comma]))
      (2 * (Computability.encodeNat n).length + 4) := by
  obtain ⟨S, hS⟩ : ∃ S, Frag.initStacks 0 (encodeNatΓ' n) = S := ⟨_, rfl⟩
  have h0 : S 0 = bits (Computability.encodeNat n) := by
    rw [← hS]; simp [Frag.initStacks, encodeNatΓ'_eq]
  have hk : ∀ k, k ≠ 0 → S k = [] := by
    intro k hk; rw [← hS]; simp [Frag.initStacks, hk]
  rw [hS]
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (Computability.encodeNat n).length + 1 + 1 +
      ((Computability.encodeNat n).length + 1)) (Frag.pushSym_runs 2 Γ'.comma v S)
    fun v₁ S₁ ⟨_, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  have h0₁ : S₁ 0 = bits (Computability.encodeNat n) := by rw [hS₁, Function.update_of_ne (by decide), h0]
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1 + ((Computability.encodeNat n).length + 1))
    (moveNum_runs_raw (src := 0) (dst := 2) (by decide) _ v₁ S₁ h0₁)
    fun v₂ S₂ ⟨h0₂, h2₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (Computability.encodeNat n).length + 1)
    (Frag.pushSym_runs 7 Γ'.comma v₂ S₂) fun v₃ S₃ ⟨_, hS₃⟩ => ?_) (fun _ _ h => h) (by omega)
  have h2₃ : S₃ 2 = bits (Computability.encodeNat n).reverse ++ Γ'.comma :: [] := by
    rw [hS₃, Function.update_of_ne (by decide), h2₂, hS₁, Function.update_self, bits_reverse, hk 2 (by decide)]
  refine Frag.runs_mono (moveNum_runs (src := 2) (dst := 7) (by decide) _ [] v₃ S₃ h2₃)
    (fun _ S₄ ⟨h2₄, h7₄, hF₄⟩ => ?_) (by simp)
  have h7₃ : S₃ 7 = [Γ'.comma] := by
    rw [hS₃, Function.update_self, hF₂ 7 (by decide) (by decide), hS₁, Function.update_of_ne (by decide),
      hk 7 (by decide)]
  funext k
  fin_cases k
  · show S₄ 0 = _
    rw [hF₄ 0 (by decide) (by decide), hS₃, Function.update_of_ne (by decide), h0₂]; rfl
  · show S₄ 1 = _
    rw [hF₄ 1 (by decide) (by decide), hS₃, Function.update_of_ne (by decide), hF₂ 1 (by decide) (by decide),
      hS₁, Function.update_of_ne (by decide), hk 1 (by decide)]; rfl
  · exact h2₄
  · show S₄ 3 = _
    rw [hF₄ 3 (by decide) (by decide), hS₃, Function.update_of_ne (by decide), hF₂ 3 (by decide) (by decide),
      hS₁, Function.update_of_ne (by decide), hk 3 (by decide)]; rfl
  · show S₄ 4 = _
    rw [hF₄ 4 (by decide) (by decide), hS₃, Function.update_of_ne (by decide), hF₂ 4 (by decide) (by decide),
      hS₁, Function.update_of_ne (by decide), hk 4 (by decide)]; rfl
  · show S₄ 5 = _
    rw [hF₄ 5 (by decide) (by decide), hS₃, Function.update_of_ne (by decide), hF₂ 5 (by decide) (by decide),
      hS₁, Function.update_of_ne (by decide), hk 5 (by decide)]; rfl
  · show S₄ 6 = _
    rw [hF₄ 6 (by decide) (by decide), hS₃, Function.update_of_ne (by decide), hF₂ 6 (by decide) (by decide),
      hS₁, Function.update_of_ne (by decide), hk 6 (by decide)]; rfl
  · show S₄ 7 = _
    rw [h7₄, h7₃, bits_reverse, List.reverse_reverse, ← encodeNatΓ'_eq]; rfl

/-! ### Clearing everything (the `none` output) and the success output -/

/-- Clear all eight stacks and leave `[comma] = encodeOutput (0, [])` on stack 1. -/
def failAll : Frag :=
  (clear 0).seq ((clear 1).seq ((clear 2).seq ((clear 3).seq ((clear 4).seq ((clear 5).seq
    ((clear 6).seq ((clear 7).seq (Frag.pushSym 1 Γ'.comma))))))))

theorem failAll_runs (v : St) (S : Stacks) :
    failAll.Runs v S (fun _ S' => S' = Frag.initStacks 1 [Γ'.comma])
      ((S 0).length + (S 1).length + (S 2).length + (S 3).length + (S 4).length + (S 5).length +
        (S 6).length + (S 7).length + 9) := by
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (S 1).length + (S 2).length + (S 3).length + (S 4).length +
      (S 5).length + (S 6).length + (S 7).length + 8) (clear_runs 0 v S)
    fun v₁ S₁ ⟨_, _, _, h0₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (S 2).length + (S 3).length + (S 4).length +
      (S 5).length + (S 6).length + (S 7).length + 7) (clear_runs 1 v₁ S₁)
    fun v₂ S₂ ⟨_, _, _, h1₂, hF₂⟩ => ?_) (fun _ _ h => h) (by rw [hF₁ 1 (by decide)]; omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (S 3).length + (S 4).length +
      (S 5).length + (S 6).length + (S 7).length + 6) (clear_runs 2 v₂ S₂)
    fun v₃ S₃ ⟨_, _, _, h2₃, hF₃⟩ => ?_) (fun _ _ h => h) (by rw [hF₂ 2 (by decide), hF₁ 2 (by decide)]; omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (S 4).length +
      (S 5).length + (S 6).length + (S 7).length + 5) (clear_runs 3 v₃ S₃)
    fun v₄ S₄ ⟨_, _, _, h3₄, hF₄⟩ => ?_) (fun _ _ h => h)
    (by rw [hF₃ 3 (by decide), hF₂ 3 (by decide), hF₁ 3 (by decide)]; omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (S 5).length + (S 6).length + (S 7).length + 4) (clear_runs 4 v₄ S₄)
    fun v₅ S₅ ⟨_, _, _, h4₅, hF₅⟩ => ?_) (fun _ _ h => h)
    (by rw [hF₄ 4 (by decide), hF₃ 4 (by decide), hF₂ 4 (by decide), hF₁ 4 (by decide)]; omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (S 6).length + (S 7).length + 3) (clear_runs 5 v₅ S₅)
    fun v₆ S₆ ⟨_, _, _, h5₆, hF₆⟩ => ?_) (fun _ _ h => h)
    (by rw [hF₅ 5 (by decide), hF₄ 5 (by decide), hF₃ 5 (by decide), hF₂ 5 (by decide), hF₁ 5 (by decide)]; omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (S 7).length + 2) (clear_runs 6 v₆ S₆)
    fun v₇ S₇ ⟨_, _, _, h6₇, hF₇⟩ => ?_) (fun _ _ h => h)
    (by rw [hF₆ 6 (by decide), hF₅ 6 (by decide), hF₄ 6 (by decide), hF₃ 6 (by decide), hF₂ 6 (by decide),
      hF₁ 6 (by decide)]; omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) (clear_runs 7 v₇ S₇)
    fun v₈ S₈ ⟨_, _, _, h7₈, hF₈⟩ => ?_) (fun _ _ h => h)
    (by rw [hF₇ 7 (by decide), hF₆ 7 (by decide), hF₅ 7 (by decide), hF₄ 7 (by decide), hF₃ 7 (by decide),
      hF₂ 7 (by decide), hF₁ 7 (by decide)])
  refine Frag.runs_mono (Frag.pushSym_runs 1 Γ'.comma v₈ S₈) (fun _ S₉ ⟨_, hS₉⟩ => ?_) le_rfl
  rw [hS₉]
  have h1₈ : S₈ 1 = [] := by rw [hF₈ 1 (by decide), hF₇ 1 (by decide), hF₆ 1 (by decide), hF₅ 1 (by decide),
    hF₄ 1 (by decide), hF₃ 1 (by decide), h1₂]
  funext k
  fin_cases k
  · show Function.update S₈ 1 (Γ'.comma :: S₈ 1) 0 = _
    rw [Function.update_of_ne (by decide), hF₈ 0 (by decide), hF₇ 0 (by decide), hF₆ 0 (by decide),
      hF₅ 0 (by decide), hF₄ 0 (by decide), hF₃ 0 (by decide), hF₂ 0 (by decide), h0₁]; rfl
  · show Function.update S₈ 1 (Γ'.comma :: S₈ 1) 1 = _
    rw [Function.update_self, h1₈]; rfl
  · show Function.update S₈ 1 (Γ'.comma :: S₈ 1) 2 = _
    rw [Function.update_of_ne (by decide), hF₈ 2 (by decide), hF₇ 2 (by decide), hF₆ 2 (by decide),
      hF₅ 2 (by decide), hF₄ 2 (by decide), h2₃]; rfl
  · show Function.update S₈ 1 (Γ'.comma :: S₈ 1) 3 = _
    rw [Function.update_of_ne (by decide), hF₈ 3 (by decide), hF₇ 3 (by decide), hF₆ 3 (by decide),
      hF₅ 3 (by decide), h3₄]; rfl
  · show Function.update S₈ 1 (Γ'.comma :: S₈ 1) 4 = _
    rw [Function.update_of_ne (by decide), hF₈ 4 (by decide), hF₇ 4 (by decide), hF₆ 4 (by decide), h4₅]; rfl
  · show Function.update S₈ 1 (Γ'.comma :: S₈ 1) 5 = _
    rw [Function.update_of_ne (by decide), hF₈ 5 (by decide), hF₇ 5 (by decide), h5₆]; rfl
  · show Function.update S₈ 1 (Γ'.comma :: S₈ 1) 6 = _
    rw [Function.update_of_ne (by decide), hF₈ 6 (by decide), h6₇]; rfl
  · show Function.update S₈ 1 (Γ'.comma :: S₈ 1) 7 = _
    rw [Function.update_of_ne (by decide), h7₈]; rfl

/-- The success output: with the witness list `U` on top of stack 4 and `m` on top of
stack 7, clear the junk, then build `encodeOutput (m, U)` on stack 1 (the entries of
`U` in order, via a reversal through stack 0, then `m` on top) and clear 4, 7. -/
def outputF : Frag :=
  (clear 0).seq ((clear 1).seq ((clear 2).seq ((clear 3).seq ((clear 5).seq ((clear 6).seq
    ((revList 4 0 2).seq ((moveEntries 0 1 2).seq ((moveEntry 7 1 2).seq ((clear 7).seq (clear 4))))))))))

theorem entries_map_reverse (U : List ℕ) :
    entries ((U.reverse.map Computability.encodeNat).reverse) = entries (U.map Computability.encodeNat) := by
  rw [List.map_reverse, List.reverse_reverse]

theorem outputF_runs (m : ℕ) (U : List ℕ) (b bM : ℕ) (hU : ∀ p ∈ U, p < 2 ^ b) (hm : m < 2 ^ bM)
    (r4 r7 : List Γ') (v : St) (S : Stacks) (h4 : S 4 = encList U ++ r4)
    (h7 : S 7 = encodeNatΓ' m ++ .comma :: r7) :
    outputF.Runs v S (fun _ S' => S' = Frag.initStacks 1 (encodeOutput (m, U)))
      ((S 0).length + (S 1).length + (S 2).length + (S 3).length + (S 5).length + (S 6).length + 6 +
        (U.length + 1) * B b + (U.length * (2 * b + 6) + 3) + B bM + (r7.length + 1) + (r4.length + 1)) := by
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (S 1).length + (S 2).length + (S 3).length + (S 5).length +
      (S 6).length + 5 + (U.length + 1) * B b + (U.length * (2 * b + 6) + 3) + B bM + (r7.length + 1) +
      (r4.length + 1)) (clear_runs 0 v S)
    fun v₁ S₁ ⟨_, _, _, h0₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (S 2).length + (S 3).length + (S 5).length +
      (S 6).length + 4 + (U.length + 1) * B b + (U.length * (2 * b + 6) + 3) + B bM + (r7.length + 1) +
      (r4.length + 1)) (clear_runs 1 v₁ S₁)
    fun v₂ S₂ ⟨_, _, _, h1₂, hF₂⟩ => ?_) (fun _ _ h => h) (by rw [hF₁ 1 (by decide)]; omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (S 3).length + (S 5).length +
      (S 6).length + 3 + (U.length + 1) * B b + (U.length * (2 * b + 6) + 3) + B bM + (r7.length + 1) +
      (r4.length + 1)) (clear_runs 2 v₂ S₂)
    fun v₃ S₃ ⟨_, _, _, h2₃, hF₃⟩ => ?_) (fun _ _ h => h) (by rw [hF₂ 2 (by decide), hF₁ 2 (by decide)]; omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (S 5).length +
      (S 6).length + 2 + (U.length + 1) * B b + (U.length * (2 * b + 6) + 3) + B bM + (r7.length + 1) +
      (r4.length + 1)) (clear_runs 3 v₃ S₃)
    fun v₄ S₄ ⟨_, _, _, h3₄, hF₄⟩ => ?_) (fun _ _ h => h)
    (by rw [hF₃ 3 (by decide), hF₂ 3 (by decide), hF₁ 3 (by decide)]; omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ :=
      (S 6).length + 1 + (U.length + 1) * B b + (U.length * (2 * b + 6) + 3) + B bM + (r7.length + 1) +
      (r4.length + 1)) (clear_runs 5 v₄ S₄)
    fun v₅ S₅ ⟨_, _, _, h5₅, hF₅⟩ => ?_) (fun _ _ h => h)
    (by rw [hF₄ 5 (by decide), hF₃ 5 (by decide), hF₂ 5 (by decide), hF₁ 5 (by decide)]; omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ :=
      (U.length + 1) * B b + (U.length * (2 * b + 6) + 3) + B bM + (r7.length + 1) +
      (r4.length + 1)) (clear_runs 6 v₅ S₅)
    fun v₆ S₆ ⟨_, _, _, h6₆, hF₆⟩ => ?_) (fun _ _ h => h)
    (by rw [hF₅ 6 (by decide), hF₄ 6 (by decide), hF₃ 6 (by decide), hF₂ 6 (by decide), hF₁ 6 (by decide)]; omega)
  -- revList 4 0 2
  have h4₆ : S₆ 4 = encList U ++ r4 := by
    rw [hF₆ 4 (by decide), hF₅ 4 (by decide), hF₄ 4 (by decide), hF₃ 4 (by decide), hF₂ 4 (by decide),
      hF₁ 4 (by decide), h4]
  have h0₆ : S₆ 0 = [] := by
    rw [hF₆ 0 (by decide), hF₅ 0 (by decide), hF₄ 0 (by decide), hF₃ 0 (by decide), hF₂ 0 (by decide), h0₁]
  have h1₆ : S₆ 1 = [] := by
    rw [hF₆ 1 (by decide), hF₅ 1 (by decide), hF₄ 1 (by decide), hF₃ 1 (by decide), h1₂]
  have h2₆ : S₆ 2 = [] := by rw [hF₆ 2 (by decide), hF₅ 2 (by decide), hF₄ 2 (by decide), h2₃]
  have h3₆ : S₆ 3 = [] := by rw [hF₆ 3 (by decide), hF₅ 3 (by decide), h3₄]
  have h5₆' : S₆ 5 = [] := by rw [hF₆ 5 (by decide), h5₅]
  have h7₆ : S₆ 7 = encodeNatΓ' m ++ .comma :: r7 := by
    rw [hF₆ 7 (by decide), hF₅ 7 (by decide), hF₄ 7 (by decide), hF₃ 7 (by decide), hF₂ 7 (by decide),
      hF₁ 7 (by decide), h7]
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (U.length * (2 * b + 6) + 3) + B bM + (r7.length + 1) +
      (r4.length + 1))
    (revList_le_B (x := 4) (y := 0) (s := 2) (by decide) (by decide) (by decide) U b hU r4 v₆ S₆ h4₆)
    fun v₇ S₇ ⟨h4₇, h0₇, h2₇, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
  -- moveEntries 0 1 2
  have h0₇' : S₇ 0 = encListB (U.reverse.map Computability.encodeNat) ++ [] := by
    rw [h0₇, h0₆, encList_eq]
  have hmv := moveEntries_runs (src := 0) (dst := 1) (s := 2) (by decide) (by decide) (by decide)
    (U.reverse.map Computability.encodeNat) b
    (entry_length_le_of_lt_pow (fun p hp => hU p (List.mem_reverse.mp hp))) [] v₇ S₇ h0₇'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B bM + (r7.length + 1) + (r4.length + 1)) hmv
    fun v₈ S₈ ⟨h0₈, h1₈, h2₈, hF₈⟩ => ?_) (fun _ _ h => h)
    (by simp only [List.length_map, List.length_reverse]; omega)
  -- moveEntry 7 1 2
  have h7₈ : S₈ 7 = encodeNatΓ' m ++ .comma :: r7 := by
    rw [hF₈ 7 (by decide) (by decide) (by decide), hF₇ 7 (by decide) (by decide) (by decide), h7₆]
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (r7.length + 1) + (r4.length + 1))
    (moveEntry_le_B (src := 7) (dst := 1) (s := 2) (by decide) (by decide) (by decide) m bM hm r7 v₈ S₈ h7₈)
    fun v₉ S₉ ⟨_, _, _, h7₉, h1₉, h2₉, hF₉⟩ => ?_) (fun _ _ h => h) (by omega)
  -- clear 7, clear 4
  refine Frag.runs_mono (Frag.seq_runs (t₂ := r4.length + 1) (clear_runs 7 v₉ S₉)
    fun v₁₀ S₁₀ ⟨_, _, _, h7₁₀, hF₁₀⟩ => ?_) (fun _ _ h => h) (by rw [h7₉])
  have h4₁₀ : S₁₀ 4 = r4 := by
    rw [hF₁₀ 4 (by decide), hF₉ 4 (by decide) (by decide) (by decide), hF₈ 4 (by decide) (by decide) (by decide),
      h4₇]
  refine Frag.runs_mono (clear_runs 4 v₁₀ S₁₀) (fun _ S₁₁ ⟨_, _, _, h4₁₁, hF₁₁⟩ => ?_) (by rw [h4₁₀])
  have h1₁₁ : S₁₁ 1 = encodeNatΓ' m ++ .comma :: entries (U.map Computability.encodeNat) := by
    rw [hF₁₁ 1 (by decide), hF₁₀ 1 (by decide), h1₉, h1₈, entries_map_reverse,
      hF₇ 1 (by decide) (by decide) (by decide), h1₆, List.append_nil]
  funext k
  fin_cases k
  · show S₁₁ 0 = _
    rw [hF₁₁ 0 (by decide), hF₁₀ 0 (by decide), hF₉ 0 (by decide) (by decide) (by decide), h0₈]; rfl
  · show S₁₁ 1 = _
    rw [h1₁₁, encodeOutput_eq]; rfl
  · show S₁₁ 2 = _
    rw [hF₁₁ 2 (by decide), hF₁₀ 2 (by decide), h2₉, h2₈, h2₇, h2₆]; rfl
  · show S₁₁ 3 = _
    rw [hF₁₁ 3 (by decide), hF₁₀ 3 (by decide), hF₉ 3 (by decide) (by decide) (by decide),
      hF₈ 3 (by decide) (by decide) (by decide), hF₇ 3 (by decide) (by decide) (by decide), h3₆]; rfl
  · exact h4₁₁
  · show S₁₁ 5 = _
    rw [hF₁₁ 5 (by decide), hF₁₀ 5 (by decide), hF₉ 5 (by decide) (by decide) (by decide),
      hF₈ 5 (by decide) (by decide) (by decide), hF₇ 5 (by decide) (by decide) (by decide), h5₆']; rfl
  · show S₁₁ 6 = _
    rw [hF₁₁ 6 (by decide), hF₁₀ 6 (by decide), hF₉ 6 (by decide) (by decide) (by decide),
      hF₈ 6 (by decide) (by decide) (by decide), hF₇ 6 (by decide) (by decide) (by decide), h6₆]; rfl
  · show S₁₁ 7 = _
    rw [hF₁₁ 7 (by decide), h7₁₀]; rfl

/-! ### Route A: `Alg.search` unfolded -/

/-- The reservoir of `search`. -/
def sRes (sc : Scales) : List ℕ × ℕ := Alg.reservoir sc.z sc.z99 sc.y

/-- `Q`: the `T` largest reservoir elements. -/
def sQ (sc : Scales) : List ℕ := (sRes sc).1.drop ((sRes sc).1.length - sc.T)

/-- `L := prodL Q`. -/
def sL (sc : Scales) : ℕ := (Alg.prodL (sQ sc)).1

/-- `x := L ^ 5`. -/
def sX (sc : Scales) : ℕ := sL sc ^ 5

/-- The scan of step 3. -/
def sScan (sc : Scales) : Option (ℕ × List ℕ) × ℕ := Alg.scan (sQ sc) (sX sc) sc.z sc.θ 1 (sX sc)

/-- The step-2 charge of `search` on success. -/
def sC2 (sc : Scales) : ℕ := (sRes sc).2 + sc.T + (Alg.prodL (sQ sc)).2 + 2

theorem search_eq (sc : Scales) (n : ℕ) :
    Alg.search sc n =
      if (sRes sc).1.length < sc.T then (none, (sRes sc).2 + 1)
      else
        match (sScan sc).1 with
        | none => (none, sC2 sc + (sScan sc).2)
        | some (_, P) =>
          match (Alg.extract (sL sc) n P).1 with
          | none => (none, sC2 sc + (sScan sc).2 + (Alg.extract (sL sc) n P).2)
          | some (m, S) =>
            ((if (Alg.verify m S).1 then some (m, S) else none),
              sC2 sc + (sScan sc).2 + (Alg.extract (sL sc) n P).2 + (Alg.verify m S).2) := rfl

theorem sQ_length_le (sc : Scales) : (sQ sc).length ≤ sc.T := by
  unfold sQ; rw [List.length_drop]; omega

theorem sQ_mem {sc : Scales} {q : ℕ} (h : q ∈ sQ sc) : q ∈ (Alg.reservoir sc.z sc.z99 sc.y).1 :=
  List.mem_of_mem_drop h

theorem sL_pos (sc : Scales) : 0 < sL sc := by
  unfold sL
  rw [prodL_fst]
  exact List.prod_pos (fun q hq => by have := reservoir_mem (sQ_mem hq); omega)

theorem sC2_eq (sc : Scales) (h : sc.T ≤ (sRes sc).1.length) : sC2 sc = step2Cost sc.z sc.z99 sc.y sc.T := by
  have h' : ¬ (Alg.reservoir sc.z sc.z99 sc.y).1.length < sc.T := not_lt.mpr h
  unfold sC2 step2Cost
  rw [if_neg h', prodL_snd]
  unfold sQ sRes at *
  rw [List.length_drop]
  omega


theorem scan_some (Q : List ℕ) (x z θ : ℕ) : ∀ (k fuel k' : ℕ) (P : List ℕ),
    (Alg.scan Q x z θ k fuel).1 = some (k', P) → P = (Alg.poolAlg Q x z k').1 ∧ k' < k + fuel := by
  intro k fuel
  induction fuel generalizing k with
  | zero => intro k' P h; simp [scan_zero] at h
  | succ f ih =>
    intro k' P h
    rw [scan_succ_raw] at h
    split_ifs at h with h1 h2
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, by omega⟩
    · have := ih (k + 1) k' P h; exact ⟨this.1, by omega⟩
    · have := ih (k + 1) k' P h; exact ⟨this.1, by omega⟩

theorem extractFin_pool_length (L n : ℕ) : ∀ (P : List ℕ) (m : ℕ) (used : List ℕ) (tb : Alg.Tbl),
    (extractFin L n P m used tb).pool.length ≤ P.length
  | [], m, used, tb => by simp [extractFin_nil]
  | p :: P, m, used, tb => by
    rcases h : (Alg.dpStep L p tb).1 (1 % L) with _ | S
    · rw [extractFin_cons_none L n p P m used tb h]
      exact le_trans (extractFin_pool_length L n P _ _ _) (by simp)
    · rw [extractFin_cons_some L n p P m used tb S h]
      split_ifs
      · simp
      · exact le_trans (extractFin_pool_length L n P _ _ _) (by simp)

theorem search_of_lt (sc : Scales) (n : ℕ) (h : (sRes sc).1.length < sc.T) :
    Alg.search sc n = (none, (sRes sc).2 + 1) := by rw [search_eq, if_pos h]

theorem search_of_none (sc : Scales) (n : ℕ) (h : ¬ (sRes sc).1.length < sc.T) (hs : (sScan sc).1 = none) :
    Alg.search sc n = (none, sC2 sc + (sScan sc).2) := by rw [search_eq, if_neg h, hs]

theorem search_of_ext_none (sc : Scales) (n k' : ℕ) (P : List ℕ) (h : ¬ (sRes sc).1.length < sc.T)
    (hs : (sScan sc).1 = some (k', P)) (he : (Alg.extract (sL sc) n P).1 = none) :
    Alg.search sc n = (none, sC2 sc + (sScan sc).2 + (Alg.extract (sL sc) n P).2) := by
  rw [search_eq, if_neg h, hs]; dsimp only; rw [he]

theorem search_of_verify (sc : Scales) (n k' : ℕ) (P : List ℕ) (m : ℕ) (S : List ℕ)
    (h : ¬ (sRes sc).1.length < sc.T) (hs : (sScan sc).1 = some (k', P))
    (he : (Alg.extract (sL sc) n P).1 = some (m, S)) :
    Alg.search sc n = ((if (Alg.verify m S).1 then some (m, S) else none),
      sC2 sc + (sScan sc).2 + (Alg.extract (sL sc) n P).2 + (Alg.verify m S).2) := by
  rw [search_eq, if_neg h, hs]; dsimp only; rw [he]

/-- The step-2 charge is always part of `search`'s charge. -/
theorem step2Cost_le_search (sc : Scales) (n : ℕ) :
    step2Cost sc.z sc.z99 sc.y sc.T ≤ (Alg.search sc n).2 := by
  by_cases h : (sRes sc).1.length < sc.T
  · rw [search_of_lt sc n h]
    unfold step2Cost sRes at *
    rw [if_pos h]
  · have hc := sC2_eq sc (not_lt.mp h)
    rw [← hc]
    rcases hs : (sScan sc).1 with _ | ⟨k', P⟩
    · rw [search_of_none sc n h hs]; dsimp only; omega
    · rcases he : (Alg.extract (sL sc) n P).1 with _ | ⟨m, S⟩
      · rw [search_of_ext_none sc n k' P h hs he]; dsimp only; omega
      · rw [search_of_verify sc n k' P m S h hs he]; dsimp only; omega

/-! ### Bit and length bookkeeping for the assembly -/

/-- The bit bound of everything in steps 3–5: `x = L ^ 5 < 2 ^ (5 (T bs + 1))`, plus `n`. -/
def sb1 (T bs bn : ℕ) : ℕ := 5 * (T * bs + 1) + bs + bn + 1

/-- The `B`-argument of the assembly's budget. -/
def searchX (T P b₁ : ℕ) : ℕ := (111 * (T + 1) + 13 * (P + 2)) * b₁ + 4 * T + 200

/-- The per-tick budget of `searchF` in terms of the scales and the bit bounds `bs`
(scale-sized numbers) and `bn` (`n` and `θ`): `L < 2 ^ (T bs + 1)` and `|P| ≤ 2 ^ T`
are built in. -/
def searchPoly (sc : Scales) (bs bn : ℕ) : ℕ :=
  300 * ((2 ^ (sc.T * bs + 1)) ^ 2 * (2 ^ sc.T + 2) * B (searchX sc.T (2 ^ sc.T) (sb1 sc.T bs bn)))

theorem num_length_le (a b : ℕ) (ha : a < 2 ^ b) (r : List Γ') :
    (encodeNatΓ' a ++ .comma :: r).length ≤ b + 1 + r.length := by
  rw [encodeNatΓ'_eq]
  simp only [List.length_append, List.length_cons, bits, List.length_map]
  have := encodeNat_length_le_of_lt_pow ha
  omega

theorem num_length_le' (a b : ℕ) (ha : a < 2 ^ b) :
    (encodeNatΓ' a ++ [Γ'.comma]).length ≤ b + 1 := by
  have := num_length_le a b ha []
  simpa using this

/-- The budget inequalities of the leaves, over bare naturals: `U` is the unit
`B X₀`, `V = E₀ U ≥ U` the unit with the extraction factor, `W = (t + 1) V`. -/
theorem bud_atoms (U V c s e w t : ℕ) (hUV : U ≤ V) (hU : 8 ≤ U) (hct : c + s + e + w ≤ t) :
    ∃ W, (t + 1) * (300 * V) = 300 * W ∧ (c + 1) * U ≤ W ∧ (s + 1) * U ≤ W ∧
      (e + 1) * (25 * V) ≤ 25 * W ∧ (w + 1) * U ≤ W ∧ U ≤ W ∧ V ≤ W ∧ 8 ≤ W := by
  refine ⟨(t + 1) * V, by ring, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.mul_le_mul (by omega) hUV
  · exact Nat.mul_le_mul (by omega) hUV
  · calc (e + 1) * (25 * V) = 25 * ((e + 1) * V) := by ring
      _ ≤ 25 * ((t + 1) * V) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
  · exact Nat.mul_le_mul (by omega) hUV
  · exact le_trans hUV (Nat.le_mul_of_pos_left V (by omega))
  · exact Nat.le_mul_of_pos_left V (by omega)
  · exact le_trans hU (le_trans hUV (Nat.le_mul_of_pos_left V (by omega)))

theorem bud_pre (U V c t : ℕ) (hUV : U ≤ V) (hU : 8 ≤ U) (hct : c ≤ t) :
    U + 50 * U + (c + 1) * U + 1 ≤ (t + 1) * (300 * V) := by
  obtain ⟨W, e0, e1, -, -, -, e4, -, e5⟩ := bud_atoms U V c 0 0 0 t hUV hU (by omega)
  rw [e0]; omega

theorem bud_pre1 (U V c s t : ℕ) (hUV : U ≤ V) (hU : 8 ≤ U) (hct : c + s ≤ t) :
    U + 50 * U + (c + 1) * U + 1 + ((s + 1) * U + 1) ≤ (t + 1) * (300 * V) := by
  obtain ⟨W, e0, e1, e2, -, -, e4, -, e5⟩ := bud_atoms U V c s 0 0 t hUV hU (by omega)
  rw [e0]; omega

theorem bud_pre2 (U V c s e t : ℕ) (hUV : U ≤ V) (hU : 8 ≤ U) (hct : c + s + e ≤ t) :
    U + 50 * U + (c + 1) * U + 1 + ((s + 1) * U + 1) + ((e + 1) * (25 * V) + 1) ≤ (t + 1) * (300 * V) := by
  obtain ⟨W, e0, e1, e2, e3, -, e4, -, e5⟩ := bud_atoms U V c s e 0 t hUV hU (by omega)
  rw [e0]; omega

theorem bud_pre3 (U V c s e w t : ℕ) (hUV : U ≤ V) (hU : 8 ≤ U) (hct : c + s + e + w ≤ t) :
    U + 50 * U + (c + 1) * U + 1 + ((s + 1) * U + 1) + ((e + 1) * (25 * V) + 1) + ((w + 1) * U + 1) ≤
      (t + 1) * (300 * V) := by
  obtain ⟨W, e0, e1, e2, e3, e3', e4, -, e5⟩ := bud_atoms U V c s e w t hUV hU hct
  rw [e0]; omega

theorem bud_A (U V c : ℕ) (hUV : U ≤ V) (hU : 8 ≤ U) :
    U + 50 * U + (c + 1) * U + 1 + ((c + 1) * U + 50 * V) ≤ (c + 1) * (300 * V) := by
  obtain ⟨W, e0, e1, -, -, -, e4, e6, e5⟩ := bud_atoms U V c 0 0 0 c hUV hU (by omega)
  rw [e0]; omega

theorem bud_B (U V c s : ℕ) (hUV : U ≤ V) (hU : 8 ≤ U) :
    U + 50 * U + (c + 1) * U + 1 + ((s + 1) * U + 1) + ((c + 1) * U + 50 * V) ≤ (c + s + 1) * (300 * V) := by
  obtain ⟨W, e0, e1, e2, -, -, e4, e6, e5⟩ := bud_atoms U V c s 0 0 (c + s) hUV hU (by omega)
  rw [e0]; omega

theorem bud_C (U V c s e : ℕ) (hUV : U ≤ V) (hU : 8 ≤ U) :
    U + 50 * U + (c + 1) * U + 1 + ((s + 1) * U + 1) + ((e + 1) * (25 * V) + 1) + ((c + 1) * U + 50 * V) ≤
      (c + s + e + 1) * (300 * V) := by
  obtain ⟨W, e0, e1, e2, e3, -, e4, e6, e5⟩ := bud_atoms U V c s e 0 (c + s + e) hUV hU (by omega)
  rw [e0]; omega

theorem bud_D (U V c s e w : ℕ) (hUV : U ≤ V) (hU : 8 ≤ U) :
    U + 50 * U + (c + 1) * U + 1 + ((s + 1) * U + 1) + ((e + 1) * (25 * V) + 1) + ((w + 1) * U + 1) +
      ((c + 1) * U + 50 * V) ≤ (c + s + e + w + 1) * (300 * V) := by
  obtain ⟨W, e0, e1, e2, e3, e3', e4, e6, e5⟩ := bud_atoms U V c s e w (c + s + e + w) hUV hU le_rfl
  rw [e0]; omega


/-! ### The machine body -/

/-- The machine body: input adapter, scales, step 2 (T4), step 3 (T4), step 4 (T5b
on stacks `np = 6, nL = 3, snap = 0, acc = 5, s = 1, t = 2, nm = 7, nu = 4`), step 5,
then the output or `failAll` on every failure path. -/
def searchF (C₁ K : ℕ) : Frag :=
  inputF.seq ((scalesF C₁ K).seq (step2F.seq (Frag.ite (fun v => v.flag)
    (scanF.seq (Frag.ite (fun v => v.flag)
      ((extractF 6 3 0 5 1 2 7 4).seq (Frag.ite (fun v => v.flag)
        (verifyF.seq (Frag.ite (fun v => v.flag) outputF failAll))
        failAll))
      failAll))
    failAll)))

theorem searchF_le_B (C₁ K n bs bn : ℕ) (hbs : 2 ≤ bs)
    (hz : (scalesTM C₁ K n).z < 2 ^ bs) (hz99 : (scalesTM C₁ K n).z99 < 2 ^ bs)
    (hy : (scalesTM C₁ K n).y < 2 ^ bs) (hT : (scalesTM C₁ K n).T < 2 ^ bs)
    (hC : C₁ < 2 ^ bs) (hK : K < 2 ^ bs) (hn : n < 2 ^ bn) (hθ : (scalesTM C₁ K n).θ < 2 ^ bn) (v : St) :
    (searchF C₁ K).Runs v (Frag.initStacks 0 (encodeNatΓ' n))
      (fun _ S' => S' = Frag.initStacks 1 (encodeOutput ((Alg.search (scalesTM C₁ K n) n).1.getD (0, []))))
      (((Alg.search (scalesTM C₁ K n) n).2 + 1) * searchPoly (scalesTM C₁ K n) bs bn) := by
  obtain ⟨sc, hsc⟩ : ∃ sc, scalesTM C₁ K n = sc := ⟨_, rfl⟩
  rw [hsc] at hz hz99 hy hT hθ ⊢
  /- the units -/
  obtain ⟨b₁, hb₁⟩ : ∃ b₁, sb1 sc.T bs bn = b₁ := ⟨_, rfl⟩
  have hb₁' : b₁ = 5 * (sc.T * bs + 1) + bs + bn + 1 := by rw [← hb₁]; rfl
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, searchX sc.T (2 ^ sc.T) b₁ = X₀ := ⟨_, rfl⟩
  have hX₀' : X₀ = (111 * (sc.T + 1) + 13 * (2 ^ sc.T + 2)) * b₁ + 4 * sc.T + 200 := by rw [← hX₀]; rfl
  obtain ⟨U, hU⟩ : ∃ U, B X₀ = U := ⟨_, rfl⟩
  obtain ⟨E₀, hE₀⟩ : ∃ E₀, (2 ^ (sc.T * bs + 1)) ^ 2 * (2 ^ sc.T + 2) = E₀ := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V, E₀ * U = V := ⟨_, rfl⟩
  have hPoly : searchPoly sc bs bn = 300 * V := by
    unfold searchPoly; rw [hb₁, hX₀, hU, hE₀, hV]
  rw [hPoly]
  have hU8 : 8 ≤ U := hU ▸ le_B_of_le_linear (by omega)
  have hE1 : 1 ≤ E₀ := by rw [← hE₀]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hUV : U ≤ V := by rw [← hV]; exact Nat.le_mul_of_pos_left U hE1
  have hXU : X₀ + 2 ≤ U := by rw [← hU]; exact le_B_of_le_linear (by omega)
  have hTb : sc.T ≤ 2 ^ sc.T := Nat.lt_two_pow_self.le
  obtain ⟨A, hA⟩ : ∃ A, 111 * (sc.T + 1) + 13 * (2 ^ sc.T + 2) = A := ⟨_, rfl⟩
  rw [hA] at hX₀'
  have hA1 : 2 ^ sc.T + 1 ≤ A := by omega
  have hTA : (2 ^ sc.T + 1) * b₁ ≤ A * b₁ := Nat.mul_le_mul_right _ hA1
  have hb₁X : b₁ + 2 ≤ X₀ := by
    have := Nat.le_mul_of_pos_left b₁ (show 0 < A by omega)
    rw [hX₀']; omega
  have hbs1 : bs ≤ b₁ := by omega
  have hbn1 : bn ≤ b₁ := by omega
  have hb₁2 : 2 ≤ b₁ := by omega
  have hBb₁ : B b₁ ≤ U := hU ▸ B_mono (by omega)
  have hBbs : B bs ≤ U := hU ▸ B_mono (by omega)
  have hBbn : B bn ≤ U := hU ▸ B_mono (by omega)
  have hbsU : bs + 2 ≤ U := by omega
  have hbnU : bn + 2 ≤ U := by omega
  have hb₁U : b₁ + 2 ≤ U := by omega
  /- Route A facts -/
  obtain ⟨t, ht⟩ : ∃ t, (Alg.search sc n).2 = t := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, step2Cost sc.z sc.z99 sc.y sc.T = c := ⟨_, rfl⟩
  have hct : c ≤ t := by rw [← hc, ← ht]; exact step2Cost_le_search sc n
  have hres : ∀ p ∈ (sRes sc).1, p < 2 ^ bs := reservoir_mem_lt_pow hz
  have hlen : (sRes sc).1.length < 2 ^ bs := reservoir_length_lt_pow hz
  have hreslen : (sRes sc).1.length ≤ (sRes sc).2 := reservoir_length_le_cost _ _ _
  have hQ : ∀ q ∈ sQ sc, q < 2 ^ bs := fun q hq => hres q (sQ_mem hq)
  have hQ1 : ∀ q ∈ sQ sc, 1 ≤ q := fun q hq => by have := reservoir_mem (sQ_mem hq); omega
  have hQb₁ : ∀ q ∈ sQ sc, q < 2 ^ b₁ :=
    fun q hq => lt_of_lt_of_le (hQ q hq) (Nat.pow_le_pow_right (by norm_num) hbs1)
  have hQlen : (sQ sc).length ≤ sc.T := sQ_length_le sc
  have hL : sL sc < 2 ^ (sc.T * bs + 1) := by
    have := prodL_le_two_pow hQ
    calc sL sc ≤ 2 ^ ((sQ sc).length * bs) := this
      _ < 2 ^ (sc.T * bs + 1) := Nat.pow_lt_pow_right (by norm_num)
          (by have := Nat.mul_le_mul_right bs hQlen; omega)
  have hLpos : 0 < sL sc := sL_pos sc
  have hLb₁ : sL sc < 2 ^ b₁ := lt_of_lt_of_le hL (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hx : sX sc < 2 ^ (5 * (sc.T * bs + 1)) := pow_lt_two_pow hL (by norm_num)
  have hxb₁ : sX sc < 2 ^ b₁ := lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hx1 : 1 + sX sc < 2 ^ b₁ := by
    have : 2 ^ (5 * (sc.T * bs + 1) + 1) ≤ 2 ^ b₁ := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at this; omega
  have hzb₁ : sc.z < 2 ^ b₁ := lt_of_lt_of_le hz (Nat.pow_le_pow_right (by norm_num) hbs1)
  have hθb₁ : sc.θ < 2 ^ b₁ := lt_of_lt_of_le hθ (Nat.pow_le_pow_right (by norm_num) hbn1)
  have hnb₁ : n < 2 ^ b₁ := lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) hbn1)
  have hL1 : sL sc + 1 ≤ 2 ^ (sc.T * bs + 1) := hL
  /- the unit bounds of the pieces -/
  have hBin : 2 * (Computability.encodeNat n).length + 4 ≤ U := by
    have hq1 := encodeNat_length_le_of_lt_pow hn
    have hq2 : 2 * bn + 4 ≤ B bn := le_B_of_le_linear (by omega)
    omega
  have hA3 : 3 * b₁ ≤ A * b₁ := Nat.mul_le_mul_right _ (by omega)
  have hBsc : B (3 * (bs + bn) + 8) ≤ U := by
    rw [← hU]; apply B_mono; rw [hX₀']; omega
  have hB2 : B (15 * (sc.T + 1) * bs + 46) ≤ U := by
    rw [← hU]; apply B_mono; rw [hX₀']
    have := Nat.mul_le_mul (show 15 * (sc.T + 1) ≤ A by omega) hbs1
    omega
  have hB3 : B (48 * ((sQ sc).length + 1) * (b₁ + b₁) + 4 * (sQ sc).length + 102) ≤ U := by
    rw [← hU]; apply B_mono; rw [hX₀']
    have e1 : 48 * ((sQ sc).length + 1) * (b₁ + b₁) = (96 * ((sQ sc).length + 1)) * b₁ := by ring
    have e2 : 96 * ((sQ sc).length + 1) ≤ A := by omega
    have := Nat.mul_le_mul_right b₁ e2
    omega
  /- named pieces -/
  obtain ⟨cin, hcin⟩ : ∃ cin, 2 * (Computability.encodeNat n).length + 4 = cin := ⟨_, rfl⟩
  obtain ⟨csc, hcsc⟩ : ∃ csc, 50 * B (3 * (bs + bn) + 8) = csc := ⟨_, rfl⟩
  obtain ⟨cst, hcst⟩ : ∃ cst, (c + 1) * B (15 * (sc.T + 1) * bs + 46) = cst := ⟨_, rfl⟩
  obtain ⟨TOT, hTOT⟩ : ∃ TOT, (t + 1) * (300 * V) = TOT := ⟨_, rfl⟩
  have hcinU : cin ≤ U := hcin ▸ hBin
  have hcscU : csc ≤ 50 * U := hcsc ▸ Nat.mul_le_mul_left _ hBsc
  have hcstU : cst ≤ (c + 1) * U := hcst ▸ Nat.mul_le_mul_left _ hB2
  rw [ht, hTOT]
  /- the machine -/
  -- 1. the input adapter
  have hin := inputF_runs n v
  rw [hcin] at hin
  refine Frag.runs_mono (Frag.seq_runs (t₂ := csc + (cst + (TOT - (cin + csc + cst)))) hin
    fun v₁ S₁ hS₁ => ?_) (fun _ _ h => h) ?_
  swap
  · have := bud_pre U V c t hUV hU8 hct
    omega
  rw [hS₁]
  have hS₁ : ∀ k, k ≠ 7 → Frag.initStacks 7 (encodeNatΓ' n ++ [Γ'.comma]) k = [] := by
    intro k hk; simp [Frag.initStacks, hk]
  have hS₁7 : Frag.initStacks 7 (encodeNatΓ' n ++ [Γ'.comma]) 7 = encodeNatΓ' n ++ .comma :: [] := by
    simp [Frag.initStacks]
  -- 2. the scales
  have hsc' := scalesF_runs C₁ K n (bs + bn) (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))
    (lt_of_lt_of_le hC (Nat.pow_le_pow_right (by norm_num) (by omega)))
    (lt_of_lt_of_le hK (Nat.pow_le_pow_right (by norm_num) (by omega))) [] v₁ _ hS₁7
  rw [hsc, hcsc] at hsc'
  refine Frag.seq_runs hsc' fun v₂ S₂ ⟨h0₂, h1₂, h2₂, h3₂, h4₂, h5₂, h6₂, h7₂⟩ => ?_
  rw [hS₁ 0 (by decide)] at h0₂
  rw [hS₁ 1 (by decide)] at h1₂
  rw [hS₁ 2 (by decide)] at h2₂
  rw [hS₁ 3 (by decide)] at h3₂
  rw [hS₁ 4 (by decide)] at h4₂
  rw [hS₁ 5 (by decide)] at h5₂
  rw [hS₁ 6 (by decide)] at h6₂
  rw [hS₁7] at h7₂
  -- 3. step 2
  have hst := step2F_le_B sc.z sc.z99 sc.y sc.T sc.θ bs hbs hz hz99 hy hT [] v₂ S₂ h0₂
  rw [hc, hcst] at hst
  refine Frag.seq_runs hst fun v₃ S₃ hpost => ?_
  rcases hpost with ⟨hlt, hfl, h0₃, h1₃, h2₃, h3₃, h4₃, h5₃, h6₃, h7₃⟩ |
    ⟨hTle, hfl, h0₃, h1₃, h2₃, h3₃, h4₃, h5₃, h6₃, h7₃⟩
  · /- step 2 fails: `len < T` -/
    have hlt' : (sRes sc).1.length < sc.T := hlt
    have hsearch := search_of_lt sc n hlt'
    have hc' : c = (sRes sc).2 + 1 := by rw [← hc]; unfold step2Cost; rw [if_pos hlt]; rfl
    have ht' : t = c := by rw [← ht, hsearch, hc']
    rw [hsearch]
    simp only [Option.getD_none, encodeOutput_default]
    refine Frag.runs_mono (Frag.ite_runs_false (by rw [hfl]) (failAll_runs v₃ S₃)) (fun _ _ h => h) ?_
    -- the lengths
    rw [h0₃, h1₃, h2₃, h3₃, h4₃, h5₃, h6₃, h7₃, h1₂, h2₂, h3₂, h4₂, h5₂, h6₂, h7₂]
    have hl0 := num_length_le sc.T bs hT (encodeNatΓ' sc.θ ++ .comma :: [])
    have hl0' := num_length_le' sc.θ bn hθ
    have hl1 := num_length_le' sc.z bs hz
    have hl2 := num_length_le' (Alg.reservoir sc.z sc.z99 sc.y).1.length bs hlen
    have hl4 : (encList (Alg.reservoir sc.z sc.z99 sc.y).1).length ≤ (c + 1) * U := by
      have hE := encList_length_le_of_lt_pow hres
      have h2 : (sRes sc).1.length * (bs + 1) + 1 ≤ (c + 1) * (bs + 2) := by
        have h1 : (sRes sc).1.length ≤ c := by rw [hc']; exact le_trans hreslen (by omega)
        have h3 := Nat.mul_le_mul h1 (show bs + 1 ≤ bs + 2 by omega)
        have h4 : (c + 1) * (bs + 2) = c * (bs + 2) + (bs + 2) := by ring
        omega
      have h3 : (c + 1) * (bs + 2) ≤ (c + 1) * U := Nat.mul_le_mul_left _ hbsU
      unfold sRes at hE h2
      omega
    have hl7 := num_length_le' n bn hn
    have hbud := bud_A U V c hUV hU8
    rw [ht'] at hTOT
    simp only [List.length_nil, List.length_append, List.length_cons] at hl0 hl0' hl1 hl2 hl7 ⊢
    omega
  · /- step 2 succeeds -/
    have hTle' : sc.T ≤ (sRes sc).1.length := hTle
    have hnlt : ¬ (sRes sc).1.length < sc.T := not_lt.mpr hTle'
    have hc2 : sC2 sc = c := by rw [← hc]; exact sC2_eq sc hTle'
    have hTc : sc.T ≤ c := by rw [← hc]; unfold step2Cost; rw [if_neg (not_lt.mpr hTle)]; omega
    have hxdef : (Alg.prodL ((Alg.reservoir sc.z sc.z99 sc.y).1.drop
        ((Alg.reservoir sc.z sc.z99 sc.y).1.length - sc.T))).1 ^ 5 = sX sc := rfl
    have hLdef : (Alg.prodL ((Alg.reservoir sc.z sc.z99 sc.y).1.drop
        ((Alg.reservoir sc.z sc.z99 sc.y).1.length - sc.T))).1 = sL sc := rfl
    have hQdef : (Alg.reservoir sc.z sc.z99 sc.y).1.drop
        ((Alg.reservoir sc.z sc.z99 sc.y).1.length - sc.T) = sQ sc := rfl
    rw [hxdef] at h0₃ h1₃
    rw [hLdef, h3₂] at h3₃
    rw [hQdef, h4₂] at h4₃
    rw [h1₂] at h1₃
    rw [h2₂] at h2₃
    rw [h5₂] at h5₃
    rw [h6₂] at h6₃
    rw [h7₂] at h7₃
    obtain ⟨s, hs⟩ : ∃ s, (sScan sc).2 = s := ⟨_, rfl⟩
    have hcs : c + s ≤ t := by
      rcases hsome : (sScan sc).1 with _ | ⟨k', P⟩
      · rw [← ht, search_of_none sc n hnlt hsome]; dsimp only; omega
      · rcases hext : (Alg.extract (sL sc) n P).1 with _ | ⟨m', U'⟩
        · rw [← ht, search_of_ext_none sc n k' P hnlt hsome hext]; dsimp only; omega
        · rw [← ht, search_of_verify sc n k' P m' U' hnlt hsome hext]; dsimp only; omega
    obtain ⟨csn, hcsn⟩ : ∃ csn,
      (s + 1) * B (48 * ((sQ sc).length + 1) * (b₁ + b₁) + 4 * (sQ sc).length + 102) = csn := ⟨_, rfl⟩
    have hcsnU : csn ≤ (s + 1) * U := hcsn ▸ Nat.mul_le_mul_left _ hB3
    have hpre1 := bud_pre1 U V c s t hUV hU8 hcs
    -- ite 1, the true branch
    refine Frag.runs_mono (Frag.ite_runs_true (t := TOT - (cin + csc + cst) - 1) (by rw [hfl]) ?_)
      (fun _ _ h => h) (by omega)
    -- 4. step 3
    have hscan := scanF_le_B (sQ sc) (sX sc) sc.z sc.θ 1 (sX sc) b₁ b₁ hQb₁ hQ1 hxb₁ hzb₁ hθb₁ hx1 [] [] [] []
      v₃ S₃ h0₃ h1₃ h2₃ h4₃
    rw [show Alg.scan (sQ sc) (sX sc) sc.z sc.θ 1 (sX sc) = sScan sc from rfl, hs, hcsn] at hscan
    refine Frag.runs_mono (Frag.seq_runs (t₂ := TOT - (cin + csc + cst) - 1 - csn) hscan
      fun v₄ S₄ ⟨h0₄, h1₄, h3₄, h4₄, h5₄, h7₄, hdisj⟩ => ?_) (fun _ _ h => h) (by omega)
    rw [h0₃] at h0₄
    rw [h3₃] at h3₄
    rw [h4₃] at h4₄
    rw [h5₃] at h5₄
    rw [h7₃] at h7₄
    rcases hdisj with ⟨k', P, hsome, hfl₄, h2₄, h6₄⟩ | ⟨hnone, hfl₄, h2₄, h6₄⟩
    · /- step 3 succeeds -/
      rw [h6₃] at h6₄
      obtain ⟨hPdef, hk'⟩ := scan_some (sQ sc) (sX sc) sc.z sc.θ 1 (sX sc) k' P hsome
      have hP : ∀ p ∈ P, p < 2 ^ b₁ := fun p hp => lt_of_le_of_lt (poolAlg_mem (hPdef ▸ hp)).1 hxb₁
      have hPlen : P.length ≤ 2 ^ sc.T := by
        rw [hPdef]
        exact le_trans (poolAlg_length_le_two_pow _ _ _ _) (Nat.pow_le_pow_right (by norm_num) hQlen)
      have hk'b : k' < 2 ^ b₁ := by omega
      obtain ⟨e, he⟩ : ∃ e, (Alg.extract (sL sc) n P).2 = e := ⟨_, rfl⟩
      obtain ⟨bM, hbM⟩ : ∃ bM, b₁ * (P.length + 1) + 1 = bM := ⟨_, rfl⟩
      have hbMX : bM + 2 ≤ X₀ := by
        have h1 : b₁ * (P.length + 1) ≤ b₁ * (2 ^ sc.T + 1) := Nat.mul_le_mul_left _ (by omega)
        have h2 : b₁ * (2 ^ sc.T + 1) = (2 ^ sc.T + 1) * b₁ := by ring
        rw [hX₀']
        omega
      have hbMU : bM + 2 ≤ U := le_trans hbMX (le_trans (Nat.le_add_right _ 2) hXU)
      have hb₁M : b₁ ≤ bM := by
        rw [← hbM]; have := Nat.le_mul_of_pos_right b₁ (show 0 < P.length + 1 by omega); omega
      have hBM : B bM ≤ U := hU ▸ B_mono (by omega)
      have hE : (sL sc + 1) ^ 2 * (P.length + 2) ≤ E₀ := by
        rw [← hE₀]; exact Nat.mul_le_mul (Nat.pow_le_pow_left hL1 2) (by omega)
      have hE' : P.length + 2 ≤ E₀ :=
        le_trans (Nat.le_mul_of_pos_left _ (by positivity)) hE
      have hB4 : B (exX P.length b₁) ≤ U := by
        rw [← hU]; apply B_mono; unfold exX; rw [hX₀']
        have e1 : 3 * P.length * b₁ + 5 * b₁ = (3 * P.length + 5) * b₁ := by ring
        have := Nat.mul_le_mul_right b₁ (show 3 * P.length + 5 ≤ A by omega)
        omega
      have hexY : 25 * exY (sL sc) P.length (exX P.length b₁) ≤ 25 * V := by
        unfold exY; rw [← hV]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hE hB4)
      obtain ⟨cex, hcex⟩ : ∃ cex, (e + 1) * (25 * exY (sL sc) P.length (exX P.length b₁)) = cex := ⟨_, rfl⟩
      have hcexV : cex ≤ (e + 1) * (25 * V) := hcex ▸ Nat.mul_le_mul_left _ hexY
      have hcse : c + s + e ≤ t := by
        rcases hext : (Alg.extract (sL sc) n P).1 with _ | ⟨m', U'⟩
        · rw [← ht, search_of_ext_none sc n k' P hnlt hsome hext]; dsimp only; omega
        · rw [← ht, search_of_verify sc n k' P m' U' hnlt hsome hext]; dsimp only; omega
      have hpre2 := bud_pre2 U V c s e t hUV hU8 hcse
      -- the product bounds for the clearing costs
      have hPV : P.length * (b₁ + 1) + 1 ≤ V := by
        have h1 : (P.length + 2) * (b₁ + 2) ≤ E₀ * U := Nat.mul_le_mul hE' hb₁U
        have h2 : (P.length + 2) * (b₁ + 2) = P.length * (b₁ + 1) + P.length + 2 * b₁ + 4 := by ring
        omega
      have hLPV : sL sc * (P.length * (b₁ + 1) + 1) + 1 ≤ V := by
        have h1 : (sL sc + 1) * ((P.length + 2) * (b₁ + 2)) ≤ (sL sc + 1) ^ 2 * (P.length + 2) * U := by
          calc (sL sc + 1) * ((P.length + 2) * (b₁ + 2))
              ≤ (sL sc + 1) ^ 2 * ((P.length + 2) * U) :=
                Nat.mul_le_mul (Nat.le_self_pow (by norm_num) _) (Nat.mul_le_mul_left _ hb₁U)
            _ = (sL sc + 1) ^ 2 * (P.length + 2) * U := by ring
        have h2 : (sL sc + 1) ^ 2 * (P.length + 2) * U ≤ E₀ * U := Nat.mul_le_mul_right _ hE
        have h3 : (P.length + 2) * (b₁ + 2) = P.length * (b₁ + 1) + P.length + 2 * b₁ + 4 := by ring
        have h4 : (sL sc + 1) * ((P.length + 2) * (b₁ + 2)) =
            sL sc * ((P.length + 2) * (b₁ + 2)) + (P.length + 2) * (b₁ + 2) := by ring
        have h5 : sL sc * (P.length * (b₁ + 1) + 1) ≤ sL sc * ((P.length + 2) * (b₁ + 2)) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      have hQc : (encList (sQ sc)).length ≤ (c + 1) * U := by
        have hq1 := encList_length_le_of_lt_pow hQ
        have hq2 := Nat.mul_le_mul_right (bs + 1) hQlen
        have h1 : sc.T * (bs + 1) + 1 ≤ (c + 1) * (bs + 2) := by
          have h3 := Nat.mul_le_mul hTc (show bs + 1 ≤ bs + 2 by omega)
          have h4 : (c + 1) * (bs + 2) = c * (bs + 2) + (bs + 2) := by ring
          omega
        have h2 : (c + 1) * (bs + 2) ≤ (c + 1) * U := Nat.mul_le_mul_left _ hbsU
        omega
      -- ite 2, the true branch
      refine Frag.runs_mono (Frag.ite_runs_true (t := TOT - (cin + csc + cst) - 1 - csn - 1) (by rw [hfl₄]) ?_)
        (fun _ _ h => h) (by omega)
      -- 5. step 4
      have hSa : S₄ 5 = [] := h5₄
      have hSp : S₄ 6 = encList P ++ [] := h6₄
      have hSL : S₄ 3 = encodeNatΓ' (sL sc) ++ .comma :: [] := h3₄
      have hSn : S₄ 7 = encodeNatΓ' n ++ .comma :: [] := h7₄
      have hext := extractF_le_B (np := 6) (nL := 3) (snap := 0) (acc := 5) (s := 1) (t := 2) (nm := 7) (nu := 4)
        (by decide) (sL sc) n b₁ hLpos hLb₁ hnb₁ P hP [] [] [] v₄ S₄ hSp hSL hSa hSn
      rw [he, hcex] at hext
      refine Frag.runs_mono (Frag.seq_runs (t₂ := TOT - (cin + csc + cst) - 1 - csn - 1 - cex) hext
        fun v₅ S₅ ⟨hfl₅, h6₅, h7₅, h4₅, h5₅, hsome₅, h3₅, h0₅, h1₅, h2₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
      rw [h3₄] at h3₅
      rw [h0₄] at h0₅
      rw [h1₄] at h1₅
      rw [h2₄] at h2₅
      rw [h4₄] at h4₅ hsome₅
      obtain ⟨hfm, hftbl, hfused, hfusedb, hfpoolb⟩ := extractFin_bounded (sL sc) n b₁ bM hLpos P hP 1 []
        Alg.emptyTbl 0 1 (tblBounded_emptyTbl _ _ _) (by norm_num)
        (by rw [← hbM, Nat.zero_add, Nat.mul_add, Nat.mul_one]; omega) (by simp)
      have hfpool_len := extractFin_pool_length (sL sc) n P 1 [] Alg.emptyTbl
      simp only [List.length_nil, Nat.zero_add] at hfused
      rw [Nat.zero_add] at hftbl
      -- lengths shared by the three leaves
      have hl0 := num_length_le (sX sc) b₁ hxb₁ (encodeNatΓ' sc.θ ++ .comma :: [])
      have hl0' := num_length_le' sc.θ bn hθ
      have hl1 := num_length_le' sc.z bs hz
      have hl2 := num_length_le' k' b₁ hk'b
      have hl3 := num_length_le' (sL sc) b₁ hLb₁
      have hl5 : (encTblAsc (sL sc) (extractFin (sL sc) n P 1 [] Alg.emptyTbl).tbl ++ [Γ'.blank]).length ≤ V := by
        have := encTblAsc_length_le hftbl
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hl6 : (encList (extractFin (sL sc) n P 1 [] Alg.emptyTbl).pool ++ []).length ≤ V := by
        have := encList_length_le_of_lt_pow hfpoolb
        have := Nat.mul_le_mul_right (b₁ + 1) hfpool_len
        simp only [List.append_nil]
        omega
      have hlQ : (encList (sQ sc) ++ []).length ≤ (c + 1) * U := by simpa using hQc
      have hl7n := num_length_le' n bn hn
      rcases hext1 : (Alg.extract (sL sc) n P).1 with _ | ⟨m', U'⟩
      · /- step 4 fails -/
        have hfl₅' : v₅.flag = false := by rw [hfl₅, hext1]; rfl
        have hsearch := search_of_ext_none sc n k' P hnlt hsome hext1
        have ht' : t = c + s + e := by rw [← ht, hsearch]; dsimp only; omega
        rw [hsearch]
        simp only [Option.getD_none, encodeOutput_default]
        refine Frag.runs_mono (Frag.ite_runs_false (by rw [hfl₅']) (failAll_runs v₅ S₅)) (fun _ _ h => h) ?_
        rw [h0₅, h1₅, h2₅, h3₅, h4₅, h5₅, h6₅, h7₅]
        have hl4 : (encList (extractFin (sL sc) n P 1 [] Alg.emptyTbl).used ++ (encList (sQ sc) ++ [])).length ≤
            V + (c + 1) * U := by
          have := encList_length_le_of_lt_pow hfusedb
          have := Nat.mul_le_mul_right (b₁ + 1) hfused
          simp only [List.length_append] at hlQ ⊢
          omega
        have hl7 := num_length_le _ bM hfm (encodeNatΓ' n ++ .comma :: [])
        have hbud := bud_C U V c s e hUV hU8
        rw [ht'] at hTOT
        simp only [List.length_nil, List.length_append, List.length_cons] at hl0 hl0' hl1 hl2 hl3 hl7 hl7n hl4 hl5 hl6 ⊢
        omega
      · /- step 4 succeeds -/
        obtain ⟨h7₅', h4₅'⟩ := hsome₅ m' U' hext1
        have hfl₅' : v₅.flag = true := by rw [hfl₅, hext1]; rfl
        have hm'U := extractGo_some (sL sc) n P 1 [] Alg.emptyTbl m' U' hext1
        have hm' : m' < 2 ^ bM := hm'U.1 ▸ hfm
        have hU' : ∀ p ∈ U', p < 2 ^ b₁ := hm'U.2 ▸ hfusedb
        have hU'len : U'.length ≤ P.length := hm'U.2 ▸ hfused
        have hTb₁ : sc.T < b₁ := by
          have : sc.T ≤ sc.T * bs := Nat.le_mul_of_pos_right _ (by omega)
          omega
        have hU'lt : U'.length < 2 ^ b₁ :=
          lt_of_le_of_lt (hU'len.trans hPlen) (Nat.pow_lt_pow_right (by norm_num) hTb₁)
        obtain ⟨w, hw⟩ : ∃ w, (Alg.verify m' U').2 = w := ⟨_, rfl⟩
        have hcsew : t = c + s + e + w := by
          rw [← ht, search_of_verify sc n k' P m' U' hnlt hsome hext1]; dsimp only; omega
        have hpre3 := bud_pre3 U V c s e w t hUV hU8 (by omega)
        have hB5 : B (4 * verifyX U'.length b₁ bM + 6) ≤ U := by
          rw [← hU]; apply B_mono
          have e1 : 4 * verifyX U'.length b₁ bM + 6 = (8 * (U'.length + 1) + 12) * b₁ + 4 * bM + 38 := by
            unfold verifyX; ring
          have e2 : (8 * (U'.length + 1) + 12) * b₁ ≤ (8 * (2 ^ sc.T + 1) + 12) * b₁ :=
            Nat.mul_le_mul_right _ (by have := hU'len.trans hPlen; omega)
          have e3 : bM ≤ b₁ * (2 ^ sc.T + 1) + 1 := by
            rw [← hbM]; have := Nat.mul_le_mul_left b₁ (show P.length + 1 ≤ 2 ^ sc.T + 1 by omega); omega
          have e4 : (8 * (2 ^ sc.T + 1) + 12) * b₁ + 4 * (b₁ * (2 ^ sc.T + 1) + 1) + 38 =
              (12 * 2 ^ sc.T + 24) * b₁ + 42 := by ring
          have e5 : (12 * 2 ^ sc.T + 24) * b₁ ≤ A * b₁ := Nat.mul_le_mul_right _ (by omega)
          rw [e1, hX₀']
          omega
        obtain ⟨cv, hcv⟩ : ∃ cv, (w + 1) * B (4 * verifyX U'.length b₁ bM + 6) = cv := ⟨_, rfl⟩
        have hcvU : cv ≤ (w + 1) * U := hcv ▸ Nat.mul_le_mul_left _ hB5
        -- ite 3, the true branch
        refine Frag.runs_mono (Frag.ite_runs_true (t := TOT - (cin + csc + cst) - 1 - csn - 1 - cex - 1)
          (by rw [hfl₅']) ?_) (fun _ _ h => h) (by omega)
        -- 6. step 5
        have h4v : S₅ 4 = encList U' ++ (encList (sQ sc) ++ []) := h4₅'
        have h7v : S₅ 7 = encodeNatΓ' m' ++ .comma :: (encodeNatΓ' n ++ .comma :: []) := h7₅'
        have hver := verifyF_le_B m' U' b₁ bM hU' hU'lt hm' hb₁M _ _ v₅ S₅ h4v h7v
        rw [hw, hcv] at hver
        refine Frag.runs_mono (Frag.seq_runs (t₂ := TOT - (cin + csc + cst) - 1 - csn - 1 - cex - 1 - cv) hver
          fun v₆ S₆ ⟨hfl₆, hS₆⟩ => ?_) (fun _ _ h => h) (by omega)
        rw [hS₆]
        have hl4 : (encList U' ++ (encList (sQ sc) ++ [])).length ≤ V + (c + 1) * U := by
          have := encList_length_le_of_lt_pow hU'
          have := Nat.mul_le_mul_right (b₁ + 1) hU'len
          simp only [List.length_append] at hlQ ⊢
          omega
        have hl7 := num_length_le m' bM hm' (encodeNatΓ' n ++ .comma :: [])
        have hsearch := search_of_verify sc n k' P m' U' hnlt hsome hext1
        rw [hcsew] at hTOT
        have hbud := bud_D U V c s e w hUV hU8
        cases hv : (Alg.verify m' U').1
        · /- step 5 rejects -/
          rw [hv] at hsearch
          simp only [Bool.false_eq_true, if_false] at hsearch
          rw [hsearch]
          simp only [Option.getD_none, encodeOutput_default]
          refine Frag.runs_mono (Frag.ite_runs_false (by rw [hfl₆, hv]) (failAll_runs v₆ S₅)) (fun _ _ h => h) ?_
          rw [h0₅, h1₅, h2₅, h3₅, h4v, h5₅, h6₅, h7v]
          simp only [List.length_nil, List.length_append, List.length_cons] at hl0 hl0' hl1 hl2 hl3 hl7 hl7n hl4 hl5 hl6 ⊢
          omega
        · /- step 5 accepts: the output -/
          rw [hv] at hsearch
          simp only [if_true] at hsearch
          rw [hsearch]
          simp only [Option.getD_some]
          have hout := outputF_runs m' U' b₁ bM hU' hm' _ _ v₆ S₅ h4v h7v
          refine Frag.runs_mono (Frag.ite_runs_true (by rw [hfl₆, hv]) hout) (fun _ _ h => h) ?_
          rw [h0₅, h1₅, h2₅, h3₅, h5₅, h6₅]
          have ho1 : (U'.length + 1) * B b₁ ≤ V := by
            have h1 : (U'.length + 1) * B b₁ ≤ (P.length + 2) * U := Nat.mul_le_mul (by omega) hBb₁
            have h2 : (P.length + 2) * U ≤ E₀ * U := Nat.mul_le_mul_right _ hE'
            omega
          have ho2 : U'.length * (2 * b₁ + 6) + 3 ≤ 3 * V := by
            have h1 : (P.length + 2) * (b₁ + 2) ≤ E₀ * U := Nat.mul_le_mul hE' hb₁U
            have h2 : U'.length * (2 * b₁ + 6) ≤ P.length * (2 * b₁ + 6) := Nat.mul_le_mul_right _ hU'len
            have h3 : 3 * ((P.length + 2) * (b₁ + 2)) = P.length * (2 * b₁ + 6) + P.length * (b₁ + 0) +
                6 * b₁ + 12 := by ring
            omega
          simp only [List.length_nil, List.length_append, List.length_cons] at hl0 hl0' hl1 hl2 hl3 hl7n hl5 hl6 hlQ ⊢
          omega
    · /- step 3 fails -/
      rw [h6₃] at h6₄
      have hsearch := search_of_none sc n hnlt hnone
      have ht' : t = c + s := by rw [← ht, hsearch]; dsimp only; omega
      rw [hsearch]
      simp only [Option.getD_none, encodeOutput_default]
      refine Frag.runs_mono (Frag.ite_runs_false (by rw [hfl₄]) (failAll_runs v₄ S₄)) (fun _ _ h => h) ?_
      rw [h0₄, h1₄, h2₄, h3₄, h4₄, h5₄, h6₄, h7₄]
      have hl0 := num_length_le (sX sc) b₁ hxb₁ (encodeNatΓ' sc.θ ++ .comma :: [])
      have hl0' := num_length_le' sc.θ bn hθ
      have hl1 := num_length_le' sc.z bs hz
      have hl2 := num_length_le' (1 + sX sc) b₁ hx1
      have hl3 := num_length_le' (sL sc) b₁ hLb₁
      have hl4 : (encList (sQ sc) ++ []).length ≤ (c + 1) * U := by
        have hq1 := encList_length_le_of_lt_pow hQ
        have hq2 := Nat.mul_le_mul_right (bs + 1) hQlen
        have h1 : sc.T * (bs + 1) + 1 ≤ (c + 1) * (bs + 2) := by
          have h3 := Nat.mul_le_mul hTc (show bs + 1 ≤ bs + 2 by omega)
          have h4 : (c + 1) * (bs + 2) = c * (bs + 2) + (bs + 2) := by ring
          omega
        have h2 : (c + 1) * (bs + 2) ≤ (c + 1) * U := Nat.mul_le_mul_left _ hbsU
        simp only [List.append_nil]
        omega
      have hl7 := num_length_le' n bn hn
      have hbud := bud_B U V c s hUV hU8
      rw [ht'] at hTOT
      simp only [List.length_nil, List.length_append, List.length_cons] at hl0 hl0' hl1 hl2 hl3 hl7 hl4 ⊢
      omega


/-! ### The unconditional bound: a function of `n` alone -/

/-- A bit bound of the scale-sized numbers valid for every `n`. -/
def sbs (C₁ K n : ℕ) : ℕ :=
  Nat.log 2 ((scalesTM C₁ K n).z + (scalesTM C₁ K n).z99 + (scalesTM C₁ K n).y + (scalesTM C₁ K n).T +
    C₁ + K) + 2

/-- A bit bound of `n` and `θ` valid for every `n`. -/
def sbn (C₁ K n : ℕ) : ℕ := Nat.log 2 (n + (scalesTM C₁ K n).θ) + 1

/-- The step bound of `searchF C₁ K` on input `n`, valid for every `n`. -/
def searchBound (C₁ K n : ℕ) : ℕ :=
  ((Alg.search (scalesTM C₁ K n) n).2 + 1) * searchPoly (scalesTM C₁ K n) (sbs C₁ K n) (sbn C₁ K n)

theorem lt_two_pow_log_succ_of_le {a s : ℕ} (h : a ≤ s) : a < 2 ^ (Nat.log 2 s + 1) :=
  lt_of_le_of_lt h (Nat.lt_pow_succ_log_self (by norm_num) s)

/-- **The machine body computes `search` on every input**: from the raw
`encodeNatΓ' n` on stack 0 to exactly `encodeOutput ((Alg.search (scalesTM C₁ K n) n).1.getD (0, []))`
on stack 1 with every other stack empty, within `searchBound C₁ K n` steps. -/
theorem searchF_runs (C₁ K n : ℕ) (v : St) :
    (searchF C₁ K).Runs v (Frag.initStacks 0 (encodeNatΓ' n))
      (fun _ S' => S' = Frag.initStacks 1 (encodeOutput ((Alg.search (scalesTM C₁ K n) n).1.getD (0, []))))
      (searchBound C₁ K n) := by
  unfold searchBound
  have hbs : 2 ≤ sbs C₁ K n := by unfold sbs; omega
  have h2 : ∀ a, a ≤ (scalesTM C₁ K n).z + (scalesTM C₁ K n).z99 + (scalesTM C₁ K n).y +
      (scalesTM C₁ K n).T + C₁ + K → a < 2 ^ sbs C₁ K n := by
    intro a ha
    unfold sbs
    exact lt_of_lt_of_le (lt_two_pow_log_succ_of_le ha) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h3 : ∀ a, a ≤ n + (scalesTM C₁ K n).θ → a < 2 ^ sbn C₁ K n := fun a ha =>
    lt_two_pow_log_succ_of_le ha
  exact searchF_le_B C₁ K n (sbs C₁ K n) (sbn C₁ K n) hbs (h2 _ (by omega)) (h2 _ (by omega)) (h2 _ (by omega))
    (h2 _ (by omega)) (h2 _ (by omega)) (h2 _ (by omega)) (h3 _ (by omega)) (h3 _ (by omega)) v

end Carmichael.TM
