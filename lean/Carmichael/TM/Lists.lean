import Carmichael.TM.Prims
import Carmichael.TM.Sub

/-!
# Route T list fragments

A list of numbers on a stack is the sequence of its entries, each a
terminated number (`bits l ++ [Γ'.comma]`, LSB on top), ended by a `Γ'.bra`:
`[a₁, …, aₖ]` is `encList [a₁, …, aₖ] = num a₁ ++ … ++ num aₖ ++ [bra]`,
head on top.  At the bit-list level (`encListB`) the entries are arbitrary
bit lists; the ℕ-level statements instantiate `L := l.map encodeNat`.

**Open lists.**  A list under construction is `pushSym k .bra` followed by
its entries pushed one at a time (each a terminated number, e.g. by `dup`,
`add`, `pushNum`): after pushing `a₁, …, aₖ` in that order the stack holds
`encList [aₖ, …, a₁] ++ rest` — the elements are CONSED on top, so the list
comes out in reverse construction order (`revList` restores the order).

Fragments (operand stacks first, scratch stacks last; every scratch stack
is restored, and need not be empty):

* `peekBra x`: `flag := (top of x = bra)`, nothing else changes.
* `popTop k`: pop one symbol.
* `forEntries x body`: run `body` once per entry of the list on `x`, `body`
  consuming the top entry each time; stops at `bra` (left on `x`).
* `moveEntry src dst s`: move the top number of `src` onto `dst`, orientation
  preserved (two reversals through `s`).
* `moveEntries src dst s`: move every entry of the list on `src` onto `dst`
  (entries intact, order reversed, no `bra` pushed), consuming `src`'s `bra`.
* `revList x y s`: `y := encList l.reverse ++ S y`, `x`'s list consumed.
* `appendList x y z s`: `y := encList (l₁ ++ l₂) ++ yr` from `l₁` on `x`
  (consumed) and `l₂` on `y`.
* `copyList x y s z`: `y := encList l ++ S y`, `x` restored.
* `listLen x y s z`: push `encodeNatΓ' l.length` (canonical) on `y`, `x` restored.
* `dropN x c s`: with `n` on `c` (consumed), `x := encList (l.drop n) ++ xr`.
* `memList x y s t z`: `flag := decide (a ∈ l)` for `a` on `y`, `l` on `x`,
  both restored.

Step bounds are stated with a uniform entry-size bound `m`
(`∀ l ∈ L, l.length ≤ m`) as `|L| * (c₁ * m + c₂) + c₃`, and at the ℕ level
with `∀ a ∈ l, a < 2 ^ b` as `(l.length + 1) * B b`.
-/

namespace Carmichael.TM

open Turing Turing.TM2 Turing.TM2.Stmt Computability

/-! ### The list encoding -/

/-- The entries of a list of bit lists: each entry's bits (LSB first)
followed by a `comma`. -/
def entries (L : List (List Bool)) : List Γ' := L.flatMap (fun l => bits l ++ [.comma])

@[simp] theorem entries_nil : entries [] = [] := rfl

@[simp] theorem entries_cons (l : List Bool) (L : List (List Bool)) :
    entries (l :: L) = bits l ++ .comma :: entries L := by
  simp [entries]

@[simp] theorem entries_append (L₁ L₂ : List (List Bool)) :
    entries (L₁ ++ L₂) = entries L₁ ++ entries L₂ := by
  simp [entries]

theorem entries_length (L : List (List Bool)) :
    (entries L).length = (L.map fun l => l.length + 1).sum := by
  induction L with
  | nil => rfl
  | cons l L ih => simp [ih]; omega

theorem entries_length_le {L : List (List Bool)} {m : ℕ} (hm : ∀ l ∈ L, l.length ≤ m) :
    (entries L).length ≤ L.length * (m + 1) := by
  induction L with
  | nil => simp
  | cons l L ih =>
    have h1 := hm l (List.mem_cons_self ..)
    have h2 := ih (fun l' hl' => hm l' (List.mem_cons_of_mem _ hl'))
    simp only [entries_cons, List.length_append, bits_length, List.length_cons, List.length_cons]
    rw [Nat.succ_mul]; omega

/-- A list of bit lists on a stack: the entries, then `bra`. -/
def encListB (L : List (List Bool)) : List Γ' := entries L ++ [.bra]

theorem encListB_nil : encListB [] = [.bra] := rfl

theorem encListB_cons (l : List Bool) (L : List (List Bool)) :
    encListB (l :: L) = bits l ++ .comma :: encListB L := by
  simp [encListB]

theorem encListB_eq_entries_append (L : List (List Bool)) (r : List Γ') :
    encListB L ++ r = entries L ++ .bra :: r := by
  simp [encListB]

theorem encListB_length_le {L : List (List Bool)} {m : ℕ} (hm : ∀ l ∈ L, l.length ≤ m) :
    (encListB L).length ≤ L.length * (m + 1) + 1 := by
  have := entries_length_le hm
  simp only [encListB, List.length_append, List.length_singleton]; omega

/-- A list of numbers on a stack: each `encodeNatΓ' a` followed by `comma`,
then `bra`. -/
def encList (l : List ℕ) : List Γ' := l.flatMap (fun a => encodeNatΓ' a ++ [.comma]) ++ [.bra]

theorem encList_eq (l : List ℕ) : encList l = encListB (l.map Computability.encodeNat) := by
  simp [encList, encListB, entries, List.flatMap_map, encodeNatΓ'_eq]

@[simp] theorem encList_nil : encList [] = [.bra] := rfl

theorem encList_cons (a : ℕ) (l : List ℕ) :
    encList (a :: l) = encodeNatΓ' a ++ .comma :: encList l := by
  simp [encList]

theorem encList_length_le (l : List ℕ) :
    (encList l).length ≤ (l.map fun a => Nat.log 2 a + 2).sum + 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have := encodeNatΓ'_length_le a
    simp only [encList_cons, List.length_append, List.length_cons, List.map_cons, List.sum_cons]
    omega

/-- Entry-size bound from a value bound. -/
theorem entry_length_le_of_lt_pow {l : List ℕ} {b : ℕ} (h : ∀ a ∈ l, a < 2 ^ b) :
    ∀ e ∈ l.map Computability.encodeNat, e.length ≤ b := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  exact encodeNat_length_le_of_lt_pow (h a ha)

theorem encList_length_le_of_lt_pow {l : List ℕ} {b : ℕ} (h : ∀ a ∈ l, a < 2 ^ b) :
    (encList l).length ≤ l.length * (b + 1) + 1 := by
  rw [encList_eq]
  have := encListB_length_le (entry_length_le_of_lt_pow h)
  simpa using this

/-- The head of a list segment is `bra` iff the list is empty. -/
theorem head?_encListB_append (L : List (List Bool)) (r : List Γ') :
    (encListB L ++ r).head? = some .bra ↔ L = [] := by
  cases L with
  | nil => simp [encListB]
  | cons l L => cases l <;> simp [encListB_cons]

theorem flag_encListB_drop (L : List (List Bool)) (i : ℕ) (r : List Γ') :
    decide ((encListB (L.drop i) ++ r).head? = some Γ'.bra) = decide (L.length ≤ i) := by
  rw [decide_eq_decide, head?_encListB_append, List.drop_eq_nil_iff]

theorem take_succ_of_drop_eq_cons {α : Type*} {L : List α} {i : ℕ} {l : α} {L' : List α}
    (h : L.drop i = l :: L') : L.take (i + 1) = L.take i ++ [l] := by
  rw [List.take_add_one, ← List.head?_drop, h]; rfl

theorem mem_of_drop_eq_cons {α : Type*} {L : List α} {i : ℕ} {l : α} {L' : List α}
    (h : L.drop i = l :: L') : l ∈ L :=
  List.drop_subset i L (by rw [h]; exact List.mem_cons_self ..)

theorem log_le_of_lt_pow {n b : ℕ} (h : n < 2 ^ b) : Nat.log 2 n ≤ b := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact (Nat.log_lt_of_lt_pow hn.ne' h).le

/-! ### Peeking at the top symbol, popping one symbol -/

/-- Peek-handler: `flag := (the symbol is bra)`. -/
def readBra (v : St) (o : Option Γ') : St := { v with flag := decide (o = some Γ'.bra) }

/-- `flag := (top of x = bra)`; nothing else changes. -/
def peekBra (x : K) : Frag := Frag.straight (peek x readBra)

theorem peekBra_runs (x : K) (v : St) (S : Stacks) :
    (peekBra x).Runs v S
      (fun v' S' => v' = { v with flag := decide ((S x).head? = some Γ'.bra) } ∧ S' = S) 1 := by
  constructor
  intro Λ M ι e hI
  refine ⟨1, le_rfl, _, S, runsTo_succ ?_ (runsTo_zero M _), rfl, rfl⟩
  tm_step () [peekBra, Frag.straight, readBra]

/-- Pop one symbol from `k`. -/
def popTop (k : K) : Frag := Frag.straight (pop k (fun v _ => v))

theorem popTop_runs (k : K) (v : St) (S : Stacks) :
    (popTop k).Runs v S (fun v' S' => v' = v ∧ S' = Function.update S k (S k).tail) 1 := by
  constructor
  intro Λ M ι e hI
  refine ⟨1, le_rfl, v, _, runsTo_succ ?_ (runsTo_zero M _), rfl, rfl⟩
  tm_step () [popTop, Frag.straight]

/-! ### The entry loop -/

/-- Run `body` once per entry of the list on `x`: `body` must consume the top
entry of `x` (leaving the rest of the list); the loop stops when the top of
`x` is `bra` (which is left in place).  `flag` is the loop control. -/
def forEntries (x : K) (body : Frag) : Frag :=
  (peekBra x).seq (Frag.loop (fun v => !v.flag) (body.seq (peekBra x)))

/-- Loop invariant of `forEntries`: `i` entries processed, `P i` holds, the
rest of the list is on `x`, and `flag` says whether the list is exhausted. -/
def ForInv (x : K) (L : List (List Bool)) (xr : List Γ') (P : ℕ → Stacks → Prop)
    (i : ℕ) (w : St) (T : Stacks) : Prop :=
  i ≤ L.length ∧ P i T ∧ T x = encListB (L.drop i) ++ xr ∧ w.flag = decide (L.length ≤ i)

/-- The entry-loop rule.  `P i S` is an invariant on the stacks after `i`
entries have been processed (it may not mention the state); the body rule
gets the top entry `l` explicitly and must restore the list form on `x`. -/
theorem forEntries_runs {x : K} {body : Frag} (L : List (List Bool)) (xr : List Γ')
    (P : ℕ → Stacks → Prop) (t : ℕ) (v : St) (S : Stacks)
    (hS : S x = encListB L ++ xr) (h0 : P 0 S)
    (hb : ∀ (i : ℕ) (l : List Bool) (L' : List (List Bool)), L.drop i = l :: L' →
      ∀ (v : St) (S : Stacks), P i S → S x = bits l ++ .comma :: (encListB L' ++ xr) →
      body.Runs v S (fun _ S' => P (i + 1) S' ∧ S' x = encListB L' ++ xr) t) :
    (forEntries x body).Runs v S
      (fun v' S' => v'.flag = true ∧ P L.length S' ∧ S' x = .bra :: xr)
      (L.length * (t + 2) + 2) := by
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L.length * (t + 2) + 1) (peekBra_runs x v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₁, hS₁]
  have hloop := Frag.loop_runs (c := fun v => !v.flag) (B := body.seq (peekBra x))
    (ForInv x L xr P) L.length (t + 1)
    (v := { v with flag := decide ((S x).head? = some Γ'.bra) }) (S := S)
    ⟨Nat.zero_le _, h0, by simpa using hS,
      by simp only [hS]; exact flag_encListB_drop L 0 xr⟩
    (fun i hi w T ⟨_, _, _, hfl⟩ => by simp [hfl]; omega)
    (fun w T ⟨_, _, _, hfl⟩ => by simp [hfl])
    (fun i hi w T ⟨_, hP, hT, _⟩ => by
      have hdrop := List.drop_eq_getElem_cons hi
      have hT' : T x = bits L[i] ++ .comma :: (encListB (L.drop (i + 1)) ++ xr) := by
        rw [hT, hdrop, encListB_cons]; simp
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 1)
        (hb i L[i] (L.drop (i + 1)) hdrop w T hP hT') fun v₂ S₂ ⟨hP₂, hS₂⟩ => ?_)
        (fun _ _ h => h) le_rfl
      refine Frag.runs_mono (peekBra_runs x v₂ S₂) (fun v₃ S₃ ⟨hv₃, hS₃⟩ => ?_) le_rfl
      rw [hv₃, hS₃]
      exact ⟨by omega, hP₂, hS₂, by simp only [hS₂]; exact flag_encListB_drop L (i + 1) xr⟩)
  refine Frag.runs_mono hloop (fun v' S' ⟨⟨_, hP, hx, _⟩, hc⟩ => ⟨?_, hP, ?_⟩) (by ring_nf; omega)
  · simpa using hc
  · rw [hx, List.drop_length]; rfl

/-! ### Moving entries -/

/-- Move the top number of `src` onto `dst`, orientation preserved (reverse
onto `s`, then reverse back onto `dst`); `s` restored. -/
def moveEntry (src dst s : K) : Frag :=
  (Frag.pushSym s .comma).seq ((moveNum src s).seq ((Frag.pushSym dst .comma).seq (moveNum s dst)))

theorem moveEntry_runs {src dst s : K} (hsd : src ≠ dst) (hss : src ≠ s) (hds : dst ≠ s)
    (l : List Bool) (sr : List Γ') (v : St) (S : Stacks) (hS : S src = bits l ++ .comma :: sr) :
    (moveEntry src dst s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' src = sr ∧ S' dst = bits l ++ .comma :: S dst ∧ S' s = S s ∧
        ∀ k, k ≠ src → k ≠ dst → k ≠ s → S' k = S k)
      (2 * l.length + 4) := by
  have hds' := hsd.symm
  have hss' := hss.symm
  have hsd' := hds.symm
  -- stage 1: push comma on s
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * l.length + 3) (Frag.pushSym_runs s .comma v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₁; rw [hv₁]
  -- stage 2: moveNum src s
  have h2 := moveNum_runs' hss l sr v (Function.update S s (.comma :: S s))
    (by simp [Function.update_of_ne hss, hS])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length + 2) h2
    fun v₂ S₂ ⟨hfl₂, hcmp₂, hcar₂, hsrc₂, hs₂, hf₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: push comma on dst
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length + 1) (Frag.pushSym_runs dst .comma v₂ S₂)
    fun v₃ S₃ ⟨hv₃, hS₃⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₃; rw [hv₃]
  -- stage 4: moveNum s dst
  have hs₃ : Function.update S₂ dst (.comma :: S₂ dst) s = bits l.reverse ++ .comma :: S s := by
    simp [Function.update_of_ne hsd', hs₂]
  have h4 := moveNum_runs' hsd' l.reverse (S s) v₂ _ hs₃
  refine Frag.runs_mono h4 (fun v₄ S₄ ⟨hfl₄, hcmp₄, hcar₄, hs₄, hdst₄, hf₄⟩ =>
    ⟨hfl₄.trans hfl₂, hcmp₄.trans hcmp₂, hcar₄.trans hcar₂, ?_, ?_, hs₄, ?_⟩) (by simp)
  · rw [hf₄ src hss hsd]; simp [Function.update_of_ne hsd, hsrc₂]
  · rw [hdst₄]; simp [hf₂ dst hds' hds, Function.update_of_ne hds]
  · intro k hks hkd hkss
    rw [hf₄ k hkss hkd]; simp [Function.update_of_ne hkd, hf₂ k hks hkss, Function.update_of_ne hkss]

/-- Move every entry of the list on `src` onto `dst` (each entry intact, the
order reversed, no `bra` pushed on `dst`), consuming `src`'s `bra`. -/
def moveEntries (src dst s : K) : Frag :=
  (forEntries src (moveEntry src dst s)).seq (popTop src)

theorem moveEntries_runs {src dst s : K} (hsd : src ≠ dst) (hss : src ≠ s) (hds : dst ≠ s)
    (L : List (List Bool)) (m : ℕ) (hm : ∀ l ∈ L, l.length ≤ m) (sr : List Γ')
    (v : St) (S : Stacks) (hS : S src = encListB L ++ sr) :
    (moveEntries src dst s).Runs v S (fun _ S' =>
        S' src = sr ∧ S' dst = entries L.reverse ++ S dst ∧ S' s = S s ∧
        ∀ k, k ≠ src → k ≠ dst → k ≠ s → S' k = S k)
      (L.length * (2 * m + 6) + 3) := by
  have hloop := forEntries_runs (body := moveEntry src dst s) L sr
    (fun i T => T dst = entries (L.take i).reverse ++ S dst ∧ T s = S s ∧
      ∀ k, k ≠ src → k ≠ dst → k ≠ s → T k = S k)
    (2 * m + 4) v S hS ⟨by simp, rfl, fun _ _ _ _ => rfl⟩
    (fun i l L' hdrop w T ⟨hd, hs, hF⟩ hT => by
      have hl := hm l (mem_of_drop_eq_cons hdrop)
      refine Frag.runs_mono (moveEntry_runs hsd hss hds l _ w T hT)
        (fun _ T' ⟨_, _, _, hsrc', hdst', hs', hF'⟩ => ⟨⟨?_, hs'.trans hs, ?_⟩, hsrc'⟩) (by omega)
      · rw [hdst', hd, take_succ_of_drop_eq_cons hdrop]; simp
      · intro k hks hkd hkss; rw [hF' k hks hkd hkss, hF k hks hkd hkss])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) hloop
    fun v₁ S₁ ⟨_, ⟨hd₁, hs₁, hF₁⟩, hsrc₁⟩ => ?_) (fun _ _ h => h) (by ring_nf; omega)
  refine Frag.runs_mono (popTop_runs src v₁ S₁) (fun v₂ S₂ ⟨_, hS₂⟩ => ?_) le_rfl
  subst hS₂
  refine ⟨by simp [hsrc₁], ?_, ?_, ?_⟩
  · rw [Function.update_of_ne hds', hd₁, List.take_length]
  · rw [Function.update_of_ne hss', hs₁]
  · intro k hks hkd hkss; rw [Function.update_of_ne hks, hF₁ k hks hkd hkss]
where
  hds' : dst ≠ src := hsd.symm
  hss' : s ≠ src := hss.symm

/-! ### Reversal and append -/

/-- `y := encList l.reverse ++ S y`; the list on `x` is consumed; `s` scratch. -/
def revList (x y s : K) : Frag := (Frag.pushSym y .bra).seq (moveEntries x y s)

theorem revList_runs {x y s : K} (hxy : x ≠ y) (hxs : x ≠ s) (hys : y ≠ s)
    (L : List (List Bool)) (m : ℕ) (hm : ∀ l ∈ L, l.length ≤ m) (xr : List Γ')
    (v : St) (S : Stacks) (hS : S x = encListB L ++ xr) :
    (revList x y s).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = encListB L.reverse ++ S y ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → S' k = S k)
      (L.length * (2 * m + 6) + 4) := by
  have hyx := hxy.symm
  have hsy := hys.symm
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L.length * (2 * m + 6) + 3) (Frag.pushSym_runs y .bra v S)
    fun v₁ S₁ ⟨_, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₁
  have h2 := moveEntries_runs hxy hxs hys L m hm xr v₁ (Function.update S y (.bra :: S y))
    (by simp [Function.update_of_ne hxy, hS])
  refine Frag.runs_mono h2 (fun _ S₂ ⟨hx₂, hy₂, hs₂, hF₂⟩ => ⟨hx₂, ?_, ?_, ?_⟩) le_rfl
  · rw [hy₂]; simp [encListB_eq_entries_append]
  · rw [hs₂]; simp [Function.update_of_ne hsy]
  · intro k hkx hky hks; rw [hF₂ k hkx hky hks]; simp [Function.update_of_ne hky]

/-- `y := encList (l₁ ++ l₂) ++ yr` for `l₁` on `x` (consumed) and `l₂` on
`y`; `z` (reversal) and `s` scratch. -/
def appendList (x y z s : K) : Frag := (revList x z s).seq (moveEntries z y s)

theorem appendList_runs {x y z s : K} (hxy : x ≠ y) (hxz : x ≠ z) (hxs : x ≠ s) (hyz : y ≠ z)
    (hys : y ≠ s) (hzs : z ≠ s) (L₁ L₂ : List (List Bool)) (m : ℕ) (hm : ∀ l ∈ L₁, l.length ≤ m)
    (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encListB L₁ ++ xr) (hSy : S y = encListB L₂ ++ yr) :
    (appendList x y z s).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = encListB (L₁ ++ L₂) ++ yr ∧ S' z = S z ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → k ≠ s → S' k = S k)
      (L₁.length * (4 * m + 12) + 7) := by
  have hzy := hyz.symm
  have h1 := revList_runs hxz hxs hzs L₁ m hm xr v S hSx
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L₁.length * (2 * m + 6) + 3) h1
    fun v₁ S₁ ⟨hx₁, hz₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h) (by ring_nf; omega)
  have hm' : ∀ l ∈ L₁.reverse, l.length ≤ m := fun l hl => hm l (List.mem_reverse.mp hl)
  have h2 := moveEntries_runs hzy hzs hys L₁.reverse m hm' (S z) v₁ S₁ hz₁
  refine Frag.runs_mono h2 (fun _ S₂ ⟨hz₂, hy₂, hs₂, hF₂⟩ => ⟨?_, ?_, hz₂, hs₂.trans hs₁, ?_⟩)
    (by simp)
  · rw [hF₂ x hxz hxy hxs, hx₁]
  · rw [hy₂, hF₁ y hxy.symm hyz hys, hSy, List.reverse_reverse, encListB, encListB, entries_append]
    simp
  · intro k hkx hky hkz hks; rw [hF₂ k hkz hky hks, hF₁ k hkx hkz hks]

/-! ### Copy and length -/

/-- `y := encList l ++ S y` with `x` restored: reverse `x` onto `z`, then move
the entries back onto `x`, copying each onto `y` as it arrives; `s`, `z` scratch. -/
def copyList (x y s z : K) : Frag :=
  (revList x z s).seq ((Frag.pushSym x .bra).seq ((Frag.pushSym y .bra).seq
    ((forEntries z ((moveEntry z x s).seq (dup x y s))).seq (popTop z))))

theorem copyList_runs {x y s z : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxz : x ≠ z) (hys : y ≠ s)
    (hyz : y ≠ z) (hsz : s ≠ z) (L : List (List Bool)) (m : ℕ) (hm : ∀ l ∈ L, l.length ≤ m)
    (xr : List Γ') (v : St) (S : Stacks) (hS : S x = encListB L ++ xr) :
    (copyList x y s z).Runs v S (fun _ S' =>
        S' x = S x ∧ S' y = encListB L ++ S y ∧ S' s = S s ∧ S' z = S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ z → S' k = S k)
      (L.length * (6 * m + 17) + 9) := by
  have hyx := hxy.symm
  have hsx := hxs.symm
  have hzx := hxz.symm
  have hsy := hys.symm
  have hzy := hyz.symm
  have hzs := hsz.symm
  have hm' : ∀ l ∈ L.reverse, l.length ≤ m := fun l hl => hm l (List.mem_reverse.mp hl)
  -- stage 1: revList x z s
  have h1 := revList_runs hxz hxs hzs L m hm xr v S hS
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L.length * (4 * m + 11) + 5) h1
    fun v₁ S₁ ⟨hx₁, hz₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h) (by ring_nf; omega)
  -- stage 2: push bra on x
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L.length * (4 * m + 11) + 4)
    (Frag.pushSym_runs x .bra v₁ S₁) fun v₂ S₂ ⟨_, hS₂⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₂
  -- stage 3: push bra on y
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L.length * (4 * m + 11) + 3)
    (Frag.pushSym_runs y .bra v₂ _) fun v₃ S₃ ⟨_, hS₃⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₃
  -- stage 4: the entry loop over z
  have hz₃ : Function.update (Function.update S₁ x (.bra :: S₁ x)) y
      (.bra :: Function.update S₁ x (.bra :: S₁ x) y) z = encListB L.reverse ++ S z := by
    simp [Function.update_of_ne hzy, Function.update_of_ne hzx, hz₁]
  have hloop := forEntries_runs (body := (moveEntry z x s).seq (dup x y s)) L.reverse (S z)
    (fun i T => T x = entries (L.reverse.take i).reverse ++ .bra :: xr ∧
      T y = entries (L.reverse.take i).reverse ++ .bra :: S y ∧ T s = S s ∧
      ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ z → T k = S k)
    (4 * m + 9) v₃ _ hz₃
    ⟨by simp [Function.update_of_ne hxy, hx₁],
      by simp [Function.update_of_ne hyx, hF₁ y hyx hyz hys],
      by simp [Function.update_of_ne hsy, Function.update_of_ne hsx, hs₁],
      fun k hkx hky hks hkz => by
        simp [Function.update_of_ne hky, Function.update_of_ne hkx, hF₁ k hkx hkz hks]⟩
    (fun i l L' hdrop w T ⟨hTx, hTy, hTs, hTF⟩ hTz => by
      have hl := hm' l (mem_of_drop_eq_cons hdrop)
      have hstep := take_succ_of_drop_eq_cons hdrop
      have h4a := moveEntry_runs hzx hzs hxs l _ w T hTz
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * m + 5) h4a
        fun w₁ T₁ ⟨_, _, _, hz', hx', hs', hF'⟩ => ?_) (fun _ _ h => h) (by omega)
      have h4b := dup_runs hxy hxs hys l _ w₁ T₁ hx'
      refine Frag.runs_mono h4b (fun _ T₂ ⟨hx'', hy'', hs'', hF''⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩)
        (by omega)
      · rw [hx'', hx', hTx, hstep]; simp
      · rw [hy'', hF' y hyz hyx hys, hTy, hstep]; simp
      · rw [hs'', hs', hTs]
      · intro k hkx hky hks hkz
        rw [hF'' k hkx hky hks, hF' k hkz hkx hks, hTF k hkx hky hks hkz]
      · rw [hF'' z hzx hzy hzs, hz'])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) hloop
    fun v₄ S₄ ⟨_, ⟨hx₄, hy₄, hs₄, hF₄⟩, hz₄⟩ => ?_) (fun _ _ h => h)
    (by simp only [List.length_reverse]; ring_nf; omega)
  -- stage 5: pop z's bra
  refine Frag.runs_mono (popTop_runs z v₄ S₄) (fun _ S₅ ⟨_, hS₅⟩ => ?_) le_rfl
  subst hS₅
  rw [List.take_length, List.reverse_reverse] at hx₄ hy₄
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne hxz, hx₄, hS, encListB_eq_entries_append]
  · rw [Function.update_of_ne hyz, hy₄, encListB_eq_entries_append]
  · rw [Function.update_of_ne hsz, hs₄]
  · simp [hz₄]
  · intro k hkx hky hks hkz; rw [Function.update_of_ne hkz, hF₄ k hkx hky hks hkz]

/-- Push the number of entries of the list on `x` (canonical) on `y`, `x`
restored: reverse onto `z`, move back counting with `incr`; `s`, `z` scratch. -/
def listLen (x y s z : K) : Frag :=
  (pushNum y 0).seq ((revList x z s).seq ((Frag.pushSym x .bra).seq
    ((forEntries z ((moveEntry z x s).seq (incr y s))).seq (popTop z))))

theorem listLen_runs {x y s z : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxz : x ≠ z) (hys : y ≠ s)
    (hyz : y ≠ z) (hsz : s ≠ z) (L : List (List Bool)) (m : ℕ) (hm : ∀ l ∈ L, l.length ≤ m)
    (xr : List Γ') (v : St) (S : Stacks) (hS : S x = encListB L ++ xr) :
    (listLen x y s z).Runs v S (fun _ S' =>
        S' x = S x ∧ S' y = encodeNatΓ' L.length ++ .comma :: S y ∧ S' s = S s ∧ S' z = S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ z → S' k = S k)
      (L.length * (4 * m + 2 * Nat.log 2 L.length + 17) + 10) := by
  have hyx := hxy.symm
  have hsx := hxs.symm
  have hzx := hxz.symm
  have hsy := hys.symm
  have hzy := hyz.symm
  have hzs := hsz.symm
  have hm' : ∀ l ∈ L.reverse, l.length ≤ m := fun l hl => hm l (List.mem_reverse.mp hl)
  -- stage 1: push 0 on y
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L.length * (4 * m + 2 * Nat.log 2 L.length + 17) + 8)
    (pushNum_runs y 0 v S) fun v₁ S₁ ⟨_, hy₁, hf₁⟩ => ?_) (fun _ _ h => h)
    (by rw [Nat.log_zero_right]; omega)
  -- stage 2: revList x z s
  have h2 := revList_runs hxz hxs hzs L m hm xr v₁ S₁ (by rw [hf₁ x hxy, hS])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L.length * (2 * m + 2 * Nat.log 2 L.length + 11) + 4) h2
    fun v₂ S₂ ⟨hx₂, hz₂, hs₂, hF₂⟩ => ?_) (fun _ _ h => h) (by ring_nf; omega)
  -- stage 3: push bra on x
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L.length * (2 * m + 2 * Nat.log 2 L.length + 11) + 3)
    (Frag.pushSym_runs x .bra v₂ S₂) fun v₃ S₃ ⟨_, hS₃⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₃
  -- stage 4: the entry loop over z
  have hloop := forEntries_runs (body := (moveEntry z x s).seq (incr y s)) L.reverse (S₁ z)
    (fun i T => T x = entries (L.reverse.take i).reverse ++ .bra :: xr ∧
      T y = encodeNatΓ' i ++ .comma :: S y ∧ T s = S s ∧
      ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ z → T k = S k)
    (2 * m + 2 * Nat.log 2 L.length + 9) v₃ (Function.update S₂ x (.bra :: S₂ x))
    (by rw [Function.update_of_ne hzx, hz₂])
    ⟨by simp [hx₂],
      by rw [Function.update_of_ne hyx, hF₂ y hyx hyz hys, hy₁],
      by rw [Function.update_of_ne hsx, hs₂, hf₁ s hsy],
      fun k hkx hky hks hkz => by
        rw [Function.update_of_ne hkx, hF₂ k hkx hkz hks, hf₁ k hky]⟩
    (fun i l L' hdrop w T ⟨hTx, hTy, hTs, hTF⟩ hTz => by
      have hl := hm' l (mem_of_drop_eq_cons hdrop)
      have hstep := take_succ_of_drop_eq_cons hdrop
      have hi : i < L.length := by
        have : L.reverse.drop i ≠ [] := by rw [hdrop]; exact List.cons_ne_nil _ _
        rw [Ne, List.drop_eq_nil_iff, List.length_reverse] at this; omega
      have hlog : Nat.log 2 i ≤ Nat.log 2 L.length := Nat.log_mono_right hi.le
      have h4a := moveEntry_runs hzx hzs hxs l _ w T hTz
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * Nat.log 2 L.length + 5) h4a
        fun w₁ T₁ ⟨_, _, _, hz', hx', hs', hF'⟩ => ?_) (fun _ _ h => h) (by omega)
      have h4b := incr_correct hys i (S y) w₁ T₁ (by rw [hF' y hyz hyx hys, hTy])
      refine Frag.runs_mono h4b (fun _ T₂ ⟨_, _, _, hy'', hs'', hF''⟩ => ⟨⟨?_, hy'', ?_, ?_⟩, ?_⟩)
        (by omega)
      · rw [hF'' x hxy hxs, hx', hTx, hstep]; simp
      · rw [hs'', hs', hTs]
      · intro k hkx hky hks hkz
        rw [hF'' k hky hks, hF' k hkz hkx hks, hTF k hkx hky hks hkz]
      · rw [hF'' z hzy hzs, hz'])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) hloop
    fun v₄ S₄ ⟨_, ⟨hx₄, hy₄, hs₄, hF₄⟩, hz₄⟩ => ?_) (fun _ _ h => h)
    (by simp only [List.length_reverse]; ring_nf; omega)
  -- stage 5: pop z's bra
  refine Frag.runs_mono (popTop_runs z v₄ S₄) (fun _ S₅ ⟨_, hS₅⟩ => ?_) le_rfl
  subst hS₅
  rw [List.take_length, List.reverse_reverse] at hx₄
  rw [List.length_reverse] at hy₄
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne hxz, hx₄, hS, encListB_eq_entries_append]
  · rw [Function.update_of_ne hyz, hy₄]
  · rw [Function.update_of_ne hsz, hs₄]
  · simp [hz₄, hf₁ z hzy]
  · intro k hkx hky hks hkz; rw [Function.update_of_ne hkz, hF₄ k hkx hky hks hkz]

/-! ### Dropping a prefix -/

/-- `flag := flag || (top of x = bra)`; nothing else changes. -/
def peekBraOr (x : K) : Frag :=
  Frag.straight (peek x (fun v o => { v with flag := v.flag || decide (o = some Γ'.bra) }))

theorem peekBraOr_runs (x : K) (v : St) (S : Stacks) :
    (peekBraOr x).Runs v S
      (fun v' S' => v' = { v with flag := v.flag || decide ((S x).head? = some Γ'.bra) } ∧ S' = S)
      1 := by
  constructor
  intro Λ M ι e hI
  refine ⟨1, le_rfl, _, S, runsTo_succ ?_ (runsTo_zero M _), rfl, rfl⟩
  tm_step () [peekBraOr, Frag.straight]

/-- One iteration of `dropN`: drop the top entry of `x`, decrement the counter
on `c`, recompute `flag := (counter = 0) || (top of x = bra)`. -/
def dropNBody (x c s : K) : Frag :=
  (dropNum x).seq ((predNum c s).seq ((isZero c s).seq (peekBraOr x)))

/-- With the number `n` on `c` (consumed) and a list on `x`, drop the first
`n` entries of the list (all of them if `n` exceeds the length); `s` scratch. -/
def dropN (x c s : K) : Frag :=
  (isZero c s).seq ((peekBraOr x).seq
    ((Frag.loop (fun v => !v.flag) (dropNBody x c s)).seq (dropNum c)))

/-- Loop invariant of `dropN`: `i` entries dropped, counter `n - i`, `flag`
set iff the counter is zero or the list is exhausted. -/
def DropInv (x c s : K) (L : List (List Bool)) (n : ℕ) (xr cr sr : List Γ') (S₀ : Stacks)
    (i : ℕ) (w : St) (T : Stacks) : Prop :=
  i ≤ n ∧ i ≤ L.length ∧ T x = encListB (L.drop i) ++ xr ∧
  T c = encodeNatΓ' (n - i) ++ .comma :: cr ∧ T s = sr ∧
  (∀ k, k ≠ x → k ≠ c → k ≠ s → T k = S₀ k) ∧
  w.flag = (decide (n - i = 0) || decide (L.length ≤ i))

theorem dropNBody_runs {x c s : K} (hxc : x ≠ c) (hxs : x ≠ s) (hcs : c ≠ s)
    (L : List (List Bool)) (m : ℕ) (hm : ∀ l ∈ L, l.length ≤ m) (n : ℕ) (xr cr sr : List Γ')
    (S₀ : Stacks) (i : ℕ) (hi : i < min n L.length) (w : St) (T : Stacks)
    (hI : DropInv x c s L n xr cr sr S₀ i w T) :
    (dropNBody x c s).Runs w T (DropInv x c s L n xr cr sr S₀ (i + 1))
      (m + 4 * Nat.log 2 n + 14) := by
  have hcx := hxc.symm
  have hsx := hxs.symm
  obtain ⟨-, -, hTx, hTc, hTs, hTF, -⟩ := hI
  have hiL : i < L.length := lt_of_lt_of_le hi (min_le_right _ _)
  have hin : i < n := lt_of_lt_of_le hi (min_le_left _ _)
  have hdrop := List.drop_eq_getElem_cons hiL
  have hl := hm L[i] (List.getElem_mem hiL)
  have hTx' : T x = bits L[i] ++ .comma :: (encListB (L.drop (i + 1)) ++ xr) := by
    rw [hTx, hdrop, encListB_cons]; simp
  have hlog1 : Nat.log 2 (n - i) ≤ Nat.log 2 n := Nat.log_mono_right (by omega)
  have hlog2 : Nat.log 2 (n - i - 1) ≤ Nat.log 2 n := Nat.log_mono_right (by omega)
  -- dropNum x
  have h1 := dropNum_runs L[i] _ w T hTx'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * Nat.log 2 n + 13) h1
    fun w₁ T₁ ⟨_, _, _, hx₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- predNum c s
  have h2 := predNum_correct hcs (n - i) (by omega) cr w₁ T₁ (by rw [hF₁ c hcx, hTc])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * Nat.log 2 n + 8) h2
    fun w₂ T₂ ⟨_, _, hc₂, hs₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- isZero c s
  have h3 := isZero_correct hcs (n - i - 1) cr w₂ T₂ hc₂
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) h3
    fun w₃ T₃ ⟨hfl₃, _, hc₃, hs₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- peekBraOr x
  refine Frag.runs_mono (peekBraOr_runs x w₃ T₃) (fun w₄ T₄ ⟨hw₄, hT₄⟩ => ?_) le_rfl
  rw [hw₄, hT₄]
  have hx₃ : T₃ x = encListB (L.drop (i + 1)) ++ xr := by
    rw [hF₃ x hxc hxs, hF₂ x hxc hxs, hx₁]
  refine ⟨by omega, by omega, hx₃, ?_, ?_, ?_, ?_⟩
  · rw [hc₃, hc₂, Nat.sub_sub]
  · rw [hs₃, hs₂, hF₁ s hsx, hTs]
  · intro k hkx hkc hks; rw [hF₃ k hkc hks, hF₂ k hkc hks, hF₁ k hkx, hTF k hkx hkc hks]
  · simp only [hfl₃, hx₃, flag_encListB_drop, Nat.sub_sub]

theorem drop_min_length {α : Type*} (L : List α) (n : ℕ) : L.drop (min n L.length) = L.drop n := by
  rcases le_total n L.length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.drop_length, List.drop_eq_nil_of_le h]

theorem dropN_runs {x c s : K} (hxc : x ≠ c) (hxs : x ≠ s) (hcs : c ≠ s)
    (L : List (List Bool)) (m : ℕ) (hm : ∀ l ∈ L, l.length ≤ m) (n : ℕ) (xr cr : List Γ')
    (v : St) (S : Stacks) (hSx : S x = encListB L ++ xr)
    (hSc : S c = encodeNatΓ' n ++ .comma :: cr) :
    (dropN x c s).Runs v S (fun _ S' =>
        S' x = encListB (L.drop n) ++ xr ∧ S' c = cr ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ c → k ≠ s → S' k = S k)
      (L.length * (m + 4 * Nat.log 2 n + 15) + 3 * Nat.log 2 n + 11) := by
  have hcx := hxc.symm
  have hsx := hxs.symm
  have hsc := hcs.symm
  set N := min n L.length with hN
  set TL := N * (m + 4 * Nat.log 2 n + 14 + 1) + 1 with hTL
  have hTL' : TL = N * (m + 4 * Nat.log 2 n + 15) + 1 := hTL
  have hNL : N ≤ L.length := min_le_right _ _
  have hmul : N * (m + 4 * Nat.log 2 n + 15) ≤ L.length * (m + 4 * Nat.log 2 n + 15) :=
    Nat.mul_le_mul_right _ hNL
  have hlogN : Nat.log 2 (n - N) ≤ Nat.log 2 n := Nat.log_mono_right (by omega)
  -- stage 1: isZero c s
  have h1 := isZero_correct hcs n cr v S hSc
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL + Nat.log 2 n + 3) h1
    fun v₁ S₁ ⟨hfl₁, _, hc₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h) (by rw [hTL']; omega)
  -- stage 2: peekBraOr x
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL + Nat.log 2 n + 2) (peekBraOr_runs x v₁ S₁)
    fun v₂ S₂ ⟨hv₂, hS₂⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₂, hS₂]
  have hx₁ : S₁ x = encListB L ++ xr := by rw [hF₁ x hxc hxs, hSx]
  have hfl0 := flag_encListB_drop L 0 xr
  rw [List.drop_zero] at hfl0
  -- stage 3: the loop
  have hloop := Frag.loop_runs (c := fun v => !v.flag) (B := dropNBody x c s)
    (DropInv x c s L n xr cr (S s) S) N (m + 4 * Nat.log 2 n + 14)
    (v := { v₁ with flag := v₁.flag || decide ((S₁ x).head? = some Γ'.bra) }) (S := S₁)
    ⟨Nat.zero_le _, Nat.zero_le _, by rw [hx₁]; rfl, by rw [hc₁, hSc]; rfl, hs₁,
      fun k hkx hkc hks => hF₁ k hkc hks, by rw [hfl₁, hx₁, hfl0]; rfl⟩
    (fun i hi w T ⟨_, _, _, _, _, _, hfl⟩ => by simp [hfl]; omega)
    (fun w T ⟨_, _, _, _, _, _, hfl⟩ => by simp [hfl]; omega)
    (fun i hi w T hI => dropNBody_runs hxc hxs hcs L m hm n xr cr (S s) S i hi w T hI)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := Nat.log 2 n + 2) hloop
    fun v₃ S₃ ⟨⟨_, _, hx₃, hc₃, hs₃, hF₃, _⟩, _⟩ => ?_) (fun _ _ h => h) le_rfl
  -- stage 4: drop the counter
  have h4 := dropNum_correct (n - N) cr v₃ S₃ hc₃
  refine Frag.runs_mono h4 (fun _ S₄ ⟨_, _, _, hc₄, hF₄⟩ => ⟨?_, hc₄, ?_, ?_⟩) (by omega)
  · rw [hF₄ x hxc, hx₃, hN, drop_min_length]
  · rw [hF₄ s hsc, hs₃]
  · intro k hkx hkc hks; rw [hF₄ k hkc, hF₃ k hkx hkc hks]

/-! ### Membership -/

/-- Membership of a value among the entries, by value. -/
def memB (ys : List Bool) (L : List (List Bool)) : Bool := L.any (fun l => toNat l == toNat ys)

theorem memB_take_succ {L : List (List Bool)} {i : ℕ} {l : List Bool} {L' : List (List Bool)}
    (h : L.drop i = l :: L') (ys : List Bool) :
    memB ys (L.take (i + 1)) = (memB ys (L.take i) || (toNat l == toNat ys)) := by
  rw [memB, memB, take_succ_of_drop_eq_cons h, List.any_append, List.any_cons, List.any_nil,
    Bool.or_false]

theorem memB_encodeNat (a : ℕ) (l : List ℕ) :
    memB (Computability.encodeNat a) (l.map Computability.encodeNat) = decide (a ∈ l) := by
  rw [Bool.eq_iff_iff]
  simp only [memB, List.any_map, List.any_eq_true, Function.comp, toNat_encodeNat, beq_iff_eq,
    decide_eq_true_eq]
  exact ⟨fun ⟨e, he, h⟩ => h ▸ he, fun h => ⟨a, h, rfl⟩⟩

/-- One iteration of `memList`: compare the top entry of `x` (copied to `t`)
with the number on `y` (copied to `s`); on equality set the accumulator on
`t` to `1`; then move the entry to `z`. -/
def memBody (x y s t z : K) : Frag :=
  (dup x t s).seq ((dup y s t).seq ((cmpFrag t s).seq
    ((Frag.ite (fun v => decide (v.cmp = .eq)) ((dropNum t).seq (pushNum t 1)) Frag.skip).seq
      (moveEntry x z s))))

theorem memBody_runs {x y s t z : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxt : x ≠ t) (hxz : x ≠ z)
    (hys : y ≠ s) (hyt : y ≠ t) (hyz : y ≠ z) (hst : s ≠ t) (hsz : s ≠ z) (htz : t ≠ z)
    (l ys : List Bool) (m a : ℕ) (hl : l.length ≤ m) (ha : ys.length ≤ a) (b₀ : Bool)
    (xr yr tr : List Γ') (w : St) (T : Stacks)
    (hTx : T x = bits l ++ .comma :: xr) (hTy : T y = bits ys ++ .comma :: yr)
    (hTt : T t = encodeNatΓ' b₀.toNat ++ .comma :: tr) :
    (memBody x y s t z).Runs w T (fun _ T' =>
        T' x = xr ∧ T' y = T y ∧ T' s = T s ∧
        T' t = encodeNatΓ' (b₀ || (toNat l == toNat ys)).toNat ++ .comma :: tr ∧
        T' z = bits l ++ .comma :: T z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ t → k ≠ z → T' k = T k)
      (5 * m + 3 * a + 21) := by
  have hyx := hxy.symm
  have hsx := hxs.symm
  have htx := hxt.symm
  have hzx := hxz.symm
  have hsy := hys.symm
  have hty := hyt.symm
  have hzy := hyz.symm
  have hts := hst.symm
  have hzs := hsz.symm
  have hzt := htz.symm
  -- stage 1: dup x t s
  have h1 := dup_runs hxt hxs hts l xr w T hTx
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * m + 3 * a + 16) h1
    fun w₁ T₁ ⟨hx₁, ht₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 2: dup y s t
  have h2 := dup_runs hys hyt hst ys yr w₁ T₁ (by rw [hF₁ y hyx hyt hys, hTy])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * m + a + 11) h2
    fun w₂ T₂ ⟨hy₂, hs₂, ht₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: cmpFrag t s
  have h3 := cmpFrag_runs hts l ys (T t) (T s) w₂ T₂ (by rw [ht₂, ht₁]) (by rw [hs₂, hs₁])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * m + 9) h3
    fun w₃ T₃ ⟨hcmp₃, ht₃, hs₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 4: on equality, set the accumulator to 1
  have hTt₃ : T₃ t = encodeNatΓ' b₀.toNat ++ .comma :: tr := by rw [ht₃, hTt]
  have hlog0 : Nat.log 2 b₀.toNat = 0 := by cases b₀ <;> simp
  have h4 : (Frag.ite (fun v => decide (v.cmp = .eq)) ((dropNum t).seq (pushNum t 1)) Frag.skip).Runs
      w₃ T₃ (fun _ T₄ => T₄ t = encodeNatΓ' (b₀ || (toNat l == toNat ys)).toNat ++ .comma :: tr ∧
        ∀ k, k ≠ t → T₄ k = T₃ k) 5 := by
    refine Frag.ite_runs (fun hc => ?_) (fun hc => ?_)
    · have heq : toNat l = toNat ys := by
        simpa [hcmp₃, compare_eq_iff_eq] using hc
      rw [heq, beq_self_eq_true, Bool.or_true]
      have h4a := dropNum_correct b₀.toNat tr w₃ T₃ hTt₃
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 2) h4a
        fun w₄ T₄ ⟨_, _, _, ht₄, hF₄⟩ => ?_) (fun _ _ h => h) (by rw [hlog0])
      refine Frag.runs_mono (pushNum_runs t 1 w₄ T₄) (fun _ T₅ ⟨_, ht₅, hF₅⟩ => ⟨?_, ?_⟩)
        (by rw [Nat.log_one_right])
      · rw [ht₅, ht₄]; rfl
      · intro k hk; rw [hF₅ k hk, hF₄ k hk]
    · have hne : toNat l ≠ toNat ys := by
        simpa [hcmp₃, compare_eq_iff_eq] using hc
      rw [beq_eq_false_iff_ne.mpr hne, Bool.or_false]
      exact Frag.runs_mono (Frag.skip_runs w₃ T₃) (fun _ T₄ ⟨_, hT₄⟩ => by subst hT₄; exact ⟨hTt₃, fun _ _ => rfl⟩)
        (by omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * m + 4) h4
    fun w₄ T₄ ⟨ht₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 5: moveEntry x z s
  have hx₄ : T₄ x = bits l ++ .comma :: xr := by
    rw [hF₄ x hxt, hF₃ x hxt hxs, hF₂ x hxy hxs hxt, hx₁, hTx]
  have h5 := moveEntry_runs hxz hxs hzs l xr w₄ T₄ hx₄
  refine Frag.runs_mono h5 (fun _ T₅ ⟨_, _, _, hx₅, hz₅, hs₅, hF₅⟩ => ⟨hx₅, ?_, ?_, ?_, ?_, ?_⟩)
    (by omega)
  · rw [hF₅ y hyx hyz hys, hF₄ y hyt, hF₃ y hyt hys, hy₂, hF₁ y hyx hyt hys]
  · rw [hs₅, hF₄ s hst, hs₃]
  · rw [hF₅ t htx htz hts, ht₄]
  · rw [hz₅, hF₄ z hzt, hF₃ z hzt hzs, hF₂ z hzy hzs hzt, hF₁ z hzx hzt hzs]
  · intro k hkx hky hks hkt hkz
    rw [hF₅ k hkx hkz hks, hF₄ k hkt, hF₃ k hkt hks, hF₂ k hky hks hkt, hF₁ k hkx hkt hks]

/-- `flag := (the number on y is among the entries of the list on x)`, both
restored.  The list is scanned entry by entry onto `z` (comparing each entry
with the number, accumulator on `t`) and moved back; `s`, `t`, `z` scratch. -/
def memList (x y s t z : K) : Frag :=
  (Frag.pushSym z .bra).seq ((pushNum t 0).seq ((forEntries x (memBody x y s t z)).seq
    ((moveEntries z x s).seq ((isZero t s).seq
      ((Frag.load' (fun v => { v with flag := !v.flag })).seq (dropNum t))))))

theorem memList_runs {x y s t z : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxt : x ≠ t) (hxz : x ≠ z)
    (hys : y ≠ s) (hyt : y ≠ t) (hyz : y ≠ z) (hst : s ≠ t) (hsz : s ≠ z) (htz : t ≠ z)
    (L : List (List Bool)) (m : ℕ) (hm : ∀ l ∈ L, l.length ≤ m) (ys : List Bool) (a : ℕ)
    (ha : ys.length ≤ a) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encListB L ++ xr) (hSy : S y = bits ys ++ .comma :: yr) :
    (memList x y s t z).Runs v S (fun v' S' =>
        v'.flag = memB ys L ∧ S' x = S x ∧ S' y = S y ∧ S' s = S s ∧ S' t = S t ∧ S' z = S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ t → k ≠ z → S' k = S k)
      (L.length * (7 * m + 3 * a + 29) + 18) := by
  have hyx := hxy.symm
  have hsx := hxs.symm
  have htx := hxt.symm
  have hzx := hxz.symm
  have hsy := hys.symm
  have hty := hyt.symm
  have hzy := hyz.symm
  have hts := hst.symm
  have hzs := hsz.symm
  have hzt := htz.symm
  have hm' : ∀ l ∈ L.reverse, l.length ≤ m := fun l hl => hm l (List.mem_reverse.mp hl)
  -- stage 1: push bra on z
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L.length * (7 * m + 3 * a + 29) + 17)
    (Frag.pushSym_runs z .bra v S) fun v₁ S₁ ⟨_, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₁
  -- stage 2: push 0 on t
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L.length * (7 * m + 3 * a + 29) + 15)
    (pushNum_runs t 0 v₁ _) fun v₂ S₂ ⟨_, ht₂, hf₂⟩ => ?_) (fun _ _ h => h)
    (by rw [Nat.log_zero_right]; omega)
  -- stage 3: the entry loop
  have hx₂ : S₂ x = encListB L ++ xr := by rw [hf₂ x hxt, Function.update_of_ne hxz, hSx]
  have hloop := forEntries_runs (body := memBody x y s t z) L xr
    (fun i T => T y = S y ∧ T s = S s ∧
      T t = encodeNatΓ' (memB ys (L.take i)).toNat ++ .comma :: S t ∧
      T z = entries (L.take i).reverse ++ .bra :: S z ∧
      ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ t → k ≠ z → T k = S k)
    (5 * m + 3 * a + 21) v₂ S₂ hx₂
    ⟨by rw [hf₂ y hyt, Function.update_of_ne hyz],
      by rw [hf₂ s hst, Function.update_of_ne hsz],
      by rw [ht₂, Function.update_of_ne htz]; rfl,
      by rw [hf₂ z hzt]; simp,
      fun k hkx hky hks hkt hkz => by rw [hf₂ k hkt, Function.update_of_ne hkz]⟩
    (fun i l L' hdrop w T ⟨hTy, hTs, hTt, hTz, hTF⟩ hTx => by
      have hl := hm l (mem_of_drop_eq_cons hdrop)
      have hstep := take_succ_of_drop_eq_cons hdrop
      have hb := memBody_runs hxy hxs hxt hxz hys hyt hyz hst hsz htz l ys m a hl ha
        (memB ys (L.take i)) _ yr (S t) w T hTx (by rw [hTy, hSy]) hTt
      refine Frag.runs_mono hb (fun _ T' ⟨hx', hy', hs', ht', hz', hF'⟩ =>
        ⟨⟨hy'.trans hTy, hs'.trans hTs, ?_, ?_, ?_⟩, hx'⟩) le_rfl
      · rw [ht', memB_take_succ hdrop]
      · rw [hz', hTz, hstep]; simp
      · intro k hkx hky hks hkt hkz; rw [hF' k hkx hky hks hkt hkz, hTF k hkx hky hks hkt hkz])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L.length * (2 * m + 6) + 13) hloop
    fun v₃ S₃ ⟨_, ⟨hy₃, hs₃, ht₃, hz₃, hF₃⟩, hx₃⟩ => ?_) (fun _ _ h => h) (by ring_nf; omega)
  rw [List.take_length] at ht₃ hz₃
  -- stage 4: move the entries back
  have h4 := moveEntries_runs hzx hzs hxs L.reverse m hm' (S z) v₃ S₃
    (by rw [hz₃, encListB_eq_entries_append])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 10) h4
    fun v₄ S₄ ⟨hz₄, hx₄, hs₄, hF₄⟩ => ?_) (fun _ _ h => h) (by simp only [List.length_reverse]; omega)
  -- stage 5: test the accumulator
  have hlog0 : Nat.log 2 (memB ys L).toNat = 0 := by cases memB ys L <;> simp
  have h5 := isZero_correct hts (memB ys L).toNat (S t) v₄ S₄ (by rw [hF₄ t htz htx hts, ht₃])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3) h5
    fun v₅ S₅ ⟨hfl₅, _, ht₅, hs₅, hF₅⟩ => ?_) (fun _ _ h => h) (by rw [hlog0])
  -- stage 6: flip the flag
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2)
    (Frag.load'_runs (fun v => { v with flag := !v.flag }) v₅ S₅)
    fun v₆ S₆ ⟨hv₆, hS₆⟩ => ?_) (fun _ _ h => h) le_rfl
  rw [hv₆, hS₆]
  -- stage 7: drop the accumulator
  have h7 := dropNum_correct (memB ys L).toNat (S t) { v₅ with flag := !v₅.flag } S₅
    (by rw [ht₅, hF₄ t htz htx hts, ht₃])
  refine Frag.runs_mono h7 (fun _ S₇ ⟨hfl₇, _, _, ht₇, hF₇⟩ => ⟨?_, ?_, ?_, ?_, ht₇, ?_, ?_⟩)
    (by rw [hlog0])
  · rw [hfl₇]; simp only [hfl₅]; cases memB ys L <;> simp
  · rw [hF₇ x hxt, hF₅ x hxt hxs, hx₄, hx₃, List.reverse_reverse, hSx, encListB_eq_entries_append]
  · rw [hF₇ y hyt, hF₅ y hyt hys, hF₄ y hyz hyx hys, hy₃]
  · rw [hF₇ s hst, hs₅, hs₄, hs₃]
  · rw [hF₇ z hzt, hF₅ z hzt hzs, hz₄]
  · intro k hkx hky hks hkt hkz
    rw [hF₇ k hkt, hF₅ k hkt hks, hF₄ k hkz hkx hks, hF₃ k hkx hky hks hkt hkz]

/-! ### ℕ-level corollaries

Inputs `encList l` with every entry below `2 ^ b`; step bounds with `m := b`,
and `B`-forms `(l.length + 1) * B b` (one budget per entry, plus one). -/

/-- A per-entry linear bound with linear overhead is within `(n + 1) * B b`. -/
theorem list_le_B {n c d b : ℕ} (hc : c ≤ 64 * (b + 2)) (hd : d ≤ 64 * (b + 2)) :
    n * c + d ≤ (n + 1) * B b := by
  have h1 := le_B_of_le_linear hc
  have h2 := le_B_of_le_linear hd
  calc n * c + d ≤ n * B b + B b := Nat.add_le_add (Nat.mul_le_mul_left _ h1) h2
    _ = (n + 1) * B b := by ring

theorem revList_correct {x y s : K} (hxy : x ≠ y) (hxs : x ≠ s) (hys : y ≠ s)
    (l : List ℕ) (b : ℕ) (hb : ∀ a ∈ l, a < 2 ^ b) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encList l ++ xr) :
    (revList x y s).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = encList l.reverse ++ S y ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → S' k = S k)
      (l.length * (2 * b + 6) + 4) := by
  rw [encList_eq] at hS
  refine Frag.runs_mono (revList_runs hxy hxs hys _ b (entry_length_le_of_lt_pow hb) xr v S hS)
    (fun _ S' ⟨hx, hy, hs, hF⟩ => ⟨hx, by rw [hy, encList_eq, List.map_reverse], hs, hF⟩) (by simp)

theorem revList_le_B {x y s : K} (hxy : x ≠ y) (hxs : x ≠ s) (hys : y ≠ s)
    (l : List ℕ) (b : ℕ) (hb : ∀ a ∈ l, a < 2 ^ b) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encList l ++ xr) :
    (revList x y s).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = encList l.reverse ++ S y ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → S' k = S k)
      ((l.length + 1) * B b) :=
  Frag.runs_mono (revList_correct hxy hxs hys l b hb xr v S hS) (fun _ _ h => h)
    (list_le_B (by omega) (by omega))

theorem appendList_correct {x y z s : K} (hxy : x ≠ y) (hxz : x ≠ z) (hxs : x ≠ s) (hyz : y ≠ z)
    (hys : y ≠ s) (hzs : z ≠ s) (l₁ l₂ : List ℕ) (b : ℕ) (hb : ∀ a ∈ l₁, a < 2 ^ b)
    (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encList l₁ ++ xr) (hSy : S y = encList l₂ ++ yr) :
    (appendList x y z s).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = encList (l₁ ++ l₂) ++ yr ∧ S' z = S z ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → k ≠ s → S' k = S k)
      (l₁.length * (4 * b + 12) + 7) := by
  rw [encList_eq] at hSx hSy
  refine Frag.runs_mono (appendList_runs hxy hxz hxs hyz hys hzs _ _ b
    (entry_length_le_of_lt_pow hb) xr yr v S hSx hSy)
    (fun _ S' ⟨hx, hy, hz, hs, hF⟩ => ⟨hx, by rw [hy, encList_eq, List.map_append], hz, hs, hF⟩)
    (by simp)

theorem appendList_le_B {x y z s : K} (hxy : x ≠ y) (hxz : x ≠ z) (hxs : x ≠ s) (hyz : y ≠ z)
    (hys : y ≠ s) (hzs : z ≠ s) (l₁ l₂ : List ℕ) (b : ℕ) (hb : ∀ a ∈ l₁, a < 2 ^ b)
    (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encList l₁ ++ xr) (hSy : S y = encList l₂ ++ yr) :
    (appendList x y z s).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = encList (l₁ ++ l₂) ++ yr ∧ S' z = S z ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → k ≠ s → S' k = S k)
      ((l₁.length + 1) * B b) :=
  Frag.runs_mono (appendList_correct hxy hxz hxs hyz hys hzs l₁ l₂ b hb xr yr v S hSx hSy)
    (fun _ _ h => h) (list_le_B (by omega) (by omega))

theorem copyList_correct {x y s z : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxz : x ≠ z) (hys : y ≠ s)
    (hyz : y ≠ z) (hsz : s ≠ z) (l : List ℕ) (b : ℕ) (hb : ∀ a ∈ l, a < 2 ^ b)
    (xr : List Γ') (v : St) (S : Stacks) (hS : S x = encList l ++ xr) :
    (copyList x y s z).Runs v S (fun _ S' =>
        S' x = S x ∧ S' y = encList l ++ S y ∧ S' s = S s ∧ S' z = S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ z → S' k = S k)
      (l.length * (6 * b + 17) + 9) := by
  rw [encList_eq] at hS
  refine Frag.runs_mono (copyList_runs hxy hxs hxz hys hyz hsz _ b
    (entry_length_le_of_lt_pow hb) xr v S hS)
    (fun _ S' ⟨hx, hy, hs, hz, hF⟩ => ⟨hx, by rw [hy, encList_eq], hs, hz, hF⟩) (by simp)

theorem copyList_le_B {x y s z : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxz : x ≠ z) (hys : y ≠ s)
    (hyz : y ≠ z) (hsz : s ≠ z) (l : List ℕ) (b : ℕ) (hb : ∀ a ∈ l, a < 2 ^ b)
    (xr : List Γ') (v : St) (S : Stacks) (hS : S x = encList l ++ xr) :
    (copyList x y s z).Runs v S (fun _ S' =>
        S' x = S x ∧ S' y = encList l ++ S y ∧ S' s = S s ∧ S' z = S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ z → S' k = S k)
      ((l.length + 1) * B b) :=
  Frag.runs_mono (copyList_correct hxy hxs hxz hys hyz hsz l b hb xr v S hS) (fun _ _ h => h)
    (list_le_B (by omega) (by omega))

theorem listLen_correct {x y s z : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxz : x ≠ z) (hys : y ≠ s)
    (hyz : y ≠ z) (hsz : s ≠ z) (l : List ℕ) (b : ℕ) (hb : ∀ a ∈ l, a < 2 ^ b)
    (xr : List Γ') (v : St) (S : Stacks) (hS : S x = encList l ++ xr) :
    (listLen x y s z).Runs v S (fun _ S' =>
        S' x = S x ∧ S' y = encodeNatΓ' l.length ++ .comma :: S y ∧ S' s = S s ∧ S' z = S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ z → S' k = S k)
      (l.length * (4 * b + 2 * Nat.log 2 l.length + 17) + 10) := by
  rw [encList_eq] at hS
  refine Frag.runs_mono (listLen_runs hxy hxs hxz hys hyz hsz _ b
    (entry_length_le_of_lt_pow hb) xr v S hS)
    (fun _ S' ⟨hx, hy, hs, hz, hF⟩ => ⟨hx, by rw [hy, List.length_map], hs, hz, hF⟩) (by simp)

/-- `listLen` within budget: the count itself must fit in `b` bits. -/
theorem listLen_le_B {x y s z : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxz : x ≠ z) (hys : y ≠ s)
    (hyz : y ≠ z) (hsz : s ≠ z) (l : List ℕ) (b : ℕ) (hb : ∀ a ∈ l, a < 2 ^ b)
    (hl : l.length < 2 ^ b) (xr : List Γ') (v : St) (S : Stacks) (hS : S x = encList l ++ xr) :
    (listLen x y s z).Runs v S (fun _ S' =>
        S' x = S x ∧ S' y = encodeNatΓ' l.length ++ .comma :: S y ∧ S' s = S s ∧ S' z = S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ z → S' k = S k)
      ((l.length + 1) * B b) := by
  have := log_le_of_lt_pow hl
  exact Frag.runs_mono (listLen_correct hxy hxs hxz hys hyz hsz l b hb xr v S hS) (fun _ _ h => h)
    (list_le_B (by omega) (by omega))

theorem dropN_correct {x c s : K} (hxc : x ≠ c) (hxs : x ≠ s) (hcs : c ≠ s)
    (l : List ℕ) (b : ℕ) (hb : ∀ a ∈ l, a < 2 ^ b) (n : ℕ) (xr cr : List Γ')
    (v : St) (S : Stacks) (hSx : S x = encList l ++ xr)
    (hSc : S c = encodeNatΓ' n ++ .comma :: cr) :
    (dropN x c s).Runs v S (fun _ S' =>
        S' x = encList (l.drop n) ++ xr ∧ S' c = cr ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ c → k ≠ s → S' k = S k)
      (l.length * (b + 4 * Nat.log 2 n + 15) + 3 * Nat.log 2 n + 11) := by
  rw [encList_eq] at hSx
  refine Frag.runs_mono (dropN_runs hxc hxs hcs _ b (entry_length_le_of_lt_pow hb) n xr cr v S
    hSx hSc)
    (fun _ S' ⟨hx, hc, hs, hF⟩ => ⟨by rw [hx, encList_eq, List.map_drop], hc, hs, hF⟩) (by simp)

/-- `dropN` within budget: the count `n` must fit in `b` bits. -/
theorem dropN_le_B {x c s : K} (hxc : x ≠ c) (hxs : x ≠ s) (hcs : c ≠ s)
    (l : List ℕ) (b : ℕ) (hb : ∀ a ∈ l, a < 2 ^ b) (n : ℕ) (hn : n < 2 ^ b) (xr cr : List Γ')
    (v : St) (S : Stacks) (hSx : S x = encList l ++ xr)
    (hSc : S c = encodeNatΓ' n ++ .comma :: cr) :
    (dropN x c s).Runs v S (fun _ S' =>
        S' x = encList (l.drop n) ++ xr ∧ S' c = cr ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ c → k ≠ s → S' k = S k)
      ((l.length + 1) * B b) := by
  have hlog := log_le_of_lt_pow hn
  refine Frag.runs_mono (dropN_correct hxc hxs hcs l b hb n xr cr v S hSx hSc) (fun _ _ h => h) ?_
  have := list_le_B (n := l.length) (c := b + 4 * Nat.log 2 n + 15) (d := 3 * Nat.log 2 n + 11)
    (b := b) (by omega) (by omega)
  omega

theorem memList_correct {x y s t z : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxt : x ≠ t) (hxz : x ≠ z)
    (hys : y ≠ s) (hyt : y ≠ t) (hyz : y ≠ z) (hst : s ≠ t) (hsz : s ≠ z) (htz : t ≠ z)
    (l : List ℕ) (a b : ℕ) (hb : ∀ e ∈ l, e < 2 ^ b) (ha : a < 2 ^ b)
    (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encList l ++ xr) (hSy : S y = encodeNatΓ' a ++ .comma :: yr) :
    (memList x y s t z).Runs v S (fun v' S' =>
        v'.flag = decide (a ∈ l) ∧ S' x = S x ∧ S' y = S y ∧ S' s = S s ∧ S' t = S t ∧
        S' z = S z ∧ ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ t → k ≠ z → S' k = S k)
      (l.length * (10 * b + 29) + 18) := by
  rw [encList_eq] at hSx
  refine Frag.runs_mono (memList_runs hxy hxs hxt hxz hys hyt hyz hst hsz htz _ b
    (entry_length_le_of_lt_pow hb) (Computability.encodeNat a) b
    (encodeNat_length_le_of_lt_pow ha) xr yr v S hSx hSy)
    (fun _ _ ⟨hfl, h⟩ => ⟨by rw [hfl, memB_encodeNat], h⟩)
    (by rw [List.length_map, show 7 * b + 3 * b + 29 = 10 * b + 29 by omega])

theorem memList_le_B {x y s t z : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxt : x ≠ t) (hxz : x ≠ z)
    (hys : y ≠ s) (hyt : y ≠ t) (hyz : y ≠ z) (hst : s ≠ t) (hsz : s ≠ z) (htz : t ≠ z)
    (l : List ℕ) (a b : ℕ) (hb : ∀ e ∈ l, e < 2 ^ b) (ha : a < 2 ^ b)
    (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encList l ++ xr) (hSy : S y = encodeNatΓ' a ++ .comma :: yr) :
    (memList x y s t z).Runs v S (fun v' S' =>
        v'.flag = decide (a ∈ l) ∧ S' x = S x ∧ S' y = S y ∧ S' s = S s ∧ S' t = S t ∧
        S' z = S z ∧ ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ t → k ≠ z → S' k = S k)
      ((l.length + 1) * B b) :=
  Frag.runs_mono (memList_correct hxy hxs hxt hxz hys hyt hyz hst hsz htz l a b hb ha xr yr v S
    hSx hSy) (fun _ _ h => h) (list_le_B (by omega) (by omega))

end Carmichael.TM
