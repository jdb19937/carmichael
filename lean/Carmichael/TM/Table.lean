import Carmichael.TM.Lists
import Carmichael.TM.MulDiv
import Carmichael.Algorithm

/-!
# Route T: the DP table of step 4

The DP table `Alg.Tbl = ℕ → Option (List ℕ)` restricted to `[0, L)` lives on
a stack as `L` consecutive slots followed by a `blank` marker: a slot is
`ket` (no witness) or a list of numbers `encList W` (ended by `bra`).  Slot
boundaries are `ket`/`bra`, numbers contain only bits and commas, and a slot
never starts with `blank`, so the table is parsed unambiguously.

* `encSlot o`, `encSlots sl`: one slot, a list of slots.
* `encTblAsc L t`: slot `0` on top; `encTblDesc L t`: slot `L-1` on top.
  A table stack is `encTblAsc L t ++ .blank :: rest`.
* `setSlotL sl j W`: the slot-list form of `Alg.setIfNone`.
* `accSeq L p t i`: the accumulator of `Alg.dpStep` after processing the
  residues `L-1, …, L-i`; `accSeq L p t L = (Alg.dpStep L p t).1`.

Fragments (operand stacks first, scratch last; scratch restored):

* `peekKet x`, `peekBlank x`: `flag := (top of x = ket / blank)`.
* `forSlots x body`: run `body` once per slot on `x` until the `blank`.
* `moveSlot src dst s s'`: move the top slot of `src` onto `dst`, exactly.
* `dropList x`: pop the list on `x`.
* `emptyTbl c tbl s`: with `L` on `c` (consumed), push the empty table
  (`L` kets over a `blank`) on `tbl`.
* `setIfNoneF tbl j w s scr`: `Alg.setIfNone` at index `j` (on `j`,
  consumed) with the witness on `w` (consumed).
* `lookupSlot tbl j w s scr`: copy slot `j` of the table onto `w`.
* `revTbl src dst s s'`: reverse the slot order (`encTblAsc ↦ encTblDesc`).
* `copyTbl src dst hold s s'`: descending copy of the table on `src` (restored).
* `resStep nL np s t`: the residue update `rp ↦ (rp + L - p % L) % L`.
* `dpStepF np nL snap acc s t`: `Alg.dpStep L p t` on the snapshot
  (`snap`, descending, consumed) and the accumulator (`acc`, ascending).
-/

namespace Carmichael.TM

open Turing Turing.TM2 Turing.TM2.Stmt Computability

/-! ### Table encodings -/

/-- One slot: `ket` for `none`, the witness list for `some W`. -/
def encSlot : Option (List ℕ) → List Γ'
  | none => [.ket]
  | some W => encList W

@[simp] theorem encSlot_none : encSlot none = [.ket] := rfl

@[simp] theorem encSlot_some (W : List ℕ) : encSlot (some W) = encList W := rfl

/-- A list of slots, head on top. -/
def encSlots (sl : List (Option (List ℕ))) : List Γ' := sl.flatMap encSlot

@[simp] theorem encSlots_nil : encSlots [] = [] := rfl

@[simp] theorem encSlots_cons (o : Option (List ℕ)) (sl : List (Option (List ℕ))) :
    encSlots (o :: sl) = encSlot o ++ encSlots sl := by
  simp [encSlots]

@[simp] theorem encSlots_append (sl₁ sl₂ : List (Option (List ℕ))) :
    encSlots (sl₁ ++ sl₂) = encSlots sl₁ ++ encSlots sl₂ := by
  simp [encSlots]

/-- The table on `[0, L)` with slot `0` on top. -/
def encTblAsc (L : ℕ) (t : Alg.Tbl) : List Γ' :=
  (List.range L).flatMap (fun r => encSlot (t r))

/-- The table on `[0, L)` with slot `L - 1` on top. -/
def encTblDesc (L : ℕ) (t : Alg.Tbl) : List Γ' :=
  (List.range L).reverse.flatMap (fun r => encSlot (t r))

theorem encTblAsc_eq (L : ℕ) (t : Alg.Tbl) :
    encTblAsc L t = encSlots ((List.range L).map t) := by
  simp [encTblAsc, encSlots, List.flatMap_map]

theorem encTblDesc_eq (L : ℕ) (t : Alg.Tbl) :
    encTblDesc L t = encSlots ((List.range L).reverse.map t) := by
  rw [encTblDesc, encSlots, List.flatMap_map]

theorem encTblDesc_eq_reverse (L : ℕ) (t : Alg.Tbl) :
    encTblDesc L t = encSlots ((List.range L).map t).reverse := by
  rw [encTblDesc_eq, List.map_reverse]

theorem encTblAsc_emptyTbl (L : ℕ) : encTblAsc L Alg.emptyTbl = List.replicate L .ket := by
  induction L with
  | zero => rfl
  | succ L ih =>
    rw [encTblAsc, List.range_succ, List.flatMap_append, ← encTblAsc, ih]
    simp [Alg.emptyTbl, List.replicate_succ']

/-! ### Agreement below `L` -/

/-- Two tables agree on `[0, L)`. -/
def TblAgree (L : ℕ) (t t' : Alg.Tbl) : Prop := ∀ r < L, t r = t' r

theorem TblAgree.refl (L : ℕ) (t : Alg.Tbl) : TblAgree L t t := fun _ _ => rfl

theorem encTblAsc_congr {L : ℕ} {t t' : Alg.Tbl} (h : TblAgree L t t') :
    encTblAsc L t = encTblAsc L t' := by
  unfold encTblAsc
  apply List.flatMap_congr
  intro r hr
  rw [h r (List.mem_range.mp hr)]

theorem setIfNone_congr {L : ℕ} {t t' : Alg.Tbl} (h : TblAgree L t t') (j : ℕ) (hj : j < L)
    (W : List ℕ) : TblAgree L (Alg.setIfNone t j W) (Alg.setIfNone t' j W) := by
  intro r hr
  unfold Alg.setIfNone
  rw [← h j hj]
  cases t j
  · simp [Function.update_apply, h r hr]
  · exact h r hr

theorem dpGo_congr_below (L p : ℕ) (t t' : Alg.Tbl) (h : TblAgree L t t') (hL : 0 < L) :
    ∀ (fuel : ℕ), fuel ≤ L → ∀ (acc acc' : Alg.Tbl), TblAgree L acc acc' →
      TblAgree L (Alg.dpGo L p t fuel acc).1 (Alg.dpGo L p t' fuel acc').1 ∧
      (Alg.dpGo L p t fuel acc).2 = (Alg.dpGo L p t' fuel acc').2 := by
  intro fuel
  induction fuel with
  | zero => intro _ acc acc' ha; exact ⟨ha, rfl⟩
  | succ r ih =>
    intro hr acc acc' ha
    have hrL : r < L := by omega
    simp only [Alg.dpGo]
    rw [← h r hrL]
    cases t r with
    | none => exact ⟨(ih (by omega) acc acc' ha).1, by rw [(ih (by omega) acc acc' ha).2]⟩
    | some W =>
      have := ih (by omega) _ _ (setIfNone_congr ha ((r * p) % L) (Nat.mod_lt _ hL) (p :: W))
      exact ⟨this.1, by rw [this.2]⟩

/-- `Alg.dpStep` reads its table only on `[0, L)` and writes only there. -/
theorem dpStep_congr_below (L p : ℕ) (t t' : Alg.Tbl) (h : TblAgree L t t') (hL : 0 < L) :
    TblAgree L (Alg.dpStep L p t).1 (Alg.dpStep L p t').1 ∧
    (Alg.dpStep L p t).2 = (Alg.dpStep L p t').2 := by
  simp only [Alg.dpStep]
  have := dpGo_congr_below L p t t' h hL L le_rfl _ _
    (setIfNone_congr h (p % L) (Nat.mod_lt _ hL) [p])
  exact ⟨this.1, by rw [this.2]⟩

/-! ### Slot lists -/

/-- The slot-list form of `Alg.setIfNone`: fill slot `j` if it is empty. -/
def setSlotL (sl : List (Option (List ℕ))) (j : ℕ) (W : List ℕ) : List (Option (List ℕ)) :=
  match sl[j]? with
  | some none => sl.set j (some W)
  | _ => sl

theorem setSlotL_length (sl : List (Option (List ℕ))) (j : ℕ) (W : List ℕ) :
    (setSlotL sl j W).length = sl.length := by
  unfold setSlotL
  split <;> simp

/-- The filled slot: `some W` if empty, unchanged otherwise. -/
def fillSlot (W : List ℕ) : Option (List ℕ) → Option (List ℕ)
  | none => some W
  | some V => some V

theorem setSlotL_eq_take_cons_drop {sl : List (Option (List ℕ))} {j : ℕ} (hj : j < sl.length)
    (W : List ℕ) : setSlotL sl j W = sl.take j ++ fillSlot W sl[j] :: sl.drop (j + 1) := by
  unfold setSlotL
  rw [List.getElem?_eq_getElem hj]
  cases h : sl[j] with
  | none => simp [fillSlot, List.set_eq_take_cons_drop _ hj]
  | some V =>
    show sl = _
    rw [show fillSlot W (some V) = some V from rfl, ← h, ← List.drop_eq_getElem_cons hj,
      List.take_append_drop]

theorem map_range_update (L : ℕ) (t : Alg.Tbl) (j : ℕ) (a : Option (List ℕ)) :
    (List.range L).map (Function.update t j a) = ((List.range L).map t).set j a := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    rw [List.getElem_map, List.getElem_range]
    by_cases hij : j = i
    · subst hij; simp
    · rw [List.getElem_set_ne hij, List.getElem_map, List.getElem_range,
        Function.update_of_ne (Ne.symm hij)]

theorem map_range_setIfNone (L : ℕ) (t : Alg.Tbl) {j : ℕ} (hj : j < L) (W : List ℕ) :
    (List.range L).map (Alg.setIfNone t j W) = setSlotL ((List.range L).map t) j W := by
  unfold Alg.setIfNone setSlotL
  have : ((List.range L).map t)[j]? = some (t j) := by
    rw [List.getElem?_eq_getElem (by simpa using hj)]; simp
  rw [this]
  cases t j
  · exact map_range_update L t j (some W)
  · rfl

theorem getElem_range_reverse_map (L : ℕ) (t : Alg.Tbl) (i : ℕ)
    (hi : i < ((List.range L).reverse.map t).length) :
    ((List.range L).reverse.map t)[i] = t (L - 1 - i) := by
  simp only [List.length_map, List.length_reverse, List.length_range] at hi
  simp [List.getElem_map, List.getElem_reverse, List.getElem_range]

/-! ### The accumulator sequence of `dpStep` -/

/-- The loop body of `Alg.dpGo` at residue `r`. -/
def dpBody (L p : ℕ) (t : Alg.Tbl) (r : ℕ) (acc : Alg.Tbl) : Alg.Tbl :=
  match t r with
  | none => acc
  | some W => Alg.setIfNone acc ((r * p) % L) (p :: W)

theorem dpGo_succ (L p : ℕ) (t : Alg.Tbl) (r : ℕ) (acc : Alg.Tbl) :
    (Alg.dpGo L p t (r + 1) acc).1 = (Alg.dpGo L p t r (dpBody L p t r acc)).1 := by
  simp only [Alg.dpGo, dpBody]
  cases t r <;> rfl

/-- The accumulator after the machine has processed residues `L-1, …, L-i`. -/
def accSeq (L p : ℕ) (t : Alg.Tbl) : ℕ → Alg.Tbl
  | 0 => Alg.setIfNone t (p % L) [p]
  | i + 1 => dpBody L p t (L - 1 - i) (accSeq L p t i)

theorem dpGo_accSeq (L p : ℕ) (t : Alg.Tbl) :
    ∀ i ≤ L, (Alg.dpGo L p t L (accSeq L p t 0)).1 = (Alg.dpGo L p t (L - i) (accSeq L p t i)).1 := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    rw [ih (by omega), show L - i = (L - (i + 1)) + 1 by omega, dpGo_succ]
    show _ = (Alg.dpGo L p t (L - (i + 1)) (dpBody L p t (L - 1 - i) (accSeq L p t i))).1
    rw [show L - 1 - i = L - (i + 1) by omega]

theorem dpStep_eq_accSeq (L p : ℕ) (t : Alg.Tbl) : (Alg.dpStep L p t).1 = accSeq L p t L := by
  simp only [Alg.dpStep]
  rw [show Alg.setIfNone t (p % L) [p] = accSeq L p t 0 from rfl, dpGo_accSeq L p t L le_rfl,
    Nat.sub_self]
  rfl

/-- The residue recursion: `(r p) % L` from `((r+1) p) % L` by one modular
subtraction of `p % L`. -/
theorem res_pred (L p r : ℕ) (hL : 0 < L) :
    (r * p) % L = if p % L ≤ ((r + 1) * p) % L then ((r + 1) * p) % L - p % L
      else L - (p % L - ((r + 1) * p) % L) := by
  have hadd : ((r + 1) * p) % L = ((r * p) % L + p % L) % L := by
    rw [add_mul, one_mul, Nat.add_mod]
  have ha : (r * p) % L < L := Nat.mod_lt _ hL
  have hq : p % L < L := Nat.mod_lt _ hL
  rw [hadd]
  generalize (r * p) % L = a at *
  generalize p % L = q at *
  by_cases hlt : a + q < L
  · rw [Nat.mod_eq_of_lt hlt]
    simp
  · have h2 : a + q - L < L := by omega
    have h3 : (a + q) % L = a + q - L := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt h2]
    rw [h3]
    have : ¬ q ≤ a + q - L := by omega
    rw [if_neg this]
    omega

/-! ### Size bookkeeping -/

/-- A slot has at most `N` entries, each below `2 ^ b`. -/
def SlotBounded (N b : ℕ) (o : Option (List ℕ)) : Prop :=
  ∀ W, o = some W → W.length ≤ N ∧ ∀ q ∈ W, q < 2 ^ b

theorem SlotBounded.none (N b : ℕ) : SlotBounded N b none := fun _ h => by cases h

theorem SlotBounded.mono {N N' b : ℕ} (h : N ≤ N') {o : Option (List ℕ)}
    (ho : SlotBounded N b o) : SlotBounded N' b o :=
  fun W hW => ⟨(ho W hW).1.trans h, (ho W hW).2⟩

theorem SlotBounded.fill {N b : ℕ} {o : Option (List ℕ)} (ho : SlotBounded N b o) {W : List ℕ}
    (hW : W.length ≤ N) (hb : ∀ q ∈ W, q < 2 ^ b) : SlotBounded N b (fillSlot W o) := by
  cases o with
  | none => intro V hV; simp [fillSlot] at hV; subst hV; exact ⟨hW, hb⟩
  | some V => exact ho

/-- Every slot of the table on `[0, L)` is bounded. -/
def TblBounded (L : ℕ) (t : Alg.Tbl) (N b : ℕ) : Prop := ∀ r < L, SlotBounded N b (t r)

theorem TblBounded.mono {L N N' b : ℕ} (h : N ≤ N') {t : Alg.Tbl} (ht : TblBounded L t N b) :
    TblBounded L t N' b := fun r hr => (ht r hr).mono h

theorem tblBounded_emptyTbl (L N b : ℕ) : TblBounded L Alg.emptyTbl N b :=
  fun _ _ => SlotBounded.none N b

theorem tblBounded_map_range {L : ℕ} {t : Alg.Tbl} {N b : ℕ} (h : TblBounded L t N b) :
    ∀ o ∈ (List.range L).map t, SlotBounded N b o := by
  intro o ho
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ho
  exact h r (List.mem_range.mp hr)

theorem tblBounded_setIfNone {L : ℕ} {t : Alg.Tbl} {N b : ℕ} (h : TblBounded L t N b) (j : ℕ)
    {W : List ℕ} (hW : W.length ≤ N) (hb : ∀ q ∈ W, q < 2 ^ b) :
    TblBounded L (Alg.setIfNone t j W) N b := by
  intro r hr
  unfold Alg.setIfNone
  cases hj : t j with
  | none =>
    dsimp only
    intro V hV
    rw [Function.update_apply] at hV
    split_ifs at hV with hrj
    · cases hV; exact ⟨hW, hb⟩
    · exact h r hr V hV
  | some _ => exact h r hr

theorem tblBounded_accSeq {L p : ℕ} {t : Alg.Tbl} {N b : ℕ} (h : TblBounded L t N b)
    (hp : p < 2 ^ b) : ∀ i, TblBounded L (accSeq L p t i) (N + 1) b := by
  intro i
  induction i with
  | zero =>
    exact tblBounded_setIfNone (h.mono (Nat.le_succ N)) _ (by simp) (by simpa using hp)
  | succ i ih =>
    simp only [accSeq, dpBody]
    cases hW : t (L - 1 - i) with
    | none => exact ih
    | some W =>
      by_cases hi : L - 1 - i < L
      · obtain ⟨h1, h2⟩ := h _ hi W hW
        exact tblBounded_setIfNone ih _ (by simp; omega)
          (fun q hq => by rcases List.mem_cons.mp hq with rfl | hq; exact hp; exact h2 q hq)
      · exact fun r hr => by omega

theorem tblBounded_dpStep {L p : ℕ} {t : Alg.Tbl} {N b : ℕ} (h : TblBounded L t N b)
    (hp : p < 2 ^ b) : TblBounded L (Alg.dpStep L p t).1 (N + 1) b := by
  rw [dpStep_eq_accSeq]; exact tblBounded_accSeq h hp L

theorem encSlot_length_le {N b : ℕ} {o : Option (List ℕ)} (h : SlotBounded N b o) :
    (encSlot o).length ≤ N * (b + 1) + 1 := by
  cases o with
  | none => simp
  | some W =>
    obtain ⟨h1, h2⟩ := h W rfl
    have := encList_length_le_of_lt_pow h2
    have := Nat.mul_le_mul_right (b + 1) h1
    simp only [encSlot_some]; omega

theorem encSlots_length_le {N b : ℕ} {sl : List (Option (List ℕ))}
    (h : ∀ o ∈ sl, SlotBounded N b o) : (encSlots sl).length ≤ sl.length * (N * (b + 1) + 1) := by
  induction sl with
  | nil => simp
  | cons o sl ih =>
    have h1 := encSlot_length_le (h o (List.mem_cons_self ..))
    have h2 := ih (fun o' ho' => h o' (List.mem_cons_of_mem _ ho'))
    simp only [encSlots_cons, List.length_append, List.length_cons]
    rw [Nat.succ_mul]; omega

theorem encTblAsc_length_le {L : ℕ} {t : Alg.Tbl} {N b : ℕ} (h : TblBounded L t N b) :
    (encTblAsc L t).length ≤ L * (N * (b + 1) + 1) := by
  rw [encTblAsc_eq]
  simpa using encSlots_length_le (tblBounded_map_range h)

/-! ### Head symbols of slots -/

theorem head?_bits_comma_ne (l : List Bool) (r : List Γ') (g : Γ') (hk : g ≠ .comma)
    (hb : ∀ b, g ≠ .bit b) : (bits l ++ .comma :: r).head? ≠ some g := by
  cases l with
  | nil => simp [Ne.symm hk]
  | cons b l => simp [Ne.symm (hb b)]

theorem head?_encList_ne_ket (W : List ℕ) (r : List Γ') :
    (encList W ++ r).head? ≠ some .ket := by
  cases W with
  | nil => simp
  | cons a W =>
    rw [encList_cons, encodeNatΓ'_eq, List.append_assoc, List.cons_append]
    exact head?_bits_comma_ne _ _ _ (by simp) (by simp)

theorem head?_encList_ne_blank (W : List ℕ) (r : List Γ') :
    (encList W ++ r).head? ≠ some .blank := by
  cases W with
  | nil => simp
  | cons a W =>
    rw [encList_cons, encodeNatΓ'_eq, List.append_assoc, List.cons_append]
    exact head?_bits_comma_ne _ _ _ (by simp) (by simp)

theorem head?_encSlot_ne_blank (o : Option (List ℕ)) (r : List Γ') :
    (encSlot o ++ r).head? ≠ some .blank := by
  cases o with
  | none => simp
  | some W => exact head?_encList_ne_blank W r

theorem decide_head?_encSlot_ket (o : Option (List ℕ)) (r : List Γ') :
    decide ((encSlot o ++ r).head? = some Γ'.ket) = decide (o = none) := by
  cases o with
  | none => simp
  | some W =>
    rw [encSlot_some, decide_eq_false (head?_encList_ne_ket W r)]
    simp

theorem head?_encSlots_blank (sl : List (Option (List ℕ))) (r : List Γ') :
    (encSlots sl ++ .blank :: r).head? = some .blank ↔ sl = [] := by
  cases sl with
  | nil => simp
  | cons o sl =>
    simp only [encSlots_cons, List.append_assoc]
    exact ⟨fun h => absurd h (head?_encSlot_ne_blank o _), fun h => by cases h⟩

theorem flag_encSlots_drop (sl : List (Option (List ℕ))) (i : ℕ) (r : List Γ') :
    decide ((encSlots (sl.drop i) ++ .blank :: r).head? = some Γ'.blank) =
      decide (sl.length ≤ i) := by
  rw [decide_eq_decide, head?_encSlots_blank, List.drop_eq_nil_iff]

/-! ### Peeking at `ket` and `blank` -/

/-- Peek-handler: `flag := (the symbol is ket)`. -/
def readKet (v : St) (o : Option Γ') : St := { v with flag := decide (o = some Γ'.ket) }

/-- `flag := (top of x = ket)`; nothing else changes. -/
def peekKet (x : K) : Frag := Frag.straight (peek x readKet)

theorem peekKet_runs (x : K) (v : St) (S : Stacks) :
    (peekKet x).Runs v S
      (fun v' S' => v' = { v with flag := decide ((S x).head? = some Γ'.ket) } ∧ S' = S) 1 := by
  constructor
  intro Λ M ι e hI
  refine ⟨1, le_rfl, _, S, runsTo_succ ?_ (runsTo_zero M _), rfl, rfl⟩
  tm_step () [peekKet, Frag.straight, readKet]

/-- Peek-handler: `flag := (the symbol is blank)`. -/
def readBlank (v : St) (o : Option Γ') : St := { v with flag := decide (o = some Γ'.blank) }

/-- `flag := (top of x = blank)`; nothing else changes. -/
def peekBlank (x : K) : Frag := Frag.straight (peek x readBlank)

theorem peekBlank_runs (x : K) (v : St) (S : Stacks) :
    (peekBlank x).Runs v S
      (fun v' S' => v' = { v with flag := decide ((S x).head? = some Γ'.blank) } ∧ S' = S) 1 := by
  constructor
  intro Λ M ι e hI
  refine ⟨1, le_rfl, _, S, runsTo_succ ?_ (runsTo_zero M _), rfl, rfl⟩
  tm_step () [peekBlank, Frag.straight, readBlank]

/-! ### The slot loop -/

/-- Run `body` once per slot on `x` (each run consumes the top slot); stops
at the `blank` marker, which is left in place.  `flag` is the loop control. -/
def forSlots (x : K) (body : Frag) : Frag :=
  (peekBlank x).seq (Frag.loop (fun v => !v.flag) (body.seq (peekBlank x)))

/-- Loop invariant of `forSlots`: `i` slots processed, `P i` holds, the rest
of the slots are on `x`, `flag` says whether the slots are exhausted. -/
def SlotsInv (x : K) (sl : List (Option (List ℕ))) (xr : List Γ') (P : ℕ → Stacks → Prop)
    (i : ℕ) (w : St) (T : Stacks) : Prop :=
  i ≤ sl.length ∧ P i T ∧ T x = encSlots (sl.drop i) ++ .blank :: xr ∧
    w.flag = decide (sl.length ≤ i)

/-- The slot-loop rule: `P i S` is a stack invariant after `i` slots; the
body rule gets slot `i` explicitly on top of `x` and must leave the remaining
slots. -/
theorem forSlots_runs {x : K} {body : Frag} (sl : List (Option (List ℕ))) (xr : List Γ')
    (P : ℕ → Stacks → Prop) (t : ℕ) (v : St) (S : Stacks)
    (hS : S x = encSlots sl ++ .blank :: xr) (h0 : P 0 S)
    (hb : ∀ (i : ℕ) (hi : i < sl.length), ∀ (v : St) (S : Stacks), P i S →
      S x = encSlot sl[i] ++ (encSlots (sl.drop (i + 1)) ++ .blank :: xr) →
      body.Runs v S (fun _ S' => P (i + 1) S' ∧ S' x = encSlots (sl.drop (i + 1)) ++ .blank :: xr) t) :
    (forSlots x body).Runs v S
      (fun v' S' => v'.flag = true ∧ P sl.length S' ∧ S' x = .blank :: xr)
      (sl.length * (t + 2) + 2) := by
  refine Frag.runs_mono (Frag.seq_runs (t₂ := sl.length * (t + 2) + 1) (peekBlank_runs x v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₁, hS₁]
  have hloop := Frag.loop_runs (c := fun v => !v.flag) (B := body.seq (peekBlank x))
    (SlotsInv x sl xr P) sl.length (t + 1)
    (v := { v with flag := decide ((S x).head? = some Γ'.blank) }) (S := S)
    ⟨Nat.zero_le _, h0, by simpa using hS,
      by simp only [hS]; exact flag_encSlots_drop sl 0 xr⟩
    (fun i hi w T ⟨_, _, _, hfl⟩ => by simp [hfl]; omega)
    (fun w T ⟨_, _, _, hfl⟩ => by simp [hfl])
    (fun i hi w T ⟨_, hP, hT, _⟩ => by
      have hT' : T x = encSlot sl[i] ++ (encSlots (sl.drop (i + 1)) ++ .blank :: xr) := by
        rw [hT, List.drop_eq_getElem_cons hi, encSlots_cons]; simp
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 1)
        (hb i hi w T hP hT') fun v₂ S₂ ⟨hP₂, hS₂⟩ => ?_)
        (fun _ _ h => h) le_rfl
      refine Frag.runs_mono (peekBlank_runs x v₂ S₂) (fun v₃ S₃ ⟨hv₃, hS₃⟩ => ?_) le_rfl
      rw [hv₃, hS₃]
      exact ⟨by omega, hP₂, hS₂, by simp only [hS₂]; exact flag_encSlots_drop sl (i + 1) xr⟩)
  refine Frag.runs_mono hloop (fun v' S' ⟨⟨_, hP, hx, _⟩, hc⟩ => ⟨?_, hP, ?_⟩) (by ring_nf; omega)
  · simpa using hc
  · rw [hx, List.drop_length]; rfl

/-! ### Moving one slot -/

/-- Move the top slot of `src` onto `dst`, exactly (a `ket` is popped and
pushed; a witness list is reversed onto `s'` and reversed back); `s`, `s'`
scratch. -/
def moveSlot (src dst s s' : K) : Frag :=
  (peekKet src).seq (Frag.ite (fun v => v.flag)
    ((popTop src).seq (Frag.pushSym dst .ket))
    ((revList src s' s).seq (revList s' dst s)))

/-- Step bound of `moveSlot` on a slot with at most `N` entries below `2 ^ b`. -/
def slotC (N b : ℕ) : ℕ := N * (4 * b + 12) + 10

theorem moveSlot_runs {src dst s s' : K} (hsd : src ≠ dst) (hss : src ≠ s) (hss' : src ≠ s')
    (hds : dst ≠ s) (hds' : dst ≠ s') (hs : s ≠ s') (o : Option (List ℕ)) (N b : ℕ)
    (ho : SlotBounded N b o) (sr : List Γ') (v : St) (S : Stacks) (hS : S src = encSlot o ++ sr) :
    (moveSlot src dst s s').Runs v S (fun _ S' =>
        S' src = sr ∧ S' dst = encSlot o ++ S dst ∧ S' s = S s ∧ S' s' = S s' ∧
        ∀ k, k ≠ src → k ≠ dst → k ≠ s → k ≠ s' → S' k = S k)
      (slotC N b) := by
  have hds₀ := hsd.symm
  have hss₀ := hss.symm
  have hs'src := hss'.symm
  have hsd₀ := hds.symm
  have hs'd := hds'.symm
  have hs's := hs.symm
  unfold slotC
  refine Frag.runs_mono (Frag.seq_runs (t₂ := N * (4 * b + 12) + 9) (peekKet_runs src v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₁, hS₁]
  cases o with
  | none =>
    have hfl : decide ((S src).head? = some Γ'.ket) = true := by simp [hS]
    refine Frag.ite_runs (t := N * (4 * b + 12) + 8) (fun _ => ?_) (fun hc => absurd hc (by simp [hfl]))
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) (popTop_runs src _ S)
      fun v₂ S₂ ⟨_, hS₂⟩ => ?_) (fun _ _ h => h) (by omega)
    subst hS₂
    refine Frag.runs_mono (Frag.pushSym_runs dst .ket v₂ _) (fun _ S₃ ⟨_, hS₃⟩ => ?_) le_rfl
    subst hS₃
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [Function.update_of_ne hsd, hS]
    · simp [Function.update_of_ne hds₀]
    · simp [Function.update_of_ne hsd₀, Function.update_of_ne hss₀]
    · simp [Function.update_of_ne hs'd, Function.update_of_ne hs'src]
    · intro k hks hkd hkss hkss'
      simp [Function.update_of_ne hkd, Function.update_of_ne hks]
  | some W =>
    obtain ⟨hWN, hWb⟩ := ho W rfl
    have hfl : decide ((S src).head? = some Γ'.ket) = false := by
      rw [hS, encSlot_some]; exact decide_eq_false (head?_encList_ne_ket W sr)
    refine Frag.ite_runs (t := N * (4 * b + 12) + 8) (fun hc => absurd hc (by simp [hfl]))
      (fun _ => ?_)
    have hmul : W.length * (2 * b + 6) ≤ N * (2 * b + 6) := Nat.mul_le_mul_right _ hWN
    have hsplit : N * (4 * b + 12) = N * (2 * b + 6) + N * (2 * b + 6) := by ring
    have h1 := revList_correct hss' hss hs's W b hWb sr
      { v with flag := decide ((S src).head? = some Γ'.ket) } S hS
    refine Frag.runs_mono (Frag.seq_runs (t₂ := N * (2 * b + 6) + 4) h1
      fun v₂ S₂ ⟨hsrc₂, hs'₂, hs₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
    have hWb' : ∀ a ∈ W.reverse, a < 2 ^ b := fun a ha => hWb a (List.mem_reverse.mp ha)
    have h2 := revList_correct hs'd hs's hds W.reverse b hWb' (S s') v₂ S₂ hs'₂
    refine Frag.runs_mono h2 (fun _ S₃ ⟨hs'₃, hdst₃, hs₃, hF₃⟩ => ⟨?_, ?_, ?_, hs'₃, ?_⟩)
      (by simp only [List.length_reverse]; omega)
    · rw [hF₃ src hss' hsd hss, hsrc₂]
    · rw [hdst₃, List.reverse_reverse, hF₂ dst hds₀ hds' hds]; rfl
    · rw [hs₃, hs₂]
    · intro k hks hkd hkss hkss'
      rw [hF₃ k hkss' hkd hkss, hF₂ k hks hkss' hkss]

/-! ### Dropping a list -/

/-- Pop the list on `x` (entries and `bra`). -/
def dropList (x : K) : Frag := (forEntries x (dropNum x)).seq (popTop x)

theorem dropList_runs {x : K} (L : List (List Bool)) (m : ℕ) (hm : ∀ l ∈ L, l.length ≤ m)
    (xr : List Γ') (v : St) (S : Stacks) (hS : S x = encListB L ++ xr) :
    (dropList x).Runs v S (fun _ S' => S' x = xr ∧ ∀ k, k ≠ x → S' k = S k)
      (L.length * (m + 3) + 3) := by
  have hloop := forEntries_runs (body := dropNum x) L xr (fun _ T => ∀ k, k ≠ x → T k = S k)
    (m + 1) v S hS (fun _ _ => rfl)
    (fun i l L' hdrop w T hF hT => by
      have hl := hm l (mem_of_drop_eq_cons hdrop)
      refine Frag.runs_mono (dropNum_runs l _ w T hT)
        (fun _ T' ⟨_, _, _, hx', hF'⟩ => ⟨fun k hk => (hF' k hk).trans (hF k hk), hx'⟩) (by omega))
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) hloop
    fun v₁ S₁ ⟨_, hF₁, hx₁⟩ => ?_) (fun _ _ h => h) (by ring_nf; omega)
  refine Frag.runs_mono (popTop_runs x v₁ S₁) (fun _ S₂ ⟨_, hS₂⟩ => ?_) le_rfl
  subst hS₂
  exact ⟨by simp [hx₁], fun k hk => by rw [Function.update_of_ne hk, hF₁ k hk]⟩

theorem dropList_correct {x : K} (l : List ℕ) (b : ℕ) (hb : ∀ a ∈ l, a < 2 ^ b)
    (xr : List Γ') (v : St) (S : Stacks) (hS : S x = encList l ++ xr) :
    (dropList x).Runs v S (fun _ S' => S' x = xr ∧ ∀ k, k ≠ x → S' k = S k)
      (l.length * (b + 3) + 3) := by
  rw [encList_eq] at hS
  refine Frag.runs_mono (dropList_runs _ b (entry_length_le_of_lt_pow hb) xr v S hS)
    (fun _ _ h => h) (by simp)

/-! ### The empty table -/

/-- One iteration of `emptyTbl`: push a `ket`, decrement the counter, test it. -/
def emptyBody (c tbl s : K) : Frag :=
  (Frag.pushSym tbl .ket).seq ((predNum c s).seq (isZero c s))

/-- With `L` on `c` (consumed), push the empty table on `[0, L)` — a `blank`
marker, then `L` kets — on `tbl`; `s` scratch. -/
def emptyTbl (c tbl s : K) : Frag :=
  (Frag.pushSym tbl .blank).seq ((isZero c s).seq
    ((Frag.loop (fun v => !v.flag) (emptyBody c tbl s)).seq (dropNum c)))

/-- Loop invariant of `emptyTbl`: `i` kets pushed, counter `L - i`. -/
def EmptyInv (c tbl s : K) (L : ℕ) (cr tr sr : List Γ') (S₀ : Stacks)
    (i : ℕ) (w : St) (T : Stacks) : Prop :=
  i ≤ L ∧ T c = encodeNatΓ' (L - i) ++ .comma :: cr ∧
  T tbl = List.replicate i .ket ++ .blank :: tr ∧ T s = sr ∧
  (∀ k, k ≠ c → k ≠ tbl → k ≠ s → T k = S₀ k) ∧ w.flag = decide (L - i = 0)

theorem emptyBody_runs {c tbl s : K} (hct : c ≠ tbl) (hcs : c ≠ s) (hts : tbl ≠ s)
    (L : ℕ) (cr tr sr : List Γ') (S₀ : Stacks) (i : ℕ) (hi : i < L) (w : St) (T : Stacks)
    (hI : EmptyInv c tbl s L cr tr sr S₀ i w T) :
    (emptyBody c tbl s).Runs w T (EmptyInv c tbl s L cr tr sr S₀ (i + 1))
      (4 * Nat.log 2 L + 13) := by
  have htc := hct.symm
  have hsc := hcs.symm
  have hst := hts.symm
  obtain ⟨-, hTc, hTt, hTs, hTF, -⟩ := hI
  have hlog1 : Nat.log 2 (L - i) ≤ Nat.log 2 L := Nat.log_mono_right (by omega)
  have hlog2 : Nat.log 2 (L - i - 1) ≤ Nat.log 2 L := Nat.log_mono_right (by omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * Nat.log 2 L + 12) (Frag.pushSym_runs tbl .ket w T)
    fun w₁ T₁ ⟨_, hT₁⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hT₁
  have h2 := predNum_correct hcs (L - i) (by omega) cr w₁ (Function.update T tbl (.ket :: T tbl))
    (by rw [Function.update_of_ne hct, hTc])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * Nat.log 2 L + 7) h2
    fun w₂ T₂ ⟨_, _, hc₂, hs₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  have h3 := isZero_correct hcs (L - i - 1) cr w₂ T₂ hc₂
  refine Frag.runs_mono h3 (fun w₃ T₃ ⟨hfl₃, _, hc₃, hs₃, hF₃⟩ => ?_) (by omega)
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hc₃, hc₂, Nat.sub_sub]
  · rw [hF₃ tbl htc hts, hF₂ tbl htc hts, Function.update_self, hTt, List.replicate_succ]
    simp
  · rw [hs₃, hs₂, Function.update_of_ne hst, hTs]
  · intro k hkc hkt hks
    rw [hF₃ k hkc hks, hF₂ k hkc hks, Function.update_of_ne hkt, hTF k hkc hkt hks]
  · rw [hfl₃, Nat.sub_sub]

theorem emptyTbl_runs {c tbl s : K} (hct : c ≠ tbl) (hcs : c ≠ s) (hts : tbl ≠ s)
    (L : ℕ) (cr : List Γ') (v : St) (S : Stacks) (hS : S c = encodeNatΓ' L ++ .comma :: cr) :
    (emptyTbl c tbl s).Runs v S (fun _ S' =>
        S' c = cr ∧ S' tbl = encTblAsc L Alg.emptyTbl ++ .blank :: S tbl ∧ S' s = S s ∧
        ∀ k, k ≠ c → k ≠ tbl → k ≠ s → S' k = S k)
      (L * (4 * Nat.log 2 L + 14) + 2 * Nat.log 2 L + 11) := by
  have htc := hct.symm
  have hsc := hcs.symm
  have hst := hts.symm
  set TL := L * (4 * Nat.log 2 L + 13 + 1) + 1 with hTL
  have hTL' : TL = L * (4 * Nat.log 2 L + 14) + 1 := hTL
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL + 2 * Nat.log 2 L + 9)
    (Frag.pushSym_runs tbl .blank v S) fun v₁ S₁ ⟨_, hS₁⟩ => ?_) (fun _ _ h => h)
    (by rw [hTL']; omega)
  subst hS₁
  have h2 := isZero_correct hcs L cr v₁ (Function.update S tbl (.blank :: S tbl))
    (by rw [Function.update_of_ne hct, hS])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL + 2) h2
    fun v₂ S₂ ⟨hfl₂, _, hc₂, hs₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  have hloop := Frag.loop_runs (c := fun v => !v.flag) (B := emptyBody c tbl s)
    (EmptyInv c tbl s L cr (S tbl) (S s) S) L (4 * Nat.log 2 L + 13) (v := v₂) (S := S₂)
    ⟨Nat.zero_le _, by rw [hc₂, Function.update_of_ne hct, hS, Nat.sub_zero],
      by rw [hF₂ tbl htc hts, Function.update_self]; rfl,
      by rw [hs₂, Function.update_of_ne hst],
      fun k hkc hkt hks => by rw [hF₂ k hkc hks, Function.update_of_ne hkt],
      by rw [hfl₂, Nat.sub_zero]⟩
    (fun i hi w T ⟨_, _, _, _, _, hfl⟩ => by simp [hfl]; omega)
    (fun w T ⟨_, _, _, _, _, hfl⟩ => by simp [hfl])
    (fun i hi w T hI => emptyBody_runs hct hcs hts L cr (S tbl) (S s) S i hi w T hI)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2) hloop
    fun v₃ S₃ ⟨⟨_, hc₃, ht₃, hs₃, hF₃, _⟩, _⟩ => ?_) (fun _ _ h => h) le_rfl
  rw [Nat.sub_self] at hc₃
  have h4 := dropNum_correct 0 cr v₃ S₃ hc₃
  refine Frag.runs_mono h4 (fun _ S₄ ⟨_, _, _, hc₄, hF₄⟩ => ⟨hc₄, ?_, ?_, ?_⟩)
    (by rw [Nat.log_zero_right])
  · rw [hF₄ tbl htc, ht₃, encTblAsc_emptyTbl]
  · rw [hF₄ s hsc, hs₃]
  · intro k hkc hkt hks; rw [hF₄ k hkc, hF₃ k hkc hkt hks]

/-! ### The slot walk -/

/-- One step of the walk: move the top slot of `tbl` onto `scr`, decrement
the counter on `j`, test it. -/
def walkBody (tbl j s scr : K) : Frag :=
  (moveSlot tbl scr s j).seq ((predNum j s).seq (isZero j s))

/-- Move the first `j` slots of the table on `tbl` onto `scr` (above a `blank`
marker), consuming the counter on `j`; `s` scratch, `j` also used as scratch. -/
def walkDown (tbl j s scr : K) : Frag :=
  (Frag.pushSym scr .blank).seq ((isZero j s).seq
    ((Frag.loop (fun v => !v.flag) (walkBody tbl j s scr)).seq (dropNum j)))

/-- Move the slots on `scr` (down to the `blank` marker, which is popped)
back onto `tbl`; `s`, `j` scratch. -/
def walkUp (tbl j s scr : K) : Frag :=
  (forSlots scr (moveSlot scr tbl s j)).seq (popTop scr)

/-- Loop invariant of `walkDown`: `i` slots moved, counter `jn - i` (as a
bit list no longer than the original). -/
def WalkInv (tbl j s scr : K) (sl : List (Option (List ℕ))) (m jn : ℕ) (tr jr sr scrr : List Γ')
    (S₀ : Stacks) (i : ℕ) (w : St) (T : Stacks) : Prop :=
  i ≤ jn ∧ (∃ l : List Bool, toNat l = jn - i ∧ l.length ≤ m ∧ T j = bits l ++ .comma :: jr) ∧
  T tbl = encSlots (sl.drop i) ++ tr ∧ T scr = encSlots (sl.take i).reverse ++ .blank :: scrr ∧
  T s = sr ∧ (∀ k, k ≠ tbl → k ≠ j → k ≠ s → k ≠ scr → T k = S₀ k) ∧
  w.flag = decide (jn - i = 0)

theorem walkBody_runs {tbl j s scr : K} (htj : tbl ≠ j) (hts : tbl ≠ s) (htc : tbl ≠ scr)
    (hjs : j ≠ s) (hjc : j ≠ scr) (hsc : s ≠ scr) (sl : List (Option (List ℕ))) (N b : ℕ)
    (hsl : ∀ o ∈ sl, SlotBounded N b o) (m jn : ℕ) (hjn : jn < sl.length)
    (tr jr sr scrr : List Γ') (S₀ : Stacks) (i : ℕ) (hi : i < jn) (w : St) (T : Stacks)
    (hI : WalkInv tbl j s scr sl m jn tr jr sr scrr S₀ i w T) :
    (walkBody tbl j s scr).Runs w T (WalkInv tbl j s scr sl m jn tr jr sr scrr S₀ (i + 1))
      (slotC N b + 4 * m + 8) := by
  have hjt := htj.symm
  have hst := hts.symm
  have hct := htc.symm
  have hsj := hjs.symm
  have hcj := hjc.symm
  have hcs := hsc.symm
  obtain ⟨-, ⟨l, hl, hlm, hTj⟩, hTt, hTc, hTs, hTF, -⟩ := hI
  have hisl : i < sl.length := by omega
  have hTt' : T tbl = encSlot sl[i] ++ (encSlots (sl.drop (i + 1)) ++ tr) := by
    rw [hTt, List.drop_eq_getElem_cons hisl, encSlots_cons, List.append_assoc]
  -- moveSlot tbl scr s j
  have h1 := moveSlot_runs htc hts htj hcs hcj hsj sl[i] N b (hsl _ (List.getElem_mem hisl)) _ w T hTt'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * m + 8) h1
    fun w₁ T₁ ⟨ht₁, hc₁, hs₁, hj₁, hF₁⟩ => ?_) (fun _ _ h => h) le_rfl
  -- predNum j s
  have h2 := predNum_runs hjs l jr w₁ T₁ (by rw [hj₁, hTj])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * m + 5) h2
    fun w₂ T₂ ⟨_, _, hj₂, hs₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- isZero j s
  have h3 := isZero_runs hjs (predBits l) jr w₂ T₂ hj₂
  refine Frag.runs_mono h3 (fun w₃ T₃ ⟨hfl₃, _, hj₃, hs₃, hF₃⟩ => ?_) (by have := predBits_length l; omega)
  have hpred : toNat (predBits l) = jn - (i + 1) := by
    have := toNat_predBits l (by omega); omega
  refine ⟨by omega, ⟨predBits l, hpred, (predBits_length l).trans hlm, by rw [hj₃, hj₂]⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF₃ tbl htj hts, hF₂ tbl htj hts, ht₁]
  · rw [hF₃ scr hcj hcs, hF₂ scr hcj hcs, hc₁, hTc, List.take_succ_eq_append_getElem hisl,
      List.reverse_append, List.reverse_singleton, List.singleton_append, encSlots_cons,
      List.append_assoc]
  · rw [hs₃, hs₂, hs₁, hTs]
  · intro k hkt hkj hks hkc
    rw [hF₃ k hkj hks, hF₂ k hkj hks, hF₁ k hkt hkc hks hkj, hTF k hkt hkj hks hkc]
  · rw [hfl₃, hpred]

theorem walkDown_runs {tbl j s scr : K} (htj : tbl ≠ j) (hts : tbl ≠ s) (htc : tbl ≠ scr)
    (hjs : j ≠ s) (hjc : j ≠ scr) (hsc : s ≠ scr) (sl : List (Option (List ℕ))) (N b : ℕ)
    (hsl : ∀ o ∈ sl, SlotBounded N b o) (js : List Bool) (m : ℕ) (hm : js.length ≤ m)
    (hjn : toNat js < sl.length) (tr jr : List Γ') (v : St) (S : Stacks)
    (hSt : S tbl = encSlots sl ++ tr) (hSj : S j = bits js ++ .comma :: jr) :
    (walkDown tbl j s scr).Runs v S (fun _ S' =>
        S' tbl = encSlots (sl.drop (toNat js)) ++ tr ∧ S' j = jr ∧
        S' scr = encSlots (sl.take (toNat js)).reverse ++ .blank :: S scr ∧ S' s = S s ∧
        ∀ k, k ≠ tbl → k ≠ j → k ≠ s → k ≠ scr → S' k = S k)
      (toNat js * (slotC N b + 4 * m + 9) + 3 * m + 8) := by
  have hjt := htj.symm
  have hst := hts.symm
  have hct := htc.symm
  have hsj := hjs.symm
  have hcj := hjc.symm
  have hcs := hsc.symm
  set jn := toNat js with hjn'
  set TL := jn * (slotC N b + 4 * m + 8 + 1) + 1 with hTL
  have hTL' : TL = jn * (slotC N b + 4 * m + 9) + 1 := hTL
  -- stage 1: the marker
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL + 3 * m + 6)
    (Frag.pushSym_runs scr .blank v S) fun v₁ S₁ ⟨_, hS₁⟩ => ?_) (fun _ _ h => h)
    (by rw [hTL']; omega)
  subst hS₁
  -- stage 2: isZero j s
  have h2 := isZero_runs hjs js jr v₁ (Function.update S scr (.blank :: S scr))
    (by rw [Function.update_of_ne hjc, hSj])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL + m + 1) h2
    fun v₂ S₂ ⟨hfl₂, _, hj₂, hs₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: the loop
  have hloop := Frag.loop_runs (c := fun v => !v.flag) (B := walkBody tbl j s scr)
    (WalkInv tbl j s scr sl m jn tr jr (S s) (S scr) S) jn (slotC N b + 4 * m + 8)
    (v := v₂) (S := S₂)
    ⟨Nat.zero_le _, ⟨js, by rw [Nat.sub_zero], hm, by rw [hj₂, Function.update_of_ne hjc, hSj]⟩,
      by rw [hF₂ tbl htj hts, Function.update_of_ne htc, hSt, List.drop_zero],
      by rw [hF₂ scr hcj hcs, Function.update_self]; rfl,
      by rw [hs₂, Function.update_of_ne hsc],
      fun k hkt hkj hks hkc => by rw [hF₂ k hkj hks, Function.update_of_ne hkc],
      by rw [hfl₂, Nat.sub_zero]⟩
    (fun i hi w T ⟨_, _, _, _, _, _, hfl⟩ => by simp [hfl]; omega)
    (fun w T ⟨_, _, _, _, _, _, hfl⟩ => by simp [hfl])
    (fun i hi w T hI => walkBody_runs htj hts htc hjs hjc hsc sl N b hsl m jn hjn tr jr (S s) (S scr)
      S i hi w T hI)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := m + 1) hloop
    fun v₃ S₃ ⟨⟨_, ⟨l, _, hlm, hj₃⟩, ht₃, hc₃, hs₃, hF₃, _⟩, _⟩ => ?_) (fun _ _ h => h) le_rfl
  -- stage 4: drop the counter
  have h4 := dropNum_runs l jr v₃ S₃ hj₃
  refine Frag.runs_mono h4 (fun _ S₄ ⟨_, _, _, hj₄, hF₄⟩ => ⟨?_, hj₄, ?_, ?_, ?_⟩) (by omega)
  · rw [hF₄ tbl htj, ht₃]
  · rw [hF₄ scr hcj, hc₃]
  · rw [hF₄ s hsj, hs₃]
  · intro k hkt hkj hks hkc; rw [hF₄ k hkj, hF₃ k hkt hkj hks hkc]

theorem walkUp_runs {tbl j s scr : K} (htj : tbl ≠ j) (hts : tbl ≠ s) (htc : tbl ≠ scr)
    (hjs : j ≠ s) (hjc : j ≠ scr) (hsc : s ≠ scr) (R sl₂ : List (Option (List ℕ))) (N b : ℕ)
    (hR : ∀ o ∈ R, SlotBounded N b o) (tr scrr : List Γ') (v : St) (S : Stacks)
    (hSc : S scr = encSlots R ++ .blank :: scrr) (hSt : S tbl = encSlots sl₂ ++ tr) :
    (walkUp tbl j s scr).Runs v S (fun _ S' =>
        S' tbl = encSlots (R.reverse ++ sl₂) ++ tr ∧ S' scr = scrr ∧ S' s = S s ∧ S' j = S j ∧
        ∀ k, k ≠ tbl → k ≠ j → k ≠ s → k ≠ scr → S' k = S k)
      (R.length * (slotC N b + 2) + 3) := by
  have hjt := htj.symm
  have hst := hts.symm
  have hct := htc.symm
  have hsj := hjs.symm
  have hcj := hjc.symm
  have hcs := hsc.symm
  have hloop := forSlots_runs (body := moveSlot scr tbl s j) R scrr
    (fun i T => T tbl = encSlots ((R.take i).reverse ++ sl₂) ++ tr ∧ T s = S s ∧ T j = S j ∧
      ∀ k, k ≠ tbl → k ≠ j → k ≠ s → k ≠ scr → T k = S k)
    (slotC N b) v S hSc ⟨by simpa using hSt, rfl, rfl, fun _ _ _ _ _ => rfl⟩
    (fun i hi w T ⟨hTt, hTs, hTj, hTF⟩ hTc => by
      have h1 := moveSlot_runs hct hcs hcj hts htj hsj R[i] N b (hR _ (List.getElem_mem hi)) _ w T hTc
      refine Frag.runs_mono h1 (fun _ T' ⟨hc', ht', hs', hj', hF'⟩ => ⟨⟨?_, hs'.trans hTs, hj'.trans hTj, ?_⟩, hc'⟩)
        le_rfl
      · rw [ht', hTt, List.take_succ_eq_append_getElem hi, List.reverse_append,
          List.reverse_singleton, List.singleton_append, List.cons_append, encSlots_cons,
          List.append_assoc]
      · intro k hkt hkj hks hkc
        rw [hF' k hkc hkt hks hkj, hTF k hkt hkj hks hkc])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) hloop
    fun v₁ S₁ ⟨_, ⟨ht₁, hs₁, hj₁, hF₁⟩, hc₁⟩ => ?_) (fun _ _ h => h) (by ring_nf; omega)
  refine Frag.runs_mono (popTop_runs scr v₁ S₁) (fun _ S₂ ⟨_, hS₂⟩ => ?_) le_rfl
  subst hS₂
  refine ⟨?_, by simp [hc₁], ?_, ?_, ?_⟩
  · rw [Function.update_of_ne htc, ht₁, List.take_length]
  · rw [Function.update_of_ne hsc, hs₁]
  · rw [Function.update_of_ne hjc, hj₁]
  · intro k hkt hkj hks hkc; rw [Function.update_of_ne hkc, hF₁ k hkt hkj hks hkc]

/-! ### Set-if-none -/

/-- `Alg.setIfNone` on the table on `tbl`: walk down `j` slots (the index on
`j`, consumed), and if the slot there is `ket`, replace it by the witness on
`w` (consumed either way); walk back.  `s`, `scr` scratch. -/
def setIfNoneF (tbl j w s scr : K) : Frag :=
  (walkDown tbl j s scr).seq ((peekKet tbl).seq
    ((Frag.ite (fun v => v.flag) ((popTop tbl).seq (moveSlot w tbl s j)) (dropList w)).seq
      (walkUp tbl j s scr)))

/-- Step bound of `setIfNoneF` at index `j` on a table of slots with at most
`N` entries below `2 ^ b`, index bit length `≤ m`. -/
def setC (j N b m : ℕ) : ℕ := j * (2 * slotC N b + 4 * m + 11) + slotC N b + 3 * m + 14

theorem setIfNoneF_runs {tbl j w s scr : K} (htj : tbl ≠ j) (htw : tbl ≠ w) (hts : tbl ≠ s)
    (htc : tbl ≠ scr) (hjw : j ≠ w) (hjs : j ≠ s) (hjc : j ≠ scr) (hws : w ≠ s) (hwc : w ≠ scr)
    (hsc : s ≠ scr) (sl : List (Option (List ℕ))) (N b : ℕ) (hsl : ∀ o ∈ sl, SlotBounded N b o)
    (js : List Bool) (m : ℕ) (hm : js.length ≤ m) (hjn : toNat js < sl.length)
    (W : List ℕ) (hWN : W.length ≤ N) (hWb : ∀ q ∈ W, q < 2 ^ b)
    (tr jr wr : List Γ') (v : St) (S : Stacks)
    (hSt : S tbl = encSlots sl ++ tr) (hSj : S j = bits js ++ .comma :: jr)
    (hSw : S w = encList W ++ wr) :
    (setIfNoneF tbl j w s scr).Runs v S (fun _ S' =>
        S' tbl = encSlots (setSlotL sl (toNat js) W) ++ tr ∧ S' j = jr ∧ S' w = wr ∧
        S' s = S s ∧ S' scr = S scr ∧
        ∀ k, k ≠ tbl → k ≠ j → k ≠ w → k ≠ s → k ≠ scr → S' k = S k)
      (setC (toNat js) N b m) := by
  have hjt := htj.symm
  have hwt := htw.symm
  have hst := hts.symm
  have hct := htc.symm
  have hwj := hjw.symm
  have hsj := hjs.symm
  have hcj := hjc.symm
  have hsw := hws.symm
  have hcw := hwc.symm
  have hcs := hsc.symm
  unfold setC
  have hsplit : (toNat js) * (2 * slotC N b + 4 * m + 11) =
      (toNat js) * (slotC N b + 4 * m + 9) + (toNat js) * (slotC N b + 2) := by ring
  -- stage 1: walk down
  have h1 := walkDown_runs htj hts htc hjs hjc hsc sl N b hsl js m hm hjn tr jr v S hSt hSj
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (toNat js) * (slotC N b + 2) + slotC N b + 6) h1
    fun v₁ S₁ ⟨ht₁, hj₁, hc₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  have ht₁' : S₁ tbl = encSlot sl[(toNat js)] ++ (encSlots (sl.drop ((toNat js) + 1)) ++ tr) := by
    rw [ht₁, List.drop_eq_getElem_cons hjn, encSlots_cons, List.append_assoc]
  -- stage 2: peek
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (toNat js) * (slotC N b + 2) + slotC N b + 5)
    (peekKet_runs tbl v₁ S₁) fun v₂ S₂ ⟨hv₂, hS₂⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hS₂]
  have hfl₂ : v₂.flag = decide (sl[(toNat js)] = none) := by
    rw [hv₂]; simp only; rw [ht₁', decide_head?_encSlot_ket]
  -- stage 3: the conditional
  have hw₁ : S₁ w = encList W ++ wr := by rw [hF₁ w hwt hwj hws hwc, hSw]
  have h3 : (Frag.ite (fun v => v.flag) ((popTop tbl).seq (moveSlot w tbl s j)) (dropList w)).Runs
      v₂ S₁ (fun _ T => T tbl = encSlots (fillSlot W sl[(toNat js)] :: sl.drop ((toNat js) + 1)) ++ tr ∧ T w = wr ∧
        T s = S₁ s ∧ T j = S₁ j ∧ ∀ k, k ≠ tbl → k ≠ w → k ≠ s → k ≠ j → T k = S₁ k)
      (slotC N b + 2) := by
    refine Frag.ite_runs (fun hc => ?_) (fun hc => ?_)
    · rw [hfl₂, decide_eq_true_eq] at hc
      refine Frag.runs_mono (Frag.seq_runs (t₂ := slotC N b) (popTop_runs tbl v₂ S₁)
        fun v₃ S₃ ⟨_, hS₃⟩ => ?_) (fun _ _ h => h) (by omega)
      subst hS₃
      have hw₃ : Function.update S₁ tbl (S₁ tbl).tail w = encSlot (some W) ++ wr := by
        rw [Function.update_of_ne hwt, hw₁]; rfl
      have h4 := moveSlot_runs hwt hws hwj hts htj hsj (some W) N b
        (fun V hV => by cases hV; exact ⟨hWN, hWb⟩) wr v₃ _ hw₃
      refine Frag.runs_mono h4 (fun _ T ⟨hw', ht', hs', hj', hF'⟩ => ⟨?_, hw', ?_, ?_, ?_⟩) le_rfl
      · rw [ht', Function.update_self, ht₁', hc, encSlot_none, List.singleton_append, List.tail_cons,
          encSlots_cons, List.append_assoc]
        rfl
      · rw [hs', Function.update_of_ne hst]
      · rw [hj', Function.update_of_ne hjt]
      · intro k hkt hkw hks hkj
        rw [hF' k hkw hkt hks hkj, Function.update_of_ne hkt]
    · rw [hfl₂, decide_eq_false_iff_not] at hc
      obtain ⟨V, hV⟩ := Option.ne_none_iff_exists'.mp hc
      have h4 := dropList_correct W b hWb wr v₂ S₁ hw₁
      refine Frag.runs_mono h4 (fun _ T ⟨hw', hF'⟩ => ⟨?_, hw', hF' s hsw, hF' j hjw, ?_⟩) ?_
      · rw [hF' tbl htw, ht₁', hV, encSlots_cons, List.append_assoc]; rfl
      · intro k hkt hkw hks hkj; exact hF' k hkw
      · have : W.length * (b + 3) ≤ N * (4 * b + 12) := by
          calc W.length * (b + 3) ≤ N * (b + 3) := Nat.mul_le_mul_right _ hWN
            _ ≤ N * (4 * b + 12) := Nat.mul_le_mul_left _ (by omega)
        unfold slotC; omega
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (toNat js) * (slotC N b + 2) + 3) h3
    fun v₃ S₃ ⟨ht₃, hw₃, hs₃, hj₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 4: walk up
  have hc₃ : S₃ scr = encSlots (sl.take (toNat js)).reverse ++ .blank :: S scr := by
    rw [hF₃ scr hct hcw hcs hcj, hc₁]
  have hR : ∀ o ∈ (sl.take (toNat js)).reverse, SlotBounded N b o :=
    fun o ho => hsl o (List.mem_of_mem_take (List.mem_reverse.mp ho))
  have h4 := walkUp_runs htj hts htc hjs hjc hsc _ _ N b hR tr (S scr) v₃ S₃ hc₃ ht₃
  refine Frag.runs_mono h4 (fun _ S₄ ⟨ht₄, hc₄, hs₄, hj₄, hF₄⟩ => ⟨?_, ?_, ?_, ?_, hc₄, ?_⟩) ?_
  · rw [ht₄, List.reverse_reverse, setSlotL_eq_take_cons_drop hjn]
  · rw [hj₄, hj₃, hj₁]
  · rw [hF₄ w hwt hwj hws hwc, hw₃]
  · rw [hs₄, hs₃, hs₁]
  · intro k hkt hkj hkw hks hkc
    rw [hF₄ k hkt hkj hks hkc, hF₃ k hkt hkw hks hkj, hF₁ k hkt hkj hks hkc]
  · rw [List.length_reverse, List.length_take, min_eq_left hjn.le]

/-! ### Slot lookup -/

/-- Copy slot `j` of the table on `tbl` (index on `j`, consumed) onto `w`,
table restored; `s`, `scr` scratch. -/
def lookupSlot (tbl j w s scr : K) : Frag :=
  (walkDown tbl j s scr).seq ((peekKet tbl).seq
    ((Frag.ite (fun v => v.flag) (Frag.pushSym w .ket) (copyList tbl w s j)).seq
      (walkUp tbl j s scr)))

/-- Step bound of `lookupSlot`. -/
def lookC (j N b m : ℕ) : ℕ :=
  j * (2 * slotC N b + 4 * m + 11) + N * (6 * b + 17) + 3 * m + 22

theorem lookupSlot_runs {tbl j w s scr : K} (htj : tbl ≠ j) (htw : tbl ≠ w) (hts : tbl ≠ s)
    (htc : tbl ≠ scr) (hjw : j ≠ w) (hjs : j ≠ s) (hjc : j ≠ scr) (hws : w ≠ s) (hwc : w ≠ scr)
    (hsc : s ≠ scr) (sl : List (Option (List ℕ))) (N b : ℕ) (hsl : ∀ o ∈ sl, SlotBounded N b o)
    (js : List Bool) (m : ℕ) (hm : js.length ≤ m) (hjn : toNat js < sl.length)
    (tr jr : List Γ') (v : St) (S : Stacks)
    (hSt : S tbl = encSlots sl ++ tr) (hSj : S j = bits js ++ .comma :: jr) :
    (lookupSlot tbl j w s scr).Runs v S (fun _ S' =>
        S' tbl = S tbl ∧ S' j = jr ∧ S' w = encSlot sl[toNat js] ++ S w ∧
        S' s = S s ∧ S' scr = S scr ∧
        ∀ k, k ≠ tbl → k ≠ j → k ≠ w → k ≠ s → k ≠ scr → S' k = S k)
      (lookC (toNat js) N b m) := by
  have hjt := htj.symm
  have hwt := htw.symm
  have hst := hts.symm
  have hct := htc.symm
  have hwj := hjw.symm
  have hsj := hjs.symm
  have hcj := hjc.symm
  have hsw := hws.symm
  have hcw := hwc.symm
  have hcs := hsc.symm
  unfold lookC
  have hsplit : (toNat js) * (2 * slotC N b + 4 * m + 11) =
      (toNat js) * (slotC N b + 4 * m + 9) + (toNat js) * (slotC N b + 2) := by ring
  -- stage 1: walk down
  have h1 := walkDown_runs htj hts htc hjs hjc hsc sl N b hsl js m hm hjn tr jr v S hSt hSj
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (toNat js) * (slotC N b + 2) + N * (6 * b + 17) + 14) h1
    fun v₁ S₁ ⟨ht₁, hj₁, hc₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  have ht₁' : S₁ tbl = encSlot sl[(toNat js)] ++ (encSlots (sl.drop ((toNat js) + 1)) ++ tr) := by
    rw [ht₁, List.drop_eq_getElem_cons hjn, encSlots_cons, List.append_assoc]
  -- stage 2: peek
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (toNat js) * (slotC N b + 2) + N * (6 * b + 17) + 13)
    (peekKet_runs tbl v₁ S₁) fun v₂ S₂ ⟨hv₂, hS₂⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hS₂]
  have hfl₂ : v₂.flag = decide (sl[(toNat js)] = none) := by
    rw [hv₂]; simp only; rw [ht₁', decide_head?_encSlot_ket]
  -- stage 3: the conditional
  have h3 : (Frag.ite (fun v => v.flag) (Frag.pushSym w .ket) (copyList tbl w s j)).Runs
      v₂ S₁ (fun _ T => T tbl = S₁ tbl ∧ T w = encSlot sl[(toNat js)] ++ S₁ w ∧
        T s = S₁ s ∧ T j = S₁ j ∧ ∀ k, k ≠ tbl → k ≠ w → k ≠ s → k ≠ j → T k = S₁ k)
      (N * (6 * b + 17) + 10) := by
    refine Frag.ite_runs (fun hc => ?_) (fun hc => ?_)
    · rw [hfl₂, decide_eq_true_eq] at hc
      refine Frag.runs_mono (Frag.pushSym_runs w .ket v₂ S₁) (fun _ T ⟨_, hT⟩ => ?_) (by omega)
      subst hT
      refine ⟨Function.update_of_ne htw _ _, ?_, Function.update_of_ne hsw _ _,
        Function.update_of_ne hjw _ _, fun k _ hkw _ _ => Function.update_of_ne hkw _ _⟩
      rw [Function.update_self, hc]; rfl
    · rw [hfl₂, decide_eq_false_iff_not] at hc
      obtain ⟨V, hV⟩ := Option.ne_none_iff_exists'.mp hc
      obtain ⟨hVN, hVb⟩ := hsl _ (List.getElem_mem hjn) V hV
      have ht₁'' : S₁ tbl = encList V ++ (encSlots (sl.drop ((toNat js) + 1)) ++ tr) := by
        rw [ht₁', hV]; rfl
      have h4 := copyList_correct htw hts htj hws hwj hsj V b hVb _ v₂ S₁ ht₁''
      refine Frag.runs_mono h4 (fun _ T ⟨ht', hw', hs', hj', hF'⟩ => ⟨ht', ?_, hs', hj', ?_⟩) ?_
      · rw [hw', hV]; rfl
      · intro k hkt hkw hks hkj; exact hF' k hkt hkw hks hkj
      · have : V.length * (6 * b + 17) ≤ N * (6 * b + 17) := Nat.mul_le_mul_right _ hVN
        omega
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (toNat js) * (slotC N b + 2) + 3) h3
    fun v₃ S₃ ⟨ht₃, hw₃, hs₃, hj₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 4: walk up
  have hc₃ : S₃ scr = encSlots (sl.take (toNat js)).reverse ++ .blank :: S scr := by
    rw [hF₃ scr hct hcw hcs hcj, hc₁]
  have hR : ∀ o ∈ (sl.take (toNat js)).reverse, SlotBounded N b o :=
    fun o ho => hsl o (List.mem_of_mem_take (List.mem_reverse.mp ho))
  have h4 := walkUp_runs htj hts htc hjs hjc hsc _ _ N b hR tr (S scr) v₃ S₃ hc₃ (ht₃.trans ht₁)
  refine Frag.runs_mono h4 (fun _ S₄ ⟨ht₄, hc₄, hs₄, hj₄, hF₄⟩ => ⟨?_, ?_, ?_, ?_, hc₄, ?_⟩) ?_
  · rw [ht₄, List.reverse_reverse, List.take_append_drop, hSt]
  · rw [hj₄, hj₃, hj₁]
  · rw [hF₄ w hwt hwj hws hwc, hw₃, hF₁ w hwt hwj hws hwc]
  · rw [hs₄, hs₃, hs₁]
  · intro k hkt hkj hkw hks hkc
    rw [hF₄ k hkt hkj hks hkc, hF₃ k hkt hkw hks hkj, hF₁ k hkt hkj hks hkc]
  · rw [List.length_reverse, List.length_take, min_eq_left hjn.le]

/-! ### Table-level forms -/

theorem setIfNoneF_tbl {tbl j w s scr : K} (htj : tbl ≠ j) (htw : tbl ≠ w) (hts : tbl ≠ s)
    (htc : tbl ≠ scr) (hjw : j ≠ w) (hjs : j ≠ s) (hjc : j ≠ scr) (hws : w ≠ s) (hwc : w ≠ scr)
    (hsc : s ≠ scr) (L : ℕ) (t : Alg.Tbl) (N b : ℕ) (ht : TblBounded L t N b)
    (js : List Bool) (m : ℕ) (hm : js.length ≤ m) (hjn : toNat js < L)
    (W : List ℕ) (hWN : W.length ≤ N) (hWb : ∀ q ∈ W, q < 2 ^ b)
    (tr jr wr : List Γ') (v : St) (S : Stacks)
    (hSt : S tbl = encTblAsc L t ++ tr) (hSj : S j = bits js ++ .comma :: jr)
    (hSw : S w = encList W ++ wr) :
    (setIfNoneF tbl j w s scr).Runs v S (fun _ S' =>
        S' tbl = encTblAsc L (Alg.setIfNone t (toNat js) W) ++ tr ∧ S' j = jr ∧ S' w = wr ∧
        S' s = S s ∧ S' scr = S scr ∧
        ∀ k, k ≠ tbl → k ≠ j → k ≠ w → k ≠ s → k ≠ scr → S' k = S k)
      (setC (toNat js) N b m) := by
  rw [encTblAsc_eq] at hSt
  refine Frag.runs_mono (setIfNoneF_runs htj htw hts htc hjw hjs hjc hws hwc hsc _ N b
    (tblBounded_map_range ht) js m hm (by simpa using hjn) W hWN hWb tr jr wr v S hSt hSj hSw)
    (fun _ S' ⟨h1, h2⟩ => ⟨?_, h2⟩) le_rfl
  rw [h1, encTblAsc_eq, map_range_setIfNone L t hjn]

theorem lookupSlot_tbl {tbl j w s scr : K} (htj : tbl ≠ j) (htw : tbl ≠ w) (hts : tbl ≠ s)
    (htc : tbl ≠ scr) (hjw : j ≠ w) (hjs : j ≠ s) (hjc : j ≠ scr) (hws : w ≠ s) (hwc : w ≠ scr)
    (hsc : s ≠ scr) (L : ℕ) (t : Alg.Tbl) (N b : ℕ) (ht : TblBounded L t N b)
    (js : List Bool) (m : ℕ) (hm : js.length ≤ m) (hjn : toNat js < L)
    (tr jr : List Γ') (v : St) (S : Stacks)
    (hSt : S tbl = encTblAsc L t ++ tr) (hSj : S j = bits js ++ .comma :: jr) :
    (lookupSlot tbl j w s scr).Runs v S (fun _ S' =>
        S' tbl = S tbl ∧ S' j = jr ∧ S' w = encSlot (t (toNat js)) ++ S w ∧
        S' s = S s ∧ S' scr = S scr ∧
        ∀ k, k ≠ tbl → k ≠ j → k ≠ w → k ≠ s → k ≠ scr → S' k = S k)
      (lookC (toNat js) N b m) := by
  rw [encTblAsc_eq] at hSt
  refine Frag.runs_mono (lookupSlot_runs htj htw hts htc hjw hjs hjc hws hwc hsc _ N b
    (tblBounded_map_range ht) js m hm (by simpa using hjn) tr jr v S hSt hSj)
    (fun _ S' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, ?_, h4⟩) le_rfl
  rw [h3]; simp

/-! ### Reversing the slot order -/

/-- Move the table on `src` (down to its `blank`, consumed) onto `dst` slot by
slot, so the slot order is reversed and each slot is intact; a fresh `blank`
is pushed on `dst` first.  `s`, `s'` scratch. -/
def revTbl (src dst s s' : K) : Frag :=
  (Frag.pushSym dst .blank).seq ((forSlots src (moveSlot src dst s s')).seq (popTop src))

theorem revTbl_runs {src dst s s' : K} (hsd : src ≠ dst) (hss : src ≠ s) (hss' : src ≠ s')
    (hds : dst ≠ s) (hds' : dst ≠ s') (hs : s ≠ s') (sl : List (Option (List ℕ))) (N b : ℕ)
    (hsl : ∀ o ∈ sl, SlotBounded N b o) (sr : List Γ') (v : St) (S : Stacks)
    (hS : S src = encSlots sl ++ .blank :: sr) :
    (revTbl src dst s s').Runs v S (fun _ S' =>
        S' src = sr ∧ S' dst = encSlots sl.reverse ++ .blank :: S dst ∧ S' s = S s ∧ S' s' = S s' ∧
        ∀ k, k ≠ src → k ≠ dst → k ≠ s → k ≠ s' → S' k = S k)
      (sl.length * (slotC N b + 2) + 4) := by
  have hds₀ := hsd.symm
  have hss₀ := hss.symm
  have hs'src := hss'.symm
  have hsd₀ := hds.symm
  have hs'd := hds'.symm
  have hs's := hs.symm
  refine Frag.runs_mono (Frag.seq_runs (t₂ := sl.length * (slotC N b + 2) + 3)
    (Frag.pushSym_runs dst .blank v S) fun v₁ S₁ ⟨_, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₁
  have hloop := forSlots_runs (body := moveSlot src dst s s') sl sr
    (fun i T => T dst = encSlots (sl.take i).reverse ++ .blank :: S dst ∧ T s = S s ∧ T s' = S s' ∧
      ∀ k, k ≠ src → k ≠ dst → k ≠ s → k ≠ s' → T k = S k)
    (slotC N b) v₁ (Function.update S dst (.blank :: S dst)) (by rw [Function.update_of_ne hsd, hS])
    ⟨by simp, Function.update_of_ne hsd₀ _ _, Function.update_of_ne hs'd _ _,
      fun k _ hkd _ _ => Function.update_of_ne hkd _ _⟩
    (fun i hi w T ⟨hTd, hTs, hTs', hTF⟩ hTsrc => by
      have h1 := moveSlot_runs hsd hss hss' hds hds' hs sl[i] N b (hsl _ (List.getElem_mem hi)) _
        w T hTsrc
      refine Frag.runs_mono h1 (fun _ T' ⟨hsrc', hd', hs', hs'', hF'⟩ =>
        ⟨⟨?_, hs'.trans hTs, hs''.trans hTs', ?_⟩, hsrc'⟩) le_rfl
      · rw [hd', hTd, List.take_succ_eq_append_getElem hi, List.reverse_append,
          List.reverse_singleton, List.singleton_append, encSlots_cons, List.append_assoc]
      · intro k hks hkd hkss hkss'
        rw [hF' k hks hkd hkss hkss', hTF k hks hkd hkss hkss'])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) hloop
    fun v₂ S₂ ⟨_, ⟨hd₂, hs₂, hs'₂, hF₂⟩, hsrc₂⟩ => ?_) (fun _ _ h => h) (by ring_nf; omega)
  refine Frag.runs_mono (popTop_runs src v₂ S₂) (fun _ S₃ ⟨_, hS₃⟩ => ?_) le_rfl
  subst hS₃
  refine ⟨by simp [hsrc₂], ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne hds₀, hd₂, List.take_length]
  · rw [Function.update_of_ne hss₀, hs₂]
  · rw [Function.update_of_ne hs'src, hs'₂]
  · intro k hks hkd hkss hkss'; rw [Function.update_of_ne hks, hF₂ k hks hkd hkss hkss']

/-- `revTbl` on a table: ascending in, descending out. -/
theorem revTbl_tbl {src dst s s' : K} (hsd : src ≠ dst) (hss : src ≠ s) (hss' : src ≠ s')
    (hds : dst ≠ s) (hds' : dst ≠ s') (hs : s ≠ s') (L : ℕ) (t : Alg.Tbl) (N b : ℕ)
    (ht : TblBounded L t N b) (sr : List Γ') (v : St) (S : Stacks)
    (hS : S src = encTblAsc L t ++ .blank :: sr) :
    (revTbl src dst s s').Runs v S (fun _ S' =>
        S' src = sr ∧ S' dst = encTblDesc L t ++ .blank :: S dst ∧ S' s = S s ∧ S' s' = S s' ∧
        ∀ k, k ≠ src → k ≠ dst → k ≠ s → k ≠ s' → S' k = S k)
      (L * (slotC N b + 2) + 4) := by
  rw [encTblAsc_eq] at hS
  refine Frag.runs_mono (revTbl_runs hsd hss hss' hds hds' hs _ N b (tblBounded_map_range ht) sr v S hS)
    (fun _ S' ⟨h1, h2, h3⟩ => ⟨h1, by rw [h2, encTblDesc_eq_reverse], h3⟩) (by simp)

/-! ### The residue update -/

/-- With `a` above `q` above `L` on `nL`, replace `a` by
`if q ≤ a then a - q else L - (q - a)` (for `a, q < L` this is `(a + L - q) % L`);
`np`, `s`, `t` scratch (restored). -/
def resStep (nL np s t : K) : Frag :=
  (moveEntry nL np s).seq ((dup np t s).seq ((dup nL s t).seq ((cmpFrag t s).seq
    ((Frag.ite (fun v => decide (v.cmp = .lt))
      ((dup nL t s).seq ((sub t np s t).seq ((moveEntry nL np s).seq ((dup nL s t).seq
        ((sub s t np s).seq ((moveEntry np nL t).seq (moveEntry s np t)))))))
      ((dup nL t s).seq (sub np t s np))).seq
    (moveEntry np nL s)))))

theorem resStep_runs {nL np s t : K} (hLp : nL ≠ np) (hLs : nL ≠ s) (hLt : nL ≠ t)
    (hps : np ≠ s) (hpt : np ≠ t) (hst : s ≠ t)
    (rl pl Ll : List Bool) (m : ℕ) (hrl : rl.length ≤ m) (hpl : pl.length ≤ m) (hLl : Ll.length ≤ m)
    (nLr : List Γ') (v : St) (S : Stacks)
    (hS : S nL = bits rl ++ .comma :: (bits pl ++ .comma :: (bits Ll ++ .comma :: nLr))) :
    (resStep nL np s t).Runs v S (fun _ S' =>
        (∃ rl' : List Bool,
          toNat rl' = (if toNat pl ≤ toNat rl then toNat rl - toNat pl
            else toNat Ll - (toNat pl - toNat rl)) ∧
          rl'.length ≤ m ∧
          S' nL = bits rl' ++ .comma :: (bits pl ++ .comma :: (bits Ll ++ .comma :: nLr))) ∧
        S' np = S np ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ nL → k ≠ np → k ≠ s → k ≠ t → S' k = S k)
      (25 * m + 53) := by
  have hpL := hLp.symm
  have hsL := hLs.symm
  have htL := hLt.symm
  have hsp := hps.symm
  have htp := hpt.symm
  have hts := hst.symm
  -- stage 1: park a on np
  have h1 := moveEntry_runs hLp hLs hps rl _ v S hS
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 23 * m + 49) h1
    fun v₁ S₁ ⟨_, _, _, hL₁, hp₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 2: copy a to t
  have h2 := dup_runs hpt hps hts rl _ v₁ S₁ hp₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 21 * m + 44) h2
    fun v₂ S₂ ⟨hp₂, ht₂, hs₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: copy q to s
  have hL₂ : S₂ nL = bits pl ++ .comma :: (bits Ll ++ .comma :: nLr) := by
    rw [hF₂ nL hLp hLt hLs, hL₁]
  have h3 := dup_runs hLs hLt hst pl _ v₂ S₂ hL₂
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 19 * m + 39) h3
    fun v₃ S₃ ⟨hL₃, hs₃, ht₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 4: compare
  have ht₃' : S₃ t = bits rl ++ .comma :: S t := by
    rw [ht₃, ht₂, hF₁ t htL htp hts]
  have hs₃' : S₃ s = bits pl ++ .comma :: S s := by
    rw [hs₃, hs₂, hs₁]
  have h4 := cmpFrag_runs hts rl pl (S t) (S s) v₃ S₃ ht₃' hs₃'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 18 * m + 37) h4
    fun v₄ S₄ ⟨hcmp₄, ht₄, hs₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  have hL₄ : S₄ nL = bits pl ++ .comma :: (bits Ll ++ .comma :: nLr) := by
    rw [hF₄ nL hLt hLs, hL₃, hL₂]
  have hp₄ : S₄ np = bits rl ++ .comma :: S np := by
    rw [hF₄ np hpt hps, hF₃ np hpL hps hpt, hp₂, hp₁]
  -- stage 5: the conditional
  have h5 : (Frag.ite (fun v => decide (v.cmp = .lt))
      ((dup nL t s).seq ((sub t np s t).seq ((moveEntry nL np s).seq ((dup nL s t).seq
        ((sub s t np s).seq ((moveEntry np nL t).seq (moveEntry s np t)))))))
      ((dup nL t s).seq (sub np t s np))).Runs v₄ S₄ (fun _ T =>
        (∃ rl' : List Bool,
          toNat rl' = (if toNat pl ≤ toNat rl then toNat rl - toNat pl
            else toNat Ll - (toNat pl - toNat rl)) ∧
          rl'.length ≤ m ∧ T np = bits rl' ++ .comma :: S np) ∧
        T nL = bits pl ++ .comma :: (bits Ll ++ .comma :: nLr) ∧ T s = S s ∧ T t = S t ∧
        ∀ k, k ≠ nL → k ≠ np → k ≠ s → k ≠ t → T k = S₄ k)
      (16 * m + 33) := by
    refine Frag.ite_runs (fun hc => ?_) (fun hc => ?_)
    · -- a < q
      have hlt : toNat rl < toNat pl := by
        rw [hcmp₄] at hc; simpa [compare_lt_iff_lt] using hc
      rw [if_neg (by omega)]
      -- a. copy q to t
      have h5a := dup_runs hLt hLs hts pl _ v₄ S₄ hL₄
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 14 * m + 27) h5a
        fun w₁ T₁ ⟨hL', ht', hs', hF'⟩ => ?_) (fun _ _ h => h) (by omega)
      -- b. t := q - a, consuming a on np
      have hp' : T₁ np = bits rl ++ .comma :: S np := by rw [hF' np hpL hpt hps, hp₄]
      have h5b := sub_runs_x htp hts hps pl rl (S₄ t) (S np) w₁ T₁ ht' hp'
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 11 * m + 22) h5b
        fun w₂ T₂ ⟨ht'', hp'', hs'', hF''⟩ => ?_) (fun _ _ h => h)
        (by have := max_le hpl hrl; omega)
      -- c. park q on np
      have hL'' : T₂ nL = bits pl ++ .comma :: (bits Ll ++ .comma :: nLr) := by
        rw [hF'' nL hLt hLp hLs, hL', hL₄]
      have h5c := moveEntry_runs hLp hLs hps pl _ w₂ T₂ hL''
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 9 * m + 18) h5c
        fun w₃ T₃ ⟨_, _, _, hL₃', hp₃', hs₃', hF₃'⟩ => ?_) (fun _ _ h => h) (by omega)
      -- d. copy L to s
      have h5d := dup_runs hLs hLt hst Ll _ w₃ T₃ hL₃'
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 7 * m + 13) h5d
        fun w₄ T₄ ⟨hL₄', hs₄', ht₄', hF₄'⟩ => ?_) (fun _ _ h => h) (by omega)
      -- e. s := L - (q - a), consuming t
      have hs₄'' : T₄ s = bits Ll ++ .comma :: S s := by
        rw [hs₄', hs₃', hs'', hs', hs₄]
      have ht₄'' : T₄ t = bits (subTrunc pl rl false) ++ .comma :: S t := by
        rw [ht₄', hF₃' t htL htp hts, ht'', ht₄]
      have h5e := sub_runs_x hst hsp htp Ll (subTrunc pl rl false) (S s) (S t) w₄ T₄ hs₄'' ht₄''
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * m + 8) h5e
        fun w₅ T₅ ⟨hs₅', ht₅', hp₅', hF₅'⟩ => ?_) (fun _ _ h => h)
        (by have := max_le hLl ((subTrunc_length pl rl false).trans (max_le hpl hrl)); omega)
      -- f. q back on nL
      have hp₅'' : T₅ np = bits pl ++ .comma :: S np := by
        rw [hp₅', hF₄' np hpL hps hpt, hp₃', hp'']
      have h5f := moveEntry_runs hpL hpt hLt pl _ w₅ T₅ hp₅''
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * m + 4) h5f
        fun w₆ T₆ ⟨_, _, _, hp₆', hL₆', ht₆', hF₆'⟩ => ?_) (fun _ _ h => h) (by omega)
      -- g. the result onto np
      have hs₆'' : T₆ s = bits (subTrunc Ll (subTrunc pl rl false) false) ++ .comma :: S s := by
        rw [hF₆' s hsp hsL hst, hs₅']
      have h5g := moveEntry_runs hsp hst hpt _ _ w₆ T₆ hs₆''
      refine Frag.runs_mono h5g (fun _ T₇ ⟨_, _, _, hs₇', hp₇', ht₇', hF₇'⟩ =>
        ⟨⟨_, ?_, ?_, by rw [hp₇', hp₆']⟩, ?_, hs₇', ?_, ?_⟩) ?_
      · rw [toNat_subTrunc, toNat_subTrunc]; simp
      · exact (subTrunc_length _ _ _).trans
          (max_le hLl ((subTrunc_length pl rl false).trans (max_le hpl hrl)))
      · rw [hF₇' nL hLs hLp hLt, hL₆', hF₅' nL hLs hLt hLp, hL₄', hL₃']
      · rw [ht₇', ht₆', ht₅']
      · intro k hkL hkp hks hkt
        rw [hF₇' k hks hkp hkt, hF₆' k hkp hkL hkt, hF₅' k hks hkt hkp, hF₄' k hkL hks hkt,
          hF₃' k hkL hkp hks, hF'' k hkt hkp hks, hF' k hkL hkt hks]
      · have := (subTrunc_length Ll (subTrunc pl rl false) false).trans
          (max_le hLl ((subTrunc_length pl rl false).trans (max_le hpl hrl)))
        omega
    · -- q ≤ a
      have hge : toNat pl ≤ toNat rl := by
        rw [hcmp₄] at hc; simpa [compare_lt_iff_lt] using hc
      rw [if_pos hge]
      have h5a := dup_runs hLt hLs hts pl _ v₄ S₄ hL₄
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * m + 5) h5a
        fun w₁ T₁ ⟨hL', ht', hs', hF'⟩ => ?_) (fun _ _ h => h) (by omega)
      have hp' : T₁ np = bits rl ++ .comma :: S np := by rw [hF' np hpL hpt hps, hp₄]
      have h5b := sub_runs_x hpt hps hts rl pl (S np) (S₄ t) w₁ T₁ hp' ht'
      refine Frag.runs_mono h5b (fun _ T₂ ⟨hp'', ht'', hs'', hF''⟩ =>
        ⟨⟨_, ?_, (subTrunc_length _ _ _).trans (max_le hrl hpl), hp''⟩, ?_, ?_, ?_, ?_⟩)
        (by have := max_le hrl hpl; omega)
      · rw [toNat_subTrunc]; simp
      · rw [hF'' nL hLp hLt hLs, hL', hL₄]
      · rw [hs'', hs', hs₄]
      · rw [ht'', ht₄]
      · intro k hkL hkp hks hkt
        rw [hF'' k hkp hkt hks, hF' k hkL hkt hks]
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * m + 4) h5
    fun v₅ S₅ ⟨⟨rl', hrl', hlen', hp₅⟩, hL₅, hs₅, ht₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 6: the result back onto nL
  have h6 := moveEntry_runs hpL hps hLs rl' _ v₅ S₅ hp₅
  refine Frag.runs_mono h6 (fun _ S₆ ⟨_, _, _, hp₆, hL₆, hs₆, hF₆⟩ =>
    ⟨⟨rl', hrl', hlen', by rw [hL₆, hL₅]⟩, hp₆, ?_, ?_, ?_⟩) (by omega)
  · rw [hs₆, hs₅]
  · rw [hF₆ t htp htL hts, ht₅]
  · intro k hkL hkp hks hkt
    rw [hF₆ k hkp hkL hks, hF₅ k hkL hkp hks hkt, hF₄ k hkt hks, hF₃ k hkL hks hkt,
      hF₂ k hkp hkt hks, hF₁ k hkL hkp hks]

/-! ### One DP step -/

/-- The loop body of `dpStepF` at one snapshot slot: update the residue on
`nL`; if the slot (top of `snap`) is a witness `W`, extend it by `p` (copied
from `np`) and `setIfNone` it into the accumulator at the residue (a copy of
which is pushed on `np` as the index); otherwise pop the `ket`. -/
def dpBodyF (np nL snap acc s t : K) : Frag :=
  (resStep nL np s t).seq ((peekKet snap).seq
    (Frag.ite (fun v => v.flag) (popTop snap)
      ((dup np snap s).seq ((dup nL np s).seq (setIfNoneF acc np snap s t)))))

/-- `Alg.dpStep L p t`: `p` on `np` (consumed), `L` on `nL` (kept), the
snapshot `encTblDesc L t` on `snap` (consumed down to its `blank`), the
accumulator `encTblAsc L t` on `acc` (replaced by the result); `s`, `t`
scratch.  Prelude: `p % L` (kept above `L` on `nL`), the initial write of
`[p]` at `p % L`, the residue `0` above `p % L`; then the slot loop; then the
cleanup. -/
def dpStepF (np nL snap acc s t : K) : Frag :=
  (dup nL t s).seq ((dup np nL s).seq ((modFrag nL t np snap s acc).seq
    ((Frag.pushSym snap .bra).seq ((dup np snap s).seq ((dup nL np s).seq
      ((setIfNoneF acc np snap s t).seq ((pushNum nL 0).seq
        ((forSlots snap (dpBodyF np nL snap acc s t)).seq
          ((popTop snap).seq ((dropNum nL).seq ((dropNum nL).seq (dropNum np))))))))))))

/-- Step bound of one `dpBodyF` iteration. -/
def dpBodyC (L N b : ℕ) : ℕ := 56 * b + 67 + setC L (N + 1) b (2 * b)

/-- Step bound of `dpStepF`. -/
def dpC (L N b : ℕ) : ℕ :=
  b * (46 * b + 60) + 33 * b + 64 + setC L (N + 1) b (2 * b) + L * (dpBodyC L N b + 2)

/-- Loop invariant of `dpStepF` after `i` slots: the residue `((L - i) p) % L`
above `p % L` above `L` on `nL`, `p` on `np`, `accSeq L p t i` on `acc`. -/
def DpInv (np nL snap acc s t : K) (L p : ℕ) (tb : Alg.Tbl) (b : ℕ) (pl : List Bool)
    (npr nLr accr : List Γ') (S₀ : Stacks) (i : ℕ) (T : Stacks) : Prop :=
  (∃ rl : List Bool, toNat rl = ((L - i) * p) % L ∧ rl.length ≤ 2 * b ∧
    T nL = bits rl ++ .comma :: (bits pl ++ .comma :: (encodeNatΓ' L ++ .comma :: nLr))) ∧
  T np = encodeNatΓ' p ++ .comma :: npr ∧
  T acc = encTblAsc L (accSeq L p tb i) ++ .blank :: accr ∧
  T s = S₀ s ∧ T t = S₀ t ∧
  ∀ k, k ≠ np → k ≠ nL → k ≠ snap → k ≠ acc → k ≠ s → k ≠ t → T k = S₀ k

theorem setC_mono_left {j j' N b m : ℕ} (h : j ≤ j') : setC j N b m ≤ setC j' N b m := by
  unfold setC
  have := Nat.mul_le_mul_right (2 * slotC N b + 4 * m + 11) h
  omega

theorem dpBodyF_runs {np nL snap acc s t : K} (hpL : np ≠ nL) (hpsn : np ≠ snap) (hpa : np ≠ acc)
    (hps : np ≠ s) (hpt : np ≠ t) (hLsn : nL ≠ snap) (hLa : nL ≠ acc) (hLs : nL ≠ s) (hLt : nL ≠ t)
    (hsna : snap ≠ acc) (hsns : snap ≠ s) (hsnt : snap ≠ t) (has : acc ≠ s) (hat : acc ≠ t)
    (hst : s ≠ t) (L p : ℕ) (hL : 0 < L) (tb : Alg.Tbl) (N b : ℕ) (ht : TblBounded L tb N b)
    (hp : p < 2 ^ b) (hLb : L < 2 ^ b) (pl : List Bool) (hpl : toNat pl = p % L)
    (hpll : pl.length ≤ 2 * b)
    (npr nLr snapr accr : List Γ') (S₀ : Stacks) (i : ℕ) (hi : i < L) (w : St) (T : Stacks)
    (hI : DpInv np nL snap acc s t L p tb b pl npr nLr accr S₀ i T)
    (hTsn : T snap = encSlot (tb (L - 1 - i)) ++
      (encSlots (((List.range L).reverse.map tb).drop (i + 1)) ++ .blank :: snapr)) :
    (dpBodyF np nL snap acc s t).Runs w T (fun _ T' =>
        DpInv np nL snap acc s t L p tb b pl npr nLr accr S₀ (i + 1) T' ∧
        T' snap = encSlots (((List.range L).reverse.map tb).drop (i + 1)) ++ .blank :: snapr)
      (dpBodyC L N b) := by
  have hLp := hpL.symm
  have hsnp := hpsn.symm
  have hap := hpa.symm
  have hsp := hps.symm
  have htp := hpt.symm
  have hsnL := hLsn.symm
  have haL := hLa.symm
  have hsL := hLs.symm
  have htL := hLt.symm
  have hasn := hsna.symm
  have hssn := hsns.symm
  have htsn := hsnt.symm
  have hsa := has.symm
  have hta := hat.symm
  have hts := hst.symm
  obtain ⟨⟨rl, hrl, hrll, hTL⟩, hTp, hTa, hTs, hTt, hTF⟩ := hI
  have hLl : (Computability.encodeNat L).length ≤ 2 * b := by
    have := encodeNat_length_le_of_lt_pow hLb; omega
  unfold dpBodyC
  -- stage 1: the residue update
  have h1 := resStep_runs hLp hLs hLt hps hpt hst rl pl (Computability.encodeNat L) (2 * b) hrll hpll
    hLl nLr w T hTL
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 6 * b + 14 + setC L (N + 1) b (2 * b)) h1
    fun w₁ T₁ ⟨⟨rl', hrl', hrll', hL₁⟩, hp₁, hs₁, ht₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  have hres : toNat rl' = ((L - (i + 1)) * p) % L := by
    rw [hrl', hrl, hpl, toNat_encodeNat, show L - (i + 1) = L - 1 - i by omega,
      res_pred L p (L - 1 - i) hL, show L - 1 - i + 1 = L - i by omega]
  have hsn₁ : T₁ snap = T snap := hF₁ snap hsnL hsnp hsns hsnt
  -- stage 2: peek at the slot
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 6 * b + 13 + setC L (N + 1) b (2 * b))
    (peekKet_runs snap w₁ T₁) fun w₂ T₂ ⟨hw₂, hT₂⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hT₂]
  have hfl₂ : w₂.flag = decide (tb (L - 1 - i) = none) := by
    rw [hw₂]; simp only; rw [hsn₁, hTsn, decide_head?_encSlot_ket]
  -- stage 3: the conditional
  refine Frag.runs_mono (Frag.ite_runs (t := 6 * b + 12 + setC L (N + 1) b (2 * b))
    (fun hc => ?_) (fun hc => ?_)) (fun _ _ h => h) (by omega)
  · -- no witness: pop the ket
    rw [hfl₂, decide_eq_true_eq] at hc
    refine Frag.runs_mono (popTop_runs snap w₂ T₁) (fun _ T₃ ⟨_, hT₃⟩ => ?_) (by omega)
    subst hT₃
    refine ⟨⟨⟨rl', hres, hrll', by rw [Function.update_of_ne hLsn, hL₁, encodeNatΓ'_eq]⟩, ?_, ?_, ?_,
      ?_, ?_⟩, ?_⟩
    · rw [Function.update_of_ne hpsn, hp₁, hTp]
    · rw [Function.update_of_ne hasn, hF₁ acc haL hap has hat, hTa]
      simp only [accSeq, dpBody, hc]
    · rw [Function.update_of_ne hssn, hs₁, hTs]
    · rw [Function.update_of_ne htsn, ht₁, hTt]
    · intro k hkp hkL hksn hka hks hkt
      rw [Function.update_of_ne hksn, hF₁ k hkL hkp hks hkt, hTF k hkp hkL hksn hka hks hkt]
    · rw [Function.update_self, hsn₁, hTsn, hc, encSlot_none, List.singleton_append, List.tail_cons]
  · -- a witness W: write p :: W at the residue
    rw [hfl₂, decide_eq_false_iff_not] at hc
    obtain ⟨W, hW⟩ := Option.ne_none_iff_exists'.mp hc
    obtain ⟨hWN, hWb⟩ := ht (L - 1 - i) (by omega) W hW
    have hlogp : Nat.log 2 p ≤ b := log_le_of_lt_pow hp
    -- 3a. copy p onto the witness
    have hp₁' : T₁ np = encodeNatΓ' p ++ .comma :: npr := by rw [hp₁, hTp]
    have h3a := dup_correct hpsn hps hsns p npr w₂ T₁ hp₁'
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * b + 5 + setC L (N + 1) b (2 * b)) h3a
      fun w₃ T₃ ⟨hp₃, hsn₃, hs₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
    -- 3b. copy the residue onto np as the index
    have hL₃ : T₃ nL = bits rl' ++ .comma :: (bits pl ++ .comma :: (encodeNatΓ' L ++ .comma :: nLr)) := by
      rw [hF₃ nL hLp hLsn hLs, hL₁, encodeNatΓ'_eq]
    have h3b := dup_runs hLp hLs hps rl' _ w₃ T₃ hL₃
    refine Frag.runs_mono (Frag.seq_runs (t₂ := setC L (N + 1) b (2 * b)) h3b
      fun w₄ T₄ ⟨hL₄, hp₄, hs₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
    -- 3c. setIfNone
    have ha₄ : T₄ acc = encTblAsc L (accSeq L p tb i) ++ .blank :: accr := by
      rw [hF₄ acc haL hap has, hF₃ acc hap hasn has, hF₁ acc haL hap has hat, hTa]
    have hp₄' : T₄ np = bits rl' ++ .comma :: (encodeNatΓ' p ++ .comma :: npr) := by
      rw [hp₄, hp₃, hp₁']
    have hsn₄ : T₄ snap = encList (p :: W) ++
        (encSlots (((List.range L).reverse.map tb).drop (i + 1)) ++ .blank :: snapr) := by
      rw [hF₄ snap hsnL hsnp hsns, hsn₃, hsn₁, hTsn, hW, encSlot_some, encList_cons,
        List.append_assoc, List.cons_append]
    have hjn : toNat rl' < L := by rw [hres]; exact Nat.mod_lt _ hL
    have h3c := setIfNoneF_tbl hap hasn has hat hpsn hps hpt hsns hsnt hst L (accSeq L p tb i)
      (N + 1) b (tblBounded_accSeq ht hp i) rl' (2 * b) hrll' hjn (p :: W)
      (by simp; omega) (fun q hq => by
        rcases List.mem_cons.mp hq with rfl | hq
        · exact hp
        · exact hWb q hq)
      (.blank :: accr) _ _ w₄ T₄ ha₄ hp₄' hsn₄
    refine Frag.runs_mono h3c (fun _ T₅ ⟨ha₅, hp₅, hsn₅, hs₅, ht₅, hF₅⟩ =>
      ⟨⟨⟨rl', hres, hrll', ?_⟩, hp₅, ?_, ?_, ?_, ?_⟩, hsn₅⟩) (setC_mono_left hjn.le)
    · rw [hF₅ nL hLa hLp hLsn hLs hLt, hL₄, hL₃]
    · rw [ha₅]
      simp only [accSeq, dpBody, hW]
      rw [hres, show L - (i + 1) = L - 1 - i by omega]
    · rw [hs₅, hs₄, hs₃, hs₁, hTs]
    · rw [ht₅, hF₄ t htL htp hts, hF₃ t htp htsn hts, ht₁, hTt]
    · intro k hkp hkL hksn hka hks hkt
      rw [hF₅ k hka hkp hksn hks hkt, hF₄ k hkL hkp hks, hF₃ k hkp hksn hks, hF₁ k hkL hkp hks hkt,
        hTF k hkp hkL hksn hka hks hkt]

theorem dpStepF_runs {np nL snap acc s t : K} (hpL : np ≠ nL) (hpsn : np ≠ snap) (hpa : np ≠ acc)
    (hps : np ≠ s) (hpt : np ≠ t) (hLsn : nL ≠ snap) (hLa : nL ≠ acc) (hLs : nL ≠ s) (hLt : nL ≠ t)
    (hsna : snap ≠ acc) (hsns : snap ≠ s) (hsnt : snap ≠ t) (has : acc ≠ s) (hat : acc ≠ t)
    (hst : s ≠ t) (L p : ℕ) (hL : 0 < L) (tb : Alg.Tbl) (N b : ℕ) (ht : TblBounded L tb N b)
    (hp : p < 2 ^ b) (hLb : L < 2 ^ b) (npr nLr snapr accr : List Γ') (v : St) (S : Stacks)
    (hSp : S np = encodeNatΓ' p ++ .comma :: npr) (hSL : S nL = encodeNatΓ' L ++ .comma :: nLr)
    (hSsn : S snap = encTblDesc L tb ++ .blank :: snapr)
    (hSa : S acc = encTblAsc L tb ++ .blank :: accr) :
    (dpStepF np nL snap acc s t).Runs v S (fun _ S' =>
        S' np = npr ∧ S' nL = S nL ∧ S' snap = snapr ∧
        S' acc = encTblAsc L (Alg.dpStep L p tb).1 ++ .blank :: accr ∧
        S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ np → k ≠ nL → k ≠ snap → k ≠ acc → k ≠ s → k ≠ t → S' k = S k)
      (dpC L N b) := by
  have hLp := hpL.symm
  have hsnp := hpsn.symm
  have hap := hpa.symm
  have hsp := hps.symm
  have htp := hpt.symm
  have hsnL := hLsn.symm
  have haL := hLa.symm
  have hsL := hLs.symm
  have htL := hLt.symm
  have hasn := hsna.symm
  have hssn := hsns.symm
  have htsn := hsnt.symm
  have hsa := has.symm
  have hta := hat.symm
  have hts := hst.symm
  have hlogp : Nat.log 2 p ≤ b := log_le_of_lt_pow hp
  have hlogL : Nat.log 2 L ≤ b := log_le_of_lt_pow hLb
  have hxs : (Computability.encodeNat p).length ≤ b := encodeNat_length_le_of_lt_pow hp
  have hds : (Computability.encodeNat L).length ≤ b := encodeNat_length_le_of_lt_pow hLb
  set SC := setC L (N + 1) b (2 * b) with hSC
  set TL := L * (dpBodyC L N b + 2) + 2 with hTL
  have hdpC : dpC L N b = b * (46 * b + 60) + 33 * b + 62 + SC + TL := by
    rw [hSC, hTL, dpC]; ring
  rw [hdpC]
  -- stage 1: L onto t
  have h1 := dup_correct hLt hLs hts L nLr v S hSL
  refine Frag.runs_mono (Frag.seq_runs (t₂ := b * (46 * b + 60) + 31 * b + 55 + SC + TL) h1
    fun v₁ S₁ ⟨hL₁, ht₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 2: p onto nL
  have hp₁ : S₁ np = encodeNatΓ' p ++ .comma :: npr := by rw [hF₁ np hpL hpt hps, hSp]
  have h2 := dup_correct hpL hps hLs p npr v₁ S₁ hp₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := b * (46 * b + 60) + 29 * b + 48 + SC + TL) h2
    fun v₂ S₂ ⟨hp₂, hL₂, hs₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: p % L
  have hL₂' : S₂ nL = bits (Computability.encodeNat p) ++ .comma :: (encodeNatΓ' L ++ .comma :: nLr) := by
    rw [hL₂, hL₁, hSL]; rfl
  have ht₂' : S₂ t = bits (Computability.encodeNat L) ++ .comma :: S t := by
    rw [hF₂ t htp htL hts, ht₁]; rfl
  have h3 := modFrag_runs hLt hLp hLsn hLs hLa htp htsn hts hta hpsn hps hpa hsns hsna hsa
    (Computability.encodeNat p) (Computability.encodeNat L)
    (by rw [toNat_encodeNat]; exact hL) _ (S t) v₂ S₂ hL₂' ht₂'
  have hmod : (Computability.encodeNat p).length *
      (23 * ((Computability.encodeNat p).length + (Computability.encodeNat L).length) + 60) +
      9 * ((Computability.encodeNat p).length + (Computability.encodeNat L).length) + 28 ≤
      b * (46 * b + 60) + 18 * b + 28 := by
    have := Nat.mul_le_mul hxs (show 23 * ((Computability.encodeNat p).length +
      (Computability.encodeNat L).length) + 60 ≤ 46 * b + 60 by omega)
    omega
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 11 * b + 20 + SC + TL) h3
    fun v₃ S₃ ⟨⟨pl, hpll, hpl, hL₃⟩, ht₃, hp₃, hsn₃, hs₃, ha₃, hF₃⟩ => ?_) (fun _ _ h => h)
    (by omega)
  rw [toNat_encodeNat, toNat_encodeNat] at hpl
  have hpll' : pl.length ≤ 2 * b := by omega
  -- stage 4: open the witness list [p]
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 11 * b + 19 + SC + TL)
    (Frag.pushSym_runs snap .bra v₃ S₃) fun v₄ S₄ ⟨_, hS₄⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₄
  -- stage 5: p onto the witness
  have hp₄ : Function.update S₃ snap (.bra :: S₃ snap) np = encodeNatΓ' p ++ .comma :: npr := by
    rw [Function.update_of_ne hpsn, hp₃, hp₂, hp₁]
  have h5 := dup_correct hpsn hps hsns p npr v₄ _ hp₄
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 9 * b + 12 + SC + TL) h5
    fun v₅ S₅ ⟨hp₅, hsn₅, hs₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 6: p % L onto np as the index
  have hL₅ : S₅ nL = bits pl ++ .comma :: (encodeNatΓ' L ++ .comma :: nLr) := by
    rw [hF₅ nL hLp hLsn hLs, Function.update_of_ne hLsn, hL₃]
  have h6 := dup_runs hLp hLs hps pl _ v₅ S₅ hL₅
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * b + 7 + SC + TL) h6
    fun v₆ S₆ ⟨hL₆, hp₆, hs₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 7: the initial write
  have ha₆ : S₆ acc = encTblAsc L tb ++ .blank :: accr := by
    rw [hF₆ acc haL hap has, hF₅ acc hap hasn has, Function.update_of_ne hasn, ha₃,
      hF₂ acc hap haL has, hF₁ acc haL hat has, hSa]
  have hp₆' : S₆ np = bits pl ++ .comma :: (encodeNatΓ' p ++ .comma :: npr) := by
    rw [hp₆, hp₅, hp₄]
  have hsn₆ : S₆ snap = encList [p] ++ (encTblDesc L tb ++ .blank :: snapr) := by
    rw [hF₆ snap hsnL hsnp hsns, hsn₅, Function.update_self, hsn₃, hF₂ snap hsnp hsnL hsns,
      hF₁ snap hsnL hsnt hsns, hSsn, encList_cons, encList_nil]
    simp
  have hjn : toNat pl < L := by rw [hpl]; exact Nat.mod_lt _ hL
  have h7 := setIfNoneF_tbl hap hasn has hat hpsn hps hpt hsns hsnt hst L tb (N + 1) b
    (ht.mono (Nat.le_succ N)) pl (2 * b) hpll' hjn [p] (by simp) (by simpa using hp)
    (.blank :: accr) _ _ v₆ S₆ ha₆ hp₆' hsn₆
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * b + 7 + TL) h7
    fun v₇ S₇ ⟨ha₇, hp₇, hsn₇, hs₇, ht₇, hF₇⟩ => ?_) (fun _ _ h => h)
    (by have := setC_mono_left (N := N + 1) (b := b) (m := 2 * b) hjn.le; omega)
  -- stage 8: the residue 0
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * b + 5 + TL) (pushNum_runs nL 0 v₇ S₇)
    fun v₈ S₈ ⟨_, hL₈, hF₈⟩ => ?_) (fun _ _ h => h) (by rw [Nat.log_zero_right]; omega)
  -- stage 9: the slot loop
  have hL₈' : S₈ nL = bits [] ++ .comma :: (bits pl ++ .comma :: (encodeNatΓ' L ++ .comma :: nLr)) := by
    rw [hL₈, hF₇ nL hLa hLp hLsn hLs hLt, hL₆, hL₅]; rfl
  have hsn₈ : S₈ snap = encSlots ((List.range L).reverse.map tb) ++ .blank :: snapr := by
    rw [hF₈ snap hsnL, hsn₇, encTblDesc_eq]
  have hs₀ : S₈ s = S s := by
    rw [hF₈ s hsL, hs₇, hs₆, hs₅, Function.update_of_ne hssn, hs₃, hs₂, hs₁]
  have ht₀ : S₈ t = S t := by
    rw [hF₈ t htL, ht₇, hF₆ t htL htp hts, hF₅ t htp htsn hts, Function.update_of_ne htsn, ht₃]
  have hF₀ : ∀ k, k ≠ np → k ≠ nL → k ≠ snap → k ≠ acc → k ≠ s → k ≠ t → S₈ k = S k := by
    intro k hkp hkL hksn hka hks hkt
    rw [hF₈ k hkL, hF₇ k hka hkp hksn hks hkt, hF₆ k hkL hkp hks, hF₅ k hkp hksn hks,
      Function.update_of_ne hksn, hF₃ k hkL hkt hkp hksn hks hka, hF₂ k hkp hkL hks,
      hF₁ k hkL hkt hks]
  have hloop := forSlots_runs (body := dpBodyF np nL snap acc s t) ((List.range L).reverse.map tb)
    snapr (DpInv np nL snap acc s t L p tb b pl npr nLr accr S) (dpBodyC L N b) v₈ S₈ hsn₈
    ⟨⟨[], by simp [toNat], by simp, hL₈'⟩, by rw [hF₈ np hpL, hp₇],
      by rw [hF₈ acc haL, ha₇, hpl]; rfl, hs₀, ht₀, hF₀⟩
    (fun i hi w T hI hT => by
      simp only [List.length_map, List.length_reverse, List.length_range] at hi
      rw [getElem_range_reverse_map L tb i (by simpa using hi)] at hT
      exact dpBodyF_runs hpL hpsn hpa hps hpt hLsn hLa hLs hLt hsna hsns hsnt has hat hst L p hL tb N
        b ht hp hLb pl hpl hpll' npr nLr snapr accr S i hi w T hI hT)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * b + 5) hloop
    fun v₉ S₉ ⟨_, ⟨⟨rl, _, hrll, hL₉⟩, hp₉, ha₉, hs₉, ht₉, hF₉⟩, hsn₉⟩ => ?_) (fun _ _ h => h)
    (by rw [hTL]; simp only [List.length_map, List.length_reverse, List.length_range]; omega)
  simp only [List.length_map, List.length_reverse, List.length_range] at ha₉
  -- stage 10: pop the snapshot's marker
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * b + 4) (popTop_runs snap v₉ S₉)
    fun v₁₀ S₁₀ ⟨_, hS₁₀⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₁₀
  -- stage 11: drop the residue
  have h11 := dropNum_runs rl _ v₁₀ (Function.update S₉ snap (S₉ snap).tail)
    (by rw [Function.update_of_ne hLsn, hL₉])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * b + 3) h11
    fun v₁₁ S₁₁ ⟨_, _, _, hL₁₁, hF₁₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 12: drop p % L
  have h12 := dropNum_runs pl _ v₁₁ S₁₁ hL₁₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := b + 2) h12
    fun v₁₂ S₁₂ ⟨_, _, _, hL₁₂, hF₁₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 13: drop p
  have hp₁₂ : S₁₂ np = encodeNatΓ' p ++ .comma :: npr := by
    rw [hF₁₂ np hpL, hF₁₁ np hpL, Function.update_of_ne hpsn, hp₉]
  have h13 := dropNum_correct p npr v₁₂ S₁₂ hp₁₂
  refine Frag.runs_mono h13 (fun _ S₁₃ ⟨_, _, _, hp₁₃, hF₁₃⟩ => ⟨hp₁₃, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    (by omega)
  · rw [hF₁₃ nL hLp, hL₁₂, hSL]
  · rw [hF₁₃ snap hsnp, hF₁₂ snap hsnL, hF₁₁ snap hsnL, Function.update_self, hsn₉, List.tail_cons]
  · rw [hF₁₃ acc hap, hF₁₂ acc haL, hF₁₁ acc haL, Function.update_of_ne hasn, ha₉,
      dpStep_eq_accSeq]
  · rw [hF₁₃ s hsp, hF₁₂ s hsL, hF₁₁ s hsL, Function.update_of_ne hssn, hs₉]
  · rw [hF₁₃ t htp, hF₁₂ t htL, hF₁₁ t htL, Function.update_of_ne htsn, ht₉]
  · intro k hkp hkL hksn hka hks hkt
    rw [hF₁₃ k hkp, hF₁₂ k hkL, hF₁₁ k hkL, Function.update_of_ne hksn,
      hF₉ k hkp hkL hksn hka hks hkt]

/-! ### Copying a table -/

/-- Copy the top slot of `src` onto `dst` (`src` unchanged); `s`, `s'` scratch. -/
def copySlot (src dst s s' : K) : Frag :=
  (peekKet src).seq (Frag.ite (fun v => v.flag) (Frag.pushSym dst .ket) (copyList src dst s s'))

theorem copySlot_runs {src dst s s' : K} (hsd : src ≠ dst) (hss : src ≠ s) (hss' : src ≠ s')
    (hds : dst ≠ s) (hds' : dst ≠ s') (hs : s ≠ s') (o : Option (List ℕ)) (N b : ℕ)
    (ho : SlotBounded N b o) (sr : List Γ') (v : St) (S : Stacks) (hS : S src = encSlot o ++ sr) :
    (copySlot src dst s s').Runs v S (fun _ S' =>
        S' src = S src ∧ S' dst = encSlot o ++ S dst ∧ S' s = S s ∧ S' s' = S s' ∧
        ∀ k, k ≠ src → k ≠ dst → k ≠ s → k ≠ s' → S' k = S k)
      (N * (6 * b + 17) + 11) := by
  have hds₀ := hsd.symm
  have hsd₀ := hds.symm
  have hs'd := hds'.symm
  refine Frag.runs_mono (Frag.seq_runs (t₂ := N * (6 * b + 17) + 10) (peekKet_runs src v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₁, hS₁]
  cases o with
  | none =>
    have hfl : decide ((S src).head? = some Γ'.ket) = true := by simp [hS]
    refine Frag.ite_runs (t := N * (6 * b + 17) + 9) (fun _ => ?_)
      (fun hc => absurd hc (by simp [hfl]))
    refine Frag.runs_mono (Frag.pushSym_runs dst .ket _ S) (fun _ S₂ ⟨_, hS₂⟩ => ?_) (by omega)
    subst hS₂
    exact ⟨Function.update_of_ne hsd _ _, by simp, Function.update_of_ne hsd₀ _ _,
      Function.update_of_ne hs'd _ _, fun k _ hkd _ _ => Function.update_of_ne hkd _ _⟩
  | some W =>
    obtain ⟨hWN, hWb⟩ := ho W rfl
    have hfl : decide ((S src).head? = some Γ'.ket) = false := by
      rw [hS, encSlot_some]; exact decide_eq_false (head?_encList_ne_ket W sr)
    refine Frag.ite_runs (t := N * (6 * b + 17) + 9) (fun hc => absurd hc (by simp [hfl]))
      (fun _ => ?_)
    have h1 := copyList_correct hsd hss hss' hds hds' hs W b hWb sr
      { v with flag := decide ((S src).head? = some Γ'.ket) } S hS
    refine Frag.runs_mono h1 (fun _ S₂ ⟨h1, h2, h3, h4, h5⟩ => ⟨h1, h2, h3, h4, h5⟩)
      (by have := Nat.mul_le_mul_right (6 * b + 17) hWN; omega)

/-- Copy the table on `src` (down to its `blank`) onto `dst` in REVERSED slot
order (`encTblAsc ↦ encTblDesc`), the source restored: each slot is copied
onto `dst`, then parked on `hold`; at the end the parked slots walk back.
`hold`, `s`, `s'` scratch. -/
def copyTbl (src dst hold s s' : K) : Frag :=
  (Frag.pushSym dst .blank).seq ((Frag.pushSym hold .blank).seq
    ((forSlots src ((copySlot src dst s s').seq (moveSlot src hold s s'))).seq
      (walkUp src s' s hold)))

/-- Per-slot step bound of `copyTbl`. -/
def copySlotC (N b : ℕ) : ℕ := N * (6 * b + 17) + 2 * slotC N b + 15

/-- Step bound of `copyTbl` on `L` slots. -/
def copyC (L N b : ℕ) : ℕ := L * copySlotC N b + 8

theorem copyTbl_runs {src dst hold s s' : K} (hsd : src ≠ dst) (hsh : src ≠ hold) (hss : src ≠ s)
    (hss' : src ≠ s') (hdh : dst ≠ hold) (hds : dst ≠ s) (hds' : dst ≠ s') (hhs : hold ≠ s)
    (hhs' : hold ≠ s') (hs : s ≠ s') (sl : List (Option (List ℕ))) (N b : ℕ)
    (hsl : ∀ o ∈ sl, SlotBounded N b o) (sr : List Γ') (v : St) (S : Stacks)
    (hS : S src = encSlots sl ++ .blank :: sr) :
    (copyTbl src dst hold s s').Runs v S (fun _ S' =>
        S' src = S src ∧ S' dst = encSlots sl.reverse ++ .blank :: S dst ∧ S' hold = S hold ∧
        S' s = S s ∧ S' s' = S s' ∧
        ∀ k, k ≠ src → k ≠ dst → k ≠ hold → k ≠ s → k ≠ s' → S' k = S k)
      (copyC sl.length N b) := by
  have hds₀ := hsd.symm
  have hhs₀ := hsh.symm
  have hss₀ := hss.symm
  have hs'src := hss'.symm
  have hhd := hdh.symm
  have hsd₀ := hds.symm
  have hs'd := hds'.symm
  have hsh₀ := hhs.symm
  have hs'h := hhs'.symm
  have hs's := hs.symm
  unfold copyC copySlotC
  have hsplit : sl.length * (N * (6 * b + 17) + 2 * slotC N b + 15) =
      sl.length * (N * (6 * b + 17) + slotC N b + 11 + 2) + sl.length * (slotC N b + 2) := by ring
  -- stage 1, 2: the markers
  refine Frag.runs_mono (Frag.seq_runs (t₂ := sl.length * (N * (6 * b + 17) + 2 * slotC N b + 15) + 7)
    (Frag.pushSym_runs dst .blank v S) fun v₁ S₁ ⟨_, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := sl.length * (N * (6 * b + 17) + 2 * slotC N b + 15) + 6)
    (Frag.pushSym_runs hold .blank v₁ _) fun v₂ S₂ ⟨_, hS₂⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₂
  -- stage 3: the slot loop
  have hsrc₂ : Function.update (Function.update S dst (.blank :: S dst)) hold
      (.blank :: Function.update S dst (.blank :: S dst) hold) src = encSlots sl ++ .blank :: sr := by
    rw [Function.update_of_ne hsh, Function.update_of_ne hsd, hS]
  have hloop := forSlots_runs (body := (copySlot src dst s s').seq (moveSlot src hold s s')) sl sr
    (fun i T => T dst = encSlots (sl.take i).reverse ++ .blank :: S dst ∧
      T hold = encSlots (sl.take i).reverse ++ .blank :: S hold ∧ T s = S s ∧ T s' = S s' ∧
      ∀ k, k ≠ src → k ≠ dst → k ≠ hold → k ≠ s → k ≠ s' → T k = S k)
    (N * (6 * b + 17) + slotC N b + 11) v₂ _ hsrc₂
    ⟨by simp [Function.update_of_ne hdh],
      by simp [Function.update_of_ne hhd],
      by simp [Function.update_of_ne hsh₀, Function.update_of_ne hsd₀],
      by simp [Function.update_of_ne hs'h, Function.update_of_ne hs'd],
      fun k _ hkd hkh _ _ => by simp [Function.update_of_ne hkh, Function.update_of_ne hkd]⟩
    (fun i hi w T ⟨hTd, hTh, hTs, hTs', hTF⟩ hTsrc => by
      have hbo := hsl _ (List.getElem_mem hi)
      have h3a := copySlot_runs hsd hss hss' hds hds' hs sl[i] N b hbo _ w T hTsrc
      refine Frag.runs_mono (Frag.seq_runs (t₂ := slotC N b) h3a
        fun w₁ T₁ ⟨hsrc₁, hd₁, hs₁, hs'₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
      have h3b := moveSlot_runs hsh hss hss' hhs hhs' hs sl[i] N b hbo _ w₁ T₁ (by rw [hsrc₁, hTsrc])
      refine Frag.runs_mono h3b (fun _ T₂ ⟨hsrc₂', hh₂, hs₂, hs'₂, hF₂⟩ =>
        ⟨⟨?_, ?_, hs₂.trans (hs₁.trans hTs), hs'₂.trans (hs'₁.trans hTs'), ?_⟩, hsrc₂'⟩) le_rfl
      · rw [hF₂ dst hds₀ hdh hds hds', hd₁, hTd, List.take_succ_eq_append_getElem hi,
          List.reverse_append, List.reverse_singleton, List.singleton_append, encSlots_cons,
          List.append_assoc]
      · rw [hh₂, hF₁ hold hhs₀ hhd hhs hhs', hTh, List.take_succ_eq_append_getElem hi,
          List.reverse_append, List.reverse_singleton, List.singleton_append, encSlots_cons,
          List.append_assoc]
      · intro k hks hkd hkh hkss hkss'
        rw [hF₂ k hks hkh hkss hkss', hF₁ k hks hkd hkss hkss', hTF k hks hkd hkh hkss hkss'])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := sl.length * (slotC N b + 2) + 3) hloop
    fun v₃ S₃ ⟨_, ⟨hd₃, hh₃, hs₃, hs'₃, hF₃⟩, hsrc₃⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [List.take_length] at hd₃ hh₃
  -- stage 4: walk the parked slots back
  have hR : ∀ o ∈ sl.reverse, SlotBounded N b o := fun o ho => hsl o (List.mem_reverse.mp ho)
  have h4 := walkUp_runs hss' hss hsh hs's hs'h hsh₀ sl.reverse [] N b hR (.blank :: sr) (S hold)
    v₃ S₃ hh₃ (by rw [hsrc₃]; rfl)
  refine Frag.runs_mono h4 (fun _ S₄ ⟨hsrc₄, hh₄, hs₄, hs'₄, hF₄⟩ => ⟨?_, ?_, hh₄, ?_, ?_, ?_⟩)
    (by rw [List.length_reverse])
  · rw [hsrc₄, List.reverse_reverse, List.append_nil, hS]
  · rw [hF₄ dst hds₀ hds' hds hdh, hd₃]
  · rw [hs₄, hs₃]
  · rw [hs'₄, hs'₃]
  · intro k hks hkd hkh hkss hkss'
    rw [hF₄ k hks hkss' hkss hkh, hF₃ k hks hkd hkh hkss hkss']

/-- `copyTbl` on a table: ascending in (restored), descending copy out. -/
theorem copyTbl_tbl {src dst hold s s' : K} (hsd : src ≠ dst) (hsh : src ≠ hold) (hss : src ≠ s)
    (hss' : src ≠ s') (hdh : dst ≠ hold) (hds : dst ≠ s) (hds' : dst ≠ s') (hhs : hold ≠ s)
    (hhs' : hold ≠ s') (hs : s ≠ s') (L : ℕ) (t : Alg.Tbl) (N b : ℕ) (ht : TblBounded L t N b)
    (sr : List Γ') (v : St) (S : Stacks) (hS : S src = encTblAsc L t ++ .blank :: sr) :
    (copyTbl src dst hold s s').Runs v S (fun _ S' =>
        S' src = S src ∧ S' dst = encTblDesc L t ++ .blank :: S dst ∧ S' hold = S hold ∧
        S' s = S s ∧ S' s' = S s' ∧
        ∀ k, k ≠ src → k ≠ dst → k ≠ hold → k ≠ s → k ≠ s' → S' k = S k)
      (copyC L N b) := by
  rw [encTblAsc_eq] at hS
  refine Frag.runs_mono (copyTbl_runs hsd hsh hss hss' hdh hds hds' hhs hhs' hs _ N b
    (tblBounded_map_range ht) sr v S hS)
    (fun _ S' ⟨h1, h2, h3⟩ => ⟨h1, by rw [h2, encTblDesc_eq_reverse], h3⟩) (by simp)

/-! ### Budget forms of the step bounds -/

theorem slotC_le (N b : ℕ) : slotC N b ≤ (N + 1) * (4 * b + 12) := by
  unfold slotC; nlinarith

theorem setC_le (j N b m : ℕ) : setC j N b m ≤ (j + 1) * ((N + 1) * (8 * b + 24) + 4 * m + 25) := by
  unfold setC
  have := slotC_le N b
  nlinarith

theorem lookC_le (j N b m : ℕ) :
    lookC j N b m ≤ (j + 1) * ((N + 1) * (8 * b + 24) + 4 * m + 33) := by
  unfold lookC
  have := slotC_le N b
  nlinarith

theorem setC_le_B (j N b : ℕ) : setC j N b (2 * b) ≤ (j + 1) * (N + 2) * B b := by
  have h1 := setC_le j N b (2 * b)
  have h2 : (N + 1) * (8 * b + 24) + 4 * (2 * b) + 25 ≤ (N + 2) * (64 * (b + 2)) := by nlinarith
  have h3 : (N + 2) * (64 * (b + 2)) ≤ (N + 2) * B b := Nat.mul_le_mul_left _ (linear_le_B le_rfl)
  calc setC j N b (2 * b) ≤ (j + 1) * ((N + 1) * (8 * b + 24) + 4 * (2 * b) + 25) := h1
    _ ≤ (j + 1) * ((N + 2) * B b) := Nat.mul_le_mul_left _ (h2.trans h3)
    _ = (j + 1) * (N + 2) * B b := by ring

theorem lookC_le_B (j N b : ℕ) : lookC j N b (2 * b) ≤ (j + 1) * (N + 2) * B b := by
  have h1 := lookC_le j N b (2 * b)
  have h2 : (N + 1) * (8 * b + 24) + 4 * (2 * b) + 33 ≤ (N + 2) * (64 * (b + 2)) := by nlinarith
  have h3 : (N + 2) * (64 * (b + 2)) ≤ (N + 2) * B b := Nat.mul_le_mul_left _ (linear_le_B le_rfl)
  calc lookC j N b (2 * b) ≤ (j + 1) * ((N + 1) * (8 * b + 24) + 4 * (2 * b) + 33) := h1
    _ ≤ (j + 1) * ((N + 2) * B b) := Nat.mul_le_mul_left _ (h2.trans h3)
    _ = (j + 1) * (N + 2) * B b := by ring

theorem revTblC_le_B (L N b : ℕ) : L * (slotC N b + 2) + 4 ≤ (L + 1) * (N + 2) * B b := by
  have h1 := slotC_le N b
  have h2 : (N + 1) * (4 * b + 12) + 2 ≤ (N + 2) * (64 * (b + 2)) := by nlinarith
  have h3 : (N + 2) * (64 * (b + 2)) ≤ (N + 2) * B b := Nat.mul_le_mul_left _ (linear_le_B le_rfl)
  have h4 : 4 ≤ (N + 2) * B b := by
    have := one_le_B b; nlinarith
  calc L * (slotC N b + 2) + 4 ≤ L * ((N + 2) * B b) + (N + 2) * B b :=
        Nat.add_le_add (Nat.mul_le_mul_left _ ((by omega : slotC N b + 2 ≤ (N + 1) * (4 * b + 12) + 2).trans (h2.trans h3))) h4
    _ = (L + 1) * (N + 2) * B b := by ring

theorem emptyTblC_le_B {L b : ℕ} (hL : L < 2 ^ b) :
    L * (4 * Nat.log 2 L + 14) + 2 * Nat.log 2 L + 11 ≤ (L + 1) * B b := by
  have := log_le_of_lt_pow hL
  have := list_le_B (n := L) (c := 4 * Nat.log 2 L + 14) (d := 2 * Nat.log 2 L + 11) (b := b)
    (by omega) (by omega)
  omega

theorem dpC_le (L N b : ℕ) : dpC L N b ≤ (L + 1) ^ 2 * (N + 2) * B b := by
  have hpos : 1 ≤ (L + 1) * (N + 2) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h1 : setC L (N + 1) b (2 * b) ≤ (L + 1) * (N + 2) * (16 * b + 49) := by
    have hi : 8 * b + 25 ≤ (N + 1 + 1) * (8 * b + 25) := Nat.le_mul_of_pos_left _ (by omega)
    calc setC L (N + 1) b (2 * b)
        ≤ (L + 1) * ((N + 1 + 1) * (8 * b + 24) + 4 * (2 * b) + 25) := setC_le L (N + 1) b (2 * b)
      _ ≤ (L + 1) * ((N + 1 + 1) * (8 * b + 24) + (N + 1 + 1) * (8 * b + 25)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = (L + 1) * (N + 2) * (16 * b + 49) := by ring
  have h2 : dpBodyC L N b + 2 ≤ (L + 1) * (N + 2) * (72 * b + 118) := by
    have hi : 56 * b + 69 ≤ (L + 1) * (N + 2) * (56 * b + 69) := Nat.le_mul_of_pos_left _ (by omega)
    unfold dpBodyC
    nlinarith
  have hB : 64 * (b + 2) ^ 2 ≤ B b := quad_le_B le_rfl
  have hpoly : 46 * b ^ 2 + 181 * b + 231 ≤ 64 * (b + 2) ^ 2 := by nlinarith
  have h3 : L * (dpBodyC L N b + 2) ≤ L * ((L + 1) * (N + 2) * (72 * b + 118)) :=
    Nat.mul_le_mul_left L h2
  have h4 : 46 * b ^ 2 + 93 * b + 64 ≤ (L + 1) * (N + 2) * (46 * b ^ 2 + 93 * b + 64) := by
    nlinarith
  calc dpC L N b
      = b * (46 * b + 60) + 33 * b + 64 + setC L (N + 1) b (2 * b) + L * (dpBodyC L N b + 2) := rfl
    _ ≤ (L + 1) * (N + 2) * (46 * b ^ 2 + 93 * b + 64) + (L + 1) * (N + 2) * (16 * b + 49) +
          L * ((L + 1) * (N + 2) * (72 * b + 118)) := by nlinarith
    _ ≤ (L + 1) * ((L + 1) * (N + 2)) * (46 * b ^ 2 + 181 * b + 231) := by nlinarith
    _ ≤ (L + 1) * ((L + 1) * (N + 2)) * (64 * (b + 2) ^ 2) := Nat.mul_le_mul_left _ hpoly
    _ ≤ (L + 1) ^ 2 * (N + 2) * B b := by
        rw [pow_two]
        have := Nat.mul_le_mul_left ((L + 1) * ((L + 1) * (N + 2))) hB
        nlinarith

/-- `dpStepF` within budget: `(L + 1) ^ 2 * (N + 2) * B b` steps. -/
theorem dpStepF_le_B {np nL snap acc s t : K} (hpL : np ≠ nL) (hpsn : np ≠ snap) (hpa : np ≠ acc)
    (hps : np ≠ s) (hpt : np ≠ t) (hLsn : nL ≠ snap) (hLa : nL ≠ acc) (hLs : nL ≠ s) (hLt : nL ≠ t)
    (hsna : snap ≠ acc) (hsns : snap ≠ s) (hsnt : snap ≠ t) (has : acc ≠ s) (hat : acc ≠ t)
    (hst : s ≠ t) (L p : ℕ) (hL : 0 < L) (tb : Alg.Tbl) (N b : ℕ) (ht : TblBounded L tb N b)
    (hp : p < 2 ^ b) (hLb : L < 2 ^ b) (npr nLr snapr accr : List Γ') (v : St) (S : Stacks)
    (hSp : S np = encodeNatΓ' p ++ .comma :: npr) (hSL : S nL = encodeNatΓ' L ++ .comma :: nLr)
    (hSsn : S snap = encTblDesc L tb ++ .blank :: snapr)
    (hSa : S acc = encTblAsc L tb ++ .blank :: accr) :
    (dpStepF np nL snap acc s t).Runs v S (fun _ S' =>
        S' np = npr ∧ S' nL = S nL ∧ S' snap = snapr ∧
        S' acc = encTblAsc L (Alg.dpStep L p tb).1 ++ .blank :: accr ∧
        S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ np → k ≠ nL → k ≠ snap → k ≠ acc → k ≠ s → k ≠ t → S' k = S k)
      ((L + 1) ^ 2 * (N + 2) * B b) :=
  Frag.runs_mono (dpStepF_runs hpL hpsn hpa hps hpt hLsn hLa hLs hLt hsna hsns hsnt has hat hst L p
    hL tb N b ht hp hLb npr nLr snapr accr v S hSp hSL hSsn hSa) (fun _ _ h => h) (dpC_le L N b)

/-- `revTbl` on a table within budget. -/
theorem revTbl_le_B {src dst s s' : K} (hsd : src ≠ dst) (hss : src ≠ s) (hss' : src ≠ s')
    (hds : dst ≠ s) (hds' : dst ≠ s') (hs : s ≠ s') (L : ℕ) (t : Alg.Tbl) (N b : ℕ)
    (ht : TblBounded L t N b) (sr : List Γ') (v : St) (S : Stacks)
    (hS : S src = encTblAsc L t ++ .blank :: sr) :
    (revTbl src dst s s').Runs v S (fun _ S' =>
        S' src = sr ∧ S' dst = encTblDesc L t ++ .blank :: S dst ∧ S' s = S s ∧ S' s' = S s' ∧
        ∀ k, k ≠ src → k ≠ dst → k ≠ s → k ≠ s' → S' k = S k)
      ((L + 1) * (N + 2) * B b) :=
  Frag.runs_mono (revTbl_tbl hsd hss hss' hds hds' hs L t N b ht sr v S hS) (fun _ _ h => h)
    (revTblC_le_B L N b)

/-- `emptyTbl` within budget (the count `L` fits in `b` bits). -/
theorem emptyTbl_le_B {c tbl s : K} (hct : c ≠ tbl) (hcs : c ≠ s) (hts : tbl ≠ s)
    (L b : ℕ) (hL : L < 2 ^ b) (cr : List Γ') (v : St) (S : Stacks)
    (hS : S c = encodeNatΓ' L ++ .comma :: cr) :
    (emptyTbl c tbl s).Runs v S (fun _ S' =>
        S' c = cr ∧ S' tbl = encTblAsc L Alg.emptyTbl ++ .blank :: S tbl ∧ S' s = S s ∧
        ∀ k, k ≠ c → k ≠ tbl → k ≠ s → S' k = S k)
      ((L + 1) * B b) :=
  Frag.runs_mono (emptyTbl_runs hct hcs hts L cr v S hS) (fun _ _ h => h) (emptyTblC_le_B hL)

/-- `lookupSlot` on a table within budget (index bit list of length `≤ 2 b`). -/
theorem lookupSlot_le_B {tbl j w s scr : K} (htj : tbl ≠ j) (htw : tbl ≠ w) (hts : tbl ≠ s)
    (htc : tbl ≠ scr) (hjw : j ≠ w) (hjs : j ≠ s) (hjc : j ≠ scr) (hws : w ≠ s) (hwc : w ≠ scr)
    (hsc : s ≠ scr) (L : ℕ) (t : Alg.Tbl) (N b : ℕ) (ht : TblBounded L t N b)
    (js : List Bool) (hm : js.length ≤ 2 * b) (hjn : toNat js < L)
    (tr jr : List Γ') (v : St) (S : Stacks)
    (hSt : S tbl = encTblAsc L t ++ tr) (hSj : S j = bits js ++ .comma :: jr) :
    (lookupSlot tbl j w s scr).Runs v S (fun _ S' =>
        S' tbl = S tbl ∧ S' j = jr ∧ S' w = encSlot (t (toNat js)) ++ S w ∧
        S' s = S s ∧ S' scr = S scr ∧
        ∀ k, k ≠ tbl → k ≠ j → k ≠ w → k ≠ s → k ≠ scr → S' k = S k)
      ((L + 1) * (N + 2) * B b) :=
  Frag.runs_mono (lookupSlot_tbl htj htw hts htc hjw hjs hjc hws hwc hsc L t N b ht js (2 * b) hm hjn
    tr jr v S hSt hSj) (fun _ _ h => h)
    ((lookC_le_B (toNat js) N b).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))))

/-- `setIfNoneF` on a table within budget (index bit list of length `≤ 2 b`). -/
theorem setIfNoneF_le_B {tbl j w s scr : K} (htj : tbl ≠ j) (htw : tbl ≠ w) (hts : tbl ≠ s)
    (htc : tbl ≠ scr) (hjw : j ≠ w) (hjs : j ≠ s) (hjc : j ≠ scr) (hws : w ≠ s) (hwc : w ≠ scr)
    (hsc : s ≠ scr) (L : ℕ) (t : Alg.Tbl) (N b : ℕ) (ht : TblBounded L t N b)
    (js : List Bool) (hm : js.length ≤ 2 * b) (hjn : toNat js < L)
    (W : List ℕ) (hWN : W.length ≤ N) (hWb : ∀ q ∈ W, q < 2 ^ b)
    (tr jr wr : List Γ') (v : St) (S : Stacks)
    (hSt : S tbl = encTblAsc L t ++ tr) (hSj : S j = bits js ++ .comma :: jr)
    (hSw : S w = encList W ++ wr) :
    (setIfNoneF tbl j w s scr).Runs v S (fun _ S' =>
        S' tbl = encTblAsc L (Alg.setIfNone t (toNat js) W) ++ tr ∧ S' j = jr ∧ S' w = wr ∧
        S' s = S s ∧ S' scr = S scr ∧
        ∀ k, k ≠ tbl → k ≠ j → k ≠ w → k ≠ s → k ≠ scr → S' k = S k)
      ((L + 1) * (N + 2) * B b) :=
  Frag.runs_mono (setIfNoneF_tbl htj htw hts htc hjw hjs hjc hws hwc hsc L t N b ht js (2 * b) hm hjn
    W hWN hWb tr jr wr v S hSt hSj hSw) (fun _ _ h => h)
    ((setC_le_B (toNat js) N b).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))))

theorem copyC_le_B (L N b : ℕ) : copyC L N b ≤ (L + 1) * (N + 2) * B b := by
  have h1 := slotC_le N b
  have h2 : copySlotC N b ≤ (N + 2) * (64 * (b + 2)) := by unfold copySlotC; nlinarith
  have h3 : (N + 2) * (64 * (b + 2)) ≤ (N + 2) * B b := Nat.mul_le_mul_left _ (linear_le_B le_rfl)
  have h4 : 8 ≤ (N + 2) * B b := by
    have := one_le_B b; nlinarith
  calc copyC L N b = L * copySlotC N b + 8 := rfl
    _ ≤ L * ((N + 2) * B b) + (N + 2) * B b :=
        Nat.add_le_add (Nat.mul_le_mul_left _ (h2.trans h3)) h4
    _ = (L + 1) * (N + 2) * B b := by ring

/-- `copyTbl` on a table within budget. -/
theorem copyTbl_le_B {src dst hold s s' : K} (hsd : src ≠ dst) (hsh : src ≠ hold) (hss : src ≠ s)
    (hss' : src ≠ s') (hdh : dst ≠ hold) (hds : dst ≠ s) (hds' : dst ≠ s') (hhs : hold ≠ s)
    (hhs' : hold ≠ s') (hs : s ≠ s') (L : ℕ) (t : Alg.Tbl) (N b : ℕ) (ht : TblBounded L t N b)
    (sr : List Γ') (v : St) (S : Stacks) (hS : S src = encTblAsc L t ++ .blank :: sr) :
    (copyTbl src dst hold s s').Runs v S (fun _ S' =>
        S' src = S src ∧ S' dst = encTblDesc L t ++ .blank :: S dst ∧ S' hold = S hold ∧
        S' s = S s ∧ S' s' = S s' ∧
        ∀ k, k ≠ src → k ≠ dst → k ≠ hold → k ≠ s → k ≠ s' → S' k = S k)
      ((L + 1) * (N + 2) * B b) :=
  Frag.runs_mono (copyTbl_tbl hsd hsh hss hss' hdh hds hds' hhs hhs' hs L t N b ht sr v S hS)
    (fun _ _ h => h) (copyC_le_B L N b)

end Carmichael.TM
