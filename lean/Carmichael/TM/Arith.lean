import Carmichael.TM.Frag
import Mathlib.Data.Nat.Log
import Mathlib.Data.Num.Lemmas

/-!
# Route T arithmetic fragments: addition and comparison

Numbers live on stacks as bit lists, least significant bit on top, followed
by a `Γ'.comma` terminator: a stack holding `a` on top of `rest` is
`encodeNatΓ' a ++ Γ'.comma :: rest`, where `encodeNatΓ' = encodingNatΓ'.encode`
is Mathlib's encoding (LSB first, no leading zeros).  Fragments consume the
top number of each operand stack (including its terminator).

* `OpA`/`OpB`: the state of an operand during a loop, with `OpA.read` /
  `OpB.read` describing the "read one bit unless exhausted" phase once, so
  each two-operand loop is proven with one case per clause of its reference
  function.
* `addLoop x y z`: schoolbook adder; consumes the top numbers of `x` and `y`,
  leaves the sum on `z` most-significant bit on top (below a fresh `comma`).
* `moveNum src dst`: pops the top number of `src` onto `dst`, reversing it.
* `add x y z w = addLoop x y z ; push comma on w ; moveNum z w`: the sum ends
  on `w` in the standard orientation, `z` is restored.
* `cmpFrag x y`: consumes the top numbers of `x`, `y` and sets `St.cmp` to
  `compare a b`.

Every fragment comes with a `Runs` triple giving the exact stack contents and
a step bound linear in the bit lengths, plus a corollary in terms of
`Nat.log 2`.
-/

namespace Carmichael.TM

open Turing Turing.TM2 Turing.TM2.Stmt Computability

/-! ### Bit encodings -/

/-- A bit list as stack symbols. -/
def bits (l : List Bool) : List Γ' := l.map Γ'.bit

@[simp] theorem bits_nil : bits [] = [] := rfl
@[simp] theorem bits_cons (b : Bool) (l : List Bool) : bits (b :: l) = Γ'.bit b :: bits l := rfl
@[simp] theorem bits_append (l₁ l₂ : List Bool) : bits (l₁ ++ l₂) = bits l₁ ++ bits l₂ :=
  List.map_append ..
@[simp] theorem bits_reverse (l : List Bool) : bits l.reverse = (bits l).reverse :=
  List.map_reverse ..
@[simp] theorem bits_length (l : List Bool) : (bits l).length = l.length := List.length_map ..

/-- Value of a little-endian bit list. -/
def toNat : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat + 2 * toNat l

/-- Mathlib's encoding of `ℕ` in `Γ'` (LSB first, no leading zeros), as a
stack segment; the caller adds the `comma` terminator. -/
abbrev encodeNatΓ' (n : ℕ) : List Γ' := encodingNatΓ'.encode n

theorem encodeNatΓ'_eq (n : ℕ) : encodeNatΓ' n = bits (Computability.encodeNat n) := rfl

theorem toNat_encodePosNum (p : PosNum) : toNat (encodePosNum p) = p := by
  induction p with
  | one => rfl
  | bit0 p ih => simp [encodePosNum, toNat, ih, PosNum.cast_bit0]; omega
  | bit1 p ih => simp [encodePosNum, toNat, ih, PosNum.cast_bit1]; omega

theorem toNat_encodeNat (n : ℕ) : toNat (Computability.encodeNat n) = n := by
  have h := Num.to_of_nat n
  unfold Computability.encodeNat
  rcases hn : (n : Num) with _ | p
  · rw [hn] at h; simpa [encodeNum, toNat] using h
  · rw [hn, Num.cast_pos] at h; rw [encodeNum, toNat_encodePosNum, h]

theorem encodePosNum_length_le (p : PosNum) :
    (encodePosNum p).length ≤ Nat.log 2 p + 1 := by
  induction p with
  | one => simp [encodePosNum]
  | bit0 p ih =>
    have hp : 1 ≤ (p : ℕ) := PosNum.one_le_cast p
    rw [encodePosNum, List.length_cons, PosNum.cast_bit0,
      Nat.log_of_one_lt_of_le one_lt_two (by omega : 2 ≤ (p : ℕ) + p),
      show ((p : ℕ) + p) / 2 = p by omega]
    omega
  | bit1 p ih =>
    have hp : 1 ≤ (p : ℕ) := PosNum.one_le_cast p
    rw [encodePosNum, List.length_cons, PosNum.cast_bit1,
      Nat.log_of_one_lt_of_le one_lt_two (by omega : 2 ≤ (p : ℕ) + p + 1),
      show ((p : ℕ) + p + 1) / 2 = p by omega]
    omega

theorem encodeNat_length_le (n : ℕ) : (Computability.encodeNat n).length ≤ Nat.log 2 n + 1 := by
  have h := Num.to_of_nat n
  unfold Computability.encodeNat
  rcases hn : (n : Num) with _ | p
  · simp [encodeNum]
  · rw [hn, Num.cast_pos] at h; rw [encodeNum, ← h]; exact encodePosNum_length_le p

theorem encodeNatΓ'_length_le (n : ℕ) : (encodeNatΓ' n).length ≤ Nat.log 2 n + 1 := by
  simpa [encodeNatΓ'_eq] using encodeNat_length_le n

/-! ### Schoolbook adder and comparator on bit lists -/

/-- Sum bit of a full adder. -/
def sumBit (a b c : Bool) : Bool := xor (xor a b) c

/-- Carry-out of a full adder. -/
def maj (a b c : Bool) : Bool := (a && b) || (c && (a || b))

/-- Register contents as a bit (missing = 0). -/
def bitOf (o : Option Bool) : Bool := o.getD false

@[simp] theorem bitOf_some (b : Bool) : bitOf (some b) = b := rfl
@[simp] theorem bitOf_none : bitOf none = false := rfl

/-- The final carry as a bit list. -/
def addCarry (c : Bool) : List Bool := if c then [true] else []

/-- Ripple-carry addition on little-endian bit lists with carry-in `c`. -/
def addBits : List Bool → List Bool → Bool → List Bool
  | [], [], c => addCarry c
  | a :: xs, [], c => sumBit a false c :: addBits xs [] (maj a false c)
  | [], b :: ys, c => sumBit false b c :: addBits [] ys (maj false b c)
  | a :: xs, b :: ys, c => sumBit a b c :: addBits xs ys (maj a b c)

theorem toNat_addBits (xs ys : List Bool) (c : Bool) :
    toNat (addBits xs ys c) = toNat xs + toNat ys + c.toNat := by
  induction xs, ys, c using addBits.induct with
  | case1 c => cases c <;> simp [addBits, addCarry, toNat]
  | case2 a xs c ih =>
    simp only [addBits, toNat]; rw [ih]
    cases a <;> cases c <;> simp [toNat, sumBit, maj] <;> omega
  | case3 b ys c ih =>
    simp only [addBits, toNat]; rw [ih]
    cases b <;> cases c <;> simp [toNat, sumBit, maj] <;> omega
  | case4 a xs b ys c ih =>
    simp only [addBits, toNat]; rw [ih]
    cases a <;> cases b <;> cases c <;> simp [toNat, sumBit, maj] <;> omega

theorem addBits_length (xs ys : List Bool) (c : Bool) :
    (addBits xs ys c).length ≤ max xs.length ys.length + 1 := by
  induction xs, ys, c using addBits.induct with
  | case1 c => cases c <;> simp [addBits, addCarry]
  | case2 a xs c ih => simp only [addBits, List.length_cons, List.length_nil] at ih ⊢; omega
  | case3 b ys c ih => simp only [addBits, List.length_cons, List.length_nil] at ih ⊢; omega
  | case4 a xs b ys c ih => simp only [addBits, List.length_cons] at ih ⊢; omega

/-- One comparator step, LSB-first: a differing bit overrides the verdict so far. -/
def cmpStep (a b : Bool) (c : Ordering) : Ordering :=
  if a = b then c else if a then .gt else .lt

/-- LSB-first comparison of bit lists (missing bits count as `0`), accumulator `c`. -/
def cmpBits : List Bool → List Bool → Ordering → Ordering
  | [], [], c => c
  | a :: xs, [], c => cmpBits xs [] (cmpStep a false c)
  | [], b :: ys, c => cmpBits [] ys (cmpStep false b c)
  | a :: xs, b :: ys, c => cmpBits xs ys (cmpStep a b c)

theorem cmpStep_shift (a b : Bool) (A B : ℕ) (c : Ordering) :
    (if A = B then cmpStep a b c else compare A B) =
      if a.toNat + 2 * A = b.toNat + 2 * B then c
      else compare (a.toNat + 2 * A) (b.toNat + 2 * B) := by
  rcases lt_trichotomy A B with h | rfl | h
  · have h1 : a.toNat + 2 * A < b.toNat + 2 * B := by cases a <;> cases b <;> simp <;> omega
    rw [if_neg h.ne, if_neg h1.ne, compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr h1]
  · cases a <;> cases b
    · simp [cmpStep]
    · simp [cmpStep]; exact (compare_lt_iff_lt.mpr (by omega)).symm
    · simp [cmpStep]; exact (compare_gt_iff_gt.mpr (by omega)).symm
    · simp [cmpStep]
  · have h1 : b.toNat + 2 * B < a.toNat + 2 * A := by cases a <;> cases b <;> simp <;> omega
    rw [if_neg h.ne', if_neg h1.ne', compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr h1]

theorem cmpBits_eq (xs ys : List Bool) (c : Ordering) :
    cmpBits xs ys c = if toNat xs = toNat ys then c else compare (toNat xs) (toNat ys) := by
  induction xs, ys, c using cmpBits.induct with
  | case1 c => simp [cmpBits]
  | case2 a xs c ih => rw [cmpBits, ih, cmpStep_shift]; rfl
  | case3 b ys c ih => rw [cmpBits, ih, cmpStep_shift]; rfl
  | case4 a xs b ys c ih => rw [cmpBits, ih, cmpStep_shift]; rfl

theorem cmpBits_eq_compare (xs ys : List Bool) :
    cmpBits xs ys .eq = compare (toNat xs) (toNat ys) := by
  rw [cmpBits_eq]
  split_ifs with h
  · exact (compare_eq_iff_eq.mpr h).symm
  · rfl

/-! ### Reading a symbol into a register -/

/-- Pop-handler for operand `a`: a bit goes to `ra`; a terminator or an empty
stack marks the operand exhausted (`da`), clearing `ra`. -/
def readA (v : St) (o : Option Γ') : St :=
  match o with
  | some (.bit b) => { v with ra := some b }
  | _ => { v with ra := none, da := true }

/-- Pop-handler for operand `b`. -/
def readB (v : St) (o : Option Γ') : St :=
  match o with
  | some (.bit b) => { v with rb := some b }
  | _ => { v with rb := none, db := true }

@[simp] theorem readA_bit (v : St) (b : Bool) : readA v (some (.bit b)) = { v with ra := some b } := rfl
@[simp] theorem readA_comma (v : St) : readA v (some .comma) = { v with ra := none, da := true } := rfl
@[simp] theorem readA_none (v : St) : readA v none = { v with ra := none, da := true } := rfl
@[simp] theorem readB_bit (v : St) (b : Bool) : readB v (some (.bit b)) = { v with rb := some b } := rfl
@[simp] theorem readB_comma (v : St) : readB v (some .comma) = { v with rb := none, db := true } := rfl
@[simp] theorem readB_none (v : St) : readB v none = { v with rb := none, db := true } := rfl

/-! ### Operand state and the read phase -/

/-- Operand `a` on stack `x` with `xs` bits still to read: either the flag is
clear and the stack holds `bits xs ++ comma :: xr`, or the operand is
exhausted (`xs = []`, flag set, register cleared, terminator popped). -/
def OpA (x : K) (xs : List Bool) (xr : List Γ') (v : St) (S : Stacks) : Prop :=
  (v.da = false ∧ S x = bits xs ++ .comma :: xr) ∨ (v.da = true ∧ xs = [] ∧ v.ra = none ∧ S x = xr)

/-- Operand `b` on stack `y`. -/
def OpB (y : K) (ys : List Bool) (yr : List Γ') (v : St) (S : Stacks) : Prop :=
  (v.db = false ∧ S y = bits ys ++ .comma :: yr) ∨ (v.db = true ∧ ys = [] ∧ v.rb = none ∧ S y = yr)

theorem OpA.transport {x xs xr v S v' S'} (h : OpA x xs xr v S) (hd : v'.da = v.da)
    (hr : v'.ra = v.ra) (hS : S' x = S x) : OpA x xs xr v' S' := by
  unfold OpA at *; rw [hd, hr, hS]; exact h

theorem OpB.transport {y ys yr v S v' S'} (h : OpB y ys yr v S) (hd : v'.db = v.db)
    (hr : v'.rb = v.rb) (hS : S' y = S y) : OpB y ys yr v' S' := by
  unfold OpB at *; rw [hd, hr, hS]; exact h

/-- The read phase for operand `a`, `branch da q (pop x readA q)`: skip if
exhausted, else pop one symbol.  Afterwards `ra` holds the head bit, `da`
says whether the operand is (now) exhausted, the other registers are
untouched, and the operand state advances to the tail. -/
theorem OpA.read {x xs xr v S} (h : OpA x xs xr v S) :
    ∃ v₁ S₁, (∀ {Λ : Type} (q : Stmt' Λ),
        stepAux (branch (fun v => v.da) q (pop x readA q)) v S = stepAux q v₁ S₁) ∧
      v₁.ra = xs.head? ∧ v₁.da = decide (xs = []) ∧ (xs = [] → S₁ x = xr) ∧
      v₁.carry = v.carry ∧ v₁.rb = v.rb ∧ v₁.db = v.db ∧ v₁.cmp = v.cmp ∧ v₁.flag = v.flag ∧
      OpA x xs.tail xr v₁ S₁ ∧ ∀ k, k ≠ x → S₁ k = S k := by
  rcases h with ⟨hda, hSx⟩ | ⟨hda, rfl, hra, hSx⟩
  · cases xs with
    | nil =>
      exact ⟨{ v with ra := none, da := true }, Function.update S x xr,
        fun q => by simp [hda, hSx], rfl, rfl, fun _ => by simp, rfl, rfl, rfl, rfl, rfl,
        Or.inr ⟨rfl, rfl, rfl, by simp⟩, fun k hk => by simp [Function.update_of_ne hk]⟩
    | cons a xs =>
      exact ⟨{ v with ra := some a }, Function.update S x (bits xs ++ .comma :: xr),
        fun q => by simp [hda, hSx], rfl, by simp [hda], (fun h => absurd h (List.cons_ne_nil _ _)), rfl, rfl, rfl, rfl, rfl,
        Or.inl ⟨hda, by simp⟩, fun k hk => by simp [Function.update_of_ne hk]⟩
  · exact ⟨v, S, fun q => by simp [hda], by simp [hra], by simp [hda], fun _ => hSx,
      rfl, rfl, rfl, rfl, rfl, Or.inr ⟨hda, rfl, hra, hSx⟩, fun _ _ => rfl⟩

/-- The read phase for operand `b`, `branch db q (pop y readB q)`. -/
theorem OpB.read {y ys yr v S} (h : OpB y ys yr v S) :
    ∃ v₁ S₁, (∀ {Λ : Type} (q : Stmt' Λ),
        stepAux (branch (fun v => v.db) q (pop y readB q)) v S = stepAux q v₁ S₁) ∧
      v₁.rb = ys.head? ∧ v₁.db = decide (ys = []) ∧ (ys = [] → S₁ y = yr) ∧
      v₁.carry = v.carry ∧ v₁.ra = v.ra ∧ v₁.da = v.da ∧ v₁.cmp = v.cmp ∧ v₁.flag = v.flag ∧
      OpB y ys.tail yr v₁ S₁ ∧ ∀ k, k ≠ y → S₁ k = S k := by
  rcases h with ⟨hdb, hSy⟩ | ⟨hdb, rfl, hrb, hSy⟩
  · cases ys with
    | nil =>
      exact ⟨{ v with rb := none, db := true }, Function.update S y yr,
        fun q => by simp [hdb, hSy], rfl, rfl, fun _ => by simp, rfl, rfl, rfl, rfl, rfl,
        Or.inr ⟨rfl, rfl, rfl, by simp⟩, fun k hk => by simp [Function.update_of_ne hk]⟩
    | cons b ys =>
      exact ⟨{ v with rb := some b }, Function.update S y (bits ys ++ .comma :: yr),
        fun q => by simp [hdb, hSy], rfl, by simp [hdb], (fun h => absurd h (List.cons_ne_nil _ _)), rfl, rfl, rfl, rfl, rfl,
        Or.inl ⟨hdb, by simp⟩, fun k hk => by simp [Function.update_of_ne hk]⟩
  · exact ⟨v, S, fun q => by simp [hdb], by simp [hrb], by simp [hdb], fun _ => hSy,
      rfl, rfl, rfl, rfl, rfl, Or.inr ⟨hdb, rfl, hrb, hSy⟩, fun _ _ => rfl⟩

/-! ### Addition -/

/-- One iteration of the adder: read a bit from each unexhausted operand,
then either emit the sum bit and loop, or (both exhausted) flush the carry
and exit. -/
def addBody {Λ : Type} (x y z : K) (self e : Λ) : Stmt' Λ :=
  let rest : Stmt' Λ :=
    branch (fun v => v.da && v.db)
      (branch (fun v => v.carry) (push z (fun _ => .bit true) (goto fun _ => e)) (goto fun _ => e))
      (push z (fun v => .bit (sumBit (bitOf v.ra) (bitOf v.rb) v.carry))
        (load (fun v => { v with carry := maj (bitOf v.ra) (bitOf v.rb) v.carry })
          (goto fun _ => self)))
  let readY : Stmt' Λ := branch (fun v => v.db) rest (pop y readB rest)
  branch (fun v => v.da) readY (pop x readA readY)

/-- The adder fragment: label `false` initialises the registers and pushes a
`comma` on `z`; label `true` is `addBody`. -/
def addLoop (x y z : K) : Frag where
  Λf := Bool
  entry := false
  code ι e
    | false =>
      load (fun v => { v with carry := false, ra := none, rb := none, da := false, db := false })
        (push z (fun _ => .comma) (goto fun _ => ι true))
    | true => addBody x y z (ι true) e

/-- Loop invariant of `addBody`: operand states, carry `c`, output so far
`zr`, all other stacks as in `S₀`. -/
def AddInv (x y z : K) (xs ys : List Bool) (xr yr zr : List Γ') (c : Bool) (S₀ : Stacks)
    (v : St) (S : Stacks) : Prop :=
  v.carry = c ∧ OpA x xs xr v S ∧ OpB y ys yr v S ∧
  S z = zr ∧ ∀ k, k ≠ x → k ≠ y → k ≠ z → S k = S₀ k

theorem addLoop_loop {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {Λ : Type} {M : Λ → Stmt' Λ} {ι : Bool → Λ} {e : Λ} (hI : (addLoop x y z).Installed M ι e)
    {xr yr : List Γ'} {S₀ : Stacks} (xs ys : List Bool) (c : Bool) :
    ∀ (v : St) (S : Stacks) (zr : List Γ'), AddInv x y z xs ys xr yr zr c S₀ v S →
    ∃ n, n ≤ max xs.length ys.length + 1 ∧ ∃ v' S',
      RunsTo M n ⟨some (ι true), v, S⟩ ⟨some e, v', S'⟩ ∧
      S' x = xr ∧ S' y = yr ∧ S' z = (bits (addBits xs ys c)).reverse ++ zr ∧
      ∀ k, k ≠ x → k ≠ y → k ≠ z → S' k = S₀ k := by
  have hyx := hxy.symm
  have hzx := hxz.symm
  have hzy := hyz.symm
  induction xs, ys, c using addBits.induct with
  | case1 c =>
    intro v S zr ⟨hc, hA, hB, hZ, hF⟩
    obtain ⟨v₁, S₁, h1, hra₁, hda₁, hx₁, hc₁, hrb₁, hdb₁, -, -, -, hf₁⟩ := hA.read
    obtain ⟨v₂, S₂, h2, hrb₂, hdb₂, hy₂, hc₂, hra₂, hda₂, -, -, -, hf₂⟩ :=
      (hB.transport hdb₁ hrb₁ (hf₁ y hyx)).read
    have hx₂ : S₂ x = xr := (hf₂ x hxy).trans (hx₁ rfl)
    have hy₂' : S₂ y = yr := hy₂ rfl
    have hz₂ : S₂ z = zr := (hf₂ z hzy).trans ((hf₁ z hzx).trans hZ)
    have hfr : ∀ k, k ≠ x → k ≠ y → k ≠ z → S₂ k = S₀ k :=
      fun k hkx hky hkz => ((hf₂ k hky).trans (hf₁ k hkx)).trans (hF k hkx hky hkz)
    cases c
    · refine ⟨1, by simp, v₂, S₂, runsTo_succ ?_ (runsTo_zero M _), hx₂, hy₂',
        by simp [addBits, addCarry, hz₂], hfr⟩
      tm_step true only [addLoop, addBody, h1, h2] [hda₂, hda₁, hdb₂, hc₂, hc₁, hc]
    · refine ⟨1, by simp, v₂, Function.update S₂ z (.bit true :: zr),
        runsTo_succ ?_ (runsTo_zero M _), by simp [Function.update_of_ne hxz, hx₂],
        by simp [Function.update_of_ne hyz, hy₂'], by simp [addBits, addCarry],
        fun k hkx hky hkz => by simp [Function.update_of_ne hkz, hfr k hkx hky hkz]⟩
      tm_step true only [addLoop, addBody, h1, h2] [hda₂, hda₁, hdb₂, hc₂, hc₁, hc, hz₂]
  | case2 a xs c ih =>
    intro v S zr ⟨hc, hA, hB, hZ, hF⟩
    obtain ⟨v₁, S₁, h1, hra₁, hda₁, -, hc₁, hrb₁, hdb₁, -, -, hA₁, hf₁⟩ := hA.read
    obtain ⟨v₂, S₂, h2, hrb₂, hdb₂, -, hc₂, hra₂, hda₂, -, -, hB₂, hf₂⟩ :=
      (hB.transport hdb₁ hrb₁ (hf₁ y hyx)).read
    have hz₂ : S₂ z = zr := (hf₂ z hzy).trans ((hf₁ z hzx).trans hZ)
    have hstep : TM2.step M ⟨some (ι true), v, S⟩ = some ⟨some (ι true),
        { v₂ with carry := maj a false c }, Function.update S₂ z (.bit (sumBit a false c) :: zr)⟩ := by
      tm_step true only [addLoop, addBody, h1, h2]
        [hra₂, hra₁, hrb₂, hda₂, hda₁, hdb₂, hc₂, hc₁, hc, hz₂]
    have hinv : AddInv x y z xs [] xr yr (.bit (sumBit a false c) :: zr) (maj a false c) S₀
        { v₂ with carry := maj a false c } (Function.update S₂ z (.bit (sumBit a false c) :: zr)) :=
      ⟨rfl, (hA₁.transport hda₂ hra₂ (hf₂ x hxy)).transport rfl rfl (by simp [Function.update_of_ne hxz]),
        hB₂.transport rfl rfl (by simp [Function.update_of_ne hyz]), by simp,
        fun k hkx hky hkz => by
          simp [Function.update_of_ne hkz, hf₂ k hky, hf₁ k hkx, hF k hkx hky hkz]⟩
    obtain ⟨n, hn, v', S', hr, hx', hy', hz', hf'⟩ := ih _ _ _ hinv
    refine ⟨n + 1, ?_, v', S', runsTo_succ hstep hr, hx', hy', ?_, hf'⟩
    · simp only [List.length_cons, List.length_nil] at hn ⊢; omega
    · rw [hz']; simp [addBits]
  | case3 b ys c ih =>
    intro v S zr ⟨hc, hA, hB, hZ, hF⟩
    obtain ⟨v₁, S₁, h1, hra₁, hda₁, -, hc₁, hrb₁, hdb₁, -, -, hA₁, hf₁⟩ := hA.read
    obtain ⟨v₂, S₂, h2, hrb₂, hdb₂, -, hc₂, hra₂, hda₂, -, -, hB₂, hf₂⟩ :=
      (hB.transport hdb₁ hrb₁ (hf₁ y hyx)).read
    have hz₂ : S₂ z = zr := (hf₂ z hzy).trans ((hf₁ z hzx).trans hZ)
    have hstep : TM2.step M ⟨some (ι true), v, S⟩ = some ⟨some (ι true),
        { v₂ with carry := maj false b c }, Function.update S₂ z (.bit (sumBit false b c) :: zr)⟩ := by
      tm_step true only [addLoop, addBody, h1, h2]
        [hra₂, hra₁, hrb₂, hda₂, hda₁, hdb₂, hc₂, hc₁, hc, hz₂]
    have hinv : AddInv x y z [] ys xr yr (.bit (sumBit false b c) :: zr) (maj false b c) S₀
        { v₂ with carry := maj false b c } (Function.update S₂ z (.bit (sumBit false b c) :: zr)) :=
      ⟨rfl, (hA₁.transport hda₂ hra₂ (hf₂ x hxy)).transport rfl rfl (by simp [Function.update_of_ne hxz]),
        hB₂.transport rfl rfl (by simp [Function.update_of_ne hyz]), by simp,
        fun k hkx hky hkz => by
          simp [Function.update_of_ne hkz, hf₂ k hky, hf₁ k hkx, hF k hkx hky hkz]⟩
    obtain ⟨n, hn, v', S', hr, hx', hy', hz', hf'⟩ := ih _ _ _ hinv
    refine ⟨n + 1, ?_, v', S', runsTo_succ hstep hr, hx', hy', ?_, hf'⟩
    · simp only [List.length_cons, List.length_nil] at hn ⊢; omega
    · rw [hz']; simp [addBits]
  | case4 a xs b ys c ih =>
    intro v S zr ⟨hc, hA, hB, hZ, hF⟩
    obtain ⟨v₁, S₁, h1, hra₁, hda₁, -, hc₁, hrb₁, hdb₁, -, -, hA₁, hf₁⟩ := hA.read
    obtain ⟨v₂, S₂, h2, hrb₂, hdb₂, -, hc₂, hra₂, hda₂, -, -, hB₂, hf₂⟩ :=
      (hB.transport hdb₁ hrb₁ (hf₁ y hyx)).read
    have hz₂ : S₂ z = zr := (hf₂ z hzy).trans ((hf₁ z hzx).trans hZ)
    have hstep : TM2.step M ⟨some (ι true), v, S⟩ = some ⟨some (ι true),
        { v₂ with carry := maj a b c }, Function.update S₂ z (.bit (sumBit a b c) :: zr)⟩ := by
      tm_step true only [addLoop, addBody, h1, h2]
        [hra₂, hra₁, hrb₂, hda₂, hda₁, hdb₂, hc₂, hc₁, hc, hz₂]
    have hinv : AddInv x y z xs ys xr yr (.bit (sumBit a b c) :: zr) (maj a b c) S₀
        { v₂ with carry := maj a b c } (Function.update S₂ z (.bit (sumBit a b c) :: zr)) :=
      ⟨rfl, (hA₁.transport hda₂ hra₂ (hf₂ x hxy)).transport rfl rfl (by simp [Function.update_of_ne hxz]),
        hB₂.transport rfl rfl (by simp [Function.update_of_ne hyz]), by simp,
        fun k hkx hky hkz => by
          simp [Function.update_of_ne hkz, hf₂ k hky, hf₁ k hkx, hF k hkx hky hkz]⟩
    obtain ⟨n, hn, v', S', hr, hx', hy', hz', hf'⟩ := ih _ _ _ hinv
    refine ⟨n + 1, ?_, v', S', runsTo_succ hstep hr, hx', hy', ?_, hf'⟩
    · simp only [List.length_cons] at hn ⊢; omega
    · rw [hz']; simp [addBits]

/-- The adder: consumes the top numbers of `x` and `y`; leaves
`comma` then the sum (MSB on top) on `z`; other stacks untouched. -/
theorem addLoop_runs {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (xs ys : List Bool) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ys ++ .comma :: yr) :
    (addLoop x y z).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ S' z = (bits (addBits xs ys false)).reverse ++ .comma :: S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → S' k = S k)
      (max xs.length ys.length + 2) := by
  constructor
  intro Λ M ι e hI
  have hstep : TM2.step M ⟨some (ι false), v, S⟩ = some
      ⟨some (ι true), { v with carry := false, ra := none, rb := none, da := false, db := false },
        Function.update S z (.comma :: S z)⟩ := by
    tm_step false [addLoop]
  obtain ⟨n, hn, v', S', hr, hx', hy', hz', hf'⟩ :=
    addLoop_loop hxy hxz hyz hI (xr := xr) (yr := yr) (S₀ := S) xs ys false
      { v with carry := false, ra := none, rb := none, da := false, db := false }
      (Function.update S z (.comma :: S z)) (.comma :: S z)
      ⟨rfl, Or.inl ⟨rfl, by simp [Function.update_of_ne hxz, hSx]⟩,
        Or.inl ⟨rfl, by simp [Function.update_of_ne hyz, hSy]⟩, by simp,
        fun k hkx hky hkz => by simp [Function.update_of_ne hkz]⟩
  exact ⟨n + 1, by omega, v', S', runsTo_succ hstep hr, hx', hy', hz', hf'⟩

/-! ### Moving (reversing) a number between stacks -/

/-- Pop a symbol from `src`; a bit is pushed on `dst` and we loop, the
terminator (or empty stack) ends the fragment. -/
def moveBody {Λ : Type} (src dst : K) (self e : Λ) : Stmt' Λ :=
  pop src readA
    (branch (fun v => v.ra.isSome)
      (push dst (fun v => .bit (bitOf v.ra)) (goto fun _ => self))
      (goto fun _ => e))

/-- Move the top number of `src` onto `dst`, reversed, consuming the terminator. -/
def moveNum (src dst : K) : Frag where
  Λf := Unit
  entry := ()
  code ι e _ := moveBody src dst (ι ()) e

theorem moveNum_loop {src dst : K} (hsd : src ≠ dst)
    {Λ : Type} {M : Λ → Stmt' Λ} {ι : Unit → Λ} {e : Λ} (hI : (moveNum src dst).Installed M ι e)
    {sr : List Γ'} {S₀ : Stacks} (l : List Bool) :
    ∀ (v : St) (S : Stacks) (dr : List Γ'), S src = bits l ++ .comma :: sr → S dst = dr →
      (∀ k, k ≠ src → k ≠ dst → S k = S₀ k) →
    ∃ n, n ≤ l.length + 1 ∧ ∃ v' S',
      RunsTo M n ⟨some (ι ()), v, S⟩ ⟨some e, v', S'⟩ ∧
      S' src = sr ∧ S' dst = (bits l).reverse ++ dr ∧ ∀ k, k ≠ src → k ≠ dst → S' k = S₀ k := by
  have hds := hsd.symm
  induction l with
  | nil =>
    intro v S dr hS hD hF
    refine ⟨1, by simp, { v with ra := none, da := true }, Function.update S src sr,
      runsTo_succ ?_ (runsTo_zero M _), by simp, by simp [Function.update_of_ne hds, hD],
      fun k hks hkd => by simp [Function.update_of_ne hks, hF k hks hkd]⟩
    tm_step () [moveNum, moveBody, hS]
  | cons b l ih =>
    intro v S dr hS hD hF
    obtain ⟨n, hn, v', S', hr, hs', hd', hf'⟩ :=
      ih { v with ra := some b }
        (Function.update (Function.update S src (bits l ++ .comma :: sr)) dst (.bit b :: dr))
        (.bit b :: dr) (by simp [Function.update_of_ne hsd]) (by simp)
        (fun k hks hkd => by
          simp [Function.update_of_ne hks, Function.update_of_ne hkd, hF k hks hkd])
    refine ⟨n + 1, ?_, v', S', runsTo_succ ?_ hr, hs', ?_, hf'⟩
    · simp only [List.length_cons] at hn ⊢; omega
    · tm_step () [moveNum, moveBody, hS, hD, hsd, hds]
    · rw [hd']; simp

theorem moveNum_runs {src dst : K} (hsd : src ≠ dst) (l : List Bool) (sr : List Γ')
    (v : St) (S : Stacks) (hS : S src = bits l ++ .comma :: sr) :
    (moveNum src dst).Runs v S (fun _ S' =>
        S' src = sr ∧ S' dst = (bits l).reverse ++ S dst ∧ ∀ k, k ≠ src → k ≠ dst → S' k = S k)
      (l.length + 1) := by
  constructor
  intro Λ M ι e hI
  exact moveNum_loop hsd hI (S₀ := S) l v S (S dst) hS rfl (fun _ _ _ => rfl)

/-! ### Addition, assembled -/

/-- `w := x + y` using scratch stack `z`: the sum is left on `w` in standard
orientation with its terminator; `x`, `y` lose their top numbers; `z` is
restored. -/
def add (x y z w : K) : Frag :=
  (addLoop x y z).seq ((Frag.pushSym w .comma).seq (moveNum z w))

theorem add_runs {x y z w : K} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) (xs ys : List Bool) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ys ++ .comma :: yr) :
    (add x y z w).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ S' z = S z ∧ S' w = bits (addBits xs ys false) ++ .comma :: S w ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → k ≠ w → S' k = S k)
      (2 * max xs.length ys.length + 5) := by
  have hwz := hzw.symm
  have h1 := addLoop_runs hxy hxz hyz xs ys xr yr v S hSx hSy
  have h2 : ∀ v₁ S₁, (S₁ x = xr ∧ S₁ y = yr ∧
      S₁ z = (bits (addBits xs ys false)).reverse ++ .comma :: S z ∧
      ∀ k, k ≠ x → k ≠ y → k ≠ z → S₁ k = S k) →
      ((Frag.pushSym w .comma).seq (moveNum z w)).Runs v₁ S₁ (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ S' z = S z ∧ S' w = bits (addBits xs ys false) ++ .comma :: S w ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → k ≠ w → S' k = S k)
      (1 + (max xs.length ys.length + 2)) := by
    intro v₁ S₁ ⟨hx₁, hy₁, hz₁, hf₁⟩
    refine Frag.seq_runs (Frag.pushSym_runs w .comma v₁ S₁) fun v₂ S₂ ⟨hv₂, hS₂⟩ => ?_
    subst hS₂
    have h3 := moveNum_runs hzw (addBits xs ys false).reverse (S z) v₂
      (Function.update S₁ w (.comma :: S₁ w)) (by simp [Function.update_of_ne hzw, hz₁])
    refine Frag.runs_mono h3 (fun v₃ S₃ ⟨hz₃, hw₃, hf₃⟩ => ?_) ?_
    · refine ⟨?_, ?_, hz₃, ?_, ?_⟩
      · rw [hf₃ x hxz hxw]; simp [Function.update_of_ne hxw, hx₁]
      · rw [hf₃ y hyz hyw]; simp [Function.update_of_ne hyw, hy₁]
      · rw [hw₃]; simp [hf₁ w hxw.symm hyw.symm hwz]
      · intro k hkx hky hkz hkw
        rw [hf₃ k hkz hkw]; simp [Function.update_of_ne hkw, hf₁ k hkx hky hkz]
    · have := addBits_length xs ys false
      simp only [List.length_reverse]; omega
  exact Frag.runs_mono (Frag.seq_runs h1 h2) (fun _ _ h => h) (by omega)

/-- Addition, stated on naturals: with `a`, `b` encoded on `x`, `y`, the machine
leaves a bit list of value `a + b` on `w`, within `9 * (log₂ a + log₂ b + 1)` steps. -/
theorem add_correct {x y z w : K} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) (a b : ℕ) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' b ++ .comma :: yr) :
    (add x y z w).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ S' z = S z ∧
        (∃ l, toNat l = a + b ∧ S' w = bits l ++ .comma :: S w) ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → k ≠ w → S' k = S k)
      (9 * (Nat.log 2 a + Nat.log 2 b + 1)) := by
  have h := add_runs hxy hxz hxw hyz hyw hzw (Computability.encodeNat a)
    (Computability.encodeNat b) xr yr v S hSx hSy
  refine Frag.runs_mono h (fun v' S' ⟨hx, hy, hz, hw, hf⟩ =>
    ⟨hx, hy, hz, ⟨_, by rw [toNat_addBits, toNat_encodeNat, toNat_encodeNat]; rfl, hw⟩, hf⟩) ?_
  have ha := encodeNat_length_le a
  have hb := encodeNat_length_le b
  omega

/-! ### Comparison -/

/-- One iteration of the comparator: read a bit from each unexhausted
operand; both exhausted exits, otherwise fold the bits into `cmp` and loop. -/
def cmpBody {Λ : Type} (x y : K) (self e : Λ) : Stmt' Λ :=
  let rest : Stmt' Λ :=
    branch (fun v => v.da && v.db)
      (goto fun _ => e)
      (load (fun v => { v with cmp := cmpStep (bitOf v.ra) (bitOf v.rb) v.cmp })
        (goto fun _ => self))
  let readY : Stmt' Λ := branch (fun v => v.db) rest (pop y readB rest)
  branch (fun v => v.da) readY (pop x readA readY)

/-- The comparator fragment: label `false` resets the registers, `true` is `cmpBody`. -/
def cmpFrag (x y : K) : Frag where
  Λf := Bool
  entry := false
  code ι e
    | false =>
      load (fun v => { v with cmp := .eq, ra := none, rb := none, da := false, db := false })
        (goto fun _ => ι true)
    | true => cmpBody x y (ι true) e

/-- Loop invariant of `cmpBody`. -/
def CmpInv (x y : K) (xs ys : List Bool) (xr yr : List Γ') (c : Ordering) (S₀ : Stacks)
    (v : St) (S : Stacks) : Prop :=
  v.cmp = c ∧ OpA x xs xr v S ∧ OpB y ys yr v S ∧ ∀ k, k ≠ x → k ≠ y → S k = S₀ k

theorem cmpFrag_loop {x y : K} (hxy : x ≠ y)
    {Λ : Type} {M : Λ → Stmt' Λ} {ι : Bool → Λ} {e : Λ} (hI : (cmpFrag x y).Installed M ι e)
    {xr yr : List Γ'} {S₀ : Stacks} (xs ys : List Bool) (c : Ordering) :
    ∀ (v : St) (S : Stacks), CmpInv x y xs ys xr yr c S₀ v S →
    ∃ n, n ≤ max xs.length ys.length + 1 ∧ ∃ v' S',
      RunsTo M n ⟨some (ι true), v, S⟩ ⟨some e, v', S'⟩ ∧
      v'.cmp = cmpBits xs ys c ∧ S' x = xr ∧ S' y = yr ∧ ∀ k, k ≠ x → k ≠ y → S' k = S₀ k := by
  have hyx := hxy.symm
  induction xs, ys, c using cmpBits.induct with
  | case1 c =>
    intro v S ⟨hc, hA, hB, hF⟩
    obtain ⟨v₁, S₁, h1, hra₁, hda₁, hx₁, -, hrb₁, hdb₁, hcmp₁, -, -, hf₁⟩ := hA.read
    obtain ⟨v₂, S₂, h2, hrb₂, hdb₂, hy₂, -, hra₂, hda₂, hcmp₂, -, -, hf₂⟩ :=
      (hB.transport hdb₁ hrb₁ (hf₁ y hyx)).read
    refine ⟨1, by simp, v₂, S₂, runsTo_succ ?_ (runsTo_zero M _),
      by simp [cmpBits, hcmp₂, hcmp₁, hc], (hf₂ x hxy).trans (hx₁ rfl), hy₂ rfl,
      fun k hkx hky => ((hf₂ k hky).trans (hf₁ k hkx)).trans (hF k hkx hky)⟩
    tm_step true only [cmpFrag, cmpBody, h1, h2] [hda₂, hda₁, hdb₂]
  | case2 a xs c ih =>
    intro v S ⟨hc, hA, hB, hF⟩
    obtain ⟨v₁, S₁, h1, hra₁, hda₁, -, -, hrb₁, hdb₁, hcmp₁, -, hA₁, hf₁⟩ := hA.read
    obtain ⟨v₂, S₂, h2, hrb₂, hdb₂, -, -, hra₂, hda₂, hcmp₂, -, hB₂, hf₂⟩ :=
      (hB.transport hdb₁ hrb₁ (hf₁ y hyx)).read
    have hstep : TM2.step M ⟨some (ι true), v, S⟩ = some ⟨some (ι true),
        { v₂ with cmp := cmpStep a false c }, S₂⟩ := by
      tm_step true only [cmpFrag, cmpBody, h1, h2]
        [hra₂, hra₁, hrb₂, hda₂, hda₁, hdb₂, hcmp₂, hcmp₁, hc]
    have hinv : CmpInv x y xs [] xr yr (cmpStep a false c) S₀ { v₂ with cmp := cmpStep a false c } S₂ :=
      ⟨rfl, (hA₁.transport hda₂ hra₂ (hf₂ x hxy)).transport rfl rfl rfl,
        hB₂.transport rfl rfl rfl,
        fun k hkx hky => ((hf₂ k hky).trans (hf₁ k hkx)).trans (hF k hkx hky)⟩
    obtain ⟨n, hn, v', S', hr, hc', hx', hy', hf'⟩ := ih _ _ hinv
    refine ⟨n + 1, ?_, v', S', runsTo_succ hstep hr, ?_, hx', hy', hf'⟩
    · simp only [List.length_cons, List.length_nil] at hn ⊢; omega
    · rw [hc', cmpBits]
  | case3 b ys c ih =>
    intro v S ⟨hc, hA, hB, hF⟩
    obtain ⟨v₁, S₁, h1, hra₁, hda₁, -, -, hrb₁, hdb₁, hcmp₁, -, hA₁, hf₁⟩ := hA.read
    obtain ⟨v₂, S₂, h2, hrb₂, hdb₂, -, -, hra₂, hda₂, hcmp₂, -, hB₂, hf₂⟩ :=
      (hB.transport hdb₁ hrb₁ (hf₁ y hyx)).read
    have hstep : TM2.step M ⟨some (ι true), v, S⟩ = some ⟨some (ι true),
        { v₂ with cmp := cmpStep false b c }, S₂⟩ := by
      tm_step true only [cmpFrag, cmpBody, h1, h2]
        [hra₂, hra₁, hrb₂, hda₂, hda₁, hdb₂, hcmp₂, hcmp₁, hc]
    have hinv : CmpInv x y [] ys xr yr (cmpStep false b c) S₀ { v₂ with cmp := cmpStep false b c } S₂ :=
      ⟨rfl, (hA₁.transport hda₂ hra₂ (hf₂ x hxy)).transport rfl rfl rfl,
        hB₂.transport rfl rfl rfl,
        fun k hkx hky => ((hf₂ k hky).trans (hf₁ k hkx)).trans (hF k hkx hky)⟩
    obtain ⟨n, hn, v', S', hr, hc', hx', hy', hf'⟩ := ih _ _ hinv
    refine ⟨n + 1, ?_, v', S', runsTo_succ hstep hr, ?_, hx', hy', hf'⟩
    · simp only [List.length_cons, List.length_nil] at hn ⊢; omega
    · rw [hc', cmpBits]
  | case4 a xs b ys c ih =>
    intro v S ⟨hc, hA, hB, hF⟩
    obtain ⟨v₁, S₁, h1, hra₁, hda₁, -, -, hrb₁, hdb₁, hcmp₁, -, hA₁, hf₁⟩ := hA.read
    obtain ⟨v₂, S₂, h2, hrb₂, hdb₂, -, -, hra₂, hda₂, hcmp₂, -, hB₂, hf₂⟩ :=
      (hB.transport hdb₁ hrb₁ (hf₁ y hyx)).read
    have hstep : TM2.step M ⟨some (ι true), v, S⟩ = some ⟨some (ι true),
        { v₂ with cmp := cmpStep a b c }, S₂⟩ := by
      tm_step true only [cmpFrag, cmpBody, h1, h2]
        [hra₂, hra₁, hrb₂, hda₂, hda₁, hdb₂, hcmp₂, hcmp₁, hc]
    have hinv : CmpInv x y xs ys xr yr (cmpStep a b c) S₀ { v₂ with cmp := cmpStep a b c } S₂ :=
      ⟨rfl, (hA₁.transport hda₂ hra₂ (hf₂ x hxy)).transport rfl rfl rfl,
        hB₂.transport rfl rfl rfl,
        fun k hkx hky => ((hf₂ k hky).trans (hf₁ k hkx)).trans (hF k hkx hky)⟩
    obtain ⟨n, hn, v', S', hr, hc', hx', hy', hf'⟩ := ih _ _ hinv
    refine ⟨n + 1, ?_, v', S', runsTo_succ hstep hr, ?_, hx', hy', hf'⟩
    · simp only [List.length_cons] at hn ⊢; omega
    · rw [hc', cmpBits]

/-- The comparator: consumes the top numbers of `x`, `y`; sets `cmp` to their
comparison; other stacks untouched. -/
theorem cmpFrag_runs {x y : K} (hxy : x ≠ y) (xs ys : List Bool) (xr yr : List Γ')
    (v : St) (S : Stacks) (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ys ++ .comma :: yr) :
    (cmpFrag x y).Runs v S (fun v' S' =>
        v'.cmp = compare (toNat xs) (toNat ys) ∧ S' x = xr ∧ S' y = yr ∧
        ∀ k, k ≠ x → k ≠ y → S' k = S k)
      (max xs.length ys.length + 2) := by
  constructor
  intro Λ M ι e hI
  have hstep : TM2.step M ⟨some (ι false), v, S⟩ = some
      ⟨some (ι true), { v with cmp := .eq, ra := none, rb := none, da := false, db := false }, S⟩ := by
    tm_step false [cmpFrag]
  obtain ⟨n, hn, v', S', hr, hc', hx', hy', hf'⟩ :=
    cmpFrag_loop hxy hI (xr := xr) (yr := yr) (S₀ := S) xs ys .eq
      { v with cmp := .eq, ra := none, rb := none, da := false, db := false } S
      ⟨rfl, Or.inl ⟨rfl, hSx⟩, Or.inl ⟨rfl, hSy⟩, fun _ _ _ => rfl⟩
  refine ⟨n + 1, by omega, v', S', runsTo_succ hstep hr, ?_, hx', hy', hf'⟩
  rw [hc', cmpBits_eq_compare]

/-- Comparison, stated on naturals: `cmp` becomes `compare a b` within
`4 * (log₂ a + log₂ b + 1)` steps. -/
theorem cmp_correct {x y : K} (hxy : x ≠ y) (a b : ℕ) (xr yr : List Γ')
    (v : St) (S : Stacks) (hSx : S x = encodeNatΓ' a ++ .comma :: xr)
    (hSy : S y = encodeNatΓ' b ++ .comma :: yr) :
    (cmpFrag x y).Runs v S (fun v' S' =>
        v'.cmp = compare a b ∧ S' x = xr ∧ S' y = yr ∧ ∀ k, k ≠ x → k ≠ y → S' k = S k)
      (4 * (Nat.log 2 a + Nat.log 2 b + 1)) := by
  have h := cmpFrag_runs hxy (Computability.encodeNat a) (Computability.encodeNat b) xr yr v S hSx hSy
  refine Frag.runs_mono h (fun v' S' ⟨hc, hx, hy, hf⟩ =>
    ⟨by rw [hc, toNat_encodeNat, toNat_encodeNat], hx, hy, hf⟩) ?_
  have ha := encodeNat_length_le a
  have hb := encodeNat_length_le b
  omega

/-! ### Smoke test: a fragment closed off into a `FinTM2` -/

/-- `moveNum 0 1` as a bundled machine: input `bits l ++ [comma]` on stack `0`,
output `(bits l).reverse` on stack `1`, within `l.length + 2` steps. -/
noncomputable def moveNum_outputs (l : List Bool) :
    TM2OutputsInTime ((moveNum 0 1).toFinTM2 0 1 default) (bits l ++ [.comma])
      (some (bits l).reverse) (l.length + 2) :=
  Frag.toFinTM2_outputs _ _ _ _ _ _ _ (by
    refine Frag.runs_mono (moveNum_runs (by decide) l [] default _
      rfl) ?_ le_rfl
    rintro _ S' ⟨h0, h1, hf⟩
    funext k
    by_cases hk0 : k = 0
    · subst hk0; simp [Frag.initStacks, h0]
    by_cases hk1 : k = 1
    · subst hk1; simp [Frag.initStacks, h1]
    · rw [hf k hk0 hk1]; simp [Frag.initStacks, hk0, hk1])

end Carmichael.TM
