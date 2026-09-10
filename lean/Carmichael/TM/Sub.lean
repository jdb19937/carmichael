import Carmichael.TM.Arith

/-!
# Route T arithmetic fragments: truncated subtraction and decrement

Same data convention as `Carmichael.TM.Arith`: a number is a bit list, LSB
on top, terminated by `Γ'.comma`; fragments consume the top numbers of their
operand stacks.

* `subBits xs ys c` / `subBorrow xs ys c`: the schoolbook subtractor on bit
  lists with borrow-in `c`: the difference bits and the borrow-out.  The
  identity `toNat (subBits xs ys c) + toNat ys + c = toNat xs + 2^n · borrow`
  (`n = max |xs| |ys|`) determines both.
* `subTrunc xs ys c`: the truncated difference — `subBits` when no borrow
  runs off the end, `[]` (zero) otherwise; `toNat = toNat xs - (toNat ys + c)`
  in ℕ's truncated subtraction, with no side condition.
* `subLoop x y z c₀ db₀`: the subtractor loop, an `addLoop` clone
  (`borrow` for `maj`, no carry flush); the final borrow is left in
  `St.carry`.  `db₀ = true` pre-exhausts operand `b`, which turns the same
  loop into a one-operand borrow chain (used by `dec`).
* `zeroIfBorrow z`: if `carry` is set, pop the just-written bits of `z` back
  to the terminator (the number becomes `0`); otherwise a no-op.
* `sub x y z w = subLoop x y z ; zeroIfBorrow z ; push comma on w ; moveNum z w`:
  `w := x - y` (truncated), `z` scratch restored — the calling convention of
  `add x y z w`.
* `dec x z w`: `w := x - 1` (truncated), `z` scratch restored.

Every fragment has a bit-list `Runs` triple and a `Nat.log 2` corollary.
-/

namespace Carmichael.TM

open Turing Turing.TM2 Turing.TM2.Stmt Computability

/-! ### Subtractor on bit lists -/

/-- Borrow-out of a full subtractor computing `a - b - c`. -/
def borrow (a b c : Bool) : Bool := (!a && (b || c)) || (b && c)

/-- Difference bits of `xs - ys - c`, LSB first; length `max |xs| |ys|`
(the final borrow is NOT recorded here, see `subBorrow`).  The difference bit
is `sumBit` (a three-way xor). -/
def subBits : List Bool → List Bool → Bool → List Bool
  | [], [], _ => []
  | a :: xs, [], c => sumBit a false c :: subBits xs [] (borrow a false c)
  | [], b :: ys, c => sumBit false b c :: subBits [] ys (borrow false b c)
  | a :: xs, b :: ys, c => sumBit a b c :: subBits xs ys (borrow a b c)

/-- Borrow-out of `xs - ys - c`. -/
def subBorrow : List Bool → List Bool → Bool → Bool
  | [], [], c => c
  | a :: xs, [], c => subBorrow xs [] (borrow a false c)
  | [], b :: ys, c => subBorrow [] ys (borrow false b c)
  | a :: xs, b :: ys, c => subBorrow xs ys (borrow a b c)

theorem subBits_length (xs ys : List Bool) (c : Bool) :
    (subBits xs ys c).length = max xs.length ys.length := by
  induction xs, ys, c using subBits.induct with
  | case1 c => simp [subBits]
  | case2 a xs c ih => simp only [subBits, List.length_cons, List.length_nil] at ih ⊢; omega
  | case3 b ys c ih => simp only [subBits, List.length_cons, List.length_nil] at ih ⊢; omega
  | case4 a xs b ys c ih => simp only [subBits, List.length_cons] at ih ⊢; omega

/-- Value of a bit list is below `2 ^ length`. -/
theorem toNat_lt_two_pow (l : List Bool) : toNat l < 2 ^ l.length := by
  induction l with
  | nil => simp [toNat]
  | cons b l ih => cases b <;> simp [toNat, pow_succ] <;> omega

/-- The subtractor identity. -/
theorem toNat_subBits (xs ys : List Bool) (c : Bool) :
    toNat (subBits xs ys c) + toNat ys + c.toNat =
      toNat xs + 2 ^ max xs.length ys.length * (subBorrow xs ys c).toNat := by
  induction xs, ys, c using subBits.induct with
  | case1 c => cases c <;> simp [subBits, subBorrow, toNat]
  | case2 a xs c ih =>
    simp only [subBits, subBorrow, List.length_cons, List.length_nil] at ih ⊢
    rw [show max (xs.length + 1) 0 = max xs.length 0 + 1 by omega, pow_succ]
    generalize subBorrow xs [] (borrow a false c) = B at ih ⊢
    cases B <;> cases a <;> cases c <;> simp [toNat, sumBit, borrow] at ih ⊢ <;> omega
  | case3 b ys c ih =>
    simp only [subBits, subBorrow, List.length_cons, List.length_nil] at ih ⊢
    rw [show max 0 (ys.length + 1) = max 0 ys.length + 1 by omega, pow_succ]
    generalize subBorrow [] ys (borrow false b c) = B at ih ⊢
    cases B <;> cases b <;> cases c <;> simp [toNat, sumBit, borrow] at ih ⊢ <;> omega
  | case4 a xs b ys c ih =>
    simp only [subBits, subBorrow, List.length_cons] at ih ⊢
    rw [show max (xs.length + 1) (ys.length + 1) = max xs.length ys.length + 1 by omega, pow_succ]
    generalize subBorrow xs ys (borrow a b c) = B at ih ⊢
    cases B <;> cases a <;> cases b <;> cases c <;> simp [toNat, sumBit, borrow] at ih ⊢ <;> omega

/-- No borrow runs off the end iff the subtraction is exact in ℕ. -/
theorem subBorrow_eq_false_iff (xs ys : List Bool) (c : Bool) :
    subBorrow xs ys c = false ↔ toNat ys + c.toNat ≤ toNat xs := by
  have h := toNat_subBits xs ys c
  have hlt := toNat_lt_two_pow (subBits xs ys c)
  rw [subBits_length] at hlt
  generalize subBorrow xs ys c = B at h ⊢
  cases B <;> cases c <;> simp at h ⊢ <;> omega

/-- The truncated difference: `subBits` if no borrow runs off the end, else `0`. -/
def subTrunc (xs ys : List Bool) (c : Bool) : List Bool :=
  if subBorrow xs ys c then [] else subBits xs ys c

theorem toNat_subTrunc (xs ys : List Bool) (c : Bool) :
    toNat (subTrunc xs ys c) = toNat xs - (toNat ys + c.toNat) := by
  unfold subTrunc
  have h := toNat_subBits xs ys c
  have hiff := subBorrow_eq_false_iff xs ys c
  generalize subBorrow xs ys c = B at h hiff ⊢
  cases B <;> cases c <;> simp [toNat] at h hiff ⊢ <;> omega

theorem subTrunc_length (xs ys : List Bool) (c : Bool) :
    (subTrunc xs ys c).length ≤ max xs.length ys.length := by
  unfold subTrunc
  split_ifs
  · simp
  · rw [subBits_length]

/-- The reversal bookkeeping for the assembled fragments. -/
theorem bits_ite_reverse (B : Bool) (l : List Bool) :
    (bits (if B then [] else l.reverse)).reverse = bits (if B then [] else l) := by
  cases B <;> simp

/-! ### The subtractor loop -/

/-- One iteration of the subtractor: read a bit from each unexhausted
operand; both exhausted exits (the borrow stays in `carry`), otherwise emit
the difference bit, update the borrow and loop. -/
def subBody {Λ : Type} (x y z : K) (self e : Λ) : Stmt' Λ :=
  let rest : Stmt' Λ :=
    branch (fun v => v.da && v.db)
      (goto fun _ => e)
      (push z (fun v => .bit (sumBit (bitOf v.ra) (bitOf v.rb) v.carry))
        (load (fun v => { v with carry := borrow (bitOf v.ra) (bitOf v.rb) v.carry })
          (goto fun _ => self)))
  let readY : Stmt' Λ := branch (fun v => v.db) rest (pop y readB rest)
  branch (fun v => v.da) readY (pop x readA readY)

/-- The subtractor loop: label `false` sets `carry := c₀`, `db := db₀`
(`db₀ = true` pre-exhausts operand `b`: stack `y` is never touched), clears
the other registers and pushes a `comma` on `z`; label `true` is `subBody`.
Leaves the difference on `z` MSB on top and the final borrow in `carry`. -/
def subLoop (x y z : K) (c₀ db₀ : Bool) : Frag where
  Λf := Bool
  entry := false
  code ι e
    | false =>
      load (fun v => { v with carry := c₀, ra := none, rb := none, da := false, db := db₀ })
        (push z (fun _ => .comma) (goto fun _ => ι true))
    | true => subBody x y z (ι true) e

theorem subLoop_loop {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) {c₀ db₀ : Bool}
    {Λ : Type} {M : Λ → Stmt' Λ} {ι : Bool → Λ} {e : Λ}
    (hI : (subLoop x y z c₀ db₀).Installed M ι e)
    {xr yr : List Γ'} {S₀ : Stacks} (xs ys : List Bool) (c : Bool) :
    ∀ (v : St) (S : Stacks) (zr : List Γ'), AddInv x y z xs ys xr yr zr c S₀ v S →
    ∃ n, n ≤ max xs.length ys.length + 1 ∧ ∃ v' S',
      RunsTo M n ⟨some (ι true), v, S⟩ ⟨some e, v', S'⟩ ∧
      v'.carry = subBorrow xs ys c ∧
      S' x = xr ∧ S' y = yr ∧ S' z = (bits (subBits xs ys c)).reverse ++ zr ∧
      ∀ k, k ≠ x → k ≠ y → k ≠ z → S' k = S₀ k := by
  have hyx := hxy.symm
  have hzx := hxz.symm
  have hzy := hyz.symm
  induction xs, ys, c using subBits.induct with
  | case1 c =>
    intro v S zr ⟨hc, hA, hB, hZ, hF⟩
    obtain ⟨v₁, S₁, h1, hra₁, hda₁, hx₁, hc₁, hrb₁, hdb₁, -, -, -, hf₁⟩ := hA.read
    obtain ⟨v₂, S₂, h2, hrb₂, hdb₂, hy₂, hc₂, hra₂, hda₂, -, -, -, hf₂⟩ :=
      (hB.transport hdb₁ hrb₁ (hf₁ y hyx)).read
    refine ⟨1, by simp, v₂, S₂, runsTo_succ ?_ (runsTo_zero M _),
      by simp [subBorrow, hc₂, hc₁, hc], (hf₂ x hxy).trans (hx₁ rfl), hy₂ rfl,
      by simp [subBits, (hf₂ z hzy).trans ((hf₁ z hzx).trans hZ)],
      fun k hkx hky hkz => ((hf₂ k hky).trans (hf₁ k hkx)).trans (hF k hkx hky hkz)⟩
    tm_step true only [subLoop, subBody, h1, h2] [hda₂, hda₁, hdb₂]
  | case2 a xs c ih =>
    intro v S zr ⟨hc, hA, hB, hZ, hF⟩
    obtain ⟨v₁, S₁, h1, hra₁, hda₁, -, hc₁, hrb₁, hdb₁, -, -, hA₁, hf₁⟩ := hA.read
    obtain ⟨v₂, S₂, h2, hrb₂, hdb₂, -, hc₂, hra₂, hda₂, -, -, hB₂, hf₂⟩ :=
      (hB.transport hdb₁ hrb₁ (hf₁ y hyx)).read
    have hz₂ : S₂ z = zr := (hf₂ z hzy).trans ((hf₁ z hzx).trans hZ)
    have hstep : TM2.step M ⟨some (ι true), v, S⟩ = some ⟨some (ι true),
        { v₂ with carry := borrow a false c },
        Function.update S₂ z (.bit (sumBit a false c) :: zr)⟩ := by
      tm_step true only [subLoop, subBody, h1, h2]
        [hra₂, hra₁, hrb₂, hda₂, hda₁, hdb₂, hc₂, hc₁, hc, hz₂]
    have hinv : AddInv x y z xs [] xr yr (.bit (sumBit a false c) :: zr) (borrow a false c) S₀
        { v₂ with carry := borrow a false c }
        (Function.update S₂ z (.bit (sumBit a false c) :: zr)) :=
      ⟨rfl, (hA₁.transport hda₂ hra₂ (hf₂ x hxy)).transport rfl rfl
          (by simp [Function.update_of_ne hxz]),
        hB₂.transport rfl rfl (by simp [Function.update_of_ne hyz]), by simp,
        fun k hkx hky hkz => by
          simp [Function.update_of_ne hkz, hf₂ k hky, hf₁ k hkx, hF k hkx hky hkz]⟩
    obtain ⟨n, hn, v', S', hr, hc', hx', hy', hz', hf'⟩ := ih _ _ _ hinv
    refine ⟨n + 1, ?_, v', S', runsTo_succ hstep hr, ?_, hx', hy', ?_, hf'⟩
    · simp only [List.length_cons, List.length_nil] at hn ⊢; omega
    · rw [hc', subBorrow]
    · rw [hz']; simp [subBits]
  | case3 b ys c ih =>
    intro v S zr ⟨hc, hA, hB, hZ, hF⟩
    obtain ⟨v₁, S₁, h1, hra₁, hda₁, -, hc₁, hrb₁, hdb₁, -, -, hA₁, hf₁⟩ := hA.read
    obtain ⟨v₂, S₂, h2, hrb₂, hdb₂, -, hc₂, hra₂, hda₂, -, -, hB₂, hf₂⟩ :=
      (hB.transport hdb₁ hrb₁ (hf₁ y hyx)).read
    have hz₂ : S₂ z = zr := (hf₂ z hzy).trans ((hf₁ z hzx).trans hZ)
    have hstep : TM2.step M ⟨some (ι true), v, S⟩ = some ⟨some (ι true),
        { v₂ with carry := borrow false b c },
        Function.update S₂ z (.bit (sumBit false b c) :: zr)⟩ := by
      tm_step true only [subLoop, subBody, h1, h2]
        [hra₂, hra₁, hrb₂, hda₂, hda₁, hdb₂, hc₂, hc₁, hc, hz₂]
    have hinv : AddInv x y z [] ys xr yr (.bit (sumBit false b c) :: zr) (borrow false b c) S₀
        { v₂ with carry := borrow false b c }
        (Function.update S₂ z (.bit (sumBit false b c) :: zr)) :=
      ⟨rfl, (hA₁.transport hda₂ hra₂ (hf₂ x hxy)).transport rfl rfl
          (by simp [Function.update_of_ne hxz]),
        hB₂.transport rfl rfl (by simp [Function.update_of_ne hyz]), by simp,
        fun k hkx hky hkz => by
          simp [Function.update_of_ne hkz, hf₂ k hky, hf₁ k hkx, hF k hkx hky hkz]⟩
    obtain ⟨n, hn, v', S', hr, hc', hx', hy', hz', hf'⟩ := ih _ _ _ hinv
    refine ⟨n + 1, ?_, v', S', runsTo_succ hstep hr, ?_, hx', hy', ?_, hf'⟩
    · simp only [List.length_cons, List.length_nil] at hn ⊢; omega
    · rw [hc', subBorrow]
    · rw [hz']; simp [subBits]
  | case4 a xs b ys c ih =>
    intro v S zr ⟨hc, hA, hB, hZ, hF⟩
    obtain ⟨v₁, S₁, h1, hra₁, hda₁, -, hc₁, hrb₁, hdb₁, -, -, hA₁, hf₁⟩ := hA.read
    obtain ⟨v₂, S₂, h2, hrb₂, hdb₂, -, hc₂, hra₂, hda₂, -, -, hB₂, hf₂⟩ :=
      (hB.transport hdb₁ hrb₁ (hf₁ y hyx)).read
    have hz₂ : S₂ z = zr := (hf₂ z hzy).trans ((hf₁ z hzx).trans hZ)
    have hstep : TM2.step M ⟨some (ι true), v, S⟩ = some ⟨some (ι true),
        { v₂ with carry := borrow a b c },
        Function.update S₂ z (.bit (sumBit a b c) :: zr)⟩ := by
      tm_step true only [subLoop, subBody, h1, h2]
        [hra₂, hra₁, hrb₂, hda₂, hda₁, hdb₂, hc₂, hc₁, hc, hz₂]
    have hinv : AddInv x y z xs ys xr yr (.bit (sumBit a b c) :: zr) (borrow a b c) S₀
        { v₂ with carry := borrow a b c }
        (Function.update S₂ z (.bit (sumBit a b c) :: zr)) :=
      ⟨rfl, (hA₁.transport hda₂ hra₂ (hf₂ x hxy)).transport rfl rfl
          (by simp [Function.update_of_ne hxz]),
        hB₂.transport rfl rfl (by simp [Function.update_of_ne hyz]), by simp,
        fun k hkx hky hkz => by
          simp [Function.update_of_ne hkz, hf₂ k hky, hf₁ k hkx, hF k hkx hky hkz]⟩
    obtain ⟨n, hn, v', S', hr, hc', hx', hy', hz', hf'⟩ := ih _ _ _ hinv
    refine ⟨n + 1, ?_, v', S', runsTo_succ hstep hr, ?_, hx', hy', ?_, hf'⟩
    · simp only [List.length_cons] at hn ⊢; omega
    · rw [hc', subBorrow]
    · rw [hz']; simp [subBits]

/-- The two-operand subtractor loop: consumes the top numbers of `x`, `y`;
leaves `comma` then `xs - ys - c₀` (MSB on top) on `z` and the final borrow
in `carry`; other stacks untouched. -/
theorem subLoop_runs {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (c₀ : Bool)
    (xs ys : List Bool) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ys ++ .comma :: yr) :
    (subLoop x y z c₀ false).Runs v S (fun v' S' =>
        v'.carry = subBorrow xs ys c₀ ∧
        S' x = xr ∧ S' y = yr ∧ S' z = (bits (subBits xs ys c₀)).reverse ++ .comma :: S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → S' k = S k)
      (max xs.length ys.length + 2) := by
  constructor
  intro Λ M ι e hI
  have hstep : TM2.step M ⟨some (ι false), v, S⟩ = some
      ⟨some (ι true), { v with carry := c₀, ra := none, rb := none, da := false, db := false },
        Function.update S z (.comma :: S z)⟩ := by
    tm_step false [subLoop]
  obtain ⟨n, hn, v', S', hr, hc', hx', hy', hz', hf'⟩ :=
    subLoop_loop hxy hxz hyz hI (xr := xr) (yr := yr) (S₀ := S) xs ys c₀
      { v with carry := c₀, ra := none, rb := none, da := false, db := false }
      (Function.update S z (.comma :: S z)) (.comma :: S z)
      ⟨rfl, Or.inl ⟨rfl, by simp [Function.update_of_ne hxz, hSx]⟩,
        Or.inl ⟨rfl, by simp [Function.update_of_ne hyz, hSy]⟩, by simp,
        fun k hkx hky hkz => by simp [Function.update_of_ne hkz]⟩
  exact ⟨n + 1, by omega, v', S', runsTo_succ hstep hr, hc', hx', hy', hz', hf'⟩

/-- The one-operand borrow chain (`db₀ = true`, `c₀ = true`): consumes the
top number of `x`; stack `y` is a phantom operand, never read; leaves
`comma` then `xs - 1` (MSB on top) on `z` and the final borrow in `carry`. -/
theorem decLoop_runs {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (xs : List Bool) (xr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) :
    (subLoop x y z true true).Runs v S (fun v' S' =>
        v'.carry = subBorrow xs [] true ∧
        S' x = xr ∧ S' y = S y ∧ S' z = (bits (subBits xs [] true)).reverse ++ .comma :: S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → S' k = S k)
      (xs.length + 2) := by
  constructor
  intro Λ M ι e hI
  have hstep : TM2.step M ⟨some (ι false), v, S⟩ = some
      ⟨some (ι true), { v with carry := true, ra := none, rb := none, da := false, db := true },
        Function.update S z (.comma :: S z)⟩ := by
    tm_step false [subLoop]
  obtain ⟨n, hn, v', S', hr, hc', hx', hy', hz', hf'⟩ :=
    subLoop_loop hxy hxz hyz hI (xr := xr) (yr := S y) (S₀ := S) xs [] true
      { v with carry := true, ra := none, rb := none, da := false, db := true }
      (Function.update S z (.comma :: S z)) (.comma :: S z)
      ⟨rfl, Or.inl ⟨rfl, by simp [Function.update_of_ne hxz, hSx]⟩,
        Or.inr ⟨rfl, rfl, rfl, by simp [Function.update_of_ne hyz]⟩, by simp,
        fun k hkx hky hkz => by simp [Function.update_of_ne hkz]⟩
  refine ⟨n + 1, ?_, v', S', runsTo_succ hstep hr, hc', hx', hy', hz', hf'⟩
  simp only [List.length_nil, Nat.max_zero] at hn; omega

/-! ### Zeroing on borrow -/

/-- If `carry` is set: pop `z`; a bit loops, the terminator is pushed back,
`carry` is cleared and we exit.  If `carry` is clear: exit at once. -/
def zeroBody {Λ : Type} (z : K) (self e : Λ) : Stmt' Λ :=
  branch (fun v => v.carry)
    (pop z readA
      (branch (fun v => v.ra.isSome)
        (goto fun _ => self)
        (push z (fun _ => .comma)
          (load (fun v => { v with carry := false }) (goto fun _ => e)))))
    (goto fun _ => e)

/-- Replace the top number of `z` by `0` if `carry` is set; no-op otherwise. -/
def zeroIfBorrow (z : K) : Frag where
  Λf := Unit
  entry := ()
  code ι e _ := zeroBody z (ι ()) e

theorem zeroIfBorrow_loop {z : K} {Λ : Type} {M : Λ → Stmt' Λ} {ι : Unit → Λ} {e : Λ}
    (hI : (zeroIfBorrow z).Installed M ι e) {zr : List Γ'} {S₀ : Stacks} (l : List Bool) :
    ∀ (v : St) (S : Stacks), v.carry = true → S z = bits l ++ .comma :: zr →
      (∀ k, k ≠ z → S k = S₀ k) →
    ∃ n, n ≤ l.length + 1 ∧ ∃ v' S',
      RunsTo M n ⟨some (ι ()), v, S⟩ ⟨some e, v', S'⟩ ∧
      v'.carry = false ∧ S' z = .comma :: zr ∧ ∀ k, k ≠ z → S' k = S₀ k := by
  induction l with
  | nil =>
    intro v S hv hS hF
    refine ⟨1, by simp, { v with ra := none, da := true, carry := false },
      Function.update S z (.comma :: zr), runsTo_succ ?_ (runsTo_zero M _), rfl, by simp,
      fun k hk => by simp [Function.update_of_ne hk, hF k hk]⟩
    tm_step () [zeroIfBorrow, zeroBody, hv, hS]
  | cons b l ih =>
    intro v S hv hS hF
    obtain ⟨n, hn, v', S', hr, hc', hz', hf'⟩ :=
      ih { v with ra := some b } (Function.update S z (bits l ++ .comma :: zr)) (by simp [hv])
        (by simp) (fun k hk => by simp [Function.update_of_ne hk, hF k hk])
    refine ⟨n + 1, ?_, v', S', runsTo_succ ?_ hr, hc', hz', hf'⟩
    · simp only [List.length_cons] at hn ⊢; omega
    · tm_step () [zeroIfBorrow, zeroBody, hv, hS]

/-- `zeroIfBorrow`: with `bits l ++ comma :: zr` on `z`, the number becomes
`0` if `carry` was set and is unchanged otherwise; other stacks untouched. -/
theorem zeroIfBorrow_runs {z : K} (l : List Bool) (zr : List Γ') (v : St) (S : Stacks)
    (hS : S z = bits l ++ .comma :: zr) :
    (zeroIfBorrow z).Runs v S (fun _ S' =>
        S' z = bits (if v.carry then [] else l) ++ .comma :: zr ∧ ∀ k, k ≠ z → S' k = S k)
      (l.length + 1) := by
  constructor
  intro Λ M ι e hI
  cases hv : v.carry
  · refine ⟨1, by omega, v, S, runsTo_succ ?_ (runsTo_zero M _), by simp [hS],
      fun _ _ => rfl⟩
    tm_step () [zeroIfBorrow, zeroBody, hv]
  · obtain ⟨n, hn, v', S', hr, -, hz', hf'⟩ :=
      zeroIfBorrow_loop hI (zr := zr) (S₀ := S) l v S hv hS (fun _ _ => rfl)
    exact ⟨n, hn, v', S', hr, by simp [hz'], hf'⟩

/-! ### Subtraction, assembled -/

/-- `w := x - y` (truncated) using scratch stack `z`: the difference is left
on `w` in standard orientation with its terminator; `x`, `y` lose their top
numbers; `z` is restored.  Same calling convention as `add x y z w`. -/
def sub (x y z w : K) : Frag :=
  (subLoop x y z false false).seq
    ((zeroIfBorrow z).seq ((Frag.pushSym w .comma).seq (moveNum z w)))

/-- The tail `zeroIfBorrow z ; push comma on w ; moveNum z w` shared by
`sub` and `dec`: from the loop's output (borrow in `carry`, reversed
difference on `z` above `zr`) to the truncated difference on `w`. -/
theorem subTail_runs {z w : K} (hzw : z ≠ w) (xs ys : List Bool) (c₀ : Bool) (zr : List Γ')
    (v₁ : St) (S₁ : Stacks) (hc₁ : v₁.carry = subBorrow xs ys c₀)
    (hz₁ : S₁ z = (bits (subBits xs ys c₀)).reverse ++ .comma :: zr) :
    ((zeroIfBorrow z).seq ((Frag.pushSym w .comma).seq (moveNum z w))).Runs v₁ S₁ (fun _ S' =>
        S' z = zr ∧ S' w = bits (subTrunc xs ys c₀) ++ .comma :: S₁ w ∧
        ∀ k, k ≠ z → k ≠ w → S' k = S₁ k)
      (2 * max xs.length ys.length + 3) := by
  have hwz := hzw.symm
  have h2a := zeroIfBorrow_runs (subBits xs ys c₀).reverse zr v₁ S₁ (by rw [bits_reverse]; exact hz₁)
  have h2b : ∀ v₂ S₂,
      (S₂ z = bits (if v₁.carry then [] else (subBits xs ys c₀).reverse) ++ .comma :: zr ∧
        ∀ k, k ≠ z → S₂ k = S₁ k) →
      ((Frag.pushSym w .comma).seq (moveNum z w)).Runs v₂ S₂ (fun _ S' =>
        S' z = zr ∧ S' w = bits (subTrunc xs ys c₀) ++ .comma :: S₁ w ∧
        ∀ k, k ≠ z → k ≠ w → S' k = S₁ k)
      (1 + (max xs.length ys.length + 1)) := by
    intro v₂ S₂ ⟨hz₂, hf₂⟩
    refine Frag.seq_runs (Frag.pushSym_runs w .comma v₂ S₂) fun v₃ S₃ ⟨hv₃, hS₃⟩ => ?_
    subst hS₃
    have h3 := moveNum_runs hzw (if v₁.carry then [] else (subBits xs ys c₀).reverse) zr v₃
      (Function.update S₂ w (.comma :: S₂ w)) (by simp [Function.update_of_ne hzw, hz₂])
    refine Frag.runs_mono h3 (fun v₄ S₄ ⟨hz₄, hw₄, hf₄⟩ => ?_) ?_
    · refine ⟨hz₄, ?_, ?_⟩
      · rw [hw₄, hc₁, bits_ite_reverse]; simp [hf₂ w hwz, subTrunc]
      · intro k hkz hkw
        rw [hf₄ k hkz hkw]; simp [Function.update_of_ne hkw, hf₂ k hkz]
    · have := subBits_length xs ys c₀
      split_ifs <;> simp only [List.length_reverse, List.length_nil] <;> omega
  refine Frag.runs_mono (Frag.seq_runs h2a h2b) (fun _ _ h => h) ?_
  simp only [List.length_reverse, subBits_length]; omega

theorem sub_runs {x y z w : K} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) (xs ys : List Bool) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ys ++ .comma :: yr) :
    (sub x y z w).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ S' z = S z ∧ S' w = bits (subTrunc xs ys false) ++ .comma :: S w ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → k ≠ w → S' k = S k)
      (3 * max xs.length ys.length + 5) := by
  have h1 := subLoop_runs hxy hxz hyz false xs ys xr yr v S hSx hSy
  have h2 : ∀ v₁ S₁, (v₁.carry = subBorrow xs ys false ∧ S₁ x = xr ∧ S₁ y = yr ∧
      S₁ z = (bits (subBits xs ys false)).reverse ++ .comma :: S z ∧
      ∀ k, k ≠ x → k ≠ y → k ≠ z → S₁ k = S k) →
      ((zeroIfBorrow z).seq ((Frag.pushSym w .comma).seq (moveNum z w))).Runs v₁ S₁ (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ S' z = S z ∧ S' w = bits (subTrunc xs ys false) ++ .comma :: S w ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → k ≠ w → S' k = S k)
      (2 * max xs.length ys.length + 3) :=
    fun v₁ S₁ ⟨hc₁, hx₁, hy₁, hz₁, hf₁⟩ =>
      Frag.runs_mono (subTail_runs hzw xs ys false (S z) v₁ S₁ hc₁ hz₁)
        (fun _ S' ⟨hz, hw, hf⟩ =>
          ⟨by rw [hf x hxz hxw]; exact hx₁, by rw [hf y hyz hyw]; exact hy₁, hz,
            by rw [hw, hf₁ w hxw.symm hyw.symm hzw.symm],
            fun k hkx hky hkz hkw => by rw [hf k hkz hkw, hf₁ k hkx hky hkz]⟩) le_rfl
  exact Frag.runs_mono (Frag.seq_runs h1 h2) (fun _ _ h => h) (by omega)

/-- Truncated subtraction, stated on naturals: with `a`, `b` encoded on `x`,
`y`, the machine leaves a bit list of value `a - b` on `w`, within
`9 * (log₂ a + log₂ b + 1)` steps. -/
theorem sub_correct {x y z w : K} (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z)
    (hyw : y ≠ w) (hzw : z ≠ w) (a b : ℕ) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' b ++ .comma :: yr) :
    (sub x y z w).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ S' z = S z ∧
        (∃ l, toNat l = a - b ∧ S' w = bits l ++ .comma :: S w) ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → k ≠ w → S' k = S k)
      (9 * (Nat.log 2 a + Nat.log 2 b + 1)) := by
  have h := sub_runs hxy hxz hxw hyz hyw hzw (Computability.encodeNat a)
    (Computability.encodeNat b) xr yr v S hSx hSy
  refine Frag.runs_mono h (fun v' S' ⟨hx, hy, hz, hw, hf⟩ =>
    ⟨hx, hy, hz, ⟨_, by rw [toNat_subTrunc, toNat_encodeNat, toNat_encodeNat]; rfl, hw⟩, hf⟩) ?_
  have ha := encodeNat_length_le a
  have hb := encodeNat_length_le b
  omega

/-! ### Decrement -/

/-- `w := x - 1` (truncated: `0 ↦ 0`) using scratch stack `z`: the result is
left on `w` with its terminator; `x` loses its top number; `z` is restored.
The subtractor loop runs with operand `b` pre-exhausted and borrow-in `1`
(stack `w` stands in as the phantom `b` operand and is never read). -/
def dec (x z w : K) : Frag :=
  (subLoop x w z true true).seq
    ((zeroIfBorrow z).seq ((Frag.pushSym w .comma).seq (moveNum z w)))

theorem dec_runs {x z w : K} (hxz : x ≠ z) (hxw : x ≠ w) (hzw : z ≠ w)
    (xs : List Bool) (xr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) :
    (dec x z w).Runs v S (fun _ S' =>
        S' x = xr ∧ S' z = S z ∧ S' w = bits (subTrunc xs [] true) ++ .comma :: S w ∧
        ∀ k, k ≠ x → k ≠ z → k ≠ w → S' k = S k)
      (3 * xs.length + 5) := by
  have hwz := hzw.symm
  have h1 := decLoop_runs hxw hxz hwz xs xr v S hSx
  have h2 : ∀ v₁ S₁, (v₁.carry = subBorrow xs [] true ∧ S₁ x = xr ∧ S₁ w = S w ∧
      S₁ z = (bits (subBits xs [] true)).reverse ++ .comma :: S z ∧
      ∀ k, k ≠ x → k ≠ w → k ≠ z → S₁ k = S k) →
      ((zeroIfBorrow z).seq ((Frag.pushSym w .comma).seq (moveNum z w))).Runs v₁ S₁ (fun _ S' =>
        S' x = xr ∧ S' z = S z ∧ S' w = bits (subTrunc xs [] true) ++ .comma :: S w ∧
        ∀ k, k ≠ x → k ≠ z → k ≠ w → S' k = S k)
      (2 * max xs.length [].length + 3) :=
    fun v₁ S₁ ⟨hc₁, hx₁, hw₁, hz₁, hf₁⟩ =>
      Frag.runs_mono (subTail_runs hzw xs [] true (S z) v₁ S₁ hc₁ hz₁)
        (fun _ S' ⟨hz, hw, hf⟩ =>
          ⟨by rw [hf x hxz hxw]; exact hx₁, hz, by rw [hw, hw₁],
            fun k hkx hkz hkw => by rw [hf k hkz hkw, hf₁ k hkx hkw hkz]⟩) le_rfl
  refine Frag.runs_mono (Frag.seq_runs h1 h2) (fun _ _ h => h) ?_
  simp only [List.length_nil]; omega

/-- Decrement, stated on naturals: with `a` encoded on `x`, the machine leaves
a bit list of value `a - 1` on `w`, within `9 * (log₂ a + 1)` steps. -/
theorem dec_correct {x z w : K} (hxz : x ≠ z) (hxw : x ≠ w) (hzw : z ≠ w)
    (a : ℕ) (xr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) :
    (dec x z w).Runs v S (fun _ S' =>
        S' x = xr ∧ S' z = S z ∧
        (∃ l, toNat l = a - 1 ∧ S' w = bits l ++ .comma :: S w) ∧
        ∀ k, k ≠ x → k ≠ z → k ≠ w → S' k = S k)
      (9 * (Nat.log 2 a + 1)) := by
  have h := dec_runs hxz hxw hzw (Computability.encodeNat a) xr v S hSx
  refine Frag.runs_mono h (fun v' S' ⟨hx, hz, hw, hf⟩ =>
    ⟨hx, hz, ⟨_, by rw [toNat_subTrunc, toNat_encodeNat]; rfl, hw⟩, hf⟩) ?_
  have ha := encodeNat_length_le a
  omega

end Carmichael.TM
