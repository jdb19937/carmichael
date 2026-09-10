import Carmichael.TM.Prims
import Carmichael.TM.Sub

/-!
# Route T arithmetic fragments: multiplication and division with remainder

Same data convention as `Carmichael.TM.Arith`: a number is a bit list, LSB
on top, terminated by `Γ'.comma`; fragments consume the top numbers of their
operand stacks.  Outputs are bit lists of the right VALUE (`∃ l, toNat l = …`),
not necessarily canonical (`add`/`sub` outputs are not canonical either).

* `popBit y`: pop one symbol of `y` into `ra`/`da` (`readBit`).
* `add x y z x` / `sub x y z x` (in-place on the first operand): the existing
  `add`/`sub` fragments with the result stack equal to operand stack `x`;
  `add_runs_x`, `sub_runs_x` are the corresponding triples (no new machine code).
* `mul x y w s t`: schoolbook multiplication, `w := x * y`; consumes the top
  numbers of `x` and `y`, scratch `s`, `t` restored.  Reference function
  `mulGo` on bit lists.
* `divmod x y q j s t`: binary long division; consumes `a` from `x` and `d`
  from `y` (`1 ≤ d`), pushes `a % d` on `x` and `a / d` on `q`; scratch `j`
  (the shift counter), `s`, `t` restored.  `divmodCore` is the same without
  the final `dropNum y` (leaves `d` on `y`).
* `divFrag`, `modFrag`: `divmod` followed by dropping the unwanted output.

Step bounds are quadratic in the bit lengths; `mul_le_B`, `divmod_le_B`
give the `B`-forms for operands below `2 ^ b`.
-/

namespace Carmichael.TM

open Turing Turing.TM2 Turing.TM2.Stmt Computability

/-! ### Reference function for multiplication -/

/-- Conditionally add `sh` to `acc`. -/
def condAdd (b : Bool) (acc sh : List Bool) : List Bool :=
  if b then addBits acc sh false else acc

/-- Shift-and-add over the multiplier bits `ys` (LSB first): accumulator
`acc`, shifted multiplicand `sh` (doubled by prepending a `0`). -/
def mulGo (acc sh : List Bool) : List Bool → List Bool
  | [] => acc
  | b :: ys => mulGo (condAdd b acc sh) (false :: sh) ys

theorem toNat_condAdd (b : Bool) (acc sh : List Bool) :
    toNat (condAdd b acc sh) = toNat acc + b.toNat * toNat sh := by
  cases b <;> simp [condAdd, toNat_addBits]

theorem condAdd_length (b : Bool) (acc sh : List Bool) :
    (condAdd b acc sh).length ≤ max acc.length sh.length + 1 := by
  cases b
  · simp [condAdd]; omega
  · simpa [condAdd] using addBits_length acc sh false

theorem toNat_mulGo (acc sh ys : List Bool) :
    toNat (mulGo acc sh ys) = toNat acc + toNat sh * toNat ys := by
  induction ys generalizing acc sh with
  | nil => simp [mulGo, toNat]
  | cons b ys ih =>
    rw [mulGo, ih, toNat_condAdd]
    simp only [toNat, Bool.toNat_false]
    ring

theorem mulGo_length (acc sh ys : List Bool) :
    (mulGo acc sh ys).length ≤ max acc.length sh.length + 2 * ys.length := by
  induction ys generalizing acc sh with
  | nil => simp [mulGo]
  | cons b ys ih =>
    rw [mulGo]
    have h1 := ih (condAdd b acc sh) (false :: sh)
    have h2 := condAdd_length b acc sh
    simp only [List.length_cons] at h1 ⊢
    omega

theorem mulGo_append (acc sh p q : List Bool) :
    mulGo acc sh (p ++ q) = mulGo (mulGo acc sh p) (List.replicate p.length false ++ sh) q := by
  induction p generalizing acc sh with
  | nil => simp [mulGo]
  | cons b p ih =>
    simp only [List.cons_append, mulGo, List.length_cons, List.replicate_succ']
    rw [ih, List.append_assoc]; rfl

theorem mulGo_singleton (acc sh : List Bool) (b : Bool) : mulGo acc sh [b] = condAdd b acc sh := rfl

/-! ### Popping one symbol into the registers -/

/-- Pop one symbol of `y`: a bit goes to `ra` (`da := false`), a terminator
or empty stack sets `da := true` (`ra := none`). -/
def popBit (y : K) : Frag := Frag.straight fun q => pop y readBit q

theorem popBit_runs_bit {y : K} (b : Bool) (q : List Bool) (yr : List Γ')
    (v : St) (S : Stacks) (hS : S y = bits (b :: q) ++ .comma :: yr) :
    (popBit y).Runs v S (fun v' S' => v' = { v with ra := some b, da := false } ∧
      S' = Function.update S y (bits q ++ .comma :: yr)) 1 := by
  constructor
  intro Λ M ι e hI
  refine ⟨1, le_rfl, _, _, runsTo_succ ?_ (runsTo_zero M _), rfl, rfl⟩
  tm_step () [popBit, Frag.straight, hS]

theorem popBit_runs_end {y : K} (yr : List Γ') (v : St) (S : Stacks) (hS : S y = .comma :: yr) :
    (popBit y).Runs v S (fun v' S' => v' = { v with ra := none, da := true } ∧
      S' = Function.update S y yr) 1 := by
  constructor
  intro Λ M ι e hI
  refine ⟨1, le_rfl, _, _, runsTo_succ ?_ (runsTo_zero M _), rfl, rfl⟩
  tm_step () [popBit, Frag.straight, hS]

/-! ### In-place addition and subtraction

`add x y z w` and `sub x y z w` consume `x` and `y` before pushing on `w`,
so `w = x` is a valid instantiation: the result replaces the first operand. -/

theorem add_runs_x {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (xs ys : List Bool) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ys ++ .comma :: yr) :
    (add x y z x).Runs v S (fun _ S' =>
        S' x = bits (addBits xs ys false) ++ .comma :: xr ∧ S' y = yr ∧ S' z = S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → S' k = S k)
      (2 * max xs.length ys.length + 5) := by
  have hzx := hxz.symm
  have h1 := addLoop_runs hxy hxz hyz xs ys xr yr v S hSx hSy
  have h2 : ∀ v₁ S₁, (S₁ x = xr ∧ S₁ y = yr ∧
      S₁ z = (bits (addBits xs ys false)).reverse ++ .comma :: S z ∧
      ∀ k, k ≠ x → k ≠ y → k ≠ z → S₁ k = S k) →
      ((Frag.pushSym x .comma).seq (moveNum z x)).Runs v₁ S₁ (fun _ S' =>
        S' x = bits (addBits xs ys false) ++ .comma :: xr ∧ S' y = yr ∧ S' z = S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → S' k = S k)
      (1 + (max xs.length ys.length + 2)) := by
    intro v₁ S₁ ⟨hx₁, hy₁, hz₁, hf₁⟩
    refine Frag.seq_runs (Frag.pushSym_runs x .comma v₁ S₁) fun v₂ S₂ ⟨hv₂, hS₂⟩ => ?_
    subst hS₂
    have h3 := moveNum_runs hzx (addBits xs ys false).reverse (S z) v₂
      (Function.update S₁ x (.comma :: S₁ x)) (by simp [Function.update_of_ne hzx, hz₁])
    refine Frag.runs_mono h3 (fun v₃ S₃ ⟨hz₃, hx₃, hf₃⟩ => ?_) ?_
    · refine ⟨?_, ?_, hz₃, ?_⟩
      · rw [hx₃]; simp [hx₁]
      · rw [hf₃ y hyz hxy.symm]; simp [Function.update_of_ne hxy.symm, hy₁]
      · intro k hkx hky hkz
        rw [hf₃ k hkz hkx]; simp [Function.update_of_ne hkx, hf₁ k hkx hky hkz]
    · have := addBits_length xs ys false
      simp only [List.length_reverse]; omega
  exact Frag.runs_mono (Frag.seq_runs h1 h2) (fun _ _ h => h) (by omega)

theorem sub_runs_x {x y z : K} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (xs ys : List Bool) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ys ++ .comma :: yr) :
    (sub x y z x).Runs v S (fun _ S' =>
        S' x = bits (subTrunc xs ys false) ++ .comma :: xr ∧ S' y = yr ∧ S' z = S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → S' k = S k)
      (3 * max xs.length ys.length + 5) := by
  have hzx := hxz.symm
  have h1 := subLoop_runs hxy hxz hyz false xs ys xr yr v S hSx hSy
  have h2 : ∀ v₁ S₁, (v₁.carry = subBorrow xs ys false ∧ S₁ x = xr ∧ S₁ y = yr ∧
      S₁ z = (bits (subBits xs ys false)).reverse ++ .comma :: S z ∧
      ∀ k, k ≠ x → k ≠ y → k ≠ z → S₁ k = S k) →
      ((zeroIfBorrow z).seq ((Frag.pushSym x .comma).seq (moveNum z x))).Runs v₁ S₁ (fun _ S' =>
        S' x = bits (subTrunc xs ys false) ++ .comma :: xr ∧ S' y = yr ∧ S' z = S z ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ z → S' k = S k)
      (2 * max xs.length ys.length + 3) :=
    fun v₁ S₁ ⟨hc₁, hx₁, hy₁, hz₁, hf₁⟩ =>
      Frag.runs_mono (subTail_runs hzx xs ys false (S z) v₁ S₁ hc₁ hz₁)
        (fun _ S' ⟨hz, hw, hf⟩ =>
          ⟨by rw [hw, hx₁], by rw [hf y hyz hxy.symm]; exact hy₁, hz,
            fun k hkx hky hkz => by rw [hf k hkz hkx, hf₁ k hkx hky hkz]⟩) le_rfl
  exact Frag.runs_mono (Frag.seq_runs h1 h2) (fun _ _ h => h) (by omega)

/-! ### Multiplication -/

/-- One iteration of `mul`: if the multiplier bit in `ra` is `1`, add the
shifted multiplicand (on `x`) to the accumulator (on `w`) through a copy on
`t`; then double `x` (push a `0`) and pop the next multiplier bit from `y`. -/
def mulBody (x y w s t : K) : Frag :=
  (Frag.ite (fun v => decide (v.ra = some true))
      ((dup x t s).seq (add w t s w)) Frag.skip).seq
    ((Frag.pushSym x (.bit false)).seq (popBit y))

/-- `w := x * y` (schoolbook, shift-and-add over the bits of `y`, LSB first):
consumes the top numbers of `x` and `y`; the product is pushed on `w` (a bit
list of the right value, not necessarily canonical); scratch `s` (used by
`dup` and `add`) and `t` (the copy of the shifted multiplicand) are restored.
`push comma on w ; popBit y ; while ¬da: mulBody ; dropNum x`. -/
def mul (x y w s t : K) : Frag :=
  (Frag.pushSym w .comma).seq ((popBit y).seq
    ((Frag.loop (fun v => !v.da) (mulBody x y w s t)).seq (dropNum x)))

/-- Loop invariant of `mul` after `i` iterations: phase 1 has popped the
multiplier bit `b` (index `i`) into `ra`, with prefix `p` already folded into
the accumulator; phase 2 (`i = |ys|`) has popped the terminator. -/
def MulInv (x y w s t : K) (xs ys : List Bool) (xr yr wr sr tr : List Γ') (S₀ : Stacks)
    (i : ℕ) (v : St) (S : Stacks) : Prop :=
  (∃ p b q, ys = p ++ b :: q ∧ p.length = i ∧ v.da = false ∧ v.ra = some b ∧
    S y = bits q ++ .comma :: yr ∧
    S x = bits (List.replicate i false ++ xs) ++ .comma :: xr ∧
    S w = bits (mulGo [] xs p) ++ .comma :: wr ∧ S s = sr ∧ S t = tr ∧
    ∀ k, k ≠ x → k ≠ y → k ≠ w → k ≠ s → k ≠ t → S k = S₀ k) ∨
  (i = ys.length ∧ v.da = true ∧ S y = yr ∧
    S x = bits (List.replicate i false ++ xs) ++ .comma :: xr ∧
    S w = bits (mulGo [] xs ys) ++ .comma :: wr ∧ S s = sr ∧ S t = tr ∧
    ∀ k, k ≠ x → k ≠ y → k ≠ w → k ≠ s → k ≠ t → S k = S₀ k)

theorem mulBody_runs {x y w s t : K} (hxy : x ≠ y) (hxw : x ≠ w) (hxs : x ≠ s) (hxt : x ≠ t)
    (hyw : y ≠ w) (hys : y ≠ s) (hyt : y ≠ t) (hws : w ≠ s) (hwt : w ≠ t) (hst : s ≠ t)
    (xs ys : List Bool) (xr yr wr sr tr : List Γ') (S₀ : Stacks)
    (i : ℕ) (hi : i < ys.length) (v : St) (S : Stacks)
    (hI : MulInv x y w s t xs ys xr yr wr sr tr S₀ i v S) :
    (mulBody x y w s t).Runs v S (MulInv x y w s t xs ys xr yr wr sr tr S₀ (i + 1))
      (4 * xs.length + 6 * ys.length + 13) := by
  have hyx := hxy.symm
  have hwx := hxw.symm
  have hwy := hyw.symm
  have hts := hst.symm
  rcases hI with ⟨p, b, q, hpq, hp, hda, hra, hy, hx, hw, hs, ht, hF⟩ | ⟨hi', -⟩
  swap; · omega
  have hlen : p.length + 1 + q.length = ys.length := by
    have := congrArg List.length hpq; simp at this; omega
  set sh := List.replicate i false ++ xs with hsh
  have hshlen : sh.length = i + xs.length := by simp [hsh]
  have hacclen : (mulGo [] xs p).length ≤ xs.length + 2 * i := by
    have := mulGo_length [] xs p; simp at this; omega
  -- stage 1: the conditional add
  have h1 : (Frag.ite (fun v => decide (v.ra = some true))
      ((dup x t s).seq (add w t s w)) Frag.skip).Runs v S
      (fun _ S₁ => S₁ y = bits q ++ .comma :: yr ∧ S₁ x = bits sh ++ .comma :: xr ∧
        S₁ w = bits (condAdd b (mulGo [] xs p) sh) ++ .comma :: wr ∧ S₁ s = sr ∧ S₁ t = tr ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ w → k ≠ s → k ≠ t → S₁ k = S₀ k)
      (4 * xs.length + 6 * ys.length + 11) := by
    cases b
    · refine Frag.ite_runs_false (by simp [hra]) ?_
      refine Frag.runs_mono (Frag.skip_runs v S) (fun v₁ S₁ ⟨_, hS₁⟩ => ?_) (by omega)
      subst hS₁
      exact ⟨hy, hx, by simpa [condAdd] using hw, hs, ht, hF⟩
    · refine Frag.ite_runs_true (by simp [hra]) ?_
      have hd := dup_runs hxt hxs hts sh xr v S hx
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * (xs.length + 2 * ys.length) + 5) hd
        fun v₁ S₁ ⟨hx₁, ht₁, hs₁, hf₁⟩ => ?_) (fun _ _ h => h) (by omega)
      have ha := add_runs_x hwt hws hts (mulGo [] xs p) sh wr tr v₁ S₁
        (by rw [hf₁ w hwx hwt hws]; exact hw) (by rw [ht₁, ht])
      refine Frag.runs_mono ha (fun v₂ S₂ ⟨hw₂, ht₂, hs₂, hf₂⟩ => ⟨?_, ?_, ?_, ?_, ht₂, ?_⟩) ?_
      · rw [hf₂ y hyw hyt hys, hf₁ y hyx hyt hys]; exact hy
      · rw [hf₂ x hxw hxt hxs, hx₁]; exact hx
      · rw [hw₂]; rfl
      · rw [hs₂, hs₁]; exact hs
      · intro k hkx hky hkw hks hkt
        rw [hf₂ k hkw hkt hks, hf₁ k hkx hkt hks]; exact hF k hkx hky hkw hks hkt
      · have : max (mulGo [] xs p).length sh.length ≤ xs.length + 2 * ys.length := by omega
        omega
  -- stage 2: double the multiplicand
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2) h1 fun v₁ S₁ ⟨hy₁, hx₁, hw₁, hs₁, ht₁, hF₁⟩ => ?_)
    (fun _ _ h => h) (by omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) (Frag.pushSym_runs x (.bit false) v₁ S₁)
    fun v₂ S₂ ⟨_, hS₂⟩ => ?_) (fun _ _ h => h) le_rfl
  subst hS₂
  have hmul : mulGo [] xs (p ++ [b]) = condAdd b (mulGo [] xs p) sh := by
    rw [mulGo_append, mulGo_singleton, hp]
  have hx₂ : Function.update S₁ x (.bit false :: S₁ x) x =
      bits (List.replicate (i + 1) false ++ xs) ++ .comma :: xr := by
    simp [hx₁, hsh, List.replicate_succ]
  -- stage 3: pop the next multiplier symbol
  cases q with
  | nil =>
    have hy₂ : Function.update S₁ x (.bit false :: S₁ x) y = .comma :: yr := by
      simp [Function.update_of_ne hyx, hy₁]
    refine Frag.runs_mono (popBit_runs_end yr v₂ _ hy₂) (fun v₃ S₃ ⟨hv₃, hS₃⟩ => Or.inr ?_) le_rfl
    subst hS₃; subst hv₃
    refine ⟨by simp at hlen; omega, rfl, by simp, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne hxy]; exact hx₂
    · rw [hpq, hmul]; simp [Function.update_of_ne hwy, Function.update_of_ne hwx, hw₁]
    · simp [Function.update_of_ne hys.symm, Function.update_of_ne hxs.symm, hs₁]
    · simp [Function.update_of_ne hyt.symm, Function.update_of_ne hxt.symm, ht₁]
    · intro k hkx hky hkw hks hkt
      simp [Function.update_of_ne hky, Function.update_of_ne hkx, hF₁ k hkx hky hkw hks hkt]
  | cons b' q' =>
    have hy₂ : Function.update S₁ x (.bit false :: S₁ x) y = bits (b' :: q') ++ .comma :: yr := by
      simp [Function.update_of_ne hyx, hy₁]
    refine Frag.runs_mono (popBit_runs_bit b' q' yr v₂ _ hy₂)
      (fun v₃ S₃ ⟨hv₃, hS₃⟩ => Or.inl ⟨p ++ [b], b', q', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
    · rw [hpq, List.append_assoc]; rfl
    · simp [hp]
    · rw [hv₃]
    · rw [hv₃]
    · rw [hS₃]; simp
    · rw [hS₃, Function.update_of_ne hxy]; exact hx₂
    · rw [hS₃, hmul]; simp [Function.update_of_ne hwy, Function.update_of_ne hwx, hw₁]
    · rw [hS₃]; simp [Function.update_of_ne hys.symm, Function.update_of_ne hxs.symm, hs₁]
    · rw [hS₃]; simp [Function.update_of_ne hyt.symm, Function.update_of_ne hxt.symm, ht₁]
    · intro k hkx hky hkw hks hkt
      rw [hS₃]; simp [Function.update_of_ne hky, Function.update_of_ne hkx, hF₁ k hkx hky hkw hks hkt]

theorem mul_runs {x y w s t : K} (hxy : x ≠ y) (hxw : x ≠ w) (hxs : x ≠ s) (hxt : x ≠ t)
    (hyw : y ≠ w) (hys : y ≠ s) (hyt : y ≠ t) (hws : w ≠ s) (hwt : w ≠ t) (hst : s ≠ t)
    (xs ys : List Bool) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ys ++ .comma :: yr) :
    (mul x y w s t).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ S' w = bits (mulGo [] xs ys) ++ .comma :: S w ∧
        S' s = S s ∧ S' t = S t ∧ ∀ k, k ≠ x → k ≠ y → k ≠ w → k ≠ s → k ≠ t → S' k = S k)
      (ys.length * (4 * xs.length + 6 * ys.length + 14) + xs.length + ys.length + 4) := by
  have hyx := hxy.symm
  have hwx := hxw.symm
  have hwy := hyw.symm
  set TL := ys.length * (4 * xs.length + 6 * ys.length + 13 + 1) + 1 with hTL
  -- stage 1: push comma on w (the accumulator `0`)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL + xs.length + ys.length + 2)
    (Frag.pushSym_runs w .comma v S) fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h)
    (by rw [hTL]; ring_nf; omega)
  subst hS₁; rw [hv₁]
  -- stage 2: pop the first multiplier symbol, establishing the invariant
  have h2 : (popBit y).Runs v (Function.update S w (.comma :: S w))
      (MulInv x y w s t xs ys xr yr (S w) (S s) (S t) S 0) 1 := by
    cases ys with
    | nil =>
      refine Frag.runs_mono (popBit_runs_end yr v _ (by simp [Function.update_of_ne hyw, hSy]))
        (fun v' S' ⟨hv', hS'⟩ => Or.inr ⟨rfl, by rw [hv'], ?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
      · rw [hS']; simp
      · rw [hS']; simp [Function.update_of_ne hxy, Function.update_of_ne hxw, hSx]
      · rw [hS']; simp [Function.update_of_ne hwy, mulGo]
      · rw [hS']; simp [Function.update_of_ne hys.symm, Function.update_of_ne hws.symm]
      · rw [hS']; simp [Function.update_of_ne hyt.symm, Function.update_of_ne hwt.symm]
      · intro k hkx hky hkw hks hkt
        rw [hS']; simp [Function.update_of_ne hky, Function.update_of_ne hkw]
    | cons b ys' =>
      refine Frag.runs_mono (popBit_runs_bit b ys' yr v _ (by simp [Function.update_of_ne hyw, hSy]))
        (fun v' S' ⟨hv', hS'⟩ => Or.inl ⟨[], b, ys', rfl, rfl, by rw [hv'], by rw [hv'],
          ?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
      · rw [hS']; simp
      · rw [hS']; simp [Function.update_of_ne hxy, Function.update_of_ne hxw, hSx]
      · rw [hS']; simp [Function.update_of_ne hwy, mulGo]
      · rw [hS']; simp [Function.update_of_ne hys.symm, Function.update_of_ne hws.symm]
      · rw [hS']; simp [Function.update_of_ne hyt.symm, Function.update_of_ne hwt.symm]
      · intro k hkx hky hkw hks hkt
        rw [hS']; simp [Function.update_of_ne hky, Function.update_of_ne hkw]
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL + xs.length + ys.length + 1) h2
    fun v₂ S₂ hI₂ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: the loop
  have hloop := Frag.loop_runs (c := fun v => !v.da) (B := mulBody x y w s t)
    (MulInv x y w s t xs ys xr yr (S w) (S s) (S t) S) ys.length
    (4 * xs.length + 6 * ys.length + 13) (v := v₂) (S := S₂) hI₂
    (fun i hi u T hI => by
      rcases hI with ⟨p, b, q, -, -, hda, -⟩ | ⟨hi', -⟩
      · simp [hda]
      · omega)
    (fun u T hI => by
      rcases hI with ⟨p, b, q, hpq, hp, -⟩ | ⟨-, hda, -⟩
      · have := congrArg List.length hpq; simp at this; omega
      · simp [hda])
    (fun i hi u T hI => mulBody_runs hxy hxw hxs hxt hyw hys hyt hws hwt hst xs ys xr yr
      (S w) (S s) (S t) S i hi u T hI)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := xs.length + ys.length + 1) hloop
    fun v₃ S₃ ⟨hI₃, _⟩ => ?_) (fun _ _ h => h) (by omega)
  rcases hI₃ with ⟨p, b, q, hpq, hp, -⟩ | ⟨-, -, hy₃, hx₃, hw₃, hs₃, ht₃, hF₃⟩
  · have := congrArg List.length hpq; simp at this; omega
  -- stage 4: drop the shifted multiplicand
  have h4 := dropNum_runs (List.replicate ys.length false ++ xs) xr v₃ S₃ hx₃
  refine Frag.runs_mono h4 (fun v₄ S₄ ⟨_, _, _, hx₄, hf₄⟩ => ⟨hx₄, ?_, ?_, ?_, ?_, ?_⟩) (by simp; omega)
  · rw [hf₄ y hyx, hy₃]
  · rw [hf₄ w hwx, hw₃]
  · rw [hf₄ s hxs.symm, hs₃]
  · rw [hf₄ t hxt.symm, ht₃]
  · intro k hkx hky hkw hks hkt; rw [hf₄ k hkx, hF₃ k hkx hky hkw hks hkt]

/-- Multiplication on naturals: the machine leaves a bit list of value
`a * b` on `w`. -/
theorem mul_correct {x y w s t : K} (hxy : x ≠ y) (hxw : x ≠ w) (hxs : x ≠ s) (hxt : x ≠ t)
    (hyw : y ≠ w) (hys : y ≠ s) (hyt : y ≠ t) (hws : w ≠ s) (hwt : w ≠ t) (hst : s ≠ t)
    (a b : ℕ) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' b ++ .comma :: yr) :
    (mul x y w s t).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ (∃ l, toNat l = a * b ∧ S' w = bits l ++ .comma :: S w) ∧
        S' s = S s ∧ S' t = S t ∧ ∀ k, k ≠ x → k ≠ y → k ≠ w → k ≠ s → k ≠ t → S' k = S k)
      ((Nat.log 2 b + 1) * (4 * Nat.log 2 a + 6 * Nat.log 2 b + 24) +
        Nat.log 2 a + Nat.log 2 b + 6) := by
  have h := mul_runs hxy hxw hxs hxt hyw hys hyt hws hwt hst (Computability.encodeNat a)
    (Computability.encodeNat b) xr yr v S hSx hSy
  refine Frag.runs_mono h (fun v' S' ⟨hx, hy, hw, hs, ht, hf⟩ =>
    ⟨hx, hy, ⟨_, by rw [toNat_mulGo, toNat_encodeNat, toNat_encodeNat]; simp [toNat], hw⟩,
      hs, ht, hf⟩) ?_
  have ha := encodeNat_length_le a
  have hb := encodeNat_length_le b
  have := Nat.mul_le_mul hb (show 4 * (Computability.encodeNat a).length +
    6 * (Computability.encodeNat b).length + 14 ≤ 4 * Nat.log 2 a + 6 * Nat.log 2 b + 24 by omega)
  omega

/-- `mul` within budget for operands below `2 ^ m`. -/
theorem mul_le_B {x y w s t : K} (hxy : x ≠ y) (hxw : x ≠ w) (hxs : x ≠ s) (hxt : x ≠ t)
    (hyw : y ≠ w) (hys : y ≠ s) (hyt : y ≠ t) (hws : w ≠ s) (hwt : w ≠ t) (hst : s ≠ t)
    (a b m : ℕ) (ha : a < 2 ^ m) (hb : b < 2 ^ m) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' b ++ .comma :: yr) :
    (mul x y w s t).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ (∃ l, toNat l = a * b ∧ S' w = bits l ++ .comma :: S w) ∧
        S' s = S s ∧ S' t = S t ∧ ∀ k, k ≠ x → k ≠ y → k ≠ w → k ≠ s → k ≠ t → S' k = S k)
      (B m) := by
  have h := mul_runs hxy hxw hxs hxt hyw hys hyt hws hwt hst (Computability.encodeNat a)
    (Computability.encodeNat b) xr yr v S hSx hSy
  refine Frag.runs_mono h (fun v' S' ⟨hx, hy, hw, hs, ht, hf⟩ =>
    ⟨hx, hy, ⟨_, by rw [toNat_mulGo, toNat_encodeNat, toNat_encodeNat]; simp [toNat], hw⟩,
      hs, ht, hf⟩) ?_
  have ha := encodeNat_length_le_of_lt_pow ha
  have hb := encodeNat_length_le_of_lt_pow hb
  have := Nat.mul_le_mul hb (show 4 * (Computability.encodeNat a).length +
    6 * (Computability.encodeNat b).length + 14 ≤ 10 * m + 14 by omega)
  apply le_B_of_le_quad
  nlinarith

/-! ### Division with remainder: arithmetic -/

/-- One step of binary long division: from `a / (2D)`, `a % (2D)` to `a / D`, `a % D`. -/
theorem divmod_step (a D : ℕ) (hD : 0 < D) :
    a / D = 2 * (a / (2 * D)) + (if D ≤ a % (2 * D) then 1 else 0) ∧
    a % D = a % (2 * D) - (if D ≤ a % (2 * D) then D else 0) := by
  have h2D : 0 < 2 * D := by omega
  have hdm := Nat.div_add_mod a (2 * D)
  have hlt := Nat.mod_lt a h2D
  rw [Nat.div_mod_unique hD]
  generalize a / (2 * D) = qq at hdm ⊢
  generalize a % (2 * D) = r at hdm hlt ⊢
  split_ifs with h
  · refine ⟨?_, by omega⟩
    have : D * (2 * qq + 1) = 2 * D * qq + D := by ring
    omega
  · simp only [add_zero, Nat.sub_zero]
    refine ⟨?_, by omega⟩
    have : D * (2 * qq) = 2 * D * qq := by ring
    omega

theorem exists_lt_two_pow_mul (a d : ℕ) (hd : 1 ≤ d) : ∃ i, a < 2 ^ i * d :=
  ⟨a, lt_of_lt_of_le Nat.lt_two_pow_self (Nat.le_mul_of_pos_right _ hd)⟩

/-- The number of doublings of `d` needed to exceed `a`: the least `i` with
`a < 2 ^ i * d`. -/
def divSteps (a d : ℕ) (hd : 1 ≤ d) : ℕ := Nat.find (exists_lt_two_pow_mul a d hd)

theorem divSteps_spec (a d : ℕ) (hd : 1 ≤ d) : a < 2 ^ divSteps a d hd * d :=
  Nat.find_spec (exists_lt_two_pow_mul a d hd)

theorem divSteps_min (a d : ℕ) (hd : 1 ≤ d) {i : ℕ} (hi : i < divSteps a d hd) :
    2 ^ i * d ≤ a := by
  have := Nat.find_min (exists_lt_two_pow_mul a d hd) hi
  omega

theorem divSteps_le (a d : ℕ) (hd : 1 ≤ d) {n : ℕ} (h : a < 2 ^ n) : divSteps a d hd ≤ n :=
  Nat.find_min' _ (lt_of_lt_of_le h (Nat.le_mul_of_pos_right _ hd))

/-! ### Division: the shift-up loop -/

/-- One iteration of the shift-up phase: `sh := 2 sh` (push a `0` on `y`),
`j := j + 1`, then compare `sh` with `a` through copies on `t`, `s`
(`cmp := compare sh a`). -/
def dmUpBody (x y j s t : K) : Frag :=
  (Frag.pushSym y (.bit false)).seq ((incr j s).seq ((dup y t s).seq ((dup x s t).seq (cmpFrag t s))))

/-- Invariant of the shift-up loop after `i` iterations: `y` holds `2^i d`,
`j` holds `i`, `cmp = compare (2^i d) a`. -/
def DmUpInv (x y j s t : K) (xs ds : List Bool) (J : ℕ) (xr yr jr sr tr : List Γ') (S₀ : Stacks)
    (i : ℕ) (v : St) (S : Stacks) : Prop :=
  i ≤ J ∧ v.cmp = compare (2 ^ i * toNat ds) (toNat xs) ∧
  S j = encodeNatΓ' i ++ .comma :: jr ∧
  S y = bits (List.replicate i false ++ ds) ++ .comma :: yr ∧
  S x = bits xs ++ .comma :: xr ∧ S s = sr ∧ S t = tr ∧
  ∀ k, k ≠ x → k ≠ y → k ≠ j → k ≠ s → k ≠ t → S k = S₀ k

theorem dmUpBody_runs {x y j s t : K} (hxy : x ≠ y) (hxj : x ≠ j) (hxs : x ≠ s) (hxt : x ≠ t)
    (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (xs ds : List Bool) (J : ℕ) (hJ : J ≤ xs.length) (xr yr jr sr tr : List Γ') (S₀ : Stacks)
    (i : ℕ) (hi : i < J) (v : St) (S : Stacks)
    (hI : DmUpInv x y j s t xs ds J xr yr jr sr tr S₀ i v S) :
    (dmUpBody x y j s t).Runs v S (DmUpInv x y j s t xs ds J xr yr jr sr tr S₀ (i + 1))
      (7 * (xs.length + ds.length) + 18) := by
  have hyx := hxy.symm
  have hjx := hxj.symm
  have hjy := hyj.symm
  have hts := hst.symm
  obtain ⟨-, -, hj, hy, hx, hs, ht, hF⟩ := hI
  set sh := List.replicate (i + 1) false ++ ds with hsh
  have hshlen : sh.length = i + 1 + ds.length := by simp [hsh]
  have hlogi : Nat.log 2 i ≤ xs.length := (Nat.log_le_self 2 i).trans (by omega)
  -- stage 1: double `sh`
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 7 * (xs.length + ds.length) + 17)
    (Frag.pushSym_runs y (.bit false) v S) fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₁; rw [hv₁]
  -- stage 2: `j := j + 1`
  have h2 := incr_correct hjs i jr v (Function.update S y (.bit false :: S y))
    (by simp [Function.update_of_ne hjy, hj])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * (xs.length + ds.length) + 12) h2
    fun v₂ S₂ ⟨_, _, _, hj₂, hs₂, hf₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: copy `sh` to `t`
  have hy₂ : S₂ y = bits sh ++ .comma :: yr := by
    rw [hf₂ y hyj hys]; simp [hy, hsh, List.replicate_succ]
  have h3 := dup_runs hyt hys hts sh yr v₂ S₂ hy₂
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * (xs.length + ds.length) + 7) h3
    fun v₃ S₃ ⟨hy₃, ht₃, hs₃, hf₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 4: copy `a` to `s`
  have hx₃ : S₃ x = bits xs ++ .comma :: xr := by
    rw [hf₃ x hxy hxt hxs, hf₂ x hxj hxs]; simp [Function.update_of_ne hxy, hx]
  have h4 := dup_runs hxs hxt hst xs xr v₃ S₃ hx₃
  refine Frag.runs_mono (Frag.seq_runs (t₂ := xs.length + ds.length + 2) h4
    fun v₄ S₄ ⟨hx₄, hs₄, ht₄, hf₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 5: compare
  have ht₄' : S₄ t = bits sh ++ .comma :: tr := by
    rw [ht₄, ht₃, hf₂ t hjt.symm hst.symm]; simp [Function.update_of_ne hyt.symm, ht]
  have hs₄' : S₄ s = bits xs ++ .comma :: sr := by
    rw [hs₄, hs₃, hs₂]; simp [Function.update_of_ne hys.symm, hs]
  have h5 := cmpFrag_runs hts sh xs tr sr v₄ S₄ ht₄' hs₄'
  refine Frag.runs_mono h5 (fun v₅ S₅ ⟨hc₅, ht₅, hs₅, hf₅⟩ => ⟨by omega, ?_, ?_, ?_, ?_, hs₅, ht₅, ?_⟩)
    (by omega)
  · rw [hc₅, hsh, toNat_replicate_false_append]
  · rw [hf₅ j hjt hjs, hf₄ j hjx hjs hjt, hf₃ j hjy hjt hjs, hj₂]
  · rw [hf₅ y hyt hys, hf₄ y hyx hys hyt, hy₃, hy₂]
  · rw [hf₅ x hxt hxs, hx₄, hx₃]
  · intro k hkx hky hkj hks hkt
    rw [hf₅ k hkt hks, hf₄ k hkx hks hkt, hf₃ k hky hkt hks, hf₂ k hkj hks]
    simp [Function.update_of_ne hky, hF k hkx hky hkj hks hkt]

/-! ### Division: the shift-down loop -/

/-- One iteration of the shift-down phase: `j := j - 1`; `sh := sh / 2` (pop
the `0` on top of `y`); `q := 2q` (push a `0` on `q`); compare `sh` with `r`
through copies on `t`, `s`; if `sh ≤ r` then `r := r - sh` (copy of `sh` on
`t`, in-place subtraction on `x`) and `q := q + 1`; finally test `j` for zero
(`flag`). -/
def dmDownBody (x y q j s t : K) : Frag :=
  (predNum j s).seq ((popBit y).seq ((Frag.pushSym q (.bit false)).seq ((dup y t s).seq
    ((dup x s t).seq ((cmpFrag t s).seq
      ((Frag.ite (fun v => !decide (v.cmp = .gt))
        ((dup y t s).seq ((sub x t s x).seq (incr q s))) Frag.skip).seq (isZero j s)))))))

/-- Invariant of the shift-down loop after `i` iterations: with
`D = 2^(J-i) d`, `j` holds `J - i`, `y` holds `D`, `q` holds `a / D` (an
`i`-bit list), `x` holds `a % D`, `flag` says whether `j` is zero. -/
def DmDownInv (x y q j s t : K) (xs ds : List Bool) (J : ℕ) (xr yr qr jr sr tr : List Γ')
    (S₀ : Stacks) (i : ℕ) (v : St) (S : Stacks) : Prop :=
  i ≤ J ∧ v.flag = decide (J - i = 0) ∧
  S j = encodeNatΓ' (J - i) ++ .comma :: jr ∧
  S y = bits (List.replicate (J - i) false ++ ds) ++ .comma :: yr ∧
  (∃ ql, ql.length = i ∧ toNat ql = toNat xs / (2 ^ (J - i) * toNat ds) ∧
    S q = bits ql ++ .comma :: qr) ∧
  (∃ rl, rl.length ≤ xs.length + ds.length ∧ toNat rl = toNat xs % (2 ^ (J - i) * toNat ds) ∧
    S x = bits rl ++ .comma :: xr) ∧
  S s = sr ∧ S t = tr ∧
  ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S k = S₀ k

theorem dmDownBody_runs {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (xs ds : List Bool) (hd : 1 ≤ toNat ds) (J : ℕ) (hJ : J ≤ xs.length)
    (xr yr qr jr sr tr : List Γ') (S₀ : Stacks) (i : ℕ) (hi : i < J) (v : St) (S : Stacks)
    (hI : DmDownInv x y q j s t xs ds J xr yr qr jr sr tr S₀ i v S) :
    (dmDownBody x y q j s t).Runs v S (DmDownInv x y q j s t xs ds J xr yr qr jr sr tr S₀ (i + 1))
      (16 * (xs.length + ds.length) + 40) := by
  have hyx := hxy.symm
  have hqx := hxq.symm
  have hqy := hyq.symm
  have hjx := hxj.symm
  have hjy := hyj.symm
  have hjq := hqj.symm
  have hsx := hxs.symm
  have hsy := hys.symm
  have hsq := hqs.symm
  have hsj := hjs.symm
  have htx := hxt.symm
  have hty := hyt.symm
  have htq := hqt.symm
  have htj := hjt.symm
  have hts := hst.symm
  obtain ⟨-, -, hj, hy, ⟨ql, hql, hqv, hq⟩, ⟨rl, hrl, hrv, hx⟩, hs, ht, hF⟩ := hI
  set N := xs.length + ds.length with hN
  set e := J - i - 1 with he
  have hJi : J - i = e + 1 := by omega
  have hJi' : J - (i + 1) = e := by omega
  set sh := List.replicate e false ++ ds with hsh
  have hshlen : sh.length = e + ds.length := by simp [hsh]
  have hshv : toNat sh = 2 ^ e * toNat ds := by rw [hsh, toNat_replicate_false_append]
  have hD : 0 < 2 ^ e * toNat ds := Nat.mul_pos (Nat.two_pow_pos e) hd
  have hstep := divmod_step (toNat xs) (2 ^ e * toNat ds) hD
  have h2D : 2 * (2 ^ e * toNat ds) = 2 ^ (J - i) * toNat ds := by rw [hJi, pow_succ]; ring
  rw [h2D] at hstep
  have hlog1 : Nat.log 2 (J - i) ≤ N := (Nat.log_le_self 2 _).trans (by omega)
  have hlog2 : Nat.log 2 e ≤ N := (Nat.log_le_self 2 _).trans (by omega)
  -- stage 1: `j := j - 1`
  have h1 := predNum_correct hjs (J - i) (by omega) jr v S hj
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 14 * N + 35) h1
    fun v₁ S₁ ⟨_, _, hj₁, hs₁, hf₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 2: `sh := sh / 2`
  have hy₁ : S₁ y = bits (false :: sh) ++ .comma :: yr := by
    rw [hf₁ y hyj hys, hy, hJi]; simp [hsh, List.replicate_succ]
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 14 * N + 34) (popBit_runs_bit false sh yr v₁ S₁ hy₁)
    fun v₂ S₂ ⟨_, hS₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: `q := 2q`
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 14 * N + 33) (Frag.pushSym_runs q (.bit false) v₂ S₂)
    fun v₃ S₃ ⟨_, hS₃⟩ => ?_) (fun _ _ h => h) (by omega)
  have hy₃ : S₃ y = bits sh ++ .comma :: yr := by rw [hS₃, hS₂]; simp [Function.update_of_ne hyq]
  have hq₃ : S₃ q = bits (false :: ql) ++ .comma :: qr := by
    rw [hS₃, hS₂]; simp [Function.update_of_ne hqy, hf₁ q hqj hqs, hq]
  have hx₃ : S₃ x = bits rl ++ .comma :: xr := by
    rw [hS₃, hS₂]; simp [Function.update_of_ne hxq, Function.update_of_ne hxy, hf₁ x hxj hxs, hx]
  have hj₃ : S₃ j = encodeNatΓ' e ++ .comma :: jr := by
    rw [hS₃, hS₂]; simp [Function.update_of_ne hjq, Function.update_of_ne hjy, hj₁, he]
  have hs₃ : S₃ s = sr := by
    rw [hS₃, hS₂]; simp [Function.update_of_ne hsq, Function.update_of_ne hsy, hs₁, hs]
  have ht₃ : S₃ t = tr := by
    rw [hS₃, hS₂]; simp [Function.update_of_ne htq, Function.update_of_ne hty, hf₁ t htj hts, ht]
  have hF₃ : ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S₃ k = S₀ k :=
    fun k hkx hky hkq hkj hks hkt => by
      rw [hS₃, hS₂]
      simp [Function.update_of_ne hkq, Function.update_of_ne hky, hf₁ k hkj hks,
        hF k hkx hky hkq hkj hks hkt]
  -- stage 4: copy `sh` to `t`
  have h4 := dup_runs hyt hys hts sh yr v₃ S₃ hy₃
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 12 * N + 28) h4
    fun v₄ S₄ ⟨hy₄, ht₄, hs₄, hf₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 5: copy `r` to `s`
  have hx₄ : S₄ x = bits rl ++ .comma :: xr := by rw [hf₄ x hxy hxt hxs, hx₃]
  have h5 := dup_runs hxs hxt hst rl xr v₄ S₄ hx₄
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 10 * N + 23) h5
    fun v₅ S₅ ⟨hx₅, hs₅, ht₅, hf₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 6: compare `sh` with `r`
  have ht₅' : S₅ t = bits sh ++ .comma :: tr := by rw [ht₅, ht₄, ht₃]
  have hs₅' : S₅ s = bits rl ++ .comma :: sr := by rw [hs₅, hs₄, hs₃]
  have h6 := cmpFrag_runs hts sh rl tr sr v₅ S₅ ht₅' hs₅'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 9 * N + 21) h6
    fun v₆ S₆ ⟨hc₆, ht₆, hs₆, hf₆⟩ => ?_) (fun _ _ h => h) (by omega)
  have hx₆ : S₆ x = bits rl ++ .comma :: xr := by rw [hf₆ x hxt hxs, hx₅, hx₄]
  have hq₆ : S₆ q = bits (false :: ql) ++ .comma :: qr := by
    rw [hf₆ q hqt hqs, hf₅ q hqx hqs hqt, hf₄ q hqy hqt hqs, hq₃]
  have hy₆ : S₆ y = bits sh ++ .comma :: yr := by
    rw [hf₆ y hyt hys, hf₅ y hyx hys hyt, hy₄, hy₃]
  have hj₆ : S₆ j = encodeNatΓ' e ++ .comma :: jr := by
    rw [hf₆ j hjt hjs, hf₅ j hjx hjs hjt, hf₄ j hjy hjt hjs, hj₃]
  have hF₆ : ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S₆ k = S₀ k :=
    fun k hkx hky hkq hkj hks hkt => by
      rw [hf₆ k hkt hks, hf₅ k hkx hks hkt, hf₄ k hky hkt hks, hF₃ k hkx hky hkq hkj hks hkt]
  rw [hshv, hrv] at hc₆
  -- stage 7: conditional subtraction
  have h7 : (Frag.ite (fun v => !decide (v.cmp = .gt))
      ((dup y t s).seq ((sub x t s x).seq (incr q s))) Frag.skip).Runs v₆ S₆
      (fun _ S₇ => S₇ j = encodeNatΓ' e ++ .comma :: jr ∧ S₇ y = bits sh ++ .comma :: yr ∧
        (∃ ql', ql'.length = i + 1 ∧ toNat ql' = toNat xs / (2 ^ e * toNat ds) ∧
          S₇ q = bits ql' ++ .comma :: qr) ∧
        (∃ rl', rl'.length ≤ N ∧ toNat rl' = toNat xs % (2 ^ e * toNat ds) ∧
          S₇ x = bits rl' ++ .comma :: xr) ∧
        S₇ s = sr ∧ S₇ t = tr ∧ ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S₇ k = S₀ k)
      (7 * N + 14) := by
    by_cases hle : 2 ^ e * toNat ds ≤ toNat xs % (2 ^ (J - i) * toNat ds)
    · have hc : (!decide (v₆.cmp = .gt)) = true := by
        rw [hc₆]; simp [compare_gt_iff_gt, hle]
      refine Frag.ite_runs_true hc ?_
      -- copy `sh` to `t`
      have h7a := dup_runs hyt hys hts sh yr v₆ S₆ hy₆
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * N + 8) h7a
        fun v₇ S₇ ⟨hy₇, ht₇, hs₇, hf₇⟩ => ?_) (fun _ _ h => h) (by omega)
      -- `r := r - sh`
      have hx₇ : S₇ x = bits rl ++ .comma :: xr := by rw [hf₇ x hxy hxt hxs, hx₆]
      have ht₇' : S₇ t = bits sh ++ .comma :: tr := by rw [ht₇, ht₆]
      have h7b := sub_runs_x hxt hxs hts rl sh xr tr v₇ S₇ hx₇ ht₇'
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * N + 3) h7b
        fun v₈ S₈ ⟨hx₈, ht₈, hs₈, hf₈⟩ => ?_) (fun _ _ h => h) (by omega)
      -- `q := q + 1`
      have hq₈ : S₈ q = bits (false :: ql) ++ .comma :: qr := by
        rw [hf₈ q hqx hqt hqs, hf₇ q hqy hqt hqs, hq₆]
      have h7c := incr_runs hqs (false :: ql) qr v₈ S₈ hq₈
      refine Frag.runs_mono h7c (fun v₉ S₉ ⟨_, _, _, hq₉, hs₉, hf₉⟩ =>
        ⟨?_, ?_, ⟨true :: ql, by simp [hql], ?_, ?_⟩, ⟨subTrunc rl sh false, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩) ?_
      · rw [hf₉ j hjq hjs, hf₈ j hjx hjt hjs, hf₇ j hjy hjt hjs, hj₆]
      · rw [hf₉ y hyq hys, hf₈ y hyx hyt hys, hy₇, hy₆]
      · rw [hstep.1, if_pos hle]; simp [toNat, hqv]; ring
      · rw [hq₉]; simp [incBits]
      · have := subTrunc_length rl sh false; omega
      · rw [hstep.2, if_pos hle, toNat_subTrunc, hrv, hshv]; simp
      · rw [hf₉ x hxq hxs, hx₈]
      · rw [hs₉, hs₈, hs₇, hs₆]
      · rw [hf₉ t htq hts, ht₈]
      · intro k hkx hky hkq hkj hks hkt
        rw [hf₉ k hkq hks, hf₈ k hkx hkt hks, hf₇ k hky hkt hks, hF₆ k hkx hky hkq hkj hks hkt]
      · simp only [List.length_cons]; omega
    · have hc : (!decide (v₆.cmp = .gt)) = false := by
        rw [hc₆]; simp [compare_gt_iff_gt]; omega
      refine Frag.ite_runs_false hc ?_
      refine Frag.runs_mono (Frag.skip_runs v₆ S₆) (fun v₇ S₇ ⟨_, hS₇⟩ => ?_) (by omega)
      subst hS₇
      refine ⟨hj₆, hy₆, ⟨false :: ql, by simp [hql], ?_, hq₆⟩, ⟨rl, by omega, ?_, hx₆⟩, hs₆, ht₆, hF₆⟩
      · rw [hstep.1, if_neg hle]; simp [toNat, hqv]
      · rw [hstep.2, if_neg hle, hrv]; simp
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * N + 7) h7
    fun v₇ S₇ ⟨hj₇, hy₇, hq₇, hx₇, hs₇, ht₇, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 8: test `j` for zero
  have h8 := isZero_correct hjs e jr v₇ S₇ hj₇
  refine Frag.runs_mono h8 (fun v₈ S₈ ⟨hfl₈, _, hj₈, hs₈, hf₈⟩ =>
    ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) (by omega)
  · rw [hfl₈, hJi']
  · rw [hj₈, hj₇, hJi']
  · rw [hf₈ y hyj hys, hy₇, hJi']
  · rw [hJi']; obtain ⟨ql', h1, h2, h3⟩ := hq₇; exact ⟨ql', h1, h2, by rw [hf₈ q hqj hqs, h3]⟩
  · rw [hJi']; obtain ⟨rl', h1, h2, h3⟩ := hx₇; exact ⟨rl', h1, h2, by rw [hf₈ x hxj hxs, h3]⟩
  · rw [hs₈, hs₇]
  · rw [hf₈ t htj hts, ht₇]
  · intro k hkx hky hkq hkj hks hkt
    rw [hf₈ k hkj hks, hF₇ k hkx hky hkq hkj hks hkt]

/-! ### Division, assembled -/

/-- Binary long division, core: with `a` on `x` and `d ≥ 1` on `y`, replaces
`a` on `x` by `a % d` and pushes `a / d` on `q`; `y` (holding `d`) is left as
found; scratch `j` (the shift counter), `s`, `t` are restored.
Phase (i): `j := 0`, `cmp := compare d a`; while `d·2^j ≤ a`: double `y`,
`j := j + 1`, recompare.  Phase (ii): `q := 0`; while `j ≠ 0`: `dmDownBody`.
Then drop the zero left on `j`. -/
def divmodCore (x y q j s t : K) : Frag :=
  (pushNum j 0).seq ((dup y t s).seq ((dup x s t).seq ((cmpFrag t s).seq
    ((Frag.loop (fun v => !decide (v.cmp = .gt)) (dmUpBody x y j s t)).seq
      ((Frag.pushSym q .comma).seq ((isZero j s).seq
        ((Frag.loop (fun v => !v.flag) (dmDownBody x y q j s t)).seq (dropNum j))))))))

/-- `divmodCore` followed by dropping `d` from `y`: consumes `a` from `x` and
`d` from `y`, pushes `a % d` on `x` and `a / d` on `q`; `j`, `s`, `t` scratch. -/
def divmod (x y q j s t : K) : Frag := (divmodCore x y q j s t).seq (dropNum y)

/-- `q := x / y`; the remainder is dropped. -/
def divFrag (x y q j s t : K) : Frag := (divmod x y q j s t).seq (dropNum x)

/-- `x := x % y`; the quotient is dropped (`q` is scratch, restored). -/
def modFrag (x y q j s t : K) : Frag := (divmod x y q j s t).seq (dropNum q)

theorem divmodCore_runs {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (xs ds : List Bool) (hd : 1 ≤ toNat ds) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ds ++ .comma :: yr) :
    (divmodCore x y q j s t).Runs v S (fun _ S' =>
        (∃ rl, rl.length ≤ xs.length + ds.length ∧ toNat rl = toNat xs % toNat ds ∧
          S' x = bits rl ++ .comma :: xr) ∧
        S' y = S y ∧
        (∃ ql, ql.length ≤ xs.length ∧ toNat ql = toNat xs / toNat ds ∧
          S' q = bits ql ++ .comma :: S q) ∧
        S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      (xs.length * (23 * (xs.length + ds.length) + 60) + 7 * (xs.length + ds.length) + 26) := by
  have hyx := hxy.symm
  have hqx := hxq.symm
  have hqy := hyq.symm
  have hjx := hxj.symm
  have hjy := hyj.symm
  have hjq := hqj.symm
  have hsx := hxs.symm
  have hsy := hys.symm
  have hsq := hqs.symm
  have hsj := hjs.symm
  have htx := hxt.symm
  have hty := hyt.symm
  have htq := hqt.symm
  have htj := hjt.symm
  have hts := hst.symm
  set N := xs.length + ds.length with hN
  set J := divSteps (toNat xs) (toNat ds) hd with hJdef
  have hJ : J ≤ xs.length := divSteps_le _ _ hd (toNat_lt_two_pow xs)
  have hJspec : toNat xs < 2 ^ J * toNat ds := divSteps_spec (toNat xs) (toNat ds) hd
  have hJmin : ∀ i < J, 2 ^ i * toNat ds ≤ toNat xs := fun i hi => divSteps_min _ _ hd hi
  have hlogJ : Nat.log 2 J ≤ N := (Nat.log_le_self 2 _).trans (by omega)
  have h0 : Nat.log 2 0 = 0 := Nat.log_zero_right 2
  set TU := J * (7 * N + 18 + 1) + 1 with hTU
  set TD := J * (16 * N + 40 + 1) + 1 with hTD
  have hTU' : TU ≤ xs.length * (7 * N + 19) + 1 := by
    rw [hTU]; exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hJ) _
  have hTD' : TD ≤ xs.length * (16 * N + 41) + 1 := by
    rw [hTD]; exact Nat.add_le_add_right (Nat.mul_le_mul_right _ hJ) _
  have hsum : xs.length * (7 * N + 19) + xs.length * (16 * N + 41) = xs.length * (23 * N + 60) := by ring
  -- stage 1: `j := 0`
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TU + TD + 7 * N + 21) (pushNum_runs j 0 v S)
    fun v₁ S₁ ⟨hv₁, hj₁, hf₁⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₁]
  -- stage 2: copy `d` to `t`
  have hy₁ : S₁ y = bits ds ++ .comma :: yr := by rw [hf₁ y hyj, hSy]
  have h2 := dup_runs hyt hys hts ds yr v S₁ hy₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TU + TD + 5 * N + 16) h2
    fun v₂ S₂ ⟨hy₂, ht₂, hs₂, hf₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: copy `a` to `s`
  have hx₂ : S₂ x = bits xs ++ .comma :: xr := by rw [hf₂ x hxy hxt hxs, hf₁ x hxj, hSx]
  have h3 := dup_runs hxs hxt hst xs xr v₂ S₂ hx₂
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TU + TD + 3 * N + 11) h3
    fun v₃ S₃ ⟨hx₃, hs₃, ht₃, hf₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 4: `cmp := compare d a`
  have ht₃' : S₃ t = bits ds ++ .comma :: S t := by rw [ht₃, ht₂, hf₁ t htj]
  have hs₃' : S₃ s = bits xs ++ .comma :: S s := by rw [hs₃, hs₂, hf₁ s hsj]
  have h4 := cmpFrag_runs hts ds xs (S t) (S s) v₃ S₃ ht₃' hs₃'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TU + TD + 2 * N + 9) h4
    fun v₄ S₄ ⟨hc₄, ht₄, hs₄, hf₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 5: the shift-up loop
  have hj₄ : S₄ j = encodeNatΓ' 0 ++ .comma :: S j := by
    rw [hf₄ j hjt hjs, hf₃ j hjx hjs hjt, hf₂ j hjy hjt hjs, hj₁]
  have hy₄ : S₄ y = bits ds ++ .comma :: yr := by
    rw [hf₄ y hyt hys, hf₃ y hyx hys hyt, hy₂, hy₁]
  have hx₄ : S₄ x = bits xs ++ .comma :: xr := by rw [hf₄ x hxt hxs, hx₃, hx₂]
  have hF₄ : ∀ k, k ≠ x → k ≠ y → k ≠ j → k ≠ s → k ≠ t → S₄ k = S k :=
    fun k hkx hky hkj hks hkt => by
      rw [hf₄ k hkt hks, hf₃ k hkx hks hkt, hf₂ k hky hkt hks, hf₁ k hkj]
  have hup := Frag.loop_runs (c := fun v => !decide (v.cmp = .gt)) (B := dmUpBody x y j s t)
    (DmUpInv x y j s t xs ds J xr yr (S j) (S s) (S t) S) J (7 * N + 18) (v := v₄) (S := S₄)
    ⟨Nat.zero_le _, by rw [hc₄]; simp, hj₄, by simpa using hy₄, hx₄, hs₄, ht₄, hF₄⟩
    (fun i hi u T ⟨_, hc, _⟩ => by
      have := hJmin i hi
      rw [hc]; simp [compare_gt_iff_gt]; omega)
    (fun u T ⟨_, hc, _⟩ => by rw [hc]; simp [compare_gt_iff_gt]; exact hJspec)
    (fun i hi u T hI => dmUpBody_runs hxy hxj hxs hxt hyj hys hyt hjs hjt hst xs ds J hJ
      xr yr (S j) (S s) (S t) S i hi u T hI)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TD + 2 * N + 9) hup
    fun v₅ S₅ ⟨⟨_, _, hj₅, hy₅, hx₅, hs₅, ht₅, hF₅⟩, _⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 6: `q := 0`
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TD + 2 * N + 8) (Frag.pushSym_runs q .comma v₅ S₅)
    fun v₆ S₆ ⟨_, hS₆⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 7: `flag := (j = 0)`
  have hj₆ : S₆ j = encodeNatΓ' J ++ .comma :: S j := by rw [hS₆, Function.update_of_ne hjq, hj₅]
  have h7 := isZero_correct hjs J (S j) v₆ S₆ hj₆
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TD + 1) h7
    fun v₇ S₇ ⟨hfl₇, _, hj₇, hs₇, hf₇⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 8: the shift-down loop
  have hdown := Frag.loop_runs (c := fun v => !v.flag) (B := dmDownBody x y q j s t)
    (DmDownInv x y q j s t xs ds J xr yr (S q) (S j) (S s) (S t) S) J (16 * N + 40)
    (v := v₇) (S := S₇)
    ⟨Nat.zero_le _, by rw [hfl₇]; simp, by rw [hj₇, hj₆]; simp,
      by rw [hf₇ y hyj hys, hS₆, Function.update_of_ne hyq, hy₅]; simp,
      ⟨[], rfl, by simp only [toNat, Nat.sub_zero]; exact (Nat.div_eq_of_lt hJspec).symm,
        by rw [hf₇ q hqj hqs, hS₆]; simp [hF₅ q hqx hqy hqj hqs hqt]⟩,
      ⟨xs, by omega, by simp only [Nat.sub_zero]; exact (Nat.mod_eq_of_lt hJspec).symm,
        by rw [hf₇ x hxj hxs, hS₆, Function.update_of_ne hxq, hx₅]⟩,
      by rw [hs₇, hS₆, Function.update_of_ne hsq, hs₅],
      by rw [hf₇ t htj hts, hS₆, Function.update_of_ne htq, ht₅],
      fun k hkx hky hkq hkj hks hkt => by
        rw [hf₇ k hkj hks, hS₆, Function.update_of_ne hkq, hF₅ k hkx hky hkj hks hkt]⟩
    (fun i hi u T ⟨_, hfl, _⟩ => by rw [hfl]; simp; omega)
    (fun u T ⟨_, hfl, _⟩ => by rw [hfl]; simp)
    (fun i hi u T hI => dmDownBody_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
      xs ds hd J hJ xr yr (S q) (S j) (S s) (S t) S i hi u T hI)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) hdown
    fun v₈ S₈ ⟨⟨_, _, hj₈, hy₈, hq₈, hx₈, hs₈, ht₈, hF₈⟩, _⟩ => ?_) (fun _ _ h => h) le_rfl
  -- stage 9: drop the zero on `j`
  have hj₈' : S₈ j = bits [] ++ .comma :: S j := by rw [hj₈]; simp
  have h9 := dropNum_runs [] (S j) v₈ S₈ hj₈'
  refine Frag.runs_mono h9 (fun v₉ S₉ ⟨_, _, _, hj₉, hf₉⟩ => ⟨?_, ?_, ?_, hj₉, ?_, ?_, ?_⟩) (by simp)
  · obtain ⟨rl, h1, h2, h3⟩ := hx₈
    exact ⟨rl, h1, by rw [h2]; simp, by rw [hf₉ x hxj, h3]⟩
  · rw [hf₉ y hyj, hy₈, hSy]; simp
  · obtain ⟨ql, h1, h2, h3⟩ := hq₈
    exact ⟨ql, by omega, by rw [h2]; simp, by rw [hf₉ q hqj, h3]⟩
  · rw [hf₉ s hsj, hs₈]
  · rw [hf₉ t htj, ht₈]
  · intro k hkx hky hkq hkj hks hkt
    rw [hf₉ k hkj, hF₈ k hkx hky hkq hkj hks hkt]

theorem divmod_runs {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (xs ds : List Bool) (hd : 1 ≤ toNat ds) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ds ++ .comma :: yr) :
    (divmod x y q j s t).Runs v S (fun _ S' =>
        (∃ rl, rl.length ≤ xs.length + ds.length ∧ toNat rl = toNat xs % toNat ds ∧
          S' x = bits rl ++ .comma :: xr) ∧
        S' y = yr ∧
        (∃ ql, ql.length ≤ xs.length ∧ toNat ql = toNat xs / toNat ds ∧
          S' q = bits ql ++ .comma :: S q) ∧
        S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      (xs.length * (23 * (xs.length + ds.length) + 60) + 8 * (xs.length + ds.length) + 27) := by
  have h1 := divmodCore_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst xs ds hd
    xr yr v S hSx hSy
  refine Frag.runs_mono (Frag.seq_runs (t₂ := ds.length + 1) h1
    fun v₁ S₁ ⟨hx₁, hy₁, hq₁, hj₁, hs₁, ht₁, hf₁⟩ => ?_) (fun _ _ h => h) (by omega)
  have h2 := dropNum_runs ds yr v₁ S₁ (by rw [hy₁, hSy])
  refine Frag.runs_mono h2 (fun v₂ S₂ ⟨_, _, _, hy₂, hf₂⟩ => ⟨?_, hy₂, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
  · obtain ⟨rl, h1, h2, h3⟩ := hx₁; exact ⟨rl, h1, h2, by rw [hf₂ x hxy, h3]⟩
  · obtain ⟨ql, h1, h2, h3⟩ := hq₁; exact ⟨ql, h1, h2, by rw [hf₂ q hyq.symm, h3]⟩
  · rw [hf₂ j hyj.symm, hj₁]
  · rw [hf₂ s hys.symm, hs₁]
  · rw [hf₂ t hyt.symm, ht₁]
  · intro k hkx hky hkq hkj hks hkt
    rw [hf₂ k hky, hf₁ k hkx hky hkq hkj hks hkt]

theorem divFrag_runs {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (xs ds : List Bool) (hd : 1 ≤ toNat ds) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ds ++ .comma :: yr) :
    (divFrag x y q j s t).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧
        (∃ ql, ql.length ≤ xs.length ∧ toNat ql = toNat xs / toNat ds ∧
          S' q = bits ql ++ .comma :: S q) ∧
        S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      (xs.length * (23 * (xs.length + ds.length) + 60) + 9 * (xs.length + ds.length) + 28) := by
  have h1 := divmod_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst xs ds hd
    xr yr v S hSx hSy
  refine Frag.runs_mono (Frag.seq_runs (t₂ := xs.length + ds.length + 1) h1
    fun v₁ S₁ ⟨⟨rl, hrl, _, hx₁⟩, hy₁, hq₁, hj₁, hs₁, ht₁, hf₁⟩ => ?_) (fun _ _ h => h) (by omega)
  have h2 := dropNum_runs rl xr v₁ S₁ hx₁
  refine Frag.runs_mono h2 (fun v₂ S₂ ⟨_, _, _, hx₂, hf₂⟩ => ⟨hx₂, ?_, ?_, ?_, ?_, ?_, ?_⟩) (by omega)
  · rw [hf₂ y hxy.symm, hy₁]
  · obtain ⟨ql, h1, h2, h3⟩ := hq₁; exact ⟨ql, h1, h2, by rw [hf₂ q hxq.symm, h3]⟩
  · rw [hf₂ j hxj.symm, hj₁]
  · rw [hf₂ s hxs.symm, hs₁]
  · rw [hf₂ t hxt.symm, ht₁]
  · intro k hkx hky hkq hkj hks hkt
    rw [hf₂ k hkx, hf₁ k hkx hky hkq hkj hks hkt]

theorem modFrag_runs {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (xs ds : List Bool) (hd : 1 ≤ toNat ds) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ds ++ .comma :: yr) :
    (modFrag x y q j s t).Runs v S (fun _ S' =>
        (∃ rl, rl.length ≤ xs.length + ds.length ∧ toNat rl = toNat xs % toNat ds ∧
          S' x = bits rl ++ .comma :: xr) ∧
        S' y = yr ∧ S' q = S q ∧ S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      (xs.length * (23 * (xs.length + ds.length) + 60) + 9 * (xs.length + ds.length) + 28) := by
  have h1 := divmod_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst xs ds hd
    xr yr v S hSx hSy
  refine Frag.runs_mono (Frag.seq_runs (t₂ := xs.length + 1) h1
    fun v₁ S₁ ⟨hx₁, hy₁, ⟨ql, hql, _, hq₁⟩, hj₁, hs₁, ht₁, hf₁⟩ => ?_) (fun _ _ h => h) (by omega)
  have h2 := dropNum_runs ql (S q) v₁ S₁ hq₁
  refine Frag.runs_mono h2 (fun v₂ S₂ ⟨_, _, _, hq₂, hf₂⟩ => ⟨?_, ?_, hq₂, ?_, ?_, ?_, ?_⟩) (by omega)
  · obtain ⟨rl, h1, h2, h3⟩ := hx₁; exact ⟨rl, h1, h2, by rw [hf₂ x hxq, h3]⟩
  · rw [hf₂ y hyq, hy₁]
  · rw [hf₂ j hqj.symm, hj₁]
  · rw [hf₂ s hqs.symm, hs₁]
  · rw [hf₂ t hqt.symm, ht₁]
  · intro k hkx hky hkq hkj hks hkt
    rw [hf₂ k hkq, hf₁ k hkx hky hkq hkj hks hkt]

/-! ### Division on naturals -/

/-- The common step-bound bookkeeping: bit lengths → `Nat.log` form. -/
theorem divBound_log (a d c : ℕ) :
    (Computability.encodeNat a).length *
        (23 * ((Computability.encodeNat a).length + (Computability.encodeNat d).length) + 60) +
      c * ((Computability.encodeNat a).length + (Computability.encodeNat d).length) + 28 ≤
    (Nat.log 2 a + 1) * (23 * (Nat.log 2 a + Nat.log 2 d + 2) + 60) +
      c * (Nat.log 2 a + Nat.log 2 d + 2) + 28 := by
  have ha := encodeNat_length_le a
  have hd := encodeNat_length_le d
  have h1 := Nat.mul_le_mul ha (show 23 * ((Computability.encodeNat a).length +
    (Computability.encodeNat d).length) + 60 ≤ 23 * (Nat.log 2 a + Nat.log 2 d + 2) + 60 by omega)
  have h2 := Nat.mul_le_mul_left c (show (Computability.encodeNat a).length +
    (Computability.encodeNat d).length ≤ Nat.log 2 a + Nat.log 2 d + 2 by omega)
  omega

/-- The common step-bound bookkeeping: bit lengths below `m` → `B m`. -/
theorem divBound_B {a d m c : ℕ} (hc : c ≤ 9) (ha : a < 2 ^ m) (hd : d < 2 ^ m) :
    (Computability.encodeNat a).length *
        (23 * ((Computability.encodeNat a).length + (Computability.encodeNat d).length) + 60) +
      c * ((Computability.encodeNat a).length + (Computability.encodeNat d).length) + 28 ≤ B m := by
  have ha := encodeNat_length_le_of_lt_pow ha
  have hd := encodeNat_length_le_of_lt_pow hd
  have h1 := Nat.mul_le_mul ha (show 23 * ((Computability.encodeNat a).length +
    (Computability.encodeNat d).length) + 60 ≤ 46 * m + 60 by omega)
  have h2 := Nat.mul_le_mul hc (show (Computability.encodeNat a).length +
    (Computability.encodeNat d).length ≤ 2 * m by omega)
  apply le_B_of_le_quad
  nlinarith

/-- Division with remainder on naturals (`1 ≤ d`): `a % d` replaces `a` on
`x`, `a / d` is pushed on `q`, `d` is consumed from `y`. -/
theorem divmod_correct {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (a d : ℕ) (hd : 1 ≤ d) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' d ++ .comma :: yr) :
    (divmod x y q j s t).Runs v S (fun _ S' =>
        (∃ l, toNat l = a % d ∧ S' x = bits l ++ .comma :: xr) ∧ S' y = yr ∧
        (∃ l, toNat l = a / d ∧ S' q = bits l ++ .comma :: S q) ∧
        S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      ((Nat.log 2 a + 1) * (23 * (Nat.log 2 a + Nat.log 2 d + 2) + 60) +
        8 * (Nat.log 2 a + Nat.log 2 d + 2) + 28) := by
  have h := divmod_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    (Computability.encodeNat a) (Computability.encodeNat d) (by rw [toNat_encodeNat]; exact hd)
    xr yr v S hSx hSy
  refine Frag.runs_mono h (fun _ S' ⟨⟨rl, _, hrv, hx⟩, hy, ⟨ql, _, hqv, hq⟩, hj, hs, ht, hf⟩ =>
    ⟨⟨rl, by rw [hrv, toNat_encodeNat, toNat_encodeNat], hx⟩, hy,
      ⟨ql, by rw [hqv, toNat_encodeNat, toNat_encodeNat], hq⟩, hj, hs, ht, hf⟩) ?_
  have := divBound_log a d 8
  omega

/-- `divmod` within budget for operands below `2 ^ m`. -/
theorem divmod_le_B {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (a d m : ℕ) (hd : 1 ≤ d) (ha : a < 2 ^ m) (hdm : d < 2 ^ m) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' d ++ .comma :: yr) :
    (divmod x y q j s t).Runs v S (fun _ S' =>
        (∃ l, toNat l = a % d ∧ S' x = bits l ++ .comma :: xr) ∧ S' y = yr ∧
        (∃ l, toNat l = a / d ∧ S' q = bits l ++ .comma :: S q) ∧
        S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      (B m) := by
  have h := divmod_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    (Computability.encodeNat a) (Computability.encodeNat d) (by rw [toNat_encodeNat]; exact hd)
    xr yr v S hSx hSy
  refine Frag.runs_mono h (fun _ S' ⟨⟨rl, _, hrv, hx⟩, hy, ⟨ql, _, hqv, hq⟩, hj, hs, ht, hf⟩ =>
    ⟨⟨rl, by rw [hrv, toNat_encodeNat, toNat_encodeNat], hx⟩, hy,
      ⟨ql, by rw [hqv, toNat_encodeNat, toNat_encodeNat], hq⟩, hj, hs, ht, hf⟩) ?_
  have := divBound_B (c := 8) (by norm_num) ha hdm
  omega

/-- `divFrag`: `a / d` is pushed on `q`; `a`, `d` are consumed. -/
theorem divFrag_correct {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (a d : ℕ) (hd : 1 ≤ d) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' d ++ .comma :: yr) :
    (divFrag x y q j s t).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ (∃ l, toNat l = a / d ∧ S' q = bits l ++ .comma :: S q) ∧
        S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      ((Nat.log 2 a + 1) * (23 * (Nat.log 2 a + Nat.log 2 d + 2) + 60) +
        9 * (Nat.log 2 a + Nat.log 2 d + 2) + 28) := by
  have h := divFrag_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    (Computability.encodeNat a) (Computability.encodeNat d) (by rw [toNat_encodeNat]; exact hd)
    xr yr v S hSx hSy
  refine Frag.runs_mono h (fun _ S' ⟨hx, hy, ⟨ql, _, hqv, hq⟩, hj, hs, ht, hf⟩ =>
    ⟨hx, hy, ⟨ql, by rw [hqv, toNat_encodeNat, toNat_encodeNat], hq⟩, hj, hs, ht, hf⟩) ?_
  exact divBound_log a d 9

/-- `divFrag` within budget for operands below `2 ^ m`. -/
theorem divFrag_le_B {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (a d m : ℕ) (hd : 1 ≤ d) (ha : a < 2 ^ m) (hdm : d < 2 ^ m) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' d ++ .comma :: yr) :
    (divFrag x y q j s t).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ (∃ l, toNat l = a / d ∧ S' q = bits l ++ .comma :: S q) ∧
        S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      (B m) := by
  have h := divFrag_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    (Computability.encodeNat a) (Computability.encodeNat d) (by rw [toNat_encodeNat]; exact hd)
    xr yr v S hSx hSy
  refine Frag.runs_mono h (fun _ S' ⟨hx, hy, ⟨ql, _, hqv, hq⟩, hj, hs, ht, hf⟩ =>
    ⟨hx, hy, ⟨ql, by rw [hqv, toNat_encodeNat, toNat_encodeNat], hq⟩, hj, hs, ht, hf⟩) ?_
  exact divBound_B (c := 9) le_rfl ha hdm

/-- `modFrag`: `a % d` replaces `a` on `x`; `d` is consumed; `q` is scratch. -/
theorem modFrag_correct {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (a d : ℕ) (hd : 1 ≤ d) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' d ++ .comma :: yr) :
    (modFrag x y q j s t).Runs v S (fun _ S' =>
        (∃ l, toNat l = a % d ∧ S' x = bits l ++ .comma :: xr) ∧ S' y = yr ∧
        S' q = S q ∧ S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      ((Nat.log 2 a + 1) * (23 * (Nat.log 2 a + Nat.log 2 d + 2) + 60) +
        9 * (Nat.log 2 a + Nat.log 2 d + 2) + 28) := by
  have h := modFrag_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    (Computability.encodeNat a) (Computability.encodeNat d) (by rw [toNat_encodeNat]; exact hd)
    xr yr v S hSx hSy
  refine Frag.runs_mono h (fun _ S' ⟨⟨rl, _, hrv, hx⟩, hy, hq, hj, hs, ht, hf⟩ =>
    ⟨⟨rl, by rw [hrv, toNat_encodeNat, toNat_encodeNat], hx⟩, hy, hq, hj, hs, ht, hf⟩) ?_
  exact divBound_log a d 9

/-- `modFrag` within budget for operands below `2 ^ m`. -/
theorem modFrag_le_B {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (a d m : ℕ) (hd : 1 ≤ d) (ha : a < 2 ^ m) (hdm : d < 2 ^ m) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' d ++ .comma :: yr) :
    (modFrag x y q j s t).Runs v S (fun _ S' =>
        (∃ l, toNat l = a % d ∧ S' x = bits l ++ .comma :: xr) ∧ S' y = yr ∧
        S' q = S q ∧ S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      (B m) := by
  have h := modFrag_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    (Computability.encodeNat a) (Computability.encodeNat d) (by rw [toNat_encodeNat]; exact hd)
    xr yr v S hSx hSy
  refine Frag.runs_mono h (fun _ S' ⟨⟨rl, _, hrv, hx⟩, hy, hq, hj, hs, ht, hf⟩ =>
    ⟨⟨rl, by rw [hrv, toNat_encodeNat, toNat_encodeNat], hx⟩, hy, hq, hj, hs, ht, hf⟩) ?_
  exact divBound_B (c := 9) le_rfl ha hdm

end Carmichael.TM
