import Carmichael.TM.Arith
import Carmichael.TM.Cost

/-!
# Route T primitive fragments

Stack-level primitives on terminated numbers (`bits l ++ Γ'.comma :: rest`,
LSB on top), each with a `Runs` triple giving the exact stack contents and an
explicit step bound, plus ℕ-level corollaries for `encodeNatΓ'` inputs and
`B`-form bounds (`steps ≤ B b` for operands below `2 ^ b`).

* `Frag.ite c F G`: one test step on the internal state, then `F` or `G`.
* `Frag.skip`: one step, no effect.
* `pushNum k c`: push the terminated constant `c` on `k`.
* `dropNum x`: pop the top number of `x` with its terminator.
* `clear k`: pop everything from `k`.
* `move2Num src d₁ d₂`: pop the top number of `src` onto both `d₁` and `d₂`, reversed.
* `dup x y s`: copy the top number of `x` onto `y` (scratch `s`, restored).
* `isZero x s`: set `flag := decide (top number of x = 0)`, `x` restored (scratch `s`).
* `incr y s`: `y := y + 1` in place (scratch `s`).
* `predNum x s`: `x := x - 1` in place for `x ≥ 1` (scratch `s`).
* `bitlen x y s s'`: push `Nat.log 2 a + 1` (`0` for `a = 0`) on `y`, `x` restored.
* `pow2 x y s s'`: consume `e` from `x`, push `2 ^ e` on `y`.
-/

namespace Carmichael.TM

open Turing Turing.TM2 Turing.TM2.Stmt Computability

/-! ### Bit-list facts -/

theorem toNat_replicate_false (n : ℕ) : toNat (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, toNat, ih]

theorem toNat_append_replicate_false (l : List Bool) (n : ℕ) :
    toNat (l ++ List.replicate n false) = toNat l := by
  induction l with
  | nil => simp [toNat_replicate_false, toNat]
  | cons b l ih => simp [toNat, ih]

theorem toNat_replicate_false_append (n : ℕ) (l : List Bool) :
    toNat (List.replicate n false ++ l) = 2 ^ n * toNat l := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, toNat, ih, pow_succ]; ring

theorem toNat_lt_two_pow (l : List Bool) : toNat l < 2 ^ l.length := by
  induction l with
  | nil => simp [toNat]
  | cons b l ih => cases b <;> simp [toNat, pow_succ] <;> omega

theorem toNat_eq_zero_iff (l : List Bool) : toNat l = 0 ↔ l.all (fun b => !b) = true := by
  induction l with
  | nil => simp [toNat]
  | cons b l ih => cases b <;> simp [toNat, ih]

@[simp] theorem encodeNatΓ'_zero : encodeNatΓ' 0 = [] := rfl

theorem decide_toNat_eq_zero (l : List Bool) : decide (toNat l = 0) = l.all (fun b => !b) := by
  simp only [toNat_eq_zero_iff, Bool.decide_eq_true]

/-- Length of Mathlib's encoding on inputs below `2 ^ b`. -/
theorem encodeNat_length_le_of_lt_pow {a b : ℕ} (h : a < 2 ^ b) :
    (Computability.encodeNat a).length ≤ b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [Computability.encodeNat, encodeNum]
  · have := encodeNat_length_le a
    have := (Nat.log_lt_iff_lt_pow one_lt_two ha.ne').mpr h
    omega

/-! ### Branching and no-op -/

namespace Frag

/-- `if c(state) then F else G`: one test step, then the chosen branch, both
exiting to the ambient exit. -/
def ite (c : St → Bool) (F G : Frag) : Frag where
  Λf := Option (F.Λf ⊕ G.Λf)
  entry := none
  code ι e
    | none => branch c (goto fun _ => ι (some (Sum.inl F.entry))) (goto fun _ => ι (some (Sum.inr G.entry)))
    | some (Sum.inl l) => F.code (ι ∘ some ∘ Sum.inl) e l
    | some (Sum.inr l) => G.code (ι ∘ some ∘ Sum.inr) e l

theorem ite_installed_left {c : St → Bool} {F G : Frag} {Λ : Type} {M : Λ → Stmt' Λ} {ι e}
    (h : (ite c F G).Installed M ι e) : F.Installed M (ι ∘ some ∘ Sum.inl) e :=
  fun l => h (some (Sum.inl l))

theorem ite_installed_right {c : St → Bool} {F G : Frag} {Λ : Type} {M : Λ → Stmt' Λ} {ι e}
    (h : (ite c F G).Installed M ι e) : G.Installed M (ι ∘ some ∘ Sum.inr) e :=
  fun l => h (some (Sum.inr l))

theorem ite_runs_true {c : St → Bool} {F G : Frag} {v S Q t} (hc : c v = true)
    (hF : F.Runs v S Q t) : (ite c F G).Runs v S Q (t + 1) := by
  constructor
  intro Λ M ι e hI
  obtain ⟨n, hn, v', S', hr, hQ⟩ := hF.run M _ _ (ite_installed_left hI)
  refine ⟨n + 1, by omega, v', S', runsTo_succ ?_ hr, hQ⟩
  tm_step none [ite, hc, Function.comp]

theorem ite_runs_false {c : St → Bool} {F G : Frag} {v S Q t} (hc : c v = false)
    (hG : G.Runs v S Q t) : (ite c F G).Runs v S Q (t + 1) := by
  constructor
  intro Λ M ι e hI
  obtain ⟨n, hn, v', S', hr, hQ⟩ := hG.run M _ _ (ite_installed_right hI)
  refine ⟨n + 1, by omega, v', S', runsTo_succ ?_ hr, hQ⟩
  tm_step none [ite, hc, Function.comp]

/-- Branch rule: each branch is only needed under its test outcome. -/
theorem ite_runs {c : St → Bool} {F G : Frag} {v S Q t}
    (hF : c v = true → F.Runs v S Q t) (hG : c v = false → G.Runs v S Q t) :
    (ite c F G).Runs v S Q (t + 1) := by
  cases hc : c v
  · exact ite_runs_false hc (hG hc)
  · exact ite_runs_true hc (hF hc)

/-- One step, no effect. -/
def skip : Frag := load' id

theorem skip_runs (v : St) (S : Stacks) : skip.Runs v S (fun v' S' => v' = v ∧ S' = S) 1 :=
  load'_runs id v S

end Frag

/-! ### Pushing a constant -/

/-- Push the symbols `l` then a `comma` on `k`, so that `k` becomes `l ++ comma :: S k`
(`l.head` on top): one label per symbol, chained by `seq`. -/
def pushTerm (k : K) : List Γ' → Frag
  | [] => Frag.pushSym k .comma
  | s :: l => (pushTerm k l).seq (Frag.pushSym k s)

theorem pushTerm_runs (k : K) (l : List Γ') (v : St) (S : Stacks) :
    (pushTerm k l).Runs v S (fun v' S' => v' = v ∧ S' = Function.update S k (l ++ .comma :: S k))
      (l.length + 1) := by
  induction l generalizing S with
  | nil => simpa [pushTerm] using Frag.pushSym_runs k .comma v S
  | cons s l ih =>
    rw [pushTerm]
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) (ih S) fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_)
      (fun _ _ h => h) (by simp)
    subst hS₁; rw [hv₁]
    refine Frag.runs_mono (Frag.pushSym_runs k s v _) (fun v₂ S₂ ⟨hv₂, hS₂⟩ => ⟨hv₂, ?_⟩) le_rfl
    rw [hS₂]; funext j
    by_cases hj : j = k
    · subst hj; simp
    · simp [Function.update_of_ne hj]

/-- Push the constant `c` as a terminated number on `k`. -/
def pushNum (k : K) (c : ℕ) : Frag := pushTerm k (encodeNatΓ' c)

theorem pushNum_runs (k : K) (c : ℕ) (v : St) (S : Stacks) :
    (pushNum k c).Runs v S
      (fun v' S' => v' = v ∧ S' k = encodeNatΓ' c ++ .comma :: S k ∧ ∀ j, j ≠ k → S' j = S j)
      (Nat.log 2 c + 2) := by
  refine Frag.runs_mono (pushTerm_runs k (encodeNatΓ' c) v S)
    (fun v' S' ⟨hv, hS⟩ => ⟨hv, by rw [hS]; simp, fun j hj => by rw [hS]; simp [Function.update_of_ne hj]⟩) ?_
  have := encodeNatΓ'_length_le c
  omega

theorem pushNum_le_B (k : K) (c : ℕ) (b : ℕ) (hc : c < 2 ^ b) (v : St) (S : Stacks) :
    (pushNum k c).Runs v S
      (fun v' S' => v' = v ∧ S' k = encodeNatΓ' c ++ .comma :: S k ∧ ∀ j, j ≠ k → S' j = S j)
      (B b) := by
  refine Frag.runs_mono (pushTerm_runs k (encodeNatΓ' c) v S)
    (fun v' S' ⟨hv, hS⟩ => ⟨hv, by rw [hS]; simp, fun j hj => by rw [hS]; simp [Function.update_of_ne hj]⟩) ?_
  have := encodeNat_length_le_of_lt_pow hc
  apply le_B_of_le_linear
  simp only [encodeNatΓ'_eq, bits_length]
  omega

/-! ### Dropping a number, clearing a stack -/

/-- Pop from `x`: a bit loops, the terminator (or empty stack) exits. -/
def dropBody {Λ : Type} (x : K) (self e : Λ) : Stmt' Λ :=
  pop x readA (branch (fun v => v.ra.isSome) (goto fun _ => self) (goto fun _ => e))

/-- Pop the top number of `x` including its terminator. -/
def dropNum (x : K) : Frag where
  Λf := Unit
  entry := ()
  code ι e _ := dropBody x (ι ()) e

theorem dropNum_loop {x : K} {Λ : Type} {M : Λ → Stmt' Λ} {ι : Unit → Λ} {e : Λ}
    (hI : (dropNum x).Installed M ι e) {xr : List Γ'} (l : List Bool) :
    ∀ (v : St) (S : Stacks), S x = bits l ++ .comma :: xr →
    ∃ n, n ≤ l.length + 1 ∧ ∃ v' S',
      RunsTo M n ⟨some (ι ()), v, S⟩ ⟨some e, v', S'⟩ ∧
      v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
      S' x = xr ∧ ∀ k, k ≠ x → S' k = S k := by
  induction l with
  | nil =>
    intro v S hS
    refine ⟨1, by simp, { v with ra := none, da := true }, Function.update S x xr,
      runsTo_succ ?_ (runsTo_zero M _), rfl, rfl, rfl, by simp,
      fun k hk => by simp [Function.update_of_ne hk]⟩
    tm_step () [dropNum, dropBody, hS]
  | cons b l ih =>
    intro v S hS
    obtain ⟨n, hn, v', S', hr, hfl, hcmp, hcar, hx', hf'⟩ :=
      ih { v with ra := some b } (Function.update S x (bits l ++ .comma :: xr)) (by simp)
    refine ⟨n + 1, ?_, v', S', runsTo_succ ?_ hr, hfl, hcmp, hcar, hx', ?_⟩
    · simp only [List.length_cons] at hn ⊢; omega
    · tm_step () [dropNum, dropBody, hS]
    · intro k hk; rw [hf' k hk]; simp [Function.update_of_ne hk]

/-- `dropNum`: pops the top number of `x` (with terminator); `flag`, `cmp`,
`carry` preserved; other stacks untouched. -/
theorem dropNum_runs {x : K} (l : List Bool) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = bits l ++ .comma :: xr) :
    (dropNum x).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' x = xr ∧ ∀ k, k ≠ x → S' k = S k)
      (l.length + 1) := by
  constructor
  intro Λ M ι e hI
  exact dropNum_loop hI l v S hS

theorem dropNum_correct {x : K} (a : ℕ) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encodeNatΓ' a ++ .comma :: xr) :
    (dropNum x).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' x = xr ∧ ∀ k, k ≠ x → S' k = S k)
      (Nat.log 2 a + 2) := by
  refine Frag.runs_mono (dropNum_runs (Computability.encodeNat a) xr v S hS) (fun _ _ h => h) ?_
  have := encodeNat_length_le a
  omega

theorem dropNum_le_B {x : K} (a b : ℕ) (ha : a < 2 ^ b) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encodeNatΓ' a ++ .comma :: xr) :
    (dropNum x).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' x = xr ∧ ∀ k, k ≠ x → S' k = S k)
      (B b) := by
  refine Frag.runs_mono (dropNum_runs (Computability.encodeNat a) xr v S hS) (fun _ _ h => h) ?_
  have := encodeNat_length_le_of_lt_pow ha
  exact le_B_of_le_linear (by omega)

/-- Pop-handler recording whether the stack was nonempty in `da` (`da = true`
iff the stack was empty). -/
def readEmpty (v : St) (o : Option Γ') : St := { v with da := o.isNone }

@[simp] theorem readEmpty_some (v : St) (s : Γ') : readEmpty v (some s) = { v with da := false } := rfl
@[simp] theorem readEmpty_none (v : St) : readEmpty v none = { v with da := true } := rfl

/-- Pop from `k`; loop while the stack was nonempty. -/
def clearBody {Λ : Type} (k : K) (self e : Λ) : Stmt' Λ :=
  pop k readEmpty (branch (fun v => v.da) (goto fun _ => e) (goto fun _ => self))

/-- Pop everything from `k` until it is empty. -/
def clear (k : K) : Frag where
  Λf := Unit
  entry := ()
  code ι e _ := clearBody k (ι ()) e

theorem clear_loop {x : K} {Λ : Type} {M : Λ → Stmt' Λ} {ι : Unit → Λ} {e : Λ}
    (hI : (clear x).Installed M ι e) (l : List Γ') :
    ∀ (v : St) (S : Stacks), S x = l →
    ∃ n, n ≤ l.length + 1 ∧ ∃ v' S',
      RunsTo M n ⟨some (ι ()), v, S⟩ ⟨some e, v', S'⟩ ∧
      v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
      S' x = [] ∧ ∀ k, k ≠ x → S' k = S k := by
  induction l with
  | nil =>
    intro v S hS
    refine ⟨1, by simp, { v with da := true }, Function.update S x [],
      runsTo_succ ?_ (runsTo_zero M _), rfl, rfl, rfl, by simp,
      fun k hk => by simp [Function.update_of_ne hk]⟩
    tm_step () [clear, clearBody, hS]
  | cons s l ih =>
    intro v S hS
    obtain ⟨n, hn, v', S', hr, hfl, hcmp, hcar, hx', hf'⟩ :=
      ih { v with da := false } (Function.update S x l) (by simp)
    refine ⟨n + 1, ?_, v', S', runsTo_succ ?_ hr, hfl, hcmp, hcar, hx', ?_⟩
    · simp only [List.length_cons] at hn ⊢; omega
    · tm_step () [clear, clearBody, hS]
    · intro k hk; rw [hf' k hk]; simp [Function.update_of_ne hk]

/-- `clear`: empties `k`; `flag`, `cmp`, `carry` preserved; other stacks untouched. -/
theorem clear_runs (k : K) (v : St) (S : Stacks) :
    (clear k).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' k = [] ∧ ∀ j, j ≠ k → S' j = S j)
      ((S k).length + 1) := by
  constructor
  intro Λ M ι e hI
  exact clear_loop hI (S k) v S rfl

/-! ### The mover, with state preservation -/

/-- `moveNum_loop` strengthened with the registers it leaves alone
(`flag`, `cmp`, `carry`). -/
theorem moveNum_loop' {src dst : K} (hsd : src ≠ dst)
    {Λ : Type} {M : Λ → Stmt' Λ} {ι : Unit → Λ} {e : Λ} (hI : (moveNum src dst).Installed M ι e)
    {sr : List Γ'} {S₀ : Stacks} (l : List Bool) :
    ∀ (v : St) (S : Stacks) (dr : List Γ'), S src = bits l ++ .comma :: sr → S dst = dr →
      (∀ k, k ≠ src → k ≠ dst → S k = S₀ k) →
    ∃ n, n ≤ l.length + 1 ∧ ∃ v' S',
      RunsTo M n ⟨some (ι ()), v, S⟩ ⟨some e, v', S'⟩ ∧
      v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
      S' src = sr ∧ S' dst = (bits l).reverse ++ dr ∧ ∀ k, k ≠ src → k ≠ dst → S' k = S₀ k := by
  have hds := hsd.symm
  induction l with
  | nil =>
    intro v S dr hS hD hF
    refine ⟨1, by simp, { v with ra := none, da := true }, Function.update S src sr,
      runsTo_succ ?_ (runsTo_zero M _), rfl, rfl, rfl, by simp, by simp [Function.update_of_ne hds, hD],
      fun k hks hkd => by simp [Function.update_of_ne hks, hF k hks hkd]⟩
    tm_step () [moveNum, moveBody, hS]
  | cons b l ih =>
    intro v S dr hS hD hF
    obtain ⟨n, hn, v', S', hr, hfl, hcmp, hcar, hs', hd', hf'⟩ :=
      ih { v with ra := some b }
        (Function.update (Function.update S src (bits l ++ .comma :: sr)) dst (.bit b :: dr))
        (.bit b :: dr) (by simp [Function.update_of_ne hsd]) (by simp)
        (fun k hks hkd => by
          simp [Function.update_of_ne hks, Function.update_of_ne hkd, hF k hks hkd])
    refine ⟨n + 1, ?_, v', S', runsTo_succ ?_ hr, hfl, hcmp, hcar, hs', ?_, hf'⟩
    · simp only [List.length_cons] at hn ⊢; omega
    · tm_step () [moveNum, moveBody, hS, hD, hsd, hds]
    · rw [hd']; simp

/-- `moveNum_runs` with `flag`, `cmp`, `carry` preserved. -/
theorem moveNum_runs' {src dst : K} (hsd : src ≠ dst) (l : List Bool) (sr : List Γ')
    (v : St) (S : Stacks) (hS : S src = bits l ++ .comma :: sr) :
    (moveNum src dst).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' src = sr ∧ S' dst = (bits l).reverse ++ S dst ∧ ∀ k, k ≠ src → k ≠ dst → S' k = S k)
      (l.length + 1) := by
  constructor
  intro Λ M ι e hI
  exact moveNum_loop' hsd hI (S₀ := S) l v S (S dst) hS rfl (fun _ _ _ => rfl)

/-! ### Copying a number -/

/-- Pop a symbol from `src`; a bit is pushed on both `d₁` and `d₂`, the
terminator (or empty stack) ends the fragment. -/
def move2Body {Λ : Type} (src d₁ d₂ : K) (self e : Λ) : Stmt' Λ :=
  pop src readA
    (branch (fun v => v.ra.isSome)
      (push d₁ (fun v => .bit (bitOf v.ra)) (push d₂ (fun v => .bit (bitOf v.ra)) (goto fun _ => self)))
      (goto fun _ => e))

/-- Move the top number of `src` onto both `d₁` and `d₂`, reversed, consuming the terminator. -/
def move2Num (src d₁ d₂ : K) : Frag where
  Λf := Unit
  entry := ()
  code ι e _ := move2Body src d₁ d₂ (ι ()) e

theorem move2Num_loop {src d₁ d₂ : K} (h₁ : src ≠ d₁) (h₂ : src ≠ d₂) (h₁₂ : d₁ ≠ d₂)
    {Λ : Type} {M : Λ → Stmt' Λ} {ι : Unit → Λ} {e : Λ} (hI : (move2Num src d₁ d₂).Installed M ι e)
    {sr : List Γ'} {S₀ : Stacks} (l : List Bool) :
    ∀ (v : St) (S : Stacks) (r₁ r₂ : List Γ'), S src = bits l ++ .comma :: sr → S d₁ = r₁ → S d₂ = r₂ →
      (∀ k, k ≠ src → k ≠ d₁ → k ≠ d₂ → S k = S₀ k) →
    ∃ n, n ≤ l.length + 1 ∧ ∃ v' S',
      RunsTo M n ⟨some (ι ()), v, S⟩ ⟨some e, v', S'⟩ ∧
      S' src = sr ∧ S' d₁ = (bits l).reverse ++ r₁ ∧ S' d₂ = (bits l).reverse ++ r₂ ∧
      ∀ k, k ≠ src → k ≠ d₁ → k ≠ d₂ → S' k = S₀ k := by
  have h₁' := h₁.symm
  have h₂' := h₂.symm
  have h₂₁ := h₁₂.symm
  induction l with
  | nil =>
    intro v S r₁ r₂ hS hD₁ hD₂ hF
    refine ⟨1, by simp, { v with ra := none, da := true }, Function.update S src sr,
      runsTo_succ ?_ (runsTo_zero M _), by simp, by simp [Function.update_of_ne h₁', hD₁],
      by simp [Function.update_of_ne h₂', hD₂],
      fun k hks hk₁ hk₂ => by simp [Function.update_of_ne hks, hF k hks hk₁ hk₂]⟩
    tm_step () [move2Num, move2Body, hS]
  | cons b l ih =>
    intro v S r₁ r₂ hS hD₁ hD₂ hF
    obtain ⟨n, hn, v', S', hr, hs', hd₁', hd₂', hf'⟩ :=
      ih { v with ra := some b }
        (Function.update (Function.update (Function.update S src (bits l ++ .comma :: sr))
          d₁ (.bit b :: r₁)) d₂ (.bit b :: r₂))
        (.bit b :: r₁) (.bit b :: r₂)
        (by simp [Function.update_of_ne h₁, Function.update_of_ne h₂])
        (by simp [Function.update_of_ne h₁₂]) (by simp)
        (fun k hks hk₁ hk₂ => by
          simp [Function.update_of_ne hks, Function.update_of_ne hk₁, Function.update_of_ne hk₂,
            hF k hks hk₁ hk₂])
    refine ⟨n + 1, ?_, v', S', runsTo_succ ?_ hr, hs', ?_, ?_, hf'⟩
    · simp only [List.length_cons] at hn ⊢; omega
    · tm_step () [move2Num, move2Body, hS, hD₁, hD₂, h₁, h₂, h₁', h₂', h₁₂, h₂₁]
    · rw [hd₁']; simp
    · rw [hd₂']; simp

theorem move2Num_runs {src d₁ d₂ : K} (h₁ : src ≠ d₁) (h₂ : src ≠ d₂) (h₁₂ : d₁ ≠ d₂)
    (l : List Bool) (sr : List Γ') (v : St) (S : Stacks) (hS : S src = bits l ++ .comma :: sr) :
    (move2Num src d₁ d₂).Runs v S (fun _ S' =>
        S' src = sr ∧ S' d₁ = (bits l).reverse ++ S d₁ ∧ S' d₂ = (bits l).reverse ++ S d₂ ∧
        ∀ k, k ≠ src → k ≠ d₁ → k ≠ d₂ → S' k = S k)
      (l.length + 1) := by
  constructor
  intro Λ M ι e hI
  exact move2Num_loop h₁ h₂ h₁₂ hI (S₀ := S) l v S (S d₁) (S d₂) hS rfl rfl (fun _ _ _ _ => rfl)

/-- Copy the top number of `x` (with terminator) onto `y`, leaving `x`
unchanged; scratch `s` is restored.  `push comma s ; moveNum x s ; push comma x ;
push comma y ; move2Num s x y`. -/
def dup (x y s : K) : Frag :=
  (Frag.pushSym s .comma).seq ((moveNum x s).seq
    ((Frag.pushSym x .comma).seq ((Frag.pushSym y .comma).seq (move2Num s x y))))

theorem dup_runs {x y s : K} (hxy : x ≠ y) (hxs : x ≠ s) (hys : y ≠ s)
    (l : List Bool) (xr : List Γ') (v : St) (S : Stacks) (hS : S x = bits l ++ .comma :: xr) :
    (dup x y s).Runs v S (fun _ S' =>
        S' x = S x ∧ S' y = bits l ++ .comma :: S y ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → S' k = S k)
      (2 * l.length + 5) := by
  have hsx := hxs.symm
  have hsy := hys.symm
  have hyx := hxy.symm
  -- stage 1: push comma on s
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * l.length + 4) (Frag.pushSym_runs s .comma v S)
    fun v₁ S₁ ⟨_, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₁
  -- stage 2: moveNum x s
  have h2 := moveNum_runs hxs l xr v₁ (Function.update S s (.comma :: S s))
    (by simp [Function.update_of_ne hxs, hS])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length + 3) h2 fun v₂ S₂ ⟨hx₂, hs₂, hf₂⟩ => ?_)
    (fun _ _ h => h) (by omega)
  -- stage 3: push comma on x
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length + 2) (Frag.pushSym_runs x .comma v₂ S₂)
    fun v₃ S₃ ⟨_, hS₃⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₃
  -- stage 4: push comma on y
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length + 1) (Frag.pushSym_runs y .comma v₃ _)
    fun v₄ S₄ ⟨_, hS₄⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₄
  -- stage 5: move2Num s x y
  have hs₄ : Function.update (Function.update S₂ x (.comma :: S₂ x)) y
      (.comma :: Function.update S₂ x (.comma :: S₂ x) y) s =
      bits l.reverse ++ .comma :: S s := by
    simp [Function.update_of_ne hsy, Function.update_of_ne hsx, hs₂]
  have h5 := move2Num_runs hsx hsy hxy l.reverse (S s) v₄ _ hs₄
  refine Frag.runs_mono h5 (fun v₅ S₅ ⟨hs₅, hx₅, hy₅, hf₅⟩ => ⟨?_, ?_, hs₅, ?_⟩) (by simp)
  · rw [hx₅]; simp [Function.update_of_ne hxy, hx₂, hS]
  · rw [hy₅]; simp [Function.update_of_ne hyx, hf₂ y hyx hys, Function.update_of_ne hys]
  · intro k hkx hky hks
    rw [hf₅ k hks hkx hky]
    simp [Function.update_of_ne hky, Function.update_of_ne hkx, hf₂ k hkx hks,
      Function.update_of_ne hks]

theorem dup_correct {x y s : K} (hxy : x ≠ y) (hxs : x ≠ s) (hys : y ≠ s)
    (a : ℕ) (xr : List Γ') (v : St) (S : Stacks) (hS : S x = encodeNatΓ' a ++ .comma :: xr) :
    (dup x y s).Runs v S (fun _ S' =>
        S' x = S x ∧ S' y = encodeNatΓ' a ++ .comma :: S y ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → S' k = S k)
      (2 * Nat.log 2 a + 7) := by
  refine Frag.runs_mono (dup_runs hxy hxs hys (Computability.encodeNat a) xr v S hS)
    (fun _ _ h => h) ?_
  have := encodeNat_length_le a
  omega

theorem dup_le_B {x y s : K} (hxy : x ≠ y) (hxs : x ≠ s) (hys : y ≠ s)
    (a b : ℕ) (ha : a < 2 ^ b) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encodeNatΓ' a ++ .comma :: xr) :
    (dup x y s).Runs v S (fun _ S' =>
        S' x = S x ∧ S' y = encodeNatΓ' a ++ .comma :: S y ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → S' k = S k)
      (B b) := by
  refine Frag.runs_mono (dup_runs hxy hxs hys (Computability.encodeNat a) xr v S hS)
    (fun _ _ h => h) ?_
  have := encodeNat_length_le_of_lt_pow ha
  exact le_B_of_le_linear (by omega)

/-! ### Canonical bit lists

A bit list is canonical when it has no trailing (high) zeros; canonical lists
are determined by their value, so a canonical output of value `a` is exactly
`Computability.encodeNat a`. -/

/-- No trailing (most significant) zero. -/
def Canon (l : List Bool) : Prop := l.getLast? ≠ some false

@[simp] theorem canon_nil : Canon [] := by simp [Canon]

theorem Canon.of_cons {b : Bool} {l : List Bool} (h : Canon (b :: l)) : Canon l := by
  cases l with
  | nil => simp
  | cons b' l => rw [Canon, List.getLast?_cons_cons] at h; exact h

theorem canon_cons_of_ne_nil {b : Bool} {l : List Bool} (hl : l ≠ []) (h : Canon l) :
    Canon (b :: l) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons b' l => rw [Canon, List.getLast?_cons_cons]; exact h

theorem canon_cons_true (l : List Bool) (h : Canon l) : Canon (true :: l) := by
  cases l with
  | nil => simp [Canon]
  | cons b' l => rw [Canon, List.getLast?_cons_cons]; exact h

theorem canon_replicate_true_append (n : ℕ) {l : List Bool} (h : Canon l) :
    Canon (List.replicate n true ++ l) := by
  induction n with
  | zero => simpa
  | succ n ih => rw [List.replicate_succ, List.cons_append]; exact canon_cons_true _ ih

theorem canon_replicate_false_append_true (n : ℕ) : Canon (List.replicate n false ++ [true]) := by
  simp [Canon, List.getLast?_append]

theorem Canon.eq_nil_of_toNat_eq_zero {l : List Bool} (h : Canon l) (h0 : toNat l = 0) : l = [] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b
    · have := ih h.of_cons (by simp [toNat] at h0; omega)
      subst this; simp [Canon] at h
    · simp [toNat] at h0

theorem Canon.unique {l l' : List Bool} (h : Canon l) (h' : Canon l') (he : toNat l = toNat l') :
    l = l' := by
  induction l generalizing l' with
  | nil => exact (h'.eq_nil_of_toNat_eq_zero (by simp [toNat] at he; omega)).symm
  | cons b l ih =>
    cases l' with
    | nil => exact h.eq_nil_of_toNat_eq_zero (by simpa [toNat] using he)
    | cons b' l' =>
      have hb : b = b' := by
        cases b <;> cases b' <;> simp only [toNat, Bool.toNat_false, Bool.toNat_true] at he <;>
          first | rfl | omega
      subst hb
      have : toNat l = toNat l' := by simp only [toNat] at he; omega
      rw [ih h.of_cons h'.of_cons this]

theorem encodePosNum_ne_nil (p : PosNum) : encodePosNum p ≠ [] := by
  cases p <;> simp [encodePosNum]

theorem canon_encodePosNum (p : PosNum) : Canon (encodePosNum p) := by
  induction p with
  | one => simp [Canon, encodePosNum]
  | bit0 p ih => exact canon_cons_of_ne_nil (encodePosNum_ne_nil p) ih
  | bit1 p ih => exact canon_cons_of_ne_nil (encodePosNum_ne_nil p) ih

theorem canon_encodeNat (n : ℕ) : Canon (Computability.encodeNat n) := by
  unfold Computability.encodeNat
  rcases (n : Num) with _ | p
  · simp [encodeNum]
  · exact canon_encodePosNum p

/-- A canonical list of value `a` is Mathlib's encoding of `a`. -/
theorem Canon.eq_encodeNat {l : List Bool} (h : Canon l) : l = Computability.encodeNat (toNat l) :=
  h.unique (canon_encodeNat _) (toNat_encodeNat _).symm

/-! ### Zero test -/

/-- The flag after scanning `l` starting from `f`: `f` and all bits zero. -/
def zeroBits : List Bool → Bool → Bool
  | [], f => f
  | b :: l, f => zeroBits l (f && !b)

theorem zeroBits_eq (l : List Bool) (f : Bool) : zeroBits l f = (f && l.all (fun b => !b)) := by
  induction l generalizing f with
  | nil => simp [zeroBits]
  | cons b l ih => simp [zeroBits, ih, Bool.and_assoc]

/-- Pop a symbol from `src`; a bit is pushed on `dst` and folded into `flag`
(`flag := flag && !bit`), the terminator ends the fragment. -/
def zeroScanBody {Λ : Type} (src dst : K) (self e : Λ) : Stmt' Λ :=
  pop src readA
    (branch (fun v => v.ra.isSome)
      (push dst (fun v => .bit (bitOf v.ra))
        (load (fun v => { v with flag := v.flag && !(bitOf v.ra) }) (goto fun _ => self)))
      (goto fun _ => e))

/-- Move the top number of `src` onto `dst` (reversed), clearing `flag` if any bit is set. -/
def zeroScan (src dst : K) : Frag where
  Λf := Unit
  entry := ()
  code ι e _ := zeroScanBody src dst (ι ()) e

theorem zeroScan_loop {src dst : K} (hsd : src ≠ dst)
    {Λ : Type} {M : Λ → Stmt' Λ} {ι : Unit → Λ} {e : Λ} (hI : (zeroScan src dst).Installed M ι e)
    {sr : List Γ'} {S₀ : Stacks} (l : List Bool) :
    ∀ (v : St) (S : Stacks) (dr : List Γ'), S src = bits l ++ .comma :: sr → S dst = dr →
      (∀ k, k ≠ src → k ≠ dst → S k = S₀ k) →
    ∃ n, n ≤ l.length + 1 ∧ ∃ v' S',
      RunsTo M n ⟨some (ι ()), v, S⟩ ⟨some e, v', S'⟩ ∧
      v'.flag = zeroBits l v.flag ∧ v'.cmp = v.cmp ∧
      S' src = sr ∧ S' dst = (bits l).reverse ++ dr ∧ ∀ k, k ≠ src → k ≠ dst → S' k = S₀ k := by
  have hds := hsd.symm
  induction l with
  | nil =>
    intro v S dr hS hD hF
    refine ⟨1, by simp, { v with ra := none, da := true }, Function.update S src sr,
      runsTo_succ ?_ (runsTo_zero M _), by simp [zeroBits], rfl, by simp,
      by simp [Function.update_of_ne hds, hD],
      fun k hks hkd => by simp [Function.update_of_ne hks, hF k hks hkd]⟩
    tm_step () [zeroScan, zeroScanBody, hS]
  | cons b l ih =>
    intro v S dr hS hD hF
    obtain ⟨n, hn, v', S', hr, hfl, hcmp, hs', hd', hf'⟩ :=
      ih { v with ra := some b, flag := v.flag && !b }
        (Function.update (Function.update S src (bits l ++ .comma :: sr)) dst (.bit b :: dr))
        (.bit b :: dr) (by simp [Function.update_of_ne hsd]) (by simp)
        (fun k hks hkd => by
          simp [Function.update_of_ne hks, Function.update_of_ne hkd, hF k hks hkd])
    refine ⟨n + 1, ?_, v', S', runsTo_succ ?_ hr, by simpa [zeroBits] using hfl, hcmp, hs', ?_, hf'⟩
    · simp only [List.length_cons] at hn ⊢; omega
    · tm_step () [zeroScan, zeroScanBody, hS, hD, hsd, hds]
    · rw [hd']; simp

theorem zeroScan_runs {src dst : K} (hsd : src ≠ dst) (l : List Bool) (sr : List Γ')
    (v : St) (S : Stacks) (hS : S src = bits l ++ .comma :: sr) :
    (zeroScan src dst).Runs v S (fun v' S' =>
        v'.flag = zeroBits l v.flag ∧ v'.cmp = v.cmp ∧
        S' src = sr ∧ S' dst = (bits l).reverse ++ S dst ∧ ∀ k, k ≠ src → k ≠ dst → S' k = S k)
      (l.length + 1) := by
  constructor
  intro Λ M ι e hI
  exact zeroScan_loop hsd hI (S₀ := S) l v S (S dst) hS rfl (fun _ _ _ => rfl)

/-- Set `flag := decide (top number of x = 0)` without consuming it: the number
is moved to scratch `s` and scanned back (`push comma s ; moveNum x s ;
push comma x ; flag := true ; zeroScan s x`); `s` is restored. -/
def isZero (x s : K) : Frag :=
  (Frag.pushSym s .comma).seq ((moveNum x s).seq ((Frag.pushSym x .comma).seq
    ((Frag.load' (fun v => { v with flag := true })).seq (zeroScan s x))))

theorem isZero_runs {x s : K} (hxs : x ≠ s) (l : List Bool) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = bits l ++ .comma :: xr) :
    (isZero x s).Runs v S (fun v' S' =>
        v'.flag = decide (toNat l = 0) ∧ v'.cmp = v.cmp ∧
        S' x = S x ∧ S' s = S s ∧ ∀ k, k ≠ x → k ≠ s → S' k = S k)
      (2 * l.length + 5) := by
  have hsx := hxs.symm
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * l.length + 4) (Frag.pushSym_runs s .comma v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₁; rw [hv₁]
  have h2 := moveNum_runs' hxs l xr v (Function.update S s (.comma :: S s))
    (by simp [Function.update_of_ne hxs, hS])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length + 3) h2
    fun v₂ S₂ ⟨_, hv₂cmp, _, hx₂, hs₂, hf₂⟩ => ?_) (fun _ _ h => h) (by omega)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length + 2) (Frag.pushSym_runs x .comma v₂ S₂)
    fun v₃ S₃ ⟨hv₃, hS₃⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₃; rw [hv₃]
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length + 1)
    (Frag.load'_runs (fun v => { v with flag := true }) v₂ _)
    fun v₄ S₄ ⟨hv₄, hS₄⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₄; rw [hv₄]
  have hs₃ : Function.update S₂ x (.comma :: S₂ x) s = bits l.reverse ++ .comma :: S s := by
    simp [Function.update_of_ne hsx, hs₂]
  have h5 := zeroScan_runs hsx l.reverse (S s) { v₂ with flag := true } _ hs₃
  refine Frag.runs_mono h5 (fun v₅ S₅ ⟨hfl, hcmp, hs₅, hx₅, hf₅⟩ => ⟨?_, ?_, ?_, hs₅, ?_⟩) (by simp)
  · rw [hfl, zeroBits_eq, List.all_reverse, decide_toNat_eq_zero]; simp
  · rw [hcmp, hv₂cmp]
  · rw [hx₅]; simp [hx₂, hS]
  · intro k hkx hks
    rw [hf₅ k hks hkx]; simp [Function.update_of_ne hkx, hf₂ k hkx hks, Function.update_of_ne hks]

theorem isZero_correct {x s : K} (hxs : x ≠ s) (a : ℕ) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encodeNatΓ' a ++ .comma :: xr) :
    (isZero x s).Runs v S (fun v' S' =>
        v'.flag = decide (a = 0) ∧ v'.cmp = v.cmp ∧
        S' x = S x ∧ S' s = S s ∧ ∀ k, k ≠ x → k ≠ s → S' k = S k)
      (2 * Nat.log 2 a + 7) := by
  refine Frag.runs_mono (isZero_runs hxs (Computability.encodeNat a) xr v S hS)
    (fun v' S' ⟨hfl, h⟩ => ⟨by rw [hfl, toNat_encodeNat], h⟩) ?_
  have := encodeNat_length_le a
  omega

theorem isZero_le_B {x s : K} (hxs : x ≠ s) (a b : ℕ) (ha : a < 2 ^ b) (xr : List Γ') (v : St)
    (S : Stacks) (hS : S x = encodeNatΓ' a ++ .comma :: xr) :
    (isZero x s).Runs v S (fun v' S' =>
        v'.flag = decide (a = 0) ∧ v'.cmp = v.cmp ∧
        S' x = S x ∧ S' s = S s ∧ ∀ k, k ≠ x → k ≠ s → S' k = S k)
      (B b) := by
  refine Frag.runs_mono (isZero_runs hxs (Computability.encodeNat a) xr v S hS)
    (fun v' S' ⟨hfl, h⟩ => ⟨by rw [hfl, toNat_encodeNat], h⟩) ?_
  have := encodeNat_length_le_of_lt_pow ha
  exact le_B_of_le_linear (by omega)

/-! ### Increment -/

/-- `l + 1` on little-endian bit lists. -/
def incBits : List Bool → List Bool
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: incBits l

/-- Number of leading (low) ones, i.e. of carries. -/
def carries : List Bool → ℕ
  | true :: l => carries l + 1
  | _ => 0

/-- What is left after the carry chain: the first zero (or the terminator) flipped. -/
def incRest : List Bool → List Bool
  | [] => [true]
  | false :: l => true :: l
  | true :: l => incRest l

theorem incBits_eq (l : List Bool) : incBits l = List.replicate (carries l) false ++ incRest l := by
  induction l using incBits.induct with
  | case1 => simp [incBits, carries, incRest]
  | case2 l => simp [incBits, carries, incRest]
  | case3 l ih => simp [incBits, carries, incRest, List.replicate_succ, ih]

theorem toNat_incBits (l : List Bool) : toNat (incBits l) = toNat l + 1 := by
  induction l using incBits.induct with
  | case1 => simp [incBits, toNat]
  | case2 l => simp [incBits, toNat]; omega
  | case3 l ih => simp [incBits, toNat, ih]; omega

theorem carries_le_length (l : List Bool) : carries l ≤ l.length := by
  induction l with
  | nil => simp [carries]
  | cons b l ih => cases b <;> simp [carries]; omega

theorem incRest_length (l : List Bool) : (incRest l).length ≤ l.length + 1 := by
  induction l using incRest.induct with
  | case1 => simp [incRest]
  | case2 l => simp [incRest]
  | case3 l ih => simp [incRest]; omega

theorem incBits_length (l : List Bool) : (incBits l).length ≤ l.length + 1 := by
  induction l using incBits.induct with
  | case1 => simp [incBits]
  | case2 l => simp [incBits]
  | case3 l ih => simp [incBits]; omega

theorem encodePosNum_succ (p : PosNum) : encodePosNum (PosNum.succ p) = incBits (encodePosNum p) := by
  induction p with
  | one => rfl
  | bit0 p _ => rfl
  | bit1 p ih => simp [encodePosNum, PosNum.succ, incBits, ih]

/-- Mathlib's encoding commutes with increment. -/
theorem encodeNat_succ (n : ℕ) : Computability.encodeNat (n + 1) = incBits (Computability.encodeNat n) := by
  unfold Computability.encodeNat
  rw [Nat.cast_succ, Num.add_one]
  rcases (n : Num) with _ | p
  · rfl
  · exact encodePosNum_succ p

/-- The carry chain: pop from `y`; a `1` becomes a `0` on scratch `s` and we
loop; a `0` becomes a `1` and we exit; the terminator is restored followed by a `1`. -/
def incBody {Λ : Type} (y s : K) (self e : Λ) : Stmt' Λ :=
  pop y readA
    (branch (fun v => decide (v.ra = some true)) (push s (fun _ => .bit false) (goto fun _ => self))
      (branch (fun v => decide (v.ra = some false)) (push y (fun _ => .bit true) (goto fun _ => e))
        (push y (fun _ => .comma) (push y (fun _ => .bit true) (goto fun _ => e)))))

/-- The carry chain as a fragment. -/
def incLoop (y s : K) : Frag where
  Λf := Unit
  entry := ()
  code ι e _ := incBody y s (ι ()) e

theorem incLoop_loop {y s : K} (hys : y ≠ s)
    {Λ : Type} {M : Λ → Stmt' Λ} {ι : Unit → Λ} {e : Λ} (hI : (incLoop y s).Installed M ι e)
    {yr : List Γ'} {S₀ : Stacks} (l : List Bool) :
    ∀ (v : St) (S : Stacks) (zr : List Γ'), S y = bits l ++ .comma :: yr → S s = zr →
      (∀ k, k ≠ y → k ≠ s → S k = S₀ k) →
    ∃ n, n ≤ carries l + 1 ∧ ∃ v' S',
      RunsTo M n ⟨some (ι ()), v, S⟩ ⟨some e, v', S'⟩ ∧
      v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
      S' y = bits (incRest l) ++ .comma :: yr ∧
      S' s = bits (List.replicate (carries l) false) ++ zr ∧
      ∀ k, k ≠ y → k ≠ s → S' k = S₀ k := by
  have hsy := hys.symm
  induction l using incRest.induct with
  | case1 =>
    intro v S zr hS hZ hF
    refine ⟨1, by simp [carries], { v with ra := none, da := true },
      Function.update S y (.bit true :: .comma :: yr),
      runsTo_succ ?_ (runsTo_zero M _), rfl, rfl, rfl, by simp [incRest],
      by simp [Function.update_of_ne hsy, hZ, carries],
      fun k hky hks => by simp [Function.update_of_ne hky, hF k hky hks]⟩
    tm_step () [incLoop, incBody, hS]
  | case2 l =>
    intro v S zr hS hZ hF
    refine ⟨1, by simp [carries], { v with ra := some false },
      Function.update (Function.update S y (bits l ++ .comma :: yr)) y (.bit true :: bits l ++ .comma :: yr),
      runsTo_succ ?_ (runsTo_zero M _), rfl, rfl, rfl, by simp [incRest],
      by simp [Function.update_of_ne hsy, hZ, carries],
      fun k hky hks => by simp [Function.update_of_ne hky, hF k hky hks]⟩
    tm_step () [incLoop, incBody, hS]
  | case3 l ih =>
    intro v S zr hS hZ hF
    obtain ⟨n, hn, v', S', hr, hfl, hcmp, hcar, hy', hs', hf'⟩ :=
      ih { v with ra := some true }
        (Function.update (Function.update S y (bits l ++ .comma :: yr)) s (.bit false :: zr))
        (.bit false :: zr) (by simp [Function.update_of_ne hys]) (by simp)
        (fun k hky hks => by
          simp [Function.update_of_ne hky, Function.update_of_ne hks, hF k hky hks])
    refine ⟨n + 1, ?_, v', S', runsTo_succ ?_ hr, hfl, hcmp, hcar, by simpa [incRest] using hy', ?_, hf'⟩
    · simp only [carries] at hn ⊢; omega
    · tm_step () [incLoop, incBody, hS, hZ, hys, hsy]
    · rw [hs']; simp [carries, List.replicate_succ']

/-- `y := y + 1` in place, using scratch `s` (restored):
`push comma s ; incLoop y s ; moveNum s y`. -/
def incr (y s : K) : Frag :=
  (Frag.pushSym s .comma).seq ((incLoop y s).seq (moveNum s y))

theorem incr_runs {y s : K} (hys : y ≠ s) (l : List Bool) (yr : List Γ') (v : St) (S : Stacks)
    (hS : S y = bits l ++ .comma :: yr) :
    (incr y s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' y = bits (incBits l) ++ .comma :: yr ∧ S' s = S s ∧ ∀ k, k ≠ y → k ≠ s → S' k = S k)
      (2 * l.length + 3) := by
  have hsy := hys.symm
  have hc := carries_le_length l
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * l.length + 2) (Frag.pushSym_runs s .comma v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₁; rw [hv₁]
  have h2 : (incLoop y s).Runs v (Function.update S s (.comma :: S s)) (fun v' S' =>
      v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
      S' y = bits (incRest l) ++ .comma :: yr ∧
      S' s = bits (List.replicate (carries l) false) ++ .comma :: S s ∧
      ∀ k, k ≠ y → k ≠ s → S' k = S k) (carries l + 1) := by
    constructor
    intro Λ M ι e hI
    obtain ⟨n, hn, v', S', hr, hfl, hcmp, hcar, hy', hs', hf'⟩ :=
      incLoop_loop hys hI (yr := yr) (S₀ := S) l v (Function.update S s (.comma :: S s)) (.comma :: S s)
        (by simp [Function.update_of_ne hys, hS]) (by simp)
        (fun k hky hks => by simp [Function.update_of_ne hks])
    exact ⟨n, hn, v', S', hr, hfl, hcmp, hcar, hy', hs', hf'⟩
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length + 1) h2
    fun v₂ S₂ ⟨hfl₂, hcmp₂, hcar₂, hy₂, hs₂, hf₂⟩ => ?_) (fun _ _ h => h) (by omega)
  have h3 := moveNum_runs' hsy (List.replicate (carries l) false) (S s) v₂ S₂ hs₂
  refine Frag.runs_mono h3 (fun v₃ S₃ ⟨hfl₃, hcmp₃, hcar₃, hs₃, hy₃, hf₃⟩ => ⟨?_, ?_, ?_, ?_, hs₃, ?_⟩)
    (by simp; omega)
  · rw [hfl₃, hfl₂]
  · rw [hcmp₃, hcmp₂]
  · rw [hcar₃, hcar₂]
  · rw [hy₃, hy₂, ← bits_reverse, List.reverse_replicate, incBits_eq]; simp
  · intro k hky hks; rw [hf₃ k hks hky, hf₂ k hky hks]


/-- Increment on naturals: the result is exactly Mathlib's encoding of `a + 1`. -/
theorem incr_correct {y s : K} (hys : y ≠ s) (a : ℕ) (yr : List Γ') (v : St) (S : Stacks)
    (hS : S y = encodeNatΓ' a ++ .comma :: yr) :
    (incr y s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' y = encodeNatΓ' (a + 1) ++ .comma :: yr ∧ S' s = S s ∧ ∀ k, k ≠ y → k ≠ s → S' k = S k)
      (2 * Nat.log 2 a + 5) := by
  refine Frag.runs_mono (incr_runs hys (Computability.encodeNat a) yr v S hS)
    (fun v' S' ⟨hfl, hcmp, hcar, hy, hs, hf⟩ =>
      ⟨hfl, hcmp, hcar, by rw [hy, encodeNatΓ'_eq, encodeNat_succ], hs, hf⟩) ?_
  have := encodeNat_length_le a
  omega

theorem incr_le_B {y s : K} (hys : y ≠ s) (a b : ℕ) (ha : a < 2 ^ b) (yr : List Γ') (v : St)
    (S : Stacks) (hS : S y = encodeNatΓ' a ++ .comma :: yr) :
    (incr y s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' y = encodeNatΓ' (a + 1) ++ .comma :: yr ∧ S' s = S s ∧ ∀ k, k ≠ y → k ≠ s → S' k = S k)
      (B b) := by
  refine Frag.runs_mono (incr_runs hys (Computability.encodeNat a) yr v S hS)
    (fun v' S' ⟨hfl, hcmp, hcar, hy, hs, hf⟩ =>
      ⟨hfl, hcmp, hcar, by rw [hy, encodeNatΓ'_eq, encodeNat_succ], hs, hf⟩) ?_
  have := encodeNat_length_le_of_lt_pow ha
  exact le_B_of_le_linear (by omega)

/-! ### Decrement -/

/-- `l - 1` on little-endian bit lists (`0 ↦ 0`); the borrow chain turns low
zeros into ones, the first one into a zero — dropped when it is the top bit,
so canonical inputs give canonical outputs. -/
def predBits : List Bool → List Bool
  | [] => []
  | false :: l => true :: predBits l
  | [true] => []
  | true :: b :: l => false :: b :: l

/-- Number of leading (low) zeros, i.e. of borrows. -/
def borrows : List Bool → ℕ
  | false :: l => borrows l + 1
  | _ => 0

/-- What is left after the borrow chain. -/
def predRest : List Bool → List Bool
  | [] => []
  | false :: l => predRest l
  | [true] => []
  | true :: b :: l => false :: b :: l

theorem predBits_eq (l : List Bool) : predBits l = List.replicate (borrows l) true ++ predRest l := by
  induction l using predBits.induct with
  | case1 => simp [predBits, borrows, predRest]
  | case2 l ih => simp [predBits, borrows, predRest, List.replicate_succ, ih]
  | case3 => simp [predBits, borrows, predRest]
  | case4 b l => simp [predBits, borrows, predRest]

theorem toNat_predBits (l : List Bool) (h : 1 ≤ toNat l) : toNat (predBits l) + 1 = toNat l := by
  induction l using predBits.induct with
  | case1 => simp [toNat] at h
  | case2 l ih =>
    simp only [toNat, Bool.toNat_false] at h ⊢
    have := ih (by omega)
    simp [predBits, toNat]; omega
  | case3 => simp [predBits, toNat]
  | case4 b l => simp [predBits, toNat]; omega

theorem borrows_le_length (l : List Bool) : borrows l ≤ l.length := by
  induction l with
  | nil => simp [borrows]
  | cons b l ih => cases b <;> simp [borrows]; omega

theorem predBits_length (l : List Bool) : (predBits l).length ≤ l.length := by
  induction l using predBits.induct with
  | case1 => simp [predBits]
  | case2 l ih => simp [predBits]; omega
  | case3 => simp [predBits]
  | case4 b l => simp [predBits]

theorem canon_predRest {l : List Bool} (h : Canon l) : Canon (predRest l) := by
  induction l using predRest.induct with
  | case1 => simp [predRest]
  | case2 l ih => exact ih h.of_cons
  | case3 => simp [predRest]
  | case4 b l => rw [predRest]; exact canon_cons_of_ne_nil (List.cons_ne_nil _ _) h.of_cons

theorem canon_predBits {l : List Bool} (h : Canon l) : Canon (predBits l) := by
  rw [predBits_eq]; exact canon_replicate_true_append _ (canon_predRest h)

/-- Peek-handler recording in `db` whether the top of the stack is NOT a bit. -/
def readEnd (v : St) (o : Option Γ') : St :=
  match o with
  | some (.bit _) => { v with db := false }
  | _ => { v with db := true }

@[simp] theorem readEnd_bit (v : St) (b : Bool) : readEnd v (some (.bit b)) = { v with db := false } := rfl
@[simp] theorem readEnd_comma (v : St) : readEnd v (some .comma) = { v with db := true } := rfl
@[simp] theorem readEnd_none (v : St) : readEnd v none = { v with db := true } := rfl

/-- The borrow chain: pop from `x`; a `0` becomes a `1` on scratch `s` and we
loop; a `1` becomes a `0` (omitted if it was the top bit) and we exit; the
terminator is restored (`0 - 1 = 0`). -/
def predBody {Λ : Type} (x s : K) (self e : Λ) : Stmt' Λ :=
  pop x readA
    (branch (fun v => decide (v.ra = some false)) (push s (fun _ => .bit true) (goto fun _ => self))
      (branch (fun v => decide (v.ra = some true))
        (peek x readEnd (branch (fun v => v.db) (goto fun _ => e)
          (push x (fun _ => .bit false) (goto fun _ => e))))
        (push x (fun _ => .comma) (goto fun _ => e))))

/-- The borrow chain as a fragment. -/
def predLoop (x s : K) : Frag where
  Λf := Unit
  entry := ()
  code ι e _ := predBody x s (ι ()) e

theorem predLoop_loop {x s : K} (hxs : x ≠ s)
    {Λ : Type} {M : Λ → Stmt' Λ} {ι : Unit → Λ} {e : Λ} (hI : (predLoop x s).Installed M ι e)
    {xr : List Γ'} {S₀ : Stacks} (l : List Bool) :
    ∀ (v : St) (S : Stacks) (zr : List Γ'), S x = bits l ++ .comma :: xr → S s = zr →
      (∀ k, k ≠ x → k ≠ s → S k = S₀ k) →
    ∃ n, n ≤ borrows l + 1 ∧ ∃ v' S',
      RunsTo M n ⟨some (ι ()), v, S⟩ ⟨some e, v', S'⟩ ∧
      v'.flag = v.flag ∧ v'.cmp = v.cmp ∧
      S' x = bits (predRest l) ++ .comma :: xr ∧
      S' s = bits (List.replicate (borrows l) true) ++ zr ∧
      ∀ k, k ≠ x → k ≠ s → S' k = S₀ k := by
  have hsx := hxs.symm
  induction l using predRest.induct with
  | case1 =>
    intro v S zr hS hZ hF
    refine ⟨1, by simp [borrows], { v with ra := none, da := true },
      Function.update (Function.update S x xr) x (.comma :: xr),
      runsTo_succ ?_ (runsTo_zero M _), rfl, rfl, by simp [predRest],
      by simp [Function.update_of_ne hsx, hZ, borrows],
      fun k hkx hks => by simp [Function.update_of_ne hkx, hF k hkx hks]⟩
    tm_step () [predLoop, predBody, hS]
  | case2 l ih =>
    intro v S zr hS hZ hF
    obtain ⟨n, hn, v', S', hr, hfl, hcmp, hx', hs', hf'⟩ :=
      ih { v with ra := some false }
        (Function.update (Function.update S x (bits l ++ .comma :: xr)) s (.bit true :: zr))
        (.bit true :: zr) (by simp [Function.update_of_ne hxs]) (by simp)
        (fun k hkx hks => by
          simp [Function.update_of_ne hkx, Function.update_of_ne hks, hF k hkx hks])
    refine ⟨n + 1, ?_, v', S', runsTo_succ ?_ hr, hfl, hcmp, by simpa [predRest] using hx', ?_, hf'⟩
    · simp only [borrows] at hn ⊢; omega
    · tm_step () [predLoop, predBody, hS, hZ, hxs, hsx]
    · rw [hs']; simp [borrows, List.replicate_succ']
  | case3 =>
    intro v S zr hS hZ hF
    refine ⟨1, by simp [borrows], { v with ra := some true, db := true },
      Function.update S x (.comma :: xr),
      runsTo_succ ?_ (runsTo_zero M _), rfl, rfl, by simp [predRest],
      by simp [Function.update_of_ne hsx, hZ, borrows],
      fun k hkx hks => by simp [Function.update_of_ne hkx, hF k hkx hks]⟩
    tm_step () [predLoop, predBody, hS]
  | case4 b l =>
    intro v S zr hS hZ hF
    refine ⟨1, by simp [borrows], { v with ra := some true, db := false },
      Function.update (Function.update S x (.bit b :: bits l ++ .comma :: xr)) x
        (.bit false :: .bit b :: bits l ++ .comma :: xr),
      runsTo_succ ?_ (runsTo_zero M _), rfl, rfl, by simp [predRest],
      by simp [Function.update_of_ne hsx, hZ, borrows],
      fun k hkx hks => by simp [Function.update_of_ne hkx, hF k hkx hks]⟩
    tm_step () [predLoop, predBody, hS]

/-- `x := x - 1` in place (`0` stays `0`), using scratch `s` (restored):
`push comma s ; predLoop x s ; moveNum s x`. -/
def predNum (x s : K) : Frag :=
  (Frag.pushSym s .comma).seq ((predLoop x s).seq (moveNum s x))

theorem predNum_runs {x s : K} (hxs : x ≠ s) (l : List Bool) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = bits l ++ .comma :: xr) :
    (predNum x s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧
        S' x = bits (predBits l) ++ .comma :: xr ∧ S' s = S s ∧ ∀ k, k ≠ x → k ≠ s → S' k = S k)
      (2 * l.length + 3) := by
  have hsx := hxs.symm
  have hc := borrows_le_length l
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * l.length + 2) (Frag.pushSym_runs s .comma v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₁; rw [hv₁]
  have h2 : (predLoop x s).Runs v (Function.update S s (.comma :: S s)) (fun v' S' =>
      v'.flag = v.flag ∧ v'.cmp = v.cmp ∧
      S' x = bits (predRest l) ++ .comma :: xr ∧
      S' s = bits (List.replicate (borrows l) true) ++ .comma :: S s ∧
      ∀ k, k ≠ x → k ≠ s → S' k = S k) (borrows l + 1) := by
    constructor
    intro Λ M ι e hI
    obtain ⟨n, hn, v', S', hr, hfl, hcmp, hx', hs', hf'⟩ :=
      predLoop_loop hxs hI (xr := xr) (S₀ := S) l v (Function.update S s (.comma :: S s)) (.comma :: S s)
        (by simp [Function.update_of_ne hxs, hS]) (by simp)
        (fun k hkx hks => by simp [Function.update_of_ne hks])
    exact ⟨n, hn, v', S', hr, hfl, hcmp, hx', hs', hf'⟩
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length + 1) h2
    fun v₂ S₂ ⟨hfl₂, hcmp₂, hx₂, hs₂, hf₂⟩ => ?_) (fun _ _ h => h) (by omega)
  have h3 := moveNum_runs' hsx (List.replicate (borrows l) true) (S s) v₂ S₂ hs₂
  refine Frag.runs_mono h3 (fun v₃ S₃ ⟨hfl₃, hcmp₃, _, hs₃, hx₃, hf₃⟩ => ⟨?_, ?_, ?_, hs₃, ?_⟩)
    (by simp; omega)
  · rw [hfl₃, hfl₂]
  · rw [hcmp₃, hcmp₂]
  · rw [hx₃, hx₂, ← bits_reverse, List.reverse_replicate, predBits_eq]; simp
  · intro k hkx hks; rw [hf₃ k hks hkx, hf₂ k hkx hks]

/-- Decrement on naturals: for `1 ≤ a` the result is exactly Mathlib's encoding of `a - 1`. -/
theorem predNum_correct {x s : K} (hxs : x ≠ s) (a : ℕ) (ha : 1 ≤ a) (xr : List Γ') (v : St)
    (S : Stacks) (hS : S x = encodeNatΓ' a ++ .comma :: xr) :
    (predNum x s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧
        S' x = encodeNatΓ' (a - 1) ++ .comma :: xr ∧ S' s = S s ∧ ∀ k, k ≠ x → k ≠ s → S' k = S k)
      (2 * Nat.log 2 a + 5) := by
  refine Frag.runs_mono (predNum_runs hxs (Computability.encodeNat a) xr v S hS)
    (fun v' S' ⟨hfl, hcmp, hx, hs, hf⟩ => ⟨hfl, hcmp, ?_, hs, hf⟩) ?_
  · have hval : toNat (predBits (Computability.encodeNat a)) = a - 1 := by
      have := toNat_predBits (Computability.encodeNat a) (by rw [toNat_encodeNat]; exact ha)
      rw [toNat_encodeNat] at this
      omega
    rw [hx, encodeNatΓ'_eq, (canon_predBits (canon_encodeNat a)).eq_encodeNat, hval]
  · have := encodeNat_length_le a
    omega

theorem predNum_le_B {x s : K} (hxs : x ≠ s) (a b : ℕ) (ha : 1 ≤ a) (hab : a < 2 ^ b)
    (xr : List Γ') (v : St) (S : Stacks) (hS : S x = encodeNatΓ' a ++ .comma :: xr) :
    (predNum x s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧
        S' x = encodeNatΓ' (a - 1) ++ .comma :: xr ∧ S' s = S s ∧ ∀ k, k ≠ x → k ≠ s → S' k = S k)
      (B b) := by
  refine Frag.runs_mono (predNum_correct hxs a ha xr v S hS) (fun _ _ h => h) ?_
  have := encodeNat_length_le_of_lt_pow hab
  have h2 : Nat.log 2 a + 1 ≤ b := by
    have := (Nat.log_lt_iff_lt_pow one_lt_two (by omega)).mpr hab
    omega
  exact le_B_of_le_linear (by omega)


/-! ### Bit length -/

/-- Bit length: `0` for `0`, else `Nat.log 2 a + 1`. -/
def bl (a : ℕ) : ℕ := if a = 0 then 0 else Nat.log 2 a + 1

@[simp] theorem bl_zero : bl 0 = 0 := by simp [bl]

theorem bl_of_pos {a : ℕ} (ha : 1 ≤ a) : bl a = Nat.log 2 a + 1 := by
  simp [bl, show a ≠ 0 by omega]

/-- Appending a low bit: the bit length grows by one unless the value stays `0`. -/
theorem bl_step (V : ℕ) (b : Bool) :
    bl (b.toNat + 2 * V) = if b.toNat + 2 * V = 0 then 0 else bl V + 1 := by
  rcases Nat.eq_zero_or_pos V with rfl | hV
  · cases b <;> simp [bl]
  · have h2 : 2 ≤ b.toNat + 2 * V := by omega
    have hd : (b.toNat + 2 * V) / 2 = V := by cases b <;> simp; omega
    rw [bl, if_neg (by omega), if_neg (by omega), bl, if_neg (by omega),
      Nat.log_of_one_lt_of_le one_lt_two h2, hd]

theorem bl_le_length (l : List Bool) : bl (toNat l) ≤ l.length := by
  rcases Nat.eq_zero_or_pos (toNat l) with h | h
  · simp [h]
  · rw [bl_of_pos h]
    have := (Nat.log_lt_iff_lt_pow one_lt_two h.ne').mpr (toNat_lt_two_pow l)
    omega

/-- Pop-handler that (re)sets both `ra` and `da` from the popped symbol. -/
def readBit (v : St) (o : Option Γ') : St :=
  match o with
  | some (.bit b) => { v with ra := some b, da := false }
  | _ => { v with ra := none, da := true }

@[simp] theorem readBit_bit (v : St) (b : Bool) :
    readBit v (some (.bit b)) = { v with ra := some b, da := false } := rfl
@[simp] theorem readBit_comma (v : St) : readBit v (some .comma) = { v with ra := none, da := true } := rfl
@[simp] theorem readBit_none (v : St) : readBit v none = { v with ra := none, da := true } := rfl

/-- Read one symbol of the (reversed) number on `s`: a bit is pushed on `x`
and or-ed into `flag`; the terminator sets `carry := true`. -/
def blScan (s x : K) : Frag :=
  Frag.straight fun q =>
    pop s readBit (branch (fun v => v.da) (load (fun v => { v with carry := true }) q)
      (push x (fun v => .bit (bitOf v.ra)) (load (fun v => { v with flag := v.flag || bitOf v.ra }) q)))

theorem blScan_runs_bit {s x : K} (hsx : s ≠ x) (b : Bool) (q : List Bool) (sr : List Γ')
    (v : St) (S : Stacks) (hS : S s = bits (b :: q) ++ .comma :: sr) :
    (blScan s x).Runs v S (fun v' S' => v' = { v with ra := some b, da := false, flag := v.flag || b } ∧
      S' = Function.update (Function.update S s (bits q ++ .comma :: sr)) x (.bit b :: S x)) 1 := by
  constructor
  intro Λ M ι e hI
  refine ⟨1, le_rfl, _, _, runsTo_succ ?_ (runsTo_zero M _), rfl, rfl⟩
  tm_step () [blScan, Frag.straight, hS, Function.update_of_ne hsx.symm]

theorem blScan_runs_end {s x : K} (sr : List Γ') (v : St) (S : Stacks) (hS : S s = .comma :: sr) :
    (blScan s x).Runs v S (fun v' S' => v' = { v with ra := none, da := true, carry := true } ∧
      S' = Function.update S s sr) 1 := by
  constructor
  intro Λ M ι e hI
  refine ⟨1, le_rfl, _, _, runsTo_succ ?_ (runsTo_zero M _), rfl, rfl⟩
  tm_step () [blScan, Frag.straight, hS]

/-- One iteration of the bit-length loop: read a symbol; on a bit, increment
the counter on `y` once a `1` has been seen. -/
def blBody (x y s s' : K) : Frag :=
  (blScan s x).seq (Frag.ite (fun v => v.da) Frag.skip
    (Frag.ite (fun v => v.flag) (incr y s') Frag.skip))

/-- Push the bit length of the top number `a` of `x` (`Nat.log 2 a + 1`, or
`0` for `a = 0`) on `y`; `x` is restored; scratch `s` (reversal) and `s'`
(carry chain) are restored.  The number is reversed onto `s`, then moved back
onto `x` most-significant bit first, counting bits from the first `1`. -/
def bitlen (x y s s' : K) : Frag :=
  (Frag.pushSym s .comma).seq ((moveNum x s).seq ((Frag.pushSym x .comma).seq ((pushNum y 0).seq
    ((Frag.load' (fun v => { v with flag := false, carry := false })).seq
      (Frag.loop (fun v => !v.carry) (blBody x y s s'))))))

/-- Loop invariant of `bitlen`: phase 1 (`carry = false`) has read the prefix
`p` (MSB first) of `l.reverse`, phase 2 (`carry = true`, `i = |l| + 1`) has
read the terminator. -/
def BlInv (x y s s' : K) (l : List Bool) (xr yr sr s'r : List Γ') (S₀ : Stacks)
    (i : ℕ) (v : St) (S : Stacks) : Prop :=
  (∃ p q, l.reverse = p ++ q ∧ p.length = i ∧ v.carry = false ∧
    v.flag = decide (toNat p.reverse ≠ 0) ∧
    S s = bits q ++ .comma :: sr ∧ S x = bits p.reverse ++ .comma :: xr ∧
    S y = encodeNatΓ' (bl (toNat p.reverse)) ++ .comma :: yr ∧ S s' = s'r ∧
    ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ s' → S k = S₀ k) ∨
  (i = l.length + 1 ∧ v.carry = true ∧ S s = sr ∧ S x = bits l ++ .comma :: xr ∧
    S y = encodeNatΓ' (bl (toNat l)) ++ .comma :: yr ∧ S s' = s'r ∧
    ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ s' → S k = S₀ k)

theorem blBody_runs {x y s s' : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxs' : x ≠ s') (hys : y ≠ s)
    (hys' : y ≠ s') (hss' : s ≠ s') (l : List Bool) (xr yr sr s'r : List Γ') (S₀ : Stacks)
    (i : ℕ) (hi : i < l.length + 1) (v : St) (S : Stacks)
    (hI : BlInv x y s s' l xr yr sr s'r S₀ i v S) :
    (blBody x y s s').Runs v S (BlInv x y s s' l xr yr sr s'r S₀ (i + 1))
      (2 * Nat.log 2 l.length + 8) := by
  have hsx := hxs.symm
  have hyx := hxy.symm
  have hsy := hys.symm
  have hs'x := hxs'.symm
  have hs'y := hys'.symm
  have hs's := hss'.symm
  rcases hI with ⟨p, q, hpq, hp, hcar, hfl, hs, hx, hy, hs', hF⟩ | ⟨hi', -⟩
  · cases q with
    | nil =>
      -- the terminator: phase 1 → phase 2
      have hp' : p = l.reverse := by simpa using hpq.symm
      subst hp'
      have hlen : i = l.length := by simpa using hp.symm
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 2) (blScan_runs_end (x := x) sr v S (by simpa using hs))
        fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
      subst hv₁ hS₁
      refine Frag.ite_runs_true (by simp) ?_
      refine Frag.runs_mono (Frag.skip_runs _ _) (fun v₂ S₂ ⟨hv₂, hS₂⟩ => Or.inr ?_) le_rfl
      subst hv₂ hS₂
      refine ⟨by omega, rfl, by simp, ?_, ?_, by simp [Function.update_of_ne hs's, hs'],
        fun k hkx hky hks hks' => by simp [Function.update_of_ne hks, hF k hkx hky hks hks']⟩
      · simpa [Function.update_of_ne hxs] using hx
      · simpa [Function.update_of_ne hys] using hy
    | cons b q =>
      -- a bit: phase 1 → phase 1 with prefix `p ++ [b]`
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * Nat.log 2 l.length + 7)
        (blScan_runs_bit hsx b q sr v S hs) fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
      subst hv₁ hS₁
      have hV : toNat (p ++ [b]).reverse = b.toNat + 2 * toNat p.reverse := by simp [toNat]
      have hpq' : l.reverse = (p ++ [b]) ++ q := by rw [hpq, List.append_assoc]; rfl
      have hlen' : (p ++ [b]).length = i + 1 := by simp [hp]
      have hblV : bl (toNat p.reverse) ≤ l.length := by
        have := bl_le_length p.reverse
        have : p.length ≤ l.length := by
          have := congrArg List.length hpq; simp at this; omega
        simp at *; omega
      have hlog : Nat.log 2 (bl (toNat p.reverse)) ≤ Nat.log 2 l.length := Nat.log_mono_right hblV
      have hx₁ : Function.update (Function.update S s (bits q ++ .comma :: sr)) x (.bit b :: S x) x =
          bits (p ++ [b]).reverse ++ .comma :: xr := by simp [hx]
      have hs₁ : Function.update (Function.update S s (bits q ++ .comma :: sr)) x (.bit b :: S x) s =
          bits q ++ .comma :: sr := by simp [Function.update_of_ne hsx]
      have hy₁ : Function.update (Function.update S s (bits q ++ .comma :: sr)) x (.bit b :: S x) y =
          encodeNatΓ' (bl (toNat p.reverse)) ++ .comma :: yr := by
        simp [Function.update_of_ne hyx, Function.update_of_ne hys, hy]
      have hs'₁ : Function.update (Function.update S s (bits q ++ .comma :: sr)) x (.bit b :: S x) s' =
          s'r := by simp [Function.update_of_ne hs'x, Function.update_of_ne hs's, hs']
      have hF₁ : ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ s' →
          Function.update (Function.update S s (bits q ++ .comma :: sr)) x (.bit b :: S x) k = S₀ k :=
        fun k hkx hky hks hks' => by
          simp [Function.update_of_ne hkx, Function.update_of_ne hks, hF k hkx hky hks hks']
      refine Frag.ite_runs_false (by simp) ?_
      by_cases hz : b.toNat + 2 * toNat p.reverse = 0
      · -- still zero: flag stays false, no increment
        have hb : b = false := by cases b <;> simp at hz ⊢
        have hV0 : toNat p.reverse = 0 := by omega
        subst hb
        refine Frag.ite_runs_false (by simp [hfl, hV0]) ?_
        refine Frag.runs_mono (Frag.skip_runs _ _) (fun v₂ S₂ ⟨hv₂, hS₂⟩ => Or.inl ?_) (by omega)
        subst hv₂ hS₂
        refine ⟨p ++ [false], q, hpq', hlen', hcar, ?_, hs₁, hx₁, ?_, hs'₁, hF₁⟩
        · simp [hV0, hfl, toNat]
        · rw [hy₁, hV, bl_step, if_pos hz]; simp [hV0]
      · -- nonzero after this bit: flag true, increment the counter
        have hfl' : (v.flag || b) = true := by
          cases b <;> simp_all
        refine Frag.ite_runs_true (by simpa using hfl') ?_
        have hinc := incr_correct hys' (bl (toNat p.reverse)) yr
          { v with ra := some b, da := false, flag := v.flag || b } _ hy₁
        refine Frag.runs_mono hinc (fun v₂ S₂ ⟨hfl₂, _, hcar₂, hy₂, hs'₂, hf₂⟩ => Or.inl ?_) (by omega)
        refine ⟨p ++ [b], q, hpq', hlen', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hcar₂]; exact hcar
        · simp only [hfl₂, hfl', List.reverse_append, List.reverse_singleton, List.singleton_append]
          simp only [toNat] at hz ⊢
          exact (decide_eq_true hz).symm
        · rw [hf₂ s hsy hss']; exact hs₁
        · rw [hf₂ x hxy hxs']; exact hx₁
        · rw [hy₂, hV, bl_step, if_neg hz]
        · rw [hs'₂]; exact hs'₁
        · intro k hkx hky hks hks'; rw [hf₂ k hky hks']; exact hF₁ k hkx hky hks hks'
  · omega


theorem bitlen_runs {x y s s' : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxs' : x ≠ s') (hys : y ≠ s)
    (hys' : y ≠ s') (hss' : s ≠ s') (l : List Bool) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = bits l ++ .comma :: xr) :
    (bitlen x y s s').Runs v S (fun _ S' =>
        S' x = S x ∧ S' y = encodeNatΓ' (bl (toNat l)) ++ .comma :: S y ∧ S' s = S s ∧ S' s' = S s' ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ s' → S' k = S k)
      ((l.length + 2) * (2 * Nat.log 2 l.length + 10)) := by
  have hsx := hxs.symm
  have hyx := hxy.symm
  have hsy := hys.symm
  have hs'x := hxs'.symm
  have hs'y := hys'.symm
  have hs's := hss'.symm
  have h0 : Nat.log 2 0 = 0 := Nat.log_zero_right 2
  -- TL: the loop's bound
  set TL := (l.length + 1) * (2 * Nat.log 2 l.length + 8 + 1) + 1 with hTL
  -- stage 1: push comma on s
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length + 5 + TL) (Frag.pushSym_runs s .comma v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by rw [hTL]; ring_nf; omega)
  subst hS₁; rw [hv₁]
  -- stage 2: moveNum x s
  have h2 := moveNum_runs' hxs l xr v (Function.update S s (.comma :: S s))
    (by simp [Function.update_of_ne hxs, hS])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL + 4) h2
    fun v₂ S₂ ⟨_, _, _, hx₂, hs₂, hf₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: push comma on x
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL + 3) (Frag.pushSym_runs x .comma v₂ S₂)
    fun v₃ S₃ ⟨hv₃, hS₃⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₃; rw [hv₃]
  -- stage 4: push 0 on y
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL + 1) (pushNum_runs y 0 v₂ _)
    fun v₄ S₄ ⟨hv₄, hy₄, hf₄⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₄]
  -- stage 5: reset flag and carry
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL)
    (Frag.load'_runs (fun v => { v with flag := false, carry := false }) v₂ S₄)
    fun v₅ S₅ ⟨hv₅, hS₅⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₅, hS₅]
  -- the loop
  have hs₄ : S₄ s = (bits l).reverse ++ .comma :: S s := by
    rw [hf₄ s hsy]; simp [Function.update_of_ne hsx, hs₂]
  have hx₄ : S₄ x = .comma :: xr := by rw [hf₄ x hxy]; simp [hx₂]
  have hy₄' : S₄ y = encodeNatΓ' 0 ++ .comma :: S y := by
    rw [hy₄]; simp [Function.update_of_ne hyx, hf₂ y hyx hys, Function.update_of_ne hys]
  have hs'₄ : S₄ s' = S s' := by
    rw [hf₄ s' hs'y]; simp [Function.update_of_ne hs'x, hf₂ s' hs'x hs's, Function.update_of_ne hs's]
  have hF₄ : ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ s' → S₄ k = S k := fun k hkx hky hks hks' => by
    rw [hf₄ k hky]; simp [Function.update_of_ne hkx, hf₂ k hkx hks, Function.update_of_ne hks]
  have hloop := Frag.loop_runs (c := fun v => !v.carry) (B := blBody x y s s')
    (BlInv x y s s' l xr (S y) (S s) (S s') S) (l.length + 1) (2 * Nat.log 2 l.length + 8)
    (v := { v₂ with flag := false, carry := false }) (S := S₄)
    (Or.inl ⟨[], l.reverse, by simp, rfl, rfl, by simp [toNat], by simpa using hs₄, by simpa using hx₄,
      by rw [hy₄']; simp [toNat], hs'₄, hF₄⟩)
    (fun i hi w T hI => by
      rcases hI with ⟨p, q, -, -, hcar, -⟩ | ⟨hi', -⟩
      · simp [hcar]
      · omega)
    (fun w T hI => by
      rcases hI with ⟨p, q, hpq, hp, -⟩ | ⟨-, hcar, -⟩
      · have := congrArg List.length hpq; simp at this; omega
      · simp [hcar])
    (fun i hi w T hI => blBody_runs hxy hxs hxs' hys hys' hss' l xr (S y) (S s) (S s') S i hi w T hI)
  refine Frag.runs_mono hloop (fun v' S' ⟨hI, _⟩ => ?_) le_rfl
  rcases hI with ⟨p, q, hpq, hp, -⟩ | ⟨-, -, hs', hx', hy', hs'', hF'⟩
  · have := congrArg List.length hpq; simp at this; omega
  · exact ⟨by rw [hx', hS], hy', hs', hs'', hF'⟩

/-- Bit length on naturals: the result is exactly Mathlib's encoding of
`Nat.log 2 a + 1` (of `0` when `a = 0`). -/
theorem bitlen_correct {x y s s' : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxs' : x ≠ s') (hys : y ≠ s)
    (hys' : y ≠ s') (hss' : s ≠ s') (a : ℕ) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encodeNatΓ' a ++ .comma :: xr) :
    (bitlen x y s s').Runs v S (fun _ S' =>
        S' x = S x ∧ S' y = encodeNatΓ' (bl a) ++ .comma :: S y ∧ S' s = S s ∧ S' s' = S s' ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ s' → S' k = S k)
      ((Nat.log 2 a + 3) * (2 * Nat.log 2 (Nat.log 2 a + 1) + 10)) := by
  refine Frag.runs_mono (bitlen_runs hxy hxs hxs' hys hys' hss' (Computability.encodeNat a) xr v S hS)
    (fun _ S' ⟨hx, hy, h⟩ => ⟨hx, by rw [hy, toNat_encodeNat], h⟩) ?_
  have hlen := encodeNat_length_le a
  exact Nat.mul_le_mul (by omega) (by have := Nat.log_mono_right (b := 2) hlen; omega)

/-- Bit length on naturals `a ≥ 1`: the result is exactly `Nat.log 2 a + 1`. -/
theorem bitlen_correct_pos {x y s s' : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxs' : x ≠ s') (hys : y ≠ s)
    (hys' : y ≠ s') (hss' : s ≠ s') (a : ℕ) (ha : 1 ≤ a) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encodeNatΓ' a ++ .comma :: xr) :
    (bitlen x y s s').Runs v S (fun _ S' =>
        S' x = S x ∧ S' y = encodeNatΓ' (Nat.log 2 a + 1) ++ .comma :: S y ∧ S' s = S s ∧
        S' s' = S s' ∧ ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ s' → S' k = S k)
      ((Nat.log 2 a + 3) * (2 * Nat.log 2 (Nat.log 2 a + 1) + 10)) := by
  refine Frag.runs_mono (bitlen_correct hxy hxs hxs' hys hys' hss' a xr v S hS)
    (fun _ S' ⟨hx, hy, h⟩ => ⟨hx, by rw [hy, bl_of_pos ha], h⟩) le_rfl

theorem bitlen_le_B {x y s s' : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxs' : x ≠ s') (hys : y ≠ s)
    (hys' : y ≠ s') (hss' : s ≠ s') (a b : ℕ) (hab : a < 2 ^ b) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encodeNatΓ' a ++ .comma :: xr) :
    (bitlen x y s s').Runs v S (fun _ S' =>
        S' x = S x ∧ S' y = encodeNatΓ' (bl a) ++ .comma :: S y ∧ S' s = S s ∧ S' s' = S s' ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ s' → S' k = S k)
      (B b) := by
  refine Frag.runs_mono (bitlen_runs hxy hxs hxs' hys hys' hss' (Computability.encodeNat a) xr v S hS)
    (fun _ S' ⟨hx, hy, h⟩ => ⟨hx, by rw [hy, toNat_encodeNat], h⟩) ?_
  have hlen := encodeNat_length_le_of_lt_pow hab
  have hlog := Nat.log_le_self 2 (Computability.encodeNat a).length
  calc ((Computability.encodeNat a).length + 2) * (2 * Nat.log 2 (Computability.encodeNat a).length + 10)
      ≤ (b + 2) * (10 * (b + 2)) := Nat.mul_le_mul (by omega) (by omega)
    _ = 10 * (b + 2) ^ 2 := by ring
    _ ≤ B b := quad_le_B (by norm_num)

/-! ### Powers of two -/

theorem encodeNat_two_pow (e : ℕ) :
    Computability.encodeNat (2 ^ e) = List.replicate e false ++ [true] := by
  rw [(canon_replicate_false_append_true e).eq_encodeNat, toNat_replicate_false_append]
  simp [toNat]

/-- One iteration: `x := x - 1`, push a `0` on `y`, test `x` for zero. -/
def pow2Body (x y s s' : K) : Frag :=
  (predNum x s').seq ((Frag.pushSym y (.bit false)).seq (isZero x s))

/-- Consume the top number `e` of `x` and push `2 ^ e` on `y`: a `1` then `e`
zeros (counting `e` down with `predNum`); scratch `s` (zero test) and `s'`
(borrow chain) are restored. -/
def pow2 (x y s s' : K) : Frag :=
  (Frag.pushSym y .comma).seq ((Frag.pushSym y (.bit true)).seq ((isZero x s).seq
    ((Frag.loop (fun v => !v.flag) (pow2Body x y s s')).seq (dropNum x))))

/-- Loop invariant of `pow2`: after `i` iterations `x` holds `e - i`, `y` holds
`i` zeros above the `1`, and `flag` says whether `x` is zero. -/
def P2Inv (x y s s' : K) (e : ℕ) (xr yr sr s'r : List Γ') (S₀ : Stacks)
    (i : ℕ) (v : St) (S : Stacks) : Prop :=
  i ≤ e ∧ v.flag = decide (e - i = 0) ∧ S x = encodeNatΓ' (e - i) ++ .comma :: xr ∧
  S y = bits (List.replicate i false) ++ .bit true :: .comma :: yr ∧ S s = sr ∧ S s' = s'r ∧
  ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ s' → S k = S₀ k

theorem pow2Body_runs {x y s s' : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxs' : x ≠ s') (hys : y ≠ s)
    (hys' : y ≠ s') (hss' : s ≠ s') (e : ℕ) (xr yr sr s'r : List Γ') (S₀ : Stacks)
    (i : ℕ) (hi : i < e) (v : St) (S : Stacks) (hI : P2Inv x y s s' e xr yr sr s'r S₀ i v S) :
    (pow2Body x y s s').Runs v S (P2Inv x y s s' e xr yr sr s'r S₀ (i + 1))
      (4 * Nat.log 2 e + 13) := by
  have hsx := hxs.symm
  have hyx := hxy.symm
  have hsy := hys.symm
  have hs'x := hxs'.symm
  have hs'y := hys'.symm
  have hs's := hss'.symm
  obtain ⟨-, -, hx, hy, hs, hs', hF⟩ := hI
  have hl1 : Nat.log 2 (e - i) ≤ Nat.log 2 e := Nat.log_mono_right (by omega)
  have hl2 : Nat.log 2 (e - i - 1) ≤ Nat.log 2 e := Nat.log_mono_right (by omega)
  -- predNum x s'
  have h1 := predNum_correct hxs' (e - i) (by omega) xr v S hx
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * Nat.log 2 e + 8) h1
    fun v₁ S₁ ⟨_, _, hx₁, hs'₁, hf₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- push 0 on y
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * Nat.log 2 e + 7) (Frag.pushSym_runs y (.bit false) v₁ S₁)
    fun v₂ S₂ ⟨hv₂, hS₂⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₂; rw [hv₂]
  -- isZero x s
  have h3 := isZero_correct hxs (e - i - 1) xr v₁ (Function.update S₁ y (.bit false :: S₁ y))
    (by simp [Function.update_of_ne hxy, hx₁])
  refine Frag.runs_mono h3 (fun v₃ S₃ ⟨hfl₃, _, hx₃, hs₃, hf₃⟩ => ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    (by omega)
  · rw [hfl₃, Nat.sub_sub]
  · rw [hx₃]; simp [Function.update_of_ne hxy, hx₁, Nat.sub_sub]
  · rw [hf₃ y hyx hys]; simp [hf₁ y hyx hys', hy, List.replicate_succ]
  · rw [hs₃]; simp [Function.update_of_ne hsy, hf₁ s hsx hss', hs]
  · rw [hf₃ s' hs'x hs's]; simp [Function.update_of_ne hs'y, hs'₁, hs']
  · intro k hkx hky hks hks'
    rw [hf₃ k hkx hks]; simp [Function.update_of_ne hky, hf₁ k hkx hks', hF k hkx hky hks hks']

/-- `pow2` on naturals: consumes `e` from `x`, leaves exactly Mathlib's
encoding of `2 ^ e` on `y`. -/
theorem pow2_correct {x y s s' : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxs' : x ≠ s') (hys : y ≠ s)
    (hys' : y ≠ s') (hss' : s ≠ s') (e : ℕ) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encodeNatΓ' e ++ .comma :: xr) :
    (pow2 x y s s').Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = encodeNatΓ' (2 ^ e) ++ .comma :: S y ∧ S' s = S s ∧ S' s' = S s' ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ s' → S' k = S k)
      ((e + 1) * (4 * Nat.log 2 e + 14)) := by
  have hsx := hxs.symm
  have hyx := hxy.symm
  have hsy := hys.symm
  have hs'x := hxs'.symm
  have hs'y := hys'.symm
  have hs's := hss'.symm
  set TL := e * (4 * Nat.log 2 e + 13 + 1) + 1 with hTL
  -- stage 1: push comma on y
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL + 2 * Nat.log 2 e + 9) (Frag.pushSym_runs y .comma v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by rw [hTL]; ring_nf; omega)
  subst hS₁; rw [hv₁]
  -- stage 2: push 1 on y
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL + 2 * Nat.log 2 e + 8) (Frag.pushSym_runs y (.bit true) v _)
    fun v₂ S₂ ⟨hv₂, hS₂⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₂; rw [hv₂]
  -- stage 3: isZero x s
  have hx₂ : Function.update (Function.update S y (.comma :: S y)) y
      (.bit true :: Function.update S y (.comma :: S y) y) x = encodeNatΓ' e ++ .comma :: xr := by
    simp [Function.update_of_ne hxy, hS]
  have h3 := isZero_correct hxs e xr v _ hx₂
  refine Frag.runs_mono (Frag.seq_runs (t₂ := TL + 1) h3
    fun v₃ S₃ ⟨hfl₃, _, hx₃, hs₃, hf₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 4: the loop
  have hloop := Frag.loop_runs (c := fun v => !v.flag) (B := pow2Body x y s s')
    (P2Inv x y s s' e xr (S y) (S s) (S s') S) e (4 * Nat.log 2 e + 13) (v := v₃) (S := S₃)
    ⟨Nat.zero_le _, by simpa using hfl₃, by rw [hx₃, hx₂]; simp,
      by rw [hf₃ y hyx hys]; simp,
      by rw [hs₃]; simp [Function.update_of_ne hsy],
      by rw [hf₃ s' hs'x hs's]; simp [Function.update_of_ne hs'y],
      fun k hkx hky hks hks' => by rw [hf₃ k hkx hks]; simp [Function.update_of_ne hky]⟩
    (fun i hi w T ⟨_, hfl, _⟩ => by simp [hfl]; omega)
    (fun w T ⟨_, hfl, _⟩ => by simp [hfl])
    (fun i hi w T hI => pow2Body_runs hxy hxs hxs' hys hys' hss' e xr (S y) (S s) (S s') S i hi w T hI)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) hloop
    fun v₄ S₄ ⟨⟨_, _, hx₄, hy₄, hs₄, hs'₄, hF₄⟩, _⟩ => ?_) (fun _ _ h => h) le_rfl
  -- stage 5: drop the zero left on x
  have h5 := dropNum_runs [] xr v₄ S₄ (by rw [hx₄]; simp)
  refine Frag.runs_mono h5 (fun v₅ S₅ ⟨_, _, _, hx₅, hf₅⟩ => ⟨hx₅, ?_, ?_, ?_, ?_⟩) (by simp)
  · rw [hf₅ y hyx, hy₄, encodeNatΓ'_eq, encodeNat_two_pow]; simp
  · rw [hf₅ s hsx, hs₄]
  · rw [hf₅ s' hs'x, hs'₄]
  · intro k hkx hky hks hks'; rw [hf₅ k hkx, hF₄ k hkx hky hks hks']

/-- `pow2` within budget: the output `2 ^ e` has `e + 1 ≤ b` bits. -/
theorem pow2_le_B {x y s s' : K} (hxy : x ≠ y) (hxs : x ≠ s) (hxs' : x ≠ s') (hys : y ≠ s)
    (hys' : y ≠ s') (hss' : s ≠ s') (e b : ℕ) (heb : e < b) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encodeNatΓ' e ++ .comma :: xr) :
    (pow2 x y s s').Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = encodeNatΓ' (2 ^ e) ++ .comma :: S y ∧ S' s = S s ∧ S' s' = S s' ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ s → k ≠ s' → S' k = S k)
      (B b) := by
  refine Frag.runs_mono (pow2_correct hxy hxs hxs' hys hys' hss' e xr v S hS) (fun _ _ h => h) ?_
  have hlog := Nat.log_le_self 2 e
  calc (e + 1) * (4 * Nat.log 2 e + 14) ≤ (b + 2) * (18 * (b + 2)) := Nat.mul_le_mul (by omega) (by omega)
    _ = 18 * (b + 2) ^ 2 := by ring
    _ ≤ B b := quad_le_B (by norm_num)


end Carmichael.TM
