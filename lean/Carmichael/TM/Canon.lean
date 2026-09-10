import Carmichael.TM.MulDiv

/-!
# Route T: canonicalisation and canonical arithmetic wrappers

`mul`/`divmod` (and `add`/`sub`) leave bit lists of the right VALUE on their
result stacks, possibly with high (most significant) zeros.  Route A's specs
are stated against Mathlib's `encodeNatΓ'`, so every consumer needs the
result in canonical form.  This file provides

* `stripHigh`, the reference function (remove the trailing `false` bits of a
  bit list), with `toNat_stripHigh`, `canon_stripHigh`,
  `stripHigh_eq_encodeNat`, `stripHigh_length_le`;
* `canonNum x s`: the fragment turning the top number of `x` (any bit list)
  into `encodeNatΓ' (its value)`, scratch `s` restored, registers `flag`,
  `cmp`, `carry` preserved; `3 * len + 5` steps;
* `mulC`, `divmodC`, `divC`, `modC`: `mul`/`divmod`/`divFrag`/`modFrag`
  followed by `canonNum` on each result, with bit-list `_runs`, ℕ-level
  `_correct` (results EXACTLY `encodeNatΓ' (a * b)`, `encodeNatΓ' (a % d)`,
  `encodeNatΓ' (a / d)`) and `B`-form `_le_B` lemmas.

Machine plan of `canonNum x s`: `pushSym s comma ; moveNum x s` (the bits now
lie reversed on `s`, MSB on top, above the marker) `; stripLoop s` (pop while
the top is `bit false`; a `bit true` or the marker `comma` stops it, peeked,
not consumed) `; pushSym x comma ; moveNum s x` (restores the orientation and
consumes the marker).
-/

namespace Carmichael.TM

open Turing Turing.TM2 Turing.TM2.Stmt Computability

/-! ### Reference function -/

/-- Drop the leading `false` bits (this is what the machine does on the
reversed list, MSB on top). -/
def dropZeros : List Bool → List Bool
  | [] => []
  | false :: l => dropZeros l
  | true :: l => true :: l

theorem dropZeros_eq (m : List Bool) : ∃ n, m = List.replicate n false ++ dropZeros m := by
  induction m using dropZeros.induct with
  | case1 => exact ⟨0, rfl⟩
  | case2 m ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by simp only [dropZeros, List.replicate_succ, List.cons_append]; rw [← hn]⟩
  | case3 m => exact ⟨0, rfl⟩

theorem dropZeros_head? (m : List Bool) : (dropZeros m).head? ≠ some false := by
  induction m using dropZeros.induct with
  | case1 => simp [dropZeros]
  | case2 m ih => simpa [dropZeros] using ih
  | case3 m => simp [dropZeros]

theorem dropZeros_length_le (m : List Bool) : (dropZeros m).length ≤ m.length := by
  induction m using dropZeros.induct with
  | case1 => simp [dropZeros]
  | case2 m ih => simp only [dropZeros, List.length_cons]; omega
  | case3 m => simp [dropZeros]

/-- Remove the trailing (most significant) `false` bits. -/
def stripHigh (l : List Bool) : List Bool := (dropZeros l.reverse).reverse

theorem stripHigh_append_replicate (l : List Bool) :
    ∃ n, l = stripHigh l ++ List.replicate n false := by
  obtain ⟨n, hn⟩ := dropZeros_eq l.reverse
  refine ⟨n, List.reverse_injective ?_⟩
  rw [stripHigh, List.reverse_append, List.reverse_reverse, List.reverse_replicate]
  exact hn

theorem toNat_stripHigh (l : List Bool) : toNat (stripHigh l) = toNat l := by
  obtain ⟨n, hn⟩ := stripHigh_append_replicate l
  conv_rhs => rw [hn]
  rw [toNat_append_replicate_false]

theorem canon_stripHigh (l : List Bool) : Canon (stripHigh l) := by
  rw [Canon, stripHigh, List.getLast?_reverse]
  exact dropZeros_head? _

theorem stripHigh_eq_encodeNat (l : List Bool) :
    stripHigh l = Computability.encodeNat (toNat l) := by
  rw [(canon_stripHigh l).eq_encodeNat, toNat_stripHigh]

theorem stripHigh_length_le (l : List Bool) : (stripHigh l).length ≤ l.length := by
  rw [stripHigh, List.length_reverse]
  exact (dropZeros_length_le _).trans (by simp)

theorem bits_stripHigh (l : List Bool) : bits (stripHigh l) = (bits (dropZeros l.reverse)).reverse := by
  rw [stripHigh, bits_reverse]

/-! ### The strip loop -/

/-- Peek at the top of `s` (into `ra` via `readA`); a `bit false` is popped
and we loop; anything else (a `bit true`, the marker `comma`, an empty stack)
is left in place and ends the fragment. -/
def stripBody {Λ : Type} (s : K) (self e : Λ) : Stmt' Λ :=
  peek s readA
    (branch (fun v => decide (v.ra = some false))
      (pop s (fun v _ => v) (goto fun _ => self))
      (goto fun _ => e))

/-- The strip loop as a fragment (one self-looping label). -/
def stripLoop (s : K) : Frag where
  Λf := Unit
  entry := ()
  code ι e _ := stripBody s (ι ()) e

theorem stripLoop_loop {s : K}
    {Λ : Type} {M : Λ → Stmt' Λ} {ι : Unit → Λ} {e : Λ} (hI : (stripLoop s).Installed M ι e)
    {sr : List Γ'} (m : List Bool) :
    ∀ (v : St) (S : Stacks), S s = bits m ++ .comma :: sr →
    ∃ n, n ≤ m.length + 1 ∧ ∃ v' S',
      RunsTo M n ⟨some (ι ()), v, S⟩ ⟨some e, v', S'⟩ ∧
      v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
      S' s = bits (dropZeros m) ++ .comma :: sr ∧ ∀ k, k ≠ s → S' k = S k := by
  induction m using dropZeros.induct with
  | case1 =>
    intro v S hS
    refine ⟨1, by simp, { v with ra := none, da := true }, S, runsTo_succ ?_ (runsTo_zero M _),
      rfl, rfl, rfl, by simp [dropZeros, hS], fun k _ => rfl⟩
    tm_step () [stripLoop, stripBody, hS]
  | case2 m ih =>
    intro v S hS
    obtain ⟨n, hn, v', S', hr, hfl, hcmp, hcar, hs', hf'⟩ :=
      ih { v with ra := some false } (Function.update S s (bits m ++ .comma :: sr)) (by simp)
    refine ⟨n + 1, ?_, v', S', runsTo_succ ?_ hr, hfl, hcmp, hcar,
      by simpa [dropZeros] using hs', ?_⟩
    · simp only [List.length_cons] at hn ⊢; omega
    · tm_step () [stripLoop, stripBody, hS]
    · intro k hks; rw [hf' k hks]; simp [Function.update_of_ne hks]
  | case3 m =>
    intro v S hS
    refine ⟨1, by simp, { v with ra := some true }, S, runsTo_succ ?_ (runsTo_zero M _),
      rfl, rfl, rfl, by simp [dropZeros, hS], fun k _ => rfl⟩
    tm_step () [stripLoop, stripBody, hS]

theorem stripLoop_runs {s : K} (m : List Bool) (sr : List Γ') (v : St) (S : Stacks)
    (hS : S s = bits m ++ .comma :: sr) :
    (stripLoop s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' s = bits (dropZeros m) ++ .comma :: sr ∧ ∀ k, k ≠ s → S' k = S k)
      (m.length + 1) := by
  constructor
  intro Λ M ι e hI
  exact stripLoop_loop hI m v S hS

/-! ### Canonicalisation fragment -/

/-- Replace the top number of `x` (any bit list) by its canonical form
`encodeNatΓ' (value)`, using scratch `s` (restored). -/
def canonNum (x s : K) : Frag :=
  (Frag.pushSym s .comma).seq ((moveNum x s).seq ((stripLoop s).seq
    ((Frag.pushSym x .comma).seq (moveNum s x))))

theorem canonNum_runs {x s : K} (hxs : x ≠ s) (l : List Bool) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = bits l ++ .comma :: xr) :
    (canonNum x s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' x = encodeNatΓ' (toNat l) ++ .comma :: xr ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ s → S' k = S k)
      (3 * l.length + 5) := by
  have hsx := hxs.symm
  have hlen : (dropZeros l.reverse).length ≤ l.length :=
    (dropZeros_length_le _).trans (by simp)
  -- stage 1: marker on `s`
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * l.length + 4) (Frag.pushSym_runs s .comma v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₁; rw [hv₁]
  -- stage 2: reverse onto `s`
  have h2 := moveNum_runs' hxs l xr v (Function.update S s (.comma :: S s))
    (by simp [Function.update_of_ne hxs, hS])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * l.length + 3) h2
    fun v₂ S₂ ⟨hfl₂, hcmp₂, hcar₂, hx₂, hs₂, hf₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: strip
  have hs₂' : S₂ s = bits l.reverse ++ .comma :: S s := by rw [hs₂]; simp
  have h3 := stripLoop_runs l.reverse (S s) v₂ S₂ hs₂'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length + 2) h3
    fun v₃ S₃ ⟨hfl₃, hcmp₃, hcar₃, hs₃, hf₃⟩ => ?_) (fun _ _ h => h)
    (by simp only [List.length_reverse]; omega)
  -- stage 4: terminator on `x`
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length + 1) (Frag.pushSym_runs x .comma v₃ S₃)
    fun v₄ S₄ ⟨hv₄, hS₄⟩ => ?_) (fun _ _ h => h) (by omega)
  subst hS₄; rw [hv₄]
  -- stage 5: reverse back onto `x`
  have h5 := moveNum_runs' hsx (dropZeros l.reverse) (S s) v₃
    (Function.update S₃ x (.comma :: S₃ x)) (by simp [Function.update_of_ne hsx, hs₃])
  refine Frag.runs_mono h5
    (fun v₅ S₅ ⟨hfl₅, hcmp₅, hcar₅, hs₅, hx₅, hf₅⟩ => ⟨?_, ?_, ?_, ?_, hs₅, ?_⟩) (by omega)
  · rw [hfl₅, hfl₃, hfl₂]
  · rw [hcmp₅, hcmp₃, hcmp₂]
  · rw [hcar₅, hcar₃, hcar₂]
  · rw [hx₅, ← bits_stripHigh, stripHigh_eq_encodeNat, ← encodeNatΓ'_eq]
    simp [hf₃ x hxs, hx₂]
  · intro k hkx hks
    rw [hf₅ k hks hkx, Function.update_of_ne hkx, hf₃ k hks, hf₂ k hkx hks,
      Function.update_of_ne hks]

/-- `canonNum` within budget for a bit list of at most `b` bits. -/
theorem canonNum_le_B {x s : K} (hxs : x ≠ s) (l : List Bool) (b : ℕ) (hl : l.length ≤ b)
    (xr : List Γ') (v : St) (S : Stacks) (hS : S x = bits l ++ .comma :: xr) :
    (canonNum x s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' x = encodeNatΓ' (toNat l) ++ .comma :: xr ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ s → S' k = S k)
      (B b) :=
  Frag.runs_mono (canonNum_runs hxs l xr v S hS) (fun _ _ h => h)
    (le_B_of_le_linear (by omega))

/-- `canonNum` on an already canonical number is the identity. -/
theorem canonNum_correct {x s : K} (hxs : x ≠ s) (a : ℕ) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encodeNatΓ' a ++ .comma :: xr) :
    (canonNum x s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' x = encodeNatΓ' a ++ .comma :: xr ∧ S' s = S s ∧
        ∀ k, k ≠ x → k ≠ s → S' k = S k)
      (3 * Nat.log 2 a + 8) := by
  refine Frag.runs_mono (canonNum_runs hxs (Computability.encodeNat a) xr v S hS)
    (fun v' S' ⟨hfl, hcmp, hcar, hx, hs, hf⟩ => ⟨hfl, hcmp, hcar, ?_, hs, hf⟩) ?_
  · rw [hx, toNat_encodeNat]
  · have := encodeNat_length_le a
    omega

/-! ### Canonical multiplication -/

/-- `w := x * y` in canonical form; consumes `x`, `y`; scratch `s`, `t` restored. -/
def mulC (x y w s t : K) : Frag := (mul x y w s t).seq (canonNum w s)

theorem mulC_runs {x y w s t : K} (hxy : x ≠ y) (hxw : x ≠ w) (hxs : x ≠ s) (hxt : x ≠ t)
    (hyw : y ≠ w) (hys : y ≠ s) (hyt : y ≠ t) (hws : w ≠ s) (hwt : w ≠ t) (hst : s ≠ t)
    (xs ys : List Bool) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ys ++ .comma :: yr) :
    (mulC x y w s t).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ S' w = encodeNatΓ' (toNat xs * toNat ys) ++ .comma :: S w ∧
        S' s = S s ∧ S' t = S t ∧ ∀ k, k ≠ x → k ≠ y → k ≠ w → k ≠ s → k ≠ t → S' k = S k)
      (ys.length * (4 * xs.length + 6 * ys.length + 14) + 4 * xs.length + 7 * ys.length + 9) := by
  have hlen := mulGo_length [] xs ys
  simp only [List.length_nil, Nat.zero_max] at hlen
  have h1 := mul_runs hxy hxw hxs hxt hyw hys hyt hws hwt hst xs ys xr yr v S hSx hSy
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * (mulGo [] xs ys).length + 5) h1
    fun v₁ S₁ ⟨hx₁, hy₁, hw₁, hs₁, ht₁, hf₁⟩ => ?_) (fun _ _ h => h) (by omega)
  have h2 := canonNum_runs hws (mulGo [] xs ys) (S w) v₁ S₁ hw₁
  refine Frag.runs_mono h2 (fun v₂ S₂ ⟨_, _, _, hw₂, hs₂, hf₂⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
  · rw [hf₂ x hxw hxs, hx₁]
  · rw [hf₂ y hyw hys, hy₁]
  · rw [hw₂, toNat_mulGo]; simp [toNat]
  · rw [hs₂, hs₁]
  · rw [hf₂ t hwt.symm hst.symm, ht₁]
  · intro k hkx hky hkw hks hkt
    rw [hf₂ k hkw hks, hf₁ k hkx hky hkw hks hkt]

/-- Canonical multiplication on naturals: `w` gets EXACTLY `encodeNatΓ' (a * b)`. -/
theorem mulC_correct {x y w s t : K} (hxy : x ≠ y) (hxw : x ≠ w) (hxs : x ≠ s) (hxt : x ≠ t)
    (hyw : y ≠ w) (hys : y ≠ s) (hyt : y ≠ t) (hws : w ≠ s) (hwt : w ≠ t) (hst : s ≠ t)
    (a b : ℕ) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' b ++ .comma :: yr) :
    (mulC x y w s t).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ S' w = encodeNatΓ' (a * b) ++ .comma :: S w ∧
        S' s = S s ∧ S' t = S t ∧ ∀ k, k ≠ x → k ≠ y → k ≠ w → k ≠ s → k ≠ t → S' k = S k)
      ((Nat.log 2 b + 1) * (4 * Nat.log 2 a + 6 * Nat.log 2 b + 24) +
        4 * Nat.log 2 a + 7 * Nat.log 2 b + 20) := by
  have h := mulC_runs hxy hxw hxs hxt hyw hys hyt hws hwt hst (Computability.encodeNat a)
    (Computability.encodeNat b) xr yr v S hSx hSy
  refine Frag.runs_mono h (fun v' S' ⟨hx, hy, hw, hs, ht, hf⟩ =>
    ⟨hx, hy, by rw [hw, toNat_encodeNat, toNat_encodeNat], hs, ht, hf⟩) ?_
  have ha := encodeNat_length_le a
  have hb := encodeNat_length_le b
  have := Nat.mul_le_mul hb (show 4 * (Computability.encodeNat a).length +
    6 * (Computability.encodeNat b).length + 14 ≤ 4 * Nat.log 2 a + 6 * Nat.log 2 b + 24 by omega)
  omega

/-- `mulC` within budget for operands below `2 ^ m`. -/
theorem mulC_le_B {x y w s t : K} (hxy : x ≠ y) (hxw : x ≠ w) (hxs : x ≠ s) (hxt : x ≠ t)
    (hyw : y ≠ w) (hys : y ≠ s) (hyt : y ≠ t) (hws : w ≠ s) (hwt : w ≠ t) (hst : s ≠ t)
    (a b m : ℕ) (ha : a < 2 ^ m) (hb : b < 2 ^ m) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' b ++ .comma :: yr) :
    (mulC x y w s t).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ S' w = encodeNatΓ' (a * b) ++ .comma :: S w ∧
        S' s = S s ∧ S' t = S t ∧ ∀ k, k ≠ x → k ≠ y → k ≠ w → k ≠ s → k ≠ t → S' k = S k)
      (B m) := by
  have h := mulC_runs hxy hxw hxs hxt hyw hys hyt hws hwt hst (Computability.encodeNat a)
    (Computability.encodeNat b) xr yr v S hSx hSy
  refine Frag.runs_mono h (fun v' S' ⟨hx, hy, hw, hs, ht, hf⟩ =>
    ⟨hx, hy, by rw [hw, toNat_encodeNat, toNat_encodeNat], hs, ht, hf⟩) ?_
  have ha := encodeNat_length_le_of_lt_pow ha
  have hb := encodeNat_length_le_of_lt_pow hb
  have := Nat.mul_le_mul hb (show 4 * (Computability.encodeNat a).length +
    6 * (Computability.encodeNat b).length + 14 ≤ 10 * m + 14 by omega)
  apply le_B_of_le_quad
  nlinarith

/-! ### Canonical division with remainder -/

/-- `divmod` followed by canonicalisation of the remainder (on `x`) and of
the quotient (on `q`). -/
def divmodC (x y q j s t : K) : Frag :=
  (divmod x y q j s t).seq ((canonNum x s).seq (canonNum q s))

/-- `divFrag` followed by canonicalisation of the quotient (on `q`). -/
def divC (x y q j s t : K) : Frag := (divFrag x y q j s t).seq (canonNum q s)

/-- `modFrag` followed by canonicalisation of the remainder (on `x`). -/
def modC (x y q j s t : K) : Frag := (modFrag x y q j s t).seq (canonNum x s)

/-- The common step-bound bookkeeping for the canonical division wrappers
(`c = 14`, constant `37`): bit lengths to `Nat.log`. -/
theorem canonDivBound_log (a d : ℕ) :
    (Computability.encodeNat a).length *
        (23 * ((Computability.encodeNat a).length + (Computability.encodeNat d).length) + 60) +
      14 * ((Computability.encodeNat a).length + (Computability.encodeNat d).length) + 37 ≤
    (Nat.log 2 a + 1) * (23 * (Nat.log 2 a + Nat.log 2 d + 2) + 60) +
      14 * (Nat.log 2 a + Nat.log 2 d + 2) + 37 := by
  have ha := encodeNat_length_le a
  have hd := encodeNat_length_le d
  have h1 := Nat.mul_le_mul ha (show 23 * ((Computability.encodeNat a).length +
    (Computability.encodeNat d).length) + 60 ≤ 23 * (Nat.log 2 a + Nat.log 2 d + 2) + 60 by omega)
  omega

/-- The same bookkeeping, bit lengths below `m` → `B m`. -/
theorem canonDivBound_B {a d m : ℕ} (ha : a < 2 ^ m) (hd : d < 2 ^ m) :
    (Computability.encodeNat a).length *
        (23 * ((Computability.encodeNat a).length + (Computability.encodeNat d).length) + 60) +
      14 * ((Computability.encodeNat a).length + (Computability.encodeNat d).length) + 37 ≤ B m := by
  have ha := encodeNat_length_le_of_lt_pow ha
  have hd := encodeNat_length_le_of_lt_pow hd
  have h1 := Nat.mul_le_mul ha (show 23 * ((Computability.encodeNat a).length +
    (Computability.encodeNat d).length) + 60 ≤ 46 * m + 60 by omega)
  apply le_B_of_le_quad
  nlinarith

theorem divmodC_runs {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (xs ds : List Bool) (hd : 1 ≤ toNat ds) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ds ++ .comma :: yr) :
    (divmodC x y q j s t).Runs v S (fun _ S' =>
        S' x = encodeNatΓ' (toNat xs % toNat ds) ++ .comma :: xr ∧ S' y = yr ∧
        S' q = encodeNatΓ' (toNat xs / toNat ds) ++ .comma :: S q ∧
        S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      (xs.length * (23 * (xs.length + ds.length) + 60) + 14 * (xs.length + ds.length) + 37) := by
  have h1 := divmod_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    xs ds hd xr yr v S hSx hSy
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 6 * (xs.length + ds.length) + 10) h1
    fun v₁ S₁ ⟨⟨rl, hrl, hrv, hx₁⟩, hy₁, ⟨ql, hql, hqv, hq₁⟩, hj₁, hs₁, ht₁, hf₁⟩ => ?_)
    (fun _ _ h => h) (by omega)
  have h2 := canonNum_runs hxs rl xr v₁ S₁ hx₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * xs.length + 5) h2
    fun v₂ S₂ ⟨_, _, _, hx₂, hs₂, hf₂⟩ => ?_) (fun _ _ h => h) (by omega)
  have hq₂ : S₂ q = bits ql ++ .comma :: S q := by rw [hf₂ q hxq.symm hqs, hq₁]
  have h3 := canonNum_runs hqs ql (S q) v₂ S₂ hq₂
  refine Frag.runs_mono h3
    (fun v₃ S₃ ⟨_, _, _, hq₃, hs₃, hf₃⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) (by omega)
  · rw [hf₃ x hxq hxs, hx₂, hrv]
  · rw [hf₃ y hyq hys, hf₂ y hxy.symm hys, hy₁]
  · rw [hq₃, hqv]
  · rw [hf₃ j hqj.symm hjs, hf₂ j hxj.symm hjs, hj₁]
  · rw [hs₃, hs₂, hs₁]
  · rw [hf₃ t hqt.symm hst.symm, hf₂ t hxt.symm hst.symm, ht₁]
  · intro k hkx hky hkq hkj hks hkt
    rw [hf₃ k hkq hks, hf₂ k hkx hks, hf₁ k hkx hky hkq hkj hks hkt]

theorem divC_runs {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (xs ds : List Bool) (hd : 1 ≤ toNat ds) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ds ++ .comma :: yr) :
    (divC x y q j s t).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ S' q = encodeNatΓ' (toNat xs / toNat ds) ++ .comma :: S q ∧
        S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      (xs.length * (23 * (xs.length + ds.length) + 60) + 14 * (xs.length + ds.length) + 37) := by
  have h1 := divFrag_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    xs ds hd xr yr v S hSx hSy
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * xs.length + 5) h1
    fun v₁ S₁ ⟨hx₁, hy₁, ⟨ql, hql, hqv, hq₁⟩, hj₁, hs₁, ht₁, hf₁⟩ => ?_)
    (fun _ _ h => h) (by omega)
  have h2 := canonNum_runs hqs ql (S q) v₁ S₁ hq₁
  refine Frag.runs_mono h2
    (fun v₂ S₂ ⟨_, _, _, hq₂, hs₂, hf₂⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) (by omega)
  · rw [hf₂ x hxq hxs, hx₁]
  · rw [hf₂ y hyq hys, hy₁]
  · rw [hq₂, hqv]
  · rw [hf₂ j hqj.symm hjs, hj₁]
  · rw [hs₂, hs₁]
  · rw [hf₂ t hqt.symm hst.symm, ht₁]
  · intro k hkx hky hkq hkj hks hkt
    rw [hf₂ k hkq hks, hf₁ k hkx hky hkq hkj hks hkt]

theorem modC_runs {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (xs ds : List Bool) (hd : 1 ≤ toNat ds) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = bits xs ++ .comma :: xr) (hSy : S y = bits ds ++ .comma :: yr) :
    (modC x y q j s t).Runs v S (fun _ S' =>
        S' x = encodeNatΓ' (toNat xs % toNat ds) ++ .comma :: xr ∧ S' y = yr ∧
        S' q = S q ∧ S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      (xs.length * (23 * (xs.length + ds.length) + 60) + 14 * (xs.length + ds.length) + 37) := by
  have h1 := modFrag_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    xs ds hd xr yr v S hSx hSy
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * (xs.length + ds.length) + 5) h1
    fun v₁ S₁ ⟨⟨rl, hrl, hrv, hx₁⟩, hy₁, hq₁, hj₁, hs₁, ht₁, hf₁⟩ => ?_)
    (fun _ _ h => h) (by omega)
  have h2 := canonNum_runs hxs rl xr v₁ S₁ hx₁
  refine Frag.runs_mono h2
    (fun v₂ S₂ ⟨_, _, _, hx₂, hs₂, hf₂⟩ => ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩) (by omega)
  · rw [hx₂, hrv]
  · rw [hf₂ y hxy.symm hys, hy₁]
  · rw [hf₂ q hxq.symm hqs, hq₁]
  · rw [hf₂ j hxj.symm hjs, hj₁]
  · rw [hs₂, hs₁]
  · rw [hf₂ t hxt.symm hst.symm, ht₁]
  · intro k hkx hky hkq hkj hks hkt
    rw [hf₂ k hkx hks, hf₁ k hkx hky hkq hkj hks hkt]

/-- Canonical division with remainder on naturals (`1 ≤ d`): `x` gets EXACTLY
`encodeNatΓ' (a % d)`, `q` gets EXACTLY `encodeNatΓ' (a / d)`; `d` is consumed. -/
theorem divmodC_correct {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (a d : ℕ) (hd : 1 ≤ d) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' d ++ .comma :: yr) :
    (divmodC x y q j s t).Runs v S (fun _ S' =>
        S' x = encodeNatΓ' (a % d) ++ .comma :: xr ∧ S' y = yr ∧
        S' q = encodeNatΓ' (a / d) ++ .comma :: S q ∧
        S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      ((Nat.log 2 a + 1) * (23 * (Nat.log 2 a + Nat.log 2 d + 2) + 60) +
        14 * (Nat.log 2 a + Nat.log 2 d + 2) + 37) := by
  have h := divmodC_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    (Computability.encodeNat a) (Computability.encodeNat d) (by rw [toNat_encodeNat]; exact hd)
    xr yr v S hSx hSy
  refine Frag.runs_mono h (fun _ S' ⟨hx, hy, hq, hj, hs, ht, hf⟩ =>
    ⟨by rw [hx, toNat_encodeNat, toNat_encodeNat], hy,
      by rw [hq, toNat_encodeNat, toNat_encodeNat], hj, hs, ht, hf⟩) (canonDivBound_log a d)

/-- `divmodC` within budget for operands below `2 ^ m`. -/
theorem divmodC_le_B {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (a d m : ℕ) (hd : 1 ≤ d) (ha : a < 2 ^ m) (hdm : d < 2 ^ m) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' d ++ .comma :: yr) :
    (divmodC x y q j s t).Runs v S (fun _ S' =>
        S' x = encodeNatΓ' (a % d) ++ .comma :: xr ∧ S' y = yr ∧
        S' q = encodeNatΓ' (a / d) ++ .comma :: S q ∧
        S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      (B m) := by
  have h := divmodC_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    (Computability.encodeNat a) (Computability.encodeNat d) (by rw [toNat_encodeNat]; exact hd)
    xr yr v S hSx hSy
  refine Frag.runs_mono h (fun _ S' ⟨hx, hy, hq, hj, hs, ht, hf⟩ =>
    ⟨by rw [hx, toNat_encodeNat, toNat_encodeNat], hy,
      by rw [hq, toNat_encodeNat, toNat_encodeNat], hj, hs, ht, hf⟩) (canonDivBound_B ha hdm)

/-- Canonical quotient on naturals (`1 ≤ d`): `q` gets EXACTLY `encodeNatΓ' (a / d)`;
`a`, `d` are consumed. -/
theorem divC_correct {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (a d : ℕ) (hd : 1 ≤ d) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' d ++ .comma :: yr) :
    (divC x y q j s t).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ S' q = encodeNatΓ' (a / d) ++ .comma :: S q ∧
        S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      ((Nat.log 2 a + 1) * (23 * (Nat.log 2 a + Nat.log 2 d + 2) + 60) +
        14 * (Nat.log 2 a + Nat.log 2 d + 2) + 37) := by
  have h := divC_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    (Computability.encodeNat a) (Computability.encodeNat d) (by rw [toNat_encodeNat]; exact hd)
    xr yr v S hSx hSy
  refine Frag.runs_mono h (fun _ S' ⟨hx, hy, hq, hj, hs, ht, hf⟩ =>
    ⟨hx, hy, by rw [hq, toNat_encodeNat, toNat_encodeNat], hj, hs, ht, hf⟩) (canonDivBound_log a d)

/-- `divC` within budget for operands below `2 ^ m`. -/
theorem divC_le_B {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (a d m : ℕ) (hd : 1 ≤ d) (ha : a < 2 ^ m) (hdm : d < 2 ^ m) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' d ++ .comma :: yr) :
    (divC x y q j s t).Runs v S (fun _ S' =>
        S' x = xr ∧ S' y = yr ∧ S' q = encodeNatΓ' (a / d) ++ .comma :: S q ∧
        S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      (B m) := by
  have h := divC_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    (Computability.encodeNat a) (Computability.encodeNat d) (by rw [toNat_encodeNat]; exact hd)
    xr yr v S hSx hSy
  refine Frag.runs_mono h (fun _ S' ⟨hx, hy, hq, hj, hs, ht, hf⟩ =>
    ⟨hx, hy, by rw [hq, toNat_encodeNat, toNat_encodeNat], hj, hs, ht, hf⟩) (canonDivBound_B ha hdm)

/-- Canonical remainder on naturals (`1 ≤ d`): `x` gets EXACTLY `encodeNatΓ' (a % d)`;
`d` is consumed, `q` untouched. -/
theorem modC_correct {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (a d : ℕ) (hd : 1 ≤ d) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' d ++ .comma :: yr) :
    (modC x y q j s t).Runs v S (fun _ S' =>
        S' x = encodeNatΓ' (a % d) ++ .comma :: xr ∧ S' y = yr ∧
        S' q = S q ∧ S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      ((Nat.log 2 a + 1) * (23 * (Nat.log 2 a + Nat.log 2 d + 2) + 60) +
        14 * (Nat.log 2 a + Nat.log 2 d + 2) + 37) := by
  have h := modC_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    (Computability.encodeNat a) (Computability.encodeNat d) (by rw [toNat_encodeNat]; exact hd)
    xr yr v S hSx hSy
  refine Frag.runs_mono h (fun _ S' ⟨hx, hy, hq, hj, hs, ht, hf⟩ =>
    ⟨by rw [hx, toNat_encodeNat, toNat_encodeNat], hy, hq, hj, hs, ht, hf⟩) (canonDivBound_log a d)

/-- `modC` within budget for operands below `2 ^ m`. -/
theorem modC_le_B {x y q j s t : K} (hxy : x ≠ y) (hxq : x ≠ q) (hxj : x ≠ j) (hxs : x ≠ s)
    (hxt : x ≠ t) (hyq : y ≠ q) (hyj : y ≠ j) (hys : y ≠ s) (hyt : y ≠ t) (hqj : q ≠ j) (hqs : q ≠ s)
    (hqt : q ≠ t) (hjs : j ≠ s) (hjt : j ≠ t) (hst : s ≠ t)
    (a d m : ℕ) (hd : 1 ≤ d) (ha : a < 2 ^ m) (hdm : d < 2 ^ m) (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encodeNatΓ' a ++ .comma :: xr) (hSy : S y = encodeNatΓ' d ++ .comma :: yr) :
    (modC x y q j s t).Runs v S (fun _ S' =>
        S' x = encodeNatΓ' (a % d) ++ .comma :: xr ∧ S' y = yr ∧
        S' q = S q ∧ S' j = S j ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ y → k ≠ q → k ≠ j → k ≠ s → k ≠ t → S' k = S k)
      (B m) := by
  have h := modC_runs hxy hxq hxj hxs hxt hyq hyj hys hyt hqj hqs hqt hjs hjt hst
    (Computability.encodeNat a) (Computability.encodeNat d) (by rw [toNat_encodeNat]; exact hd)
    xr yr v S hSx hSy
  refine Frag.runs_mono h (fun _ S' ⟨hx, hy, hq, hj, hs, ht, hf⟩ =>
    ⟨by rw [hx, toNat_encodeNat, toNat_encodeNat], hy, hq, hj, hs, ht, hf⟩) (canonDivBound_B ha hdm)

end Carmichael.TM
