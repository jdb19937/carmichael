import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype

/-!
# Route T framework: TM2 fragments with step counts

The machine shape is fixed once for the whole campaign:

* `K = Fin 8` stacks, all over Mathlib's TM alphabet `Computability.Γ'`
  (`blank | bit b | bra | ket | comma`): bits carry numbers, `comma` is the
  number terminator, `bra` is a spare marker, `ket`/`blank` are free;
* `St`, a small record of flags/registers, is the internal state `σ`.

A **fragment** (`Frag`) is a piece of TM2 program with its own finite label
type `Λf`, an entry label, and code parametrised over the ambient label type
`Λ`, an embedding `ι : Λf → Λ` of the fragment's labels, and an exit label
`e : Λ`.  Internal jumps go through `ι`, the continuation jump goes to `e`.
`Frag.Installed F M ι e` says the ambient program `M` agrees with `F.code ι e`
on `ι`'s image; `Frag.Runs F v S Q t` is a Hoare-style triple: in every
ambient machine in which `F` is installed, starting at `ι F.entry` with state
`v` and stacks `S`, the machine reaches the exit label with some `v'`, `S'`
satisfying `Q` in at most `t` steps (a step = one `TM2.step`, i.e. one label
executed).

Combinators: `seq` (labels `Λf ⊕ Λg`, `f`'s exit is `g`'s entry), `loop`
(labels `Option Λb`; `none` is the test label, `branch c` on the internal
state), and `toFinTM2` which closes a fragment off into Mathlib's `FinTM2`
(labels `Option Λf`, `none` resets the state and halts) so that
`TM2OutputsInTime` follows from a `Runs` triple.
-/

namespace Carmichael.TM

open Turing Turing.TM2 Turing.TM2.Stmt StateTransition Computability

/-! ### The machine shape -/

/-- Stack index type: eight stacks (headroom for the campaign). -/
abbrev K := Fin 8

/-- All stacks carry the same alphabet, Mathlib's `Computability.Γ'`
(so that `TM2ComputableInTime` can be stated against `encodingNatΓ'`). -/
abbrev Γ : K → Type := fun _ => Γ'

/-- The internal state: registers read from stacks, "done" flags, a carry,
a comparison result, and a spare flag. -/
structure St where
  carry : Bool := false
  ra : Option Bool := none
  rb : Option Bool := none
  da : Bool := false
  db : Bool := false
  cmp : Ordering := .eq
  flag : Bool := false
  deriving DecidableEq

instance : Inhabited St := ⟨{}⟩

/-- `St` as a product, for finiteness. -/
def St.equivProd : St ≃ Bool × Option Bool × Option Bool × Bool × Bool × Ordering × Bool where
  toFun v := (v.carry, v.ra, v.rb, v.da, v.db, v.cmp, v.flag)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1, p.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype St := Fintype.ofEquiv _ St.equivProd.symm

/-- Stack contents. -/
abbrev Stacks := ∀ k : K, List (Γ k)

/-- Statements over the fixed shape, for an ambient label type `Λ`. -/
abbrev Stmt' (Λ : Type) := TM2.Stmt Γ Λ St

/-- Configurations over the fixed shape. -/
abbrev Cfg' (Λ : Type) := TM2.Cfg Γ Λ St

/-! ### Exact step counting -/

/-- `RunsTo M n c c'`: iterating `TM2.step M` exactly `n` times from `c`
reaches `c'` (in particular no halt in between).  This is the iterate
`StateTransition.EvalsTo` uses, so it converts to `TM2OutputsInTime` for free. -/
def RunsTo {Λ : Type} (M : Λ → Stmt' Λ) (n : ℕ) (c c' : Cfg' Λ) : Prop :=
  (flip bind (TM2.step M))^[n] (some c) = some c'

theorem runsTo_zero {Λ : Type} (M : Λ → Stmt' Λ) (c : Cfg' Λ) : RunsTo M 0 c c := rfl

theorem runsTo_succ {Λ : Type} {M : Λ → Stmt' Λ} {n : ℕ} {c c₁ c' : Cfg' Λ}
    (h : TM2.step M c = some c₁) (h' : RunsTo M n c₁ c') : RunsTo M (n + 1) c c' := by
  unfold RunsTo at *
  rw [Function.iterate_succ_apply]
  simpa [flip, h] using h'

theorem runsTo_trans {Λ : Type} {M : Λ → Stmt' Λ} {n₁ n₂ : ℕ} {c c₁ c₂ : Cfg' Λ}
    (h₁ : RunsTo M n₁ c c₁) (h₂ : RunsTo M n₂ c₁ c₂) : RunsTo M (n₁ + n₂) c c₂ := by
  unfold RunsTo at *
  rw [add_comm, Function.iterate_add_apply, h₁, h₂]

/-- One step from a labelled configuration executes the label's statement. -/
theorem step_label {Λ : Type} (M : Λ → Stmt' Λ) (l : Λ) (v : St) (S : Stacks) :
    TM2.step M ⟨some l, v, S⟩ = some (stepAux (M l) v S) := rfl

/-- `tm_step l [facts]`: simulate one step of the fragment installed by the
local hypothesis `hI : F.Installed M ι e` at internal label `l`, then `simp`
with the given facts (typically the fragment's definitions, the stack-content
hypotheses, register facts and stack-distinctness facts).
`tm_step l only [defs, h₁, h₂] [facts]` first runs `simp only [defs, h₁, h₂]`
(unfolding the fragment and rewriting with read-phase equations such as
`OpA.read`) before the general `simp`.  Requires `hI` to be named `hI`. -/
syntax "tm_step" term:max (" only " Lean.Parser.Tactic.simpArgs)? (Lean.Parser.Tactic.simpArgs)? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| tm_step $l $[only [$os,*]]? $[[$args,*]]?) => do
    let args := args.map (·.getElems) |>.getD #[]
    match os with
    | some os => `(tactic| (erw [step_label, hI $l]; simp only [$os,*]; simp [$args,*]))
    | none => `(tactic| (erw [step_label, hI $l]; simp [$args,*]))

/-! ### Fragments -/

/-- A program fragment: finite internal labels, an entry label, and code
parametrised by the ambient label type, the embedding of internal labels,
and the exit label. -/
structure Frag where
  /-- internal labels -/
  Λf : Type
  [fin : Fintype Λf]
  /-- entry label -/
  entry : Λf
  /-- code for each internal label, given the embedding `ι` and exit `e` -/
  code : ∀ {Λ : Type}, (Λf → Λ) → Λ → Λf → Stmt' Λ

attribute [instance] Frag.fin

namespace Frag

/-- `F` is installed in the ambient program `M` along `ι` with exit `e`. -/
def Installed (F : Frag) {Λ : Type} (M : Λ → Stmt' Λ) (ι : F.Λf → Λ) (e : Λ) : Prop :=
  ∀ l, M (ι l) = F.code ι e l

/-- Hoare triple with a step bound: wherever `F` is installed, from
`⟨ι F.entry, v, S⟩` the machine reaches `⟨e, v', S'⟩` with `Q v' S'`
in at most `t` steps. -/
structure Runs (F : Frag) (v : St) (S : Stacks) (Q : St → Stacks → Prop) (t : ℕ) : Prop where
  run : ∀ {Λ : Type} (M : Λ → Stmt' Λ) (ι : F.Λf → Λ) (e : Λ), F.Installed M ι e →
    ∃ n, n ≤ t ∧ ∃ v' S', RunsTo M n ⟨some (ι F.entry), v, S⟩ ⟨some e, v', S'⟩ ∧ Q v' S'

theorem runs_mono {F : Frag} {v S Q Q' t t'} (h : F.Runs v S Q t)
    (hQ : ∀ v S, Q v S → Q' v S) (ht : t ≤ t') : F.Runs v S Q' t' := by
  constructor
  intro Λ M ι e hI
  obtain ⟨n, hn, v', S', hr, hQ'⟩ := h.run M ι e hI
  exact ⟨n, hn.trans ht, v', S', hr, hQ v' S' hQ'⟩

/-! #### Sequencing -/

/-- Run `F`, then `G`.  Labels `F.Λf ⊕ G.Λf`; `F`'s exit is `G`'s entry. -/
def seq (F G : Frag) : Frag where
  Λf := F.Λf ⊕ G.Λf
  entry := Sum.inl F.entry
  code ι e
    | Sum.inl l => F.code (ι ∘ Sum.inl) (ι (Sum.inr G.entry)) l
    | Sum.inr l => G.code (ι ∘ Sum.inr) e l

theorem seq_installed_left {F G : Frag} {Λ : Type} {M : Λ → Stmt' Λ} {ι e}
    (h : (F.seq G).Installed M ι e) :
    F.Installed M (ι ∘ Sum.inl) (ι (Sum.inr G.entry)) :=
  fun l => h (Sum.inl l)

theorem seq_installed_right {F G : Frag} {Λ : Type} {M : Λ → Stmt' Λ} {ι e}
    (h : (F.seq G).Installed M ι e) :
    G.Installed M (ι ∘ Sum.inr) e :=
  fun l => h (Sum.inr l)

/-- Sequencing adds step bounds exactly (no extra transition: `F`'s final
`goto` lands directly on `G`'s entry). -/
theorem seq_runs {F G : Frag} {v S Q₁ Q₂ t₁ t₂}
    (hF : F.Runs v S Q₁ t₁) (hG : ∀ v' S', Q₁ v' S' → G.Runs v' S' Q₂ t₂) :
    (F.seq G).Runs v S Q₂ (t₁ + t₂) := by
  constructor
  intro Λ M ι e hI
  obtain ⟨n₁, hn₁, v₁, S₁, hr₁, hQ₁⟩ := hF.run M _ _ (seq_installed_left hI)
  obtain ⟨n₂, hn₂, v₂, S₂, hr₂, hQ₂⟩ := (hG v₁ S₁ hQ₁).run M _ _ (seq_installed_right hI)
  exact ⟨n₁ + n₂, by omega, v₂, S₂, runsTo_trans hr₁ hr₂, hQ₂⟩

/-! #### Bounded loop -/

/-- `while c(state) do B`.  Labels `Option B.Λf`; `none` is the test label,
which costs one step per test; `B`'s exit is the test label. -/
def loop (c : St → Bool) (B : Frag) : Frag where
  Λf := Option B.Λf
  entry := none
  code ι e
    | none => branch c (goto fun _ => ι (some B.entry)) (goto fun _ => e)
    | some l => B.code (ι ∘ some) (ι none) l

theorem loop_installed_body {c : St → Bool} {B : Frag} {Λ : Type} {M : Λ → Stmt' Λ} {ι e}
    (h : (loop c B).Installed M ι e) : B.Installed M (ι ∘ some) (ι none) :=
  fun l => h (some l)

/-- Loop rule with an indexed invariant `I i` (iteration `i` of `n`), a per-iteration
step bound `t` for the body, and total bound `n * (t + 1) + 1`. -/
theorem loop_runs {c : St → Bool} {B : Frag} (I : ℕ → St → Stacks → Prop) (n t : ℕ) {v S}
    (h0 : I 0 v S)
    (hc : ∀ i < n, ∀ v S, I i v S → c v = true)
    (hn : ∀ v S, I n v S → c v = false)
    (hb : ∀ i < n, ∀ v S, I i v S → B.Runs v S (I (i + 1)) t) :
    (loop c B).Runs v S (fun v S => I n v S ∧ c v = false) (n * (t + 1) + 1) := by
  constructor
  intro Λ M ι e hI
  suffices key : ∀ m i, i + m = n → ∀ v S, I i v S →
      ∃ n', n' ≤ m * (t + 1) + 1 ∧ ∃ v' S',
        RunsTo M n' ⟨some (ι none), v, S⟩ ⟨some e, v', S'⟩ ∧ I n v' S' ∧ c v' = false from
    key n 0 (by omega) v S h0
  intro m
  induction m with
  | zero =>
    intro i hi v S hIv
    obtain rfl : i = n := by omega
    have hcv := hn v S hIv
    refine ⟨1, by omega, v, S, ?_, hIv, hcv⟩
    refine runsTo_succ ?_ (runsTo_zero M _)
    tm_step none [loop, hcv]
  | succ m ih =>
    intro i hi v S hIv
    have hcv := hc i (by omega) v S hIv
    obtain ⟨n₁, hn₁, v₁, S₁, hr₁, hI₁⟩ :=
      (hb i (by omega) v S hIv).run M _ _ (loop_installed_body hI)
    obtain ⟨n₂, hn₂, v₂, S₂, hr₂, hI₂, hc₂⟩ := ih (i + 1) (by omega) v₁ S₁ hI₁
    refine ⟨n₁ + n₂ + 1, ?_, v₂, S₂, ?_, hI₂, hc₂⟩
    · rw [add_mul, one_mul]; omega
    · refine runsTo_succ ?_ (runsTo_trans hr₁ hr₂)
      tm_step none [loop, hcv, Function.comp]

/-! #### One-statement fragments -/

/-- A fragment with a single label executing `q` followed by `goto exit`. -/
def straight (q : ∀ {Λ : Type}, Stmt' Λ → Stmt' Λ) : Frag where
  Λf := Unit
  entry := ()
  code _ e _ := q (goto fun _ => e)

/-- Push a fixed symbol on stack `k`. -/
def pushSym (k : K) (s : Γ') : Frag := straight (push k (fun _ => s))

/-- Apply a state transformation. -/
def load' (f : St → St) : Frag := straight (load f)

theorem pushSym_runs (k : K) (s : Γ') (v : St) (S : Stacks) :
    (pushSym k s).Runs v S (fun v' S' => v' = v ∧ S' = Function.update S k (s :: S k)) 1 := by
  constructor
  intro Λ M ι e hI
  refine ⟨1, le_rfl, v, Function.update S k (s :: S k), ?_, rfl, rfl⟩
  refine runsTo_succ ?_ (runsTo_zero M _)
  tm_step () [pushSym, straight]

theorem load'_runs (f : St → St) (v : St) (S : Stacks) :
    (load' f).Runs v S (fun v' S' => v' = f v ∧ S' = S) 1 := by
  constructor
  intro Λ M ι e hI
  refine ⟨1, le_rfl, f v, S, ?_, rfl, rfl⟩
  refine runsTo_succ ?_ (runsTo_zero M _)
  tm_step () [load', straight]

/-! #### Closing off into a `FinTM2` -/

/-- The stacks with `l` on stack `k₀` and everything else empty. -/
def initStacks (k₀ : K) (l : List Γ') : Stacks := fun k => if k = k₀ then l else []

/-- The bundled machine: labels `Option F.Λf`, `F` installed along `some`
with exit `none`; the exit label resets the state to `v₀` and halts. -/
def toFinTM2 (F : Frag) (k₀ k₁ : K) (v₀ : St) : FinTM2 where
  K := K
  k₀ := k₀
  k₁ := k₁
  Γ := Γ
  Λ := Option F.Λf
  main := some F.entry
  σ := St
  initialState := v₀
  m
    | some l => F.code some none l
    | none => load (fun _ => v₀) halt

theorem toFinTM2_installed (F : Frag) (k₀ k₁ : K) (v₀ : St) :
    F.Installed (F.toFinTM2 k₀ k₁ v₀).m some none :=
  fun _ => rfl

theorem initList_toFinTM2 (F : Frag) (k₀ k₁ : K) (v₀ : St) (l : List Γ') :
    initList (F.toFinTM2 k₀ k₁ v₀) l = ⟨some (some F.entry), v₀, initStacks k₀ l⟩ := by
  unfold initList initStacks
  congr 1

theorem haltList_toFinTM2 (F : Frag) (k₀ k₁ : K) (v₀ : St) (l : List Γ') :
    haltList (F.toFinTM2 k₀ k₁ v₀) l = ⟨none, v₀, initStacks k₁ l⟩ := by
  unfold haltList initStacks
  congr 1

/-- Data-level `EvalsToInTime` from a Prop-level existence statement. -/
noncomputable def _root_.StateTransition.EvalsToInTime.ofExists {α : Type*} {f : α → Option α}
    {a : α} {b : Option α} {m : ℕ} (h : ∃ n, n ≤ m ∧ (flip bind f)^[n] (some a) = b) :
    EvalsToInTime f a b m :=
  ⟨⟨Classical.choose h, (Classical.choose_spec h).2⟩, (Classical.choose_spec h).1⟩

/-- A `Runs` triple whose postcondition pins the stacks to "`out` on `k₁`,
everything else empty" yields the iterate equation behind Mathlib's
`TM2OutputsInTime`, with one extra step for the halting label. -/
theorem toFinTM2_outputs_exists (F : Frag) (k₀ k₁ : K) (v₀ : St) (l out : List Γ') (t : ℕ)
    (h : F.Runs v₀ (initStacks k₀ l) (fun _ S' => S' = initStacks k₁ out) t) :
    ∃ n, n ≤ t + 1 ∧ (flip bind (F.toFinTM2 k₀ k₁ v₀).step)^[n]
      (some (initList (F.toFinTM2 k₀ k₁ v₀) l)) =
        Option.map (haltList (F.toFinTM2 k₀ k₁ v₀)) (some out) := by
  obtain ⟨n, hn, v', S', hr, hS⟩ := h.run _ some none (toFinTM2_installed F k₀ k₁ v₀)
  refine ⟨n + 1, by omega, ?_⟩
  have hr' : (flip bind (F.toFinTM2 k₀ k₁ v₀).step)^[n]
      (some (initList (F.toFinTM2 k₀ k₁ v₀) l)) = some ⟨some none, v', S'⟩ := by
    rw [initList_toFinTM2]; exact hr
  rw [Function.iterate_succ_apply', hr', hS]
  exact Eq.trans rfl (congrArg some (haltList_toFinTM2 F k₀ k₁ v₀ out).symm)

/-- The closing lemma in Mathlib's data-level form. -/
noncomputable def toFinTM2_outputs (F : Frag) (k₀ k₁ : K) (v₀ : St) (l out : List Γ') (t : ℕ)
    (h : F.Runs v₀ (initStacks k₀ l) (fun _ S' => S' = initStacks k₁ out) t) :
    TM2OutputsInTime (F.toFinTM2 k₀ k₁ v₀) l (some out) (t + 1) :=
  EvalsToInTime.ofExists (toFinTM2_outputs_exists F k₀ k₁ v₀ l out t h)

end Frag

end Carmichael.TM
