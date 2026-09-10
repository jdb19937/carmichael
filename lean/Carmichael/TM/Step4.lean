import Carmichael.TM.Table
import Carmichael.TM.PrimList

/-!
# Route T: step 4, greedy extraction (sortie T5b)

Machine fragments refining `Alg.extractGo` and `Alg.extract`
(Algorithm.lean) with EXACT postconditions: the running product `m`, the
witness list `used` (in the Lean order `S ++ used`) and the DP table on the
stacks are, at every fragment boundary, `encodeNatΓ' m`, `encList used`,
`encTblAsc L t ++ [blank]` for the values of the Lean recursion, and the
result flag is `(Alg.extractGo L n P m used t).1.isSome`.

## Stack allocation (`K = Fin 8`; all eight stacks named, pairwise distinct)

| stack | contents | role |
|---|---|---|
| `np` | `encList P ++ npr` | the pool; its top entry is the current `p`, consumed per element (the pool's `bra` remains at the end) |
| `nL` | `encodeNatΓ' L ++ comma :: nLr` | the modulus `L` (kept) |
| `snap` | `S snap` between elements | the descending snapshot of the table for `dpStepF`, then the looked-up slot |
| `acc` | `encTblAsc L t ++ [blank]` | the DP table, ALONE on its stack (so `clear acc` resets it) |
| `s`, `t` | `S s`, `S t` between elements | scratch (restored) |
| `nm` | `encodeNatΓ' m ++ comma :: (encodeNatΓ' n ++ comma :: nmr)` | `m` packed above `n` |
| `nu` | `encList used ++ nur` | the witnesses collected so far |

Per pool element `p` (Lean: `st := dpStep L p t`, then `st.1 (1 % L)`):

* `exPre`: `copyTbl acc snap np s t` (snapshot, `acc` unchanged),
  `dpStepF np nL snap acc s t` (`acc := dpStep`, `p` consumed, `snap` restored),
  `pushNum t 1 ; dup nL snap s ; modC t snap np acc s nu` (`t := 1 % L`),
  `lookupSlot acc t snap s np` (`snap := encSlot (st.1 (1 % L)) ++ S snap`, `t` consumed),
  `peekKet snap` (`flag := (slot = none)`).
* `none`: `popTop snap ; peekBra np` (`flag := pool exhausted`).
* `some S`: `prodLF snap t np s nu` (`t := prodL S`), `mulC nm t s np nu ;
  moveEntry s nm t` (`m := m * prodL S`), `appendList snap nu t s`
  (`used := S ++ used`, `S` consumed), `clear acc ; dup nL t s ; emptyTbl t acc s`
  (table reset), then the exit test `n < m'` on copies (`moveEntry`/`dup`/`cmpFrag`):
  on success `pushSym np ket` (marker) and `flag := true`, else `peekBra np`.

The loop is `Frag.loop (fun v => !v.flag) exBody`; `flag` means "stop"
(pool exhausted or success).  After the loop `peekKet np` reads the success
marker into `flag` and `popTop np` removes it, so `flag = (extractGo …).1.isSome`
and `np` holds the remaining pool in both cases.

## Refinement

`extractFin L n P m used t : ExFin` is the final `(m, used, t, pool)` state of
the Lean recursion (the state at the hit, or when the pool runs out); the
machine's stacks hold exactly `extractFin` (`ExPost`), and
`extractGo_some` ties it to `(Alg.extractGo …).1`.  The loop lemma is a
structural induction on the pool mirroring the recursion, using the two
one-iteration rules `Frag.loop_runs_exit` / `Frag.loop_runs_step`
(no iteration-indexed invariant is needed).

## Step bounds

Per element `≤ exC L Nb X = 20 (L + 1)^2 (Nb + 2) B X` where `Nb` bounds the
witness length (`N + |P| ≤ Nb`, crude: `Nb = |P|` for `extract`) and `X` bounds
the bit lengths (`b ≤ X`, `bM ≤ X`, `2 (Nb + 2) b + 4 ≤ X`; `bM` is the bit
bound of every `m` encountered, `bm + b (N + |P|) ≤ bM` for `m < 2 ^ bm`).
Total `≤ ((Alg.extractGo …).2 + 1) * (exC L Nb X + 5)`.
-/

namespace Carmichael.TM

open Turing Turing.TM2 Turing.TM2.Stmt Computability

/-! ### Lean side: unfolding `extractGo`, the final state `extractFin` -/

theorem extractGo_nil (L n m : ℕ) (used : List ℕ) (tb : Alg.Tbl) :
    Alg.extractGo L n [] m used tb = (none, 0) := rfl

theorem extractGo_cons_none (L n p : ℕ) (P : List ℕ) (m : ℕ) (used : List ℕ) (tb : Alg.Tbl)
    (h : (Alg.dpStep L p tb).1 (1 % L) = none) :
    Alg.extractGo L n (p :: P) m used tb =
      ((Alg.extractGo L n P m used (Alg.dpStep L p tb).1).1,
        (Alg.extractGo L n P m used (Alg.dpStep L p tb).1).2 + (Alg.dpStep L p tb).2 + 1) := by
  simp only [Alg.extractGo, h]

theorem extractGo_cons_some (L n p : ℕ) (P : List ℕ) (m : ℕ) (used : List ℕ) (tb : Alg.Tbl)
    (S : List ℕ) (h : (Alg.dpStep L p tb).1 (1 % L) = some S) :
    Alg.extractGo L n (p :: P) m used tb =
      if n < m * (Alg.prodL S).1 then
        (some (m * (Alg.prodL S).1, S ++ used), (Alg.dpStep L p tb).2 + (Alg.prodL S).2 + 1)
      else
        ((Alg.extractGo L n P (m * (Alg.prodL S).1) (S ++ used) Alg.emptyTbl).1,
          (Alg.extractGo L n P (m * (Alg.prodL S).1) (S ++ used) Alg.emptyTbl).2 +
            (Alg.dpStep L p tb).2 + (Alg.prodL S).2 + 1) := by
  simp only [Alg.extractGo, h]

/-- The final state of `extractGo`'s recursion: the running product, the
witness list, the table and the remaining pool, at the hit or when the pool
runs out. -/
structure ExFin where
  m : ℕ
  used : List ℕ
  tbl : Alg.Tbl
  pool : List ℕ

/-- The final `(m, used, t, pool)` of `Alg.extractGo L n P m used t`: mirrors
the recursion; at a hit the table is the (reset) empty table and the pool the
unprocessed rest. -/
def extractFin (L n : ℕ) : List ℕ → ℕ → List ℕ → Alg.Tbl → ExFin
  | [], m, used, t => ⟨m, used, t, []⟩
  | p :: P, m, used, t =>
    let st := Alg.dpStep L p t
    match st.1 (1 % L) with
    | none => extractFin L n P m used st.1
    | some S =>
      let m' := m * (Alg.prodL S).1
      if n < m' then ⟨m', S ++ used, Alg.emptyTbl, P⟩
      else extractFin L n P m' (S ++ used) Alg.emptyTbl

theorem extractFin_nil (L n m : ℕ) (used : List ℕ) (tb : Alg.Tbl) :
    extractFin L n [] m used tb = ⟨m, used, tb, []⟩ := rfl

theorem extractFin_cons_none (L n p : ℕ) (P : List ℕ) (m : ℕ) (used : List ℕ) (tb : Alg.Tbl)
    (h : (Alg.dpStep L p tb).1 (1 % L) = none) :
    extractFin L n (p :: P) m used tb = extractFin L n P m used (Alg.dpStep L p tb).1 := by
  simp only [extractFin, h]

theorem extractFin_cons_some (L n p : ℕ) (P : List ℕ) (m : ℕ) (used : List ℕ) (tb : Alg.Tbl)
    (S : List ℕ) (h : (Alg.dpStep L p tb).1 (1 % L) = some S) :
    extractFin L n (p :: P) m used tb =
      if n < m * (Alg.prodL S).1 then ⟨m * (Alg.prodL S).1, S ++ used, Alg.emptyTbl, P⟩
      else extractFin L n P (m * (Alg.prodL S).1) (S ++ used) Alg.emptyTbl := by
  simp only [extractFin, h]

/-- On success, `extractFin` holds the returned pair. -/
theorem extractGo_some (L n : ℕ) (P : List ℕ) :
    ∀ (m : ℕ) (used : List ℕ) (tb : Alg.Tbl) (m' : ℕ) (U : List ℕ),
      (Alg.extractGo L n P m used tb).1 = some (m', U) →
      (extractFin L n P m used tb).m = m' ∧ (extractFin L n P m used tb).used = U := by
  induction P with
  | nil => intro m used tb m' U h; simp [extractGo_nil] at h
  | cons p P ih =>
    intro m used tb m' U h
    cases hl : (Alg.dpStep L p tb).1 (1 % L) with
    | none =>
      rw [extractGo_cons_none L n p P m used tb hl] at h
      rw [extractFin_cons_none L n p P m used tb hl]
      exact ih _ _ _ _ _ h
    | some S =>
      rw [extractGo_cons_some L n p P m used tb S hl] at h
      rw [extractFin_cons_some L n p P m used tb S hl]
      by_cases hn : n < m * (Alg.prodL S).1
      · rw [if_pos hn] at h ⊢
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact ⟨h.1, h.2⟩
      · rw [if_neg hn] at h ⊢
        exact ih _ _ _ _ _ h

/-- On failure the remaining pool is empty. -/
theorem extractGo_none (L n : ℕ) (P : List ℕ) :
    ∀ (m : ℕ) (used : List ℕ) (tb : Alg.Tbl),
      (Alg.extractGo L n P m used tb).1 = none → (extractFin L n P m used tb).pool = [] := by
  induction P with
  | nil => intro m used tb _; rfl
  | cons p P ih =>
    intro m used tb h
    cases hl : (Alg.dpStep L p tb).1 (1 % L) with
    | none =>
      rw [extractGo_cons_none L n p P m used tb hl] at h
      rw [extractFin_cons_none L n p P m used tb hl]
      exact ih _ _ _ h
    | some S =>
      rw [extractGo_cons_some L n p P m used tb S hl] at h
      rw [extractFin_cons_some L n p P m used tb S hl]
      by_cases hn : n < m * (Alg.prodL S).1
      · rw [if_pos hn] at h; simp at h
      · rw [if_neg hn] at h ⊢
        exact ih _ _ _ h

/-- Size bookkeeping along the recursion: with `TblBounded L tb N b`,
`m < 2 ^ bm`, `bm + b (N + |P|) ≤ bM`, every reachable table is
`TblBounded L _ (N + |P|) b`, every `m` is `< 2 ^ bM`, and the final witness
list has at most `|used| + N + |P|` entries, all `< 2 ^ b`. -/
theorem extractFin_bounded (L n b bM : ℕ) (hL : 0 < L) (P : List ℕ) (hb : ∀ p ∈ P, p < 2 ^ b) :
    ∀ (m : ℕ) (used : List ℕ) (tb : Alg.Tbl) (N bm : ℕ), TblBounded L tb N b →
      m < 2 ^ bm → bm + b * (N + P.length) ≤ bM →
      (∀ q ∈ used, q < 2 ^ b) →
      (extractFin L n P m used tb).m < 2 ^ bM ∧
      TblBounded L (extractFin L n P m used tb).tbl (N + P.length) b ∧
      (extractFin L n P m used tb).used.length ≤ used.length + N + P.length ∧
      (∀ q ∈ (extractFin L n P m used tb).used, q < 2 ^ b) ∧
      (∀ q ∈ (extractFin L n P m used tb).pool, q < 2 ^ b) := by
  induction P with
  | nil =>
    intro m used tb N bm ht hm hbM hu
    rw [extractFin_nil]
    refine ⟨lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by simp at hbM; omega)),
      by simpa using ht, by simp, hu, by simp⟩
  | cons p P ih =>
    intro m used tb N bm ht hm hbM hu
    have hp : p < 2 ^ b := hb p (List.mem_cons_self ..)
    have hbP : ∀ q ∈ P, q < 2 ^ b := fun q hq => hb q (List.mem_cons_of_mem _ hq)
    have ht' : TblBounded L (Alg.dpStep L p tb).1 (N + 1) b := tblBounded_dpStep ht hp
    simp only [List.length_cons] at hbM
    cases hl : (Alg.dpStep L p tb).1 (1 % L) with
    | none =>
      rw [extractFin_cons_none L n p P m used tb hl]
      have := ih hbP m used _ (N + 1) bm ht' hm
        (by have h2 : N + 1 + P.length = N + (P.length + 1) := by ring
            rw [h2]; exact hbM) hu
      simp only [List.length_cons]
      refine ⟨this.1, ?_, by omega, this.2.2.2.1, this.2.2.2.2⟩
      have h2 : N + 1 + P.length = N + (P.length + 1) := by ring
      rw [← h2]; exact this.2.1
    | some S =>
      rw [extractFin_cons_some L n p P m used tb S hl]
      have hS := ht' (1 % L) (Nat.mod_lt 1 hL) S hl
      have hprod : (Alg.prodL S).1 ≤ 2 ^ ((N + 1) * b) :=
        (prodL_le_two_pow hS.2).trans (Nat.pow_le_pow_right (by norm_num)
          (Nat.mul_le_mul_right _ hS.1))
      have hm' : m * (Alg.prodL S).1 < 2 ^ (bm + (N + 1) * b) := by
        rw [Nat.pow_add]
        exact Nat.mul_lt_mul_of_lt_of_le hm hprod (Nat.two_pow_pos _)
      have hu' : ∀ q ∈ S ++ used, q < 2 ^ b := by
        intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hS.2 q hq
        · exact hu q hq
      by_cases hn : n < m * (Alg.prodL S).1
      · rw [if_pos hn]
        simp only [List.length_cons, List.length_append]
        refine ⟨lt_of_lt_of_le hm' (Nat.pow_le_pow_right (by norm_num) (by nlinarith)),
          tblBounded_emptyTbl _ _ _, by omega, hu', hbP⟩
      · rw [if_neg hn]
        have := ih hbP (m * (Alg.prodL S).1) (S ++ used) Alg.emptyTbl 0 (bm + (N + 1) * b)
          (tblBounded_emptyTbl _ _ _) hm' (by nlinarith) hu'
        simp only [List.length_cons, List.length_append, Nat.zero_add] at this ⊢
        refine ⟨this.1, TblBounded.mono (by omega) this.2.1, by omega, this.2.2.2.1,
          this.2.2.2.2⟩

/-! ### Two one-iteration rules for `Frag.loop` -/

namespace Frag

/-- A loop whose test fails at entry exits in one step. -/
theorem loop_runs_exit {c : St → Bool} {Bd : Frag} {v : St} {S : Stacks} (hc : c v = false) :
    (loop c Bd).Runs v S (fun v' S' => v' = v ∧ S' = S) 1 := by
  constructor
  intro Λ M ι e hI
  refine ⟨1, le_rfl, v, S, ?_, rfl, rfl⟩
  refine runsTo_succ ?_ (runsTo_zero M _)
  tm_step none [loop, hc]

/-- A loop whose test succeeds at entry runs the body once and then the loop
again. -/
theorem loop_runs_step {c : St → Bool} {Bd : Frag} {v : St} {S : Stacks} {Q₁ Q : St → Stacks → Prop}
    {t₁ t₂ : ℕ} (hc : c v = true) (hB : Bd.Runs v S Q₁ t₁)
    (hrest : ∀ v' S', Q₁ v' S' → (loop c Bd).Runs v' S' Q t₂) :
    (loop c Bd).Runs v S Q (t₁ + t₂ + 1) := by
  constructor
  intro Λ M ι e hI
  obtain ⟨n₁, hn₁, v₁, S₁, hr₁, hQ₁⟩ := hB.run M _ _ (loop_installed_body hI)
  obtain ⟨n₂, hn₂, v₂, S₂, hr₂, hQ⟩ := (hrest v₁ S₁ hQ₁).run M ι e hI
  refine ⟨n₁ + n₂ + 1, by omega, v₂, S₂, ?_, hQ⟩
  refine runsTo_succ ?_ (runsTo_trans hr₁ hr₂)
  tm_step none [loop, hc, Function.comp]

end Frag

/-! ### List helpers -/

theorem encList_cons_append (a : ℕ) (l : List ℕ) (r : List Γ') :
    encList (a :: l) ++ r = encodeNatΓ' a ++ .comma :: (encList l ++ r) := by
  rw [encList_cons]; simp

theorem decide_head?_encList_bra (l : List ℕ) (r : List Γ') :
    decide ((encList l ++ r).head? = some Γ'.bra) = decide (l = []) := by
  rw [encList_eq]
  exact decide_eq_decide.mpr ((head?_encListB_append _ _).trans List.map_eq_nil_iff)

theorem head?_encList_ne_ket' (l : List ℕ) (r : List Γ') :
    decide ((encList l ++ r).head? = some Γ'.ket) = false :=
  decide_eq_false (head?_encList_ne_ket l r)


/-! ### The eight stacks -/

/-- Pairwise distinctness of the eight stacks of step 4 (`by decide` at use sites). -/
abbrev Dist8 (np nL snap acc s t nm nu : K) : Prop :=
  np ≠ nL ∧ np ≠ snap ∧ np ≠ acc ∧ np ≠ s ∧ np ≠ t ∧ np ≠ nm ∧ np ≠ nu ∧
  nL ≠ snap ∧ nL ≠ acc ∧ nL ≠ s ∧ nL ≠ t ∧ nL ≠ nm ∧ nL ≠ nu ∧
  snap ≠ acc ∧ snap ≠ s ∧ snap ≠ t ∧ snap ≠ nm ∧ snap ≠ nu ∧
  acc ≠ s ∧ acc ≠ t ∧ acc ≠ nm ∧ acc ≠ nu ∧
  s ≠ t ∧ s ≠ nm ∧ s ≠ nu ∧
  t ≠ nm ∧ t ≠ nu ∧
  nm ≠ nu

/-! ### Budgets -/

/-- The unit of the per-element budget: `(L + 1)^2 (Nb + 2) B X`. -/
def exY (L Nb X : ℕ) : ℕ := (L + 1) ^ 2 * (Nb + 2) * B X

/-- The per-element budget of the extraction loop. -/
def exC (L Nb X : ℕ) : ℕ := 20 * exY L Nb X

/-- Raw budget of the prelude `exPre` (table bounded by `N`, bits by `b`). -/
def exPreC (L N b : ℕ) : ℕ :=
  (L + 1) * (N + 2) * B b + (L + 1) ^ 2 * (N + 2) * B b + B b + B b + B b +
    (L + 1) * (N + 1 + 2) * B b + 1

/-- Raw budget of the `some` branch `exSome` (table bounded by `N'`, witness of
length `sl`, products below `2 ^ bM`). -/
def exSomeC (L N' b sl bM : ℕ) : ℕ :=
  (sl + 1) * B (2 * (sl + 1) * b + 4) + B bM + B bM + (sl + 1) * B b +
    (L * (N' * (b + 1) + 1) + 2) + B b + (L + 1) * B b + (5 * B bM + 3)

theorem B_le_exY (L Nb X : ℕ) : B X ≤ exY L Nb X := by
  unfold exY
  have h1 : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ (L + 1) ^ 2 * (Nb + 2) := by nlinarith
  exact Nat.le_mul_of_pos_left _ h2

theorem three_le_exY (L Nb X : ℕ) : 3 ≤ exY L Nb X := by
  have := B_le_exY L Nb X
  have : 3 ≤ B X := by unfold B; have := Nat.one_le_pow 3 (X + 2) (by omega); omega
  omega

theorem exPreC_le (L N Nb b X : ℕ) (hN : N + 1 ≤ Nb) (hXb : b ≤ X) :
    exPreC L N b + 1 ≤ 7 * exY L Nb X := by
  have hBb : B b ≤ B X := B_mono hXb
  have hY := B_le_exY L Nb X
  have hL2 : L + 1 ≤ (L + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have he : (L + 1) * (N + 2) * B b ≤ exY L Nb X :=
    Nat.mul_le_mul (Nat.mul_le_mul hL2 (by omega)) hBb
  have hf : (L + 1) ^ 2 * (N + 2) * B b ≤ exY L Nb X :=
    Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by omega)) hBb
  have hg : (L + 1) * (N + 1 + 2) * B b ≤ exY L Nb X :=
    Nat.mul_le_mul (Nat.mul_le_mul hL2 (by omega)) hBb
  have := three_le_exY L Nb X
  unfold exPreC; omega

theorem exSomeC_le (L N Nb b bM X sl : ℕ) (hsl : sl ≤ N + 1) (hN : N + 1 ≤ Nb) (hXb : b ≤ X)
    (hXM : bM ≤ X) (hXN : 2 * (Nb + 2) * b + 4 ≤ X) :
    exSomeC L (N + 1) b sl bM ≤ 13 * exY L Nb X := by
  have hBb : B b ≤ B X := B_mono hXb
  have hBM : B bM ≤ B X := B_mono hXM
  have hBs : B (2 * (sl + 1) * b + 4) ≤ B X := B_mono (by nlinarith)
  have hY := B_le_exY L Nb X
  have hL2 : L + 1 ≤ (L + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have h1 : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hh : (sl + 1) * B (2 * (sl + 1) * b + 4) ≤ exY L Nb X := by
    unfold exY
    calc (sl + 1) * B (2 * (sl + 1) * b + 4) ≤ (1 * (Nb + 2)) * B X :=
          Nat.mul_le_mul (by omega) hBs
      _ ≤ (L + 1) ^ 2 * (Nb + 2) * B X := Nat.mul_le_mul (Nat.mul_le_mul h1 le_rfl) le_rfl
  have hi : (sl + 1) * B b ≤ exY L Nb X := by
    unfold exY
    calc (sl + 1) * B b ≤ (1 * (Nb + 2)) * B X := Nat.mul_le_mul (by omega) hBb
      _ ≤ (L + 1) ^ 2 * (Nb + 2) * B X := Nat.mul_le_mul (Nat.mul_le_mul h1 le_rfl) le_rfl
  have hj : L * ((N + 1) * (b + 1) + 1) + 2 ≤ exY L Nb X := by
    have h2 : b + 2 ≤ B b := by simpa using linear_le_B (c := 1) (b := b) (by norm_num)
    have h3 : L * ((N + 1) * (b + 1) + 1) + 2 ≤ (L + 1) * (N + 1 + 2) * (b + 2) := by nlinarith
    calc L * ((N + 1) * (b + 1) + 1) + 2 ≤ (L + 1) * (N + 1 + 2) * (b + 2) := h3
      _ ≤ (L + 1) ^ 2 * (Nb + 2) * B X :=
          Nat.mul_le_mul (Nat.mul_le_mul hL2 (by omega)) (h2.trans hBb)
  have hk : (L + 1) * B b ≤ exY L Nb X := by
    unfold exY
    exact Nat.mul_le_mul (by nlinarith) hBb
  have h3e := three_le_exY L Nb X
  unfold exSomeC; omega

/-- Bit bounds of a witness product. -/
theorem prodL_bounds {W : List ℕ} {b N' m bm : ℕ} (hWN : W.length ≤ N') (hWb : ∀ q ∈ W, q < 2 ^ b)
    (hm : m < 2 ^ bm) (hbm1 : 1 ≤ bm) :
    (Alg.prodL W).1 < 2 ^ (bm + b * N') ∧ m * (Alg.prodL W).1 < 2 ^ (bm + b * N') := by
  have hprod : (Alg.prodL W).1 ≤ 2 ^ (b * N') :=
    (prodL_le_two_pow hWb).trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  have h2 : m * (Alg.prodL W).1 < 2 ^ (bm + b * N') := by
    rw [Nat.pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hm hprod (Nat.two_pow_pos _)
  refine ⟨lt_of_le_of_lt hprod ?_, h2⟩
  exact Nat.pow_lt_pow_right (by norm_num) (by omega)

/-! ### Fragments -/

/-- Prelude of one element: snapshot, `dpStep`, look up slot `1 % L` onto
`snap`, `flag := (slot = none)`.  Consumes `p` from `np`; `t := 1 % L` is
consumed by the lookup.  Scratch `s`, `t`; `nm`, `nu` restored (`modC` scratch). -/
def exPre (np nL snap acc s t nu : K) : Frag :=
  (copyTbl acc snap np s t).seq ((dpStepF np nL snap acc s t).seq
    ((pushNum t 1).seq ((dup nL snap s).seq ((modC t snap np acc s nu).seq
      ((lookupSlot acc t snap s np).seq (peekKet snap))))))

/-- The `none` branch: pop the `ket`, `flag := (pool exhausted)`. -/
def exNone (np snap : K) : Frag := (popTop snap).seq (peekBra np)

/-- The exit test `n < m'` on copies (`nm = m' ; n ; …`): on success push the
marker `ket` on `np` and `flag := true`, else `flag := (pool exhausted)`.
Scratch `snap`, `s`, `t`; `nm` restored. -/
def exTest (np snap s t nm : K) : Frag :=
  (moveEntry nm snap s).seq ((dup nm t s).seq ((moveEntry snap nm s).seq ((dup nm snap s).seq
    ((cmpFrag t snap).seq
      (Frag.ite (fun v => decide (v.cmp = .lt))
        ((Frag.pushSym np .ket).seq (Frag.load' fun v => { v with flag := true }))
        (peekBra np))))))

/-- The `some S` branch: `m := m * prodL S` (on `nm`), `used := S ++ used`
(`S` consumed from `snap`), reset the table on `acc`, then `exTest`. -/
def exSome (np nL snap acc s t nm nu : K) : Frag :=
  (prodLF snap t np s nu).seq ((mulC nm t s np nu).seq ((moveEntry s nm t).seq
    ((appendList snap nu t s).seq ((clear acc).seq ((dup nL t s).seq ((emptyTbl t acc s).seq
      (exTest np snap s t nm)))))))

/-- One element of the extraction loop. -/
def exBody (np nL snap acc s t nm nu : K) : Frag :=
  (exPre np nL snap acc s t nu).seq
    (Frag.ite (fun v => v.flag) (exNone np snap) (exSome np nL snap acc s t nm nu))

/-- `Alg.extractGo L n P m used t`: the loop over the pool, then the success
marker is read into `flag` and removed. -/
def extractGoF (np nL snap acc s t nm nu : K) : Frag :=
  (peekBra np).seq ((Frag.loop (fun v => !v.flag) (exBody np nL snap acc s t nm nu)).seq
    ((peekKet np).seq (Frag.ite (fun v => v.flag) (popTop np) Frag.skip)))

/-- `Alg.extract L n P`: `m := 1`, `used := []`, the empty table, then `extractGoF`. -/
def extractF (np nL snap acc s t nm nu : K) : Frag :=
  (pushNum nm 1).seq ((Frag.pushSym nu .bra).seq ((dup nL t s).seq ((emptyTbl t acc s).seq
    (extractGoF np nL snap acc s t nm nu))))

/-! ### The prelude -/

theorem exPre_runs {np nL snap acc s t nm nu : K} (hd : Dist8 np nL snap acc s t nm nu)
    (L p : ℕ) (hL : 0 < L) (tb : Alg.Tbl) (N b : ℕ) (ht : TblBounded L tb N b)
    (hp : p < 2 ^ b) (hLb : L < 2 ^ b) (npr nLr : List Γ') (v : St) (S : Stacks)
    (hSp : S np = encodeNatΓ' p ++ .comma :: npr) (hSL : S nL = encodeNatΓ' L ++ .comma :: nLr)
    (hSa : S acc = encTblAsc L tb ++ [.blank]) :
    (exPre np nL snap acc s t nu).Runs v S (fun v' S' =>
        v'.flag = decide ((Alg.dpStep L p tb).1 (1 % L) = none) ∧
        S' np = npr ∧ S' nL = S nL ∧
        S' snap = encSlot ((Alg.dpStep L p tb).1 (1 % L)) ++ S snap ∧
        S' acc = encTblAsc L (Alg.dpStep L p tb).1 ++ [.blank] ∧
        S' s = S s ∧ S' t = S t ∧ S' nm = S nm ∧ S' nu = S nu ∧
        ∀ k, k ≠ np → k ≠ nL → k ≠ snap → k ≠ acc → k ≠ s → k ≠ t → S' k = S k)
      (exPreC L N b) := by
  obtain ⟨hpL, hpsn, hpa, hps, hpt, hpm, hpu, hLsn, hLa, hLs, hLt, hLm, hLu, hsna, hsns, hsnt,
    hsnm, hsnu, has, hat, ham, hau, hst, hsm, hsu, htm, htu, hmu⟩ := hd
  have hLp := hpL.symm; have hsnp := hpsn.symm; have hap := hpa.symm; have hsp := hps.symm
  have htp := hpt.symm; have hsnL := hLsn.symm; have haL := hLa.symm; have hsL := hLs.symm
  have htL := hLt.symm; have hasn := hsna.symm; have hssn := hsns.symm; have htsn := hsnt.symm
  have hsa := has.symm; have hta := hat.symm; have hts := hst.symm
  have hb1 : b ≠ 0 := by rintro rfl; simp at hLb; omega
  have h1lt : 1 < 2 ^ b := Nat.one_lt_two_pow hb1
  have ht' : TblBounded L (Alg.dpStep L p tb).1 (N + 1) b := tblBounded_dpStep ht hp
  have hmod : 1 % L < L := Nat.mod_lt 1 hL
  unfold exPreC
  -- stage 1: the snapshot
  have h1 := copyTbl_le_B hasn hap has hat hsnp hsns hsnt hps hpt hst L tb N b ht [] v S hSa
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (L + 1) ^ 2 * (N + 2) * B b + B b + B b + B b + (L + 1) * (N + 1 + 2) * B b + 1) h1
    fun v₁ S₁ ⟨ha₁, hsn₁, hp₁, hs₁, ht₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 2: dpStep
  have hL₁ : S₁ nL = encodeNatΓ' L ++ .comma :: nLr := by rw [hF₁ nL hLa hLsn hLp hLs hLt, hSL]
  have h2 := dpStepF_le_B hpL hpsn hpa hps hpt hLsn hLa hLs hLt hsna hsns hsnt has hat hst L p hL
    tb N b ht hp hLb npr nLr (S snap) [] v₁ S₁ (by rw [hp₁, hSp]) hL₁ hsn₁ (by rw [ha₁, hSa])
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := B b + B b + B b + (L + 1) * (N + 1 + 2) * B b + 1) h2
    fun v₂ S₂ ⟨hp₂, hL₂, hsn₂, ha₂, hs₂, ht₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: push 1
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + B b + (L + 1) * (N + 1 + 2) * B b + 1)
    (pushNum_le_B t 1 b h1lt v₂ S₂) fun v₃ S₃ ⟨_, ht₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 4: L onto snap
  have hL₃ : S₃ nL = encodeNatΓ' L ++ .comma :: nLr := by rw [hF₃ nL hLt, hL₂, hL₁]
  have h4 := dup_le_B hLsn hLs hsns L b hLb nLr v₃ S₃ hL₃
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + (L + 1) * (N + 1 + 2) * B b + 1) h4
    fun v₄ S₄ ⟨hL₄, hsn₄, hs₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 5: 1 % L on t
  have ht₄ : S₄ t = encodeNatΓ' 1 ++ .comma :: S₂ t := by rw [hF₄ t htL htsn hts, ht₃]
  have h5 := modC_le_B htsn htp hta hts htu hsnp hsna hsns hsnu hpa hps hpu has hau hsu 1 L b hL
    h1lt hLb (S₂ t) (S₃ snap) v₄ S₄ ht₄ hsn₄
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (L + 1) * (N + 1 + 2) * B b + 1) h5
    fun v₅ S₅ ⟨ht₅, hsn₅, hp₅, ha₅, hs₅, hu₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 6: the lookup
  have ha₅' : S₅ acc = encTblAsc L (Alg.dpStep L p tb).1 ++ [.blank] := by
    rw [ha₅, hF₄ acc haL hasn has, hF₃ acc hat, ha₂]
  have ht₅' : S₅ t = bits (Computability.encodeNat (1 % L)) ++ .comma :: S₂ t := ht₅
  have hjs : (Computability.encodeNat (1 % L)).length ≤ 2 * b := by
    have := encodeNat_length_le_of_lt_pow (lt_of_lt_of_le hmod hLb.le); omega
  have hjn : toNat (Computability.encodeNat (1 % L)) < L := by rw [toNat_encodeNat]; exact hmod
  have h6 := lookupSlot_le_B hat hasn has hap htsn hts htp hsns hsnp hsp L _ (N + 1) b ht' _ hjs hjn
    [.blank] (S₂ t) v₅ S₅ ha₅' ht₅'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) h6
    fun v₆ S₆ ⟨ha₆, ht₆, hsn₆, hs₆, hp₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [toNat_encodeNat] at hsn₆
  -- stage 7: peek
  refine Frag.runs_mono (peekKet_runs snap v₆ S₆) (fun v₇ S₇ ⟨hv₇, hS₇⟩ => ?_) le_rfl
  have hsn₆' : S₆ snap = encSlot ((Alg.dpStep L p tb).1 (1 % L)) ++ S snap := by
    rw [hsn₆, hsn₅, hF₃ snap hsnt, hsn₂]
  rw [hS₇]
  refine ⟨?_, ?_, ?_, hsn₆', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv₇]; show decide ((S₆ snap).head? = some Γ'.ket) = _
    rw [hsn₆', decide_head?_encSlot_ket]
  · rw [hp₆, hp₅, hF₄ np hpL hpsn hps, hF₃ np hpt, hp₂]
  · rw [hF₆ nL hLa hLt hLsn hLs hLp, hF₅ nL hLt hLsn hLp hLa hLs hLu, hL₄, hL₃, hSL]
  · rw [ha₆, ha₅']
  · rw [hs₆, hs₅, hs₄, hF₃ s hst, hs₂, hs₁]
  · rw [ht₆, ht₂, ht₁]
  · rw [hF₆ nm ham.symm htm.symm hsnm.symm hsm.symm hpm.symm, hF₅ nm htm.symm hsnm.symm hpm.symm
      ham.symm hsm.symm hmu, hF₄ nm hLm.symm hsnm.symm hsm.symm, hF₃ nm htm.symm,
      hF₂ nm hpm.symm hLm.symm hsnm.symm ham.symm hsm.symm htm.symm,
      hF₁ nm ham.symm hsnm.symm hpm.symm hsm.symm htm.symm]
  · rw [hF₆ nu hau.symm htu.symm hsnu.symm hsu.symm hpu.symm, hu₅,
      hF₄ nu hLu.symm hsnu.symm hsu.symm, hF₃ nu htu.symm,
      hF₂ nu hpu.symm hLu.symm hsnu.symm hau.symm hsu.symm htu.symm,
      hF₁ nu hau.symm hsnu.symm hpu.symm hsu.symm htu.symm]
  · intro k hkp hkL hksn hka hks hkt
    by_cases hku : k = nu
    · subst hku
      rw [hF₆ k hka hkt hksn hks hkp, hu₅, hF₄ k hkL hksn hks, hF₃ k hkt,
        hF₂ k hkp hkL hksn hka hks hkt, hF₁ k hka hksn hkp hks hkt]
    · rw [hF₆ k hka hkt hksn hks hkp, hF₅ k hkt hksn hkp hka hks hku, hF₄ k hkL hksn hks,
        hF₃ k hkt, hF₂ k hkp hkL hksn hka hks hkt, hF₁ k hka hksn hkp hks hkt]

/-! ### The `none` branch -/

theorem exNone_runs {np snap : K} (hpsn : np ≠ snap) (P' : List ℕ) (npr snapr : List Γ')
    (v : St) (S : Stacks) (hSp : S np = encList P' ++ npr) (hSsn : S snap = .ket :: snapr) :
    (exNone np snap).Runs v S (fun v' S' =>
        v'.flag = decide (P' = []) ∧ S' snap = snapr ∧ ∀ k, k ≠ snap → S' k = S k) 2 := by
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) (popTop_runs snap v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) le_rfl
  subst hS₁
  refine Frag.runs_mono (peekBra_runs np v₁ _) (fun v₂ S₂ ⟨hv₂, hS₂⟩ => ⟨?_, ?_, ?_⟩) le_rfl
  · rw [hv₂]; show decide _ = _
    rw [Function.update_of_ne hpsn, hSp, decide_head?_encList_bra]
  · rw [hS₂, Function.update_self, hSsn, List.tail_cons]
  · intro k hk; rw [hS₂, Function.update_of_ne hk]

/-! ### The exit test -/

theorem exTest_runs {np nL snap acc s t nm nu : K} (hd : Dist8 np nL snap acc s t nm nu)
    (n m' bM : ℕ) (hn : n < 2 ^ bM) (hm : m' < 2 ^ bM) (P' : List ℕ) (npr nmr : List Γ')
    (v : St) (S : Stacks) (hSp : S np = encList P' ++ npr)
    (hSm : S nm = encodeNatΓ' m' ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr)) :
    (exTest np snap s t nm).Runs v S (fun v' S' =>
        (if n < m' then v'.flag = true ∧ S' np = .ket :: S np
          else v'.flag = decide (P' = []) ∧ S' np = S np) ∧
        S' nm = S nm ∧ S' snap = S snap ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ np → k ≠ snap → k ≠ s → k ≠ t → k ≠ nm → S' k = S k)
      (5 * B bM + 3) := by
  obtain ⟨hpL, hpsn, hpa, hps, hpt, hpm, hpu, hLsn, hLa, hLs, hLt, hLm, hLu, hsna, hsns, hsnt,
    hsnm, hsnu, has, hat, ham, hau, hst, hsm, hsu, htm, htu, hmu⟩ := hd
  have hsnp := hpsn.symm; have hsp := hps.symm; have htp := hpt.symm; have hmp := hpm.symm
  have hssn := hsns.symm; have htsn := hsnt.symm; have hmsn := hsnm.symm
  have hts := hst.symm; have hms := hsm.symm; have hmt := htm.symm
  have hlm : (Computability.encodeNat m').length ≤ bM := encodeNat_length_le_of_lt_pow hm
  have hlogn : Nat.log 2 n ≤ bM := log_le_of_lt_pow hn
  have hlogm : Nat.log 2 m' ≤ bM := log_le_of_lt_pow hm
  -- stage 1: m' onto snap
  have h1 := moveEntry_runs hmsn hms hsns (Computability.encodeNat m') _ v S hSm
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * B bM + 3) h1
    fun v₁ S₁ ⟨_, _, _, hm₁, hsn₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h)
    (by have := le_B_of_le_linear (b := bM) (n := 2 * (Computability.encodeNat m').length + 4)
          (by omega); omega)
  -- stage 2: n onto t
  have h2 := dup_le_B hmt hms hts n bM hn nmr v₁ S₁ hm₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * B bM + 3) h2
    fun v₂ S₂ ⟨hm₂, ht₂, hs₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: m' back onto nm
  have hsn₂ : S₂ snap = bits (Computability.encodeNat m') ++ .comma :: S snap := by
    rw [hF₂ snap hsnm hsnt hsns, hsn₁]
  have h3 := moveEntry_runs hsnm hsns hms (Computability.encodeNat m') _ v₂ S₂ hsn₂
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B bM + 3) h3
    fun v₃ S₃ ⟨_, _, _, hsn₃, hm₃, hs₃, hF₃⟩ => ?_) (fun _ _ h => h)
    (by have := le_B_of_le_linear (b := bM) (n := 2 * (Computability.encodeNat m').length + 4)
          (by omega); omega)
  -- stage 4: m' onto snap (copy)
  have hm₃' : S₃ nm = encodeNatΓ' m' ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr) := by
    rw [hm₃, hm₂, hm₁]; rfl
  have h4 := dup_le_B hmsn hms hsns m' bM hm _ v₃ S₃ hm₃'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B bM + 3) h4
    fun v₄ S₄ ⟨hm₄, hsn₄, hs₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 5: compare
  have ht₄ : S₄ t = encodeNatΓ' n ++ .comma :: S₁ t := by rw [hF₄ t htm htsn hts, hF₃ t htsn htm hts, ht₂]
  have h5 := cmp_correct htsn n m' (S₁ t) (S₃ snap) v₄ S₄ ht₄ hsn₄
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3) h5
    fun v₅ S₅ ⟨hc₅, ht₅, hsn₅, hF₅⟩ => ?_) (fun _ _ h => h)
    (by have := le_B_of_le_linear (b := bM) (n := 4 * (Nat.log 2 n + Nat.log 2 m' + 1))
          (by omega); omega)
  -- common facts after stage 5
  have hp₅ : S₅ np = S np := by
    rw [hF₅ np hpt hpsn, hF₄ np hpm hpsn hps, hF₃ np hpsn hpm hps, hF₂ np hpm hpt hps,
      hF₁ np hpm hpsn hps]
  have hm₅ : S₅ nm = S nm := by rw [hF₅ nm hmt hmsn, hm₄, hm₃', hSm]
  have hsn₅' : S₅ snap = S snap := by rw [hsn₅, hsn₃]
  have hs₅ : S₅ s = S s := by rw [hF₅ s hst hssn, hs₄, hs₃, hs₂, hs₁]
  have ht₅' : S₅ t = S t := by rw [ht₅, hF₁ t htm htsn hts]
  have hF₅' : ∀ k, k ≠ np → k ≠ snap → k ≠ s → k ≠ t → k ≠ nm → S₅ k = S k := by
    intro k hkp hksn hks hkt hkm
    rw [hF₅ k hkt hksn, hF₄ k hkm hksn hks, hF₃ k hksn hkm hks, hF₂ k hkm hkt hks,
      hF₁ k hkm hksn hks]
  -- stage 6: the branch
  refine Frag.ite_runs (t := 2) (fun hc => ?_) (fun hc => ?_)
  · -- success
    have hlt : n < m' := by
      rw [hc₅] at hc; exact compare_lt_iff_lt.mp (of_decide_eq_true hc)
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) (Frag.pushSym_runs np .ket v₅ S₅)
      fun v₆ S₆ ⟨hv₆, hS₆⟩ => ?_) (fun _ _ h => h) le_rfl
    subst hS₆
    refine Frag.runs_mono (Frag.load'_runs _ v₆ _) (fun v₇ S₇ ⟨hv₇, hS₇⟩ => ?_) le_rfl
    subst hS₇
    rw [if_pos hlt]
    refine ⟨⟨by rw [hv₇], by rw [Function.update_self, hp₅]⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Function.update_of_ne hmp, hm₅]
    · rw [Function.update_of_ne hsnp, hsn₅']
    · rw [Function.update_of_ne hsp, hs₅]
    · rw [Function.update_of_ne htp, ht₅']
    · intro k hkp hksn hks hkt hkm; rw [Function.update_of_ne hkp, hF₅' k hkp hksn hks hkt hkm]
  · -- no exit
    have hlt : ¬ n < m' := by
      rw [hc₅] at hc
      intro h; exact absurd (decide_eq_true (compare_lt_iff_lt.mpr h)) (by rw [hc]; decide)
    refine Frag.runs_mono (peekBra_runs np v₅ S₅) (fun v₆ S₆ ⟨hv₆, hS₆⟩ => ?_) (by omega)
    subst hS₆
    rw [if_neg hlt]
    refine ⟨⟨?_, hp₅⟩, hm₅, hsn₅', hs₅, ht₅', hF₅'⟩
    rw [hv₆]; show decide _ = _
    rw [hp₅, hSp, decide_head?_encList_bra]

/-! ### The `some` branch -/

theorem exSome_runs {np nL snap acc s t nm nu : K} (hd : Dist8 np nL snap acc s t nm nu)
    (L n b : ℕ) (hLb : L < 2 ^ b) (tb' : Alg.Tbl) (N' : ℕ) (ht' : TblBounded L tb' N' b)
    (W : List ℕ) (hWb : ∀ q ∈ W, q < 2 ^ b) (m bM : ℕ) (hm : m < 2 ^ bM)
    (hprod : (Alg.prodL W).1 < 2 ^ bM) (hm' : m * (Alg.prodL W).1 < 2 ^ bM) (hn : n < 2 ^ bM)
    (used P' : List ℕ) (npr nLr snapr nmr nur : List Γ') (v : St) (S : Stacks)
    (hSp : S np = encList P' ++ npr) (hSL : S nL = encodeNatΓ' L ++ .comma :: nLr)
    (hSsn : S snap = encList W ++ snapr) (hSa : S acc = encTblAsc L tb' ++ [.blank])
    (hSm : S nm = encodeNatΓ' m ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr))
    (hSu : S nu = encList used ++ nur) :
    (exSome np nL snap acc s t nm nu).Runs v S (fun v' S' =>
        (if n < m * (Alg.prodL W).1 then v'.flag = true ∧ S' np = .ket :: S np
          else v'.flag = decide (P' = []) ∧ S' np = S np) ∧
        S' nL = S nL ∧ S' snap = snapr ∧ S' acc = encTblAsc L Alg.emptyTbl ++ [.blank] ∧
        S' s = S s ∧ S' t = S t ∧
        S' nm = encodeNatΓ' (m * (Alg.prodL W).1) ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr) ∧
        S' nu = encList (W ++ used) ++ nur ∧
        ∀ k, k ≠ np → k ≠ nL → k ≠ snap → k ≠ acc → k ≠ s → k ≠ t → k ≠ nm → k ≠ nu → S' k = S k)
      (exSomeC L N' b W.length bM) := by
  have hd' := hd
  obtain ⟨hpL, hpsn, hpa, hps, hpt, hpm, hpu, hLsn, hLa, hLs, hLt, hLm, hLu, hsna, hsns, hsnt,
    hsnm, hsnu, has, hat, ham, hau, hst, hsm, hsu, htm, htu, hmu⟩ := hd
  have hLp := hpL.symm; have hsnp := hpsn.symm; have hap := hpa.symm; have hsp := hps.symm
  have htp := hpt.symm; have hmp := hpm.symm; have hup := hpu.symm
  have hsnL := hLsn.symm; have haL := hLa.symm; have hsL := hLs.symm; have htL := hLt.symm
  have hmL := hLm.symm; have huL := hLu.symm
  have hasn := hsna.symm; have hssn := hsns.symm; have htsn := hsnt.symm; have hmsn := hsnm.symm
  have husn := hsnu.symm
  have hsa := has.symm; have hta := hat.symm; have hma := ham.symm; have hua := hau.symm
  have hts := hst.symm; have hms := hsm.symm; have hus := hsu.symm
  have hmt := htm.symm; have hut := htu.symm; have hum := hmu.symm
  have hlm' : (Computability.encodeNat (m * (Alg.prodL W).1)).length ≤ bM :=
    encodeNat_length_le_of_lt_pow hm'
  unfold exSomeC
  -- stage 1: the product onto t
  have h1 := prodLF_le_B hsnt hsnp hsns hsnu htp hts htu hps hpu hsu W b hWb snapr v S hSsn
  rw [prodL_snd] at h1
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B bM + B bM + (W.length + 1) * B b +
      (L * (N' * (b + 1) + 1) + 2) + B b + (L + 1) * B b + (5 * B bM + 3)) h1
    fun v₁ S₁ ⟨hsn₁, ht₁, hp₁, hs₁, hu₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 2: m * prod onto s
  have hm₁ : S₁ nm = encodeNatΓ' m ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr) := by
    rw [hF₁ nm hmsn hmt hmp hms hmu, hSm]
  have h2 := mulC_le_B hmt hms hmp hmu hts htp htu hsp hsu hpu m (Alg.prodL W).1 bM hm hprod _
    (S t) v₁ S₁ hm₁ ht₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B bM + (W.length + 1) * B b +
      (L * (N' * (b + 1) + 1) + 2) + B b + (L + 1) * B b + (5 * B bM + 3)) h2
    fun v₂ S₂ ⟨hm₂, ht₂, hs₂, hp₂, hu₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: back onto nm
  have h3 := moveEntry_runs hsm hst hmt (Computability.encodeNat (m * (Alg.prodL W).1)) _ v₂ S₂ hs₂
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (W.length + 1) * B b +
      (L * (N' * (b + 1) + 1) + 2) + B b + (L + 1) * B b + (5 * B bM + 3)) h3
    fun v₃ S₃ ⟨_, _, _, hs₃, hm₃, ht₃, hF₃⟩ => ?_) (fun _ _ h => h)
    (by have := le_B_of_le_linear (b := bM)
          (n := 2 * (Computability.encodeNat (m * (Alg.prodL W).1)).length + 4) (by omega); omega)
  -- stage 4: used := W ++ used
  have hsn₃ : S₃ snap = encList W ++ snapr := by
    rw [hF₃ snap hsns hsnm hsnt, hF₂ snap hsnm hsnt hsns hsnp hsnu, hsn₁, hSsn]
  have hu₃ : S₃ nu = encList used ++ nur := by
    rw [hF₃ nu hus hum hut, hu₂, hu₁, hSu]
  have h4 := appendList_le_B hsnu hsnt hsns hut hus hts W used b hWb snapr nur v₃ S₃ hsn₃ hu₃
  refine Frag.runs_mono (Frag.seq_runs (t₂ :=
      (L * (N' * (b + 1) + 1) + 2) + B b + (L + 1) * B b + (5 * B bM + 3)) h4
    fun v₄ S₄ ⟨hsn₄, hu₄, ht₄, hs₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 5: drop the table
  have ha₄ : S₄ acc = encTblAsc L tb' ++ [.blank] := by
    rw [hF₄ acc hasn hau hat has, hF₃ acc has ham hat, hF₂ acc ham hat has hap hau,
      hF₁ acc hasn hat hap has hau, hSa]
  have hlen : (S₄ acc).length + 1 ≤ L * (N' * (b + 1) + 1) + 2 := by
    rw [ha₄, List.length_append, List.length_singleton]
    have := encTblAsc_length_le ht'; omega
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + (L + 1) * B b + (5 * B bM + 3))
    (clear_runs acc v₄ S₄) fun v₅ S₅ ⟨_, _, _, ha₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 6: L onto t
  have hL₅ : S₅ nL = encodeNatΓ' L ++ .comma :: nLr := by
    rw [hF₅ nL hLa, hF₄ nL hLsn hLu hLt hLs, hF₃ nL hLs hLm hLt, hF₂ nL hLm hLt hLs hLp hLu,
      hF₁ nL hLsn hLt hLp hLs hLu, hSL]
  have h6 := dup_le_B hLt hLs hts L b hLb nLr v₅ S₅ hL₅
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (L + 1) * B b + (5 * B bM + 3)) h6
    fun v₆ S₆ ⟨hL₆, ht₆, hs₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 7: the empty table
  have h7 := emptyTbl_le_B hta hts has L b hLb (S₅ t) v₆ S₆ ht₆
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * B bM + 3) h7
    fun v₇ S₇ ⟨ht₇, ha₇, hs₇, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 8: the exit test
  have hp₇ : S₇ np = encList P' ++ npr := by
    rw [hF₇ np hpt hpa hps, hF₆ np hpL hpt hps, hF₅ np hpa, hF₄ np hpsn hpu hpt hps,
      hF₃ np hps hpm hpt, hp₂, hp₁, hSp]
  have hm₇ : S₇ nm = encodeNatΓ' (m * (Alg.prodL W).1) ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr) := by
    rw [hF₇ nm hmt hma hms, hF₆ nm hmL hmt hms, hF₅ nm hma, hF₄ nm hmsn hmu hmt hms, hm₃, hm₂]; rfl
  have h8 := exTest_runs hd' n (m * (Alg.prodL W).1) bM hn hm' P' npr nmr v₇ S₇ hp₇ hm₇
  refine Frag.runs_mono h8 (fun v₈ S₈ ⟨hbr, hm₈, hsn₈, hs₈, ht₈, hF₈⟩ => ?_) le_rfl
  have hsn₇ : S₇ snap = snapr := by
    rw [hF₇ snap hsnt hsna hsns, hF₆ snap hsnL hsnt hsns, hF₅ snap hsna, hsn₄]
  have hs₇' : S₇ s = S s := by
    rw [hs₇, hs₆, hF₅ s hsa, hs₄, hs₃, hs₁]
  have ht₇' : S₇ t = S t := by
    rw [ht₇, hF₅ t hta, ht₄, ht₃, ht₂]
  have hu₇ : S₇ nu = encList (W ++ used) ++ nur := by
    rw [hF₇ nu hut hua hus, hF₆ nu huL hut hus, hF₅ nu hua, hu₄]
  have hL₇ : S₇ nL = S nL := by
    rw [hF₇ nL hLt hLa hLs, hL₆, hL₅, hSL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp₇] at hbr; rw [hSp]; exact hbr
  · rw [hF₈ nL hLp hLsn hLs hLt hLm, hL₇]
  · rw [hsn₈, hsn₇]
  · rw [hF₈ acc hap hasn has hat ham, ha₇, hF₆ acc haL hat has, ha₅]
  · rw [hs₈, hs₇']
  · rw [ht₈, ht₇']
  · rw [hm₈, hm₇]
  · rw [hF₈ nu hup husn hus hut hum, hu₇]
  · intro k hkp hkL hksn hka hks hkt hkm hku
    rw [hF₈ k hkp hksn hks hkt hkm, hF₇ k hkt hka hks, hF₆ k hkL hkt hks, hF₅ k hka,
      hF₄ k hksn hku hkt hks, hF₃ k hks hkm hkt, hF₂ k hkm hkt hks hkp hku,
      hF₁ k hksn hkt hkp hks hku]


/-! ### One element -/

theorem exBody_runs_none {np nL snap acc s t nm nu : K} (hd : Dist8 np nL snap acc s t nm nu)
    (L p : ℕ) (hL : 0 < L) (tb : Alg.Tbl) (N b Nb X : ℕ) (ht : TblBounded L tb N b)
    (hp : p < 2 ^ b) (hLb : L < 2 ^ b) (hN : N + 1 ≤ Nb) (hXb : b ≤ X)
    (hl : (Alg.dpStep L p tb).1 (1 % L) = none)
    (P' : List ℕ) (npr nLr : List Γ') (v : St) (S : Stacks)
    (hSp : S np = encList (p :: P') ++ npr) (hSL : S nL = encodeNatΓ' L ++ .comma :: nLr)
    (hSa : S acc = encTblAsc L tb ++ [.blank]) :
    (exBody np nL snap acc s t nm nu).Runs v S (fun v' S' =>
        v'.flag = decide (P' = []) ∧ S' np = encList P' ++ npr ∧ S' nL = S nL ∧
        S' snap = S snap ∧ S' acc = encTblAsc L (Alg.dpStep L p tb).1 ++ [.blank] ∧
        S' s = S s ∧ S' t = S t ∧ S' nm = S nm ∧ S' nu = S nu ∧
        ∀ k, k ≠ np → k ≠ nL → k ≠ snap → k ≠ acc → k ≠ s → k ≠ t → S' k = S k)
      (exC L Nb X) := by
  have hpsn : np ≠ snap := hd.2.1
  have hmsn : nm ≠ snap := hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm
  have husn : nu ≠ snap := hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm
  have h1 := exPre_runs hd L p hL tb N b ht hp hLb (encList P' ++ npr) nLr v S
    (by rw [hSp, encList_cons_append]) hSL hSa
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 13 * exY L Nb X + 1) h1
    fun v₁ S₁ ⟨hf₁, hp₁, hL₁, hsn₁, ha₁, hs₁, ht₁, hm₁, hu₁, hF₁⟩ => ?_) (fun _ _ h => h)
    (by have := exPreC_le L N Nb b X hN hXb; unfold exC; omega)
  rw [hl] at hsn₁ hf₁
  simp only [encSlot_none, List.singleton_append, decide_true] at hsn₁ hf₁
  refine Frag.ite_runs (t := 13 * exY L Nb X) (fun _ => ?_) (fun hc => by rw [hf₁] at hc; cases hc)
  have h2 := exNone_runs hpsn P' npr (S snap) v₁ S₁ hp₁ hsn₁
  refine Frag.runs_mono h2 (fun v₂ S₂ ⟨hf₂, hsn₂, hF₂⟩ => ⟨hf₂, ?_, ?_, hsn₂, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    (by have := three_le_exY L Nb X; omega)
  · rw [hF₂ np hpsn, hp₁]
  · rw [hF₂ nL hd.2.2.2.2.2.2.2.1, hL₁]
  · rw [hF₂ acc hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm, ha₁]
  · rw [hF₂ s hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm, hs₁]
  · rw [hF₂ t hd.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.symm, ht₁]
  · rw [hF₂ nm hmsn, hm₁]
  · rw [hF₂ nu husn, hu₁]
  · intro k hkp hkL hksn hka hks hkt
    rw [hF₂ k hksn, hF₁ k hkp hkL hksn hka hks hkt]

theorem exBody_runs_some {np nL snap acc s t nm nu : K} (hd : Dist8 np nL snap acc s t nm nu)
    (L n p : ℕ) (hL : 0 < L) (tb : Alg.Tbl) (N b Nb X : ℕ) (ht : TblBounded L tb N b)
    (hp : p < 2 ^ b) (hLb : L < 2 ^ b) (hN : N + 1 ≤ Nb) (hXb : b ≤ X)
    (W : List ℕ) (hl : (Alg.dpStep L p tb).1 (1 % L) = some W)
    (m bm bM : ℕ) (hm : m < 2 ^ bm) (hbm1 : 1 ≤ bm) (hbm : bm + b * (N + 1) ≤ bM)
    (hn : n < 2 ^ bM) (hXM : bM ≤ X) (hXN : 2 * (Nb + 2) * b + 4 ≤ X)
    (used P' : List ℕ) (npr nLr nmr nur : List Γ') (v : St) (S : Stacks)
    (hSp : S np = encList (p :: P') ++ npr) (hSL : S nL = encodeNatΓ' L ++ .comma :: nLr)
    (hSa : S acc = encTblAsc L tb ++ [.blank])
    (hSm : S nm = encodeNatΓ' m ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr))
    (hSu : S nu = encList used ++ nur) :
    (exBody np nL snap acc s t nm nu).Runs v S (fun v' S' =>
        (if n < m * (Alg.prodL W).1 then v'.flag = true ∧ S' np = .ket :: (encList P' ++ npr)
          else v'.flag = decide (P' = []) ∧ S' np = encList P' ++ npr) ∧
        S' nL = S nL ∧ S' snap = S snap ∧ S' acc = encTblAsc L Alg.emptyTbl ++ [.blank] ∧
        S' s = S s ∧ S' t = S t ∧
        S' nm = encodeNatΓ' (m * (Alg.prodL W).1) ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr) ∧
        S' nu = encList (W ++ used) ++ nur ∧
        ∀ k, k ≠ np → k ≠ nL → k ≠ snap → k ≠ acc → k ≠ s → k ≠ t → k ≠ nm → k ≠ nu → S' k = S k)
      (exC L Nb X) := by
  have ht' : TblBounded L (Alg.dpStep L p tb).1 (N + 1) b := tblBounded_dpStep ht hp
  have hW := ht' (1 % L) (Nat.mod_lt 1 hL) W hl
  have hpr := prodL_bounds hW.1 hW.2 hm hbm1
  have hbMle : 2 ^ (bm + b * (N + 1)) ≤ 2 ^ bM := Nat.pow_le_pow_right (by norm_num) hbm
  have h1 := exPre_runs hd L p hL tb N b ht hp hLb (encList P' ++ npr) nLr v S
    (by rw [hSp, encList_cons_append]) hSL hSa
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 13 * exY L Nb X + 1) h1
    fun v₁ S₁ ⟨hf₁, hp₁, hL₁, hsn₁, ha₁, hs₁, ht₁, hm₁, hu₁, hF₁⟩ => ?_) (fun _ _ h => h)
    (by have := exPreC_le L N Nb b X hN hXb; unfold exC; omega)
  rw [hl] at hsn₁ hf₁
  simp only [encSlot_some, Option.some_ne_none, decide_false] at hsn₁ hf₁
  refine Frag.ite_runs (t := 13 * exY L Nb X) (fun hc => by rw [hf₁] at hc; cases hc) (fun _ => ?_)
  have h2 := exSome_runs hd L n b hLb _ (N + 1) ht' W hW.2 m bM
    (lt_of_lt_of_le hm ((Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)).trans hbMle))
    (lt_of_lt_of_le hpr.1 hbMle) (lt_of_lt_of_le hpr.2 hbMle) hn used P' npr nLr (S snap) nmr nur
    v₁ S₁ hp₁ (by rw [hL₁, hSL]) hsn₁ ha₁ (by rw [hm₁, hSm]) (by rw [hu₁, hSu])
  refine Frag.runs_mono h2
    (fun v₂ S₂ ⟨hbr, hL₂, hsn₂, ha₂, hs₂, ht₂, hm₂, hu₂, hF₂⟩ => ⟨?_, ?_, hsn₂, ha₂, ?_, ?_, hm₂, hu₂, ?_⟩)
    (exSomeC_le L N Nb b bM X W.length hW.1 hN hXb hXM hXN)
  · rw [hp₁] at hbr; exact hbr
  · rw [hL₂, hL₁]
  · rw [hs₂, hs₁]
  · rw [ht₂, ht₁]
  · intro k hkp hkL hksn hka hks hkt hkm hku
    rw [hF₂ k hkp hkL hksn hka hks hkt hkm hku, hF₁ k hkp hkL hksn hka hks hkt]

/-! ### The loop -/

/-- Postcondition of the extraction loop relative to the entry stacks `S₀`:
the stacks hold `extractFin`, and `np` carries the success marker `ket`. -/
def ExPost (np nL snap acc s t nm nu : K) (L n : ℕ) (P : List ℕ) (m : ℕ) (used : List ℕ)
    (tb : Alg.Tbl) (npr nmr nur : List Γ') (S₀ S' : Stacks) : Prop :=
  S' np = (if (Alg.extractGo L n P m used tb).1.isSome then [Γ'.ket] else []) ++
      (encList (extractFin L n P m used tb).pool ++ npr) ∧
  S' nm = encodeNatΓ' (extractFin L n P m used tb).m ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr) ∧
  S' nu = encList (extractFin L n P m used tb).used ++ nur ∧
  S' acc = encTblAsc L (extractFin L n P m used tb).tbl ++ [.blank] ∧
  S' nL = S₀ nL ∧ S' snap = S₀ snap ∧ S' s = S₀ s ∧ S' t = S₀ t ∧
  ∀ k, k ≠ np → k ≠ nL → k ≠ snap → k ≠ acc → k ≠ s → k ≠ t → k ≠ nm → k ≠ nu → S' k = S₀ k

theorem exLoop_runs {np nL snap acc s t nm nu : K} (hd : Dist8 np nL snap acc s t nm nu)
    (L n b Nb bM X : ℕ) (hL : 0 < L) (hLb : L < 2 ^ b) (hn : n < 2 ^ bM) (hXb : b ≤ X)
    (hXM : bM ≤ X) (hXN : 2 * (Nb + 2) * b + 4 ≤ X) (P : List ℕ) (hb : ∀ p ∈ P, p < 2 ^ b) :
    ∀ (m : ℕ) (used : List ℕ) (tb : Alg.Tbl) (N bm : ℕ) (npr nLr nmr nur : List Γ') (v : St)
      (S : Stacks), TblBounded L tb N b → m < 2 ^ bm → 1 ≤ bm →
      bm + b * (N + P.length) ≤ bM → N + P.length ≤ Nb →
      S np = encList P ++ npr → S nL = encodeNatΓ' L ++ .comma :: nLr →
      S acc = encTblAsc L tb ++ [.blank] →
      S nm = encodeNatΓ' m ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr) →
      S nu = encList used ++ nur → v.flag = decide (P = []) →
      (Frag.loop (fun v => !v.flag) (exBody np nL snap acc s t nm nu)).Runs v S
        (fun _ S' => ExPost np nL snap acc s t nm nu L n P m used tb npr nmr nur S S')
        ((Alg.extractGo L n P m used tb).2 * (exC L Nb X + 1) + 1) := by
  induction P with
  | nil =>
    intro m used tb N bm npr nLr nmr nur v S ht hm hbm1 hbM hNb hSp hSL hSa hSm hSu hf
    have hc : (!v.flag) = false := by rw [hf]; rfl
    refine Frag.runs_mono (Frag.loop_runs_exit hc) (fun v' S' ⟨_, hS'⟩ => ?_)
      (by rw [extractGo_nil]; omega)
    rw [hS']
    refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, fun k _ _ _ _ _ _ _ _ => rfl⟩
    · rw [extractGo_nil, extractFin_nil, hSp]; rfl
    · rw [extractFin_nil, hSm]
    · rw [extractFin_nil, hSu]
    · rw [extractFin_nil, hSa]
  | cons p P' ih =>
    intro m used tb N bm npr nLr nmr nur v S ht hm hbm1 hbM hNb hSp hSL hSa hSm hSu hf
    have hp : p < 2 ^ b := hb p (List.mem_cons_self ..)
    have hbP : ∀ q ∈ P', q < 2 ^ b := fun q hq => hb q (List.mem_cons_of_mem _ hq)
    have hc : (!v.flag) = true := by rw [hf]; rfl
    simp only [List.length_cons] at hbM hNb
    have hN1 : N + 1 ≤ Nb := by omega
    have hsplit : b * (N + (P'.length + 1)) = b * (N + 1) + b * P'.length := by ring
    cases hl : (Alg.dpStep L p tb).1 (1 % L) with
    | none =>
      have hB := exBody_runs_none hd L p hL tb N b Nb X ht hp hLb hN1 hXb hl P' npr nLr v S hSp
        hSL hSa
      refine Frag.runs_mono (Frag.loop_runs_step
        (t₂ := (Alg.extractGo L n P' m used (Alg.dpStep L p tb).1).2 * (exC L Nb X + 1) + 1) hc hB
        fun v₁ S₁ ⟨hf₁, hp₁, hL₁, hsn₁, ha₁, hs₁, ht₁, hm₁, hu₁, hF₁⟩ => ?_) (fun _ _ h => h) ?_
      · have hrest := ih hbP m used _ (N + 1) bm npr nLr nmr nur v₁ S₁ (tblBounded_dpStep ht hp)
          hm hbm1 (by rw [show N + 1 + P'.length = N + (P'.length + 1) by omega]; exact hbM)
          (by omega) hp₁ (by rw [hL₁, hSL]) ha₁ (by rw [hm₁, hSm])
          (by rw [hu₁, hSu]) hf₁
        refine Frag.runs_mono hrest (fun v₂ S₂ hpost => ?_) le_rfl
        unfold ExPost at hpost ⊢
        rw [extractGo_cons_none L n p P' m used tb hl, extractFin_cons_none L n p P' m used tb hl]
        obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hpost
        refine ⟨h1, h2, h3, h4, by rw [h5, hL₁], by rw [h6, hsn₁], by rw [h7, hs₁],
          by rw [h8, ht₁], fun k hkp hkL hksn hka hks hkt hkm hku => ?_⟩
        rw [h9 k hkp hkL hksn hka hks hkt hkm hku, hF₁ k hkp hkL hksn hka hks hkt]
      · rw [extractGo_cons_none L n p P' m used tb hl]
        dsimp only
        have h := Nat.mul_le_mul_right (exC L Nb X + 1)
          (show (Alg.extractGo L n P' m used (Alg.dpStep L p tb).1).2 + 1 ≤
            (Alg.extractGo L n P' m used (Alg.dpStep L p tb).1).2 + (Alg.dpStep L p tb).2 + 1 by omega)
        rw [Nat.add_mul, one_mul] at h
        omega
    | some W =>
      have hW := (tblBounded_dpStep ht hp) (1 % L) (Nat.mod_lt 1 hL) W hl
      have hB := exBody_runs_some hd L n p hL tb N b Nb X ht hp hLb hN1 hXb W hl m bm bM hm hbm1
        (by omega) hn hXM hXN used P' npr nLr nmr nur v S hSp hSL hSa hSm hSu
      by_cases hlt : n < m * (Alg.prodL W).1
      · refine Frag.runs_mono (Frag.loop_runs_step (t₂ := 1) hc hB
          fun v₁ S₁ ⟨hbr, hL₁, hsn₁, ha₁, hs₁, ht₁, hm₁, hu₁, hF₁⟩ => ?_) (fun _ _ h => h) ?_
        · rw [if_pos hlt] at hbr
          obtain ⟨hf₁, hp₁⟩ := hbr
          have hc₁ : (!v₁.flag) = false := by rw [hf₁]; rfl
          refine Frag.runs_mono (Frag.loop_runs_exit hc₁) (fun v₂ S₂ ⟨_, hS₂⟩ => ?_) le_rfl
          rw [hS₂]
          unfold ExPost
          rw [extractGo_cons_some L n p P' m used tb W hl, extractFin_cons_some L n p P' m used tb W hl,
            if_pos hlt, if_pos hlt]
          exact ⟨by rw [hp₁]; rfl, hm₁, hu₁, ha₁, hL₁, hsn₁, hs₁, ht₁, hF₁⟩
        · rw [extractGo_cons_some L n p P' m used tb W hl, if_pos hlt]
          dsimp only
          have h := Nat.le_mul_of_pos_left (exC L Nb X + 1)
            (show 0 < (Alg.dpStep L p tb).2 + (Alg.prodL W).2 + 1 by omega)
          omega
      · refine Frag.runs_mono (Frag.loop_runs_step
          (t₂ := (Alg.extractGo L n P' (m * (Alg.prodL W).1) (W ++ used) Alg.emptyTbl).2 *
            (exC L Nb X + 1) + 1) hc hB
          fun v₁ S₁ ⟨hbr, hL₁, hsn₁, ha₁, hs₁, ht₁, hm₁, hu₁, hF₁⟩ => ?_) (fun _ _ h => h) ?_
        · rw [if_neg hlt] at hbr
          obtain ⟨hf₁, hp₁⟩ := hbr
          have hpr := prodL_bounds hW.1 hW.2 hm hbm1
          have hrest := ih hbP (m * (Alg.prodL W).1) (W ++ used) Alg.emptyTbl 0 (bm + b * (N + 1))
            npr nLr nmr nur v₁ S₁ (tblBounded_emptyTbl _ _ _) hpr.2 (by omega)
            (by rw [Nat.zero_add]; omega) (by omega) hp₁ (by rw [hL₁, hSL]) ha₁ hm₁ hu₁ hf₁
          refine Frag.runs_mono hrest (fun v₂ S₂ hpost => ?_) le_rfl
          unfold ExPost at hpost ⊢
          rw [extractGo_cons_some L n p P' m used tb W hl, extractFin_cons_some L n p P' m used tb W hl,
            if_neg hlt, if_neg hlt]
          obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hpost
          refine ⟨h1, h2, h3, h4, by rw [h5, hL₁], by rw [h6, hsn₁], by rw [h7, hs₁],
            by rw [h8, ht₁], fun k hkp hkL hksn hka hks hkt hkm hku => ?_⟩
          rw [h9 k hkp hkL hksn hka hks hkt hkm hku, hF₁ k hkp hkL hksn hka hks hkt hkm hku]
        · rw [extractGo_cons_some L n p P' m used tb W hl, if_neg hlt]
          dsimp only
          have h := Nat.mul_le_mul_right (exC L Nb X + 1)
            (show (Alg.extractGo L n P' (m * (Alg.prodL W).1) (W ++ used) Alg.emptyTbl).2 + 1 ≤
              (Alg.extractGo L n P' (m * (Alg.prodL W).1) (W ++ used) Alg.emptyTbl).2 +
                (Alg.dpStep L p tb).2 + (Alg.prodL W).2 + 1 by omega)
          rw [Nat.add_mul, one_mul] at h
          omega

/-! ### `extractGo` and `extract` -/

theorem extractGoF_runs {np nL snap acc s t nm nu : K} (hd : Dist8 np nL snap acc s t nm nu)
    (L n b Nb bM X : ℕ) (hL : 0 < L) (hLb : L < 2 ^ b) (hn : n < 2 ^ bM) (hXb : b ≤ X)
    (hXM : bM ≤ X) (hXN : 2 * (Nb + 2) * b + 4 ≤ X) (P : List ℕ) (hb : ∀ p ∈ P, p < 2 ^ b)
    (m : ℕ) (used : List ℕ) (tb : Alg.Tbl) (N bm : ℕ) (ht : TblBounded L tb N b) (hm : m < 2 ^ bm)
    (hbm1 : 1 ≤ bm) (hbM : bm + b * (N + P.length) ≤ bM) (hNb : N + P.length ≤ Nb)
    (npr nLr nmr nur : List Γ') (v : St) (S : Stacks)
    (hSp : S np = encList P ++ npr) (hSL : S nL = encodeNatΓ' L ++ .comma :: nLr)
    (hSa : S acc = encTblAsc L tb ++ [.blank])
    (hSm : S nm = encodeNatΓ' m ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr))
    (hSu : S nu = encList used ++ nur) :
    (extractGoF np nL snap acc s t nm nu).Runs v S (fun v' S' =>
        v'.flag = (Alg.extractGo L n P m used tb).1.isSome ∧
        S' np = encList (extractFin L n P m used tb).pool ++ npr ∧
        S' nm = encodeNatΓ' (extractFin L n P m used tb).m ++ .comma ::
          (encodeNatΓ' n ++ .comma :: nmr) ∧
        S' nu = encList (extractFin L n P m used tb).used ++ nur ∧
        S' acc = encTblAsc L (extractFin L n P m used tb).tbl ++ [.blank] ∧
        (∀ m' U, (Alg.extractGo L n P m used tb).1 = some (m', U) →
          S' nm = encodeNatΓ' m' ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr) ∧
          S' nu = encList U ++ nur) ∧
        S' nL = S nL ∧ S' snap = S snap ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ np → k ≠ nL → k ≠ snap → k ≠ acc → k ≠ s → k ≠ t → k ≠ nm → k ≠ nu → S' k = S k)
      (((Alg.extractGo L n P m used tb).2 + 1) * (exC L Nb X + 5)) := by
  -- stage 1: flag := (pool empty)
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (Alg.extractGo L n P m used tb).2 * (exC L Nb X + 1) + 1 + 3) (peekBra_runs np v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) ?_
  · rw [hS₁]
    have hf₁ : v₁.flag = decide (P = []) := by
      rw [hv₁]; show decide _ = _; rw [hSp, decide_head?_encList_bra]
    -- stage 2: the loop
    have h2 := exLoop_runs hd L n b Nb bM X hL hLb hn hXb hXM hXN P hb m used tb N bm npr nLr nmr
      nur v₁ S ht hm hbm1 hbM hNb hSp hSL hSa hSm hSu hf₁
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 3) h2
      fun v₂ S₂ ⟨hp₂, hm₂, hu₂, ha₂, hL₂, hsn₂, hs₂, ht₂, hF₂⟩ => ?_) (fun _ _ h => h) le_rfl
    -- stage 3: read the marker
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 2) (peekKet_runs np v₂ S₂)
      fun v₃ S₃ ⟨hv₃, hS₃⟩ => ?_) (fun _ _ h => h) le_rfl
    rw [hS₃]
    have hf₃ : v₃.flag = (Alg.extractGo L n P m used tb).1.isSome := by
      rw [hv₃]; show decide _ = _
      rw [hp₂]
      cases (Alg.extractGo L n P m used tb).1.isSome
      · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append]
        exact head?_encList_ne_ket' _ _
      · rfl
    have hsome : ∀ m' U, (Alg.extractGo L n P m used tb).1 = some (m', U) →
        S₂ nm = encodeNatΓ' m' ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr) ∧
        S₂ nu = encList U ++ nur := by
      intro m' U h
      obtain ⟨h1, h2⟩ := extractGo_some L n P m used tb m' U h
      rw [hm₂, hu₂, h1, h2]; exact ⟨rfl, rfl⟩
    -- stage 4: remove the marker
    refine Frag.ite_runs (t := 1) (fun hc => ?_) (fun hc => ?_)
    · rw [hf₃] at hc
      refine Frag.runs_mono (popTop_runs np v₃ S₂) (fun v₄ S₄ ⟨hv₄, hS₄⟩ => ?_) le_rfl
      rw [hS₄, hv₄]
      refine ⟨hf₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Function.update_self, hp₂, hc]; rfl
      · rw [Function.update_of_ne hd.2.2.2.2.2.1.symm, hm₂]
      · rw [Function.update_of_ne hd.2.2.2.2.2.2.1.symm, hu₂]
      · rw [Function.update_of_ne hd.2.2.1.symm, ha₂]
      · intro m' U h; rw [Function.update_of_ne hd.2.2.2.2.2.1.symm,
          Function.update_of_ne hd.2.2.2.2.2.2.1.symm]; exact hsome m' U h
      · rw [Function.update_of_ne hd.1.symm, hL₂]
      · rw [Function.update_of_ne hd.2.1.symm, hsn₂]
      · rw [Function.update_of_ne hd.2.2.2.1.symm, hs₂]
      · rw [Function.update_of_ne hd.2.2.2.2.1.symm, ht₂]
      · intro k hkp hkL hksn hka hks hkt hkm hku
        rw [Function.update_of_ne hkp, hF₂ k hkp hkL hksn hka hks hkt hkm hku]
    · rw [hf₃] at hc
      refine Frag.runs_mono (Frag.skip_runs v₃ S₂) (fun v₄ S₄ ⟨hv₄, hS₄⟩ => ?_) le_rfl
      rw [hS₄, hv₄]
      refine ⟨hf₃, ?_, hm₂, hu₂, ha₂, hsome, hL₂, hsn₂, hs₂, ht₂, hF₂⟩
      rw [hp₂, hc]; rfl
  · have h := Nat.mul_le_mul_left (Alg.extractGo L n P m used tb).2
      (show exC L Nb X + 1 ≤ exC L Nb X + 5 by omega)
    rw [Nat.add_mul, one_mul]
    omega

/-- The bit-length argument of `extractF`'s budget: `3 |P| b + 5 b + 5`. -/
def exX (l b : ℕ) : ℕ := 3 * l * b + 5 * b + 5

theorem extractF_le_B {np nL snap acc s t nm nu : K} (hd : Dist8 np nL snap acc s t nm nu)
    (L n b : ℕ) (hL : 0 < L) (hLb : L < 2 ^ b) (hn : n < 2 ^ b) (P : List ℕ)
    (hb : ∀ p ∈ P, p < 2 ^ b) (npr nLr nmr : List Γ') (v : St) (S : Stacks)
    (hSp : S np = encList P ++ npr) (hSL : S nL = encodeNatΓ' L ++ .comma :: nLr)
    (hSa : S acc = []) (hSn : S nm = encodeNatΓ' n ++ .comma :: nmr) :
    (extractF np nL snap acc s t nm nu).Runs v S (fun v' S' =>
        v'.flag = (Alg.extract L n P).1.isSome ∧
        S' np = encList (extractFin L n P 1 [] Alg.emptyTbl).pool ++ npr ∧
        S' nm = encodeNatΓ' (extractFin L n P 1 [] Alg.emptyTbl).m ++ .comma ::
          (encodeNatΓ' n ++ .comma :: nmr) ∧
        S' nu = encList (extractFin L n P 1 [] Alg.emptyTbl).used ++ S nu ∧
        S' acc = encTblAsc L (extractFin L n P 1 [] Alg.emptyTbl).tbl ++ [.blank] ∧
        (∀ m' U, (Alg.extract L n P).1 = some (m', U) →
          S' nm = encodeNatΓ' m' ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr) ∧
          S' nu = encList U ++ S nu) ∧
        S' nL = S nL ∧ S' snap = S snap ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ np → k ≠ nL → k ≠ snap → k ≠ acc → k ≠ s → k ≠ t → k ≠ nm → k ≠ nu → S' k = S k)
      (((Alg.extract L n P).2 + 1) * (25 * exY L P.length (exX P.length b))) := by
  have hd' := hd
  obtain ⟨hpL, hpsn, hpa, hps, hpt, hpm, hpu, hLsn, hLa, hLs, hLt, hLm, hLu, hsna, hsns, hsnt,
    hsnm, hsnu, has, hat, ham, hau, hst, hsm, hsu, htm, htu, hmu⟩ := hd
  have hts := hst.symm; have hta := hat.symm; have hmt := htm.symm
  have hb1 : b ≠ 0 := by rintro rfl; simp at hLb; omega
  have h1lt : 1 < 2 ^ b := Nat.one_lt_two_pow hb1
  set X := exX P.length b with hX
  set E := exY L P.length X with hE
  have hY := B_le_exY L P.length X
  have hBb : B b ≤ B X := B_mono (by rw [hX, exX]; omega)
  have h3 := three_le_exY L P.length X
  have hL2 : L + 1 ≤ (L + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have hLB : (L + 1) * B b ≤ E := by
    rw [hE]; unfold exY
    calc (L + 1) * B b ≤ ((L + 1) ^ 2 * (P.length + 2)) * B X :=
          Nat.mul_le_mul (by nlinarith) hBb
      _ = _ := rfl
  show (extractF np nL snap acc s t nm nu).Runs v S _ (((Alg.extract L n P).2 + 1) * (25 * E))
  -- stage 1: m := 1
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1 + B b + (L + 1) * B b +
      ((Alg.extract L n P).2 + 1) * (exC L P.length X + 5)) (pushNum_le_B nm 1 b h1lt v S)
    fun v₁ S₁ ⟨_, hm₁, hF₁⟩ => ?_) (fun _ _ h => h) ?_
  · -- stage 2: used := []
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + (L + 1) * B b +
        ((Alg.extract L n P).2 + 1) * (exC L P.length X + 5)) (Frag.pushSym_runs nu .bra v₁ S₁)
      fun v₂ S₂ ⟨_, hS₂⟩ => ?_) (fun _ _ h => h) (by omega)
    rw [hS₂]
    -- stage 3: L onto t
    have hL₂ : Function.update S₁ nu (.bra :: S₁ nu) nL = encodeNatΓ' L ++ .comma :: nLr := by
      rw [Function.update_of_ne hLu, hF₁ nL hLm, hSL]
    have h3' := dup_le_B hLt hLs hts L b hLb nLr v₂ _ hL₂
    refine Frag.runs_mono (Frag.seq_runs (t₂ := (L + 1) * B b +
        ((Alg.extract L n P).2 + 1) * (exC L P.length X + 5)) h3'
      fun v₃ S₃ ⟨hL₃, ht₃, hs₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
    -- stage 4: the empty table
    have h4 := emptyTbl_le_B hta hts has L b hLb _ v₃ S₃ ht₃
    refine Frag.runs_mono (Frag.seq_runs
      (t₂ := ((Alg.extract L n P).2 + 1) * (exC L P.length X + 5)) h4
      fun v₄ S₄ ⟨ht₄, ha₄, hs₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
    -- stage 5: the loop
    have ha₄' : S₄ acc = encTblAsc L Alg.emptyTbl ++ [.blank] := by
      rw [ha₄, hF₃ acc hLa.symm hat has, Function.update_of_ne hau, hF₁ acc ham, hSa]
    have hp₄ : S₄ np = encList P ++ npr := by
      rw [hF₄ np hpt hpa hps, hF₃ np hpL hpt hps, Function.update_of_ne hpu, hF₁ np hpm, hSp]
    have hL₄ : S₄ nL = encodeNatΓ' L ++ .comma :: nLr := by
      rw [hF₄ nL hLt hLa hLs, hL₃, hL₂]
    have hm₄ : S₄ nm = encodeNatΓ' 1 ++ .comma :: (encodeNatΓ' n ++ .comma :: nmr) := by
      rw [hF₄ nm hmt ham.symm hsm.symm, hF₃ nm hLm.symm hmt hsm.symm, Function.update_of_ne hmu,
        hm₁, hSn]
    have hu₄ : S₄ nu = encList [] ++ S nu := by
      rw [hF₄ nu htu.symm hau.symm hsu.symm, hF₃ nu hLu.symm htu.symm hsu.symm,
        Function.update_self, hF₁ nu hmu.symm, encList_nil]; rfl
    have hbM : 1 + b * (0 + P.length) ≤ b * (P.length + 1) + 1 := by nlinarith
    have hn' : n < 2 ^ (b * (P.length + 1) + 1) :=
      lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
    have h5 := extractGoF_runs hd' L n b P.length (b * (P.length + 1) + 1) X hL hLb hn'
      (by rw [hX, exX]; omega) (by rw [hX, exX]; nlinarith) (by rw [hX, exX]; nlinarith) P hb
      1 [] Alg.emptyTbl 0 1 (tblBounded_emptyTbl _ _ _) (by norm_num) le_rfl hbM (by omega)
      npr nLr nmr (S nu) v₄ S₄ hp₄ hL₄ ha₄' hm₄ hu₄
    refine Frag.runs_mono h5 (fun v₅ S₅ ⟨hf₅, hp₅, hm₅, hu₅, ha₅, hsome₅, hL₅, hsn₅, hs₅, ht₅, hF₅⟩
      => ⟨hf₅, hp₅, hm₅, hu₅, ha₅, hsome₅, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
    · rw [hL₅, hL₄, hSL]
    · rw [hsn₅, hF₄ snap hsnt hsna hsns, hF₃ snap hLsn.symm hsnt hsns, Function.update_of_ne hsnu,
        hF₁ snap hsnm]
    · rw [hs₅, hs₄, hs₃, Function.update_of_ne hsu, hF₁ s hsm]
    · rw [ht₅, ht₄, Function.update_of_ne htu, hF₁ t htm]
    · intro k hkp hkL hksn hka hks hkt hkm hku
      rw [hF₅ k hkp hkL hksn hka hks hkt hkm hku, hF₄ k hkt hka hks, hF₃ k hkL hkt hks,
        Function.update_of_ne hku, hF₁ k hkm]
  · -- the budget
    have hc : exC L P.length X + 5 + (1 + B b + (L + 1) * B b + B b) ≤ 25 * E := by
      have : B b ≤ E := hBb.trans hY
      unfold exC; rw [← hE]; omega
    have h := Nat.mul_le_mul_left ((Alg.extract L n P).2 + 1) hc
    rw [Nat.mul_add] at h
    have h' := Nat.le_mul_of_pos_left (1 + B b + (L + 1) * B b + B b)
      (show 0 < (Alg.extract L n P).2 + 1 by omega)
    omega

end Carmichael.TM
