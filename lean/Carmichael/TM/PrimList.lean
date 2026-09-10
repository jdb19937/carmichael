import Carmichael.TM.Canon
import Carmichael.TM.Lists
import Carmichael.Algorithm

/-!
# Route T: subset products, coprimality, list product (sortie T3b)

Machine fragments refining the Route A list primitives `Alg.prodL`,
`Alg.coprimeTo`, `Alg.mulAll`, `Alg.divisorsOf` (Algorithm.lean), each with
an EXACT postcondition (`encodeNatΓ' (Alg.f args).1` for numbers,
`encList (Alg.f args).1` for lists in the SAME order as the Lean function,
`v'.flag = (Alg.f args).1` for Booleans) and a step bound of the form
`((Alg.f args).2 + 1) * B b'` with `b'` affine in the input bit bound `b`.

## Stack allocation (`K = Fin 8`; every named stack pairwise distinct)

Every scratch stack is RESTORED (`S' k = S k`) and need not be empty, so a
caller may pass stacks holding its own data as scratch.  Operands are
`encodeNatΓ' a ++ comma :: rest` (numbers) and `encList l ++ rest` (lists).

| fragment | operands | result | scratch (restored) | registers |
|---|---|---|---|---|
| `prodLF x w c s t` | list on `x` (restored) | `encodeNatΓ' (Alg.prodL S).1` pushed on `w` | `c` (copy of the list), `s`, `t` | nothing claimed |
| `coprimeToF x y z s t u` | list on `x` (restored), `k` on `y` (restored) | `flag := (Alg.coprimeTo Q k).1` | `z` (processed entries), `s`, `t`, `u` | `flag` only |
| `mulAllF x y r s t` | list on `x` (CONSUMED), `q` on `y` (restored) | `x := encList (Alg.mulAll q ds).1 ++ xr` | `r` (open list of products), `s`, `t` | nothing claimed |
| `divisorsOfF x z a c s t` | list on `x` (CONSUMED) | `x := encList (Alg.divisorsOf Q).1 ++ xr` | `z` (reversed `Q`), `a` (reversed accumulator), `c`, `s`, `t` | nothing claimed |

Inside `coprimeToF`, `modC` uses the data stacks `x`, `y`, `z` as its scratch
(they are restored by `modC`); inside `divisorsOfF`, `mulAllF` uses `x` (the
consumed input stack) as its open-list stack.  Loop control is `flag`
(`forEntries` / `peekBraOr`); `coprimeToF` keeps its "divisor found" marker
in `cmp` across the loop (`isZero`, `dropNum`, `moveEntry`, `peekBraOr` all
preserve `cmp`; `dup`/`modC` run before `isZero` sets it).

## Loops

`Alg.prodL`, `Alg.mulAll` are `forEntries` loops (one body per entry, the
uniform-cost rule).  `Alg.divisorsOf` processes `Q` from its LAST element
(the recursion returns before multiplying): the machine reverses `Q` once and
folds head-first over `Q.reverse`; the accumulator after `i` iterations is
exactly `(Alg.divisorsOf ((Q.reverse.take i).reverse)).1` (kept reversed on
its stack so that `acc ++ acc.map (· * q)` is one `appendList`), and its
per-iteration cost grows like `2 ^ i`, so the loop uses the Σ-cost rules
`Frag.loop_runs'` / `forEntries_runs'` (per-iteration budget `t i`).
`Alg.coprimeTo` early-exits, so it is a `Frag.loop` whose test reads `flag`
(set by `peekBraOr` = "divisor found ∨ list exhausted"); its iteration count
`cpIter Q k` equals `(Alg.coprimeTo Q k).2` exactly.
-/

namespace Carmichael.TM

open Turing Turing.TM2 Turing.TM2.Stmt Computability

/-! ### Route A facts -/

theorem prodL_fst (S : List ℕ) : (Alg.prodL S).1 = S.prod := by
  induction S with
  | nil => rfl
  | cons p S ih => simp [Alg.prodL, ih]

theorem prodL_snd (S : List ℕ) : (Alg.prodL S).2 = S.length := by
  induction S with
  | nil => rfl
  | cons p S ih => simp [Alg.prodL, ih]

theorem mulAll_fst (q : ℕ) (ds : List ℕ) : (Alg.mulAll q ds).1 = ds.map (· * q) := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [Alg.mulAll, ih]

theorem mulAll_snd (q : ℕ) (ds : List ℕ) : (Alg.mulAll q ds).2 = ds.length := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [Alg.mulAll, ih]

theorem divisorsOf_cons (q : ℕ) (Q : List ℕ) :
    (Alg.divisorsOf (q :: Q)).1 = (Alg.divisorsOf Q).1 ++ (Alg.divisorsOf Q).1.map (· * q) := by
  simp [Alg.divisorsOf, mulAll_fst]

theorem divisorsOf_length (Q : List ℕ) : (Alg.divisorsOf Q).1.length = 2 ^ Q.length := by
  induction Q with
  | nil => rfl
  | cons q Q ih => rw [divisorsOf_cons, List.length_append, List.length_map, ih]; simp [pow_succ]; ring

theorem divisorsOf_snd (Q : List ℕ) : (Alg.divisorsOf Q).2 = 2 ^ Q.length - 1 := by
  induction Q with
  | nil => rfl
  | cons q Q ih =>
    have h1 : 1 ≤ 2 ^ Q.length := Nat.one_le_two_pow
    simp only [Alg.divisorsOf, mulAll_snd, divisorsOf_length, ih, List.length_cons, pow_succ]
    omega

/-- A product of numbers below `2 ^ b` is at most `2 ^ (length * b)`. -/
theorem prod_le_two_pow {l : List ℕ} {b : ℕ} (hb : ∀ p ∈ l, p < 2 ^ b) :
    l.prod ≤ 2 ^ (l.length * b) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hb p (List.mem_cons_self ..)
    have ih' := ih (fun q hq => hb q (List.mem_cons_of_mem _ hq))
    rw [List.prod_cons, List.length_cons, add_mul, one_mul, pow_add, mul_comm]
    exact Nat.mul_le_mul ih' hp.le

/-- Every subset product of `Q` (elements below `2 ^ b`) is at most `2 ^ (|Q| * b)`. -/
theorem divisorsOf_mem_le {Q : List ℕ} {b : ℕ} (hb : ∀ q ∈ Q, q < 2 ^ b) :
    ∀ d ∈ (Alg.divisorsOf Q).1, d ≤ 2 ^ (Q.length * b) := by
  induction Q with
  | nil => intro d hd; simp [Alg.divisorsOf] at hd; simp [hd]
  | cons q Q ih =>
    intro d hd
    have hq := hb q (List.mem_cons_self ..)
    have ih' := ih (fun q' hq' => hb q' (List.mem_cons_of_mem _ hq'))
    rw [divisorsOf_cons, List.mem_append, List.mem_map] at hd
    rw [List.length_cons, add_mul, one_mul, pow_add]
    rcases hd with hd | ⟨d', hd', rfl⟩
    · exact (ih' d hd).trans (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos b))
    · exact Nat.mul_le_mul (ih' d' hd') hq.le

/-- The iteration count of `Alg.coprimeTo Q k`: the position of the first
divisor plus one, or `|Q|` if there is none. -/
def cpIter : List ℕ → ℕ → ℕ
  | [], _ => 0
  | q :: Q, k => if k % q = 0 then 1 else cpIter Q k + 1

theorem coprimeTo_snd (Q : List ℕ) (k : ℕ) : (Alg.coprimeTo Q k).2 = cpIter Q k := by
  induction Q with
  | nil => rfl
  | cons q Q ih =>
    simp only [Alg.coprimeTo, cpIter]
    split_ifs <;> simp [ih]

theorem cpIter_le_length (Q : List ℕ) (k : ℕ) : cpIter Q k ≤ Q.length := by
  induction Q with
  | nil => simp [cpIter]
  | cons q Q ih => simp only [cpIter, List.length_cons]; split_ifs <;> omega

theorem lt_cpIter_iff (Q : List ℕ) (k i : ℕ) :
    i < cpIter Q k ↔ i < Q.length ∧ ∀ q ∈ Q.take i, k % q ≠ 0 := by
  induction Q generalizing i with
  | nil => simp [cpIter]
  | cons q Q ih =>
    cases i with
    | zero =>
      simp only [cpIter, List.length_cons, List.take_zero, List.not_mem_nil, ne_eq, false_imp_iff,
        implies_true, and_true]
      split_ifs <;> omega
    | succ j =>
      simp only [cpIter, List.length_cons, List.take_succ_cons, List.mem_cons, forall_eq_or_imp]
      split_ifs with h
      · simp [h]
      · rw [Nat.add_lt_add_iff_right, Nat.add_lt_add_iff_right, ih]
        tauto

theorem coprimeTo_fst' (Q : List ℕ) (k : ℕ) :
    (Alg.coprimeTo Q k).1 = decide (∀ q ∈ Q, k % q ≠ 0) := by
  induction Q with
  | nil => simp [Alg.coprimeTo]
  | cons q Q ih =>
    simp only [Alg.coprimeTo]
    split_ifs with h <;> simp [ih, h]

theorem forall_take_cpIter_iff (Q : List ℕ) (k : ℕ) :
    (∀ q ∈ Q.take (cpIter Q k), k % q ≠ 0) ↔ ∀ q ∈ Q, k % q ≠ 0 := by
  constructor
  · intro h
    by_cases hQ : Q.length ≤ cpIter Q k
    · rwa [List.take_of_length_le hQ] at h
    · exact absurd ((lt_cpIter_iff Q k _).2 ⟨by omega, h⟩) (lt_irrefl _)
  · intro h q hq; exact h q (List.mem_of_mem_take hq)

theorem coprimeTo_fst (Q : List ℕ) (k : ℕ) :
    (Alg.coprimeTo Q k).1 = decide (∀ q ∈ Q.take (cpIter Q k), k % q ≠ 0) := by
  rw [coprimeTo_fst']
  simp only [forall_take_cpIter_iff]

/-! ### Budget helpers -/

/-- Scaling the argument of `B` scales the budget cubically. -/
theorem B_scale (c m : ℕ) : (c + 1) ^ 3 * B m = B ((c + 1) * m + 2 * c) := by
  unfold B
  have : (c + 1) * m + 2 * c + 2 = (c + 1) * (m + 2) := by ring
  rw [this, mul_pow]; ring

theorem two_pow_mul_le (n : ℕ) : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self

/-- `∑_{i<n} ((2^i + 1) * C + 2) + 2 ≤ 2^n * (2 C + 2)`. -/
theorem sum_geom_bound (C n : ℕ) :
    ∑ i ∈ Finset.range n, ((2 ^ i + 1) * C + 2) + 2 ≤ 2 ^ n * (2 * C + 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    nlinarith

/-! ### Σ-cost loop rules -/

/-- `Frag.loop_runs` with a per-iteration budget `t i`. -/
theorem Frag.loop_runs' {c : St → Bool} {Bd : Frag} (I : ℕ → St → Stacks → Prop) (n : ℕ)
    (t : ℕ → ℕ) {v S}
    (h0 : I 0 v S)
    (hc : ∀ i < n, ∀ v S, I i v S → c v = true)
    (hn : ∀ v S, I n v S → c v = false)
    (hb : ∀ i < n, ∀ v S, I i v S → Bd.Runs v S (I (i + 1)) (t i)) :
    (Frag.loop c Bd).Runs v S (fun v S => I n v S ∧ c v = false)
      (∑ i ∈ Finset.range n, (t i + 1) + 1) := by
  constructor
  intro Λ M ι e hI
  suffices key : ∀ m i, i + m = n → ∀ v S, I i v S →
      ∃ n', n' ≤ ∑ j ∈ Finset.Ico i n, (t j + 1) + 1 ∧ ∃ v' S',
        RunsTo M n' ⟨some (ι none), v, S⟩ ⟨some e, v', S'⟩ ∧ I n v' S' ∧ c v' = false by
    rw [Finset.range_eq_Ico]
    exact key n 0 (by omega) v S h0
  intro m
  induction m with
  | zero =>
    intro i hi v S hIv
    obtain rfl : i = n := by omega
    have hcv := hn v S hIv
    refine ⟨1, by simp, v, S, ?_, hIv, hcv⟩
    refine runsTo_succ ?_ (runsTo_zero M _)
    tm_step none [Frag.loop, hcv]
  | succ m ih =>
    intro i hi v S hIv
    have hcv := hc i (by omega) v S hIv
    obtain ⟨n₁, hn₁, v₁, S₁, hr₁, hI₁⟩ :=
      (hb i (by omega) v S hIv).run M _ _ (Frag.loop_installed_body hI)
    obtain ⟨n₂, hn₂, v₂, S₂, hr₂, hI₂, hc₂⟩ := ih (i + 1) (by omega) v₁ S₁ hI₁
    refine ⟨n₁ + n₂ + 1, ?_, v₂, S₂, ?_, hI₂, hc₂⟩
    · rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]; omega
    · refine runsTo_succ ?_ (runsTo_trans hr₁ hr₂)
      tm_step none [Frag.loop, hcv, Function.comp]

/-- `forEntries_runs` with a per-entry budget `t i`. -/
theorem forEntries_runs' {x : K} {body : Frag} (L : List (List Bool)) (xr : List Γ')
    (P : ℕ → Stacks → Prop) (t : ℕ → ℕ) (v : St) (S : Stacks)
    (hS : S x = encListB L ++ xr) (h0 : P 0 S)
    (hb : ∀ (i : ℕ) (l : List Bool) (L' : List (List Bool)), L.drop i = l :: L' →
      ∀ (v : St) (S : Stacks), P i S → S x = bits l ++ .comma :: (encListB L' ++ xr) →
      body.Runs v S (fun _ S' => P (i + 1) S' ∧ S' x = encListB L' ++ xr) (t i)) :
    (forEntries x body).Runs v S
      (fun v' S' => v'.flag = true ∧ P L.length S' ∧ S' x = .bra :: xr)
      (∑ i ∈ Finset.range L.length, (t i + 2) + 2) := by
  refine Frag.runs_mono (Frag.seq_runs (t₂ := ∑ i ∈ Finset.range L.length, (t i + 2) + 1)
    (peekBra_runs x v S) fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₁, hS₁]
  have hloop := Frag.loop_runs' (c := fun v => !v.flag) (Bd := body.seq (peekBra x))
    (ForInv x L xr P) L.length (fun i => t i + 1)
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
  refine Frag.runs_mono hloop (fun v' S' ⟨⟨_, hP, hx, _⟩, hc⟩ => ⟨?_, hP, ?_⟩) ?_
  · simpa using hc
  · rw [hx, List.drop_length]; rfl
  · have : ∀ i, t i + 1 + 1 = t i + 2 := fun i => rfl
    simp only [this]; omega

theorem map_encodeNat_drop_eq_cons {l : List ℕ} {i : ℕ} {e : List Bool} {L' : List (List Bool)}
    (h : (l.map Computability.encodeNat).drop i = e :: L') :
    ∃ a l', l.drop i = a :: l' ∧ e = Computability.encodeNat a ∧
      L' = l'.map Computability.encodeNat := by
  rw [← List.map_drop, List.map_eq_cons_iff] at h
  obtain ⟨a, l', h1, h2, h3⟩ := h
  exact ⟨a, l', h1, h2.symm, h3.symm⟩

/-- ℕ-level `forEntries` rule with a per-entry budget: the body receives the
top entry as `encodeNatΓ' a` with `l.drop i = a :: l'`. -/
theorem forEntriesN_runs' {x : K} {body : Frag} (l : List ℕ) (xr : List Γ')
    (P : ℕ → Stacks → Prop) (t : ℕ → ℕ) (v : St) (S : Stacks)
    (hS : S x = encList l ++ xr) (h0 : P 0 S)
    (hb : ∀ (i : ℕ) (a : ℕ) (l' : List ℕ), l.drop i = a :: l' →
      ∀ (v : St) (S : Stacks), P i S → S x = encodeNatΓ' a ++ .comma :: (encList l' ++ xr) →
      body.Runs v S (fun _ S' => P (i + 1) S' ∧ S' x = encList l' ++ xr) (t i)) :
    (forEntries x body).Runs v S
      (fun v' S' => v'.flag = true ∧ P l.length S' ∧ S' x = .bra :: xr)
      (∑ i ∈ Finset.range l.length, (t i + 2) + 2) := by
  rw [encList_eq] at hS
  have h := forEntries_runs' (l.map Computability.encodeNat) xr P t v S hS h0
    (fun i e L' hdrop w T hP hT => by
      obtain ⟨a, l', hl, rfl, rfl⟩ := map_encodeNat_drop_eq_cons hdrop
      rw [← encList_eq, ← encodeNatΓ'_eq] at hT
      refine Frag.runs_mono (hb i a l' hl w T hP hT) (fun _ T' ⟨hP', hx'⟩ => ⟨hP', ?_⟩) le_rfl
      rw [hx', encList_eq])
  simpa only [List.length_map] using h

/-- ℕ-level `forEntries` rule with a uniform per-entry budget. -/
theorem forEntriesN_runs {x : K} {body : Frag} (l : List ℕ) (xr : List Γ')
    (P : ℕ → Stacks → Prop) (t : ℕ) (v : St) (S : Stacks)
    (hS : S x = encList l ++ xr) (h0 : P 0 S)
    (hb : ∀ (i : ℕ) (a : ℕ) (l' : List ℕ), l.drop i = a :: l' →
      ∀ (v : St) (S : Stacks), P i S → S x = encodeNatΓ' a ++ .comma :: (encList l' ++ xr) →
      body.Runs v S (fun _ S' => P (i + 1) S' ∧ S' x = encList l' ++ xr) t) :
    (forEntries x body).Runs v S
      (fun v' S' => v'.flag = true ∧ P l.length S' ∧ S' x = .bra :: xr)
      (l.length * (t + 2) + 2) := by
  refine Frag.runs_mono (forEntriesN_runs' l xr P (fun _ => t) v S hS h0 hb) (fun _ _ h => h) ?_
  simp [Finset.sum_const, Finset.card_range]

/-! ### A state-dependent single-bit push -/

/-- Push the bit `c v` on stack `k`. -/
def pushBit (k : K) (c : St → Bool) : Frag := Frag.straight (push k (fun v => .bit (c v)))

theorem pushBit_runs (k : K) (c : St → Bool) (v : St) (S : Stacks) :
    (pushBit k c).Runs v S
      (fun v' S' => v' = v ∧ S' = Function.update S k (.bit (c v) :: S k)) 1 := by
  constructor
  intro Λ M ι e hI
  refine ⟨1, le_rfl, v, Function.update S k (.bit (c v) :: S k), ?_, rfl, rfl⟩
  refine runsTo_succ ?_ (runsTo_zero M _)
  tm_step () [pushBit, Frag.straight]

/-! ### `Alg.prodL`: the product of a list -/

theorem prodL_le_two_pow {l : List ℕ} {b : ℕ} (hb : ∀ p ∈ l, p < 2 ^ b) :
    (Alg.prodL l).1 ≤ 2 ^ (l.length * b) := by
  rw [prodL_fst]; exact prod_le_two_pow hb

theorem take_prod_lt {l : List ℕ} {b : ℕ} (hb : ∀ p ∈ l, p < 2 ^ b) (i : ℕ) :
    (l.take i).prod < 2 ^ ((l.length + 1) * b + 1) := by
  have h1 : (l.take i).prod ≤ 2 ^ ((l.take i).length * b) :=
    prod_le_two_pow (fun p hp => hb p (List.mem_of_mem_take hp))
  have h2 : (l.take i).length * b ≤ (l.length + 1) * b :=
    Nat.mul_le_mul_right _ (by rw [List.length_take]; omega)
  calc (l.take i).prod ≤ 2 ^ ((l.take i).length * b) := h1
    _ ≤ 2 ^ ((l.length + 1) * b) := Nat.pow_le_pow_right (by norm_num) h2
    _ < 2 ^ ((l.length + 1) * b + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- One entry of `prodLF`: multiply the accumulator (top of `w`) by the entry on
top of `c` (consumed); the product is pushed on `x` by `mulC` and moved back
to `w`.  Scratch `s`, `t`. -/
def prodBody (x w c s t : K) : Frag := (mulC c w x s t).seq (moveEntry x w s)

/-- `Alg.prodL`: list on `x` (restored), `encodeNatΓ' (Alg.prodL l).1` pushed on
`w`; `c` receives a copy of the list (consumed by the loop), `s`, `t` scratch. -/
def prodLF (x w c s t : K) : Frag :=
  (copyList x c s t).seq ((pushNum w 1).seq ((forEntries c (prodBody x w c s t)).seq (popTop c)))

/-- Loop invariant of `prodLF` (stack-only, as `forEntries` requires). -/
def ProdInv (x w c s t : K) (l : List ℕ) (S₀ : Stacks) (i : ℕ) (T : Stacks) : Prop :=
  T w = encodeNatΓ' (l.take i).prod ++ .comma :: S₀ w ∧ T x = S₀ x ∧ T s = S₀ s ∧ T t = S₀ t ∧
  ∀ k, k ≠ x → k ≠ w → k ≠ c → k ≠ s → k ≠ t → T k = S₀ k

theorem prodBody_runs {x w c s t : K} (hxw : x ≠ w) (hxc : x ≠ c) (hxs : x ≠ s) (hxt : x ≠ t)
    (hwc : w ≠ c) (hws : w ≠ s) (hwt : w ≠ t) (hcs : c ≠ s) (hct : c ≠ t) (hst : s ≠ t)
    (l : List ℕ) (b : ℕ) (hb : ∀ p ∈ l, p < 2 ^ b) (S₀ : Stacks)
    (i p : ℕ) (l' : List ℕ) (hdrop : l.drop i = p :: l') (v : St) (T : Stacks)
    (hP : ProdInv x w c s t l S₀ i T)
    (hTc : T c = encodeNatΓ' p ++ .comma :: (encList l' ++ S₀ c)) :
    (prodBody x w c s t).Runs v T (fun _ T' =>
        ProdInv x w c s t l S₀ (i + 1) T' ∧ T' c = encList l' ++ S₀ c)
      (2 * B ((l.length + 1) * b + 1)) := by
  obtain ⟨hTw, hTx, hTs, hTt, hTF⟩ := hP
  set M := (l.length + 1) * b + 1 with hM
  have hp : p < 2 ^ M := by
    calc p < 2 ^ b := hb p (mem_of_drop_eq_cons hdrop)
      _ ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (by rw [hM]; nlinarith)
  have hacc : (l.take i).prod < 2 ^ M := take_prod_lt hb i
  have hval : p * (l.take i).prod = (l.take (i + 1)).prod := by
    rw [take_succ_of_drop_eq_cons hdrop, List.prod_append, List.prod_singleton, mul_comm]
  have hacc' : (l.take (i + 1)).prod < 2 ^ M := take_prod_lt hb (i + 1)
  have hlen : (Computability.encodeNat (l.take (i + 1)).prod).length ≤ M :=
    encodeNat_length_le_of_lt_pow hacc'
  -- stage 1: mulC c w x s t
  have h1 := mulC_le_B hwc.symm hxc.symm hcs hct hxw.symm hws hwt hxs hxt hst p (l.take i).prod M
    hp hacc _ _ v T hTc hTw
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B M) h1
    fun v₁ T₁ ⟨hc₁, hw₁, hx₁, hs₁, ht₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 2: moveEntry x w s
  rw [hval, encodeNatΓ'_eq] at hx₁
  have h2 := moveEntry_runs hxw hxs hws _ _ v₁ T₁ hx₁
  refine Frag.runs_mono h2 (fun _ T₂ ⟨_, _, _, hx₂, hw₂, hs₂, hF₂⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    (le_B_of_le_linear (by omega))
  · rw [hw₂, hw₁, ← encodeNatΓ'_eq]
  · rw [hx₂, hTx]
  · rw [hs₂, hs₁, hTs]
  · rw [hF₂ t hxt.symm hwt.symm hst.symm, ht₁, hTt]
  · intro k hkx hkw hkc hks hkt
    rw [hF₂ k hkx hkw hks, hF₁ k hkc hkw hkx hks hkt, hTF k hkx hkw hkc hks hkt]
  · rw [hF₂ c hxc.symm hwc.symm hcs, hc₁]

theorem prodLF_le_B {x w c s t : K} (hxw : x ≠ w) (hxc : x ≠ c) (hxs : x ≠ s) (hxt : x ≠ t)
    (hwc : w ≠ c) (hws : w ≠ s) (hwt : w ≠ t) (hcs : c ≠ s) (hct : c ≠ t) (hst : s ≠ t)
    (l : List ℕ) (b : ℕ) (hb : ∀ p ∈ l, p < 2 ^ b) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encList l ++ xr) :
    (prodLF x w c s t).Runs v S (fun _ S' =>
        S' x = S x ∧ S' w = encodeNatΓ' (Alg.prodL l).1 ++ .comma :: S w ∧
        S' c = S c ∧ S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ w → k ≠ c → k ≠ s → k ≠ t → S' k = S k)
      (((Alg.prodL l).2 + 1) * B (2 * (l.length + 1) * b + 4)) := by
  set M := (l.length + 1) * b + 1 with hM
  have hBM : B (2 * (l.length + 1) * b + 4) = 8 * B M := by
    rw [show 2 * (l.length + 1) * b + 4 = (1 + 1) * M + 2 * 1 by rw [hM]; ring, ← B_scale]
    norm_num
  have hBb : B b ≤ B M := B_mono (by rw [hM]; nlinarith)
  have hB8 : 8 ≤ B M := le_B_of_le_linear (by omega)
  rw [prodL_snd, hBM]
  -- stage 1: copyList x c s t
  have h1 := copyList_le_B hxc hxs hxt hcs hct hst l b hb xr v S hS
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length * (2 * B M + 2) + 5) h1
    fun v₁ S₁ ⟨hx₁, hc₁, hs₁, ht₁, hF₁⟩ => ?_) (fun _ _ h => h) (by nlinarith)
  -- stage 2: pushNum w 1
  refine Frag.runs_mono (Frag.seq_runs (t₂ := l.length * (2 * B M + 2) + 3) (pushNum_runs w 1 v₁ S₁)
    fun v₂ S₂ ⟨hv₂, hw₂, hF₂⟩ => ?_) (fun _ _ h => h) (by simp only [Nat.log_one_right]; omega)
  -- stage 3: the loop
  have hw₁ : S₁ w = S w := hF₁ w hxw.symm hwc hws hwt
  have hloop := forEntriesN_runs (x := c) (body := prodBody x w c s t) l (S c)
    (ProdInv x w c s t l S) (2 * B M) v₂ S₂ (by rw [hF₂ c hwc.symm, hc₁])
    ⟨by rw [hw₂, hw₁]; simp, by rw [hF₂ x hxw, hx₁], by rw [hF₂ s hws.symm, hs₁],
      by rw [hF₂ t hwt.symm, ht₁],
      fun k hkx hkw hkc hks hkt => by rw [hF₂ k hkw, hF₁ k hkx hkc hks hkt]⟩
    (fun i p l' hdrop w' T hP hT =>
      prodBody_runs hxw hxc hxs hxt hwc hws hwt hcs hct hst l b hb S i p l' hdrop w' T hP hT)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) hloop
    fun v₃ S₃ ⟨_, ⟨hw₃, hx₃, hs₃, ht₃, hF₃⟩, hc₃⟩ => ?_) (fun _ _ h => h) le_rfl
  -- stage 4: popTop c
  refine Frag.runs_mono (popTop_runs c v₃ S₃) (fun _ S₄ ⟨_, hS₄⟩ => ?_) le_rfl
  subst hS₄
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne hxc, hx₃]
  · rw [Function.update_of_ne hwc, hw₃, List.take_length, prodL_fst]
  · rw [Function.update_self, hc₃]; rfl
  · rw [Function.update_of_ne hcs.symm, hs₃]
  · rw [Function.update_of_ne hct.symm, ht₃]
  · intro k hkx hkw hkc hks hkt; rw [Function.update_of_ne hkc, hF₃ k hkx hkw hkc hks hkt]

/-! ### `Alg.coprimeTo`: no element of `Q` divides `k` (early exit) -/

/-- One test of `coprimeToF`: copy the entry `q` (top of `x`) to `t` and `k`
(top of `y`) to `u`; `u := k % q` (`modC`, scratch `x y z s`); `flag := (k % q = 0)`;
record it in `cmp` (`.eq` = divisor found, `.lt` = not); drop the remainder;
move the entry from `x` to `z`; `flag := flag ∨ (x exhausted)`. -/
def cpBody (x y z s t u : K) : Frag :=
  (dup x t s).seq ((dup y u s).seq ((modC u t x y z s).seq ((isZero u s).seq
    ((Frag.load' (fun v => { v with cmp := if v.flag then Ordering.eq else Ordering.lt })).seq
      ((dropNum u).seq ((moveEntry x z s).seq (peekBraOr x)))))))

/-- `Alg.coprimeTo`: list on `x` and `k` on `y` (both restored),
`flag := (Alg.coprimeTo Q k).1`.  `z` receives the processed entries (moved
back at the end), `t` the entry copies and the final result bit, `u` the
`k` copies, `s` scratch. -/
def coprimeToF (x y z s t u : K) : Frag :=
  (Frag.pushSym z .bra).seq ((Frag.load' (fun v => { v with cmp := Ordering.lt })).seq
    ((peekBra x).seq ((Frag.loop (fun v => !v.flag) (cpBody x y z s t u)).seq
      ((Frag.pushSym t .comma).seq ((pushBit t (fun v => decide (v.cmp ≠ Ordering.lt))).seq
        ((moveEntries z x s).seq ((isZero t s).seq (dropNum t))))))))

/-- Loop invariant of `coprimeToF` after `i` tests: no divisor among the first
`i` entries unless `i` is the last iteration; `flag` = "found ∨ exhausted";
`cmp` = `.lt` iff no divisor so far. -/
def CpInv (x y z s t u : K) (Q : List ℕ) (k : ℕ) (xr : List Γ') (S₀ : Stacks)
    (i : ℕ) (v : St) (S : Stacks) : Prop :=
  i ≤ cpIter Q k ∧
  v.flag = (!decide (∀ q ∈ Q.take i, k % q ≠ 0) || decide (Q.length ≤ i)) ∧
  v.cmp = (if ∀ q ∈ Q.take i, k % q ≠ 0 then Ordering.lt else Ordering.eq) ∧
  S x = encList (Q.drop i) ++ xr ∧
  S z = entries ((Q.take i).map Computability.encodeNat).reverse ++ .bra :: S₀ z ∧
  S y = S₀ y ∧ S s = S₀ s ∧ S t = S₀ t ∧ S u = S₀ u ∧
  ∀ j, j ≠ x → j ≠ y → j ≠ z → j ≠ s → j ≠ t → j ≠ u → S j = S₀ j

theorem entries_take_append_drop (l : List ℕ) (n : ℕ) (r : List Γ') :
    entries ((l.take n).map Computability.encodeNat) ++ (encList (l.drop n) ++ r) =
      encList l ++ r := by
  rw [encList_eq, encList_eq, encListB, encListB, ← List.append_assoc, ← List.append_assoc,
    ← entries_append, ← List.map_append, List.take_append_drop]

theorem cpBody_runs {x y z s t u : K} (hxy : x ≠ y) (hxz : x ≠ z) (hxs : x ≠ s) (hxt : x ≠ t)
    (hxu : x ≠ u) (hyz : y ≠ z) (hys : y ≠ s) (hyt : y ≠ t) (hyu : y ≠ u) (hzs : z ≠ s)
    (hzt : z ≠ t) (hzu : z ≠ u) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (Q : List ℕ) (k b : ℕ) (hb : ∀ q ∈ Q, q < 2 ^ b) (hQ1 : ∀ q ∈ Q, 1 ≤ q) (hk : k < 2 ^ b)
    (xr yr : List Γ') (S₀ : Stacks) (hS₀y : S₀ y = encodeNatΓ' k ++ .comma :: yr)
    (i : ℕ) (hi : i < cpIter Q k) (v : St) (S : Stacks)
    (hI : CpInv x y z s t u Q k xr S₀ i v S) :
    (cpBody x y z s t u).Runs v S (CpInv x y z s t u Q k xr S₀ (i + 1))
      (5 * B b + 2 * b + 6) := by
  obtain ⟨-, -, -, hSx, hSz, hSy, hSs, hSt, hSu, hF⟩ := hI
  obtain ⟨hiQ, hclean⟩ := (lt_cpIter_iff Q k i).1 hi
  have hdrop := List.drop_eq_getElem_cons hiQ
  have hqQ : Q[i] ∈ Q := List.getElem_mem hiQ
  have hq := hb _ hqQ
  have hq1 := hQ1 _ hqQ
  have hkq : k % Q[i] < 2 ^ b := lt_of_le_of_lt (Nat.mod_le _ _) hk
  have hSx' : S x = encodeNatΓ' Q[i] ++ .comma :: (encList (Q.drop (i + 1)) ++ xr) := by
    rw [hSx, hdrop, encList_cons]; simp
  have hcl' : (∀ q ∈ Q.take (i + 1), k % q ≠ 0) ↔ k % Q[i] ≠ 0 := by
    rw [take_succ_of_drop_eq_cons hdrop]
    simp only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
    exact ⟨fun h => h.2, fun h => ⟨hclean, h⟩⟩
  have hlenQ : Q.length = i + 1 + (Q.drop (i + 1)).length := by rw [List.length_drop]; omega
  -- stage 1: dup x t s
  have h1 := dup_le_B hxt hxs hst.symm Q[i] b hq _ v S hSx'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * B b + 2 * b + 6) h1
    fun v₁ S₁ ⟨hx₁, ht₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 2: dup y u s
  have hy₁ : S₁ y = encodeNatΓ' k ++ .comma :: yr := by rw [hF₁ y hxy.symm hyt hys, hSy, hS₀y]
  have h2 := dup_le_B hyu hys hsu.symm k b hk yr v₁ S₁ hy₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * B b + 2 * b + 6) h2
    fun v₂ S₂ ⟨hy₂, hu₂, hs₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: modC u t x y z s
  have ht₂ : S₂ t = encodeNatΓ' Q[i] ++ .comma :: S t := by rw [hF₂ t hyt.symm htu hst.symm, ht₁]
  have h3 := modC_le_B htu.symm hxu.symm hyu.symm hzu.symm hsu.symm hxt.symm hyt.symm hzt.symm
    hst.symm hxy hxz hxs hyz hys hzs k Q[i] b hq1 hk hq _ _ v₂ S₂ hu₂ ht₂
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B b + 2 * b + 6) h3
    fun v₃ S₃ ⟨hu₃, ht₃, hx₃, hy₃, hz₃, hs₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 4: isZero u s
  have h4 := isZero_le_B hsu.symm (k % Q[i]) b hkq _ v₃ S₃ hu₃
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + 2 * b + 6) h4
    fun v₄ S₄ ⟨hfl₄, hcmp₄, hu₄, hs₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 5: record the flag in cmp
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + 2 * b + 5)
    (Frag.load'_runs (fun v => { v with cmp := if v.flag then Ordering.eq else Ordering.lt }) v₄ S₄)
    fun v₅ S₅ ⟨hv₅, hS₅⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hS₅]
  -- stage 6: dropNum u
  have hu₄' : S₄ u = encodeNatΓ' (k % Q[i]) ++ .comma :: S₁ u := by rw [hu₄, hu₃]
  have h6 := dropNum_le_B (k % Q[i]) b hkq _ v₅ S₄ hu₄'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * b + 5) h6
    fun v₆ S₆ ⟨hfl₆, hcmp₆, _, hu₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 7: moveEntry x z s
  have hx₆ : S₆ x = bits (Computability.encodeNat Q[i]) ++ .comma :: (encList (Q.drop (i + 1)) ++ xr) := by
    rw [hF₆ x hxu, hF₄ x hxu hxs, hx₃, hF₂ x hxy hxu hxs, hx₁, hSx', encodeNatΓ'_eq]
  have h7 := moveEntry_runs hxz hxs hzs _ _ v₆ S₆ hx₆
  have hlen : (Computability.encodeNat Q[i]).length ≤ b := encodeNat_length_le_of_lt_pow hq
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) h7
    fun v₇ S₇ ⟨hfl₇, hcmp₇, _, hx₇, hz₇, hs₇, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 8: peekBraOr x
  refine Frag.runs_mono (peekBraOr_runs x v₇ S₇) (fun v₈ S₈ ⟨hv₈, hS₈⟩ => ?_) le_rfl
  rw [hv₈, hS₈]
  have hflag : decide ((S₇ x).head? = some Γ'.bra) = decide (Q.length ≤ i + 1) := by
    rw [hx₇, encList_eq, List.map_drop, flag_encListB_drop, List.length_map]
  have hz₆ : S₆ z = entries ((Q.take i).map Computability.encodeNat).reverse ++ .bra :: S₀ z := by
    rw [hF₆ z hzu, hF₄ z hzu hzs, hz₃, hF₂ z hyz.symm hzu hzs, hF₁ z hxz.symm hzt hzs, hSz]
  refine ⟨hi, ?_, ?_, hx₇, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfl₇, hfl₆, hv₅]
    simp only [hfl₄, hflag]
    by_cases h : k % Q[i] = 0 <;> simp [h, hcl']
  · rw [hcmp₇, hcmp₆, hv₅]
    simp only [hfl₄]
    by_cases h : k % Q[i] = 0 <;> simp [h, hcl']
  · rw [hz₇, hz₆, take_succ_of_drop_eq_cons hdrop, List.map_append, List.reverse_append]
    simp
  · rw [hF₇ y hxy.symm hyz hys, hF₆ y hyu, hF₄ y hyu hys, hy₃, hy₂, hF₁ y hxy.symm hyt hys, hSy]
  · rw [hs₇, hF₆ s hsu, hs₄, hs₃, hs₂, hs₁, hSs]
  · rw [hF₇ t hxt.symm hzt.symm hst.symm, hF₆ t htu, hF₄ t htu hst.symm, ht₃, hSt]
  · rw [hF₇ u hxu.symm hzu.symm hsu.symm, hu₆, hF₁ u hxu.symm htu.symm hsu.symm, hSu]
  · intro j hjx hjy hjz hjs hjt hju
    rw [hF₇ j hjx hjz hjs, hF₆ j hju, hF₄ j hju hjs, hF₃ j hju hjt hjx hjy hjz hjs,
      hF₂ j hjy hju hjs, hF₁ j hjx hjt hjs, hF j hjx hjy hjz hjs hjt hju]

theorem coprimeToF_le_B {x y z s t u : K} (hxy : x ≠ y) (hxz : x ≠ z) (hxs : x ≠ s) (hxt : x ≠ t)
    (hxu : x ≠ u) (hyz : y ≠ z) (hys : y ≠ s) (hyt : y ≠ t) (hyu : y ≠ u) (hzs : z ≠ s)
    (hzt : z ≠ t) (hzu : z ≠ u) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (Q : List ℕ) (k b : ℕ) (hb : ∀ q ∈ Q, q < 2 ^ b) (hQ1 : ∀ q ∈ Q, 1 ≤ q) (hk : k < 2 ^ b)
    (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encList Q ++ xr) (hSy : S y = encodeNatΓ' k ++ .comma :: yr) :
    (coprimeToF x y z s t u).Runs v S (fun v' S' =>
        v'.flag = (Alg.coprimeTo Q k).1 ∧
        S' x = S x ∧ S' y = S y ∧ S' z = S z ∧ S' s = S s ∧ S' t = S t ∧ S' u = S u ∧
        ∀ j, j ≠ x → j ≠ y → j ≠ z → j ≠ s → j ≠ t → j ≠ u → S' j = S j)
      (((Alg.coprimeTo Q k).2 + 1) * B (2 * b + 2)) := by
  set n := cpIter Q k with hn
  set tb := 5 * B b + 2 * b + 6 with htb
  set E := n * (tb + 1) + 1 + n * (2 * b + 6) + 15 with hE
  have hnQ : n ≤ Q.length := cpIter_le_length Q k
  have hB8 : B (2 * b + 2) = 8 * B b := by
    rw [show 2 * b + 2 = (1 + 1) * b + 2 * 1 by ring, ← B_scale]; norm_num
  have hBlin : 4 * b + 13 ≤ B b := le_B_of_le_linear (by omega)
  have hB18 : 18 ≤ B b := le_B_of_le_linear (by omega)
  rw [coprimeTo_snd, ← hn, hB8]
  -- stage 1: pushSym z bra
  refine Frag.runs_mono (Frag.seq_runs (t₂ := E + 2) (Frag.pushSym_runs z .bra v S)
    fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by rw [hE, htb]; nlinarith)
  rw [hv₁]; subst hS₁
  -- stage 2: cmp := lt
  refine Frag.runs_mono (Frag.seq_runs (t₂ := E + 1)
    (Frag.load'_runs (fun v => { v with cmp := Ordering.lt }) v _)
    fun v₂ S₂ ⟨hv₂, hS₂⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₂, hS₂]
  -- stage 3: peekBra x
  refine Frag.runs_mono (Frag.seq_runs (t₂ := E) (peekBra_runs x _ _)
    fun v₃ S₃ ⟨hv₃, hS₃⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₃, hS₃]
  -- stage 4: the loop
  have hfl0 := flag_encListB_drop (Q.map Computability.encodeNat) 0 xr
  rw [List.drop_zero, List.length_map, ← encList_eq] at hfl0
  have hloop := Frag.loop_runs (c := fun v => !v.flag) (B := cpBody x y z s t u)
    (CpInv x y z s t u Q k xr S) n tb
    (v := { v with cmp := Ordering.lt, flag := decide ((Function.update S z (Γ'.bra :: S z) x).head? = some Γ'.bra) })
    (S := Function.update S z (Γ'.bra :: S z))
    ⟨Nat.zero_le _,
      by
        show decide ((Function.update S z (Γ'.bra :: S z) x).head? = some Γ'.bra) = _
        rw [Function.update_of_ne hxz, hSx, hfl0]; simp,
      by simp,
      by simp [Function.update_of_ne hxz, hSx], by simp,
      by simp [Function.update_of_ne hyz], by simp [Function.update_of_ne hzs.symm],
      by simp [Function.update_of_ne hzt.symm], by simp [Function.update_of_ne hzu.symm],
      fun j _ _ hjz _ _ _ => by simp [Function.update_of_ne hjz]⟩
    (fun i hi w T ⟨_, hfl, _⟩ => by
      obtain ⟨h1, h2⟩ := (lt_cpIter_iff Q k i).1 hi
      simp [hfl, decide_eq_true h2, Nat.not_le.2 h1])
    (fun w T ⟨_, hfl, _⟩ => by
      by_cases hcl : ∀ q ∈ Q.take n, k % q ≠ 0
      · have : ¬ n < Q.length := fun h => lt_irrefl _ ((lt_cpIter_iff Q k n).2 ⟨h, hcl⟩)
        simp [hfl, decide_eq_true hcl, Nat.not_lt.1 this]
      · simp [hfl, decide_eq_false hcl])
    (fun i hi w T hI => cpBody_runs hxy hxz hxs hxt hxu hyz hys hyt hyu hzs hzt hzu hst hsu htu
      Q k b hb hQ1 hk xr yr S hSy i hi w T hI)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := n * (2 * b + 6) + 14) hloop
    fun v₄ S₄ ⟨⟨_, _, hcmp₄, hx₄, hz₄, hy₄, hs₄, ht₄, hu₄, hF₄⟩, _⟩ => ?_) (fun _ _ h => h)
    (by rw [hE]; omega)
  -- stage 5: pushSym t comma
  refine Frag.runs_mono (Frag.seq_runs (t₂ := n * (2 * b + 6) + 13) (Frag.pushSym_runs t .comma v₄ S₄)
    fun v₅ S₅ ⟨hv₅, hS₅⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₅]; subst hS₅
  -- stage 6: pushBit t (cmp ≠ lt)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := n * (2 * b + 6) + 12)
    (pushBit_runs t (fun v => decide (v.cmp ≠ Ordering.lt)) v₄ _)
    fun v₆ S₆ ⟨hv₆, hS₆⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₆]; subst hS₆
  -- stage 7: moveEntries z x s
  have hz₆ : Function.update (Function.update S₄ t (Γ'.comma :: S₄ t)) t
      (Γ'.bit (decide (v₄.cmp ≠ Ordering.lt)) :: Function.update S₄ t (Γ'.comma :: S₄ t) t) z =
      encListB ((Q.take n).map Computability.encodeNat).reverse ++ S z := by
    rw [Function.update_of_ne hzt, Function.update_of_ne hzt, hz₄, encListB_eq_entries_append]
  have hm : ∀ l ∈ ((Q.take n).map Computability.encodeNat).reverse, l.length ≤ b := by
    intro l hl
    rw [List.mem_reverse] at hl
    exact entry_length_le_of_lt_pow (fun a ha => hb a (List.mem_of_mem_take ha)) l hl
  have h7 := moveEntries_runs hxz.symm hzs hxs _ b hm (S z) v₄ _ hz₆
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 9) h7
    fun v₇ S₇ ⟨hz₇, hx₇, hs₇, hF₇⟩ => ?_) (fun _ _ h => h)
    (by simp only [List.length_reverse, List.length_map, List.length_take, min_eq_left hnQ]; omega)
  -- stage 8: isZero t s
  have ht₇ : S₇ t = bits [decide (v₄.cmp ≠ Ordering.lt)] ++ .comma :: S t := by
    rw [hF₇ t hzt.symm hxt.symm hst.symm, Function.update_self, Function.update_self, ht₄]; rfl
  have h8 := isZero_runs hst.symm _ _ v₇ S₇ ht₇
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2) h8
    fun v₈ S₈ ⟨hfl₈, _, ht₈, hs₈, hF₈⟩ => ?_) (fun _ _ h => h) (by simp)
  -- stage 9: dropNum t
  have ht₈' : S₈ t = bits [decide (v₄.cmp ≠ Ordering.lt)] ++ .comma :: S t := by rw [ht₈, ht₇]
  have h9 := dropNum_runs _ _ v₈ S₈ ht₈'
  refine Frag.runs_mono h9 (fun v₉ S₉ ⟨hfl₉, _, _, ht₉, hF₉⟩ => ⟨?_, ?_, ?_, ?_, ?_, ht₉, ?_, ?_⟩)
    (by simp)
  · rw [hfl₉, hfl₈, coprimeTo_fst, ← hn, hcmp₄]
    by_cases hcl : ∀ q ∈ Q.take n, k % q ≠ 0 <;> simp [hcl, toNat]
  · rw [hF₉ x hxt, hF₈ x hxt hxs, hx₇, Function.update_of_ne hxt,
      Function.update_of_ne hxt, hx₄, List.reverse_reverse, entries_take_append_drop, hSx]
  · rw [hF₉ y hyt, hF₈ y hyt hys, hF₇ y hyz hxy.symm hys,
      Function.update_of_ne hyt, Function.update_of_ne hyt, hy₄]
  · rw [hF₉ z hzt, hF₈ z hzt hzs, hz₇]
  · rw [hF₉ s hst, hs₈, hs₇, Function.update_of_ne hst, Function.update_of_ne hst, hs₄]
  · rw [hF₉ u htu.symm, hF₈ u htu.symm hsu.symm, hF₇ u hzu.symm hxu.symm hsu.symm,
      Function.update_of_ne htu.symm, Function.update_of_ne htu.symm, hu₄]
  · intro j hjx hjy hjz hjs hjt hju
    rw [hF₉ j hjt, hF₈ j hjt hjs, hF₇ j hjz hjx hjs, Function.update_of_ne hjt,
      Function.update_of_ne hjt, hF₄ j hjx hjy hjz hjs hjt hju]

/-! ### `Alg.mulAll`: `ds.map (· * q)` -/

theorem mulAll_mem_lt {q : ℕ} {ds : List ℕ} {b : ℕ} (hq : q < 2 ^ b) (hb : ∀ d ∈ ds, d < 2 ^ b) :
    ∀ e ∈ (Alg.mulAll q ds).1, e < 2 ^ (2 * b) := by
  intro e he
  rw [mulAll_fst, List.mem_map] at he
  obtain ⟨d, hd, rfl⟩ := he
  rw [two_mul, pow_add]
  exact Nat.mul_lt_mul'' (hb d hd) hq

/-- One entry of `mulAllF`: copy `q` (top of `y`) to `t`, then `mulC x t r s y`
consumes the entry `d` on `x` and the copy, pushing `encodeNatΓ' (d * q)` on
the open list `r` (`y` doubles as `mul`'s second scratch stack; restored). -/
def mulAllBody (x y r s t : K) : Frag := (dup y t s).seq (mulC x t r s y)

/-- `Alg.mulAll`: list `ds` on `x` (consumed), `q` on `y` (restored);
`x := encList (Alg.mulAll q ds).1 ++ xr` (same order as `ds`).  The products
are collected on the open list `r` (reversed) and moved back onto `x` by
`revList`; `r`, `s`, `t` restored. -/
def mulAllF (x y r s t : K) : Frag :=
  (Frag.pushSym r .bra).seq ((forEntries x (mulAllBody x y r s t)).seq
    ((popTop x).seq (revList r x s)))

/-- Loop invariant of `mulAllF` (stack-only). -/
def MulAllInv (x y r s t : K) (q : ℕ) (ds : List ℕ) (S₀ : Stacks) (i : ℕ) (T : Stacks) : Prop :=
  T r = encList ((ds.take i).map (· * q)).reverse ++ S₀ r ∧
  T y = S₀ y ∧ T s = S₀ s ∧ T t = S₀ t ∧
  ∀ k, k ≠ x → k ≠ y → k ≠ r → k ≠ s → k ≠ t → T k = S₀ k

theorem mulAllBody_runs {x y r s t : K} (hxy : x ≠ y) (hxr : x ≠ r) (hxs : x ≠ s) (hxt : x ≠ t)
    (hyr : y ≠ r) (hys : y ≠ s) (hyt : y ≠ t) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (q : ℕ) (ds : List ℕ) (b : ℕ) (hq : q < 2 ^ b) (hb : ∀ d ∈ ds, d < 2 ^ b)
    (xr yr : List Γ') (S₀ : Stacks) (hS₀y : S₀ y = encodeNatΓ' q ++ .comma :: yr)
    (i d : ℕ) (ds' : List ℕ) (hdrop : ds.drop i = d :: ds') (v : St) (T : Stacks)
    (hP : MulAllInv x y r s t q ds S₀ i T)
    (hTx : T x = encodeNatΓ' d ++ .comma :: (encList ds' ++ xr)) :
    (mulAllBody x y r s t).Runs v T (fun _ T' =>
        MulAllInv x y r s t q ds S₀ (i + 1) T' ∧ T' x = encList ds' ++ xr)
      (2 * B b) := by
  obtain ⟨hTr, hTy, hTs, hTt, hTF⟩ := hP
  have hd : d < 2 ^ b := hb d (mem_of_drop_eq_cons hdrop)
  -- stage 1: dup y t s
  have h1 := dup_le_B hyt hys hst.symm q b hq yr v T (by rw [hTy, hS₀y])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b) h1
    fun v₁ T₁ ⟨hy₁, ht₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 2: mulC x t r s y
  have hx₁ : T₁ x = encodeNatΓ' d ++ .comma :: (encList ds' ++ xr) := by
    rw [hF₁ x hxy hxt hxs, hTx]
  have h2 := mulC_le_B hxt hxr hxs hxy hrt.symm hst.symm hyt.symm hrs hyr.symm hys.symm d q b hd hq
    _ _ v₁ T₁ hx₁ ht₁
  refine Frag.runs_mono h2 (fun _ T₂ ⟨hx₂, ht₂, hr₂, hs₂, hy₂, hF₂⟩ =>
    ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hx₂⟩) le_rfl
  · rw [hr₂, hF₁ r hyr.symm hrt hrs, hTr, take_succ_of_drop_eq_cons hdrop, List.map_append,
      List.reverse_append]
    simp [encList_cons]
  · rw [hy₂, hy₁, hTy]
  · rw [hs₂, hs₁, hTs]
  · rw [ht₂, hTt]
  · intro k hkx hky hkr hks hkt
    rw [hF₂ k hkx hkt hkr hks hky, hF₁ k hky hkt hks, hTF k hkx hky hkr hks hkt]

theorem mulAllF_le_B {x y r s t : K} (hxy : x ≠ y) (hxr : x ≠ r) (hxs : x ≠ s) (hxt : x ≠ t)
    (hyr : y ≠ r) (hys : y ≠ s) (hyt : y ≠ t) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (q : ℕ) (ds : List ℕ) (b : ℕ) (hq : q < 2 ^ b) (hb : ∀ d ∈ ds, d < 2 ^ b)
    (xr yr : List Γ') (v : St) (S : Stacks)
    (hSx : S x = encList ds ++ xr) (hSy : S y = encodeNatΓ' q ++ .comma :: yr) :
    (mulAllF x y r s t).Runs v S (fun _ S' =>
        S' x = encList (Alg.mulAll q ds).1 ++ xr ∧ S' y = S y ∧ S' r = S r ∧ S' s = S s ∧
        S' t = S t ∧ ∀ k, k ≠ x → k ≠ y → k ≠ r → k ≠ s → k ≠ t → S' k = S k)
      (((Alg.mulAll q ds).2 + 1) * B (4 * b + 2)) := by
  have hB8 : B (4 * b + 2) = 8 * B (2 * b) := by
    rw [show 4 * b + 2 = (1 + 1) * (2 * b) + 2 * 1 by ring, ← B_scale]; norm_num
  have hBb : B b ≤ B (2 * b) := B_mono (by omega)
  have hB8' : 8 ≤ B (2 * b) := le_B_of_le_linear (by omega)
  rw [mulAll_snd, hB8]
  -- stage 1: pushSym r bra
  refine Frag.runs_mono (Frag.seq_runs (t₂ := ds.length * (2 * B b + 2) + 4 + (ds.length + 1) * B (2 * b))
    (Frag.pushSym_runs r .bra v S) fun v₁ S₁ ⟨hv₁, hS₁⟩ => ?_) (fun _ _ h => h) (by nlinarith)
  rw [hv₁]; subst hS₁
  -- stage 2: the loop
  have hloop := forEntriesN_runs (x := x) (body := mulAllBody x y r s t) ds xr
    (MulAllInv x y r s t q ds S) (2 * B b) v (Function.update S r (Γ'.bra :: S r))
    (by rw [Function.update_of_ne hxr, hSx])
    ⟨by simp, by simp [Function.update_of_ne hyr], by simp [Function.update_of_ne hrs.symm],
      by simp [Function.update_of_ne hrt.symm], fun k _ _ hkr _ _ => by simp [Function.update_of_ne hkr]⟩
    (fun i d ds' hdrop w T hP hT =>
      mulAllBody_runs hxy hxr hxs hxt hyr hys hyt hrs hrt hst q ds b hq hb xr yr S hSy i d ds' hdrop
        w T hP hT)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 + (ds.length + 1) * B (2 * b)) hloop
    fun v₂ S₂ ⟨_, ⟨hr₂, hy₂, hs₂, ht₂, hF₂⟩, hx₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: popTop x
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1 + (ds.length + 1) * B (2 * b)) (popTop_runs x v₂ S₂)
    fun v₃ S₃ ⟨hv₃, hS₃⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₃]; subst hS₃
  -- stage 4: revList r x s
  have hprod : ∀ e ∈ ((ds.take ds.length).map (· * q)).reverse, e < 2 ^ (2 * b) := by
    intro e he
    rw [List.take_length, List.mem_reverse, ← mulAll_fst] at he
    exact mulAll_mem_lt hq hb e he
  have hr₃ : Function.update S₂ x (S₂ x).tail r =
      encList ((ds.take ds.length).map (· * q)).reverse ++ S r := by
    rw [Function.update_of_ne hxr.symm, hr₂]
  have h4 := revList_le_B hxr.symm hrs hxs _ (2 * b) hprod (S r) v₂ _ hr₃
  refine Frag.runs_mono h4 (fun _ S₄ ⟨hr₄, hx₄, hs₄, hF₄⟩ => ⟨?_, ?_, hr₄, ?_, ?_, ?_⟩)
    (by simp only [List.length_reverse, List.length_map, List.take_length]; omega)
  · rw [hx₄, Function.update_self, hx₂, List.reverse_reverse, List.take_length, mulAll_fst]; rfl
  · rw [hF₄ y hyr hxy.symm hys, Function.update_of_ne hxy.symm, hy₂]
  · rw [hs₄, Function.update_of_ne hxs.symm, hs₂]
  · rw [hF₄ t hrt.symm hxt.symm hst.symm, Function.update_of_ne hxt.symm, ht₂]
  · intro k hkx hky hkr hks hkt
    rw [hF₄ k hkr hkx hks, Function.update_of_ne hkx, hF₂ k hkx hky hkr hks hkt]

/-! ### `Alg.divisorsOf`: all subset products -/

theorem divisorsOf_rev_take_length (Q : List ℕ) (i : ℕ) (hi : i ≤ Q.length) :
    (Alg.divisorsOf ((Q.reverse.take i).reverse)).1.length = 2 ^ i := by
  rw [divisorsOf_length, List.length_reverse, List.length_take, List.length_reverse, min_eq_left hi]

theorem divisorsOf_rev_take_mem_lt {Q : List ℕ} {b : ℕ} (hb : ∀ q ∈ Q, q < 2 ^ b) (i : ℕ) :
    ∀ d ∈ (Alg.divisorsOf ((Q.reverse.take i).reverse)).1, d < 2 ^ (Q.length * b + 1) := by
  intro d hd
  have hb' : ∀ q ∈ (Q.reverse.take i).reverse, q < 2 ^ b := fun q hq =>
    hb q (List.mem_reverse.1 (List.mem_of_mem_take (List.mem_reverse.1 hq)))
  have h1 := divisorsOf_mem_le hb' d hd
  have h2 : ((Q.reverse.take i).reverse).length * b ≤ Q.length * b :=
    Nat.mul_le_mul_right _ (by simp only [List.length_reverse, List.length_take]; omega)
  calc d ≤ _ := h1
    _ ≤ 2 ^ (Q.length * b) := Nat.pow_le_pow_right (by norm_num) h2
    _ < 2 ^ (Q.length * b + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- The fold step: the reversed accumulator after one more element `q` of
`Q.reverse` is `acc.map (· * q) ++ acc` (for the reversed `acc`). -/
theorem divisorsOf_rev_take_succ (Q : List ℕ) (i q : ℕ) (R : List ℕ)
    (hdrop : Q.reverse.drop i = q :: R) :
    (Alg.divisorsOf ((Q.reverse.take (i + 1)).reverse)).1.reverse =
      (Alg.mulAll q (Alg.divisorsOf ((Q.reverse.take i).reverse)).1.reverse).1 ++
        (Alg.divisorsOf ((Q.reverse.take i).reverse)).1.reverse := by
  rw [take_succ_of_drop_eq_cons hdrop, List.reverse_append, List.reverse_singleton,
    List.singleton_append, divisorsOf_cons, List.reverse_append, mulAll_fst, List.map_reverse]

/-- One element `q` (top of `z`) of `divisorsOfF`: with the reversed
accumulator `acc` on `a`, copy it to `c`, `c := acc.map (· * q)` (`mulAllF`,
open list on `x`), `a := c ++ a` (`appendList`), drop `q`.  Scratch `s`, `t`. -/
def divBody (x z a c s t : K) : Frag :=
  (copyList a c s t).seq ((mulAllF c z x s t).seq ((appendList c a t s).seq (dropNum z)))

/-- `Alg.divisorsOf`: list `Q` on `x` (consumed);
`x := encList (Alg.divisorsOf Q).1 ++ xr`.  `Q` is reversed onto `z` and folded
head-first; the accumulator lives reversed on `a`; `c`, `s`, `t` scratch.
All of `z`, `a`, `c`, `s`, `t` are restored. -/
def divisorsOfF (x z a c s t : K) : Frag :=
  (revList x z s).seq ((Frag.pushSym a .bra).seq ((pushNum a 1).seq
    ((forEntries z (divBody x z a c s t)).seq ((popTop z).seq (revList a x s)))))

/-- Loop invariant of `divisorsOfF` (stack-only): after `i` elements of
`Q.reverse`, `a` holds `(Alg.divisorsOf ((Q.reverse.take i).reverse)).1` reversed. -/
def DivInv (x z a c s t : K) (Q : List ℕ) (xr : List Γ') (S₀ : Stacks) (i : ℕ) (T : Stacks) :
    Prop :=
  T a = encList (Alg.divisorsOf ((Q.reverse.take i).reverse)).1.reverse ++ S₀ a ∧
  T x = xr ∧ T c = S₀ c ∧ T s = S₀ s ∧ T t = S₀ t ∧
  ∀ k, k ≠ x → k ≠ z → k ≠ a → k ≠ c → k ≠ s → k ≠ t → T k = S₀ k

theorem divBody_runs {x z a c s t : K} (hxz : x ≠ z) (hxa : x ≠ a) (hxc : x ≠ c) (hxs : x ≠ s)
    (hxt : x ≠ t) (hza : z ≠ a) (hzc : z ≠ c) (hzs : z ≠ s) (hzt : z ≠ t) (hac : a ≠ c)
    (has : a ≠ s) (hat : a ≠ t) (hcs : c ≠ s) (hct : c ≠ t) (hst : s ≠ t)
    (Q : List ℕ) (b : ℕ) (hb : ∀ q ∈ Q, q < 2 ^ b) (xr : List Γ') (S₀ : Stacks)
    (i q : ℕ) (R : List ℕ) (hdrop : Q.reverse.drop i = q :: R) (v : St) (T : Stacks)
    (hP : DivInv x z a c s t Q xr S₀ i T)
    (hTz : T z = encodeNatΓ' q ++ .comma :: (encList R ++ S₀ z)) :
    (divBody x z a c s t).Runs v T (fun _ T' =>
        DivInv x z a c s t Q xr S₀ (i + 1) T' ∧ T' z = encList R ++ S₀ z)
      ((2 ^ i + 1) * (4 * B (4 * (Q.length * b + 1) + 2))) := by
  obtain ⟨hTa, hTx, hTc, hTs, hTt, hTF⟩ := hP
  set M := Q.length * b + 1 with hM
  set M' := 4 * M + 2 with hM'
  have hin : i < Q.length := by
    by_contra h
    have h' : Q.reverse.length ≤ i := by rw [List.length_reverse]; omega
    rw [List.drop_eq_nil_of_le h'] at hdrop
    cases hdrop
  have hqQ : q ∈ Q := List.mem_reverse.1 (mem_of_drop_eq_cons hdrop)
  have hqb : q < 2 ^ b := hb q hqQ
  have hbM : b ≤ M := by rw [hM]; nlinarith
  have hq : q < 2 ^ M := lt_of_lt_of_le hqb (Nat.pow_le_pow_right (by norm_num) hbM)
  set acc := (Alg.divisorsOf ((Q.reverse.take i).reverse)).1 with hacc
  have hacc_len : acc.reverse.length = 2 ^ i := by
    rw [List.length_reverse, hacc, divisorsOf_rev_take_length Q i hin.le]
  have hacc_lt : ∀ d ∈ acc.reverse, d < 2 ^ M := fun d hd =>
    divisorsOf_rev_take_mem_lt hb i d (List.mem_reverse.1 hd)
  set X := (2 ^ i + 1) * B M' with hX
  have hX4 : (2 ^ i + 1) * (4 * B M') = 4 * X := by rw [hX]; ring
  rw [hX4]
  have e1 : (2 ^ i + 1) * B M ≤ X := Nat.mul_le_mul_left _ (B_mono (by omega))
  have e2 : (2 ^ i + 1) * B (2 * M) ≤ X := Nat.mul_le_mul_left _ (B_mono (by omega))
  have e3 : B b ≤ X := by
    calc B b ≤ B M' := B_mono (by omega)
      _ = 1 * B M' := (one_mul _).symm
      _ ≤ X := Nat.mul_le_mul_right _ (by omega)
  -- stage 1: copyList a c s t
  have h1 := copyList_le_B hac has hat hcs hct hst acc.reverse M hacc_lt (S₀ a) v T hTa
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * X) h1
    fun v₁ T₁ ⟨ha₁, hc₁, hs₁, ht₁, hF₁⟩ => ?_) (fun _ _ h => h) (by rw [hacc_len]; omega)
  -- stage 2: mulAllF c z x s t
  have hz₁ : T₁ z = encodeNatΓ' q ++ .comma :: (encList R ++ S₀ z) := by
    rw [hF₁ z hza hzc hzs hzt, hTz]
  have h2 := mulAllF_le_B hzc.symm hxc.symm hcs hct hxz.symm hzs hzt hxs hxt hst q acc.reverse M hq
    hacc_lt (T c) _ v₁ T₁ hc₁ hz₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * X) h2
    fun v₂ T₂ ⟨hc₂, hz₂, hx₂, hs₂, ht₂, hF₂⟩ => ?_) (fun _ _ h => h)
    (by rw [mulAll_snd, hacc_len, ← hM', ← hX]; omega)
  -- stage 3: appendList c a t s
  have hl₁ : ∀ e ∈ (Alg.mulAll q acc.reverse).1, e < 2 ^ (2 * M) := mulAll_mem_lt hq hacc_lt
  have ha₂ : T₂ a = encList acc.reverse ++ S₀ a := by
    rw [hF₂ a hac hza.symm hxa.symm has hat, ha₁, hTa]
  have h3 := appendList_le_B hac.symm hct hcs hat has hst.symm _ acc.reverse (2 * M) hl₁ (T c) (S₀ a)
    v₂ T₂ hc₂ ha₂
  refine Frag.runs_mono (Frag.seq_runs (t₂ := X) h3
    fun v₃ T₃ ⟨hc₃, ha₃, ht₃, hs₃, hF₃⟩ => ?_) (fun _ _ h => h)
    (by rw [mulAll_fst, List.length_map, hacc_len]; omega)
  -- stage 4: dropNum z
  have hz₃ : T₃ z = encodeNatΓ' q ++ .comma :: (encList R ++ S₀ z) := by
    rw [hF₃ z hzc hza hzt hzs, hz₂, hz₁]
  have h4 := dropNum_le_B q b hqb _ v₃ T₃ hz₃
  refine Frag.runs_mono h4 (fun _ T₄ ⟨_, _, _, hz₄, hF₄⟩ => ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hz₄⟩) e3
  · rw [hF₄ a hza.symm, ha₃, divisorsOf_rev_take_succ Q i q R hdrop]
  · rw [hF₄ x hxz, hF₃ x hxc hxa hxt hxs, hx₂, hF₁ x hxa hxc hxs hxt, hTx]
  · rw [hF₄ c hzc.symm, hc₃, hTc]
  · rw [hF₄ s hzs.symm, hs₃, hs₂, hs₁, hTs]
  · rw [hF₄ t hzt.symm, ht₃, ht₂, ht₁, hTt]
  · intro k hkx hkz hka hkc hks hkt
    rw [hF₄ k hkz, hF₃ k hkc hka hkt hks, hF₂ k hkc hkz hkx hks hkt, hF₁ k hka hkc hks hkt,
      hTF k hkx hkz hka hkc hks hkt]

theorem divisorsOfF_le_B {x z a c s t : K} (hxz : x ≠ z) (hxa : x ≠ a) (hxc : x ≠ c) (hxs : x ≠ s)
    (hxt : x ≠ t) (hza : z ≠ a) (hzc : z ≠ c) (hzs : z ≠ s) (hzt : z ≠ t) (hac : a ≠ c)
    (has : a ≠ s) (hat : a ≠ t) (hcs : c ≠ s) (hct : c ≠ t) (hst : s ≠ t)
    (Q : List ℕ) (b : ℕ) (hb : ∀ q ∈ Q, q < 2 ^ b) (xr : List Γ') (v : St) (S : Stacks)
    (hS : S x = encList Q ++ xr) :
    (divisorsOfF x z a c s t).Runs v S (fun _ S' =>
        S' x = encList (Alg.divisorsOf Q).1 ++ xr ∧ S' z = S z ∧ S' a = S a ∧ S' c = S c ∧
        S' s = S s ∧ S' t = S t ∧
        ∀ k, k ≠ x → k ≠ z → k ≠ a → k ≠ c → k ≠ s → k ≠ t → S' k = S k)
      (((Alg.divisorsOf Q).2 + 1) * B (12 * Q.length * b + 22)) := by
  set M := Q.length * b + 1 with hM
  set M' := 4 * M + 2 with hM'
  have hcost : (Alg.divisorsOf Q).2 + 1 = 2 ^ Q.length := by
    rw [divisorsOf_snd, Nat.sub_add_cancel Nat.one_le_two_pow]
  have hB27 : B (12 * Q.length * b + 22) = 27 * B M' := by
    rw [show 12 * Q.length * b + 22 = (2 + 1) * M' + 2 * 2 by rw [hM', hM]; ring, ← B_scale]
    norm_num
  have hBM : B M ≤ B M' := B_mono (by omega)
  have hn2 : Q.length + 1 ≤ 2 ^ Q.length := two_pow_mul_le _
  have hB1 : 1 ≤ B M' := one_le_B _
  have hB4 : 4 ≤ B M' := le_B_of_le_linear (by omega)
  rw [hcost, hB27, Nat.mul_left_comm]
  set L := ∑ i ∈ Finset.range Q.length, ((2 ^ i + 1) * (4 * B M') + 2) + 2 with hL
  have hLle : L ≤ 8 * (2 ^ Q.length * B M') + 2 * 2 ^ Q.length := by
    calc L ≤ 2 ^ Q.length * (2 * (4 * B M') + 2) := sum_geom_bound _ _
      _ = 8 * (2 ^ Q.length * B M') + 2 * 2 ^ Q.length := by ring
  have e4 : 1 ≤ 2 ^ Q.length := Nat.one_le_two_pow
  have e1 : Q.length * (2 * b + 6) + 4 ≤ 2 ^ Q.length * B M' := by
    rcases Nat.eq_zero_or_pos Q.length with h0 | hpos
    · rw [h0]; simp only [zero_mul, zero_add, pow_zero, one_mul]; exact hB4
    · have hb' : b ≤ Q.length * b := Nat.le_mul_of_pos_left b hpos
      have h2 : 2 * b + 6 ≤ B M' := le_B_of_le_linear (by omega)
      have h3 : Q.length * (2 * b + 6) ≤ Q.length * B M' := Nat.mul_le_mul_left _ h2
      have h4 : (Q.length + 1) * B M' ≤ 2 ^ Q.length * B M' := Nat.mul_le_mul_right _ hn2
      have h5 : (Q.length + 1) * B M' = Q.length * B M' + B M' := by ring
      omega
  have e2 : (2 ^ Q.length + 1) * B M ≤ 2 * (2 ^ Q.length * B M') := by
    calc (2 ^ Q.length + 1) * B M ≤ (2 * 2 ^ Q.length) * B M' := Nat.mul_le_mul (by omega) hBM
      _ = 2 * (2 ^ Q.length * B M') := by ring
  have e3 : 2 ^ Q.length ≤ 2 ^ Q.length * B M' := Nat.le_mul_of_pos_right _ hB1
  -- stage 1: revList x z s
  have h1 := revList_correct hxz hxs hzs Q b hb xr v S hS
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L + 4 + (2 ^ Q.length + 1) * B M) h1
    fun v₁ S₁ ⟨hx₁, hz₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 2: pushSym a bra
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L + 3 + (2 ^ Q.length + 1) * B M)
    (Frag.pushSym_runs a .bra v₁ S₁) fun v₂ S₂ ⟨hv₂, hS₂⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₂]; subst hS₂
  -- stage 3: pushNum a 1
  refine Frag.runs_mono (Frag.seq_runs (t₂ := L + 1 + (2 ^ Q.length + 1) * B M)
    (pushNum_runs a 1 v₁ (Function.update S₁ a (Γ'.bra :: S₁ a)))
    fun v₃ S₃ ⟨hv₃, ha₃, hF₃⟩ => ?_) (fun _ _ h => h) (by simp only [Nat.log_one_right]; omega)
  -- stage 4: the loop over Q.reverse
  have hz₃ : S₃ z = encList Q.reverse ++ S z := by
    rw [hF₃ z hza, Function.update_of_ne hza, hz₁]
  have ha₁ : S₁ a = S a := hF₁ a hxa.symm hza.symm has
  have hloop := forEntriesN_runs' (x := z) (body := divBody x z a c s t) Q.reverse (S z)
    (DivInv x z a c s t Q xr S) (fun i => (2 ^ i + 1) * (4 * B M')) v₃ S₃ hz₃
    ⟨by rw [ha₃, Function.update_self, ha₁]; simp [Alg.divisorsOf, encList_cons],
      by rw [hF₃ x hxa, Function.update_of_ne hxa, hx₁],
      by rw [hF₃ c hac.symm, Function.update_of_ne hac.symm, hF₁ c hxc.symm hzc.symm hcs],
      by rw [hF₃ s has.symm, Function.update_of_ne has.symm, hs₁],
      by rw [hF₃ t hat.symm, Function.update_of_ne hat.symm, hF₁ t hxt.symm hzt.symm hst.symm],
      fun k hkx hkz hka hkc hks hkt => by
        rw [hF₃ k hka, Function.update_of_ne hka, hF₁ k hkx hkz hks]⟩
    (fun i q R hdrop w T hP hT =>
      divBody_runs hxz hxa hxc hxs hxt hza hzc hzs hzt hac has hat hcs hct hst Q b hb xr S i q R
        hdrop w T hP hT)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 1 + (2 ^ Q.length + 1) * B M) hloop
    fun v₄ S₄ ⟨_, ⟨ha₄, hx₄, hc₄, hs₄, ht₄, hF₄⟩, hz₄⟩ => ?_) (fun _ _ h => h)
    (by simp only [List.length_reverse]; rw [← hL]; omega)
  -- stage 5: popTop z
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (2 ^ Q.length + 1) * B M) (popTop_runs z v₄ S₄)
    fun v₅ S₅ ⟨hv₅, hS₅⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₅]; subst hS₅
  -- stage 6: revList a x s
  have hdiv_lt : ∀ d ∈ (Alg.divisorsOf Q).1.reverse, d < 2 ^ M := by
    intro d hd
    have := divisorsOf_mem_le hb d (List.mem_reverse.1 hd)
    calc d ≤ 2 ^ (Q.length * b) := this
      _ < 2 ^ M := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have ha₅ : Function.update S₄ z (S₄ z).tail a = encList (Alg.divisorsOf Q).1.reverse ++ S a := by
    rw [Function.update_of_ne hza.symm, ha₄, List.take_length, List.reverse_reverse]
  have h6 := revList_le_B hxa.symm has hxs _ M hdiv_lt (S a) v₄ _ ha₅
  refine Frag.runs_mono h6 (fun _ S₆ ⟨ha₆, hx₆, hs₆, hF₆⟩ => ⟨?_, ?_, ha₆, ?_, ?_, ?_, ?_⟩)
    (by simp only [List.length_reverse, divisorsOf_length]; omega)
  · rw [hx₆, Function.update_of_ne hxz, hx₄, List.reverse_reverse]
  · rw [hF₆ z hza hxz.symm hzs, Function.update_self, hz₄]; rfl
  · rw [hF₆ c hac.symm hxc.symm hcs, Function.update_of_ne hzc.symm, hc₄]
  · rw [hs₆, Function.update_of_ne hzs.symm, hs₄]
  · rw [hF₆ t hat.symm hxt.symm hst.symm, Function.update_of_ne hzt.symm, ht₄]
  · intro k hkx hkz hka hkc hks hkt
    rw [hF₆ k hka hkx hks, Function.update_of_ne hkz, hF₄ k hkx hkz hka hkc hks hkt]

end Carmichael.TM
