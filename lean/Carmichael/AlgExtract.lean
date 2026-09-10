/-
Route A, step 4: correctness and cost of `Alg.extract`, the greedy
extraction of subsets of the pool with product `≡ 1 (mod L)`.

The DP table `t : Tbl` is analysed through three invariants relative to the
list `E` of elements processed since the last reset:

* `TblSound L t E`: every entry `t r = some W` is a nonempty duplicate-free
  list of elements of `E` with `W.prod % L = r`;
* `TblComplete L t E`: every nonempty subset of `E` has its product residue
  populated;
* `TblBounded t k`: every entry has length at most `k` (for the cost bound;
  it needs no hypothesis on the input list).

`dpStep` preserves all three from `E` to `p :: E` (soundness needs
`p ∉ E`). The round argument for `extractGo` then shows: completeness plus
the VEBK hypothesis force a hit within `N` fresh elements of every reset;
each hit multiplies the running product by at least `L + 1`; so the product
exceeds `n` after at most `Nat.log (L + 1) n + 1` hits, before the pool is
exhausted.
-/
import Carmichael.Algorithm

set_option autoImplicit false

namespace Carmichael

namespace Alg

/-! ### Table invariants -/

/-- Every entry of `t` is a nonempty duplicate-free list of elements of `E`
stored at the residue of its product. -/
def TblSound (L : ℕ) (t : Tbl) (E : List ℕ) : Prop :=
  ∀ r W, t r = some W → W ≠ [] ∧ W.Nodup ∧ (∀ q ∈ W, q ∈ E) ∧ W.prod % L = r

/-- Every nonempty subset of `E` has the residue of its product populated. -/
def TblComplete (L : ℕ) (t : Tbl) (E : List ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ E.toFinset → S.Nonempty → t ((∏ q ∈ S, q) % L) ≠ none

/-- Every entry of `t` has length at most `k`. -/
def TblBounded (t : Tbl) (k : ℕ) : Prop :=
  ∀ r W, t r = some W → W.length ≤ k

/-! ### `setIfNone` -/

theorem setIfNone_apply (t : Tbl) (r : ℕ) (W : List ℕ) (r' : ℕ) :
    setIfNone t r W r' = if t r = none ∧ r' = r then some W else t r' := by
  unfold setIfNone
  cases hr : t r with
  | none => simp only [true_and]; exact Function.update_apply t r (some W) r'
  | some V => simp

theorem setIfNone_persist {t : Tbl} {r' : ℕ} {W' : List ℕ} (r : ℕ) (W : List ℕ)
    (h : t r' = some W') : setIfNone t r W r' = some W' := by
  rw [setIfNone_apply]
  split_ifs with hc
  · obtain ⟨h1, rfl⟩ := hc
    rw [h] at h1
    exact absurd h1 (by simp)
  · exact h

theorem setIfNone_self (t : Tbl) (r : ℕ) (W : List ℕ) : setIfNone t r W r ≠ none := by
  rw [setIfNone_apply]
  split_ifs with hc
  · simp
  · intro h
    exact hc ⟨h, rfl⟩

theorem setIfNone_cases {t : Tbl} {r' : ℕ} {W' : List ℕ} {r : ℕ} {W : List ℕ}
    (h : setIfNone t r W r' = some W') : t r' = some W' ∨ (r' = r ∧ W' = W) := by
  rw [setIfNone_apply] at h
  split_ifs at h with hc
  · exact Or.inr ⟨hc.2, (Option.some.inj h).symm⟩
  · exact Or.inl h

/-! ### `dpGo` -/

theorem dpGo_cost (L p : ℕ) (t : Tbl) (fuel : ℕ) :
    ∀ acc : Tbl, (dpGo L p t fuel acc).2 = fuel := by
  induction fuel with
  | zero => intro acc; simp [dpGo]
  | succ fuel ih => intro acc; simp only [dpGo]; rw [ih]

/-- Entries of the accumulator persist. -/
theorem dpGo_persist (L p : ℕ) (t : Tbl) (fuel : ℕ) :
    ∀ (acc : Tbl) (r' : ℕ) (W' : List ℕ), acc r' = some W' →
      (dpGo L p t fuel acc).1 r' = some W' := by
  induction fuel with
  | zero => intro acc r' W' h; simpa [dpGo] using h
  | succ fuel ih =>
    intro acc r' W' h
    simp only [dpGo]
    apply ih
    cases ht : t fuel with
    | none => exact h
    | some W => exact setIfNone_persist _ _ h

theorem dpGo_ne_none (L p : ℕ) (t : Tbl) (fuel : ℕ) (acc : Tbl) (r' : ℕ)
    (h : acc r' ≠ none) : (dpGo L p t fuel acc).1 r' ≠ none := by
  obtain ⟨W', hW'⟩ := Option.ne_none_iff_exists'.mp h
  rw [dpGo_persist L p t fuel acc r' W' hW']
  simp

/-- Every snapshot entry at `r < fuel` is propagated to `(r * p) % L`. -/
theorem dpGo_hit (L p : ℕ) (t : Tbl) (fuel : ℕ) :
    ∀ (acc : Tbl) (r : ℕ), r < fuel → t r ≠ none →
      (dpGo L p t fuel acc).1 ((r * p) % L) ≠ none := by
  induction fuel with
  | zero => intro acc r hr _; exact absurd hr (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro acc r hr htr
    simp only [dpGo]
    by_cases hrf : r = fuel
    · subst hrf
      apply dpGo_ne_none
      obtain ⟨W, hW⟩ := Option.ne_none_iff_exists'.mp htr
      simp only [hW]
      exact setIfNone_self _ _ _
    · exact ih _ r (by omega) htr

/-- Every entry of the result is an entry of the accumulator or `p :: W` for
a snapshot entry `W` at some `r < fuel`. -/
theorem dpGo_cases (L p : ℕ) (t : Tbl) (fuel : ℕ) :
    ∀ (acc : Tbl) (r' : ℕ) (W' : List ℕ), (dpGo L p t fuel acc).1 r' = some W' →
      acc r' = some W' ∨
        ∃ r W, r < fuel ∧ t r = some W ∧ r' = (r * p) % L ∧ W' = p :: W := by
  induction fuel with
  | zero => intro acc r' W' h; exact Or.inl (by simpa [dpGo] using h)
  | succ fuel ih =>
    intro acc r' W' h
    simp only [dpGo] at h
    rcases ih _ r' W' h with h1 | ⟨r, W, hr, htr, rfl, rfl⟩
    · cases ht : t fuel with
      | none =>
        simp only [ht] at h1
        exact Or.inl h1
      | some W =>
        simp only [ht] at h1
        rcases setIfNone_cases h1 with h2 | ⟨rfl, rfl⟩
        · exact Or.inl h2
        · exact Or.inr ⟨fuel, W, Nat.lt_succ_self _, ht, rfl, rfl⟩
    · exact Or.inr ⟨r, W, Nat.lt_succ_of_lt hr, htr, rfl, rfl⟩

/-! ### `dpStep` -/

theorem dpStep_cost (L p : ℕ) (t : Tbl) : (dpStep L p t).2 = L + 1 := by
  simp only [dpStep, dpGo_cost]

theorem dpStep_persist (L p : ℕ) (t : Tbl) {r' : ℕ} {W' : List ℕ} (h : t r' = some W') :
    (dpStep L p t).1 r' = some W' := by
  simp only [dpStep]
  exact dpGo_persist _ _ _ _ _ _ _ (setIfNone_persist _ _ h)

theorem dpStep_ne_none (L p : ℕ) (t : Tbl) {r' : ℕ} (h : t r' ≠ none) :
    (dpStep L p t).1 r' ≠ none := by
  obtain ⟨W', hW'⟩ := Option.ne_none_iff_exists'.mp h
  rw [dpStep_persist L p t hW']
  simp

theorem dpStep_self (L p : ℕ) (t : Tbl) : (dpStep L p t).1 (p % L) ≠ none := by
  simp only [dpStep]
  exact dpGo_ne_none _ _ _ _ _ _ (setIfNone_self _ _ _)

theorem dpStep_hit (L p : ℕ) (t : Tbl) {r : ℕ} (hr : r < L) (h : t r ≠ none) :
    (dpStep L p t).1 ((r * p) % L) ≠ none := by
  simp only [dpStep]
  exact dpGo_hit _ _ _ _ _ _ hr h

theorem dpStep_cases (L p : ℕ) (t : Tbl) {r' : ℕ} {W' : List ℕ}
    (h : (dpStep L p t).1 r' = some W') :
    t r' = some W' ∨ (r' = p % L ∧ W' = [p]) ∨
      ∃ r W, r < L ∧ t r = some W ∧ r' = (r * p) % L ∧ W' = p :: W := by
  simp only [dpStep] at h
  rcases dpGo_cases _ _ _ _ _ _ _ h with h1 | h1
  · rcases setIfNone_cases h1 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h1)

/-! ### Preservation of the invariants -/

theorem tblSound_empty (L : ℕ) (E : List ℕ) : TblSound L emptyTbl E := by
  intro r W h
  exact absurd h (by simp [emptyTbl])

theorem tblComplete_empty (L : ℕ) : TblComplete L emptyTbl [] := by
  intro S hS hne
  rw [List.toFinset_nil, Finset.subset_empty] at hS
  exact absurd hS hne.ne_empty

theorem tblBounded_empty (k : ℕ) : TblBounded emptyTbl k := by
  intro r W h
  exact absurd h (by simp [emptyTbl])

theorem tblSound_dpStep {L : ℕ} {t : Tbl} {E : List ℕ} (p : ℕ) (hp : p ∉ E)
    (hs : TblSound L t E) : TblSound L (dpStep L p t).1 (p :: E) := by
  intro r' W' h
  rcases dpStep_cases L p t h with h1 | ⟨rfl, rfl⟩ | ⟨r, W, _, htr, rfl, rfl⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hs _ _ h1
    exact ⟨h1, h2, fun q hq => List.mem_cons_of_mem _ (h3 q hq), h4⟩
  · refine ⟨by simp, List.nodup_singleton p, ?_, by simp⟩
    intro q hq
    rw [List.mem_singleton] at hq
    subst hq
    exact List.mem_cons_self
  · obtain ⟨_, h2, h3, h4⟩ := hs _ _ htr
    refine ⟨by simp, ?_, ?_, ?_⟩
    · rw [List.nodup_cons]
      exact ⟨fun hpW => hp (h3 p hpW), h2⟩
    · intro q hq
      rw [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (h3 q hq)
    · rw [List.prod_cons, ← h4, Nat.mod_mul_mod, mul_comm]

theorem tblComplete_dpStep {L : ℕ} (hL : 0 < L) {t : Tbl} {E : List ℕ} (p : ℕ)
    (hc : TblComplete L t E) : TblComplete L (dpStep L p t).1 (p :: E) := by
  intro S hS hne
  rw [List.toFinset_cons] at hS
  by_cases hpS : p ∈ S
  · have hS' : S.erase p ⊆ E.toFinset := by
      intro q hq
      rw [Finset.mem_erase] at hq
      have := hS hq.2
      rw [Finset.mem_insert] at this
      exact this.resolve_left hq.1
    have hprod : ∏ q ∈ S, q = p * ∏ q ∈ S.erase p, q :=
      (Finset.mul_prod_erase S (fun q => q) hpS).symm
    rw [hprod]
    rcases (S.erase p).eq_empty_or_nonempty with he | hne'
    · rw [he, Finset.prod_empty, mul_one]
      exact dpStep_self L p t
    · have := dpStep_hit L p t (Nat.mod_lt _ hL) (hc _ hS' hne')
      rwa [Nat.mod_mul_mod, mul_comm] at this
  · have hS' : S ⊆ E.toFinset := by
      intro q hq
      have := hS hq
      rw [Finset.mem_insert] at this
      exact this.resolve_left (fun h => hpS (h ▸ hq))
    exact dpStep_ne_none L p t (hc S hS' hne)

theorem tblBounded_dpStep {t : Tbl} {k : ℕ} (L p : ℕ) (hb : TblBounded t k) :
    TblBounded (dpStep L p t).1 (k + 1) := by
  intro r' W' h
  rcases dpStep_cases L p t h with h1 | ⟨_, rfl⟩ | ⟨r, W, _, htr, _, rfl⟩
  · exact Nat.le_succ_of_le (hb _ _ h1)
  · simp
  · simp only [List.length_cons]
    exact Nat.succ_le_succ (hb _ _ htr)

/-! ### `prodL` -/

private theorem prodL_fst (S : List ℕ) : (prodL S).1 = S.prod := by
  induction S with
  | nil => rfl
  | cons p S ih => simp only [prodL, List.prod_cons, ih]

private theorem prodL_snd (S : List ℕ) : (prodL S).2 = S.length := by
  induction S with
  | nil => rfl
  | cons p S ih => simp only [prodL, List.length_cons, ih]

/-! ### The cost of `extractGo` -/

/-- With every table entry of length at most `k`, `extractGo` charges at
most `P.length * (L + 3) + k`: each element charges `dpStep = L + 1` plus
`1`, and a hit charges `|S|`, which is at most the number of elements
processed since the last reset. -/
theorem extractGo_cost (L n : ℕ) (P : List ℕ) :
    ∀ (m : ℕ) (used : List ℕ) (t : Tbl) (k : ℕ), TblBounded t k →
      (extractGo L n P m used t).2 ≤ P.length * (L + 3) + k := by
  induction P with
  | nil => intro m used t k _; simp [extractGo]
  | cons p P ih =>
    intro m used t k hb
    have hb' := tblBounded_dpStep L p hb
    simp only [extractGo, List.length_cons, dpStep_cost, prodL_snd]
    rw [Nat.add_mul, one_mul]
    cases hst : (dpStep L p t).1 (1 % L) with
    | none =>
      have := ih m used (dpStep L p t).1 (k + 1) hb'
      simp only
      omega
    | some S =>
      have hS := hb' _ _ hst
      simp only
      split_ifs
      · omega
      · have := ih (m * (prodL S).1) (S ++ used) emptyTbl 0 (tblBounded_empty 0)
        omega

/-! ### The round argument for `extractGo` -/

/-- The invariant of the extraction loop. `P₀` is the original pool; `P` the
remaining suffix; `used` the elements already multiplied into `m`; `E` the
elements processed since the last reset; `h` the number of hits so far. -/
theorem extractGo_spec (L n x N : ℕ) (P₀ : List ℕ) (hL : 2 ≤ L) (hN : 1 ≤ N)
    (hP2 : ∀ p ∈ P₀, 2 ≤ p) (hPx : ∀ p ∈ P₀, p ≤ x)
    (hvebk : ∀ W : Finset ℕ, W ⊆ P₀.toFinset → W.card = N →
      ∃ S ⊆ W, S.Nonempty ∧ (∏ p ∈ S, p) ≡ 1 [MOD L]) (P : List ℕ) :
    ∀ (m : ℕ) (used E : List ℕ) (t : Tbl) (h : ℕ),
      P.Nodup → (∀ q ∈ P, q ∈ P₀) →
      E.Nodup → (∀ q ∈ E, q ∈ P₀) → (∀ q ∈ E, q ∉ P) → (∀ q ∈ E, q ∉ used) →
      used.Nodup → (∀ q ∈ used, q ∈ P₀) → (∀ q ∈ used, q ∉ P) →
      m = used.prod → m ≡ 1 [MOD L] → m ≤ n →
      TblSound L t E → TblComplete L t E → E.length < N →
      (L + 1) ^ h ≤ m → (Nat.log (L + 1) n + 1) * N ≤ P.length + h * N + E.length →
      ∃ m' S, (extractGo L n P m used t).1 = some (m', S) ∧ S.Nodup ∧
        (∀ p ∈ S, p ∈ P₀) ∧ S.prod = m' ∧ m' ≡ 1 [MOD L] ∧ n < m' ∧ m' ≤ n * x ^ N := by
  induction P with
  | nil =>
    intro m used E t h _ _ _ _ _ _ _ _ _ _ _ hmn _ _ hEN hpow hsup
    exfalso
    simp only [List.length_nil, zero_add] at hsup
    have hh : Nat.log (L + 1) n + 1 ≤ h := by
      rcases Nat.lt_or_ge h (Nat.log (L + 1) n + 1) with hlt | hge
      · exfalso
        have : (h + 1) * N ≤ (Nat.log (L + 1) n + 1) * N := Nat.mul_le_mul_right N hlt
        rw [Nat.add_mul, one_mul] at this
        omega
      · exact hge
    have h1 : (L + 1) ^ (Nat.log (L + 1) n + 1) ≤ (L + 1) ^ h :=
      Nat.pow_le_pow_right (by omega) hh
    have h2 : n < (L + 1) ^ (Nat.log (L + 1) n + 1) := Nat.lt_pow_succ_log_self (by omega) n
    omega
  | cons p P ih =>
    intro m used E t h hPnd hPP₀ hEnd hEP₀ hEP hEu hund huP₀ huP hm hm1 hmn hs hc hEN hpow hsup
    have hpE : p ∉ E := fun hpE => hEP p hpE List.mem_cons_self
    have hpP : p ∉ P := (List.nodup_cons.mp hPnd).1
    have hPnd' : P.Nodup := (List.nodup_cons.mp hPnd).2
    have hpP₀ : p ∈ P₀ := hPP₀ p List.mem_cons_self
    have hpu : p ∉ used := fun hpu => huP p hpu List.mem_cons_self
    have hs' := tblSound_dpStep p hpE hs
    have hc' := tblComplete_dpStep (by omega) p hc
    have hPP₀' : ∀ q ∈ P, q ∈ P₀ := fun q hq => hPP₀ q (List.mem_cons_of_mem _ hq)
    have huP' : ∀ q ∈ used, q ∉ P := fun q hq hqP => huP q hq (List.mem_cons_of_mem _ hqP)
    simp only [extractGo]
    cases hst : (dpStep L p t).1 (1 % L) with
    | none =>
      -- no hit: `E.length + 1 < N`, else VEBK and completeness give a hit
      have hEN' : E.length + 1 < N := by
        rcases Nat.lt_or_ge (E.length + 1) N with hlt | hge
        · exact hlt
        · exfalso
          have hcard : (p :: E).toFinset.card = N := by
            rw [List.toFinset_card_of_nodup (List.nodup_cons.mpr ⟨hpE, hEnd⟩)]
            simp only [List.length_cons]
            omega
          have hsub : (p :: E).toFinset ⊆ P₀.toFinset := by
            intro q hq
            rw [List.mem_toFinset] at hq ⊢
            rw [List.mem_cons] at hq
            rcases hq with rfl | hq
            · exact hpP₀
            · exact hEP₀ q hq
          obtain ⟨S, hSsub, hSne, hS1⟩ := hvebk _ hsub hcard
          have := hc' S hSsub hSne
          have hS1' : (∏ q ∈ S, q) % L = 1 % L := hS1
          rw [hS1', hst] at this
          exact this rfl
      simp only
      refine ih m used (p :: E) (dpStep L p t).1 h hPnd' hPP₀'
        (List.nodup_cons.mpr ⟨hpE, hEnd⟩) ?_ ?_ ?_ hund huP₀ huP' hm hm1 hmn hs' hc'
        (by simpa using hEN') hpow ?_
      · intro q hq
        rw [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hpP₀
        · exact hEP₀ q hq
      · intro q hq
        rw [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hpP
        · exact fun hqP => hEP q hq (List.mem_cons_of_mem _ hqP)
      · intro q hq
        rw [List.mem_cons] at hq
        rcases hq with rfl | hq
        · exact hpu
        · exact hEu q hq
      · simp only [List.length_cons] at hsup ⊢
        omega
    | some S =>
      obtain ⟨hSne, hSnd, hSE, hSprod⟩ := hs' _ _ hst
      simp only [prodL_fst]
      have hSP₀ : ∀ q ∈ S, q ∈ P₀ := fun q hq => by
        rcases List.mem_cons.mp (hSE q hq) with rfl | hq'
        · exact hpP₀
        · exact hEP₀ q hq'
      have hSu : ∀ q ∈ S, q ∉ used := fun q hq => by
        rcases List.mem_cons.mp (hSE q hq) with rfl | hq'
        · exact hpu
        · exact hEu q hq'
      have hSP : ∀ q ∈ S, q ∉ P := fun q hq => by
        rcases List.mem_cons.mp (hSE q hq) with rfl | hq'
        · exact hpP
        · exact fun hqP => hEP q hq' (List.mem_cons_of_mem _ hqP)
      have hSlen : S.length ≤ N := by
        have := (List.subperm_of_subset hSnd hSE).length_le
        simp only [List.length_cons] at this
        omega
      have hSprod1 : S.prod ≡ 1 [MOD L] := hSprod
      obtain ⟨q₀, S', hS'⟩ := List.exists_cons_of_ne_nil hSne
      have hq₀ : q₀ ∈ S := hS' ▸ List.mem_cons_self
      have hq₀2 : 2 ≤ q₀ := hP2 q₀ (hSP₀ q₀ hq₀)
      have hq₀x : q₀ ≤ x := hPx q₀ (hSP₀ q₀ hq₀)
      have hS2 : 2 ≤ S.prod := by
        rw [hS', List.prod_cons]
        have hpos : 0 < S'.prod := List.prod_pos (fun a ha => by
          have := hP2 a (hSP₀ a (hS' ▸ List.mem_cons_of_mem _ ha))
          omega)
        nlinarith
      have hSL : L + 1 ≤ S.prod := by
        have hdm := Nat.div_add_mod S.prod L
        have h1L : 1 % L = 1 := Nat.mod_eq_of_lt (by omega)
        rw [hSprod, h1L] at hdm
        rcases Nat.eq_zero_or_pos (S.prod / L) with h0 | hpos
        · rw [h0, mul_zero, zero_add] at hdm
          omega
        · nlinarith
      have hSx : S.prod ≤ x ^ N :=
        calc S.prod ≤ x ^ S.length := List.prod_le_pow_card S x (fun q hq => hPx q (hSP₀ q hq))
          _ ≤ x ^ N := Nat.pow_le_pow_right (by omega) hSlen
      have hnd : (S ++ used).Nodup := by
        rw [List.nodup_append]
        exact ⟨hSnd, hund, fun a ha b hb hab => hSu a ha (hab ▸ hb)⟩
      have hprod : (S ++ used).prod = m * S.prod := by
        rw [List.prod_append, hm, mul_comm]
      have hm1' : m * S.prod ≡ 1 [MOD L] := by simpa using hm1.mul hSprod1
      have hall : ∀ q ∈ S ++ used, q ∈ P₀ := fun q hq => by
        rcases List.mem_append.mp hq with hq | hq
        · exact hSP₀ q hq
        · exact huP₀ q hq
      by_cases hlt : n < m * S.prod
      · rw [if_pos hlt]
        exact ⟨m * S.prod, S ++ used, rfl, hnd, hall, hprod, hm1', hlt, Nat.mul_le_mul hmn hSx⟩
      · rw [if_neg hlt]
        simp only
        refine ih (m * S.prod) (S ++ used) [] emptyTbl (h + 1) hPnd' hPP₀' List.nodup_nil
          (by simp) (by simp) (by simp) hnd hall ?_ hprod.symm hm1' (by omega)
          (tblSound_empty L []) (tblComplete_empty L) (by simp only [List.length_nil]; exact hN) ?_ ?_
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact hSP q hq
          · exact huP' q hq
        · rw [pow_succ]
          exact Nat.mul_le_mul hpow hSL
        · simp only [List.length_cons, List.length_nil, add_zero, Nat.add_mul, one_mul] at hsup ⊢
          omega

end Alg

/-! ### The frozen statements (blueprint §3, sortie A4) -/

-- `hPcop` is part of the frozen statement but unused: the DP tracks residues
-- directly and never needs coprimality of the pool to `L`.
set_option linter.unusedVariables false in
theorem extract_spec (L n x N : ℕ) (P : List ℕ)
    (hL : 2 ≤ L) (hn : 1 ≤ n) (hN : 1 ≤ N)
    (hP : P.Nodup) (hPcop : ∀ p ∈ P, p.Coprime L) (hP2 : ∀ p ∈ P, 2 ≤ p)
    (hPx : ∀ p ∈ P, p ≤ x)
    (hvebk : ∀ W : Finset ℕ, W ⊆ P.toFinset → W.card = N →
      ∃ S ⊆ W, S.Nonempty ∧ (∏ p ∈ S, p) ≡ 1 [MOD L])
    (hsupply : (Nat.log (L + 1) n + 1) * N ≤ P.length) :
    ∃ m S, (Alg.extract L n P).1 = some (m, S) ∧ S.Nodup ∧ (∀ p ∈ S, p ∈ P) ∧
      S.prod = m ∧ m ≡ 1 [MOD L] ∧ n < m ∧ m ≤ n * x ^ N := by
  exact Alg.extractGo_spec L n x N P hL hN hP2 hPx hvebk P 1 [] [] Alg.emptyTbl 0 hP
    (fun q hq => hq) List.nodup_nil (by simp) (by simp) (by simp) List.nodup_nil (by simp)
    (by simp) List.prod_nil.symm (Nat.ModEq.refl 1) hn (Alg.tblSound_empty L [])
    (Alg.tblComplete_empty L) (by simp only [List.length_nil]; exact hN) (by simp)
    (by simpa using hsupply)

theorem extract_cost (L n : ℕ) (P : List ℕ) :
    (Alg.extract L n P).2 ≤ P.length * (L + 3) + 1 := by
  have := Alg.extractGo_cost L n P 1 [] Alg.emptyTbl 0 (Alg.tblBounded_empty 0)
  unfold Alg.extract
  omega

end Carmichael
