/-
Route A, sortie A2: correctness and cost of the primitives, of step 2 (the
reservoir), of step 3 (pool and scan) and of step 5 (verification) of
`Carmichael/Algorithm.lean`, against the Mathlib predicates and the
`Finset` definitions of `Carmichael/Defs.lean` and `Carmichael/DefsW.lean`.

Every loop of the algorithm is structural on a fuel or on a list, so every
proof below is a plain induction with the loop invariant stated explicitly
(`primeGo_spec`, `divOut_*`, `smoothGo_*`, `resGo_*`, `poolGo_*`,
`scan_go`).
-/
import Carmichael.Algorithm
import Carmichael.DefsW
import Carmichael.Korselt

set_option autoImplicit false

namespace Carmichael

open Alg

/-! ### Primality by trial division -/

/-- Loop invariant of `primeGo`: with `2 ≤ d` and enough fuel to reach
`d > m`, the loop reports `true` iff no `e ∈ [d, √m]` divides `m`. -/
theorem primeGo_spec (m d fuel : ℕ) (hd : 2 ≤ d) (hfuel : m < d + fuel) :
    (primeGo m d fuel).1 = true ↔ ∀ e, d ≤ e → e * e ≤ m → ¬ e ∣ m := by
  induction fuel generalizing d with
  | zero =>
    simp only [primeGo, true_iff]
    intro e hde hee _
    have : d ≤ e * e := le_trans hde (Nat.le_mul_self e)
    omega
  | succ fuel ih =>
    simp only [primeGo]
    split_ifs with h1 h2
    · simp only [true_iff]
      intro e hde hee
      have : d * d ≤ e * e := Nat.mul_le_mul hde hde
      omega
    · simp only [false_iff, not_forall, not_not]
      exact ⟨d, le_rfl, by omega, Nat.dvd_of_mod_eq_zero h2⟩
    · rw [ih (d + 1) (by omega) (by omega)]
      constructor
      · intro h e hde hee
        rcases Nat.eq_or_lt_of_le hde with rfl | hlt
        · intro hdvd
          exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
        · exact h e hlt hee
      · intro h e hde hee
        exact h e (by omega) hee

theorem isPrimeTD_spec (m : ℕ) : (Alg.isPrimeTD m).1 = true ↔ m.Prime := by
  unfold isPrimeTD
  split_ifs with h
  · simp only [false_iff]
    intro hp
    have := hp.two_le
    omega
  · simp only
    rw [primeGo_spec m 2 m le_rfl (by omega), Nat.prime_def_le_sqrt]
    constructor
    · intro h
      refine ⟨by omega, fun e he hes => h e he (Nat.le_sqrt.mp hes)⟩
    · intro h e he hee
      exact h.2 e he (Nat.le_sqrt.mpr hee)

/-- Cost invariant of `primeGo`: starting at `d ≤ √m + 1`, at most
`√m + 2 - d` bodies run. -/
theorem primeGo_cost (m d fuel : ℕ) (hd : d ≤ Nat.sqrt m + 1) :
    (primeGo m d fuel).2 ≤ Nat.sqrt m + 2 - d := by
  induction fuel generalizing d with
  | zero => simp [primeGo]
  | succ fuel ih =>
    simp only [primeGo]
    split_ifs with h1 h2
    · omega
    · omega
    · have hle : d ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by omega)
      have := ih (d + 1) (by omega)
      omega

theorem isPrimeTD_cost (m : ℕ) : (Alg.isPrimeTD m).2 ≤ Nat.sqrt m + 1 := by
  unfold isPrimeTD
  split_ifs with h
  · omega
  · simp only
    have h1 : 1 ≤ Nat.sqrt m := Nat.le_sqrt.mpr (by omega)
    have := primeGo_cost m 2 m (by omega)
    omega

/-! ### Smoothness by trial division -/

theorem divOut_dvd (d r fuel : ℕ) : (divOut d r fuel).1 ∣ r := by
  induction fuel generalizing r with
  | zero => simp [divOut]
  | succ fuel ih =>
    simp only [divOut]
    split_ifs with h
    · exact (ih (r / d)).trans (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero h))
    · exact dvd_rfl

theorem divOut_prime (d r fuel p : ℕ) (hp : p.Prime) (hpr : p ∣ r) :
    p ∣ (divOut d r fuel).1 ∨ p ∣ d := by
  induction fuel generalizing r with
  | zero => simpa [divOut] using Or.inl hpr
  | succ fuel ih =>
    simp only [divOut]
    split_ifs with h
    · have hdr : d ∣ r := Nat.dvd_of_mod_eq_zero h
      have hr : r = d * (r / d) := (Nat.mul_div_cancel' hdr).symm
      rw [hr] at hpr
      rcases (Nat.Prime.dvd_mul hp).mp hpr with hpd | hpq
      · exact Or.inr hpd
      · exact ih (r / d) hpq
    · exact Or.inl hpr

theorem divOut_not_dvd (d r fuel : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) (hfuel : r ≤ fuel) :
    ¬ d ∣ (divOut d r fuel).1 := by
  induction fuel generalizing r with
  | zero => omega
  | succ fuel ih =>
    simp only [divOut]
    split_ifs with h
    · have hdr : d ∣ r := Nat.dvd_of_mod_eq_zero h
      have h1 : 1 ≤ r / d := Nat.div_pos (Nat.le_of_dvd hr hdr) (by omega)
      have h2 : r / d < r := Nat.div_lt_self hr (by omega)
      exact ih (r / d) h1 (by omega)
    · intro hdvd
      exact h (Nat.mod_eq_zero_of_dvd hdvd)

/-- Each successful division at least halves `r`, so the number of
successful divisions plus `log₂` of the result is at most `log₂ r`. -/
theorem divOut_cost (d r fuel : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) :
    (divOut d r fuel).2 + Nat.log 2 (divOut d r fuel).1 ≤ Nat.log 2 r := by
  induction fuel generalizing r with
  | zero => simp [divOut]
  | succ fuel ih =>
    simp only [divOut]
    split_ifs with h
    · dsimp only
      have hdr : d ∣ r := Nat.dvd_of_mod_eq_zero h
      have h1 : 1 ≤ r / d := Nat.div_pos (Nat.le_of_dvd hr hdr) (by omega)
      have h2 : r / d * 2 ≤ r :=
        le_trans (Nat.mul_le_mul_left (r / d) hd) (Nat.div_mul_le_self r d)
      have h3 : Nat.log 2 (r / d) + 1 ≤ Nat.log 2 r := by
        rw [← Nat.log_mul_base (by norm_num) (by omega)]
        exact Nat.log_mono_right h2
      have := ih (r / d) h1
      omega
    · simp

theorem smoothGo_dvd (d r fuel : ℕ) : (smoothGo d r fuel).1 ∣ r := by
  induction fuel generalizing d r with
  | zero => simp [smoothGo]
  | succ fuel ih =>
    simp only [smoothGo]
    exact (ih (d + 1) _).trans (divOut_dvd d r r)

/-- Invariant: no `e ∈ [d, d + fuel)` divides the result. -/
theorem smoothGo_not_dvd (d r fuel : ℕ) (hd : 2 ≤ d) (hr : 1 ≤ r) :
    ∀ e, d ≤ e → e < d + fuel → ¬ e ∣ (smoothGo d r fuel).1 := by
  induction fuel generalizing d r with
  | zero => intro e _ _; omega
  | succ fuel ih =>
    simp only [smoothGo]
    intro e hde helt hdvd
    have hs1 : 1 ≤ (divOut d r r).1 := Nat.pos_of_dvd_of_pos (divOut_dvd d r r) hr
    rcases Nat.eq_or_lt_of_le hde with heq | hlt
    · rw [← heq] at hdvd
      exact divOut_not_dvd d r r hd hr le_rfl
        (hdvd.trans (smoothGo_dvd (d + 1) _ fuel))
    · exact ih (d + 1) _ (by omega) hs1 e hlt (by omega) hdvd

/-- Invariant: every prime factor of `r` either survives or is `< d + fuel`. -/
theorem smoothGo_prime (d r fuel p : ℕ) (hd : 1 ≤ d) (hp : p.Prime) (hpr : p ∣ r) :
    p ∣ (smoothGo d r fuel).1 ∨ p < d + fuel := by
  induction fuel generalizing d r with
  | zero => simpa [smoothGo] using Or.inl hpr
  | succ fuel ih =>
    simp only [smoothGo]
    rcases divOut_prime d r r p hp hpr with hps | hpd
    · rcases ih (d + 1) _ (by omega) hps with h | h
      · exact Or.inl h
      · exact Or.inr (by omega)
    · have : p ≤ d := Nat.le_of_dvd hd hpd
      exact Or.inr (by omega)

theorem smoothGo_cost (d r fuel : ℕ) (hd : 2 ≤ d) :
    (smoothGo d r fuel).2 + Nat.log 2 (smoothGo d r fuel).1 ≤ fuel + Nat.log 2 r := by
  induction fuel generalizing d r with
  | zero => simp [smoothGo]
  | succ fuel ih =>
    simp only [smoothGo]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · have h0 : divOut d 0 0 = (0, 0) := by simp [divOut]
      rw [h0]
      dsimp only
      have := ih (d + 1) 0 (by omega)
      omega
    · have h1 := divOut_cost d r r hd hr
      have h2 := ih (d + 1) (divOut d r r).1 (by omega)
      omega

theorem smoothTD_spec (y k : ℕ) (hk : 1 ≤ k) :
    (Alg.smoothTD y k).1 = true ↔ SmoothUpTo y k := by
  simp only [smoothTD, beq_iff_eq]
  constructor
  · intro h p hp hpk
    rcases smoothGo_prime 2 k (y - 1) p (by omega) hp hpk with h1 | h1
    · rw [h] at h1
      have := Nat.le_of_dvd one_pos h1
      have := hp.two_le
      omega
    · have := hp.two_le
      omega
  · intro h
    by_contra hne
    obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd hne
    have hpk : p ∣ k := hpt.trans (smoothGo_dvd 2 k (y - 1))
    have hpy : p ≤ y := h p hp hpk
    have h2 := hp.two_le
    exact smoothGo_not_dvd 2 k (y - 1) le_rfl hk p h2 (by omega) hpt

theorem smoothTD_cost (y k : ℕ) : (Alg.smoothTD y k).2 ≤ y + Nat.log 2 k + 2 := by
  simp only [smoothTD]
  have := smoothGo_cost 2 k (y - 1) le_rfl
  omega

/-! ### Subset products, coprimality, product -/

theorem mulAll_fst (q : ℕ) (ds : List ℕ) : (mulAll q ds).1 = ds.map (· * q) := by
  induction ds with
  | nil => simp [mulAll]
  | cons d ds ih => simp [mulAll, ih]

theorem mulAll_snd (q : ℕ) (ds : List ℕ) : (mulAll q ds).2 = ds.length := by
  induction ds with
  | nil => simp [mulAll]
  | cons d ds ih => simp [mulAll, ih]

theorem divisorsOf_cons_fst (q : ℕ) (Q : List ℕ) :
    (divisorsOf (q :: Q)).1 = (divisorsOf Q).1 ++ (divisorsOf Q).1.map (· * q) := by
  simp [divisorsOf, mulAll_fst]

theorem divisorsOf_length (Q : List ℕ) : (Alg.divisorsOf Q).1.length = 2 ^ Q.length := by
  induction Q with
  | nil => simp [divisorsOf]
  | cons q Q ih =>
    rw [divisorsOf_cons_fst, List.length_append, List.length_map, ih, List.length_cons,
      pow_succ]
    omega

theorem divisorsOf_cost (Q : List ℕ) : (Alg.divisorsOf Q).2 ≤ 2 ^ Q.length := by
  induction Q with
  | nil => simp [divisorsOf]
  | cons q Q ih =>
    have h : (divisorsOf (q :: Q)).2 = (divisorsOf Q).2 + (divisorsOf Q).1.length := by
      simp [divisorsOf, mulAll_snd]
    rw [h, divisorsOf_length, List.length_cons, pow_succ]
    omega

/-- The divisors of `q * P` for a prime `q`: those of `P` and their
`q`-multiples. -/
theorem divisors_prime_mul (q P : ℕ) (hq : q.Prime) (hP : P ≠ 0) :
    (q * P).divisors = P.divisors ∪ P.divisors.image (· * q) := by
  ext x
  simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hx, -⟩
    obtain ⟨a, b, ha, hb, rfl⟩ := Nat.dvd_mul.mp hx
    rcases hq.eq_one_or_self_of_dvd a ha with rfl | rfl
    · exact Or.inl ⟨by simpa using hb, hP⟩
    · exact Or.inr ⟨b, ⟨hb, hP⟩, mul_comm _ _⟩
  · rintro (⟨hx, -⟩ | ⟨b, ⟨hb, -⟩, rfl⟩)
    · exact ⟨hx.trans (dvd_mul_left _ _), mul_ne_zero hq.ne_zero hP⟩
    · exact ⟨by rw [mul_comm q P]; exact Nat.mul_dvd_mul hb dvd_rfl,
        mul_ne_zero hq.ne_zero hP⟩

theorem divisorsOf_spec (Q : List ℕ) (hQ : Q.Nodup) (hp : ∀ q ∈ Q, q.Prime) :
    (Alg.divisorsOf Q).1.Nodup ∧ (Alg.divisorsOf Q).1.toFinset = (Q.prod).divisors := by
  induction Q with
  | nil => simp [divisorsOf]
  | cons q Q ih =>
    rw [List.nodup_cons] at hQ
    have hq : q.Prime := hp q (List.mem_cons_self ..)
    have hQp : ∀ q ∈ Q, q.Prime := fun q' h => hp q' (List.mem_cons_of_mem _ h)
    obtain ⟨hnd, hfin⟩ := ih hQ.2 hQp
    have hcop : Nat.Coprime q Q.prod := by
      rw [Nat.coprime_list_prod_right_iff]
      intro q' hq'
      rw [Nat.coprime_primes hq (hQp q' hq')]
      rintro rfl
      exact hQ.1 hq'
    have hP0 : Q.prod ≠ 0 := List.prod_ne_zero fun h0 => (hQp 0 h0).ne_zero rfl
    have hmem : ∀ d, d ∈ (divisorsOf Q).1 ↔ d ∣ Q.prod := by
      intro d
      rw [← List.mem_toFinset, hfin, Nat.mem_divisors]
      exact ⟨fun h => h.1, fun h => ⟨h, hP0⟩⟩
    refine ⟨?_, ?_⟩
    · rw [divisorsOf_cons_fst, List.nodup_append]
      refine ⟨hnd, hnd.map (mul_left_injective₀ hq.ne_zero), ?_⟩
      intro a ha b hb hab
      subst hab
      rw [List.mem_map] at hb
      obtain ⟨d, hd, rfl⟩ := hb
      rw [hmem] at ha
      have hqdvd : q ∣ Q.prod := (dvd_mul_left q d).trans ha
      exact hq.one_lt.ne' (hcop.eq_one_of_dvd hqdvd)
    · rw [divisorsOf_cons_fst, List.prod_cons, divisors_prime_mul q Q.prod hq hP0,
        List.toFinset_append, hfin]
      congr 1
      ext x
      simp only [List.mem_toFinset, List.mem_map, Finset.mem_image, Nat.mem_divisors]
      constructor
      · rintro ⟨d, hd, rfl⟩
        exact ⟨d, ⟨(hmem d).mp hd, hP0⟩, rfl⟩
      · rintro ⟨d, ⟨hd, -⟩, rfl⟩
        exact ⟨d, (hmem d).mpr hd, rfl⟩

theorem coprimeTo_fst (Q : List ℕ) (k : ℕ) :
    (coprimeTo Q k).1 = true ↔ ∀ q ∈ Q, ¬ q ∣ k := by
  induction Q with
  | nil => simp [coprimeTo]
  | cons q Q ih =>
    simp only [coprimeTo]
    split_ifs with h
    · simp only [false_iff, not_forall]
      exact ⟨q, List.mem_cons_self .., by simpa using Nat.dvd_of_mod_eq_zero h⟩
    · rw [ih, List.forall_mem_cons]
      constructor
      · intro h' 
        exact ⟨fun hd => h (Nat.mod_eq_zero_of_dvd hd), h'⟩
      · exact fun h' => h'.2

set_option linter.unusedVariables false in
theorem coprimeTo_spec (Q : List ℕ) (hQ : Q.Nodup) (hp : ∀ q ∈ Q, q.Prime) (k : ℕ) :
    (Alg.coprimeTo Q k).1 = true ↔ k.Coprime Q.prod := by
  rw [coprimeTo_fst, Nat.coprime_list_prod_right_iff]
  apply forall_congr'
  intro q
  apply imp_congr_right
  intro hq
  rw [Nat.coprime_comm, (hp q hq).coprime_iff_not_dvd]

theorem coprimeTo_cost (Q : List ℕ) (k : ℕ) : (Alg.coprimeTo Q k).2 ≤ Q.length + 1 := by
  suffices h : (Alg.coprimeTo Q k).2 ≤ Q.length by omega
  induction Q with
  | nil => simp [coprimeTo]
  | cons q Q ih =>
    simp only [coprimeTo, List.length_cons]
    split_ifs
    · omega
    · dsimp only
      omega

theorem prodL_spec (S : List ℕ) : (Alg.prodL S).1 = S.prod := by
  induction S with
  | nil => simp [prodL]
  | cons p S ih => simp [prodL, ih]

theorem prodL_cost (S : List ℕ) : (Alg.prodL S).2 = S.length := by
  induction S with
  | nil => simp [prodL]
  | cons p S ih => simp [prodL, ih]

theorem Lmod_toFinset (Q : List ℕ) (hQ : Q.Nodup) : Lmod Q.toFinset = Q.prod := by
  unfold Lmod
  rw [List.prod_toFinset (fun q => q) hQ, List.map_id']

theorem xceil_toFinset (Q : List ℕ) (hQ : Q.Nodup) : xceil Q.toFinset = Q.prod ^ 5 := by
  unfold xceil
  rw [Lmod_toFinset Q hQ]

/-! ### Step 2: the reservoir -/

/-- Membership in the reservoir loop: exactly the `q' ∈ [q, q + fuel)` above
the floor that pass both tests. -/
theorem resGo_mem (z99 y q fuel x : ℕ) :
    x ∈ (resGo z99 y q fuel).1 ↔
      q ≤ x ∧ x < q + fuel ∧ z99 < x ∧ x.Prime ∧ SmoothUpTo y (x - 1) := by
  induction fuel generalizing q with
  | zero =>
    simp only [resGo, List.not_mem_nil, false_iff]
    rintro ⟨h1, h2, -⟩
    omega
  | succ fuel ih =>
    simp only [resGo]
    have hkeep : ∀ x, (z99 < x ∧ (isPrimeTD x).1 = true ∧ (smoothTD y (x - 1)).1 = true) ↔
        (z99 < x ∧ x.Prime ∧ SmoothUpTo y (x - 1)) := by
      intro x
      rw [isPrimeTD_spec]
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, (smoothTD_spec y (x - 1) (by have := h2.two_le; omega)).mp h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, (smoothTD_spec y (x - 1) (by have := h2.two_le; omega)).mpr h3⟩
    by_cases hq : z99 < q ∧ (isPrimeTD q).1 = true ∧ (smoothTD y (q - 1)).1 = true
    · have hif : (if z99 < q then (isPrimeTD q).1 && (smoothTD y (q - 1)).1 else false) = true := by
        rw [if_pos hq.1, Bool.and_eq_true]
        exact hq.2
      rw [hif, if_pos rfl, List.mem_cons, ih (q + 1)]
      rw [hkeep] at hq
      constructor
      · rintro (rfl | ⟨h1, h2, h3⟩)
        · exact ⟨le_rfl, by omega, hq⟩
        · exact ⟨by omega, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩
        rcases Nat.eq_or_lt_of_le h1 with heq | hlt
        · exact Or.inl heq.symm
        · exact Or.inr ⟨hlt, by omega, h3⟩
    · have hif : (if z99 < q then (isPrimeTD q).1 && (smoothTD y (q - 1)).1 else false) = false := by
        split_ifs with h1
        · by_cases h2 : ((isPrimeTD q).1 && (smoothTD y (q - 1)).1) = true
          · rw [Bool.and_eq_true] at h2
            exact absurd ⟨h1, h2⟩ hq
          · simpa using h2
        · rfl
      rw [hif, if_neg Bool.false_ne_true, ih (q + 1)]
      rw [hkeep] at hq
      constructor
      · rintro ⟨h1, h2, h3⟩
        exact ⟨by omega, by omega, h3⟩
      · rintro ⟨h1, h2, h3⟩
        rcases Nat.eq_or_lt_of_le h1 with heq | hlt
        · subst heq
          exact absurd h3 hq
        · exact ⟨hlt, by omega, h3⟩

theorem resGo_nodup (z99 y q fuel : ℕ) : (resGo z99 y q fuel).1.Nodup := by
  induction fuel generalizing q with
  | zero => simp [resGo]
  | succ fuel ih =>
    simp only [resGo]
    by_cases hk : (if z99 < q then (isPrimeTD q).1 && (smoothTD y (q - 1)).1 else false) = true
    · rw [if_pos hk, List.nodup_cons]
      refine ⟨fun h => ?_, ih (q + 1)⟩
      rw [resGo_mem] at h
      omega
    · rw [if_neg hk]
      exact ih (q + 1)

theorem reservoir_specW (z w y : ℕ) :
    (Alg.reservoir z w y).1.Nodup ∧ (Alg.reservoir z w y).1.toFinset = goodPrimesW z w y := by
  refine ⟨resGo_nodup _ _ _ _, ?_⟩
  ext x
  rw [List.mem_toFinset, reservoir, resGo_mem]
  unfold goodPrimesW
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨by omega, h4, h3, h5⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have := h2.two_le
    exact ⟨by omega, by omega, h3, h2, h4⟩

theorem reservoir_spec (C₁ E : ℝ) (n : ℕ) :
    let sc := scalesOf C₁ E n
    (Alg.reservoir sc.z sc.z99 sc.y).1.Nodup ∧
    (Alg.reservoir sc.z sc.z99 sc.y).1.toFinset = goodPrimesE C₁ n E := by
  intro sc
  simp only [sc, scalesOf]
  refine ⟨(reservoir_specW _ _ _).1, ?_⟩
  rw [(reservoir_specW _ _ _).2]
  ext q
  unfold goodPrimesW goodPrimesE
  simp only [Finset.mem_filter]
  have h0 : (0 : ℝ) ≤ (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [Nat.floor_lt h0]

/-- Cost invariant of the reservoir loop: `fuel` bodies, each charging at
most `√M + y + log₂ M + 4` when every `q'` visited is `≤ M`. -/
theorem resGo_cost (z99 y q fuel M : ℕ) (hM : q + fuel ≤ M + 1) :
    (resGo z99 y q fuel).2 ≤ fuel * (Nat.sqrt M + y + Nat.log 2 M + 4) := by
  induction fuel generalizing q with
  | zero => simp [resGo]
  | succ fuel ih =>
    simp only [resGo]
    have h1 := isPrimeTD_cost q
    have h2 := smoothTD_cost y (q - 1)
    have h3 : Nat.sqrt q ≤ Nat.sqrt M := Nat.sqrt_le_sqrt (by omega)
    have h4 : Nat.log 2 (q - 1) ≤ Nat.log 2 M := Nat.log_mono_right (by omega)
    have h5 := ih (q + 1) (by omega)
    rw [Nat.succ_mul]
    omega

theorem reservoir_cost (z z99 y : ℕ) :
    (Alg.reservoir z z99 y).2 ≤ (z + 1) * (Nat.sqrt z + y + Nat.log 2 z + 6) := by
  rw [reservoir]
  rcases Nat.eq_zero_or_pos z with rfl | hz
  · simp [resGo]
  have h1 : 2 + (z - 1) ≤ z + 1 := by omega
  refine le_trans (resGo_cost z99 y 2 (z - 1) z h1) ?_
  have h2 : z - 1 ≤ z + 1 := by omega
  have h3 : Nat.sqrt z + y + Nat.log 2 z + 4 ≤ Nat.sqrt z + y + Nat.log 2 z + 6 := by omega
  exact Nat.mul_le_mul h2 h3

/-! ### Step 3: the pool and the scan -/

theorem poolGo_mem (x z k : ℕ) (ds : List ℕ) (p : ℕ) :
    p ∈ (poolGo x z k ds).1 ↔
      ∃ d ∈ ds, d * k + 1 = p ∧ p ≤ x ∧ z < p ∧ p.Prime := by
  induction ds with
  | nil => simp [poolGo]
  | cons d ds ih =>
    simp only [poolGo]
    split_ifs with h1 h2
    · rw [List.mem_cons, ih]
      constructor
      · rintro (rfl | ⟨d', hd', h⟩)
        · exact ⟨d, List.mem_cons_self .., rfl, h1.1, h1.2, (isPrimeTD_spec _).mp h2⟩
        · exact ⟨d', List.mem_cons_of_mem _ hd', h⟩
      · rintro ⟨d', hd', h⟩
        rw [List.mem_cons] at hd'
        rcases hd' with rfl | hd'
        · exact Or.inl h.1.symm
        · exact Or.inr ⟨d', hd', h⟩
    · rw [ih]
      constructor
      · rintro ⟨d', hd', h⟩
        exact ⟨d', List.mem_cons_of_mem _ hd', h⟩
      · rintro ⟨d', hd', h⟩
        rw [List.mem_cons] at hd'
        rcases hd' with rfl | hd'
        · rw [h.1] at h2
          exact absurd ((isPrimeTD_spec _).mpr h.2.2.2) h2
        · exact ⟨d', hd', h⟩
    · rw [ih]
      constructor
      · rintro ⟨d', hd', h⟩
        exact ⟨d', List.mem_cons_of_mem _ hd', h⟩
      · rintro ⟨d', hd', h⟩
        rw [List.mem_cons] at hd'
        rcases hd' with rfl | hd'
        · rw [h.1] at h1
          exact absurd ⟨h.2.1, h.2.2.1⟩ h1
        · exact ⟨d', hd', h⟩

theorem poolGo_nodup (x z k : ℕ) (ds : List ℕ) (hds : ds.Nodup) : (poolGo x z k ds).1.Nodup := by
  induction ds with
  | nil => simp [poolGo]
  | cons d ds ih =>
    rw [List.nodup_cons] at hds
    simp only [poolGo]
    split_ifs with h1 h2
    · rw [List.nodup_cons]
      refine ⟨fun h => ?_, ih hds.2⟩
      rw [poolGo_mem] at h
      obtain ⟨d', hd', heq, -, -, hp⟩ := h
      have hk : 0 < k := by
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · rw [mul_zero, zero_add] at hp
          exact absurd hp Nat.not_prime_one
        · exact hk
      have : d' = d := Nat.eq_of_mul_eq_mul_right hk (by omega)
      subst this
      exact hds.1 hd'
    · exact ih hds.2
    · exact ih hds.2

theorem poolAlg_spec (Q : List ℕ) (hQ : Q.Nodup) (hp : ∀ q ∈ Q, q.Prime) (z k : ℕ) :
    (Alg.poolAlg Q (Q.prod ^ 5) z k).1.Nodup ∧
    (Alg.poolAlg Q (Q.prod ^ 5) z k).1.toFinset = pool Q.toFinset z k := by
  obtain ⟨hnd, hfin⟩ := divisorsOf_spec Q hQ hp
  refine ⟨poolGo_nodup _ _ _ _ hnd, ?_⟩
  ext p
  rw [List.mem_toFinset, poolAlg, poolGo_mem, pool, Lmod_toFinset Q hQ, xceil_toFinset Q hQ,
    Finset.mem_image]
  constructor
  · rintro ⟨d, hd, heq, h1, h2, h3⟩
    refine ⟨d, ?_, heq⟩
    rw [Finset.mem_filter, ← hfin, List.mem_toFinset, heq]
    exact ⟨hd, h1, h3, h2⟩
  · rintro ⟨d, hd, heq⟩
    rw [Finset.mem_filter, ← hfin, List.mem_toFinset, heq] at hd
    exact ⟨d, hd.1, heq, hd.2.1, hd.2.2.2, hd.2.2.1⟩

theorem poolGo_cost (x z k : ℕ) (ds : List ℕ) :
    (poolGo x z k ds).2 ≤ ds.length * (Nat.sqrt x + 2) := by
  induction ds with
  | nil => simp [poolGo]
  | cons d ds ih =>
    simp only [poolGo, List.length_cons]
    rw [Nat.succ_mul]
    split_ifs with h1 h2
    · have h3 := isPrimeTD_cost (d * k + 1)
      have h4 : Nat.sqrt (d * k + 1) ≤ Nat.sqrt x := Nat.sqrt_le_sqrt h1.1
      omega
    · have h3 := isPrimeTD_cost (d * k + 1)
      have h4 : Nat.sqrt (d * k + 1) ≤ Nat.sqrt x := Nat.sqrt_le_sqrt h1.1
      omega
    · omega

theorem poolAlg_cost (Q : List ℕ) (x z k : ℕ) :
    (Alg.poolAlg Q x z k).2 ≤ 2 ^ Q.length * (Nat.sqrt x + 3) := by
  simp only [poolAlg]
  have h1 := divisorsOf_cost Q
  have h2 := poolGo_cost x z k (divisorsOf Q).1
  rw [divisorsOf_length] at h2
  have h3 : 2 ^ Q.length * (Nat.sqrt x + 3) = 2 ^ Q.length * (Nat.sqrt x + 2) + 2 ^ Q.length := by
    ring
  omega

/-- The scan started at `k` with fuel reaching a good `k₀ ≥ k` returns the
first good `k' ∈ [k, k₀]`, charging at most `(k' - k + 1)` bodies. -/
theorem scan_go (Q : List ℕ) (x z θ k₀ : ℕ)
    (hgood : (coprimeTo Q k₀).1 = true ∧ θ ≤ (poolAlg Q x z k₀).1.length) :
    ∀ fuel k, k ≤ k₀ → k₀ < k + fuel →
    ∃ k' P, (scan Q x z θ k fuel).1 = some (k', P) ∧ k ≤ k' ∧ k' ≤ k₀ ∧
      (coprimeTo Q k').1 = true ∧ θ ≤ P.length ∧ P = (poolAlg Q x z k').1 ∧
      (scan Q x z θ k fuel).2 ≤ (k' - k + 1) * (Q.length + 2 + 2 ^ Q.length * (Nat.sqrt x + 3)) := by
  intro fuel
  induction fuel with
  | zero => intro k h1 h2; omega
  | succ fuel ih =>
    intro k hk hfuel
    have hc := coprimeTo_cost Q k
    have hpc := poolAlg_cost Q x z k
    simp only [scan]
    split_ifs with h1 h2
    · refine ⟨k, (poolAlg Q x z k).1, rfl, le_rfl, hk, h1, h2, rfl, ?_⟩
      rw [Nat.sub_self, zero_add, one_mul]
      omega
    · have hne : k ≠ k₀ := by
        rintro rfl
        exact h2 hgood.2
      obtain ⟨k', P, hs, hk1, hk2, hcp, hθ, hP, hcost⟩ := ih (k + 1) (by omega) (by omega)
      refine ⟨k', P, hs, by omega, hk2, hcp, hθ, hP, ?_⟩
      have heq : (k' - k + 1) * (Q.length + 2 + 2 ^ Q.length * (Nat.sqrt x + 3)) =
          (k' - (k + 1) + 1) * (Q.length + 2 + 2 ^ Q.length * (Nat.sqrt x + 3)) +
          (Q.length + 2 + 2 ^ Q.length * (Nat.sqrt x + 3)) := by
        rw [← Nat.succ_mul]
        congr 1
        omega
      rw [heq]
      omega
    · have hne : k ≠ k₀ := by
        rintro rfl
        exact h1 hgood.1
      obtain ⟨k', P, hs, hk1, hk2, hcp, hθ, hP, hcost⟩ := ih (k + 1) (by omega) (by omega)
      refine ⟨k', P, hs, by omega, hk2, hcp, hθ, hP, ?_⟩
      have heq : (k' - k + 1) * (Q.length + 2 + 2 ^ Q.length * (Nat.sqrt x + 3)) =
          (k' - (k + 1) + 1) * (Q.length + 2 + 2 ^ Q.length * (Nat.sqrt x + 3)) +
          (Q.length + 2 + 2 ^ Q.length * (Nat.sqrt x + 3)) := by
        rw [← Nat.succ_mul]
        congr 1
        omega
      rw [heq]
      omega

theorem scan_spec (Q : List ℕ) (x z θ k₀ fuel : ℕ) (hk₀ : 1 ≤ k₀) (hfuel : k₀ ≤ fuel)
    (hgood : (Alg.coprimeTo Q k₀).1 = true ∧ θ ≤ (Alg.poolAlg Q x z k₀).1.length) :
    ∃ k P, (Alg.scan Q x z θ 1 fuel).1 = some (k, P) ∧ 1 ≤ k ∧ k ≤ k₀ ∧
      (Alg.coprimeTo Q k).1 = true ∧ θ ≤ P.length ∧ P = (Alg.poolAlg Q x z k).1 ∧
      (Alg.scan Q x z θ 1 fuel).2 ≤ k * (Q.length + 2 + 2 ^ Q.length * (Nat.sqrt x + 3)) := by
  obtain ⟨k, P, hs, hk1, hk2, hcp, hθ, hP, hcost⟩ :=
    scan_go Q x z θ k₀ hgood fuel 1 hk₀ (by omega)
  refine ⟨k, P, hs, hk1, hk2, hcp, hθ, hP, ?_⟩
  have : k - 1 + 1 = k := by omega
  rwa [this] at hcost

/-! ### Step 5: verification -/

theorem notMemTD_fst (p : ℕ) (S : List ℕ) : (notMemTD p S).1 = true ↔ p ∉ S := by
  induction S with
  | nil => simp [notMemTD]
  | cons q S ih =>
    simp only [notMemTD, List.mem_cons, not_or]
    split_ifs with h
    · simp [h]
    · rw [ih]
      exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩

theorem notMemTD_snd (p : ℕ) (S : List ℕ) : (notMemTD p S).2 = S.length := by
  induction S with
  | nil => simp [notMemTD]
  | cons q S ih => simp [notMemTD, ih]

theorem nodupTD_fst (S : List ℕ) : (nodupTD S).1 = true ↔ S.Nodup := by
  induction S with
  | nil => simp [nodupTD]
  | cons p S ih =>
    simp only [nodupTD, Bool.and_eq_true, List.nodup_cons]
    rw [notMemTD_fst, ih]

theorem nodupTD_snd (S : List ℕ) : (nodupTD S).2 ≤ S.length * (S.length + 1) := by
  induction S with
  | nil => simp [nodupTD]
  | cons p S ih =>
    simp only [nodupTD, notMemTD_snd, List.length_cons]
    nlinarith only [ih]

theorem allPrimeTD_fst (S : List ℕ) : (allPrimeTD S).1 = true ↔ ∀ p ∈ S, p.Prime := by
  induction S with
  | nil => simp [allPrimeTD]
  | cons p S ih =>
    simp only [allPrimeTD, Bool.and_eq_true, List.forall_mem_cons]
    rw [isPrimeTD_spec, ih]

theorem allPrimeTD_snd (x : ℕ) (S : List ℕ) (hx : ∀ p ∈ S, p ≤ x) :
    (allPrimeTD S).2 ≤ S.length * (Nat.sqrt x + 2) := by
  induction S with
  | nil => simp [allPrimeTD]
  | cons p S ih =>
    simp only [allPrimeTD, List.length_cons]
    have h1 := isPrimeTD_cost p
    have h2 : Nat.sqrt p ≤ Nat.sqrt x := Nat.sqrt_le_sqrt (hx p (List.mem_cons_self ..))
    have h3 := ih (fun q hq => hx q (List.mem_cons_of_mem _ hq))
    rw [Nat.succ_mul]
    omega

theorem korseltTD_fst (m : ℕ) (S : List ℕ) :
    (korseltTD m S).1 = true ↔ ∀ p ∈ S, (m - 1) % (p - 1) = 0 := by
  induction S with
  | nil => simp [korseltTD]
  | cons p S ih =>
    simp only [korseltTD, List.forall_mem_cons]
    split_ifs with h
    · rw [ih]
      exact ⟨fun h' => ⟨h, h'⟩, fun h' => h'.2⟩
    · simp [h]

theorem korseltTD_snd (m : ℕ) (S : List ℕ) : (korseltTD m S).2 = S.length := by
  induction S with
  | nil => simp [korseltTD]
  | cons p S ih => simp [korseltTD, ih]

theorem verify_spec (m : ℕ) (S : List ℕ) (hS : S.Nodup) (hp : ∀ p ∈ S, p.Prime)
    (h3 : 3 ≤ S.length) (hm : m = S.prod) (hc : IsCarmichael m) :
    (Alg.verify m S).1 = true := by
  simp only [verify]
  rw [if_pos h3, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, nodupTD_fst,
    allPrimeTD_fst, prodL_spec, beq_iff_eq, korseltTD_fst]
  refine ⟨⟨⟨hS, hp⟩, hm.symm⟩, ?_⟩
  intro p hpS
  have hkor := (korselt m hc.1 hc.2.1).mp hc
  apply Nat.mod_eq_zero_of_dvd
  exact hkor.2 p (hp p hpS) (hm ▸ List.dvd_prod hpS)

theorem verify_cost (m x : ℕ) (S : List ℕ) (hx : ∀ p ∈ S, p ≤ x) :
    (Alg.verify m S).2 ≤ S.length * (Nat.sqrt x + S.length + 6) + 4 := by
  simp only [verify]
  have h1 := nodupTD_snd S
  have h2 := allPrimeTD_snd x S hx
  have h3 := prodL_cost S
  have h4 := korseltTD_snd m S
  nlinarith only [h1, h2, h3, h4]

end Carmichael
