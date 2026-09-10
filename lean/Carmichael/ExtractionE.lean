/-
Lemma 4.3 of the paper, generic in the AGP smoothness parameter `E`
(Step 4 always finds a subset, and the pool suffices). Proved from the
van Emde Boas--Kruyswijk theorem (`Carmichael/ZeroSum.lean`) by the
round-by-round extraction argument, exactly as in
`Carmichael/Extraction.lean`, whose `E = 1/3` smoothness arithmetic
(`y = ⌈z^{2/3}⌉`) is here replaced by the generic `y = ⌈z^{1-E}⌉`
estimate `(y+1) log z = O(ℓ₂^{1-E/2}) = o(ℓ₂)`, via
`Carmichael.eventually_log_sq_le_rpow`.
-/
import Carmichael.Defs
import Carmichael.ZeroSum
import Carmichael.LogPow

namespace Carmichael

open Filter Finset

/-! ### Multiset helper: a sub-multiset of a mapped multiset is a mapped
sub-multiset. -/

private lemma exists_le_of_le_map {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β) :
    ∀ (t : Multiset β) (u : Multiset α), t ≤ u.map f → ∃ u' ≤ u, u'.map f = t := by
  intro t
  induction t using Multiset.induction_on with
  | empty => exact fun u _ => ⟨0, Multiset.zero_le u, rfl⟩
  | cons a t ih =>
    intro u h
    have ha : a ∈ u.map f := Multiset.mem_of_le h (Multiset.mem_cons_self a t)
    obtain ⟨b, hb, hfb⟩ := Multiset.mem_map.mp ha
    have ht : t ≤ (u.erase b).map f := by
      have h1 : t ≤ (u.map f).erase a := by
        have := Multiset.erase_le_erase a h
        rwa [Multiset.erase_cons_head] at this
      have h2 : (u.map f).erase a = (u.erase b).map f := by
        conv_lhs => rw [← Multiset.cons_erase hb]
        rw [Multiset.map_cons, hfb, Multiset.erase_cons_head]
      rwa [h2] at h1
    obtain ⟨u', hu', hmap⟩ := ih (u.erase b) ht
    refine ⟨b ::ₘ u', ?_, ?_⟩
    · calc b ::ₘ u' ≤ b ::ₘ u.erase b := Multiset.cons_le_cons b hu'
        _ = u := Multiset.cons_erase hb
    · rw [Multiset.map_cons, hfb, hmap]

/-! ### Pool element facts -/

private lemma pool_mem_facts {Q : Finset ℕ} {z k p : ℕ} (hp : p ∈ pool Q z k) :
    p.Prime ∧ z < p ∧ p ≤ xceil Q := by
  classical
  simp only [pool, Finset.mem_image, Finset.mem_filter] at hp
  obtain ⟨d, ⟨-, h1, h2, h3⟩, rfl⟩ := hp
  exact ⟨h2, h3, h1⟩

/-- A pool element is coprime to the modulus: it is a prime exceeding `z`,
while every prime of `Q` is at most `z`. -/
private lemma pool_coprime {Q : Finset ℕ} {z k p : ℕ}
    (hQ : ∀ q ∈ Q, q ≤ z ∧ q.Prime) (hp : p ∈ pool Q z k) :
    p.Coprime (Lmod Q) := by
  obtain ⟨hpp, hzp, -⟩ := pool_mem_facts hp
  rw [Nat.Prime.coprime_iff_not_dvd hpp]
  intro hdvd
  rw [Lmod] at hdvd
  obtain ⟨q, hq, hpq⟩ := hpp.prime.exists_mem_finset_dvd hdvd
  have := (Nat.prime_dvd_prime_iff_eq hpp (hQ q hq).2).mp hpq
  have hqz := (hQ q hq).1
  omega

/-! ### The exponent of `(ℤ/Lℤ)ˣ` divides `λ(L)` -/

private lemma exponent_dvd_lambda {Q : Finset ℕ} (hQp : ∀ q ∈ Q, q.Prime)
    (hL : 2 ≤ Lmod Q) :
    Monoid.exponent (ZMod (Lmod Q))ˣ ∣ lambdaL Q := by
  classical
  set L := Lmod Q with hLdef
  have : NeZero L := ⟨by omega⟩
  apply Monoid.exponent_dvd_of_forall_pow_eq_one
  intro u
  set a := (u : ZMod L).val with ha
  have hcop : a.Coprime L := ZMod.val_coe_unit_coprime u
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h0 | h
    · exfalso
      rw [h0] at hcop
      have := (Nat.coprime_zero_left L).mp hcop
      omega
    · exact h
  have h1le : 1 ≤ a ^ lambdaL Q := Nat.one_le_pow _ _ (by omega)
  have hdvd : L ∣ a ^ lambdaL Q - 1 := by
    rw [hLdef, Lmod]
    apply Finset.prod_primes_dvd
    · exact fun q hq => (hQp q hq).prime
    · intro q hq
      have : Fact (q.Prime) := ⟨hQp q hq⟩
      have hqL : q ∣ L := hLdef ▸ Finset.dvd_prod_of_mem _ hq
      have hqa : ¬ q ∣ a := by
        intro hd
        have hgcd : q ∣ Nat.gcd a L := Nat.dvd_gcd hd hqL
        rw [Nat.Coprime] at hcop
        rw [hcop] at hgcd
        exact (hQp q hq).one_lt.ne' (Nat.dvd_one.mp hgcd)
      have hane : (a : ZMod q) ≠ 0 := by
        rwa [Ne, ZMod.natCast_eq_zero_iff]
      have hfermat : (a : ZMod q) ^ (q - 1) = 1 := ZMod.pow_card_sub_one_eq_one hane
      obtain ⟨m, hm⟩ : (q - 1) ∣ lambdaL Q := Finset.dvd_lcm hq
      have hpow : (a : ZMod q) ^ lambdaL Q = 1 := by
        rw [hm, pow_mul, hfermat, one_pow]
      have hmod : a ^ lambdaL Q ≡ 1 [MOD q] := by
        rw [← ZMod.natCast_eq_natCast_iff]
        push_cast
        exact hpow
      exact (Nat.modEq_iff_dvd' h1le).mp hmod.symm
  have hmodL : a ^ lambdaL Q ≡ 1 [MOD L] := ((Nat.modEq_iff_dvd' h1le).mpr hdvd).symm
  have hcast : ((a : ℕ) : ZMod L) = (u : ZMod L) := ZMod.natCast_rightInverse (u : ZMod L)
  have hupow : ((u : ZMod L)) ^ lambdaL Q = 1 := by
    calc (u : ZMod L) ^ lambdaL Q = ((a : ℕ) : ZMod L) ^ lambdaL Q := by rw [hcast]
      _ = ((a ^ lambdaL Q : ℕ) : ZMod L) := by push_cast; ring
      _ = ((1 : ℕ) : ZMod L) := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmodL
      _ = 1 := Nat.cast_one
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact hupow

private lemma lambdaL_ne_zero {Q : Finset ℕ} (hQp : ∀ q ∈ Q, q.Prime) :
    lambdaL Q ≠ 0 := by
  classical
  rw [lambdaL, Finset.lcm_ne_zero_iff]
  intro q hq
  have := (hQp q hq).two_le
  omega

/-! ### One extraction round: any `N*` coprime numbers contain a nonempty
subset with product `≡ 1 (mod L)` (van Emde Boas--Kruyswijk). -/

private lemma round_extract {L : ℕ} (hL : 2 ≤ L) {lam : ℕ}
    (hexp : Monoid.exponent (ZMod L)ˣ ∣ lam) (hlam : lam ≠ 0)
    {W : Finset ℕ} (hWcop : ∀ p ∈ W, p.Coprime L)
    (hWcard : (lam : ℝ) * (1 + Real.log L) < (W.card : ℝ)) :
    ∃ S ⊆ W, S.Nonempty ∧ (∏ p ∈ S, p) ≡ 1 [MOD L] := by
  classical
  have : NeZero L := ⟨by omega⟩
  set G := (ZMod L)ˣ with hG
  set f : {x // x ∈ W} → G := fun x => ZMod.unitOfCoprime x.1 (hWcop x.1 x.2) with hf
  set s : Multiset G := W.attach.val.map f with hs
  have hexp_ne : Monoid.exponent G ≠ 0 := by
    intro h0
    rw [h0] at hexp
    exact hlam (Nat.eq_zero_of_zero_dvd hexp)
  have hexp_pos : (0 : ℝ) < (Monoid.exponent G : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hexp_ne
  have hexp_le : Monoid.exponent G ≤ lam := Nat.le_of_dvd (Nat.pos_of_ne_zero hlam) hexp
  have hcard_le : Fintype.card G ≤ L :=
    le_trans (le_of_eq (ZMod.card_units_eq_totient L)) (Nat.totient_le L)
  have hcard_pos : 0 < Fintype.card G := Fintype.card_pos
  have hscard : (s.card : ℝ) = (W.card : ℝ) := by
    rw [hs, Multiset.card_map, Finset.attach_val, Multiset.card_attach]
    rfl
  have hveb : (Monoid.exponent G : ℝ) *
      (1 + Real.log ((Fintype.card G : ℝ) / (Monoid.exponent G : ℝ))) < (s.card : ℝ) := by
    rw [hscard]
    by_cases hc0 : 0 ≤ 1 + Real.log ((Fintype.card G : ℝ) / (Monoid.exponent G : ℝ))
    · have hlog : Real.log ((Fintype.card G : ℝ) / (Monoid.exponent G : ℝ)) ≤ Real.log L := by
        apply Real.log_le_log (by positivity)
        calc (Fintype.card G : ℝ) / (Monoid.exponent G : ℝ) ≤ (Fintype.card G : ℝ) := by
              apply div_le_self (by positivity)
              exact_mod_cast Nat.pos_of_ne_zero hexp_ne
          _ ≤ (L : ℝ) := by exact_mod_cast hcard_le
      calc (Monoid.exponent G : ℝ) *
            (1 + Real.log ((Fintype.card G : ℝ) / (Monoid.exponent G : ℝ)))
          ≤ (lam : ℝ) * (1 + Real.log ((Fintype.card G : ℝ) / (Monoid.exponent G : ℝ))) := by
            apply mul_le_mul_of_nonneg_right _ hc0
            exact_mod_cast hexp_le
        _ ≤ (lam : ℝ) * (1 + Real.log L) := by
            apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ < (W.card : ℝ) := hWcard
    · push Not at hc0
      have hneg : (Monoid.exponent G : ℝ) *
          (1 + Real.log ((Fintype.card G : ℝ) / (Monoid.exponent G : ℝ))) < 0 :=
        mul_neg_of_pos_of_neg hexp_pos hc0
      exact lt_of_lt_of_le hneg (by positivity)
  obtain ⟨t, htle, htne, htprod⟩ := vebk G s hveb
  obtain ⟨u', hu'le, hu'map⟩ := exists_le_of_le_map f t W.attach.val htle
  have hnodup : u'.Nodup := Multiset.nodup_of_le hu'le W.attach.nodup
  set S'' : Finset {x // x ∈ W} := ⟨u', hnodup⟩ with hS''
  set S : Finset ℕ := S''.map (Function.Embedding.subtype _) with hSdef
  have hSsub : S ⊆ W := by
    intro p hp
    rw [hSdef, Finset.mem_map] at hp
    obtain ⟨x, -, rfl⟩ := hp
    exact x.2
  have hprod_units : ∏ x ∈ S'', f x = 1 := by
    rw [Finset.prod_eq_multiset_prod]
    show (u'.map f).prod = 1
    rw [hu'map, htprod]
  have hprod_zmod : ∏ x ∈ S'', ((x.1 : ℕ) : ZMod L) = 1 := by
    have hcoe := congrArg (Units.coeHom (ZMod L)) hprod_units
    rw [map_prod] at hcoe
    simpa [hf, ZMod.coe_unitOfCoprime] using hcoe
  have hprodS : ((∏ p ∈ S, p : ℕ) : ZMod L) = 1 := by
    push_cast
    rw [hSdef, Finset.prod_map]
    simpa using hprod_zmod
  have hSne : S.Nonempty := by
    obtain ⟨g, hg⟩ := Multiset.exists_mem_of_ne_zero htne
    rw [← hu'map, Multiset.mem_map] at hg
    obtain ⟨x, hx, -⟩ := hg
    exact ⟨x.1, Finset.mem_map_of_mem _ hx⟩
  refine ⟨S, hSsub, hSne, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_one]
  exact hprodS

/-! ### The greedy round-by-round extraction -/

/-- The greedy loop: after `r` rounds we have a subset `S` of the pool with
`∏ S ≡ 1 (mod L)` using at most `r · N*` pool elements; either the product is
still at most `n` (and then it is at least `(L+1)^r`), or it has crossed `n`
(and then it is at most `n · x^{N*}`). -/
private lemma greedy_rounds {n L Nst x : ℕ} {P : Finset ℕ}
    (hn : 1 ≤ n) (_hL : 2 ≤ L) (hx : 1 ≤ x)
    (hPtwo : ∀ p ∈ P, 2 ≤ p) (hPle : ∀ p ∈ P, p ≤ x)
    (hextract : ∀ W ⊆ P, W.card = Nst →
      ∃ S ⊆ W, S.Nonempty ∧ (∏ p ∈ S, p) ≡ 1 [MOD L]) :
    ∀ r : ℕ, r * Nst ≤ P.card →
    ∃ S ⊆ P, S.card ≤ r * Nst ∧ (∏ p ∈ S, p) ≡ 1 [MOD L] ∧
      (((L + 1) ^ r ≤ ∏ p ∈ S, p ∧ ∏ p ∈ S, p ≤ n) ∨
       (n < ∏ p ∈ S, p ∧ ∏ p ∈ S, p ≤ n * x ^ Nst)) := by
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨∅, Finset.empty_subset _, by simp, ?_, ?_⟩
    · simp only [Finset.prod_empty]
      rfl
    · left
      simp [hn]
  | succ r ih =>
    intro hr
    have hr' : r * Nst ≤ P.card :=
      le_trans (Nat.mul_le_mul_right Nst (Nat.le_succ r)) hr
    obtain ⟨S, hSP, hScard, hSmod, hSdisj⟩ := ih hr'
    rcases hSdisj with ⟨hlow, hup⟩ | hdone
    · -- extract another round from the unused part of the pool
      have hcard_sdiff : Nst ≤ (P \ S).card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hSP]
        have h1 : (r + 1) * Nst = r * Nst + Nst := by ring
        have h2 : S.card ≤ P.card := Finset.card_le_card hSP
        omega
      obtain ⟨W, hWsub, hWcard⟩ := Finset.exists_subset_card_eq hcard_sdiff
      have hWP : W ⊆ P := hWsub.trans Finset.sdiff_subset
      obtain ⟨S', hS'W, hS'ne, hS'mod⟩ := hextract W hWP hWcard
      have hS'P : S' ⊆ P := hS'W.trans hWP
      have hdisj : Disjoint S S' := by
        rw [Finset.disjoint_right]
        intro p hp
        have hmem := hWsub (hS'W hp)
        rw [Finset.mem_sdiff] at hmem
        exact hmem.2
      have hprod_union : ∏ p ∈ S ∪ S', p = (∏ p ∈ S, p) * ∏ p ∈ S', p :=
        Finset.prod_union hdisj
      have hS'two : ∀ p ∈ S', 2 ≤ p := fun p hp => hPtwo p (hS'P hp)
      obtain ⟨p₀, hp₀⟩ := hS'ne
      have hS'prod_ge2 : 2 ≤ ∏ p ∈ S', p := by
        have h1 : p₀ ≤ ∏ p ∈ S', p :=
          Finset.single_le_prod' (f := fun p => p)
            (fun p hp => by have := hS'two p hp; omega) hp₀
        have := hS'two p₀ hp₀
        omega
      have hS'ge : L + 1 ≤ ∏ p ∈ S', p := by
        have h1 : 1 ≡ (∏ p ∈ S', p) [MOD L] := hS'mod.symm
        have hdvd : L ∣ (∏ p ∈ S', p) - 1 := (Nat.modEq_iff_dvd' (by omega)).mp h1
        have := Nat.le_of_dvd (by omega) hdvd
        omega
      have hS'cardle : S'.card ≤ Nst := hWcard ▸ Finset.card_le_card hS'W
      refine ⟨S ∪ S', Finset.union_subset hSP hS'P, ?_, ?_, ?_⟩
      · calc (S ∪ S').card ≤ S.card + S'.card := Finset.card_union_le _ _
          _ ≤ r * Nst + Nst := by omega
          _ = (r + 1) * Nst := by ring
      · rw [hprod_union]
        have := hSmod.mul hS'mod
        simpa using this
      · by_cases hcross : (∏ p ∈ S, p) * ∏ p ∈ S', p ≤ n
        · left
          rw [hprod_union]
          refine ⟨?_, hcross⟩
          calc (L + 1) ^ (r + 1) = (L + 1) ^ r * (L + 1) := by ring
            _ ≤ (∏ p ∈ S, p) * ∏ p ∈ S', p := Nat.mul_le_mul hlow hS'ge
        · right
          rw [hprod_union]
          push Not at hcross
          refine ⟨hcross, ?_⟩
          have hS'le : ∏ p ∈ S', p ≤ x ^ Nst := by
            calc ∏ p ∈ S', p ≤ x ^ S'.card :=
                Finset.prod_le_pow_card _ _ _ (fun p hp => hPle p (hS'P hp))
              _ ≤ x ^ Nst := Nat.pow_le_pow_right (by omega) hS'cardle
          exact Nat.mul_le_mul hup hS'le
    · exact ⟨S, hSP,
        le_trans hScard (Nat.mul_le_mul_right Nst (Nat.le_succ r)), hSmod, Or.inr hdone⟩

/-! ### Size bounds: `λ(L)`, `log L`, `N*` -/

/-- Smoothness bound: since each `q - 1` is `y`-smooth and at most `z`, the
lcm `λ(L)` divides `∏_{p ≤ y} p^{⌊log_p z⌋}`, which is at most `z^{y+1}`.
(Stated for a generic `y`; below it is applied with `y = yscaleE C₁ n E`.) -/
private lemma lambdaL_le_pow {Q : Finset ℕ} {y z : ℕ} (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, q.Prime ∧ q ≤ z ∧ SmoothUpTo y (q - 1)) :
    lambdaL Q ≤ z ^ (y + 1) := by
  classical
  set M : ℕ := ∏ p ∈ (Finset.range (y + 1)).filter Nat.Prime, p ^ (Nat.log p z) with hM
  have hMpos : 0 < M := Finset.prod_pos fun p hp =>
    pow_pos (Finset.mem_filter.mp hp).2.pos _
  have hdvd : lambdaL Q ∣ M := by
    rw [lambdaL]
    apply Finset.lcm_dvd
    intro q hq
    obtain ⟨hqp, hqz, hsm⟩ := hQ q hq
    have hq1 : q - 1 ≠ 0 := by have := hqp.two_le; omega
    have hfact : ∏ p ∈ (q - 1).primeFactors, p ^ ((q - 1).factorization p) = q - 1 := by
      rw [← Nat.prod_factorization_eq_prod_primeFactors]
      exact Nat.prod_factorization_pow_eq_self hq1
    have hsub : (q - 1).primeFactors ⊆ (Finset.range (y + 1)).filter Nat.Prime := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      obtain ⟨hpp, hpdvd, -⟩ := hp
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le (hsm p hpp hpdvd), hpp⟩
    have hstep : (∏ p ∈ (q - 1).primeFactors, p ^ ((q - 1).factorization p)) ∣
        ∏ p ∈ (q - 1).primeFactors, p ^ (Nat.log p z) := by
      apply Finset.prod_dvd_prod_of_dvd
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      obtain ⟨hpp, hpdvd, -⟩ := hp
      apply pow_dvd_pow
      have hple : p ^ ((q - 1).factorization p) ≤ z :=
        le_trans (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd (q - 1) p)) (by omega)
      exact (Nat.le_log_iff_pow_le hpp.one_lt (by omega)).mpr hple
    rw [← hfact, hM]
    exact hstep.trans (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
  have hMle : M ≤ z ^ (y + 1) := by
    calc M ≤ z ^ ((Finset.range (y + 1)).filter Nat.Prime).card :=
        Finset.prod_le_pow_card _ _ _ (fun p _ => Nat.pow_log_le_self p (by omega))
      _ ≤ z ^ (y + 1) := Nat.pow_le_pow_right hz
          (le_trans (Finset.card_filter_le _ _) (by simp))
  exact le_trans (Nat.le_of_dvd hMpos hdvd) hMle

/-- Lower bound on `log L`: the primes of `Q` all exceed `√z`. -/
private lemma log_Lmod_ge {Q : Finset ℕ} {z : ℕ} (hz : 1 ≤ z)
    (hQ : ∀ q ∈ Q, Real.sqrt z < (q : ℝ)) :
    (Q.card : ℝ) * (Real.log z / 2) ≤ Real.log (Lmod Q) := by
  have hsqrt_pos : 0 < Real.sqrt z := Real.sqrt_pos.mpr (by exact_mod_cast hz)
  have hprod : (Real.sqrt z) ^ Q.card ≤ (Lmod Q : ℝ) := by
    rw [Lmod, Nat.cast_prod]
    calc (Real.sqrt z) ^ Q.card = ∏ _q ∈ Q, Real.sqrt z := (Finset.prod_const _).symm
      _ ≤ ∏ q ∈ Q, (q : ℝ) :=
        Finset.prod_le_prod (fun q _ => le_of_lt hsqrt_pos) (fun q hq => le_of_lt (hQ q hq))
  calc (Q.card : ℝ) * (Real.log z / 2) = (Q.card : ℝ) * Real.log (Real.sqrt z) := by
        rw [Real.log_sqrt (by positivity)]
    _ = Real.log ((Real.sqrt z) ^ Q.card) := (Real.log_pow _ _).symm
    _ ≤ Real.log (Lmod Q) := Real.log_le_log (by positivity) hprod

/-- Upper bound on `log L`: the primes of `Q` are all at most `z`. -/
private lemma log_Lmod_le {Q : Finset ℕ} {z : ℕ}
    (hQ : ∀ q ∈ Q, q ≤ z) (hQ1 : ∀ q ∈ Q, 1 ≤ q) :
    Real.log (Lmod Q) ≤ (Q.card : ℝ) * Real.log z := by
  have hL1 : 1 ≤ Lmod Q := by
    rw [Lmod]
    exact Finset.one_le_prod' hQ1
  have hle : Lmod Q ≤ z ^ Q.card := by
    rw [Lmod]
    exact Finset.prod_le_pow_card _ _ _ hQ
  calc Real.log (Lmod Q) ≤ Real.log ((z : ℝ) ^ Q.card) := by
        apply Real.log_le_log (by exact_mod_cast hL1)
        exact_mod_cast hle
    _ = (Q.card : ℝ) * Real.log z := Real.log_pow _ _

/-- `N* ≤ λ(L)(1 + log L) + 2`. -/
private lemma Nstar_le (Q : Finset ℕ) :
    (Nstar Q : ℝ) ≤ (lambdaL Q : ℝ) * (1 + Real.log (Lmod Q)) + 2 := by
  have hnn : 0 ≤ (lambdaL Q : ℝ) * (1 + Real.log (Lmod Q)) := by
    apply mul_nonneg (by positivity)
    have := Real.log_natCast_nonneg (Lmod Q)
    linarith
  have h := Nat.ceil_lt_add_one hnn
  rw [Nstar]
  push_cast
  linarith

/-- `λ(L)(1 + log L) < N*`. -/
private lemma lt_Nstar (Q : Finset ℕ) :
    (lambdaL Q : ℝ) * (1 + Real.log (Lmod Q)) < (Nstar Q : ℝ) := by
  have h := Nat.le_ceil ((lambdaL Q : ℝ) * (1 + Real.log (Lmod Q)))
  rw [Nstar]
  push_cast
  linarith

/-- Round-count bound: `Nat.log (L+1) n ≤ log n / c` whenever `c ≤ log (L+1)`. -/
private lemma natLog_le_div {L n : ℕ} (hn : 1 ≤ n) {c : ℝ} (hc : 0 < c)
    (hcL : c ≤ Real.log ((L : ℝ) + 1)) :
    (Nat.log (L + 1) n : ℝ) ≤ Real.log n / c := by
  have hpow : (L + 1) ^ Nat.log (L + 1) n ≤ n := Nat.pow_log_le_self (L + 1) (by omega)
  have hpowR : ((L : ℝ) + 1) ^ Nat.log (L + 1) n ≤ (n : ℝ) := by exact_mod_cast hpow
  have hlog : (Nat.log (L + 1) n : ℝ) * Real.log ((L : ℝ) + 1) ≤ Real.log n := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by positivity) hpowR
  rw [le_div_iff₀ hc]
  calc (Nat.log (L + 1) n : ℝ) * c ≤ (Nat.log (L + 1) n : ℝ) * Real.log ((L : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hcL (by positivity)
    _ ≤ Real.log n := hlog

/-! ### Eventual analytic bounds -/

private lemma tendsto_ell2_atTop : Tendsto (fun n : ℕ => ell2 n) atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private lemma tendsto_ell3_atTop : Tendsto (fun n : ℕ => ell3 n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_ell2_atTop

private lemma eventually_sq_le_exp :
    ∀ᶠ x : ℝ in atTop, 13 * x ^ 2 ≤ Real.exp (0.03 * x) := by
  filter_upwards [eventually_ge_atTop (10 ^ 8 : ℝ)] with x hx
  have hx0 : (0:ℝ) ≤ x := by linarith
  have h1 : 0.01 * x + 1 ≤ Real.exp (0.01 * x) := by
    have := Real.add_one_le_exp (0.01 * x)
    linarith
  have hsplit : Real.exp (0.03 * x) =
      Real.exp (0.01 * x) * Real.exp (0.01 * x) * Real.exp (0.01 * x) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h0 : (0:ℝ) ≤ 0.01 * x + 1 := by linarith
  have h2 : (0.01 * x + 1) * (0.01 * x + 1) ≤ Real.exp (0.01 * x) * Real.exp (0.01 * x) :=
    mul_le_mul h1 h1 h0 (le_trans h0 h1)
  have h3 : (0.01 * x + 1) * (0.01 * x + 1) * (0.01 * x + 1) ≤
      Real.exp (0.01 * x) * Real.exp (0.01 * x) * Real.exp (0.01 * x) :=
    mul_le_mul h2 h1 h0 (mul_nonneg (le_trans h0 h1) (le_trans h0 h1))
  rw [hsplit]
  nlinarith [h3, mul_le_mul_of_nonneg_right hx (sq_nonneg x)]

set_option maxHeartbeats 1000000 in
/-- The core asymptotic comparison, generic in `E`: the number of pool
elements consumed by the greedy loop, bounded via the smoothness estimate
for `λ(L)` and the round-count estimate, is eventually below
`(log n)^{1.2} = e^{1.2 ℓ₂}`. The key point replacing the `E = 1/3`
arithmetic of `Extraction.lean` is
`(y_E + 1) log z ≤ 6 C₁ ℓ₂^{1-E} ℓ₃² + 6 ℓ₃ ≤ 0.01 ℓ₂` eventually, from
`ℓ₃² ≤ ℓ₂^{E/4}` (`eventually_log_sq_le_rpow`). -/
private lemma star_boundE (C₁ E : ℝ) (hE : 0 < E) (hE2 : E ≤ 1 / 2)
    (h1000 : (1000 : ℝ) ≤ C₁) :
    ∀ᶠ n : ℕ in atTop,
      (Real.exp (ell2 n) / (1.5 * ell2 n * ell3 n) + 1) *
          ((zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) *
            (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n)) + 2)
        ≤ Real.exp (1.2 * ell2 n) := by
  have hE4 : (0:ℝ) < E / 4 := by linarith
  have h3E4 : (0:ℝ) < 3 * E / 4 := by linarith
  have h1E4 : (0:ℝ) < 1 - E / 4 := by linarith
  filter_upwards [tendsto_ell2_atTop.eventually_ge_atTop 50,
    tendsto_ell3_atTop.eventually_ge_atTop 1,
    tendsto_ell3_atTop.eventually_ge_atTop (Real.log (2 * C₁)),
    tendsto_ell2_atTop.eventually (eventually_log_sq_le_rpow hE4),
    ((tendsto_rpow_atTop h3E4).comp
      tendsto_ell2_atTop).eventually_ge_atTop (1200 * C₁),
    ((tendsto_rpow_atTop h1E4).comp
      tendsto_ell2_atTop).eventually_ge_atTop 1200,
    tendsto_ell2_atTop.eventually eventually_sq_le_exp] with n ha50 hb1 hbC hbsq' h34' h14' hsq'
  set a := ell2 n with hadef
  set b := ell3 n with hbdef
  have hba : b = Real.log a := rfl
  have hbsq : b ^ 2 ≤ a ^ (E / 4) := by rw [hba]; exact hbsq'
  have h34 : 1200 * C₁ ≤ a ^ (3 * E / 4) := h34'
  have h14 : (1200:ℝ) ≤ a ^ (1 - E / 4) := h14'
  have hsq : 13 * a ^ 2 ≤ Real.exp (0.03 * a) := hsq'
  have hzdef : zscale C₁ n = ⌈C₁ * a * b⌉₊ := rfl
  have hTdef : Tscale n = ⌈(3:ℝ) * a⌉₊ := rfl
  have hydef : yscaleE C₁ n E = ⌈(zscale C₁ n : ℝ) ^ ((1:ℝ) - E)⌉₊ := rfl
  clear_value a b
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have ha1 : (1:ℝ) ≤ a := by linarith
  -- z bounds
  have hCa : (1000:ℝ) * 50 ≤ C₁ * a := mul_le_mul h1000 ha50 (by norm_num) (by linarith)
  have hCab : (1000:ℝ) * 50 * 1 ≤ C₁ * a * b :=
    mul_le_mul hCa hb1 (by norm_num) (le_trans (by norm_num) hCa)
  have hzlow : C₁ * a * b ≤ (zscale C₁ n : ℝ) := by
    rw [hzdef]
    exact Nat.le_ceil _
  have hzpos : (0:ℝ) < (zscale C₁ n : ℝ) := lt_of_lt_of_le (by linarith) hzlow
  have hzup : (zscale C₁ n : ℝ) ≤ 2 * (C₁ * a * b) := by
    rw [hzdef]
    have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ C₁ * a * b by linarith)
    linarith
  -- log z bounds
  have hCb : (1000:ℝ) * 1 ≤ C₁ * b := mul_le_mul h1000 hb1 (by norm_num) (by linarith)
  have ha_le_Cab : a ≤ C₁ * a * b := by nlinarith [hCb, ha0]
  have hlogz_low : b ≤ Real.log (zscale C₁ n : ℝ) := by
    rw [hba]
    exact Real.log_le_log ha0 (le_trans ha_le_Cab hzlow)
  have hlogz_pos : 0 < Real.log (zscale C₁ n : ℝ) := lt_of_lt_of_le hb0 hlogz_low
  have hlogz_up : Real.log (zscale C₁ n : ℝ) ≤ 3 * b := by
    calc Real.log (zscale C₁ n : ℝ) ≤ Real.log (2 * C₁ * (a * b)) := by
          apply Real.log_le_log hzpos
          calc (zscale C₁ n : ℝ) ≤ 2 * (C₁ * a * b) := hzup
            _ = 2 * C₁ * (a * b) := by ring
      _ = Real.log (2 * C₁) + (Real.log a + Real.log b) := by
          rw [Real.log_mul (ne_of_gt (show (0:ℝ) < 2 * C₁ by linarith))
              (ne_of_gt (mul_pos ha0 hb0)),
            Real.log_mul (ne_of_gt ha0) (ne_of_gt hb0)]
      _ ≤ b + (b + b) := by
          have h2 : Real.log a = b := hba.symm
          have hlogb : Real.log b ≤ b := by
            have := Real.log_le_sub_one_of_pos hb0
            linarith
          linarith
      _ = 3 * b := by ring
  -- T bounds
  have hT_low : 3 * a ≤ (Tscale n : ℝ) := by
    rw [hTdef]
    exact Nat.le_ceil _
  have hT_up : (Tscale n : ℝ) ≤ 4 * a := by
    rw [hTdef]
    have h := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 3 * a by linarith)
    linarith
  -- y bound
  have hy_up : (yscaleE C₁ n E : ℝ) ≤ (zscale C₁ n : ℝ) ^ ((1:ℝ) - E) + 1 := by
    rw [hydef]
    exact (Nat.ceil_lt_add_one (Real.rpow_nonneg hzpos.le _)).le
  -- z^{1-E} ≤ 2C₁ · a^{1-E} · b
  have hz1E : (zscale C₁ n : ℝ) ^ ((1:ℝ) - E) ≤ 2 * C₁ * (a ^ ((1:ℝ) - E) * b) := by
    have hz2 : (zscale C₁ n : ℝ) ≤ 2 * C₁ * (a * b) := by linarith
    have hb1E : b ^ ((1:ℝ) - E) ≤ b := by
      calc b ^ ((1:ℝ) - E) ≤ b ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
        _ = b := Real.rpow_one b
    have hC1E : (2 * C₁) ^ ((1:ℝ) - E) ≤ 2 * C₁ := by
      calc (2 * C₁) ^ ((1:ℝ) - E) ≤ (2 * C₁) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 2 * C₁ := Real.rpow_one _
    calc (zscale C₁ n : ℝ) ^ ((1:ℝ) - E)
        ≤ (2 * C₁ * (a * b)) ^ ((1:ℝ) - E) :=
          Real.rpow_le_rpow hzpos.le hz2 (by linarith)
      _ = (2 * C₁) ^ ((1:ℝ) - E) * (a ^ ((1:ℝ) - E) * b ^ ((1:ℝ) - E)) := by
          rw [Real.mul_rpow (by linarith) (mul_nonneg ha0.le hb0.le),
            Real.mul_rpow ha0.le hb0.le]
      _ ≤ 2 * C₁ * (a ^ ((1:ℝ) - E) * b) := by
          have h1 : a ^ ((1:ℝ) - E) * b ^ ((1:ℝ) - E) ≤ a ^ ((1:ℝ) - E) * b :=
            mul_le_mul_of_nonneg_left hb1E (Real.rpow_nonneg ha0.le _)
          have h2 : (0:ℝ) ≤ a ^ ((1:ℝ) - E) * b :=
            mul_nonneg (Real.rpow_nonneg ha0.le _) hb0.le
          have h3 : (0:ℝ) ≤ (2 * C₁) ^ ((1:ℝ) - E) := Real.rpow_nonneg (by linarith) _
          calc (2 * C₁) ^ ((1:ℝ) - E) * (a ^ ((1:ℝ) - E) * b ^ ((1:ℝ) - E))
              ≤ (2 * C₁) ^ ((1:ℝ) - E) * (a ^ ((1:ℝ) - E) * b) :=
                mul_le_mul_of_nonneg_left h1 h3
            _ ≤ 2 * C₁ * (a ^ ((1:ℝ) - E) * b) :=
                mul_le_mul_of_nonneg_right hC1E h2
  -- rpow splitting identities
  have hsum1 : a ^ ((1:ℝ) - E) * a ^ (E / 4) = a ^ (1 - 3 * E / 4) := by
    rw [← Real.rpow_add ha0]
    congr 1
    ring
  have hsplit1 : a ^ (3 * E / 4) * a ^ (1 - 3 * E / 4) = a := by
    rw [← Real.rpow_add ha0,
      show 3 * E / 4 + (1 - 3 * E / 4) = (1:ℝ) by ring, Real.rpow_one]
  have hsplit2 : a ^ (1 - E / 4) * a ^ (E / 4) = a := by
    rw [← Real.rpow_add ha0,
      show 1 - E / 4 + E / 4 = (1:ℝ) by ring, Real.rpow_one]
  -- key bound: (y_E + 1) log z ≤ 0.01 a
  have hb2 : b ≤ b ^ 2 := by nlinarith
  have hterm1 : 6 * C₁ * (a ^ ((1:ℝ) - E) * b ^ 2) ≤ 0.005 * a := by
    have ht1 : a ^ ((1:ℝ) - E) * b ^ 2 ≤ a ^ ((1:ℝ) - E) * a ^ (E / 4) :=
      mul_le_mul_of_nonneg_left hbsq (Real.rpow_nonneg ha0.le _)
    have h6C : 6 * C₁ ≤ 0.005 * a ^ (3 * E / 4) := by linarith
    calc 6 * C₁ * (a ^ ((1:ℝ) - E) * b ^ 2)
        ≤ 6 * C₁ * (a ^ ((1:ℝ) - E) * a ^ (E / 4)) :=
          mul_le_mul_of_nonneg_left ht1 (by linarith)
      _ = 6 * C₁ * a ^ (1 - 3 * E / 4) := by rw [hsum1]
      _ ≤ (0.005 * a ^ (3 * E / 4)) * a ^ (1 - 3 * E / 4) :=
          mul_le_mul_of_nonneg_right h6C (Real.rpow_nonneg ha0.le _)
      _ = 0.005 * a := by rw [mul_assoc, hsplit1]
  have hterm2 : 6 * b ≤ 0.005 * a := by
    have hbE : b ≤ a ^ (E / 4) := le_trans hb2 hbsq
    have h6 : (6:ℝ) ≤ 0.005 * a ^ (1 - E / 4) := by linarith
    calc 6 * b ≤ 6 * a ^ (E / 4) := by linarith
      _ ≤ (0.005 * a ^ (1 - E / 4)) * a ^ (E / 4) :=
          mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg ha0.le _)
      _ = 0.005 * a := by rw [mul_assoc, hsplit2]
  have hkey : ((yscaleE C₁ n E : ℝ) + 1) * Real.log (zscale C₁ n : ℝ) ≤ 0.01 * a := by
    have h1 : (yscaleE C₁ n E : ℝ) + 1 ≤ 2 * C₁ * (a ^ ((1:ℝ) - E) * b) + 2 := by
      linarith
    have hnnB : (0:ℝ) ≤ 2 * C₁ * (a ^ ((1:ℝ) - E) * b) + 2 := by
      have h : (0:ℝ) ≤ 2 * C₁ * (a ^ ((1:ℝ) - E) * b) :=
        mul_nonneg (show (0:ℝ) ≤ 2 * C₁ by linarith)
          (mul_nonneg (Real.rpow_nonneg ha0.le ((1:ℝ) - E)) hb0.le)
      linarith
    have h2 : ((yscaleE C₁ n E : ℝ) + 1) * Real.log (zscale C₁ n : ℝ) ≤
        (2 * C₁ * (a ^ ((1:ℝ) - E) * b) + 2) * (3 * b) :=
      mul_le_mul h1 hlogz_up hlogz_pos.le hnnB
    have hexpand : (2 * C₁ * (a ^ ((1:ℝ) - E) * b) + 2) * (3 * b) =
        6 * C₁ * (a ^ ((1:ℝ) - E) * b ^ 2) + 6 * b := by ring
    calc ((yscaleE C₁ n E : ℝ) + 1) * Real.log (zscale C₁ n : ℝ)
        ≤ (2 * C₁ * (a ^ ((1:ℝ) - E) * b) + 2) * (3 * b) := h2
      _ = 6 * C₁ * (a ^ ((1:ℝ) - E) * b ^ 2) + 6 * b := hexpand
      _ ≤ 0.005 * a + 0.005 * a := by linarith
      _ = 0.01 * a := by ring
  -- second factor bound
  have hb_le_a : b ≤ a := by
    rw [hba]
    have := Real.log_le_sub_one_of_pos ha0
    linarith
  have hTlogz : (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ) ≤ 4 * a * (3 * b) :=
    mul_le_mul hT_up hlogz_up hlogz_pos.le (by linarith)
  have hone_plus : 1 + (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ) ≤ 13 * a ^ 2 := by
    nlinarith [hTlogz, mul_le_mul_of_nonneg_left hb_le_a ha0.le, ha50]
  have hfac_nn : (0:ℝ) ≤ 1 + (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ) := by
    have := mul_nonneg (Nat.cast_nonneg (Tscale n) : (0:ℝ) ≤ (Tscale n : ℝ)) hlogz_pos.le
    linarith
  have hzy_exp : (zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) =
      Real.exp (((yscaleE C₁ n E + 1 : ℕ) : ℝ) * Real.log (zscale C₁ n : ℝ)) := by
    rw [← Real.rpow_natCast (zscale C₁ n : ℝ) (yscaleE C₁ n E + 1),
      Real.rpow_def_of_pos hzpos, mul_comm]
  have hzy_le : (zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) ≤ Real.exp (0.01 * a) := by
    rw [hzy_exp]
    apply Real.exp_le_exp.mpr
    push_cast
    exact hkey
  have hP2 : (zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) *
      (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ)) + 2 ≤ Real.exp (0.1 * a) := by
    have hfac_le : 1 + (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ) ≤ Real.exp (0.03 * a) :=
      le_trans hone_plus hsq
    have hmul : (zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) *
        (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ)) ≤
        Real.exp (0.01 * a) * Real.exp (0.03 * a) :=
      mul_le_mul hzy_le hfac_le hfac_nn (Real.exp_nonneg _)
    have hexp_sum : Real.exp (0.01 * a) * Real.exp (0.03 * a) = Real.exp (0.04 * a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp_sum] at hmul
    have h6 : Real.exp (0.1 * a) = Real.exp (0.04 * a) * Real.exp (0.06 * a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h7 : (4:ℝ) ≤ Real.exp (0.06 * a) := by
      have := Real.add_one_le_exp (0.06 * a)
      linarith
    have h8 : (1:ℝ) ≤ Real.exp (0.04 * a) := Real.one_le_exp (by linarith)
    have h9 : Real.exp (0.04 * a) * 4 ≤ Real.exp (0.04 * a) * Real.exp (0.06 * a) :=
      mul_le_mul_of_nonneg_left h7 (Real.exp_nonneg _)
    rw [h6]
    linarith
  -- first factor bound
  have hab50 : (50:ℝ) * 1 ≤ a * b := mul_le_mul ha50 hb1 zero_le_one (by linarith)
  have hP1 : Real.exp a / (1.5 * a * b) + 1 ≤ Real.exp (1.1 * a) := by
    have hd1 : (1:ℝ) ≤ 1.5 * a * b := by nlinarith [hab50]
    have hdiv : Real.exp a / (1.5 * a * b) ≤ Real.exp a :=
      div_le_self (Real.exp_nonneg a) hd1
    have hsplit : Real.exp (1.1 * a) = Real.exp (0.1 * a) * Real.exp a := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h2 : (2:ℝ) ≤ Real.exp (0.1 * a) := by
      have := Real.add_one_le_exp (0.1 * a)
      linarith
    have h1e : (1:ℝ) ≤ Real.exp a := Real.one_le_exp (by linarith)
    have h9 : 2 * Real.exp a ≤ Real.exp (0.1 * a) * Real.exp a :=
      mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg a)
    rw [hsplit]
    linarith
  -- combine
  have hP1nn : (0:ℝ) ≤ Real.exp a / (1.5 * a * b) + 1 := by
    have h1 : (0:ℝ) ≤ 1.5 * a * b := by nlinarith [hab50]
    have := div_nonneg (Real.exp_nonneg a) h1
    linarith
  have hP2nn : (0:ℝ) ≤ (zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) *
      (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ)) + 2 := by
    have := mul_nonneg (pow_nonneg hzpos.le (yscaleE C₁ n E + 1)) hfac_nn
    linarith
  calc (Real.exp a / (1.5 * a * b) + 1) *
      ((zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) *
        (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n : ℝ)) + 2)
      ≤ Real.exp (1.1 * a) * Real.exp (0.1 * a) :=
        mul_le_mul hP1 hP2 hP2nn (Real.exp_nonneg _)
    _ = Real.exp (1.2 * a) := by
        rw [← Real.exp_add]
        congr 1
        ring

set_option maxHeartbeats 800000 in
/-- Lemma 4.3 generic in the AGP smoothness parameter `E ∈ (0, 1/2]`
(Step 4 always finds a subset, and the pool suffices): from a pool of
`(log n)^{1.2}` primes one can extract a subset `S` whose product is
`≡ 1 (mod L)` and lands in `(n, n · x^{N*}]`. -/
theorem extractionE (C₁ E : ℝ) (hE : 0 < E) (hE2 : E ≤ 1 / 2)
    (h1000 : (1000 : ℝ) ≤ C₁) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ Q ⊆ goodPrimesE C₁ n E, Q.card = Tscale n →
      ∀ k : ℕ, 0 < k → k.Coprime (Lmod Q) →
      (Real.log n) ^ (1.2 : ℝ) ≤ ((pool Q (zscale C₁ n) k).card : ℝ) →
      ∃ S : Finset ℕ, S ⊆ pool Q (zscale C₁ n) k ∧ S.Nonempty ∧
        (∏ p ∈ S, p) ≡ 1 [MOD Lmod Q] ∧
        n < ∏ p ∈ S, p ∧
        ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (n : ℝ) * (xceil Q : ℝ) ^ (Nstar Q : ℕ) := by
  classical
  filter_upwards [eventually_ge_atTop 2,
    tendsto_ell2_atTop.eventually_ge_atTop 50,
    tendsto_ell3_atTop.eventually_ge_atTop 1,
    star_boundE C₁ E hE hE2 h1000] with n hn2 ha50 hb1 hstar
  intro Q hQsub hQcard k hk hkcop hpool
  set a := ell2 n with hadef
  set b := ell3 n with hbdef
  have hba : b = Real.log a := rfl
  have hzdef : zscale C₁ n = ⌈C₁ * a * b⌉₊ := rfl
  have hTdef : Tscale n = ⌈(3:ℝ) * a⌉₊ := rfl
  clear_value a b
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hCa : (1000:ℝ) * 50 ≤ C₁ * a := mul_le_mul h1000 ha50 (by norm_num) (by linarith)
  have hCab : (1000:ℝ) * 50 * 1 ≤ C₁ * a * b :=
    mul_le_mul hCa hb1 (by norm_num) (le_trans (by norm_num) hCa)
  have hz_real : C₁ * a * b ≤ (zscale C₁ n : ℝ) := by
    rw [hzdef]
    exact Nat.le_ceil _
  have hz1 : 1 ≤ zscale C₁ n := by
    have h : (1:ℝ) ≤ (zscale C₁ n : ℝ) := le_trans (by linarith) hz_real
    exact_mod_cast h
  have hCb : (1000:ℝ) * 1 ≤ C₁ * b := mul_le_mul h1000 hb1 (by norm_num) (by linarith)
  have ha_le_Cab : a ≤ C₁ * a * b := by nlinarith [hCb, ha0]
  have hlogz_low : b ≤ Real.log (zscale C₁ n : ℝ) := by
    rw [hba]
    exact Real.log_le_log ha0 (le_trans ha_le_Cab hz_real)
  -- T facts
  have hT3a : 3 * a ≤ (Tscale n : ℝ) := by
    rw [hTdef]
    exact Nat.le_ceil _
  have hT1 : 1 ≤ Tscale n := by
    have h : (1:ℝ) ≤ (Tscale n : ℝ) := by linarith
    exact_mod_cast h
  -- facts about the primes of Q
  have hQfacts : ∀ q ∈ Q, q.Prime ∧ q ≤ zscale C₁ n ∧
      Real.sqrt (zscale C₁ n) < (q : ℝ) ∧ SmoothUpTo (yscaleE C₁ n E) (q - 1) := by
    intro q hq
    have hmem := hQsub hq
    rw [goodPrimesE, Finset.mem_filter, Finset.mem_range] at hmem
    have hz2 : 1 ≤ zscale C₁ n := by
      have := hmem.2.1.two_le
      have := hmem.1
      omega
    have h1z : (1 : ℝ) ≤ (zscale C₁ n : ℝ) := by exact_mod_cast hz2
    refine ⟨hmem.2.1, by omega, ?_, hmem.2.2.2⟩
    calc Real.sqrt (zscale C₁ n : ℝ)
        = (zscale C₁ n : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
      _ ≤ (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) :=
          Real.rpow_le_rpow_of_exponent_le h1z (by norm_num)
      _ < (q : ℝ) := hmem.2.2.1
  have hQprime : ∀ q ∈ Q, q.Prime := fun q hq => (hQfacts q hq).1
  have hQne : Q.Nonempty := Finset.card_pos.mp (by rw [hQcard]; omega)
  have hL2 : 2 ≤ Lmod Q := by
    obtain ⟨q₀, hq₀⟩ := hQne
    calc 2 ≤ q₀ := (hQprime q₀ hq₀).two_le
      _ ≤ Lmod Q := by
        rw [Lmod]
        exact Finset.single_le_prod' (f := fun q => q)
          (fun q hq => (hQprime q hq).one_lt.le) hq₀
  have hLpos : (0:ℝ) < (Lmod Q : ℝ) := by
    have : (2:ℝ) ≤ (Lmod Q : ℝ) := by exact_mod_cast hL2
    linarith
  -- lower bound on log L
  have hlogL_ge : 1.5 * a * b ≤ Real.log (Lmod Q) := by
    have h := log_Lmod_ge hz1 (fun q hq => (hQfacts q hq).2.2.1)
    rw [hQcard] at h
    calc 1.5 * a * b = (3 * a) * (b / 2) := by ring
      _ ≤ (Tscale n : ℝ) * (Real.log (zscale C₁ n) / 2) := by
        apply mul_le_mul hT3a (by linarith) (by linarith) (by positivity)
      _ ≤ Real.log (Lmod Q) := h
  have hcpos : (0:ℝ) < 1.5 * a * b := by nlinarith
  have hlogL1_ge : 1.5 * a * b ≤ Real.log ((Lmod Q : ℝ) + 1) :=
    le_trans hlogL_ge (Real.log_le_log hLpos (by linarith))
  -- λ and N* bounds
  have hlam_le : (lambdaL Q : ℝ) ≤ (zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) := by
    have h := lambdaL_le_pow hz1
      (fun q hq => ⟨(hQfacts q hq).1, (hQfacts q hq).2.1, (hQfacts q hq).2.2.2⟩)
    exact_mod_cast h
  have hlogL_le : Real.log (Lmod Q) ≤ (Tscale n : ℝ) * Real.log (zscale C₁ n) := by
    have h := log_Lmod_le (fun q hq => (hQfacts q hq).2.1)
      (fun q hq => (hQprime q hq).one_lt.le)
    rwa [hQcard] at h
  have hNstar_le : (Nstar Q : ℝ) ≤ (zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) *
      (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n)) + 2 := by
    refine le_trans (Nstar_le Q) ?_
    have h0 : (0:ℝ) ≤ 1 + Real.log (Lmod Q) := by
      have := Real.log_natCast_nonneg (Lmod Q)
      linarith
    have h1 : (lambdaL Q : ℝ) * (1 + Real.log (Lmod Q)) ≤
        (zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) *
          (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n)) :=
      mul_le_mul hlam_le (by linarith) h0 (by positivity)
    linarith
  -- log n facts
  have hn1 : 1 ≤ n := by omega
  have hlogn_pos : (0:ℝ) < Real.log n := by
    apply Real.log_pos
    have h : 1 < n := by omega
    exact_mod_cast h
  have hexp_a : Real.exp a = Real.log n := by
    rw [hadef]
    exact Real.exp_log hlogn_pos
  have hrpow : (Real.log n) ^ (1.2:ℝ) = Real.exp (1.2 * a) := by
    rw [Real.rpow_def_of_pos hlogn_pos, hadef]
    congr 1
    simp only [ell2]
    ring
  -- round-count bound
  have hrle : (Nat.log (Lmod Q + 1) n : ℝ) ≤ Real.exp a / (1.5 * a * b) := by
    have h := natLog_le_div hn1 hcpos hlogL1_ge
    rwa [← hexp_a] at h
  -- the budget: the greedy loop consumes at most the pool
  have hbudget : (Nat.log (Lmod Q + 1) n + 1) * Nstar Q ≤ (pool Q (zscale C₁ n) k).card := by
    have hP1nn : (0:ℝ) ≤ Real.exp a / (1.5 * a * b) + 1 := by
      have := div_nonneg (Real.exp_nonneg a) hcpos.le
      linarith
    have hcast : (((Nat.log (Lmod Q + 1) n + 1) * Nstar Q : ℕ) : ℝ) ≤
        ((pool Q (zscale C₁ n) k).card : ℝ) := by
      push_cast
      calc ((Nat.log (Lmod Q + 1) n : ℝ) + 1) * (Nstar Q : ℝ)
          ≤ (Real.exp a / (1.5 * a * b) + 1) *
            ((zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) *
              (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n)) + 2) :=
            mul_le_mul (by linarith) hNstar_le (Nat.cast_nonneg _) hP1nn
        _ ≤ Real.exp (1.2 * a) := hstar
        _ = (Real.log n) ^ (1.2:ℝ) := hrpow.symm
        _ ≤ ((pool Q (zscale C₁ n) k).card : ℝ) := hpool
    exact_mod_cast hcast
  -- one round of extraction is always possible
  have hQ_le_z : ∀ q ∈ Q, q ≤ zscale C₁ n ∧ q.Prime :=
    fun q hq => ⟨(hQfacts q hq).2.1, (hQfacts q hq).1⟩
  have hextract : ∀ W ⊆ pool Q (zscale C₁ n) k, W.card = Nstar Q →
      ∃ S ⊆ W, S.Nonempty ∧ (∏ p ∈ S, p) ≡ 1 [MOD Lmod Q] := by
    intro W hW hWcard
    refine round_extract hL2 (exponent_dvd_lambda hQprime hL2) (lambdaL_ne_zero hQprime)
      (fun p hp => pool_coprime hQ_le_z (hW hp)) ?_
    rw [hWcard]
    exact lt_Nstar Q
  -- run the greedy loop and conclude
  have hx1 : 1 ≤ xceil Q := by
    rw [xceil]
    exact Nat.one_le_pow _ _ (by omega)
  obtain ⟨S, hSsub, hScard, hSmod, hSdisj⟩ :=
    greedy_rounds (n := n) (L := Lmod Q) (Nst := Nstar Q) (x := xceil Q)
      (P := pool Q (zscale C₁ n) k) hn1 hL2 hx1
      (fun p hp => (pool_mem_facts hp).1.two_le)
      (fun p hp => (pool_mem_facts hp).2.2)
      hextract (Nat.log (Lmod Q + 1) n + 1) hbudget
  rcases hSdisj with ⟨hlow, hup⟩ | ⟨hgt, hle⟩
  · exfalso
    have hlt : n < (Lmod Q + 1) ^ (Nat.log (Lmod Q + 1) n + 1) :=
      Nat.lt_pow_succ_log_self (by omega) n
    exact absurd (lt_of_lt_of_le hlt (le_trans hlow hup)) (lt_irrefl n)
  · refine ⟨S, hSsub, ?_, hSmod, hgt, ?_⟩
    · rcases Finset.eq_empty_or_nonempty S with rfl | hne
      · exfalso
        rw [Finset.prod_empty] at hgt
        omega
      · exact hne
    · have hcast : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ ((n * xceil Q ^ Nstar Q : ℕ) : ℝ) := by
        exact_mod_cast hle
      have heq : ((n * xceil Q ^ Nstar Q : ℕ) : ℝ) =
          (n : ℝ) * (xceil Q : ℝ) ^ (Nstar Q : ℕ) := by
        push_cast
        ring
      rw [heq] at hcast
      exact hcast

set_option maxHeartbeats 800000 in
/-- The two inputs of the algorithm's extraction loop, exposed for the
algorithmic main theorem (Route A): the modulus is at least `2`, `N* ≥ 1`,
every pool element is a prime `≤ x` coprime to `L`, the pool supplies
`⌊log_{L+1} n⌋ + 1` rounds of `N*` elements, and every `N*`-subset of the
pool contains a nonempty subset with product `≡ 1 (mod L)` (van Emde
Boas–Kruyswijk). This is the first part of the proof of `extractionE`. -/
theorem extraction_inputsE (C₁ E : ℝ) (hE : 0 < E) (hE2 : E ≤ 1 / 2)
    (h1000 : (1000 : ℝ) ≤ C₁) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ Q ⊆ goodPrimesE C₁ n E, Q.card = Tscale n →
      ∀ k : ℕ, 0 < k → k.Coprime (Lmod Q) →
      (Real.log n) ^ (1.2 : ℝ) ≤ ((pool Q (zscale C₁ n) k).card : ℝ) →
      2 ≤ Lmod Q ∧ 1 ≤ Nstar Q ∧
      (∀ p ∈ pool Q (zscale C₁ n) k, p.Prime ∧ p ≤ xceil Q ∧ p.Coprime (Lmod Q)) ∧
      (Nat.log (Lmod Q + 1) n + 1) * Nstar Q ≤ (pool Q (zscale C₁ n) k).card ∧
      ∀ W ⊆ pool Q (zscale C₁ n) k, W.card = Nstar Q →
        ∃ S ⊆ W, S.Nonempty ∧ (∏ p ∈ S, p) ≡ 1 [MOD Lmod Q] := by
  classical
  filter_upwards [eventually_ge_atTop 2,
    tendsto_ell2_atTop.eventually_ge_atTop 50,
    tendsto_ell3_atTop.eventually_ge_atTop 1,
    star_boundE C₁ E hE hE2 h1000] with n hn2 ha50 hb1 hstar
  intro Q hQsub hQcard k hk hkcop hpool
  set a := ell2 n with hadef
  set b := ell3 n with hbdef
  have hba : b = Real.log a := rfl
  have hzdef : zscale C₁ n = ⌈C₁ * a * b⌉₊ := rfl
  have hTdef : Tscale n = ⌈(3:ℝ) * a⌉₊ := rfl
  clear_value a b
  have ha0 : (0:ℝ) < a := by linarith
  have hb0 : (0:ℝ) < b := by linarith
  have hCa : (1000:ℝ) * 50 ≤ C₁ * a := mul_le_mul h1000 ha50 (by norm_num) (by linarith)
  have hCab : (1000:ℝ) * 50 * 1 ≤ C₁ * a * b :=
    mul_le_mul hCa hb1 (by norm_num) (le_trans (by norm_num) hCa)
  have hz_real : C₁ * a * b ≤ (zscale C₁ n : ℝ) := by
    rw [hzdef]
    exact Nat.le_ceil _
  have hz1 : 1 ≤ zscale C₁ n := by
    have h : (1:ℝ) ≤ (zscale C₁ n : ℝ) := le_trans (by linarith) hz_real
    exact_mod_cast h
  have hCb : (1000:ℝ) * 1 ≤ C₁ * b := mul_le_mul h1000 hb1 (by norm_num) (by linarith)
  have ha_le_Cab : a ≤ C₁ * a * b := by nlinarith [hCb, ha0]
  have hlogz_low : b ≤ Real.log (zscale C₁ n : ℝ) := by
    rw [hba]
    exact Real.log_le_log ha0 (le_trans ha_le_Cab hz_real)
  -- T facts
  have hT3a : 3 * a ≤ (Tscale n : ℝ) := by
    rw [hTdef]
    exact Nat.le_ceil _
  have hT1 : 1 ≤ Tscale n := by
    have h : (1:ℝ) ≤ (Tscale n : ℝ) := by linarith
    exact_mod_cast h
  -- facts about the primes of Q
  have hQfacts : ∀ q ∈ Q, q.Prime ∧ q ≤ zscale C₁ n ∧
      Real.sqrt (zscale C₁ n) < (q : ℝ) ∧ SmoothUpTo (yscaleE C₁ n E) (q - 1) := by
    intro q hq
    have hmem := hQsub hq
    rw [goodPrimesE, Finset.mem_filter, Finset.mem_range] at hmem
    have hz2 : 1 ≤ zscale C₁ n := by
      have := hmem.2.1.two_le
      have := hmem.1
      omega
    have h1z : (1 : ℝ) ≤ (zscale C₁ n : ℝ) := by exact_mod_cast hz2
    refine ⟨hmem.2.1, by omega, ?_, hmem.2.2.2⟩
    calc Real.sqrt (zscale C₁ n : ℝ)
        = (zscale C₁ n : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
      _ ≤ (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) :=
          Real.rpow_le_rpow_of_exponent_le h1z (by norm_num)
      _ < (q : ℝ) := hmem.2.2.1
  have hQprime : ∀ q ∈ Q, q.Prime := fun q hq => (hQfacts q hq).1
  have hQne : Q.Nonempty := Finset.card_pos.mp (by rw [hQcard]; omega)
  have hL2 : 2 ≤ Lmod Q := by
    obtain ⟨q₀, hq₀⟩ := hQne
    calc 2 ≤ q₀ := (hQprime q₀ hq₀).two_le
      _ ≤ Lmod Q := by
        rw [Lmod]
        exact Finset.single_le_prod' (f := fun q => q)
          (fun q hq => (hQprime q hq).one_lt.le) hq₀
  have hLpos : (0:ℝ) < (Lmod Q : ℝ) := by
    have : (2:ℝ) ≤ (Lmod Q : ℝ) := by exact_mod_cast hL2
    linarith
  -- lower bound on log L
  have hlogL_ge : 1.5 * a * b ≤ Real.log (Lmod Q) := by
    have h := log_Lmod_ge hz1 (fun q hq => (hQfacts q hq).2.2.1)
    rw [hQcard] at h
    calc 1.5 * a * b = (3 * a) * (b / 2) := by ring
      _ ≤ (Tscale n : ℝ) * (Real.log (zscale C₁ n) / 2) := by
        apply mul_le_mul hT3a (by linarith) (by linarith) (by positivity)
      _ ≤ Real.log (Lmod Q) := h
  have hcpos : (0:ℝ) < 1.5 * a * b := by nlinarith
  have hlogL1_ge : 1.5 * a * b ≤ Real.log ((Lmod Q : ℝ) + 1) :=
    le_trans hlogL_ge (Real.log_le_log hLpos (by linarith))
  -- λ and N* bounds
  have hlam_le : (lambdaL Q : ℝ) ≤ (zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) := by
    have h := lambdaL_le_pow hz1
      (fun q hq => ⟨(hQfacts q hq).1, (hQfacts q hq).2.1, (hQfacts q hq).2.2.2⟩)
    exact_mod_cast h
  have hlogL_le : Real.log (Lmod Q) ≤ (Tscale n : ℝ) * Real.log (zscale C₁ n) := by
    have h := log_Lmod_le (fun q hq => (hQfacts q hq).2.1)
      (fun q hq => (hQprime q hq).one_lt.le)
    rwa [hQcard] at h
  have hNstar_le : (Nstar Q : ℝ) ≤ (zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) *
      (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n)) + 2 := by
    refine le_trans (Nstar_le Q) ?_
    have h0 : (0:ℝ) ≤ 1 + Real.log (Lmod Q) := by
      have := Real.log_natCast_nonneg (Lmod Q)
      linarith
    have h1 : (lambdaL Q : ℝ) * (1 + Real.log (Lmod Q)) ≤
        (zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) *
          (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n)) :=
      mul_le_mul hlam_le (by linarith) h0 (by positivity)
    linarith
  -- log n facts
  have hn1 : 1 ≤ n := by omega
  have hlogn_pos : (0:ℝ) < Real.log n := by
    apply Real.log_pos
    have h : 1 < n := by omega
    exact_mod_cast h
  have hexp_a : Real.exp a = Real.log n := by
    rw [hadef]
    exact Real.exp_log hlogn_pos
  have hrpow : (Real.log n) ^ (1.2:ℝ) = Real.exp (1.2 * a) := by
    rw [Real.rpow_def_of_pos hlogn_pos, hadef]
    congr 1
    simp only [ell2]
    ring
  -- round-count bound
  have hrle : (Nat.log (Lmod Q + 1) n : ℝ) ≤ Real.exp a / (1.5 * a * b) := by
    have h := natLog_le_div hn1 hcpos hlogL1_ge
    rwa [← hexp_a] at h
  -- the budget: the greedy loop consumes at most the pool
  have hbudget : (Nat.log (Lmod Q + 1) n + 1) * Nstar Q ≤ (pool Q (zscale C₁ n) k).card := by
    have hP1nn : (0:ℝ) ≤ Real.exp a / (1.5 * a * b) + 1 := by
      have := div_nonneg (Real.exp_nonneg a) hcpos.le
      linarith
    have hcast : (((Nat.log (Lmod Q + 1) n + 1) * Nstar Q : ℕ) : ℝ) ≤
        ((pool Q (zscale C₁ n) k).card : ℝ) := by
      push_cast
      calc ((Nat.log (Lmod Q + 1) n : ℝ) + 1) * (Nstar Q : ℝ)
          ≤ (Real.exp a / (1.5 * a * b) + 1) *
            ((zscale C₁ n : ℝ) ^ (yscaleE C₁ n E + 1) *
              (1 + (Tscale n : ℝ) * Real.log (zscale C₁ n)) + 2) :=
            mul_le_mul (by linarith) hNstar_le (Nat.cast_nonneg _) hP1nn
        _ ≤ Real.exp (1.2 * a) := hstar
        _ = (Real.log n) ^ (1.2:ℝ) := hrpow.symm
        _ ≤ ((pool Q (zscale C₁ n) k).card : ℝ) := hpool
    exact_mod_cast hcast
  -- one round of extraction is always possible
  have hQ_le_z : ∀ q ∈ Q, q ≤ zscale C₁ n ∧ q.Prime :=
    fun q hq => ⟨(hQfacts q hq).2.1, (hQfacts q hq).1⟩
  have hextract : ∀ W ⊆ pool Q (zscale C₁ n) k, W.card = Nstar Q →
      ∃ S ⊆ W, S.Nonempty ∧ (∏ p ∈ S, p) ≡ 1 [MOD Lmod Q] := by
    intro W hW hWcard
    refine round_extract hL2 (exponent_dvd_lambda hQprime hL2) (lambdaL_ne_zero hQprime)
      (fun p hp => pool_coprime hQ_le_z (hW hp)) ?_
    rw [hWcard]
    exact lt_Nstar Q
  -- assemble the five inputs
  have hN1 : 1 ≤ Nstar Q := by
    rw [Nstar]
    omega
  exact ⟨hL2, hN1,
    fun p hp => ⟨(pool_mem_facts hp).1, (pool_mem_facts hp).2.2, pool_coprime hQ_le_z hp⟩,
    hbudget, hextract⟩

end Carmichael
