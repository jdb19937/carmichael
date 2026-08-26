/-
The van Emde Boas–Kruyswijk zero-sum theorem (a Davenport-constant bound for
finite abelian groups), following the simplified character-theoretic proof of
Theorem 1.1 in W.R. Alford, A. Granville, C. Pomerance, "There are infinitely
many Carmichael numbers", Annals of Math. 140 (1994), 703–722 (itself based on
P. van Emde Boas and D. Kruyswijk, "A combinatorial problem on finite abelian
groups III", CWI report ZW-1969-008).

Statement: if `G` is a finite abelian group of exponent `m`, then any multiset
of more than `m * (1 + log (|G| / m))` elements of `G` contains a nonempty
sub-multiset whose product is `1`.

Proof sketch (multiplicative form, over `ℂ`): let `g_1, ..., g_n` be the
sequence and suppose no nonempty subsequence has product `1`.  For characters
`χ : G →* ℂˣ` and any `a_i ∈ ℂˣ`, expanding and using orthogonality of
characters,
  `∑_χ ∏_i (a_i - χ(g_i)) = |Ĝ| * ∑_{T : ∏_{i∈T} g_i = 1} (-1)^|T| ∏_{i∉T} a_i
                          = |Ĝ| * ∏_i a_i ≠ 0`.
On the other hand each character value `χ(g)` is an `m`-th root of unity, of
which there are only `m` in `ℂ`, so by a greedy/pigeonhole argument one can
choose the `a_i` so that every character `χ` satisfies `χ(g_i) = a_i` for some
`i`, provided `n > m * (1 + log(|G|/m))`; then every summand on the left
vanishes, a contradiction.
-/
import Mathlib

namespace Carmichael

namespace ZeroSum

open Finset

variable {G : Type*} [CommGroup G] [Fintype G]

/-- Pigeonhole step: for any finite set `S` of characters of `G` and any `g : G`,
some value `b ∈ ℂˣ` satisfies `χ g = b` for at least `|S| / m` characters in `S`,
where `m` is the exponent of `G`.  We record the complementary set. -/
private lemma exists_step (S : Finset (G →* ℂˣ)) (g : G) :
    ∃ (b : ℂˣ) (S' : Finset (G →* ℂˣ)),
      (∀ χ ∈ S, χ g ≠ b → χ ∈ S') ∧
      ((S'.card : ℝ) ≤ (1 - 1 / (Monoid.exponent G : ℝ)) * S.card) := by
  classical
  have : NeZero (Monoid.exponent G) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  let : Fintype (rootsOfUnity (Monoid.exponent G) ℂ) := Fintype.ofFinite _
  have hcardμ : Fintype.card (rootsOfUnity (Monoid.exponent G) ℂ) = Monoid.exponent G := by
    rw [← Nat.card_eq_fintype_card]
    exact Complex.card_rootsOfUnity (Monoid.exponent G)
  -- the map sending a character to its value at `g`, viewed as a root of unity
  have hmem : ∀ χ : G →* ℂˣ, χ g ∈ rootsOfUnity (Monoid.exponent G) ℂ := fun χ => by
    rw [mem_rootsOfUnity, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
  set f : (G →* ℂˣ) → rootsOfUnity (Monoid.exponent G) ℂ := fun χ => ⟨χ g, hmem χ⟩ with hf
  have hcard : S.card = ∑ b ∈ (univ : Finset (rootsOfUnity (Monoid.exponent G) ℂ)),
      (S.filter fun χ => f χ = b).card :=
    Finset.card_eq_sum_card_fiberwise fun χ _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  -- pick a value with the largest fiber
  have hne : (univ : Finset (rootsOfUnity (Monoid.exponent G) ℂ)).Nonempty :=
    ⟨1, Finset.mem_univ 1⟩
  obtain ⟨b₀, -, hb₀max⟩ :=
    Finset.exists_max_image univ (fun b => (S.filter fun χ => f χ = b).card) hne
  have hSle : S.card ≤ Monoid.exponent G * (S.filter fun χ => f χ = b₀).card := by
    calc S.card
        = ∑ b ∈ (univ : Finset (rootsOfUnity (Monoid.exponent G) ℂ)),
            (S.filter fun χ => f χ = b).card := hcard
      _ ≤ (univ : Finset (rootsOfUnity (Monoid.exponent G) ℂ)).card •
            (S.filter fun χ => f χ = b₀).card :=
          Finset.sum_le_card_nsmul _ _ _ fun b hb => hb₀max b hb
      _ = Monoid.exponent G * (S.filter fun χ => f χ = b₀).card := by
          rw [smul_eq_mul, Finset.card_univ, hcardμ]
  -- translate the fiber condition to `χ g = ↑b₀`
  have hfib_eq : S.filter (fun χ => χ g = (b₀ : ℂˣ)) = S.filter (fun χ => f χ = b₀) :=
    Finset.filter_congr fun χ _ =>
      ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  refine ⟨(b₀ : ℂˣ), S.filter (fun χ => ¬ χ g = (b₀ : ℂˣ)),
    fun χ hχ hne' => Finset.mem_filter.mpr ⟨hχ, hne'⟩, ?_⟩
  have hm1 : 1 ≤ Monoid.exponent G :=
    Nat.one_le_iff_ne_zero.mpr Monoid.exponent_ne_zero_of_finite
  have hm0R : (0 : ℝ) < (Monoid.exponent G : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_pos hm1
  have hsplit := Finset.card_filter_add_card_filter_not (s := S) (fun χ => χ g = (b₀ : ℂˣ))
  have hsplitR : ((S.filter fun χ => χ g = (b₀ : ℂˣ)).card : ℝ) +
      ((S.filter fun χ => ¬ χ g = (b₀ : ℂˣ)).card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast hsplit
  have hAR : (S.card : ℝ) / (Monoid.exponent G : ℝ) ≤
      ((S.filter fun χ => χ g = (b₀ : ℂˣ)).card : ℝ) := by
    rw [div_le_iff₀ hm0R]
    have h1 : (S.card : ℝ) ≤ (Monoid.exponent G : ℝ) *
        ((S.filter fun χ => χ g = (b₀ : ℂˣ)).card : ℝ) := by
      rw [hfib_eq]; exact_mod_cast hSle
    linarith
  have hring : (1 - 1 / (Monoid.exponent G : ℝ)) * (S.card : ℝ)
      = (S.card : ℝ) - (S.card : ℝ) / (Monoid.exponent G : ℝ) := by ring
  rw [hring]
  linarith [hsplitR, hAR]

/-- Greedy lemma: given `n` elements of `G` and a finite set `S` of characters, one can
choose values `a : Fin n → ℂˣ` so that the set `R` of characters of `S` not "hit" by any
of them has size at most `(1 - 1/m)^n * |S|`. -/
private lemma greedy : ∀ (n : ℕ) (v : Fin n → G) (S : Finset (G →* ℂˣ)),
    ∃ (a : Fin n → ℂˣ) (R : Finset (G →* ℂˣ)),
      (∀ χ ∈ S, χ ∉ R → ∃ i, χ (v i) = a i) ∧
      ((R.card : ℝ) ≤ (1 - 1 / (Monoid.exponent G : ℝ)) ^ n * S.card)
  | 0, _, S => ⟨Fin.elim0, S, fun _ hχ hR => absurd hχ hR, by simp⟩
  | (n + 1), v, S => by
    obtain ⟨b, S', hbmem, hS'card⟩ := exists_step S (v 0)
    obtain ⟨a', R, hcov, hcard⟩ := greedy n (Fin.tail v) S'
    refine ⟨Fin.cons b a', R, ?_, ?_⟩
    · intro χ hχS hχR
      by_cases hb : χ (v 0) = b
      · exact ⟨0, by rw [Fin.cons_zero]; exact hb⟩
      · obtain ⟨i, hi⟩ := hcov χ (hbmem χ hχS hb) hχR
        exact ⟨i.succ, by rw [Fin.cons_succ]; exact hi⟩
    · have hm1 : 1 ≤ Monoid.exponent G :=
        Nat.one_le_iff_ne_zero.mpr Monoid.exponent_ne_zero_of_finite
      have hm1R : (1 : ℝ) ≤ (Monoid.exponent G : ℝ) := by exact_mod_cast hm1
      have h0 : (0 : ℝ) ≤ 1 - 1 / (Monoid.exponent G : ℝ) := by
        rw [sub_nonneg]
        exact div_le_one_of_le₀ hm1R (by linarith)
      calc (R.card : ℝ)
          ≤ (1 - 1 / (Monoid.exponent G : ℝ)) ^ n * S'.card := hcard
        _ ≤ (1 - 1 / (Monoid.exponent G : ℝ)) ^ n *
              ((1 - 1 / (Monoid.exponent G : ℝ)) * S.card) :=
            mul_le_mul_of_nonneg_left hS'card (pow_nonneg h0 n)
        _ = (1 - 1 / (Monoid.exponent G : ℝ)) ^ (n + 1) * S.card := by ring

/-- Column orthogonality at the identity: the character sum at `1` is `|Ĝ|`. -/
private lemma sum_char_one (G : Type*) [CommGroup G] [Fintype G] [Fintype (G →* ℂˣ)] :
    ∑ χ : G →* ℂˣ, ((χ (1 : G) : ℂˣ) : ℂ) = (Fintype.card (G →* ℂˣ) : ℂ) := by
  simp

/-- Column orthogonality away from the identity: the character sum at `g ≠ 1` vanishes.
This uses that characters of a finite abelian group separate points (Mathlib's
finite-abelian duality, available since `ℂ` has enough roots of unity). -/
private lemma sum_char_ne_one [Fintype (G →* ℂˣ)] {g : G} (hg : g ≠ 1) :
    ∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) = 0 := by
  have : NeZero (Monoid.exponent G) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨χ₀, hχ₀⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hg
  have key : ((χ₀ g : ℂˣ) : ℂ) * ∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ)
      = ∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) := by
    rw [Finset.mul_sum]
    calc ∑ χ : G →* ℂˣ, ((χ₀ g : ℂˣ) : ℂ) * ((χ g : ℂˣ) : ℂ)
        = ∑ χ : G →* ℂˣ, (((Equiv.mulLeft χ₀ χ) g : ℂˣ) : ℂ) := by
          refine Finset.sum_congr rfl fun χ _ => ?_
          simp [Units.val_mul]
      _ = ∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) :=
          Equiv.sum_comp (Equiv.mulLeft χ₀) fun ψ : G →* ℂˣ => ((ψ g : ℂˣ) : ℂ)
  have hne : ((χ₀ g : ℂˣ) : ℂ) ≠ 1 := by
    intro h
    exact hχ₀ (Units.ext (by rw [h, Units.val_one]))
  have h0 : (((χ₀ g : ℂˣ) : ℂ) - 1) * ∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) = 0 := by
    rw [sub_mul, one_mul, key, sub_self]
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-- Core step of the AGP argument: if the values `a : Fin n → ℂˣ` "cover" every
character (each `χ` satisfies `χ (v i) = a i` for some `i`), then some nonempty
subfamily of the `v i` has product `1`. -/
private lemma zero_sum_of_cover [Fintype (G →* ℂˣ)] {n : ℕ} (v : Fin n → G)
    (a : Fin n → ℂˣ) (hcov : ∀ χ : G →* ℂˣ, ∃ i, χ (v i) = a i) :
    ∃ T : Finset (Fin n), T.Nonempty ∧ ∏ i ∈ T, v i = 1 := by
  by_contra hno
  push Not at hno
  classical
  -- every summand of the character sum vanishes
  have hzero : ∑ χ : G →* ℂˣ, ∏ i, ((a i : ℂ) - ((χ (v i) : ℂˣ) : ℂ)) = 0 := by
    refine Finset.sum_eq_zero fun χ _ => ?_
    obtain ⟨i, hi⟩ := hcov χ
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, sub_self])
  -- expand the product over subsets
  have expand : ∀ χ : G →* ℂˣ,
      ∏ i, ((a i : ℂ) - ((χ (v i) : ℂˣ) : ℂ))
        = ∑ T ∈ (univ : Finset (Fin n)).powerset,
            (((χ (∏ i ∈ T, v i) : ℂˣ) : ℂ) *
              ((-1) ^ T.card * ∏ i ∈ univ \ T, (a i : ℂ))) := by
    intro χ
    have h1 : ∏ i, ((a i : ℂ) - ((χ (v i) : ℂˣ) : ℂ))
        = ∏ i, ((-((χ (v i) : ℂˣ) : ℂ)) + (a i : ℂ)) :=
      Finset.prod_congr rfl fun i _ => by ring
    rw [h1, Finset.prod_add]
    refine Finset.sum_congr rfl fun T _ => ?_
    have h2 : ∏ i ∈ T, (-((χ (v i) : ℂˣ) : ℂ))
        = (-1) ^ T.card * ∏ i ∈ T, ((χ (v i) : ℂˣ) : ℂ) := by
      calc ∏ i ∈ T, (-((χ (v i) : ℂˣ) : ℂ))
          = ∏ i ∈ T, ((-1) * ((χ (v i) : ℂˣ) : ℂ)) :=
            Finset.prod_congr rfl fun i _ => (neg_one_mul _).symm
        _ = (∏ _i ∈ T, (-1 : ℂ)) * ∏ i ∈ T, ((χ (v i) : ℂˣ) : ℂ) :=
            Finset.prod_mul_distrib
        _ = (-1) ^ T.card * ∏ i ∈ T, ((χ (v i) : ℂˣ) : ℂ) := by
            rw [Finset.prod_const]
    have h3 : ((χ (∏ i ∈ T, v i) : ℂˣ) : ℂ) = ∏ i ∈ T, ((χ (v i) : ℂˣ) : ℂ) := by
      rw [map_prod χ]
      exact map_prod (Units.coeHom ℂ) (fun i => χ (v i)) T
    rw [h2, h3]
    ring
  -- swap the two sums and use orthogonality
  have swap : ∑ χ : G →* ℂˣ, ∏ i, ((a i : ℂ) - ((χ (v i) : ℂˣ) : ℂ))
      = ∑ T ∈ (univ : Finset (Fin n)).powerset,
          ((∑ χ : G →* ℂˣ, ((χ (∏ i ∈ T, v i) : ℂˣ) : ℂ)) *
            ((-1) ^ T.card * ∏ i ∈ univ \ T, (a i : ℂ))) := by
    calc ∑ χ : G →* ℂˣ, ∏ i, ((a i : ℂ) - ((χ (v i) : ℂˣ) : ℂ))
        = ∑ χ : G →* ℂˣ, ∑ T ∈ (univ : Finset (Fin n)).powerset,
            (((χ (∏ i ∈ T, v i) : ℂˣ) : ℂ) *
              ((-1) ^ T.card * ∏ i ∈ univ \ T, (a i : ℂ))) :=
          Finset.sum_congr rfl fun χ _ => expand χ
      _ = ∑ T ∈ (univ : Finset (Fin n)).powerset, ∑ χ : G →* ℂˣ,
            (((χ (∏ i ∈ T, v i) : ℂˣ) : ℂ) *
              ((-1) ^ T.card * ∏ i ∈ univ \ T, (a i : ℂ))) :=
          Finset.sum_comm
      _ = ∑ T ∈ (univ : Finset (Fin n)).powerset,
            ((∑ χ : G →* ℂˣ, ((χ (∏ i ∈ T, v i) : ℂˣ) : ℂ)) *
              ((-1) ^ T.card * ∏ i ∈ univ \ T, (a i : ℂ))) :=
          Finset.sum_congr rfl fun T _ => (Finset.sum_mul _ _ _).symm
  -- only `T = ∅` survives, giving a nonzero value
  have heval : ∑ T ∈ (univ : Finset (Fin n)).powerset,
      ((∑ χ : G →* ℂˣ, ((χ (∏ i ∈ T, v i) : ℂˣ) : ℂ)) *
        ((-1) ^ T.card * ∏ i ∈ univ \ T, (a i : ℂ)))
      = (Fintype.card (G →* ℂˣ) : ℂ) * ∏ i, (a i : ℂ) := by
    refine (Finset.sum_eq_single (∅ : Finset (Fin n)) ?_ ?_).trans ?_
    · intro T _ hTne
      rw [sum_char_ne_one (hno T (Finset.nonempty_iff_ne_empty.mpr hTne)), zero_mul]
    · intro h
      exact absurd (Finset.empty_mem_powerset _) h
    · simp only [Finset.prod_empty, Finset.card_empty, pow_zero, one_mul,
        Finset.sdiff_empty]
      rw [sum_char_one]
  rw [swap, heval] at hzero
  have : Nonempty (G →* ℂˣ) := ⟨1⟩
  have hN : (Fintype.card (G →* ℂˣ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have ha : (∏ i, (a i : ℂ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero (a i)
  exact mul_ne_zero hN ha hzero

/-- The Fin-indexed form of the van Emde Boas–Kruyswijk theorem. -/
private theorem vebk_fin {n : ℕ} (v : Fin n → G)
    (hn : (Monoid.exponent G : ℝ) *
        (1 + Real.log ((Fintype.card G : ℝ) / (Monoid.exponent G : ℝ))) < (n : ℝ)) :
    ∃ T : Finset (Fin n), T.Nonempty ∧ ∏ i ∈ T, v i = 1 := by
  classical
  have : NeZero (Monoid.exponent G) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have : Finite (G →* ℂˣ) :=
    Finite.of_equiv G
      (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).some.symm.toEquiv
  let : Fintype (G →* ℂˣ) := Fintype.ofFinite _
  -- abbreviations: `e` the exponent, `c` the order of `G`
  obtain ⟨e, he⟩ : ∃ e, e = Monoid.exponent G := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = Fintype.card G := ⟨_, rfl⟩
  rw [← he, ← hc] at hn
  have hNc : Fintype.card (G →* ℂˣ) = c := by
    rw [hc, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ
  have he1 : 1 ≤ e := by
    rw [he]; exact Nat.one_le_iff_ne_zero.mpr Monoid.exponent_ne_zero_of_finite
  have he0R : (0 : ℝ) < (e : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_pos he1
  have heR1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he1
  have hc0 : 0 < c := by rw [hc]; exact Fintype.card_pos
  have hc0R : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc0
  have hec : e ≤ c := by
    rw [he, hc]; exact Nat.le_of_dvd Fintype.card_pos Group.exponent_dvd_card
  have hecR : (e : ℝ) ≤ (c : ℝ) := by exact_mod_cast hec
  have hlog0 : 0 ≤ Real.log ((c : ℝ) / (e : ℝ)) :=
    Real.log_nonneg (by rw [le_div_iff₀ he0R]; linarith)
  have henR : (e : ℝ) < (n : ℝ) := by
    nlinarith [mul_nonneg he0R.le hlog0, hn]
  have hen : e < n := by exact_mod_cast henR
  -- choice of the number `k` of greedy steps
  obtain ⟨k, hk⟩ : ∃ k, k = n - e + 1 := ⟨_, rfl⟩
  have hkle : k ≤ n := by omega
  have hkcast : (k : ℝ) = (n : ℝ) - (e : ℝ) + 1 := by
    rw [hk, Nat.cast_add, Nat.cast_sub hen.le, Nat.cast_one]
  have hkR : (e : ℝ) * Real.log ((c : ℝ) / (e : ℝ)) < (k : ℝ) := by
    nlinarith [hn, hkcast]
  -- run the greedy algorithm on the first `k` elements
  obtain ⟨a', R, hcov', hRle⟩ := greedy k (fun i => v (Fin.castLE hkle i)) Finset.univ
  rw [← he] at hRle
  rw [Finset.card_univ, hNc] at hRle
  -- the residual set has fewer than `e` elements
  have hstep : ((1 : ℝ) - 1 / (e : ℝ)) ^ k * (c : ℝ) < (e : ℝ) := by
    have h0 : (0 : ℝ) ≤ 1 - 1 / (e : ℝ) := by
      rw [sub_nonneg]
      exact div_le_one_of_le₀ heR1 he0R.le
    have h2 : (1 : ℝ) - 1 / (e : ℝ) ≤ Real.exp (-(1 / (e : ℝ))) := by
      have := Real.add_one_le_exp (-(1 / (e : ℝ)))
      linarith
    have h3 : ((1 : ℝ) - 1 / (e : ℝ)) ^ k ≤ Real.exp (-(1 / (e : ℝ))) ^ k :=
      pow_le_pow_left₀ h0 h2 k
    have h4 : Real.exp (-(1 / (e : ℝ))) ^ k = Real.exp ((k : ℝ) * -(1 / (e : ℝ))) :=
      (Real.exp_nat_mul _ k).symm
    have h5 : (k : ℝ) * -(1 / (e : ℝ)) < Real.log ((e : ℝ) / (c : ℝ)) := by
      have hld : Real.log ((e : ℝ) / (c : ℝ)) = Real.log (e : ℝ) - Real.log (c : ℝ) :=
        Real.log_div (ne_of_gt he0R) (ne_of_gt hc0R)
      have hld2 : Real.log ((c : ℝ) / (e : ℝ)) = Real.log (c : ℝ) - Real.log (e : ℝ) :=
        Real.log_div (ne_of_gt hc0R) (ne_of_gt he0R)
      rw [hld]
      rw [hld2] at hkR
      have hdiv : Real.log (c : ℝ) - Real.log (e : ℝ) < (k : ℝ) / (e : ℝ) := by
        rw [lt_div_iff₀ he0R]
        nlinarith [hkR]
      have hrewrite : (k : ℝ) * -(1 / (e : ℝ)) = -((k : ℝ) / (e : ℝ)) := by ring
      rw [hrewrite]
      linarith
    calc ((1 : ℝ) - 1 / (e : ℝ)) ^ k * (c : ℝ)
        ≤ Real.exp ((k : ℝ) * -(1 / (e : ℝ))) * (c : ℝ) := by
          rw [← h4]; exact mul_le_mul_of_nonneg_right h3 hc0R.le
      _ < ((e : ℝ) / (c : ℝ)) * (c : ℝ) := by
          have hexp := Real.exp_lt_exp.mpr h5
          rw [Real.exp_log (div_pos he0R hc0R)] at hexp
          exact mul_lt_mul_of_pos_right hexp hc0R
      _ = (e : ℝ) := div_mul_cancel₀ _ (ne_of_gt hc0R)
  have hRlt : (R.card : ℝ) < (e : ℝ) := lt_of_le_of_lt hRle hstep
  have hRcard : R.card < e := by exact_mod_cast hRlt
  have hkRn : k + R.card ≤ n := by omega
  -- assign the leftover characters to the remaining positions
  have hrlen : R.toList.length = R.card := Finset.length_toList R
  set a : Fin n → ℂˣ := fun i =>
    if h : (i : ℕ) < k then a' ⟨i, h⟩ else (R.toList.getD ((i : ℕ) - k) 1) (v i) with ha
  have hcov : ∀ χ : G →* ℂˣ, ∃ i, χ (v i) = a i := by
    intro χ
    by_cases hχR : χ ∈ R
    · obtain ⟨j, hj, hjχ⟩ := List.mem_iff_getElem.mp (Finset.mem_toList.mpr hχR)
      have hjn : k + j < n := by omega
      refine ⟨⟨k + j, hjn⟩, ?_⟩
      have h1 : ¬ (k + j < k) := by omega
      have h2eq : k + j - k = j := by omega
      show χ (v ⟨k + j, hjn⟩) = a ⟨k + j, hjn⟩
      simp only [ha]
      rw [dif_neg h1]
      show χ (v ⟨k + j, hjn⟩) = (R.toList.getD (k + j - k) 1) (v ⟨k + j, hjn⟩)
      rw [h2eq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
        hjχ]
    · obtain ⟨i, hi⟩ := hcov' χ (Finset.mem_univ χ) hχR
      refine ⟨Fin.castLE hkle i, ?_⟩
      have h1 : ((Fin.castLE hkle i : Fin n) : ℕ) < k := i.isLt
      show χ (v (Fin.castLE hkle i)) = a (Fin.castLE hkle i)
      simp only [ha]
      rw [dif_pos h1]
      have hmk : (⟨((Fin.castLE hkle i : Fin n) : ℕ), h1⟩ : Fin k) = i := Fin.ext rfl
      rw [hmk]
      exact hi
  exact zero_sum_of_cover v a hcov

end ZeroSum

/-- **The van Emde Boas–Kruyswijk zero-sum theorem** (multiplicative form).

If `G` is a finite abelian group whose exponent (equivalently, for abelian `G`,
the maximal order of an element) is `m`, then any multiset of more than
`m * (1 + log (|G| / m))` elements of `G` has a nonempty sub-multiset whose
product is the identity.

Reference: Alford–Granville–Pomerance, Annals of Math. 140 (1994), Theorem 1.1. -/
theorem vebk : ∀ (G : Type) [CommGroup G] [Fintype G] (s : Multiset G),
    (Monoid.exponent G : ℝ) *
        (1 + Real.log ((Fintype.card G : ℝ) / (Monoid.exponent G : ℝ)))
      < (s.card : ℝ) →
    ∃ t : Multiset G, t ≤ s ∧ t ≠ 0 ∧ t.prod = 1 := by
  intro G _ _ s hs
  classical
  obtain ⟨T, hTne, hTprod⟩ :=
    ZeroSum.vebk_fin (fun i : Fin s.toList.length => s.toList.get i)
      (by rw [Multiset.length_toList]; exact hs)
  refine ⟨Multiset.map (fun i : Fin s.toList.length => s.toList.get i) T.val, ?_, ?_, ?_⟩
  · have h1 : Multiset.map (fun i : Fin s.toList.length => s.toList.get i) T.val
        ≤ Multiset.map (fun i : Fin s.toList.length => s.toList.get i)
            (Finset.univ : Finset (Fin s.toList.length)).val :=
      Multiset.map_le_map (Finset.val_le_iff.mpr (Finset.subset_univ T))
    have h2 : Multiset.map (fun i : Fin s.toList.length => s.toList.get i)
        (Finset.univ : Finset (Fin s.toList.length)).val = s := by
      rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
    rwa [h2] at h1
  · simp only [ne_eq, Multiset.map_eq_zero]
    exact fun h => (Finset.nonempty_iff_ne_empty.mp hTne) (Finset.val_eq_zero.mp h)
  · rw [← Finset.prod_eq_multiset_prod]
    exact hTprod

end Carmichael
