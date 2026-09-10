/-
Route A, critical assembly: Mickey's theorem in algorithmic form.

`Alg.search` (Carmichael/Algorithm.lean) is a computable `def` with a
built-in operation counter. This file proves that at every scale in the
window `InWindow` (in particular at the paper's exact scales
`scalesOf C₁alg Eweak n`) the search outputs a certified Carmichael number
`m ∈ (n, n^{1+ε}]` with its complete prime factorization and charges at
most `exp(100 ℓ₂ ℓ₃)` operations, for all large `n`, with no hypothesis
(Route Z discharges AGP Theorem 3.1).

Proof pattern (mirrors `main_theorem_weak`): `filter_upwards` over the four
windowed step theorems (`step2_succeedsW`, `step3_haltsW`,
`extraction_inputsW`, `output_carmichaelW`) and the budget
(`costPieces_leW`), then chain the algorithm's specifications
(`reservoir_specW`, `scan_spec`, `extract_spec`, `verify_spec`,
`search_success`) through them.
-/
import Carmichael.AlgScan
import Carmichael.AlgExtract
import Carmichael.AlgBudget
import Carmichael.Step2W
import Carmichael.Step3W
import Carmichael.ExtractionW
import Carmichael.OutputW
import Carmichael.Unconditional

set_option autoImplicit false

namespace Carmichael

open Filter

/-- The scale constant for the algorithm: `C₁ = max(60/γ, 1000)` (Step 2 at
windowed scales needs `60 ≤ C₁ γ`). -/
noncomputable def C₁alg : ℝ := max (60 / gammaWeak) 1000

theorem thousand_le_C₁alg : (1000 : ℝ) ≤ C₁alg := le_max_right _ _

theorem sixty_le_C₁alg_mul_gammaWeak : (60 : ℝ) ≤ C₁alg * gammaWeak :=
  (div_le_iff₀ gammaWeak_pos).mp (le_max_left _ _)

/-- `ℓ₂(n) → ∞`. -/
private lemma tendsto_ell2_atTopA : Tendsto ell2 atTop atTop :=
  Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- `ℓ₃(n) → ∞`. -/
private lemma tendsto_ell3_atTopA : Tendsto ell3 atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_ell2_atTopA

open Classical in
/-- The sieve's smooth-shifted-prime density at exponent `Eweak` transfers
to any smaller exponent `E` (the filtered set only grows). -/
private lemma smooth_shifted_of_le (E : ℝ) (hEw : E ≤ Eweak) :
    ∀ x : ℕ, x₁Weak ≤ x →
      gammaWeak * (primePi x : ℝ) ≤
        (((Finset.range (x + 1)).filter (fun p => p.Prime ∧
          ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) - E))).card : ℝ) := by
  intro x hx
  refine le_trans (smooth_shifted_weak_spec x hx) ?_
  have hsub : ((Finset.range (x + 1)).filter (fun p => p.Prime ∧
        ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) - Eweak))) ⊆
      ((Finset.range (x + 1)).filter (fun p => p.Prime ∧
        ∀ q : ℕ, q.Prime → q ∣ p - 1 → (q : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) - E))) := by
    intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    obtain ⟨hpr, hpp, hq⟩ := hp
    refine ⟨hpr, hpp, fun q hq' hqd => ?_⟩
    have h1x : (1 : ℝ) ≤ (x : ℝ) := by
      have hx1 : 1 ≤ x := by
        rcases Nat.eq_zero_or_pos x with h0 | h0
        · subst h0
          have : p < 1 := Finset.mem_range.mp hpr
          have : p = 0 := by omega
          subst this
          exact absurd hpp Nat.not_prime_zero
        · exact h0
      exact_mod_cast hx1
    refine le_trans (hq q hq' hqd) ?_
    exact Real.rpow_le_rpow_of_exponent_le h1x (by linarith only [hEw])
  exact_mod_cast Finset.card_le_card hsub

/-- **`Alg.search` succeeds at every scale in the window**, given AGP 3.1
(`A`), for any `C₁ ≥ 1000` with `60 ≤ C₁ γ` and any `0 < E ≤ Eweak`: for
every `ε > 0` and all large `n`, at any scales `sc` in the window with a
threshold `θ ∈ [(log n)^{1.2}, 16 (log n)^{1.2}]`, the search outputs a
certified Carmichael number in `(n, n^{1+ε}]` and charges at most
`exp(100 ℓ₂ ℓ₃)` operations. -/
theorem search_successW_of (A : AssumptionsWeak) (C₁ E : ℝ)
    (hE : 0 < E) (hEw : E ≤ Eweak) (h1000 : (1000 : ℝ) ≤ C₁)
    (h60 : (60 : ℝ) ≤ C₁ * gammaWeak) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ sc : Scales,
      InWindow C₁ E n sc.z sc.z99 sc.y sc.T →
      (Real.log n) ^ (1.2 : ℝ) ≤ (sc.θ : ℝ) → (sc.θ : ℝ) ≤ 16 * (Real.log n) ^ (1.2 : ℝ) →
      ∃ m : ℕ, ∃ S : List ℕ,
        (Alg.search sc n).1 = some (m, S) ∧
        S.Nodup ∧ (∀ p ∈ S, p.Prime) ∧ 3 ≤ S.length ∧ m = S.prod ∧
        IsCarmichael m ∧ n < m ∧ (m : ℝ) ≤ (n : ℝ) ^ (1 + ε) ∧
        ((Alg.search sc n).2 : ℝ) ≤ Real.exp (100 * ell2 n * ell3 n) := by
  have hE2 : E ≤ 1 / 2 := hEw.trans Eweak_le_half
  filter_upwards [
    step2_succeedsW C₁ gammaWeak E x₁Weak hE hE2 gammaWeak_pos h60 h1000
      (smooth_shifted_of_le E hEw),
    step3_haltsW C₁ A.D E A.z₃ 16 hE hE2 h1000 A.pigeonhole,
    extraction_inputsW C₁ E hE hE2 h1000,
    output_carmichaelW C₁ E hE hE2 h1000 ε hε,
    costPieces_leW C₁ E hE hE2 h1000,
    eventually_ge_atTop 2] with n h2 h3 h4 h5 hb hn2
  intro sc hW hθlo hθhi
  have hn1 : 1 ≤ n := by omega
  /- Step 2: the reservoir and `Q`, its `T` largest elements. -/
  obtain ⟨R, hR⟩ : ∃ R, (Alg.reservoir sc.z sc.z99 sc.y).1 = R := ⟨_, rfl⟩
  obtain ⟨hRnodup, hRfin⟩ := reservoir_specW sc.z sc.z99 sc.y
  rw [hR] at hRnodup hRfin
  have hlen : sc.T ≤ R.length := by
    have := h2 _ _ _ _ hW
    rwa [← hRfin, List.toFinset_card_of_nodup hRnodup] at this
  obtain ⟨Q, hQ⟩ : ∃ Q, R.drop (R.length - sc.T) = Q := ⟨_, rfl⟩
  have hQnodup : Q.Nodup := by
    rw [← hQ]; exact hRnodup.sublist (List.drop_sublist _ _)
  have hQlen : Q.length = sc.T := by
    rw [← hQ, List.length_drop]; omega
  have hQsub : Q.toFinset ⊆ goodPrimesW sc.z sc.z99 sc.y := by
    intro q hq
    rw [← hRfin, List.mem_toFinset]
    rw [List.mem_toFinset, ← hQ] at hq
    exact List.mem_of_mem_drop hq
  have hQcard : Q.toFinset.card = sc.T := by
    rw [List.toFinset_card_of_nodup hQnodup, hQlen]
  have hQgood : ∀ q ∈ Q, q.Prime ∧ q ≤ sc.z := by
    intro q hq
    have hmem := hQsub (List.mem_toFinset.mpr hq)
    simp only [goodPrimesW, Finset.mem_filter, Finset.mem_range] at hmem
    exact ⟨hmem.2.1, by omega⟩
  have hQprime : ∀ q ∈ Q, q.Prime := fun q hq => (hQgood q hq).1
  have hLpos : 0 < Q.prod :=
    Nat.pos_of_ne_zero (List.prod_ne_zero (fun h0 => (hQprime 0 h0).ne_zero rfl))
  have hxpos : 0 < Q.prod ^ 5 := pow_pos hLpos 5
  have hx1 : (1 : ℝ) ≤ ((Q.prod ^ 5 : ℕ) : ℝ) := by exact_mod_cast hxpos
  have hLmod := Lmod_toFinset Q hQnodup
  have hxceil := xceil_toFinset Q hQnodup
  /- Step 3: some `k₀` passes the test, so the scan halts at some `k ≤ k₀`. -/
  obtain ⟨k₀, hk₀pos, hk₀x, hk₀cop, hpool₀⟩ := h3 _ _ _ _ hW Q.toFinset hQsub hQcard
  rw [hxceil] at hk₀x
  rw [hLmod] at hk₀cop
  have hk₀fuel : k₀ ≤ Q.prod ^ 5 := by
    have h1 : ((Q.prod ^ 5 : ℕ) : ℝ) ^ ((79 : ℝ) / 100) ≤ ((Q.prod ^ 5 : ℕ) : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at h1
    exact_mod_cast hk₀x.trans h1
  obtain ⟨hP₀nodup, hP₀fin⟩ := poolAlg_spec Q hQnodup hQprime sc.z k₀
  have hθk₀ : sc.θ ≤ (Alg.poolAlg Q (Q.prod ^ 5) sc.z k₀).1.length := by
    have hc : (sc.θ : ℝ) ≤ ((pool Q.toFinset sc.z k₀).card : ℝ) := hθhi.trans hpool₀
    rw [← hP₀fin, List.toFinset_card_of_nodup hP₀nodup] at hc
    exact_mod_cast hc
  have hcop₀ : (Alg.coprimeTo Q k₀).1 = true :=
    (coprimeTo_spec Q hQnodup hQprime k₀).mpr hk₀cop
  obtain ⟨k, P, hscan, hk1, hkk₀, hkcop, hθP, hPdef, hscancost⟩ :=
    scan_spec Q (Q.prod ^ 5) sc.z sc.θ k₀ (Q.prod ^ 5) hk₀pos hk₀fuel ⟨hcop₀, hθk₀⟩
  have hkpos : 0 < k := hk1
  have hkcopL : k.Coprime (Lmod Q.toFinset) := by
    rw [hLmod]; exact (coprimeTo_spec Q hQnodup hQprime k).mp hkcop
  obtain ⟨hPnodup, hPfin⟩ := poolAlg_spec Q hQnodup hQprime sc.z k
  rw [← hPdef] at hPnodup hPfin
  have hPlen : P.length = (pool Q.toFinset sc.z k).card := by
    rw [← hPfin, List.toFinset_card_of_nodup hPnodup]
  have hpoolk : (Real.log n) ^ (1.2 : ℝ) ≤ ((pool Q.toFinset sc.z k).card : ℝ) := by
    refine hθlo.trans ?_
    rw [← hPlen]; exact_mod_cast hθP
  /- Step 4: the extraction inputs, then `extract_spec`. -/
  obtain ⟨hL2, hN1, hpoolfacts, hsupply, hvebk⟩ :=
    h4 _ _ _ _ hW Q.toFinset hQsub hQcard k hkpos hkcopL hpoolk
  rw [hLmod] at hL2 hsupply hvebk
  rw [← hPlen] at hsupply
  rw [← hPfin] at hvebk
  have hPfacts : ∀ p ∈ P, p.Prime ∧ p ≤ Q.prod ^ 5 ∧ p.Coprime Q.prod := by
    intro p hp
    have := hpoolfacts p (by rw [← hPfin]; exact List.mem_toFinset.mpr hp)
    rwa [hxceil, hLmod] at this
  obtain ⟨m, S, hext, hSnodup, hSsubP, hSprod, hSmod, hnm, hmle⟩ :=
    extract_spec Q.prod n (Q.prod ^ 5) (Nstar Q.toFinset) P hL2 hn1 hN1 hPnodup
      (fun p hp => (hPfacts p hp).2.2) (fun p hp => (hPfacts p hp).1.two_le)
      (fun p hp => (hPfacts p hp).2.1) hvebk hsupply
  /- Step 5: the output is Carmichael, in `(n, n^{1+ε}]`. -/
  have hSprodF : ∏ p ∈ S.toFinset, p = S.prod := by
    rw [List.prod_toFinset _ hSnodup, List.map_id']
  have hSsub : S.toFinset ⊆ pool Q.toFinset sc.z k := by
    rw [← hPfin]
    intro p hp
    exact List.mem_toFinset.mpr (hSsubP p (List.mem_toFinset.mp hp))
  have hSne : S.toFinset.Nonempty := by
    rw [List.toFinset_nonempty_iff]
    rintro rfl
    simp only [List.prod_nil] at hSprod
    omega
  have hSmodF : (∏ p ∈ S.toFinset, p) ≡ 1 [MOD Lmod Q.toFinset] := by
    rw [hSprodF, hSprod, hLmod]; exact hSmod
  have hnmF : n < ∏ p ∈ S.toFinset, p := by rw [hSprodF, hSprod]; exact hnm
  have hmleF : ((∏ p ∈ S.toFinset, p : ℕ) : ℝ) ≤
      (n : ℝ) * (xceil Q.toFinset : ℝ) ^ (Nstar Q.toFinset : ℕ) := by
    rw [hSprodF, hSprod, hxceil]
    exact_mod_cast hmle
  obtain ⟨hprimeF, hcardF, hcarmF, hupperF⟩ :=
    h5 _ _ _ _ hW Q.toFinset hQsub hQcard k hkpos hkcopL S.toFinset hSsub hSne hSmodF hnmF hmleF
  have hSprime : ∀ p ∈ S, p.Prime := fun p hp => hprimeF p (List.mem_toFinset.mpr hp)
  have hS3 : 3 ≤ S.length := by
    rwa [List.toFinset_card_of_nodup hSnodup] at hcardF
  have hcarm : IsCarmichael m := by rwa [hSprodF, hSprod] at hcarmF
  have hupper : (m : ℝ) ≤ (n : ℝ) ^ (1 + ε) := by rwa [hSprodF, hSprod] at hupperF
  have hver : (Alg.verify m S).1 = true :=
    verify_spec m S hSnodup hSprime hS3 hSprod.symm hcarm
  /- The success path of `search`. -/
  have hsearch := search_success sc n Q k P m S (hR ▸ hlen) (by rw [hR, hQ]) hscan hext hver
  /- The cost. -/
  have hSx : ∀ p ∈ S, p ≤ Q.prod ^ 5 := fun p hp => (hPfacts p (hSsubP p hp)).2.1
  have hcost : (Alg.reservoir sc.z sc.z99 sc.y).2 + 2 * sc.T + 2
      + (Alg.scan Q (Q.prod ^ 5) sc.z sc.θ 1 (Q.prod ^ 5)).2
      + (Alg.extract Q.prod n P).2 + (Alg.verify m S).2
      ≤ costPieces sc.z sc.y sc.T Q.prod (Q.prod ^ 5) k P.length S.length := by
    have c2 := reservoir_cost sc.z sc.z99 sc.y
    have c4 := extract_cost Q.prod n P
    have c5 := verify_cost m (Q.prod ^ 5) S hSx
    rw [hQlen] at hscancost
    unfold costPieces
    omega
  have hLz : Q.prod ≤ sc.z ^ sc.T := by
    rw [← hQlen]
    exact List.prod_le_pow_card Q sc.z (fun q hq => (hQgood q hq).2)
  have hk79 : (k : ℝ) ≤ ((Q.prod ^ 5 : ℕ) : ℝ) ^ ((79 : ℝ) / 100) :=
    le_trans (by exact_mod_cast hkk₀) hk₀x
  have hP2T : P.length ≤ 2 ^ sc.T := by
    obtain ⟨hDnodup, hDfin⟩ := divisorsOf_spec Q hQnodup hQprime
    have h1 : (pool Q.toFinset sc.z k).card ≤ (Lmod Q.toFinset).divisors.card := by
      unfold pool
      exact Finset.card_image_le.trans (Finset.card_filter_le _ _)
    have h2 : (Lmod Q.toFinset).divisors.card = 2 ^ sc.T := by
      rw [hLmod, ← hDfin, List.toFinset_card_of_nodup hDnodup, divisorsOf_length, hQlen]
    rw [hPlen]; omega
  have hS2T : S.length ≤ 2 ^ sc.T :=
    le_trans (List.Subperm.length_le (List.subperm_of_subset hSnodup hSsubP)) hP2T
  have hbudget := hb _ _ _ _ hW Q.prod (Q.prod ^ 5) k P.length S.length hLz rfl hk79 hP2T hS2T
  refine ⟨m, S, ?_, hSnodup, hSprime, hS3, hSprod.symm, hcarm, hnm, hupper, ?_⟩
  · rw [hsearch]
  · rw [hsearch]
    exact le_trans (by exact_mod_cast hcost) hbudget

/-- The same with no hypothesis (Route Z discharges AGP 3.1). -/
theorem search_successW (C₁ E : ℝ)
    (hE : 0 < E) (hEw : E ≤ Eweak) (h1000 : (1000 : ℝ) ≤ C₁)
    (h60 : (60 : ℝ) ≤ C₁ * gammaWeak) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ sc : Scales,
      InWindow C₁ E n sc.z sc.z99 sc.y sc.T →
      (Real.log n) ^ (1.2 : ℝ) ≤ (sc.θ : ℝ) → (sc.θ : ℝ) ≤ 16 * (Real.log n) ^ (1.2 : ℝ) →
      ∃ m : ℕ, ∃ S : List ℕ,
        (Alg.search sc n).1 = some (m, S) ∧
        S.Nodup ∧ (∀ p ∈ S, p.Prime) ∧ 3 ≤ S.length ∧ m = S.prod ∧
        IsCarmichael m ∧ n < m ∧ (m : ℝ) ≤ (n : ℝ) ^ (1 + ε) ∧
        ((Alg.search sc n).2 : ℝ) ≤ Real.exp (100 * ell2 n * ell3 n) :=
  search_successW_of assumptionsWeak_routeZ C₁ E hE hEw h1000 h60 ε hε

/-- The search at the paper's exact scales. `Alg.search` is a computable
`def`; only the scale constants `C₁alg`, `Eweak` are existential reals. -/
noncomputable def carmichaelSearch (n : ℕ) : Option (ℕ × List ℕ) × ℕ :=
  Alg.search (scalesOf C₁alg Eweak n) n

/-- The search at the exact scales, eventual form with both conclusions. -/
private lemma carmichaelSearch_eventually (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ∃ m : ℕ, ∃ S : List ℕ,
        (carmichaelSearch n).1 = some (m, S) ∧
        S.Nodup ∧ (∀ p ∈ S, p.Prime) ∧ 3 ≤ S.length ∧ m = S.prod ∧
        IsCarmichael m ∧ n < m ∧ (m : ℝ) ≤ (n : ℝ) ^ (1 + ε) ∧
        ((carmichaelSearch n).2 : ℝ) ≤ Real.exp (100 * ell2 n * ell3 n) := by
  have hC : (1 : ℝ) ≤ C₁alg := le_trans (by norm_num) thousand_le_C₁alg
  filter_upwards [
    search_successW C₁alg Eweak Eweak_pos le_rfl thousand_le_C₁alg
      sixty_le_C₁alg_mul_gammaWeak ε hε,
    tendsto_ell2_atTopA.eventually_ge_atTop 1,
    tendsto_ell3_atTopA.eventually_ge_atTop 1,
    eventually_ge_atTop 3] with n h h2 h3 hn3
  have hW := inWindow_exact C₁alg Eweak hC Eweak_pos Eweak_le_half n h2 h3
  -- `1 ≤ (log n)^{1.2}` since `n ≥ 3 > e`.
  have hlog1 : (1 : ℝ) ≤ Real.log n := by
    have h3r : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
    have hlog3 : (1 : ℝ) ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      exact le_trans Real.exp_one_lt_d9.le (by norm_num)
    exact hlog3.trans (Real.log_le_log (by norm_num) h3r)
  have hpow1 : (1 : ℝ) ≤ (Real.log n) ^ (1.2 : ℝ) := Real.one_le_rpow hlog1 (by norm_num)
  have hθlo : (Real.log n) ^ (1.2 : ℝ) ≤ ((⌈(Real.log n) ^ (1.2 : ℝ)⌉₊ : ℕ) : ℝ) :=
    Nat.le_ceil _
  have hθhi : ((⌈(Real.log n) ^ (1.2 : ℝ)⌉₊ : ℕ) : ℝ) ≤ 16 * (Real.log n) ^ (1.2 : ℝ) := by
    have := Nat.ceil_lt_add_one (by linarith only [hpow1] : (0 : ℝ) ≤ (Real.log n) ^ (1.2 : ℝ))
    linarith only [this, hpow1]
  exact h (scalesOf C₁alg Eweak n) hW hθlo hθhi

/-- **Mickey's theorem, algorithmic form, no hypotheses.** -/
theorem main_theorem_algorithmic :
    (∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ((carmichaelSearch n).2 : ℝ) ≤ Real.exp (C * ell2 n * ell3 n)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∃ m : ℕ, ∃ S : List ℕ,
          (carmichaelSearch n).1 = some (m, S) ∧
          S.Nodup ∧ (∀ p ∈ S, p.Prime) ∧ 3 ≤ S.length ∧ m = S.prod ∧
          IsCarmichael m ∧ n < m ∧ (m : ℝ) ≤ (n : ℝ) ^ (1 + ε)) := by
  refine ⟨⟨100, by norm_num, ?_⟩, fun ε hε => ?_⟩
  · obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (carmichaelSearch_eventually 1 one_pos)
    refine ⟨n₀, fun n hn => ?_⟩
    obtain ⟨m, S, -, -, -, -, -, -, -, -, hc⟩ := hn₀ n hn
    exact hc
  · obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (carmichaelSearch_eventually ε hε)
    refine ⟨n₀, fun n hn => ?_⟩
    obtain ⟨m, S, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hn₀ n hn
    exact ⟨m, S, h1, h2, h3, h4, h5, h6, h7, h8⟩

end Carmichael
