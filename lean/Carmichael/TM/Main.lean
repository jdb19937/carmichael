/-
The closing file of Route T (sortie T8b).

The machine `searchTM C₁ K` (T6's `searchF C₁ K` closed off into Mathlib's
`FinTM2`) computes `searchFun n = (Alg.search (scalesTM C₁ K n) n).1.getD (0, [])`
on every input `n` within `searchBound C₁ K n + 1` steps.  In the window the
step bound is `exp(O(ℓ₂ ℓ₃))`, hence T8a's `exists_timeFun_of_ExpB` produces a
time function of the input length bounded by
`exp(C · log N · log log N)`; Route A's `search_successW` supplies the
correctness clauses.  `carmichael_search_TM_of` packages everything for
`MainTM.lean`, generically in the output encoding so that the root-level
`encodeOutput` of `MainTM.lean` can be substituted with `rfl`.
-/
import Carmichael.TM.Step5
import Carmichael.TM.Overhead
import Carmichael.MainAlgorithmic

set_option autoImplicit false

namespace Carmichael.TM

open Filter Computability Turing

/-! ### The constants -/

/-- The window parameter `K = max 2 ⌈1 / Eweak⌉₊`, so that `2 ≤ K` and
`1 / K ≤ Eweak`. -/
noncomputable def Kc : ℕ := max 2 ⌈1 / Eweak⌉₊

theorem two_le_Kc : 2 ≤ Kc := le_max_left _ _

theorem Kc_pos_real : (0 : ℝ) < Kc := by
  have : (2 : ℝ) ≤ Kc := by exact_mod_cast two_le_Kc
  linarith

theorem inv_Kc_le_Eweak : 1 / (Kc : ℝ) ≤ Eweak := by
  have hpos := Eweak_pos
  have h1 : (⌈1 / Eweak⌉₊ : ℝ) ≤ Kc := by exact_mod_cast le_max_right 2 _
  have h2 : 1 / Eweak ≤ (⌈1 / Eweak⌉₊ : ℝ) := Nat.le_ceil _
  have h3 : 1 ≤ (Kc : ℝ) * Eweak := (div_le_iff₀ hpos).mp (h2.trans h1)
  rw [div_le_iff₀ Kc_pos_real]
  linarith

/-- The scale constant `C₁ = ⌈C₁alg⌉₊`, so that `1000 ≤ C₁` and
`60 ≤ C₁ · gammaWeak`. -/
noncomputable def C₁c : ℕ := ⌈C₁alg⌉₊

theorem C₁alg_le_C₁c : C₁alg ≤ (C₁c : ℝ) := Nat.le_ceil _

theorem thousand_le_C₁c_real : (1000 : ℝ) ≤ C₁c := thousand_le_C₁alg.trans C₁alg_le_C₁c

theorem thousand_le_C₁c : 1000 ≤ C₁c := by exact_mod_cast thousand_le_C₁c_real

theorem sixty_le_C₁c_mul_gammaWeak : (60 : ℝ) ≤ C₁c * gammaWeak :=
  sixty_le_C₁alg_mul_gammaWeak.trans
    (mul_le_mul_of_nonneg_right C₁alg_le_C₁c gammaWeak_pos.le)

/-! ### The machine -/

/-- The search algorithm at the machine's scales, as a function `ℕ → ℕ × List ℕ`
(`(0, [])` when the search fails, which never happens for `n` large). -/
noncomputable def searchFun (n : ℕ) : ℕ × List ℕ :=
  (Alg.search (scalesTM C₁c Kc n) n).1.getD (0, [])

/-- The Turing machine: `searchF C₁ K` with input stack `0`, output stack `1`. -/
def searchTM (C₁ K : ℕ) : FinTM2 := (searchF C₁ K).toFinTM2 0 1 default

/-- The machine outputs `encodeOutput (search …)` on input `encodeNatΓ' n` within
`searchBound C₁ K n + 1` steps, for every `n`. -/
noncomputable def searchTM_outputs (C₁ K n : ℕ) :
    TM2OutputsInTime (searchTM C₁ K) (encodeNatΓ' n)
      (some (encodeOutput ((Alg.search (scalesTM C₁ K n) n).1.getD (0, []))))
      (searchBound C₁ K n + 1) :=
  Frag.toFinTM2_outputs (searchF C₁ K) 0 1 default _ _ _ (searchF_runs C₁ K n default)

/-! ### The step bound in the window -/

/-- The threshold scale is at least `4`. -/
theorem four_le_scalesTM_θ (C₁ K n : ℕ) : 4 ≤ (scalesTM C₁ K n).θ := by
  show 4 ≤ 2 ^ ((6 * (Nat.log 2 (Nat.log 2 n + 1) + 1) + 4) / 5)
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ ((6 * (Nat.log 2 (Nat.log 2 n + 1) + 1) + 4) / 5) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)

/-- `Nat.log 2 s ≤ 2 log s` for `1 ≤ s`. -/
theorem natLog_le_two_log (s : ℕ) (hs : 1 ≤ s) : (Nat.log 2 s : ℝ) ≤ 2 * Real.log s := by
  obtain ⟨h, _⟩ := natLog_bridge s hs
  have hl2 := Real.log_two_gt_d9
  have h0 : (0 : ℝ) ≤ Nat.log 2 s := Nat.cast_nonneg _
  nlinarith

/-- In the window, the machine's step bound `searchBound C₁ K n + 1` is
`exp(O(ℓ₂ ℓ₃))`, given the algorithmic cost bound `exp(100 ℓ₂ ℓ₃)`. -/
theorem searchBound_ExpB (C₁ K : ℕ) (h1000 : 1000 ≤ C₁) (hK : 2 ≤ K)
    (hcost : ∀ᶠ n : ℕ in atTop,
      ((Alg.search (scalesTM C₁ K n) n).2 : ℝ) ≤ Real.exp (100 * ell2 n * ell3 n)) :
    ∀ᶠ n : ℕ in atTop, ExpB n 2000 ((searchBound C₁ K n + 1 : ℕ) : ℝ) := by
  have hC : (1000 : ℝ) ≤ C₁ := by exact_mod_cast h1000
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hE : (0 : ℝ) < 1 / (K : ℝ) := one_div_pos.mpr (by linarith)
  -- the constant `A` with `z + z99 + y + T + C₁ + K ≤ A ℓ₂ ℓ₃`
  have hlogA := tendsto_ell3_atTopT.eventually_ge_atTop (Real.log (37 * C₁ + K + 5))
  filter_upwards [scalesTM_inWindow C₁ K h1000 hK, window_base (C₁ : ℝ) (1 / K) hE hC,
    window_base_nat (C₁ : ℝ) (1 / K) hE hC, hcost, hlogA, eventually_ge_atTop 2]
    with n hW hb hbn hc hlogA hn2
  have hθ4 := four_le_scalesTM_θ C₁ K n
  -- generalize the scales
  unfold searchBound sbs sbn
  obtain ⟨sc, hsc⟩ : ∃ sc, scalesTM C₁ K n = sc := ⟨_, rfl⟩
  rw [hsc] at hW hc hθ4 ⊢
  obtain ⟨hw, _, hθhi⟩ := hW
  obtain ⟨h2, h3, hM12, hzE, _, _, hTE, _, _, _, _, hθ16⟩ := hb _ _ _ _ hw
  obtain ⟨h2Tn, _, hbitsn⟩ := hbn _ _ _ _ hw
  have hM : (1 : ℝ) ≤ ell2 n * ell3 n := by linarith only [hM12]
  /- Real-side size facts. -/
  have hl2 : (0 : ℝ) ≤ ell2 n := by linarith only [h2]
  have hl3 : (0 : ℝ) ≤ ell3 n := by linarith only [h3]
  have hl2M : ell2 n ≤ ell2 n * ell3 n := by nlinarith
  have hl3M : ell3 n ≤ ell2 n * ell3 n := by nlinarith
  have hz1 : (1 : ℝ) ≤ sc.z := by
    have := hw.z_lo
    have h' : (1000 : ℝ) * 12 ≤ C₁ * (ell2 n * ell3 n) :=
      mul_le_mul hC hM12 (by norm_num) (by linarith)
    nlinarith
  have hz99 : (sc.z99 : ℝ) ≤ 4 * sc.z := by
    have := hw.w_hi
    have h' : (sc.z : ℝ) ^ ((99 : ℝ) / 100) ≤ (sc.z : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
    rw [Real.rpow_one] at h'
    linarith
  have hy : (sc.y : ℝ) ≤ 4 * sc.z := by
    have := hw.y_hi
    have h' : (sc.z : ℝ) ^ ((1 : ℝ) - 1 / K) ≤ (sc.z : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)
    rw [Real.rpow_one] at h'
    linarith
  have hzhi : (sc.z : ℝ) ≤ 4 * C₁ * (ell2 n * ell3 n) := by
    have := hw.z_hi
    linarith
  have hT5 : (sc.T : ℝ) ≤ 5 * ell2 n := hw.T_hi
  -- the sum
  have hsum : ((sc.z + sc.z99 + sc.y + sc.T + C₁ + K : ℕ) : ℝ) ≤
      (37 * C₁ + K + 5) * (ell2 n * ell3 n) := by
    push_cast
    have hC1 : (C₁ : ℝ) ≤ C₁ * (ell2 n * ell3 n) := by nlinarith
    have hK1 : (K : ℝ) ≤ K * (ell2 n * ell3 n) := by nlinarith
    nlinarith
  have hs1 : 1 ≤ sc.z + sc.z99 + sc.y + sc.T + C₁ + K := by omega
  -- `log (sum) ≤ 3 ℓ₃`
  have hlogsum : Real.log ((sc.z + sc.z99 + sc.y + sc.T + C₁ + K : ℕ) : ℝ) ≤ 3 * ell3 n := by
    have hA : (1 : ℝ) ≤ 37 * C₁ + K + 5 := by linarith
    have hMpos : (0 : ℝ) < ell2 n * ell3 n := by linarith
    have hspos : (0 : ℝ) < ((sc.z + sc.z99 + sc.y + sc.T + C₁ + K : ℕ) : ℝ) := by
      exact_mod_cast hs1
    have h1 := Real.log_le_log hspos hsum
    rw [Real.log_mul (by linarith) hMpos.ne', Real.log_mul (by linarith) (by linarith)] at h1
    have h2' : Real.log (ell3 n) ≤ ell3 n - 1 := Real.log_le_sub_one_of_pos (by linarith)
    have h3' : Real.log (ell2 n) = ell3 n := rfl
    linarith
  -- bit bound `bs ≤ 7 ℓ₃`
  have hbs7 : ((Nat.log 2 (sc.z + sc.z99 + sc.y + sc.T + C₁ + K) + 2 : ℕ) : ℝ) ≤ 7 * ell3 n := by
    have := natLog_le_two_log _ hs1
    push_cast
    linarith
  have hbsE : ExpB n 7 ((Nat.log 2 (sc.z + sc.z99 + sc.y + sc.T + C₁ + K) + 2 : ℕ) : ℝ) := by
    rw [ExpB.def']
    have := Real.add_one_le_exp (7 * (ell2 n * ell3 n))
    linarith
  -- the exponent `T * bs + 1 ≤ 36 M`
  have hTbs : ((sc.T * (Nat.log 2 (sc.z + sc.z99 + sc.y + sc.T + C₁ + K) + 2) + 1 : ℕ) : ℝ) ≤
      36 * (ell2 n * ell3 n) := by
    push_cast
    push_cast at hbs7
    have := mul_le_mul hT5 hbs7 (by positivity) (by linarith)
    linarith
  have h2Tbs := ExpB.two_pow_nat hTbs
  -- bit bound `bn ≤ bits n + bits θ`
  have hθE : ExpB n 1 (sc.θ : ℝ) := ExpB.of_le hθhi hθ16
  have hbitsθ := ExpB.bits hM (by norm_num) hθE
  have hbn_le : Nat.log 2 (n + sc.θ) + 1 ≤ (Nat.log 2 n + 1) + (Nat.log 2 sc.θ + 1) := by
    have h1 : n + sc.θ ≤ n * sc.θ := Nat.add_le_mul hn2 (by omega)
    have h2 := Nat.log_mono_right (b := 2) h1
    have h3 := bits_mul_le n sc.θ
    omega
  have hbnE := ExpB.of_nat_le hbn_le (ExpB.add_nat hM (by norm_num) (by norm_num) hbitsn hbitsθ)
  /- The polynomial. -/
  have hTbsE := ExpB.mul_nat hTE hbsE
  have hsb1 := ExpB.succ_nat hM (by norm_num)
    (ExpB.add_nat hM (by norm_num) (by norm_num)
      (ExpB.add_nat hM (by norm_num) (by norm_num)
        (ExpB.mul_nat (ExpB.natCast hM 5) (ExpB.succ_nat hM (by norm_num) hTbsE)) hbsE) hbnE)
  have hT1 := ExpB.succ_nat hM (by norm_num) hTE
  have h2T2 := ExpB.add_nat hM (by norm_num) (by norm_num) h2Tn (ExpB.natCast hM 2)
  have hcoef := ExpB.add_nat hM (by norm_num) (by norm_num)
    (ExpB.mul_nat (ExpB.natCast hM 111) hT1) (ExpB.mul_nat (ExpB.natCast hM 13) h2T2)
  have hX := ExpB.add_nat hM (by norm_num) (by norm_num)
    (ExpB.add_nat hM (by norm_num) (by norm_num) (ExpB.mul_nat hcoef hsb1)
      (ExpB.mul_nat (ExpB.natCast hM 4) hTE)) (ExpB.natCast hM 200)
  have hB := ExpB.B hM (by norm_num) hX
  have hpoly := ExpB.mul_nat (ExpB.natCast hM 300)
    (ExpB.mul_nat (ExpB.mul_nat (ExpB.pow_nat h2Tbs 2) h2T2) hB)
  have hsteps := ExpB.succ_nat hM (by norm_num)
    (ExpB.steps_of_le hM (by norm_num) le_rfl (ExpB.of_cost hc) hpoly)
  exact ExpB.mono (by linarith only [hM12]) (by norm_num) hsteps

/-! ### The time function and the machine structure -/

/-- Transport of `TM2OutputsInTime` along equalities of the input and output
lists, weakening the step budget. -/
def outputs_of_eq {tm : FinTM2} {l₁ l₂ : List (tm.Γ tm.k₀)} {o₁ o₂ : Option (List (tm.Γ tm.k₁))}
    {m₁ m₂ : ℕ} (h : TM2OutputsInTime tm l₁ o₁ m₁) (hl : l₁ = l₂) (ho : o₁ = o₂) (hm : m₁ ≤ m₂) :
    TM2OutputsInTime tm l₂ o₂ m₂ := by
  subst hl ho
  exact ⟨h.toEvalsTo, h.steps_le_m.trans hm⟩

/-- The machine computes `searchFun` in time `exp(C log N log log N)` of the
input length. -/
theorem exists_computableInTime :
    ∃ h : TM2ComputableInTime encodingNatΓ'.encode encodeOutput searchFun,
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
        (h.time N : ℝ) ≤ Real.exp (C * Real.log N * Real.log (Real.log N)) := by
  have hcost : ∀ᶠ n : ℕ in atTop,
      ((Alg.search (scalesTM C₁c Kc n) n).2 : ℝ) ≤ Real.exp (100 * ell2 n * ell3 n) := by
    filter_upwards [search_successW (C₁c : ℝ) (1 / Kc) (one_div_pos.mpr Kc_pos_real)
      inv_Kc_le_Eweak thousand_le_C₁c_real sixty_le_C₁c_mul_gammaWeak 1 one_pos,
      scalesTM_inWindow C₁c Kc thousand_le_C₁c two_le_Kc] with n hs hW
    obtain ⟨hw, hθlo, hθhi⟩ := hW
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hb⟩ := hs _ hw hθlo hθhi
    exact hb
  obtain ⟨time, htime, N₀, hN₀⟩ := exists_timeFun_of_ExpB (fun n => searchBound C₁c Kc n + 1)
    2000 (by norm_num) (searchBound_ExpB C₁c Kc thousand_le_C₁c two_le_Kc hcost)
  refine ⟨{ tm := searchTM C₁c Kc
            inputAlphabet := Equiv.refl _
            outputAlphabet := Equiv.refl _
            time := time
            outputsFun := fun n => ?_ }, 2000, by norm_num, N₀, hN₀⟩
  have h := searchTM_outputs C₁c Kc n
  have hlen : (encodingNatΓ'.encode n).length = (encodeNat n).length := by
    simp [encodingNatΓ']
  exact outputs_of_eq h (List.map_id _).symm (congrArg some (List.map_id _).symm)
    (by rw [hlen]; exact htime n)

/-! ### Correctness -/

/-- For `n` large, `searchFun n` is a certified Carmichael number in `(n, n^{1+ε}]`. -/
theorem searchFun_spec (ε : ℝ) (hε : 0 < ε) : ∃ n₀ : ℕ, ∀ n ≥ n₀,
    (searchFun n).2.Nodup ∧ (∀ p ∈ (searchFun n).2, p.Prime) ∧ 3 ≤ (searchFun n).2.length ∧
    (searchFun n).1 = (searchFun n).2.prod ∧
    (1 < (searchFun n).1 ∧ ¬ (searchFun n).1.Prime ∧
      ∀ a : ℤ, ((searchFun n).1 : ℤ) ∣ a ^ (searchFun n).1 - a) ∧
    n < (searchFun n).1 ∧ ((searchFun n).1 : ℝ) ≤ (n : ℝ) ^ (1 + ε) := by
  rw [← Filter.eventually_atTop]
  filter_upwards [search_successW (C₁c : ℝ) (1 / Kc) (one_div_pos.mpr Kc_pos_real)
    inv_Kc_le_Eweak thousand_le_C₁c_real sixty_le_C₁c_mul_gammaWeak ε hε,
    scalesTM_inWindow C₁c Kc thousand_le_C₁c two_le_Kc] with n hs hW
  obtain ⟨hw, hθlo, hθhi⟩ := hW
  obtain ⟨m, S, hsearch, hnodup, hprime, h3, hprod, hcarm, hnm, hupper, _⟩ :=
    hs _ hw hθlo hθhi
  have hf : searchFun n = (m, S) := by
    unfold searchFun
    rw [hsearch]
    rfl
  rw [hf]
  exact ⟨hnodup, hprime, h3, hprod, hcarm, hnm, hupper⟩

/-! ### The final assembly -/

/-- The theorem of `MainTM.lean`, generic in the output encoding: any `eo` with
the body of `encodeOutput` qualifies. -/
theorem carmichael_search_TM_of (eo : ℕ × List ℕ → List Γ')
    (heo : ∀ m S, eo (m, S) = (encodeNat m).map inclusionBoolΓ' ++ Γ'.comma ::
      S.flatMap (fun p => (encodeNat p).map inclusionBoolΓ' ++ [Γ'.comma])) :
    ∃ (f : ℕ → ℕ × List ℕ)
      (h : TM2ComputableInTime encodingNatΓ'.encode eo f),
      (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
          (h.time N : ℝ) ≤ Real.exp (C * Real.log N * Real.log (Real.log N))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
          (f n).2.Nodup ∧ (∀ p ∈ (f n).2, p.Prime) ∧ 3 ≤ (f n).2.length ∧
          (f n).1 = (f n).2.prod ∧
          (1 < (f n).1 ∧ ¬ (f n).1.Prime ∧
            ∀ a : ℤ, ((f n).1 : ℤ) ∣ a ^ (f n).1 - a) ∧
          n < (f n).1 ∧ ((f n).1 : ℝ) ≤ (n : ℝ) ^ (1 + ε)) := by
  have heo' : eo = encodeOutput := by
    funext x
    obtain ⟨m, S⟩ := x
    rw [heo]
    rfl
  subst heo'
  obtain ⟨h, C, hC, N₀, hN₀⟩ := exists_computableInTime
  exact ⟨searchFun, h, ⟨C, hC, N₀, hN₀⟩, searchFun_spec⟩

end Carmichael.TM
