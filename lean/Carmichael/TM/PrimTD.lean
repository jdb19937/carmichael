import Carmichael.TM.Canon
import Carmichael.TM.Lists
import Carmichael.Algorithm

/-!
# Route T: trial-division primality and smoothness (`Alg.isPrimeTD`, `Alg.smoothTD`)

Machine fragments refining, EXACTLY, the Route A functions `Alg.primeGo`,
`Alg.isPrimeTD`, `Alg.divOut`, `Alg.smoothGo`, `Alg.smoothTD`
(`Carmichael/Algorithm.lean`).  Bool results are returned in `St.flag`, ℕ
results as `encodeNatΓ' value` on a stack; every loop keeps the Lean
function's fuel counter on a stack and has the same control flow.

## Stack allocation

Numbers are `encodeNatΓ' a ++ comma :: rest` (LSB on top).  Every stack is
restored except where a result is stated; scratch stacks need not be empty.
The canonical arithmetic wrappers need six pairwise distinct stacks, so the
persistent loop state doubles as their (restored) scratch:

| fragment | persistent state | scratch | total |
|---|---|---|---|
| `primeGoF xm xd xf a b c` | `m` on `xm` (peeked), `d` on `xd`, `fuel` on `xf` | `a b c` (+ `xm xd xf` as `mulC`/`modC` scratch) | 6 |
| `isPrimeTDF xm xd xf a b c` | `m` on `xm` (peeked, restored) | `xd xf a b c` | 6 |
| `divOutF xd xr xf a b c` | `d` on `xd` (kept), `r` on `xr` (replaced), `fuel` on `xf` (replaced by the leftover) | `a b c` (+ `xd xf xr` as `divmodC` scratch) | 6 |
| `smoothGoF xd xr xf xF a b c` | `d` on `xd`, `r` on `xr`, outer `fuel` on `xF`; `xf` receives the inner fuel (a copy of `r`) | `a b c` | 7 |
| `smoothTDF xy xr xd xf a b c` | `y` on `xy` (peeked, restored; the fuel `y - 1` is pushed on top of it), `k` on `xr` (CONSUMED) | `xd xf a b c` | 7 |

## Registers

`primeGoF`: the loop test reads `carry` ("continue"); the result is
`flag`.  Both are set by the `Frag.load'` that ends every branch of the
body, after the last register-clobbering fragment.  `divOutF`: loop test
`flag` (set by the test phase `divOutTest`, which ends with `isZero` +
`load'`/`skip`).  `smoothGoF`: loop test `!flag` (`isZero` on the outer
fuel is the last fragment of the body).  Nothing else is claimed about the
final state except the stated `flag` results.

## Step bounds

All in the form `((Alg.f args).2 + 1) * B (c * b + c')` for inputs
`< 2 ^ b`: `primeGoF`, `isPrimeTDF`: `B (3b + 7)`; `divOutF`: `B (3b + 4)`;
`smoothGoF`, `smoothTDF`: `B (4b + 10)`.  The outer loop of `smoothGo` has
data-dependent per-iteration cost, so it uses the budget form of the loop
rule, `Frag.loop_runs_budget` (proved here).
-/

namespace Carmichael.TM

open Turing Turing.TM2 Turing.TM2.Stmt Computability

/-! ### Iteration counts and unfolding lemmas for the Route A functions -/

/-- Number of body executions of the `primeGo` loop (mirrors the recursion;
equals the charged cost `(Alg.primeGo m d fuel).2`). -/
def primeIters (m : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | d, fuel + 1 =>
    if m < d * d then 1 else if m % d = 0 then 1 else primeIters m (d + 1) fuel + 1

theorem primeGo_zero (m d : ℕ) : Alg.primeGo m d 0 = (true, 0) := rfl

theorem primeGo_succ_lt {m d : ℕ} (f : ℕ) (h : m < d * d) :
    Alg.primeGo m d (f + 1) = (true, 1) := by
  simp [Alg.primeGo, h]

theorem primeGo_succ_dvd {m d : ℕ} (f : ℕ) (h : ¬ m < d * d) (h2 : m % d = 0) :
    Alg.primeGo m d (f + 1) = (false, 1) := by
  simp [Alg.primeGo, h, h2]

theorem primeGo_succ_next {m d : ℕ} (f : ℕ) (h : ¬ m < d * d) (h2 : m % d ≠ 0) :
    Alg.primeGo m d (f + 1) = ((Alg.primeGo m (d + 1) f).1, (Alg.primeGo m (d + 1) f).2 + 1) := by
  simp [Alg.primeGo, h, h2]

theorem primeIters_zero (m d : ℕ) : primeIters m d 0 = 0 := rfl

theorem primeIters_succ_lt {m d : ℕ} (f : ℕ) (h : m < d * d) : primeIters m d (f + 1) = 1 := by
  simp [primeIters, h]

theorem primeIters_succ_dvd {m d : ℕ} (f : ℕ) (h : ¬ m < d * d) (h2 : m % d = 0) :
    primeIters m d (f + 1) = 1 := by
  simp [primeIters, h, h2]

theorem primeIters_succ_next {m d : ℕ} (f : ℕ) (h : ¬ m < d * d) (h2 : m % d ≠ 0) :
    primeIters m d (f + 1) = primeIters m (d + 1) f + 1 := by
  simp [primeIters, h, h2]

theorem primeIters_eq (m d fuel : ℕ) : primeIters m d fuel = (Alg.primeGo m d fuel).2 := by
  induction fuel generalizing d with
  | zero => rfl
  | succ f ih =>
    by_cases h : m < d * d
    · rw [primeIters_succ_lt f h, primeGo_succ_lt f h]
    · by_cases h2 : m % d = 0
      · rw [primeIters_succ_dvd f h h2, primeGo_succ_dvd f h h2]
      · rw [primeIters_succ_next f h h2, primeGo_succ_next f h h2, ih]

theorem primeIters_le_fuel (m d fuel : ℕ) : primeIters m d fuel ≤ fuel := by
  induction fuel generalizing d with
  | zero => exact le_rfl
  | succ f ih =>
    by_cases h : m < d * d
    · rw [primeIters_succ_lt f h]; omega
    · by_cases h2 : m % d = 0
      · rw [primeIters_succ_dvd f h h2]; omega
      · rw [primeIters_succ_next f h h2]; have := ih (d + 1); omega

theorem primeIters_le_cost (m d fuel : ℕ) : primeIters m d fuel ≤ (Alg.primeGo m d fuel).2 + 1 := by
  rw [primeIters_eq]; omega

theorem primeIters_pos (m d : ℕ) {fuel : ℕ} (h : 0 < fuel) : 0 < primeIters m d fuel := by
  obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
  by_cases h1 : m < d * d
  · rw [primeIters_succ_lt f h1]; omega
  · by_cases h2 : m % d = 0
    · rw [primeIters_succ_dvd f h1 h2]; omega
    · rw [primeIters_succ_next f h1 h2]; omega

/-- After `i` non-exiting iterations the loop is at `(d + i, fuel - i)` with the
same result and `i` fewer remaining iterations. -/
theorem primeGo_shift (m d fuel : ℕ) (i : ℕ) (hi : i < primeIters m d fuel) :
    (Alg.primeGo m d fuel).1 = (Alg.primeGo m (d + i) (fuel - i)).1 ∧
    primeIters m d fuel = primeIters m (d + i) (fuel - i) + i := by
  induction i with
  | zero => simp
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hle := primeIters_le_fuel m (d + i) (fuel - i)
    obtain ⟨f, hf⟩ : ∃ f, fuel - i = f + 1 := ⟨fuel - i - 1, by omega⟩
    rw [hf] at h1 h2
    have hfi : fuel - (i + 1) = f := by omega
    rw [hfi, ← add_assoc]
    by_cases hlt : m < (d + i) * (d + i)
    · rw [primeIters_succ_lt f hlt] at h2; omega
    · by_cases hmod : m % (d + i) = 0
      · rw [primeIters_succ_dvd f hlt hmod] at h2; omega
      · rw [primeIters_succ_next f hlt hmod] at h2
        rw [primeGo_succ_next f hlt hmod] at h1
        exact ⟨h1, by omega⟩

/-- Number of body executions of the machine's `divOut` loop (one per
successful division; the failing test runs in the prelude / at the end of a
body): equals the charged cost. -/
def divOutIters (d : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | r, fuel + 1 => if r % d = 0 then divOutIters d (r / d) fuel + 1 else 0

theorem divOut_zero (d r : ℕ) : Alg.divOut d r 0 = (r, 0) := rfl

theorem divOut_succ_dvd {d r : ℕ} (f : ℕ) (h : r % d = 0) :
    Alg.divOut d r (f + 1) = ((Alg.divOut d (r / d) f).1, (Alg.divOut d (r / d) f).2 + 1) := by
  simp [Alg.divOut, h]

theorem divOut_succ_ndvd {d r : ℕ} (f : ℕ) (h : r % d ≠ 0) : Alg.divOut d r (f + 1) = (r, 0) := by
  simp [Alg.divOut, h]

theorem divOutIters_eq (d r fuel : ℕ) : divOutIters d r fuel = (Alg.divOut d r fuel).2 := by
  induction fuel generalizing r with
  | zero => rfl
  | succ f ih =>
    by_cases h : r % d = 0
    · simp only [divOutIters, h, if_true, divOut_succ_dvd f h, ih]
    · simp only [divOutIters, h, if_false, divOut_succ_ndvd f h]

theorem divOutIters_le_cost (d r fuel : ℕ) : divOutIters d r fuel ≤ (Alg.divOut d r fuel).2 + 1 := by
  rw [divOutIters_eq]; omega

theorem divOut_cost_pos_iff (d r fuel : ℕ) :
    0 < (Alg.divOut d r fuel).2 ↔ 0 < fuel ∧ r % d = 0 := by
  cases fuel with
  | zero => simp [divOut_zero]
  | succ f =>
    by_cases h : r % d = 0
    · rw [divOut_succ_dvd f h]; simp [h]
    · rw [divOut_succ_ndvd f h]; simp [h]

theorem divOut_fst_of_cost_zero {d r fuel : ℕ} (h : (Alg.divOut d r fuel).2 = 0) :
    (Alg.divOut d r fuel).1 = r := by
  cases fuel with
  | zero => rfl
  | succ f =>
    by_cases h' : r % d = 0
    · rw [divOut_succ_dvd f h'] at h; simp at h
    · rw [divOut_succ_ndvd f h']

theorem divOut_fst_le (d r fuel : ℕ) : (Alg.divOut d r fuel).1 ≤ r := by
  induction fuel generalizing r with
  | zero => exact le_rfl
  | succ f ih =>
    by_cases h : r % d = 0
    · rw [divOut_succ_dvd f h]
      exact (ih (r / d)).trans (Nat.div_le_self r d)
    · rw [divOut_succ_ndvd f h]

theorem divOut_cost_le_fuel (d r fuel : ℕ) : (Alg.divOut d r fuel).2 ≤ fuel := by
  induction fuel generalizing r with
  | zero => exact le_rfl
  | succ f ih =>
    by_cases h : r % d = 0
    · rw [divOut_succ_dvd f h]; have := ih (r / d); simp only; omega
    · rw [divOut_succ_ndvd f h]; simp

theorem smoothGo_zero (d r : ℕ) : Alg.smoothGo d r 0 = (r, 0) := rfl

theorem smoothGo_succ (d r f : ℕ) :
    Alg.smoothGo d r (f + 1) =
      ((Alg.smoothGo (d + 1) (Alg.divOut d r r).1 f).1,
        (Alg.smoothGo (d + 1) (Alg.divOut d r r).1 f).2 + (Alg.divOut d r r).2 + 1) := rfl

/-- Number of body executions of the `smoothGo` loop: exactly the fuel. -/
def smoothGoIters (_d _r fuel : ℕ) : ℕ := fuel

theorem smoothGoIters_le_cost (d r fuel : ℕ) :
    smoothGoIters d r fuel ≤ (Alg.smoothGo d r fuel).2 + 1 := by
  unfold smoothGoIters
  induction fuel generalizing d r with
  | zero => simp
  | succ f ih => rw [smoothGo_succ]; have := ih (d + 1) (Alg.divOut d r r).1; simp only; omega

theorem fuel_le_smoothGo_cost (d r fuel : ℕ) : fuel ≤ (Alg.smoothGo d r fuel).2 := by
  induction fuel generalizing d r with
  | zero => simp
  | succ f ih => rw [smoothGo_succ]; have := ih (d + 1) (Alg.divOut d r r).1; simp only; omega

theorem smoothGo_fst_le (d r fuel : ℕ) : (Alg.smoothGo d r fuel).1 ≤ r := by
  induction fuel generalizing d r with
  | zero => exact le_rfl
  | succ f ih =>
    rw [smoothGo_succ]
    exact (ih (d + 1) _).trans (divOut_fst_le d r r)

theorem isPrimeTD_of_lt {m : ℕ} (h : m < 2) : Alg.isPrimeTD m = (false, 1) := by
  simp [Alg.isPrimeTD, h]

theorem isPrimeTD_of_ge {m : ℕ} (h : ¬ m < 2) :
    Alg.isPrimeTD m = ((Alg.primeGo m 2 m).1, (Alg.primeGo m 2 m).2 + 1) := by
  simp [Alg.isPrimeTD, h]

theorem beq_one_eq_decide (a : ℕ) : (a == 1) = decide (a = 1) := by
  cases h : decide (a = 1) <;> simp_all

theorem smoothTD_eq (y k : ℕ) :
    Alg.smoothTD y k = (decide ((Alg.smoothGo 2 k (y - 1)).1 = 1), (Alg.smoothGo 2 k (y - 1)).2 + 1) := by
  simp [Alg.smoothTD, beq_one_eq_decide]

/-! ### Budget form of the loop rule

`Frag.loop_runs` has a uniform per-iteration bound; the outer loop of
`smoothGo` runs `divOut` whose cost varies per iteration.  Here the invariant
carries a budget `β` that each body execution consumes (`t + 1 + β' ≤ β`);
the total is `β₀ + 1`. -/

namespace Frag

theorem loop_runs_budget {c : St → Bool} {B : Frag} (I : ℕ → ℕ → St → Stacks → Prop) (n β₀ : ℕ)
    {v S}
    (h0 : I 0 β₀ v S)
    (hc : ∀ i < n, ∀ β v S, I i β v S → c v = true)
    (hn : ∀ β v S, I n β v S → c v = false)
    (hb : ∀ i < n, ∀ β v S, I i β v S →
      ∃ t β', t + 1 + β' ≤ β ∧ B.Runs v S (I (i + 1) β') t) :
    (loop c B).Runs v S (fun v S => (∃ β, I n β v S) ∧ c v = false) (β₀ + 1) := by
  constructor
  intro Λ M ι e hI
  suffices key : ∀ m i, i + m = n → ∀ β v S, I i β v S →
      ∃ n', n' ≤ β + 1 ∧ ∃ v' S',
        RunsTo M n' ⟨some (ι none), v, S⟩ ⟨some e, v', S'⟩ ∧ (∃ β, I n β v' S') ∧ c v' = false from
    key n 0 (by omega) β₀ v S h0
  intro m
  induction m with
  | zero =>
    intro i hi β v S hIv
    obtain rfl : i = n := by omega
    have hcv := hn β v S hIv
    refine ⟨1, by omega, v, S, ?_, ⟨β, hIv⟩, hcv⟩
    refine runsTo_succ ?_ (runsTo_zero M _)
    tm_step none [loop, hcv]
  | succ m ih =>
    intro i hi β v S hIv
    have hcv := hc i (by omega) β v S hIv
    obtain ⟨t, β', hβ, hB⟩ := hb i (by omega) β v S hIv
    obtain ⟨n₁, hn₁, v₁, S₁, hr₁, hI₁⟩ := hB.run M _ _ (loop_installed_body hI)
    obtain ⟨n₂, hn₂, v₂, S₂, hr₂, hI₂, hc₂⟩ := ih (i + 1) (by omega) β' v₁ S₁ hI₁
    refine ⟨n₁ + n₂ + 1, by omega, v₂, S₂, ?_, hI₂, hc₂⟩
    refine runsTo_succ ?_ (runsTo_trans hr₁ hr₂)
    tm_step none [loop, hcv, Function.comp]

end Frag

/-! ### Small helpers -/

/-- `predNum` on naturals without the `1 ≤ a` side condition (`0 ↦ 0`, as
`Nat.sub`). -/
theorem predNum_correct' {x s : K} (hxs : x ≠ s) (a : ℕ) (xr : List Γ') (v : St)
    (S : Stacks) (hS : S x = encodeNatΓ' a ++ .comma :: xr) :
    (predNum x s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧
        S' x = encodeNatΓ' (a - 1) ++ .comma :: xr ∧ S' s = S s ∧ ∀ k, k ≠ x → k ≠ s → S' k = S k)
      (2 * Nat.log 2 a + 5) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have h := predNum_runs hxs [] xr v S (by simpa using hS)
    refine Frag.runs_mono h (fun v' S' ⟨hfl, hcmp, hx, hs, hf⟩ => ⟨hfl, hcmp, ?_, hs, hf⟩) (by simp)
    rw [hx]; simp [predBits]
  · exact predNum_correct hxs a ha xr v S hS

/-- `moveEntry` on naturals. -/
theorem moveEntry_correct {src dst s : K} (hsd : src ≠ dst) (hss : src ≠ s) (hds : dst ≠ s)
    (a : ℕ) (sr : List Γ') (v : St) (S : Stacks) (hS : S src = encodeNatΓ' a ++ .comma :: sr) :
    (moveEntry src dst s).Runs v S (fun v' S' =>
        v'.flag = v.flag ∧ v'.cmp = v.cmp ∧ v'.carry = v.carry ∧
        S' src = sr ∧ S' dst = encodeNatΓ' a ++ .comma :: S dst ∧ S' s = S s ∧
        ∀ k, k ≠ src → k ≠ dst → k ≠ s → S' k = S k)
      (2 * Nat.log 2 a + 6) := by
  refine Frag.runs_mono (moveEntry_runs hsd hss hds (Computability.encodeNat a) sr v S hS)
    (fun _ _ h => h) ?_
  have := encodeNat_length_le a
  omega

theorem lt_pow_succ {a b : ℕ} (h : a < 2 ^ b) : a < 2 ^ (b + 1) :=
  h.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))

theorem B_three_add_four (b : ℕ) : B (3 * b + 4) = 27 * B b := by unfold B; ring

theorem B_three_add_seven (b : ℕ) : B (3 * b + 7) = 27 * B (b + 1) := by unfold B; ring

theorem B_four_add_ten (b : ℕ) : B (4 * b + 10) = 64 * B (b + 1) := by unfold B; ring

theorem B_succ_le (b : ℕ) : B b ≤ B (b + 1) := B_mono (by omega)

/-! ### `primeGo`: the trial-division loop

Stacks: `m` on `xm` (peeked), `d` on `xd`, `fuel` on `xf`; scratch `s t u`.
Body: `d * d` (two copies of `d`, `mulC` on `u`), compare with a copy of `m`
(`cmpFrag s u`, `cmp = compare m (d*d)`); if `m < d*d` stop with `true`;
else `m % d` (copies on `s`, `t`; `modC` leaves `m % d` on `s`), `isZero`; if
zero stop with `false`; else `incr d`, `predNum fuel`, `isZero fuel` and
continue iff the fuel is nonzero (result `true` if it is exhausted).
`carry` = continue, `flag` = result, both set by the final `load'` of each
branch. -/

/-- One iteration of `primeGo`. -/
def primeGoBody (xm xd xf s t u : K) : Frag :=
  (dup xd s t).seq ((dup xd t s).seq ((mulC s t u xf xm).seq ((dup xm s t).seq ((cmpFrag s u).seq
    (Frag.ite (fun v => decide (v.cmp = .lt))
      (Frag.load' (fun v => { v with carry := false, flag := true }))
      ((dup xm s t).seq ((dup xd t s).seq ((modC s t u xd xf xm).seq ((isZero s t).seq ((dropNum s).seq
        (Frag.ite (fun v => v.flag)
          (Frag.load' (fun v => { v with carry := false, flag := false }))
          ((incr xd s).seq ((predNum xf s).seq ((isZero xf s).seq
            (Frag.load' (fun v => { v with carry := !v.flag, flag := true }))))))))))))))))

/-- The trial-division loop: `isZero fuel`, set `carry := fuel ≠ 0`,
`flag := true`, then loop on `carry`. -/
def primeGoF (xm xd xf s t u : K) : Frag :=
  (isZero xf s).seq ((Frag.load' (fun v => { v with carry := !v.flag, flag := true })).seq
    (Frag.loop (fun v => v.carry) (primeGoBody xm xd xf s t u)))

/-- Loop invariant of `primeGoF` after `i` body executions: while running
(`i < primeIters`), `carry = true` and the stacks hold `(d + i, fuel - i)`;
at the exit (`i = primeIters`), `carry = false`, `flag` is the result, and
the stacks hold some `d' ≤ d + fuel`, `f' ≤ fuel`. -/
def PGInv (xm xd xf s t u : K) (m d fuel : ℕ) (mr dr fr : List Γ') (S₀ : Stacks)
    (i : ℕ) (v : St) (S : Stacks) : Prop :=
  i ≤ primeIters m d fuel ∧
  S xm = encodeNatΓ' m ++ .comma :: mr ∧ S s = S₀ s ∧ S t = S₀ t ∧ S u = S₀ u ∧
  (∀ k, k ≠ xm → k ≠ xd → k ≠ xf → k ≠ s → k ≠ t → k ≠ u → S k = S₀ k) ∧
  ((i < primeIters m d fuel ∧ v.carry = true ∧
      S xd = encodeNatΓ' (d + i) ++ .comma :: dr ∧ S xf = encodeNatΓ' (fuel - i) ++ .comma :: fr) ∨
   (i = primeIters m d fuel ∧ v.carry = false ∧ v.flag = (Alg.primeGo m d fuel).1 ∧
      ∃ d' f', d' ≤ d + fuel ∧ f' ≤ fuel ∧
        S xd = encodeNatΓ' d' ++ .comma :: dr ∧ S xf = encodeNatΓ' f' ++ .comma :: fr))

theorem primeGoBody_runs {xm xd xf s t u : K} (hmd : xm ≠ xd) (hmf : xm ≠ xf) (hms : xm ≠ s)
    (hmt : xm ≠ t) (hmu : xm ≠ u) (hdf : xd ≠ xf) (hds : xd ≠ s) (hdt : xd ≠ t) (hdu : xd ≠ u)
    (hfs : xf ≠ s) (hft : xf ≠ t) (hfu : xf ≠ u) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (m d fuel : ℕ) (hd : 1 ≤ d) (b : ℕ) (hm : m < 2 ^ b) (hdb : d < 2 ^ b) (hfb : fuel < 2 ^ b)
    (mr dr fr : List Γ') (S₀ : Stacks) (i : ℕ) (hi : i < primeIters m d fuel) (v : St) (S : Stacks)
    (hI : PGInv xm xd xf s t u m d fuel mr dr fr S₀ i v S) :
    (primeGoBody xm xd xf s t u).Runs v S (PGInv xm xd xf s t u m d fuel mr dr fr S₀ (i + 1))
      (13 * B (b + 1) + 3) := by
  have hdm := hmd.symm
  have hfm := hmf.symm
  have hsm := hms.symm
  have htm := hmt.symm
  have hum := hmu.symm
  have hfd := hdf.symm
  have hsd := hds.symm
  have htd := hdt.symm
  have hud := hdu.symm
  have hsf := hfs.symm
  have htf := hft.symm
  have huf := hfu.symm
  have hts := hst.symm
  have hus := hsu.symm
  have hut := htu.symm
  obtain ⟨-, hSm, hSs, hSt, hSu, hF, hph⟩ := hI
  rcases hph with ⟨-, -, hSd, hSf⟩ | ⟨heq, -⟩
  swap
  · omega
  obtain ⟨hsh1, hsh2⟩ := primeGo_shift m d fuel i hi
  have hle := primeIters_le_fuel m (d + i) (fuel - i)
  have hle' := primeIters_le_fuel m d fuel
  obtain ⟨f, hf⟩ : ∃ f, fuel - i = f + 1 := ⟨fuel - i - 1, by omega⟩
  rw [hf] at hsh1 hsh2 hSf
  have hfi : fuel - (i + 1) = f := by omega
  have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
  have hd'b : d + i < 2 ^ (b + 1) := by omega
  have hd'1 : 1 ≤ d + i := by omega
  have hmb1 := lt_pow_succ hm
  have hB1 := one_le_B (b + 1)
  have hBb := B_succ_le b
  -- 1. dup xd s t : s := d + i
  have h1 := dup_le_B hds hdt hst (d + i) (b + 1) hd'b dr v S hSd
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 12 * B (b + 1) + 3) h1
    fun v₁ S₁ ⟨hd₁, hs₁, ht₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 2. dup xd t s : t := d + i
  have h2' := dup_le_B hdt hds hts (d + i) (b + 1) hd'b dr v₁ S₁ (by rw [hd₁, hSd])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 11 * B (b + 1) + 3) h2'
    fun v₂ S₂ ⟨hd₂, ht₂, hs₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. mulC s t u xf xm : u := (d + i) * (d + i)
  have hs₂' : S₂ s = encodeNatΓ' (d + i) ++ .comma :: S s := by rw [hs₂, hs₁]
  have ht₂' : S₂ t = encodeNatΓ' (d + i) ++ .comma :: S t := by rw [ht₂, ht₁]
  have h3 := mulC_le_B hst hsu hsf hsm htu htf htm huf hum hfm (d + i) (d + i) (b + 1) hd'b hd'b
    (S s) (S t) v₂ S₂ hs₂' ht₂'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 10 * B (b + 1) + 3) h3
    fun v₃ S₃ ⟨hs₃, ht₃, hu₃, hf₃, hm₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 4. dup xm s t : s := m
  have hm₃' : S₃ xm = encodeNatΓ' m ++ .comma :: mr := by
    rw [hm₃, hF₂ xm hmd hmt hms, hF₁ xm hmd hms hmt, hSm]
  have h4 := dup_le_B hms hmt hst m (b + 1) hmb1 mr v₃ S₃ hm₃'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 9 * B (b + 1) + 3) h4
    fun v₄ S₄ ⟨hm₄, hs₄, ht₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 5. cmpFrag s u : cmp := compare m ((d + i) * (d + i))
  have hu₂ : S₂ u = S u := by rw [hF₂ u hud hut hus, hF₁ u hud hus hut]
  have hs₄' : S₄ s = encodeNatΓ' m ++ .comma :: S s := by rw [hs₄, hs₃]
  have hu₄ : S₄ u = encodeNatΓ' ((d + i) * (d + i)) ++ .comma :: S u := by
    rw [hF₄ u hum hus hut, hu₃, hu₂]
  have h5 := cmp_correct hsu m ((d + i) * (d + i)) (S s) (S u) v₄ S₄ hs₄' hu₄
  have hcmpb : 4 * (Nat.log 2 m + Nat.log 2 ((d + i) * (d + i)) + 1) ≤ B (b + 1) := by
    have hlm := log_le_of_lt_pow hm
    have hdd : (d + i) * (d + i) < 2 ^ (2 * (b + 1)) := by
      rw [two_mul, pow_add]; exact Nat.mul_lt_mul'' hd'b hd'b
    have hld := log_le_of_lt_pow hdd
    apply le_B_of_le_linear; omega
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 8 * B (b + 1) + 3) h5
    fun v₅ S₅ ⟨hcmp₅, hs₅, hu₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  have hm₅ : S₅ xm = encodeNatΓ' m ++ .comma :: mr := by rw [hF₅ xm hms hmu, hm₄, hm₃']
  have hd₅ : S₅ xd = encodeNatΓ' (d + i) ++ .comma :: dr := by
    rw [hF₅ xd hds hdu, hF₄ xd hdm hds hdt, hF₃ xd hds hdt hdu hdf hdm, hd₂, hd₁, hSd]
  have hf₅ : S₅ xf = encodeNatΓ' (f + 1) ++ .comma :: fr := by
    rw [hF₅ xf hfs hfu, hF₄ xf hfm hfs hft, hf₃, hF₂ xf hfd hft hfs, hF₁ xf hfd hfs hft, hSf]
  have ht₅ : S₅ t = S t := by rw [hF₅ t hts htu, ht₄, ht₃]
  have hF₅' : ∀ k, k ≠ xm → k ≠ xd → k ≠ xf → k ≠ s → k ≠ t → k ≠ u → S₅ k = S k := by
    intro k hkm hkd hkf hks hkt hku
    rw [hF₅ k hks hku, hF₄ k hkm hks hkt, hF₃ k hks hkt hku hkf hkm, hF₂ k hkd hkt hks,
      hF₁ k hkd hks hkt]
  -- 6. branch on `m < d * d`
  refine Frag.runs_mono (Frag.ite_runs (t := 8 * B (b + 1) + 2) (fun hc => ?_) (fun hc => ?_))
    (fun _ _ h => h) (by omega)
  · -- stop, result true
    have hlt : m < (d + i) * (d + i) := by simpa [hcmp₅, compare_lt_iff_lt] using hc
    have hn1 := primeIters_succ_lt f hlt
    refine Frag.runs_mono (Frag.load'_runs _ v₅ S₅) (fun v₆ S₆ ⟨hv₆, hS₆⟩ => ?_) (by omega)
    rw [hv₆, hS₆]
    refine ⟨by omega, hm₅, hs₅.trans hSs, ht₅.trans hSt, hu₅.trans hSu,
      fun k hkm hkd hkf hks hkt hku => (hF₅' k hkm hkd hkf hks hkt hku).trans (hF k hkm hkd hkf hks hkt hku),
      Or.inr ⟨by omega, rfl, ?_, d + i, f + 1, by omega, by omega, hd₅, hf₅⟩⟩
    rw [hsh1, primeGo_succ_lt f hlt]
  · have hnlt : ¬ m < (d + i) * (d + i) := by simpa [hcmp₅, compare_lt_iff_lt] using hc
    -- 6a. dup xm s t : s := m
    have h6a := dup_le_B hms hmt hst m (b + 1) hmb1 mr v₅ S₅ hm₅
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 7 * B (b + 1) + 2) h6a
      fun v₆ S₆ ⟨hm₆, hs₆, ht₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
    -- 6b. dup xd t s : t := d + i
    have hd₆ : S₆ xd = encodeNatΓ' (d + i) ++ .comma :: dr := by rw [hF₆ xd hdm hds hdt, hd₅]
    have h6b := dup_le_B hdt hds hts (d + i) (b + 1) hd'b dr v₆ S₆ hd₆
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 6 * B (b + 1) + 2) h6b
      fun v₇ S₇ ⟨hd₇, ht₇, hs₇, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
    -- 6c. modC s t u xd xf xm : s := m % (d + i)
    have hs₇' : S₇ s = encodeNatΓ' m ++ .comma :: S s := by rw [hs₇, hs₆, hs₅]
    have ht₇' : S₇ t = encodeNatΓ' (d + i) ++ .comma :: S t := by rw [ht₇, ht₆, ht₅]
    have h6c := modC_le_B hst hsu hsd hsf hsm htu htd htf htm hud huf hum hdf hdm hfm
      m (d + i) (b + 1) hd'1 hmb1 hd'b (S s) (S t) v₇ S₇ hs₇' ht₇'
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * B (b + 1) + 2) h6c
      fun v₈ S₈ ⟨hs₈, ht₈, hu₈, hd₈, hf₈, hm₈, hF₈⟩ => ?_) (fun _ _ h => h) (by omega)
    -- 6d. isZero s t : flag := (m % (d + i) = 0)
    have hmod_lt : m % (d + i) < 2 ^ (b + 1) := lt_of_le_of_lt (Nat.mod_le m _) hmb1
    have h6d := isZero_le_B hst (m % (d + i)) (b + 1) hmod_lt (S s) v₈ S₈ hs₈
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * B (b + 1) + 2) h6d
      fun v₉ S₉ ⟨hfl₉, _, hs₉, ht₉, hF₉⟩ => ?_) (fun _ _ h => h) (by omega)
    -- 6e. dropNum s
    have h6e := dropNum_le_B (m % (d + i)) (b + 1) hmod_lt (S s) v₉ S₉ (by rw [hs₉, hs₈])
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * B (b + 1) + 2) h6e
      fun v₁₀ S₁₀ ⟨hfl₁₀, _, _, hs₁₀, hF₁₀⟩ => ?_) (fun _ _ h => h) (by omega)
    have hm₁₀ : S₁₀ xm = encodeNatΓ' m ++ .comma :: mr := by
      rw [hF₁₀ xm hms, hF₉ xm hms hmt, hm₈, hF₇ xm hmd hmt hms, hm₆, hm₅]
    have hd₁₀ : S₁₀ xd = encodeNatΓ' (d + i) ++ .comma :: dr := by
      rw [hF₁₀ xd hds, hF₉ xd hds hdt, hd₈, hd₇, hd₆]
    have hf₁₀ : S₁₀ xf = encodeNatΓ' (f + 1) ++ .comma :: fr := by
      rw [hF₁₀ xf hfs, hF₉ xf hfs hft, hf₈, hF₇ xf hfd hft hfs, hF₆ xf hfm hfs hft, hf₅]
    have ht₁₀ : S₁₀ t = S t := by rw [hF₁₀ t hts, ht₉, ht₈]
    have hu₁₀ : S₁₀ u = S u := by
      rw [hF₁₀ u hus, hF₉ u hus hut, hu₈, hF₇ u hud hut hus, hF₆ u hum hus hut, hu₅]
    have hF₁₀' : ∀ k, k ≠ xm → k ≠ xd → k ≠ xf → k ≠ s → k ≠ t → k ≠ u → S₁₀ k = S k := by
      intro k hkm hkd hkf hks hkt hku
      rw [hF₁₀ k hks, hF₉ k hks hkt, hF₈ k hks hkt hku hkd hkf hkm, hF₇ k hkd hkt hks,
        hF₆ k hkm hks hkt, hF₅' k hkm hkd hkf hks hkt hku]
    have hfl : v₁₀.flag = decide (m % (d + i) = 0) := by rw [hfl₁₀, hfl₉]
    -- 6f. branch on `m % d = 0`
    refine Frag.runs_mono (Frag.ite_runs (t := 3 * B (b + 1) + 1) (fun hc2 => ?_) (fun hc2 => ?_))
      (fun _ _ h => h) (by omega)
    · -- stop, result false
      have hmod : m % (d + i) = 0 := by simpa [hfl] using hc2
      have hn1 := primeIters_succ_dvd f hnlt hmod
      refine Frag.runs_mono (Frag.load'_runs _ v₁₀ S₁₀) (fun v' S' ⟨hv', hS'⟩ => ?_) (by omega)
      rw [hv', hS']
      refine ⟨by omega, hm₁₀, hs₁₀.trans hSs, ht₁₀.trans hSt, hu₁₀.trans hSu,
        fun k hkm hkd hkf hks hkt hku =>
          (hF₁₀' k hkm hkd hkf hks hkt hku).trans (hF k hkm hkd hkf hks hkt hku),
        Or.inr ⟨by omega, rfl, ?_, d + i, f + 1, by omega, by omega, hd₁₀, hf₁₀⟩⟩
      rw [hsh1, primeGo_succ_dvd f hnlt hmod]
    · -- continue
      have hmod : m % (d + i) ≠ 0 := by simpa [hfl] using hc2
      have hn1 := primeIters_succ_next f hnlt hmod
      have hpg := primeGo_succ_next f hnlt hmod
      -- incr xd s
      have h7 := incr_le_B hds (d + i) (b + 1) hd'b dr v₁₀ S₁₀ hd₁₀
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B (b + 1) + 1) h7
        fun v₁₁ S₁₁ ⟨_, _, _, hd₁₁, hs₁₁, hF₁₁⟩ => ?_) (fun _ _ h => h) (by omega)
      -- predNum xf s
      have h8 := predNum_le_B hfs (f + 1) b (by omega) (by omega) fr v₁₁ S₁₁
        (by rw [hF₁₁ xf hfd hfs, hf₁₀])
      refine Frag.runs_mono (Frag.seq_runs (t₂ := B (b + 1) + 1) h8
        fun v₁₂ S₁₂ ⟨_, _, hf₁₂, hs₁₂, hF₁₂⟩ => ?_) (fun _ _ h => h) (by omega)
      -- isZero xf s
      rw [Nat.add_sub_cancel] at hf₁₂
      have h9 := isZero_le_B hfs f b (by omega) fr v₁₂ S₁₂ hf₁₂
      refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) h9
        fun v₁₃ S₁₃ ⟨hfl₁₃, _, hf₁₃, hs₁₃, hF₁₃⟩ => ?_) (fun _ _ h => h) (by omega)
      -- load'
      refine Frag.runs_mono (Frag.load'_runs _ v₁₃ S₁₃) (fun v' S' ⟨hv', hS'⟩ => ?_) le_rfl
      rw [hv', hS']
      have hd₁₃ : S₁₃ xd = encodeNatΓ' (d + i + 1) ++ .comma :: dr := by
        rw [hF₁₃ xd hdf hds, hF₁₂ xd hdf hds, hd₁₁]
      have hf₁₃' : S₁₃ xf = encodeNatΓ' f ++ .comma :: fr := by rw [hf₁₃, hf₁₂]
      have hm₁₃ : S₁₃ xm = encodeNatΓ' m ++ .comma :: mr := by
        rw [hF₁₃ xm hmf hms, hF₁₂ xm hmf hms, hF₁₁ xm hmd hms, hm₁₀]
      have hs₁₃' : S₁₃ s = S₀ s := by rw [hs₁₃, hs₁₂, hs₁₁, hs₁₀, hSs]
      have ht₁₃ : S₁₃ t = S₀ t := by rw [hF₁₃ t htf hts, hF₁₂ t htf hts, hF₁₁ t htd hts, ht₁₀, hSt]
      have hu₁₃ : S₁₃ u = S₀ u := by rw [hF₁₃ u huf hus, hF₁₂ u huf hus, hF₁₁ u hud hus, hu₁₀, hSu]
      have hF₁₃' : ∀ k, k ≠ xm → k ≠ xd → k ≠ xf → k ≠ s → k ≠ t → k ≠ u → S₁₃ k = S₀ k := by
        intro k hkm hkd hkf hks hkt hku
        rw [hF₁₃ k hkf hks, hF₁₂ k hkf hks, hF₁₁ k hkd hks, hF₁₀' k hkm hkd hkf hks hkt hku,
          hF k hkm hkd hkf hks hkt hku]
      refine ⟨by omega, hm₁₃, hs₁₃', ht₁₃, hu₁₃, hF₁₃', ?_⟩
      by_cases hf0 : f = 0
      · subst hf0
        rw [primeIters_zero] at hn1
        refine Or.inr ⟨by omega, by simp [hfl₁₃], ?_, d + i + 1, 0, by omega, by omega, hd₁₃, hf₁₃'⟩
        simp only
        rw [hsh1, hpg, primeGo_zero]
      · refine Or.inl ⟨?_, by simp [hfl₁₃, hf0], ?_, ?_⟩
        · have := primeIters_pos m (d + i + 1) (Nat.pos_of_ne_zero hf0); omega
        · rw [hd₁₃, Nat.add_assoc]
        · rw [hfi, hf₁₃']

theorem primeGoF_le_B {xm xd xf s t u : K} (hmd : xm ≠ xd) (hmf : xm ≠ xf) (hms : xm ≠ s)
    (hmt : xm ≠ t) (hmu : xm ≠ u) (hdf : xd ≠ xf) (hds : xd ≠ s) (hdt : xd ≠ t) (hdu : xd ≠ u)
    (hfs : xf ≠ s) (hft : xf ≠ t) (hfu : xf ≠ u) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (m d fuel : ℕ) (hd : 1 ≤ d) (b : ℕ) (hm : m < 2 ^ b) (hdb : d < 2 ^ b) (hfb : fuel < 2 ^ b)
    (mr dr fr : List Γ') (v : St) (S : Stacks)
    (hSm : S xm = encodeNatΓ' m ++ .comma :: mr) (hSd : S xd = encodeNatΓ' d ++ .comma :: dr)
    (hSf : S xf = encodeNatΓ' fuel ++ .comma :: fr) :
    (primeGoF xm xd xf s t u).Runs v S (fun v' S' =>
        v'.flag = (Alg.primeGo m d fuel).1 ∧ S' xm = S xm ∧
        (∃ d' f', d' ≤ d + fuel ∧ f' ≤ fuel ∧
          S' xd = encodeNatΓ' d' ++ .comma :: dr ∧ S' xf = encodeNatΓ' f' ++ .comma :: fr) ∧
        S' s = S s ∧ S' t = S t ∧ S' u = S u ∧
        ∀ k, k ≠ xm → k ≠ xd → k ≠ xf → k ≠ s → k ≠ t → k ≠ u → S' k = S k)
      (((Alg.primeGo m d fuel).2 + 1) * B (3 * b + 7)) := by
  have hfm := hmf.symm
  have hsm := hms.symm
  have hsd := hds.symm
  have hsf := hfs.symm
  have htf := hft.symm
  have hts := hst.symm
  have huf := hfu.symm
  have hus := hsu.symm
  rw [← primeIters_eq, B_three_add_seven]
  have hB1 := one_le_B (b + 1)
  have hBb := B_succ_le b
  have hnB : primeIters m d fuel ≤ primeIters m d fuel * B (b + 1) :=
    Nat.le_mul_of_pos_right _ hB1
  -- stage 1: isZero xf s
  have h1 := isZero_le_B hfs fuel b hfb fr v S hSf
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := primeIters m d fuel * (13 * B (b + 1) + 3 + 1) + 1 + 1) h1
    fun v₁ S₁ ⟨hfl₁, _, hf₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h) (by nlinarith)
  -- stage 2: carry := fuel ≠ 0, flag := true
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := primeIters m d fuel * (13 * B (b + 1) + 3 + 1) + 1)
    (Frag.load'_runs _ v₁ S₁) fun v₂ S₂ ⟨hv₂, hS₂⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [hv₂, hS₂]
  -- stage 3: the loop
  have hm₁ : S₁ xm = encodeNatΓ' m ++ .comma :: mr := by rw [hF₁ xm hmf hms, hSm]
  have hd₁ : S₁ xd = encodeNatΓ' d ++ .comma :: dr := by rw [hF₁ xd hdf hds, hSd]
  have hf₁' : S₁ xf = encodeNatΓ' fuel ++ .comma :: fr := by rw [hf₁, hSf]
  have h0 : PGInv xm xd xf s t u m d fuel mr dr fr S 0
      { v₁ with carry := !v₁.flag, flag := true } S₁ := by
    refine ⟨Nat.zero_le _, hm₁, hs₁, hF₁ t htf hts, hF₁ u huf hus,
      fun k _ _ hkf hks _ _ => hF₁ k hkf hks, ?_⟩
    by_cases hfuel : fuel = 0
    · subst hfuel
      refine Or.inr ⟨by rw [primeIters_zero], by simp [hfl₁], by rw [primeGo_zero],
        d, 0, by omega, le_rfl, hd₁, hf₁'⟩
    · refine Or.inl ⟨primeIters_pos m d (Nat.pos_of_ne_zero hfuel), by simp [hfl₁, hfuel], ?_, ?_⟩
      · rw [Nat.add_zero, hd₁]
      · rw [Nat.sub_zero, hf₁']
  have hloop := Frag.loop_runs (c := fun v => v.carry) (B := primeGoBody xm xd xf s t u)
    (PGInv xm xd xf s t u m d fuel mr dr fr S) (primeIters m d fuel) (13 * B (b + 1) + 3)
    (v := { v₁ with carry := !v₁.flag, flag := true }) (S := S₁) h0
    (fun i hi w T ⟨_, _, _, _, _, _, hph⟩ => by
      rcases hph with ⟨_, hcar, _, _⟩ | ⟨heq, _⟩
      · exact hcar
      · omega)
    (fun w T ⟨_, _, _, _, _, _, hph⟩ => by
      rcases hph with ⟨hlt, _, _, _⟩ | ⟨_, hcar, _⟩
      · omega
      · exact hcar)
    (fun i hi w T hI => primeGoBody_runs hmd hmf hms hmt hmu hdf hds hdt hdu hfs hft hfu hst hsu htu
      m d fuel hd b hm hdb hfb mr dr fr S i hi w T hI)
  refine Frag.runs_mono hloop (fun v' S' ⟨⟨_, hm', hs', ht', hu', hF', hph⟩, _⟩ => ?_) le_rfl
  rcases hph with ⟨hlt, _, _, _⟩ | ⟨_, _, hfl', d', f', hd', hf', hSd', hSf'⟩
  · omega
  · exact ⟨hfl', hm'.trans hSm.symm, ⟨d', f', hd', hf', hSd', hSf'⟩, hs', ht', hu', hF'⟩

/-! ### `isPrimeTD` -/

/-- `flag := isPrimeTD m` for `m` on `xm` (restored).  `m < 2` by
`pushNum 2` + a copy of `m` + `cmpFrag`; otherwise `primeGoF` with `d := 2`,
`fuel := m` (a copy), then the two counters are dropped. -/
def isPrimeTDF (xm xd xf s t u : K) : Frag :=
  (pushNum s 2).seq ((dup xm t u).seq ((cmpFrag t s).seq
    (Frag.ite (fun v => decide (v.cmp = .lt))
      (Frag.load' (fun v => { v with flag := false }))
      ((pushNum xd 2).seq ((dup xm xf s).seq ((primeGoF xm xd xf s t u).seq
        ((dropNum xd).seq (dropNum xf))))))))

theorem isPrimeTDF_le_B {xm xd xf s t u : K} (hmd : xm ≠ xd) (hmf : xm ≠ xf) (hms : xm ≠ s)
    (hmt : xm ≠ t) (hmu : xm ≠ u) (hdf : xd ≠ xf) (hds : xd ≠ s) (hdt : xd ≠ t) (hdu : xd ≠ u)
    (hfs : xf ≠ s) (hft : xf ≠ t) (hfu : xf ≠ u) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (m : ℕ) (b : ℕ) (hm : m < 2 ^ b) (mr : List Γ') (v : St) (S : Stacks)
    (hSm : S xm = encodeNatΓ' m ++ .comma :: mr) :
    (isPrimeTDF xm xd xf s t u).Runs v S (fun v' S' =>
        v'.flag = (Alg.isPrimeTD m).1 ∧ S' xm = S xm ∧ S' xd = S xd ∧ S' xf = S xf ∧
        S' s = S s ∧ S' t = S t ∧ S' u = S u ∧
        ∀ k, k ≠ xm → k ≠ xd → k ≠ xf → k ≠ s → k ≠ t → k ≠ u → S' k = S k)
      (((Alg.isPrimeTD m).2 + 1) * B (3 * b + 7)) := by
  have hdm := hmd.symm
  have hfm := hmf.symm
  have hsm := hms.symm
  have htm := hmt.symm
  have hum := hmu.symm
  have hfd := hdf.symm
  have hsd := hds.symm
  have htd := hdt.symm
  have hud := hdu.symm
  have hsf := hfs.symm
  have htf := hft.symm
  have huf := hfu.symm
  have hts := hst.symm
  have hus := hsu.symm
  have hut := htu.symm
  have hB1 := one_le_B (b + 1)
  have hBb := B_succ_le b
  have hlin : 4 * b + 40 ≤ B (b + 1) := le_B_of_le_linear (by omega)
  have hl2 : Nat.log 2 2 ≤ 2 := log_le_of_lt_pow (by norm_num)
  have hlm := log_le_of_lt_pow hm
  rw [B_three_add_seven]
  -- stage 1: pushNum s 2
  have h1 := pushNum_runs s 2 v S
  -- stage 2: dup xm t u
  have hm₁ : Function.update S s (encodeNatΓ' 2 ++ .comma :: S s) xm = encodeNatΓ' m ++ .comma :: mr := by
    simp [Function.update_of_ne hms, hSm]
  by_cases hm2 : m < 2
  · rw [isPrimeTD_of_lt hm2]
    simp only
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + 4 * (Nat.log 2 m + Nat.log 2 2 + 1) + 2) h1
      fun v₁ S₁ ⟨hv₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
    have hS₁ : S₁ = Function.update S s (encodeNatΓ' 2 ++ .comma :: S s) := by
      funext k; by_cases hk : k = s
      · subst hk; simp [hs₁]
      · rw [hF₁ k hk, Function.update_of_ne hk]
    rw [hv₁, hS₁]
    have h2 := dup_le_B hmt hmu htu m b hm mr v _ hm₁
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * (Nat.log 2 m + Nat.log 2 2 + 1) + 2) h2
      fun v₂ S₂ ⟨hm₂, ht₂, hu₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
    -- stage 3: cmpFrag t s
    have hs₂ : S₂ s = encodeNatΓ' 2 ++ .comma :: S s := by rw [hF₂ s hsm hst hsu]; simp
    have ht₂' : S₂ t = encodeNatΓ' m ++ .comma :: S t := by
      rw [ht₂]; simp [Function.update_of_ne hts]
    have h3 := cmp_correct hts m 2 (S t) (S s) v₂ S₂ ht₂' hs₂
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 2) h3
      fun v₃ S₃ ⟨hcmp₃, ht₃, hs₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
    have hc : decide (v₃.cmp = Ordering.lt) = true := by simp [hcmp₃, compare_lt_iff_lt, hm2]
    refine Frag.runs_mono (Frag.ite_runs_true (t := 1) hc (Frag.load'_runs _ v₃ S₃))
      (fun v₄ S₄ ⟨hv₄, hS₄⟩ => ?_) (by omega)
    rw [hv₄, hS₄]
    refine ⟨rfl, ?_, ?_, ?_, hs₃, ht₃, ?_, ?_⟩
    · rw [hF₃ xm hmt hms, hm₂]; simp [Function.update_of_ne hms]
    · rw [hF₃ xd hdt hds, hF₂ xd hdm hdt hdu]; simp [Function.update_of_ne hds]
    · rw [hF₃ xf hft hfs, hF₂ xf hfm hft hfu]; simp [Function.update_of_ne hfs]
    · rw [hF₃ u hut hus, hu₂]; simp [Function.update_of_ne hus]
    · intro k hkm hkd hkf hks hkt hku
      rw [hF₃ k hkt hks, hF₂ k hkm hkt hku]; simp [Function.update_of_ne hks]
  · rw [isPrimeTD_of_ge hm2]
    simp only
    have h2b : 2 < 2 ^ b := by omega
    have h2b1 : 2 < 2 ^ (b + 1) := lt_pow_succ h2b
    have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
    have hmb1 := lt_pow_succ hm
    have hnB : (Alg.primeGo m 2 m).2 ≤ (Alg.primeGo m 2 m).2 * B (b + 1) :=
      Nat.le_mul_of_pos_right _ hB1
    refine Frag.runs_mono (Frag.seq_runs
      (t₂ := B b + 4 * (Nat.log 2 m + Nat.log 2 2 + 1) + 1 + (Nat.log 2 2 + 2) + B b +
        ((Alg.primeGo m 2 m).2 + 1) * (27 * B (b + 1)) + B (b + 1) + B b) h1
      fun v₁ S₁ ⟨hv₁, hs₁, hF₁⟩ => ?_) (fun _ _ h => h) (by nlinarith)
    have hS₁ : S₁ = Function.update S s (encodeNatΓ' 2 ++ .comma :: S s) := by
      funext k; by_cases hk : k = s
      · subst hk; simp [hs₁]
      · rw [hF₁ k hk, Function.update_of_ne hk]
    rw [hv₁, hS₁]
    have h2 := dup_le_B hmt hmu htu m b hm mr v _ hm₁
    refine Frag.runs_mono (Frag.seq_runs
      (t₂ := 4 * (Nat.log 2 m + Nat.log 2 2 + 1) + 1 + (Nat.log 2 2 + 2) + B b +
        ((Alg.primeGo m 2 m).2 + 1) * (27 * B (b + 1)) + B (b + 1) + B b) h2
      fun v₂ S₂ ⟨hm₂, ht₂, hu₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
    -- stage 3: cmpFrag t s
    have hs₂ : S₂ s = encodeNatΓ' 2 ++ .comma :: S s := by rw [hF₂ s hsm hst hsu]; simp
    have ht₂' : S₂ t = encodeNatΓ' m ++ .comma :: S t := by
      rw [ht₂]; simp [Function.update_of_ne hts]
    have h3 := cmp_correct hts m 2 (S t) (S s) v₂ S₂ ht₂' hs₂
    refine Frag.runs_mono (Frag.seq_runs
      (t₂ := 1 + (Nat.log 2 2 + 2) + B b + ((Alg.primeGo m 2 m).2 + 1) * (27 * B (b + 1)) +
        B (b + 1) + B b) h3
      fun v₃ S₃ ⟨hcmp₃, ht₃, hs₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
    have hc : decide (v₃.cmp = Ordering.lt) = false := by simp [hcmp₃, compare_lt_iff_lt, hm2]
    -- stacks after the comparison
    have hm₃ : S₃ xm = encodeNatΓ' m ++ .comma :: mr := by
      rw [hF₃ xm hmt hms, hm₂]; simp [Function.update_of_ne hms, hSm]
    have hd₃ : S₃ xd = S xd := by rw [hF₃ xd hdt hds, hF₂ xd hdm hdt hdu]; simp [Function.update_of_ne hds]
    have hf₃ : S₃ xf = S xf := by rw [hF₃ xf hft hfs, hF₂ xf hfm hft hfu]; simp [Function.update_of_ne hfs]
    have hu₃ : S₃ u = S u := by rw [hF₃ u hut hus, hu₂]; simp [Function.update_of_ne hus]
    have hF₃' : ∀ k, k ≠ xm → k ≠ xd → k ≠ xf → k ≠ s → k ≠ t → k ≠ u → S₃ k = S k := by
      intro k hkm hkd hkf hks hkt hku
      rw [hF₃ k hkt hks, hF₂ k hkm hkt hku]; simp [Function.update_of_ne hks]
    refine Frag.runs_mono (Frag.ite_runs_false
      (t := (Nat.log 2 2 + 2) + B b + ((Alg.primeGo m 2 m).2 + 1) * (27 * B (b + 1)) + B (b + 1) + B b)
      hc ?_) (fun _ _ h => h) (by omega)
    -- stage 4: pushNum xd 2
    refine Frag.runs_mono (Frag.seq_runs
      (t₂ := B b + ((Alg.primeGo m 2 m).2 + 1) * (27 * B (b + 1)) + B (b + 1) + B b)
      (pushNum_runs xd 2 v₃ S₃) fun v₄ S₄ ⟨hv₄, hd₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
    -- stage 5: dup xm xf s : fuel := m
    have hm₄ : S₄ xm = encodeNatΓ' m ++ .comma :: mr := by rw [hF₄ xm hmd, hm₃]
    have h5 := dup_le_B hmf hms hfs m b hm mr v₄ S₄ hm₄
    refine Frag.runs_mono (Frag.seq_runs
      (t₂ := ((Alg.primeGo m 2 m).2 + 1) * (27 * B (b + 1)) + B (b + 1) + B b) h5
      fun v₅ S₅ ⟨hm₅, hf₅, hs₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
    -- stage 6: primeGoF
    have hm₅' : S₅ xm = encodeNatΓ' m ++ .comma :: mr := by rw [hm₅, hm₄]
    have hd₅ : S₅ xd = encodeNatΓ' 2 ++ .comma :: S xd := by rw [hF₅ xd hdm hdf hds, hd₄, hd₃]
    have hf₅' : S₅ xf = encodeNatΓ' m ++ .comma :: S xf := by rw [hf₅, hF₄ xf hfd, hf₃]
    have h6 := primeGoF_le_B hmd hmf hms hmt hmu hdf hds hdt hdu hfs hft hfu hst hsu htu
      m 2 m (by norm_num) b hm h2b hm mr (S xd) (S xf) v₅ S₅ hm₅' hd₅ hf₅'
    rw [B_three_add_seven] at h6
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B (b + 1) + B b) h6
      fun v₆ S₆ ⟨hfl₆, hm₆, ⟨d', f', hd', hf', hd₆, hf₆⟩, hs₆, ht₆, hu₆, hF₆⟩ => ?_)
      (fun _ _ h => h) (by omega)
    -- stage 7: dropNum xd
    have h7 := dropNum_le_B d' (b + 1) (by omega) (S xd) v₆ S₆ hd₆
    refine Frag.runs_mono (Frag.seq_runs (t₂ := B b) h7
      fun v₇ S₇ ⟨hfl₇, _, _, hd₇, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
    -- stage 8: dropNum xf
    have h8 := dropNum_le_B f' b (by omega) (S xf) v₇ S₇ (by rw [hF₇ xf hfd, hf₆])
    refine Frag.runs_mono h8 (fun v₈ S₈ ⟨hfl₈, _, _, hf₈, hF₈⟩ => ⟨?_, ?_, ?_, hf₈, ?_, ?_, ?_, ?_⟩)
      (by omega)
    · rw [hfl₈, hfl₇, hfl₆]
    · rw [hF₈ xm hmf, hF₇ xm hmd, hm₆, hm₅', hSm]
    · rw [hF₈ xd hdf, hd₇]
    · rw [hF₈ s hsf, hF₇ s hsd, hs₆, hs₅, hF₄ s hsd, hs₃]
    · rw [hF₈ t htf, hF₇ t htd, ht₆, hF₅ t htm htf hts, hF₄ t htd, ht₃]
    · rw [hF₈ u huf, hF₇ u hud, hu₆, hF₅ u hum huf hus, hF₄ u hud, hu₃]
    · intro k hkm hkd hkf hks hkt hku
      rw [hF₈ k hkf, hF₇ k hkd, hF₆ k hkm hkd hkf hks hkt hku, hF₅ k hkm hkf hks, hF₄ k hkd,
        hF₃' k hkm hkd hkf hks hkt hku]

/-! ### `divOut`: divide `d` out of `r` while it divides

Stacks: `d` on `xd` (kept), `r` on `xr` (replaced by the result), `fuel` on
`xf` (replaced by the leftover fuel `fuel - cost`); scratch `s t u`.

The loop is test-first: the test phase `divOutTest` computes `r % d` and
`r / d` (copies of `r`, `d` on `s`, `t`; `divmodC` leaves the remainder on
`s` and the quotient on `u`), sets `flag := (r % d = 0 ∧ fuel ≠ 0)` and
leaves the quotient on `u`.  The body (run iff `flag`) replaces `r` by the
quotient, decrements the fuel and re-runs the test.  So the body runs
exactly `(Alg.divOut d r fuel).2` times (one per successful division), and
the final `dropNum u` discards the unused quotient. -/

/-- Test phase of `divOut`: `flag := (r % d = 0 ∧ fuel ≠ 0)`, quotient `r / d`
pushed on `u`. -/
def divOutTest (xd xr xf s t u : K) : Frag :=
  (dup xr s t).seq ((dup xd t s).seq ((divmodC s t u xd xf xr).seq ((isZero s t).seq ((dropNum s).seq
    (Frag.ite (fun v => v.flag)
      ((isZero xf s).seq (Frag.load' (fun v => { v with flag := !v.flag })))
      Frag.skip)))))

/-- Body of `divOut`: `r := r / d` (the quotient waiting on `u`), `fuel := fuel - 1`,
then the test phase again. -/
def divOutBody (xd xr xf s t u : K) : Frag :=
  (dropNum xr).seq ((moveEntry u xr s).seq ((predNum xf s).seq (divOutTest xd xr xf s t u)))

/-- `divOut d r fuel` on the machine. -/
def divOutF (xd xr xf s t u : K) : Frag :=
  (divOutTest xd xr xf s t u).seq
    ((Frag.loop (fun v => v.flag) (divOutBody xd xr xf s t u)).seq (dropNum u))

theorem divOutTest_le_B {xd xr xf s t u : K} (hdr : xd ≠ xr) (hdf : xd ≠ xf) (hds : xd ≠ s)
    (hdt : xd ≠ t) (hdu : xd ≠ u) (hrf : xr ≠ xf) (hrs : xr ≠ s) (hrt : xr ≠ t) (hru : xr ≠ u)
    (hfs : xf ≠ s) (hft : xf ≠ t) (hfu : xf ≠ u) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (d r f : ℕ) (hd : 1 ≤ d) (b : ℕ) (hdb : d < 2 ^ b) (hrb : r < 2 ^ b) (hfb : f < 2 ^ b)
    (dr rr fr : List Γ') (v : St) (S : Stacks)
    (hSd : S xd = encodeNatΓ' d ++ .comma :: dr) (hSr : S xr = encodeNatΓ' r ++ .comma :: rr)
    (hSf : S xf = encodeNatΓ' f ++ .comma :: fr) :
    (divOutTest xd xr xf s t u).Runs v S (fun v' S' =>
        v'.flag = (decide (r % d = 0) && !decide (f = 0)) ∧
        S' xd = S xd ∧ S' xr = S xr ∧ S' xf = S xf ∧ S' s = S s ∧ S' t = S t ∧
        S' u = encodeNatΓ' (r / d) ++ .comma :: S u ∧
        ∀ k, k ≠ xd → k ≠ xr → k ≠ xf → k ≠ s → k ≠ t → k ≠ u → S' k = S k)
      (6 * B b + 2) := by
  have hrd := hdr.symm
  have hfd := hdf.symm
  have hsd := hds.symm
  have htd := hdt.symm
  have hud := hdu.symm
  have hfr := hrf.symm
  have hsr := hrs.symm
  have htr := hrt.symm
  have hur := hru.symm
  have hsf := hfs.symm
  have htf := hft.symm
  have huf := hfu.symm
  have hts := hst.symm
  have hus := hsu.symm
  have hut := htu.symm
  have hmod_lt : r % d < 2 ^ b := lt_of_le_of_lt (Nat.mod_le r d) hrb
  -- 1. dup xr s t : s := r
  have h1 := dup_le_B hrs hrt hst r b hrb rr v S hSr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 5 * B b + 2) h1
    fun v₁ S₁ ⟨hr₁, hs₁, ht₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 2. dup xd t s : t := d
  have hd₁ : S₁ xd = encodeNatΓ' d ++ .comma :: dr := by rw [hF₁ xd hdr hds hdt, hSd]
  have h2 := dup_le_B hdt hds hts d b hdb dr v₁ S₁ hd₁
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 4 * B b + 2) h2
    fun v₂ S₂ ⟨hd₂, ht₂, hs₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. divmodC s t u xd xf xr
  have hs₂' : S₂ s = encodeNatΓ' r ++ .comma :: S s := by rw [hs₂, hs₁]
  have ht₂' : S₂ t = encodeNatΓ' d ++ .comma :: S t := by rw [ht₂, ht₁]
  have h3 := divmodC_le_B hst hsu hsd hsf hsr htu htd htf htr hud huf hur hdf hdr hfr
    r d b hd hrb hdb (S s) (S t) v₂ S₂ hs₂' ht₂'
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 3 * B b + 2) h3
    fun v₃ S₃ ⟨hs₃, ht₃, hu₃, hd₃, hf₃, hr₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 4. isZero s t
  have h4 := isZero_le_B hst (r % d) b hmod_lt (S s) v₃ S₃ hs₃
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 2 * B b + 2) h4
    fun v₄ S₄ ⟨hfl₄, _, hs₄, ht₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 5. dropNum s
  have h5 := dropNum_le_B (r % d) b hmod_lt (S s) v₄ S₄ (by rw [hs₄, hs₃])
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b + 2) h5
    fun v₅ S₅ ⟨hfl₅, _, _, hs₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stacks after stage 5
  have hd₅ : S₅ xd = S xd := by rw [hF₅ xd hds, hF₄ xd hds hdt, hd₃, hd₂, hd₁, hSd]
  have hr₅ : S₅ xr = S xr := by rw [hF₅ xr hrs, hF₄ xr hrs hrt, hr₃, hF₂ xr hrd hrt hrs, hr₁]
  have hf₅ : S₅ xf = S xf := by
    rw [hF₅ xf hfs, hF₄ xf hfs hft, hf₃, hF₂ xf hfd hft hfs, hF₁ xf hfr hfs hft]
  have ht₅ : S₅ t = S t := by rw [hF₅ t hts, ht₄, ht₃]
  have hu₅ : S₅ u = encodeNatΓ' (r / d) ++ .comma :: S u := by
    rw [hF₅ u hus, hF₄ u hus hut, hu₃, hF₂ u hud hut hus, hF₁ u hur hus hut]
  have hF₅' : ∀ k, k ≠ xd → k ≠ xr → k ≠ xf → k ≠ s → k ≠ t → k ≠ u → S₅ k = S k := by
    intro k hkd hkr hkf hks hkt hku
    rw [hF₅ k hks, hF₄ k hks hkt, hF₃ k hks hkt hku hkd hkf hkr, hF₂ k hkd hkt hks,
      hF₁ k hkr hks hkt]
  have hfl : v₅.flag = decide (r % d = 0) := by rw [hfl₅, hfl₄]
  -- 6. if `r % d = 0` then `flag := fuel ≠ 0` else `flag` stays `false`
  refine Frag.runs_mono (Frag.ite_runs (t := B b + 1) (fun hc => ?_) (fun hc => ?_))
    (fun _ _ h => h) (by omega)
  · have hmod : r % d = 0 := by simpa [hfl] using hc
    have h6 := isZero_le_B hfs f b hfb fr v₅ S₅ (by rw [hf₅, hSf])
    refine Frag.runs_mono (Frag.seq_runs (t₂ := 1) h6
      fun v₆ S₆ ⟨hfl₆, _, hf₆, hs₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
    refine Frag.runs_mono (Frag.load'_runs _ v₆ S₆) (fun v₇ S₇ ⟨hv₇, hS₇⟩ => ?_) le_rfl
    rw [hv₇, hS₇]
    refine ⟨by simp [hfl₆, hmod], ?_, ?_, hf₆.trans hf₅, hs₆.trans hs₅, ?_, ?_, ?_⟩
    · rw [hF₆ xd hdf hds, hd₅]
    · rw [hF₆ xr hrf hrs, hr₅]
    · rw [hF₆ t htf hts, ht₅]
    · rw [hF₆ u huf hus, hu₅]
    · intro k hkd hkr hkf hks hkt hku
      rw [hF₆ k hkf hks, hF₅' k hkd hkr hkf hks hkt hku]
  · have hmod : r % d ≠ 0 := by simpa [hfl] using hc
    refine Frag.runs_mono (Frag.skip_runs v₅ S₅) (fun v₆ S₆ ⟨hv₆, hS₆⟩ => ?_) (by omega)
    rw [hv₆, hS₆]
    exact ⟨by simp [hfl, hmod], hd₅, hr₅, hf₅, hs₅, ht₅, hu₅, hF₅'⟩

/-- Loop invariant of `divOutF` after `i` successful divisions: the current
`r'` on `xr`, `fuel - i` on `xf`, the quotient `r' / d` on `u`, the flag
`(r' % d = 0 ∧ fuel - i ≠ 0)`, and `divOut d r fuel` equals `divOut d r' (fuel - i)`
with `i` more charged. -/
def DOInv (xd xr xf s t u : K) (d r fuel : ℕ) (dr rr fr : List Γ') (S₀ : Stacks)
    (i : ℕ) (v : St) (S : Stacks) : Prop :=
  i ≤ (Alg.divOut d r fuel).2 ∧
  ∃ r', r' ≤ r ∧
    S xr = encodeNatΓ' r' ++ .comma :: rr ∧
    S xf = encodeNatΓ' (fuel - i) ++ .comma :: fr ∧
    S u = encodeNatΓ' (r' / d) ++ .comma :: S₀ u ∧
    S xd = encodeNatΓ' d ++ .comma :: dr ∧ S s = S₀ s ∧ S t = S₀ t ∧
    (∀ k, k ≠ xd → k ≠ xr → k ≠ xf → k ≠ s → k ≠ t → k ≠ u → S k = S₀ k) ∧
    Alg.divOut d r fuel = ((Alg.divOut d r' (fuel - i)).1, (Alg.divOut d r' (fuel - i)).2 + i) ∧
    v.flag = (decide (r' % d = 0) && !decide (fuel - i = 0))

theorem divOutBody_runs {xd xr xf s t u : K} (hdr : xd ≠ xr) (hdf : xd ≠ xf) (hds : xd ≠ s)
    (hdt : xd ≠ t) (hdu : xd ≠ u) (hrf : xr ≠ xf) (hrs : xr ≠ s) (hrt : xr ≠ t) (hru : xr ≠ u)
    (hfs : xf ≠ s) (hft : xf ≠ t) (hfu : xf ≠ u) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (d r fuel : ℕ) (hd : 1 ≤ d) (b : ℕ) (hdb : d < 2 ^ b) (hrb : r < 2 ^ b) (hfb : fuel < 2 ^ b)
    (dr rr fr : List Γ') (S₀ : Stacks) (i : ℕ) (hi : i < (Alg.divOut d r fuel).2)
    (v : St) (S : Stacks) (hI : DOInv xd xr xf s t u d r fuel dr rr fr S₀ i v S) :
    (divOutBody xd xr xf s t u).Runs v S (DOInv xd xr xf s t u d r fuel dr rr fr S₀ (i + 1))
      (9 * B b + 2) := by
  have hrd := hdr.symm
  have hfd := hdf.symm
  have hsd := hds.symm
  have hfr := hrf.symm
  have hsr := hrs.symm
  have htr := hrt.symm
  have hur := hru.symm
  have hsf := hfs.symm
  have htf := hft.symm
  have huf := hfu.symm
  have hus := hsu.symm
  have hts := hst.symm
  have hut := htu.symm
  obtain ⟨-, r', hr'r, hSr, hSf, hSu, hSd, hSs, hSt, hF, hrel, -⟩ := hI
  have hcost : (Alg.divOut d r fuel).2 = (Alg.divOut d r' (fuel - i)).2 + i :=
    congrArg Prod.snd hrel
  have hpos : 0 < (Alg.divOut d r' (fuel - i)).2 := by omega
  rw [divOut_cost_pos_iff] at hpos
  obtain ⟨hfpos, hdv⟩ := hpos
  obtain ⟨f, hf⟩ : ∃ f, fuel - i = f + 1 := ⟨fuel - i - 1, by omega⟩
  rw [hf] at hrel hSf
  have hfi : fuel - (i + 1) = f := by omega
  have hstep := divOut_succ_dvd f hdv
  have hr'b : r' < 2 ^ b := lt_of_le_of_lt hr'r hrb
  have hq_le : r' / d ≤ r := (Nat.div_le_self r' d).trans hr'r
  have hqb : r' / d < 2 ^ b := lt_of_le_of_lt hq_le hrb
  -- 1. dropNum xr
  have h1 := dropNum_le_B r' b hr'b rr v S hSr
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 8 * B b + 2) h1
    fun v₁ S₁ ⟨_, _, _, hr₁, hF₁⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 2. moveEntry u xr s : xr := r' / d
  have hu₁ : S₁ u = encodeNatΓ' (r' / d) ++ .comma :: S₀ u := by rw [hF₁ u hur, hSu]
  have h2 := moveEntry_correct hur hus hrs (r' / d) (S₀ u) v₁ S₁ hu₁
  have hmv : 2 * Nat.log 2 (r' / d) + 6 ≤ B b := by
    have := log_le_of_lt_pow hqb
    apply le_B_of_le_linear; omega
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 7 * B b + 2) h2
    fun v₂ S₂ ⟨_, _, _, hu₂, hr₂, hs₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- 3. predNum xf s
  have hf₂ : S₂ xf = encodeNatΓ' (f + 1) ++ .comma :: fr := by
    rw [hF₂ xf hfu hfr hfs, hF₁ xf hfr, hSf]
  have h3 := predNum_le_B hfs (f + 1) b (by omega) (by omega) fr v₂ S₂ hf₂
  refine Frag.runs_mono (Frag.seq_runs (t₂ := 6 * B b + 2) h3
    fun v₃ S₃ ⟨_, _, hf₃, hs₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  rw [Nat.add_sub_cancel] at hf₃
  -- 4. the test phase with `r' / d`
  have hd₃ : S₃ xd = encodeNatΓ' d ++ .comma :: dr := by
    rw [hF₃ xd hdf hds, hF₂ xd hdu hdr hds, hF₁ xd hdr, hSd]
  have hr₃ : S₃ xr = encodeNatΓ' (r' / d) ++ .comma :: rr := by
    rw [hF₃ xr hrf hrs, hr₂, hr₁]
  have h4 := divOutTest_le_B hdr hdf hds hdt hdu hrf hrs hrt hru hfs hft hfu hst hsu htu
    d (r' / d) f hd b hdb hqb (by omega) dr rr fr v₃ S₃ hd₃ hr₃ hf₃
  refine Frag.runs_mono h4 (fun v₄ S₄ ⟨hfl₄, hd₄, hr₄, hf₄, hs₄, ht₄, hu₄, hF₄⟩ =>
    ⟨by omega, r' / d, hq_le, hr₄.trans hr₃, ?_, ?_, hd₄.trans hd₃, ?_, ?_, ?_, ?_, ?_⟩) le_rfl
  · rw [hf₄, hf₃, hfi]
  · rw [hu₄, hF₃ u huf hus, hu₂]
  · rw [hs₄, hs₃, hs₂, hF₁ s hsr, hSs]
  · rw [ht₄, hF₃ t htf hts, hF₂ t htu htr hts, hF₁ t htr, hSt]
  · intro k hkd hkr hkf hks hkt hku
    rw [hF₄ k hkd hkr hkf hks hkt hku, hF₃ k hkf hks, hF₂ k hku hkr hks, hF₁ k hkr,
      hF k hkd hkr hkf hks hkt hku]
  · rw [hrel, hstep, hfi]; simp only [Prod.mk.injEq, true_and]; omega
  · rw [hfl₄, hfi]

theorem divOutF_le_B {xd xr xf s t u : K} (hdr : xd ≠ xr) (hdf : xd ≠ xf) (hds : xd ≠ s)
    (hdt : xd ≠ t) (hdu : xd ≠ u) (hrf : xr ≠ xf) (hrs : xr ≠ s) (hrt : xr ≠ t) (hru : xr ≠ u)
    (hfs : xf ≠ s) (hft : xf ≠ t) (hfu : xf ≠ u) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (d r fuel : ℕ) (hd : 1 ≤ d) (b : ℕ) (hdb : d < 2 ^ b) (hrb : r < 2 ^ b) (hfb : fuel < 2 ^ b)
    (dr rr fr : List Γ') (v : St) (S : Stacks)
    (hSd : S xd = encodeNatΓ' d ++ .comma :: dr) (hSr : S xr = encodeNatΓ' r ++ .comma :: rr)
    (hSf : S xf = encodeNatΓ' fuel ++ .comma :: fr) :
    (divOutF xd xr xf s t u).Runs v S (fun _ S' =>
        S' xr = encodeNatΓ' (Alg.divOut d r fuel).1 ++ .comma :: rr ∧
        S' xf = encodeNatΓ' (fuel - (Alg.divOut d r fuel).2) ++ .comma :: fr ∧
        S' xd = S xd ∧ S' s = S s ∧ S' t = S t ∧ S' u = S u ∧
        ∀ k, k ≠ xd → k ≠ xr → k ≠ xf → k ≠ s → k ≠ t → k ≠ u → S' k = S k)
      (((Alg.divOut d r fuel).2 + 1) * B (3 * b + 4)) := by
  have hud := hdu.symm
  have hur := hru.symm
  have huf := hfu.symm
  have hus := hsu.symm
  have hut := htu.symm
  rw [B_three_add_four]
  have hB := one_le_B b
  obtain ⟨n, hn⟩ : ∃ n, (Alg.divOut d r fuel).2 = n := ⟨_, rfl⟩
  rw [hn]
  have hnB : n ≤ n * B b := Nat.le_mul_of_pos_right _ hB
  -- stage 1: the test phase
  have h1 := divOutTest_le_B hdr hdf hds hdt hdu hrf hrs hrt hru hfs hft hfu hst hsu htu
    d r fuel hd b hdb hrb hfb dr rr fr v S hSd hSr hSf
  refine Frag.runs_mono (Frag.seq_runs (t₂ := n * (9 * B b + 2 + 1) + 1 + B b) h1
    fun v₁ S₁ ⟨hfl₁, hd₁, hr₁, hf₁, hs₁, ht₁, hu₁, hF₁⟩ => ?_) (fun _ _ h => h) (by nlinarith)
  -- stage 2: the loop
  have h0 : DOInv xd xr xf s t u d r fuel dr rr fr S 0 v₁ S₁ :=
    ⟨Nat.zero_le _, r, le_rfl, hr₁.trans hSr, by rw [Nat.sub_zero, hf₁, hSf], hu₁,
      hd₁.trans hSd, hs₁, ht₁, hF₁, by simp, by rw [hfl₁, Nat.sub_zero]⟩
  have hloop := Frag.loop_runs (c := fun v => v.flag) (B := divOutBody xd xr xf s t u)
    (DOInv xd xr xf s t u d r fuel dr rr fr S) n (9 * B b + 2) (v := v₁) (S := S₁) h0
    (fun i hi w T ⟨_, r', _, _, _, _, _, _, _, _, hrel, hfl⟩ => by
      have hcost : (Alg.divOut d r fuel).2 = (Alg.divOut d r' (fuel - i)).2 + i :=
        congrArg Prod.snd hrel
      have hpos : 0 < (Alg.divOut d r' (fuel - i)).2 := by omega
      rw [divOut_cost_pos_iff] at hpos
      obtain ⟨hfpos, hdv⟩ := hpos
      have hne : fuel - i ≠ 0 := by omega
      simp [hfl, hdv, hne])
    (fun w T ⟨_, r', _, _, _, _, _, _, _, _, hrel, hfl⟩ => by
      have hcost : (Alg.divOut d r fuel).2 = (Alg.divOut d r' (fuel - n)).2 + n :=
        congrArg Prod.snd hrel
      have hzero : (Alg.divOut d r' (fuel - n)).2 = 0 := by omega
      by_cases hdv : r' % d = 0
      · have hfz : fuel - n = 0 := by
          by_contra hne
          have := (divOut_cost_pos_iff d r' (fuel - n)).mpr ⟨Nat.pos_of_ne_zero hne, hdv⟩
          omega
        simp [hfl, hfz]
      · simp [hfl, hdv])
    (fun i hi w T hI => divOutBody_runs hdr hdf hds hdt hdu hrf hrs hrt hru hfs hft hfu hst hsu htu
      d r fuel hd b hdb hrb hfb dr rr fr S i (by omega) w T hI)
  refine Frag.runs_mono (Frag.seq_runs (t₂ := B b) hloop
    fun v₂ S₂ ⟨⟨_, r', hr'r, hr₂, hf₂, hu₂, hd₂, hs₂, ht₂, hF₂, hrel, _⟩, _⟩ => ?_)
    (fun _ _ h => h) (by omega)
  have hcost : (Alg.divOut d r fuel).2 = (Alg.divOut d r' (fuel - n)).2 + n :=
    congrArg Prod.snd hrel
  have hzero : (Alg.divOut d r' (fuel - n)).2 = 0 := by omega
  have hfst : (Alg.divOut d r fuel).1 = r' := by
    rw [congrArg Prod.fst hrel]; exact divOut_fst_of_cost_zero hzero
  have hqb : r' / d < 2 ^ b := lt_of_le_of_lt ((Nat.div_le_self r' d).trans hr'r) hrb
  -- stage 3: drop the unused quotient
  have h3 := dropNum_le_B (r' / d) b hqb (S u) v₂ S₂ hu₂
  refine Frag.runs_mono h3 (fun _ S₃ ⟨_, _, _, hu₃, hF₃⟩ => ⟨?_, ?_, ?_, ?_, ?_, hu₃, ?_⟩) le_rfl
  · rw [hF₃ xr hru, hr₂, hfst]
  · rw [hF₃ xf hfu, hf₂]
  · rw [hF₃ xd hdu, hd₂, hSd]
  · rw [hF₃ s hsu, hs₂]
  · rw [hF₃ t htu, ht₂]
  · intro k hkd hkr hkf hks hkt hku
    rw [hF₃ k hku, hF₂ k hkd hkr hkf hks hkt hku]

/-! ### `smoothGo`: divide out `d = d₀, d₀ + 1, …`

Stacks: `d` on `xd`, `r` on `xr`, outer `fuel` on `xF`; `xf` receives the
inner fuel (a copy of `r`) for each `divOutF` call; scratch `s t u`.  Body:
`dup xr xf s ; divOutF ; dropNum xf ; incr xd ; predNum xF ; isZero xF`;
loop while `!flag`.  The per-iteration cost is `((divOut …).2 + 1) * B (3b+7)`
plus a constant, data-dependent, so the loop rule is `Frag.loop_runs_budget`
with budget `(Alg.smoothGo (d + i) r' (fuel - i)).2 * B (4b + 10)`. -/

/-- One iteration of `smoothGo`. -/
def smoothGoBody (xd xr xf xF s t u : K) : Frag :=
  (dup xr xf s).seq ((divOutF xd xr xf s t u).seq ((dropNum xf).seq ((incr xd s).seq
    ((predNum xF s).seq (isZero xF s)))))

/-- `smoothGo d r fuel` on the machine. -/
def smoothGoF (xd xr xf xF s t u : K) : Frag :=
  (isZero xF s).seq (Frag.loop (fun v => !v.flag) (smoothGoBody xd xr xf xF s t u))

/-- Loop invariant of `smoothGoF` after `i` iterations, with the remaining
budget `β`. -/
def SGInv (xd xr xf xF s t u : K) (d r fuel : ℕ) (dr rr Fr : List Γ') (S₀ : Stacks) (b : ℕ)
    (i β : ℕ) (v : St) (S : Stacks) : Prop :=
  i ≤ fuel ∧
  ∃ r' c', r' ≤ r ∧
    S xr = encodeNatΓ' r' ++ .comma :: rr ∧
    S xd = encodeNatΓ' (d + i) ++ .comma :: dr ∧
    S xF = encodeNatΓ' (fuel - i) ++ .comma :: Fr ∧
    S xf = S₀ xf ∧ S s = S₀ s ∧ S t = S₀ t ∧ S u = S₀ u ∧
    (∀ k, k ≠ xd → k ≠ xr → k ≠ xf → k ≠ xF → k ≠ s → k ≠ t → k ≠ u → S k = S₀ k) ∧
    Alg.smoothGo d r fuel =
      ((Alg.smoothGo (d + i) r' (fuel - i)).1, (Alg.smoothGo (d + i) r' (fuel - i)).2 + c') ∧
    v.flag = decide (fuel - i = 0) ∧
    β = (Alg.smoothGo (d + i) r' (fuel - i)).2 * B (4 * b + 10)

theorem smoothGoBody_runs {xd xr xf xF s t u : K} (hdr : xd ≠ xr) (hdf : xd ≠ xf) (hdF : xd ≠ xF)
    (hds : xd ≠ s) (hdt : xd ≠ t) (hdu : xd ≠ u) (hrf : xr ≠ xf) (hrF : xr ≠ xF) (hrs : xr ≠ s)
    (hrt : xr ≠ t) (hru : xr ≠ u) (hfF : xf ≠ xF) (hfs : xf ≠ s) (hft : xf ≠ t) (hfu : xf ≠ u)
    (hFs : xF ≠ s) (hFt : xF ≠ t) (hFu : xF ≠ u) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (d r fuel : ℕ) (hd : 1 ≤ d) (b : ℕ) (hdb : d < 2 ^ b) (hrb : r < 2 ^ b) (hfb : fuel < 2 ^ b)
    (dr rr Fr : List Γ') (S₀ : Stacks) (i : ℕ) (hi : i < fuel) (β : ℕ) (v : St) (S : Stacks)
    (hI : SGInv xd xr xf xF s t u d r fuel dr rr Fr S₀ b i β v S) :
    ∃ t' β', t' + 1 + β' ≤ β ∧
      (smoothGoBody xd xr xf xF s t u).Runs v S
        (SGInv xd xr xf xF s t u d r fuel dr rr Fr S₀ b (i + 1) β') t' := by
  have hrd := hdr.symm
  have hfd := hdf.symm
  have hFd := hdF.symm
  have hsd := hds.symm
  have hfr := hrf.symm
  have hFr := hrF.symm
  have hsr := hrs.symm
  have hFf := hfF.symm
  have hsf := hfs.symm
  have hsF := hFs.symm
  have htF := hFt.symm
  have huF := hFu.symm
  have hts := hst.symm
  have hus := hsu.symm
  obtain ⟨-, r', c', hr'r, hSr, hSd, hSF, hSf, hSs, hSt, hSu, hF, hrel, -, hβ⟩ := hI
  obtain ⟨f, hf⟩ : ∃ f, fuel - i = f + 1 := ⟨fuel - i - 1, by omega⟩
  rw [hf] at hrel hSF hβ
  have hfi : fuel - (i + 1) = f := by omega
  have hsg := smoothGo_succ (d + i) r' f
  have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
  have hr'b : r' < 2 ^ b := lt_of_le_of_lt hr'r hrb
  have hr'b1 := lt_pow_succ hr'b
  have hd'b : d + i < 2 ^ (b + 1) := by omega
  have hd'1 : 1 ≤ d + i := by omega
  have hB1 := one_le_B (b + 1)
  have hBb := B_succ_le b
  have hres_le : (Alg.divOut (d + i) r' r').1 ≤ r := (divOut_fst_le _ _ _).trans hr'r
  have hleft_lt : r' - (Alg.divOut (d + i) r' r').2 < 2 ^ b := by omega
  refine ⟨B b + (((Alg.divOut (d + i) r' r').2 + 1) * (27 * B (b + 1)) +
      (B b + (B (b + 1) + (B b + B b)))),
    (Alg.smoothGo (d + i + 1) (Alg.divOut (d + i) r' r').1 f).2 * B (4 * b + 10), ?_, ?_⟩
  · -- the budget
    rw [hβ, hsg, B_four_add_ten]
    have hcB : B (b + 1) ≤ ((Alg.divOut (d + i) r' r').2 + 1) * B (b + 1) :=
      Nat.le_mul_of_pos_left _ (by omega)
    nlinarith [hcB, hBb, hB1]
  -- 1. dup xr xf s : inner fuel := r'
  have h1 := dup_le_B hrf hrs hfs r' b hr'b rr v S hSr
  refine Frag.seq_runs h1 fun v₁ S₁ ⟨hr₁, hf₁, hs₁, hF₁⟩ => ?_
  -- 2. divOutF xd xr xf s t u
  have hd₁ : S₁ xd = encodeNatΓ' (d + i) ++ .comma :: dr := by rw [hF₁ xd hdr hdf hds, hSd]
  have hr₁' : S₁ xr = encodeNatΓ' r' ++ .comma :: rr := by rw [hr₁, hSr]
  have h2 := divOutF_le_B hdr hdf hds hdt hdu hrf hrs hrt hru hfs hft hfu hst hsu htu
    (d + i) r' r' hd'1 (b + 1) hd'b hr'b1 hr'b1 dr rr (S xf) v₁ S₁ hd₁ hr₁' hf₁
  have h37 : 3 * (b + 1) + 4 = 3 * b + 7 := by ring
  rw [h37, B_three_add_seven] at h2
  refine Frag.seq_runs h2 fun v₂ S₂ ⟨hr₂, hf₂, hd₂, hs₂, ht₂, hu₂, hF₂⟩ => ?_
  -- 3. dropNum xf
  have h3 := dropNum_le_B _ b hleft_lt (S xf) v₂ S₂ hf₂
  refine Frag.seq_runs h3 fun v₃ S₃ ⟨_, _, _, hf₃, hF₃⟩ => ?_
  -- 4. incr xd s
  have hd₃ : S₃ xd = encodeNatΓ' (d + i) ++ .comma :: dr := by rw [hF₃ xd hdf, hd₂, hd₁]
  have h4 := incr_le_B hds (d + i) (b + 1) hd'b dr v₃ S₃ hd₃
  refine Frag.seq_runs h4 fun v₄ S₄ ⟨_, _, _, hd₄, hs₄, hF₄⟩ => ?_
  -- 5. predNum xF s
  have hF₄' : S₄ xF = encodeNatΓ' (f + 1) ++ .comma :: Fr := by
    rw [hF₄ xF hFd hFs, hF₃ xF hFf, hF₂ xF hFd hFr hFf hFs hFt hFu, hF₁ xF hFr hFf hFs, hSF]
  have h5 := predNum_le_B hFs (f + 1) b (by omega) (by omega) Fr v₄ S₄ hF₄'
  refine Frag.seq_runs h5 fun v₅ S₅ ⟨_, _, hF₅, hs₅, hF₅'⟩ => ?_
  rw [Nat.add_sub_cancel] at hF₅
  -- 6. isZero xF s
  have h6 := isZero_le_B hFs f b (by omega) Fr v₅ S₅ hF₅
  refine Frag.runs_mono h6 (fun v₆ S₆ ⟨hfl₆, _, hF₆, hs₆, hF₆'⟩ => ?_) le_rfl
  refine ⟨by omega, (Alg.divOut (d + i) r' r').1, c' + (Alg.divOut (d + i) r' r').2 + 1, hres_le,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF₆' xr hrF hrs, hF₅' xr hrF hrs, hF₄ xr hrd hrs, hF₃ xr hrf, hr₂]
  · rw [hF₆' xd hdF hds, hF₅' xd hdF hds, hd₄, Nat.add_assoc]
  · rw [hF₆, hF₅, hfi]
  · rw [hF₆' xf hfF hfs, hF₅' xf hfF hfs, hF₄ xf hfd hfs, hf₃, hSf]
  · rw [hs₆, hs₅, hs₄, hF₃ s hsf, hs₂, hs₁, hSs]
  · rw [hF₆' t htF hts, hF₅' t htF hts, hF₄ t hdt.symm hts, hF₃ t hft.symm, ht₂,
      hF₁ t hrt.symm hft.symm hts, hSt]
  · rw [hF₆' u huF hus, hF₅' u huF hus, hF₄ u hdu.symm hus, hF₃ u hfu.symm, hu₂,
      hF₁ u hru.symm hfu.symm hus, hSu]
  · intro k hkd hkr hkf hkF hks hkt hku
    rw [hF₆' k hkF hks, hF₅' k hkF hks, hF₄ k hkd hks, hF₃ k hkf, hF₂ k hkd hkr hkf hks hkt hku,
      hF₁ k hkr hkf hks, hF k hkd hkr hkf hkF hks hkt hku]
  · rw [hfi, ← Nat.add_assoc, hrel, hsg]
    simp only [Prod.mk.injEq, true_and]
    omega
  · rw [hfl₆, hfi]
  · rw [hfi, ← Nat.add_assoc]

theorem smoothGoF_le_B {xd xr xf xF s t u : K} (hdr : xd ≠ xr) (hdf : xd ≠ xf) (hdF : xd ≠ xF)
    (hds : xd ≠ s) (hdt : xd ≠ t) (hdu : xd ≠ u) (hrf : xr ≠ xf) (hrF : xr ≠ xF) (hrs : xr ≠ s)
    (hrt : xr ≠ t) (hru : xr ≠ u) (hfF : xf ≠ xF) (hfs : xf ≠ s) (hft : xf ≠ t) (hfu : xf ≠ u)
    (hFs : xF ≠ s) (hFt : xF ≠ t) (hFu : xF ≠ u) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (d r fuel : ℕ) (hd : 1 ≤ d) (b : ℕ) (hdb : d < 2 ^ b) (hrb : r < 2 ^ b) (hfb : fuel < 2 ^ b)
    (dr rr Fr : List Γ') (v : St) (S : Stacks)
    (hSd : S xd = encodeNatΓ' d ++ .comma :: dr) (hSr : S xr = encodeNatΓ' r ++ .comma :: rr)
    (hSF : S xF = encodeNatΓ' fuel ++ .comma :: Fr) :
    (smoothGoF xd xr xf xF s t u).Runs v S (fun _ S' =>
        S' xr = encodeNatΓ' (Alg.smoothGo d r fuel).1 ++ .comma :: rr ∧
        S' xd = encodeNatΓ' (d + fuel) ++ .comma :: dr ∧
        S' xF = encodeNatΓ' 0 ++ .comma :: Fr ∧
        S' xf = S xf ∧ S' s = S s ∧ S' t = S t ∧ S' u = S u ∧
        ∀ k, k ≠ xd → k ≠ xr → k ≠ xf → k ≠ xF → k ≠ s → k ≠ t → k ≠ u → S' k = S k)
      (((Alg.smoothGo d r fuel).2 + 1) * B (4 * b + 10)) := by
  have hFd := hdF.symm
  have hFr := hrF.symm
  have hFf := hfF.symm
  have hsF := hFs.symm
  have htF := hFt.symm
  have huF := hFu.symm
  have hts := hst.symm
  have hus := hsu.symm
  have hB1 := one_le_B (b + 1)
  have hBb := B_succ_le b
  -- stage 1: isZero xF s
  have h1 := isZero_le_B hFs fuel b hfb Fr v S hSF
  refine Frag.runs_mono (Frag.seq_runs (t₂ := (Alg.smoothGo d r fuel).2 * B (4 * b + 10) + 1) h1
    fun v₁ S₁ ⟨hfl₁, _, hF₁, hs₁, hF₁'⟩ => ?_) (fun _ _ h => h) ?_
  swap
  · rw [B_four_add_ten]; nlinarith
  -- stage 2: the loop
  have h0 : SGInv xd xr xf xF s t u d r fuel dr rr Fr S b 0
      ((Alg.smoothGo d r fuel).2 * B (4 * b + 10)) v₁ S₁ :=
    ⟨Nat.zero_le _, r, 0, le_rfl, by rw [hF₁' xr hrF hrs, hSr],
      by rw [hF₁' xd hdF hds, Nat.add_zero, hSd], by rw [hF₁, Nat.sub_zero, hSF],
      hF₁' xf hfF hfs, hs₁, hF₁' t htF hts, hF₁' u huF hus,
      fun k _ _ hkf hkF hks _ _ => hF₁' k hkF hks, by simp, by rw [hfl₁, Nat.sub_zero], by simp⟩
  have hloop := Frag.loop_runs_budget (c := fun v => !v.flag) (B := smoothGoBody xd xr xf xF s t u)
    (SGInv xd xr xf xF s t u d r fuel dr rr Fr S b) fuel
    ((Alg.smoothGo d r fuel).2 * B (4 * b + 10)) (v := v₁) (S := S₁) h0
    (fun i hi β w T ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hfl, _⟩ => by
      have : fuel - i ≠ 0 := by omega
      simp [hfl, this])
    (fun β w T ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hfl, _⟩ => by simp [hfl])
    (fun i hi β w T hI => smoothGoBody_runs hdr hdf hdF hds hdt hdu hrf hrF hrs hrt hru hfF hfs hft
      hfu hFs hFt hFu hst hsu htu d r fuel hd b hdb hrb hfb dr rr Fr S i hi β w T hI)
  refine Frag.runs_mono hloop
    (fun v' S' ⟨⟨_, ⟨_, r', c', _, hr', hd', hF', hf', hs', ht', hu', hFr', hrel, _, _⟩⟩, _⟩ =>
      ⟨?_, hd', ?_, hf', hs', ht', hu', hFr'⟩) le_rfl
  · rw [hr', congrArg Prod.fst hrel, Nat.sub_self, smoothGo_zero]
  · rw [hF', Nat.sub_self]

/-! ### `smoothTD` -/

/-- `flag := smoothTD y k` for `y` on `xy` (restored) and `k` on `xr`
(CONSUMED).  The fuel `y - 1` is pushed on top of `y` (`dup`, `predNum`,
`moveEntry`), `d := 2` on `xd`, then `smoothGoF` with `xF := xy`; the fuel
remnant (`0`) and `d` are dropped, and the result on `xr` is compared with
`1`. -/
def smoothTDF (xy xr xd xf s t u : K) : Frag :=
  (dup xy s t).seq ((predNum s t).seq ((moveEntry s xy t).seq ((pushNum xd 2).seq
    ((smoothGoF xd xr xf xy s t u).seq ((dropNum xy).seq ((dropNum xd).seq ((pushNum s 1).seq
      ((cmpFrag xr s).seq (Frag.load' (fun v => { v with flag := decide (v.cmp = .eq) }))))))))))

theorem smoothTDF_le_B {xy xr xd xf s t u : K} (hyr : xy ≠ xr) (hyd : xy ≠ xd) (hyf : xy ≠ xf)
    (hys : xy ≠ s) (hyt : xy ≠ t) (hyu : xy ≠ u) (hrd : xr ≠ xd) (hrf : xr ≠ xf) (hrs : xr ≠ s)
    (hrt : xr ≠ t) (hru : xr ≠ u) (hdf : xd ≠ xf) (hds : xd ≠ s) (hdt : xd ≠ t) (hdu : xd ≠ u)
    (hfs : xf ≠ s) (hft : xf ≠ t) (hfu : xf ≠ u) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (y k : ℕ) (b : ℕ) (hb : 2 ≤ b) (hyb : y < 2 ^ b) (hkb : k < 2 ^ b) (yr kr : List Γ')
    (v : St) (S : Stacks)
    (hSy : S xy = encodeNatΓ' y ++ .comma :: yr) (hSk : S xr = encodeNatΓ' k ++ .comma :: kr) :
    (smoothTDF xy xr xd xf s t u).Runs v S (fun v' S' =>
        v'.flag = (Alg.smoothTD y k).1 ∧ S' xy = S xy ∧ S' xr = kr ∧ S' xd = S xd ∧
        S' xf = S xf ∧ S' s = S s ∧ S' t = S t ∧ S' u = S u ∧
        ∀ k, k ≠ xy → k ≠ xr → k ≠ xd → k ≠ xf → k ≠ s → k ≠ t → k ≠ u → S' k = S k)
      (((Alg.smoothTD y k).2 + 1) * B (4 * b + 10)) := by
  have hry := hyr.symm
  have hdy := hyd.symm
  have hfy := hyf.symm
  have hsy := hys.symm
  have hty := hyt.symm
  have huy := hyu.symm
  have hdr := hrd.symm
  have hfr := hrf.symm
  have hsr := hrs.symm
  have htr := hrt.symm
  have hur := hru.symm
  have hfd := hdf.symm
  have hsd := hds.symm
  have htd := hdt.symm
  have hud := hdu.symm
  have hsf := hfs.symm
  have htf := hft.symm
  have huf := hfu.symm
  have hts := hst.symm
  have hus := hsu.symm
  have hut := htu.symm
  have hB1 := one_le_B (b + 1)
  have hBb := B_succ_le b
  have hlin : 4 * b + 40 ≤ B (b + 1) := le_B_of_le_linear (by omega)
  have hl2 : Nat.log 2 2 ≤ 2 := log_le_of_lt_pow (by norm_num)
  have hl0 : Nat.log 2 0 = 0 := Nat.log_zero_right 2
  have hl1 : Nat.log 2 1 = 0 := Nat.log_one_right 2
  have hly := log_le_of_lt_pow hyb
  have hly1 : Nat.log 2 (y - 1) ≤ b := log_le_of_lt_pow (by omega)
  have h2b : 2 < 2 ^ b := by
    have : 2 ^ 2 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
    omega
  have hpow : 2 ^ (b + 1) = 2 * 2 ^ b := by ring
  rw [smoothTD_eq]
  simp only
  obtain ⟨n, hn⟩ : ∃ n, (Alg.smoothGo 2 k (y - 1)).2 = n := ⟨_, rfl⟩
  rw [hn, B_four_add_ten]
  have hres_le : (Alg.smoothGo 2 k (y - 1)).1 ≤ k := smoothGo_fst_le _ _ _
  have hlres : Nat.log 2 (Alg.smoothGo 2 k (y - 1)).1 ≤ b :=
    log_le_of_lt_pow (lt_of_le_of_lt hres_le hkb)
  have hmul : (n + 1 + 1) * (64 * B (b + 1)) = (n + 1) * (64 * B (b + 1)) + 64 * B (b + 1) := by
    ring
  -- stage 1: dup xy s t : s := y
  have h1 := dup_le_B hys hyt hst y b hyb yr v S hSy
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (2 * Nat.log 2 y + 5) + (2 * Nat.log 2 (y - 1) + 6) + (Nat.log 2 2 + 2) + (n + 1) * (64 * B (b + 1)) + (Nat.log 2 0 + 2) + (B (b + 1)) + (Nat.log 2 1 + 2) + (4 * (Nat.log 2 (Alg.smoothGo 2 k (y - 1)).1 + Nat.log 2 1 + 1)) + 1)
    h1 fun v₁ S₁ ⟨hy₁, hs₁, ht₁, hF₁⟩ => ?_) (fun _ _ h => h) (by rw [hmul]; omega)
  -- stage 2: predNum s t : s := y - 1
  have h2 := predNum_correct' hst y (S s) v₁ S₁ hs₁
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (2 * Nat.log 2 (y - 1) + 6) + (Nat.log 2 2 + 2) + (n + 1) * (64 * B (b + 1)) + (Nat.log 2 0 + 2) + (B (b + 1)) + (Nat.log 2 1 + 2) + (4 * (Nat.log 2 (Alg.smoothGo 2 k (y - 1)).1 + Nat.log 2 1 + 1)) + 1)
    h2 fun v₂ S₂ ⟨_, _, hs₂, ht₂, hF₂⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 3: moveEntry s xy t : push y - 1 on top of y
  have h3 := moveEntry_correct hsy hst hyt (y - 1) (S s) v₂ S₂ hs₂
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (Nat.log 2 2 + 2) + (n + 1) * (64 * B (b + 1)) + (Nat.log 2 0 + 2) + (B (b + 1)) + (Nat.log 2 1 + 2) + (4 * (Nat.log 2 (Alg.smoothGo 2 k (y - 1)).1 + Nat.log 2 1 + 1)) + 1)
    h3 fun v₃ S₃ ⟨_, _, _, hs₃, hy₃, ht₃, hF₃⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 4: pushNum xd 2
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (n + 1) * (64 * B (b + 1)) + (Nat.log 2 0 + 2) + (B (b + 1)) + (Nat.log 2 1 + 2) + (4 * (Nat.log 2 (Alg.smoothGo 2 k (y - 1)).1 + Nat.log 2 1 + 1)) + 1)
    (pushNum_runs xd 2 v₃ S₃) fun v₄ S₄ ⟨hv₄, hd₄, hF₄⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 5: smoothGoF xd xr xf xy s t u
  have hy₄ : S₄ xy = encodeNatΓ' (y - 1) ++ .comma :: S xy := by
    rw [hF₄ xy hyd, hy₃, hF₂ xy hys hyt, hy₁]
  have hr₄ : S₄ xr = encodeNatΓ' k ++ .comma :: kr := by
    rw [hF₄ xr hrd, hF₃ xr hrs hry hrt, hF₂ xr hrs hrt, hF₁ xr hry hrs hrt, hSk]
  have hd₄' : S₄ xd = encodeNatΓ' 2 ++ .comma :: S xd := by
    rw [hd₄, hF₃ xd hds hdy hdt, hF₂ xd hds hdt, hF₁ xd hdy hds hdt]
  have h5 := smoothGoF_le_B hdr hdf hdy hds hdt hdu hrf hry hrs hrt hru hfy hfs hft hfu hys hyt hyu
    hst hsu htu 2 k (y - 1) (by norm_num) b h2b hkb (by omega) (S xd) kr (S xy) v₄ S₄ hd₄' hr₄ hy₄
  rw [hn, B_four_add_ten] at h5
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (Nat.log 2 0 + 2) + (B (b + 1)) + (Nat.log 2 1 + 2) + (4 * (Nat.log 2 (Alg.smoothGo 2 k (y - 1)).1 + Nat.log 2 1 + 1)) + 1)
    h5 fun v₅ S₅ ⟨hr₅, hd₅, hy₅, hf₅, hs₅, ht₅, hu₅, hF₅⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 6: dropNum xy (the fuel remnant 0)
  have h6 := dropNum_correct 0 (S xy) v₅ S₅ hy₅
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (B (b + 1)) + (Nat.log 2 1 + 2) + (4 * (Nat.log 2 (Alg.smoothGo 2 k (y - 1)).1 + Nat.log 2 1 + 1)) + 1)
    h6 fun v₆ S₆ ⟨_, _, _, hy₆, hF₆⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 7: dropNum xd
  have hd₆ : S₆ xd = encodeNatΓ' (2 + (y - 1)) ++ .comma :: S xd := by rw [hF₆ xd hdy, hd₅]
  have h7 := dropNum_le_B (2 + (y - 1)) (b + 1) (by omega) (S xd) v₆ S₆ hd₆
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (Nat.log 2 1 + 2) + (4 * (Nat.log 2 (Alg.smoothGo 2 k (y - 1)).1 + Nat.log 2 1 + 1)) + 1)
    h7 fun v₇ S₇ ⟨_, _, _, hd₇, hF₇⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 8: pushNum s 1
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := (4 * (Nat.log 2 (Alg.smoothGo 2 k (y - 1)).1 + Nat.log 2 1 + 1)) + 1)
    (pushNum_runs s 1 v₇ S₇) fun v₈ S₈ ⟨hv₈, hs₈, hF₈⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 9: cmpFrag xr s
  have hr₈ : S₈ xr = encodeNatΓ' (Alg.smoothGo 2 k (y - 1)).1 ++ .comma :: kr := by
    rw [hF₈ xr hrs, hF₇ xr hrd, hF₆ xr hry, hr₅]
  have hs₇ : S₇ s = S s := by
    rw [hF₇ s hsd, hF₆ s hsy, hs₅, hF₄ s hsd, hs₃]
  have hs₈' : S₈ s = encodeNatΓ' 1 ++ .comma :: S s := by rw [hs₈, hs₇]
  have h9 := cmp_correct hrs (Alg.smoothGo 2 k (y - 1)).1 1 kr (S s) v₈ S₈ hr₈ hs₈'
  refine Frag.runs_mono (Frag.seq_runs
    (t₂ := 1)
    h9 fun v₉ S₉ ⟨hcmp₉, hr₉, hs₉, hF₉⟩ => ?_) (fun _ _ h => h) (by omega)
  -- stage 10: flag := (result = 1)
  refine Frag.runs_mono (Frag.load'_runs _ v₉ S₉) (fun v' S' ⟨hv', hS'⟩ => ?_) le_rfl
  rw [hv', hS']
  refine ⟨by simp [hcmp₉], ?_, hr₉, ?_, ?_, hs₉, ?_, ?_, ?_⟩
  · rw [hF₉ xy hyr hys, hF₈ xy hys, hF₇ xy hyd, hy₆]
  · rw [hF₉ xd hdr hds, hF₈ xd hds, hd₇]
  · rw [hF₉ xf hfr hfs, hF₈ xf hfs, hF₇ xf hfd, hF₆ xf hfy, hf₅, hF₄ xf hfd, hF₃ xf hfs hfy hft,
      hF₂ xf hfs hft, hF₁ xf hfy hfs hft]
  · rw [hF₉ t htr hts, hF₈ t hts, hF₇ t htd, hF₆ t hty, ht₅, hF₄ t htd, ht₃, ht₂, ht₁]
  · rw [hF₉ u hur hus, hF₈ u hus, hF₇ u hud, hF₆ u huy, hu₅, hF₄ u hud, hF₃ u hus huy hut,
      hF₂ u hus hut, hF₁ u huy hus hut]
  · intro j hjy hjr hjd hjf hjs hjt hju
    rw [hF₉ j hjr hjs, hF₈ j hjs, hF₇ j hjd, hF₆ j hjy, hF₅ j hjd hjr hjf hjy hjs hjt hju,
      hF₄ j hjd, hF₃ j hjs hjy hjt, hF₂ j hjs hjt, hF₁ j hjy hjs hjt]

end Carmichael.TM
