/-
AGP Theorem 4.1 (= "Theorem 3.1" of the plan): the pigeonhole step, derived
from `𝓑`-membership (`BMembership`) together with two analytic inputs that are
taken here as *hypotheses* (they are the deliverables of later sorties):

* a Brun--Titchmarsh upper bound `hBT` for `π(y; m, 1)`;
* a Chebyshev/PNT lower bound `hpi` for `π(y)`.

Deviations from the plan's hypothesis sketch (BVPLAN §1.4), recorded here as
required:

* `hBT` is stated for **all** moduli `m ≥ 2`, with no squarefreeness
  hypothesis.  The moduli actually used are `m = d * q` with `d ∣ L` and `q`
  a prime factor of `L`; when `q ∣ d` this modulus is *not* squarefree
  (it is divisible by `q ^ 2`), so a squarefree-only Brun--Titchmarsh is
  insufficient for the argument of AGP p. 716.  It carries an existentially
  quantified absolute threshold `y₀ ≤ y` (matching Z2's delivered theorem,
  whose threshold is `exp 200000000`); the threshold is absorbed into `z₃`.
* `hpi` is stated with the constant `c = 11/10 ≤ 1.3` (BVPLAN §1.5 budget) and
  with an existentially quantified threshold `y₀`.  The value `c = 13/10`
  leaves a margin of only `0.006` in the constant budget once the
  `⌈d x^{1-B}⌉` rounding loss is paid, which is too tight to be worth the
  risk; `c = 11/10` leaves `0.075` and is still supplied by the planned
  `d = 1` PNT (which gives `1 + ε` for every `ε > 0`).
-/
import Carmichael.Defs

namespace Carmichael

open Finset

open Classical in
/-- `𝓑`-membership package (AGP p. 705, one-sided at the residue `a`), the
analytic core deliverable.  `bad x` is the exceptional set `𝓓(x)`. -/
structure BMembership (B : ℝ) where
  /-- Bound on the number of exceptional moduli. -/
  D : ℕ
  /-- Threshold `x₂(B)`. -/
  x₂ : ℕ
  /-- The exceptional set `𝓓(x)`. -/
  bad : ℕ → Finset ℕ
  bad_card : ∀ x, (bad x).card ≤ D
  bad_ge_two : ∀ x, ∀ m ∈ bad x, 2 ≤ m
  lower : ∀ x y d a : ℕ, x₂ ≤ x → 0 < d → Nat.Coprime a d →
    (d : ℝ) ≤ (x : ℝ) ^ B → (d : ℝ) * (x : ℝ) ^ (1 - B) ≤ (y : ℝ) → (y : ℝ) ≤ x →
    (∀ m ∈ bad x, ¬ m ∣ d) →
    (primePi y : ℝ) / (2 * Nat.totient d) ≤
      (((Finset.range (y + 1)).filter (fun p => p.Prime ∧ p % d = a % d)).card : ℝ)

/-! ### The divisor-transfer lemma, AGP (4.1) -/

/-- AGP (4.1).  Removing one prime factor for each member of the exceptional
set produces a divisor `L'` of `L` divisible by no member of `bad`, and the
divisor counts drop by at most a factor `2 ^ D`. -/
theorem exists_reduced_modulus {L : ℕ} (hL : Squarefree L) (bad : Finset ℕ) (D : ℕ)
    (hcard : bad.card ≤ D) (hge : ∀ m ∈ bad, 2 ≤ m) :
    ∃ L' : ℕ, 0 < L' ∧ L' ∣ L ∧ (∀ m ∈ bad, ¬ m ∣ L') ∧
      ∀ y : ℝ, (L.divisors.filter (fun d : ℕ => (d : ℝ) ≤ y)).card ≤
        2 ^ D * (L'.divisors.filter (fun d : ℕ => (d : ℝ) ≤ y)).card := by
  classical
  have hL0 : L ≠ 0 := hL.ne_zero
  set S : Finset ℕ := bad.image (fun m => (Nat.gcd m L).minFac) with hSdef
  set T : Finset ℕ := L.primeFactors \ S with hTdef
  have hTprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
  set L' : ℕ := ∏ p ∈ T, p with hL'def
  have hL'pos : 0 < L' := Finset.prod_pos fun p hp => (hTprime p hp).pos
  have hL'ne : L' ≠ 0 := hL'pos.ne'
  have hL'pf : L'.primeFactors = T := Nat.primeFactors_prod hTprime
  have hL'dvd : L' ∣ L := by
    have hLprod : L = ∏ p ∈ L.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hL).symm
    rw [hL'def, hLprod]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.sdiff_subset)
  refine ⟨L', hL'pos, hL'dvd, ?_, ?_⟩
  · -- no member of `bad` divides `L'`
    intro m hm hdvd
    have hmL : m ∣ L := hdvd.trans hL'dvd
    have hgcd : Nat.gcd m L = m := Nat.gcd_eq_left hmL
    have hm1 : m ≠ 1 := by
      have := hge m hm
      omega
    have hp : (Nat.gcd m L).minFac.Prime := by rw [hgcd]; exact Nat.minFac_prime hm1
    have hpdvd : (Nat.gcd m L).minFac ∣ L' := by
      rw [hgcd]
      exact (Nat.minFac_dvd m).trans hdvd
    have hmemT : (Nat.gcd m L).minFac ∈ T := by
      rw [← hL'pf]
      exact Nat.mem_primeFactors.mpr ⟨hp, hpdvd, hL'ne⟩
    have hmemS : (Nat.gcd m L).minFac ∈ S := Finset.mem_image_of_mem _ hm
    exact (Finset.mem_sdiff.mp hmemT).2 hmemS
  · -- the divisor count transfer
    intro y
    refine Finset.card_le_mul_card_image_of_maps_to (f := fun d => Nat.gcd d L') ?_ (2 ^ D) ?_
    · intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      obtain ⟨⟨hdL, -⟩, hPd⟩ := hd
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdL (Nat.pos_of_ne_zero hL0)
      refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hL'ne⟩, ?_⟩
      have : Nat.gcd d L' ≤ d := Nat.le_of_dvd hdpos (Nat.gcd_dvd_left _ _)
      exact le_trans (by exact_mod_cast this) hPd
    · intro b hb
      -- the fibre of `b` injects into the powerset of the removed primes
      have hsub : L.primeFactors \ T ⊆ S := by
        intro p hp
        rw [Finset.mem_sdiff, hTdef, Finset.mem_sdiff] at hp
        by_contra hpS
        exact hp.2 ⟨hp.1, hpS⟩
      have hcardS : (L.primeFactors \ T).card ≤ D :=
        le_trans (le_trans (Finset.card_le_card hsub) (Finset.card_image_le)) hcard
      have hfib : (((L.divisors.filter (fun d : ℕ => (d : ℝ) ≤ y)).filter
          (fun d => Nat.gcd d L' = b)).card) ≤ ((L.primeFactors \ T).powerset).card := by
        refine Finset.card_le_card_of_injOn (fun d => d.primeFactors \ T) ?_ ?_
        · intro d hd
          have hd' := Finset.mem_coe.mp hd
          rw [Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors] at hd'
          rw [Finset.mem_coe, Finset.mem_powerset]
          exact Finset.sdiff_subset_sdiff (Nat.primeFactors_mono hd'.1.1.1 hL0)
            (Finset.Subset.refl _)
        · intro d₁ h₁ d₂ h₂ heq
          have heq' : d₁.primeFactors \ T = d₂.primeFactors \ T := heq
          have m₁ := Finset.mem_coe.mp h₁
          have m₂ := Finset.mem_coe.mp h₂
          rw [Finset.mem_filter, Finset.mem_filter, Nat.mem_divisors] at m₁ m₂
          obtain ⟨⟨⟨hd₁L, -⟩, -⟩, hg₁⟩ := m₁
          obtain ⟨⟨⟨hd₂L, -⟩, -⟩, hg₂⟩ := m₂
          have hd₁0 : d₁ ≠ 0 :=
            (Nat.pos_of_dvd_of_pos hd₁L (Nat.pos_of_ne_zero hL0)).ne'
          have hd₂0 : d₂ ≠ 0 :=
            (Nat.pos_of_dvd_of_pos hd₂L (Nat.pos_of_ne_zero hL0)).ne'
          have hint : ∀ d : ℕ, d ≠ 0 → Nat.gcd d L' = b → d.primeFactors ∩ T = b.primeFactors := by
            intro d hd0 hgd
            rw [← hgd, Nat.primeFactors_gcd hd0 hL'ne, hL'pf]
          have h1 : d₁.primeFactors = d₂.primeFactors := by
            have e1 : d₁.primeFactors \ T ∪ d₁.primeFactors ∩ T = d₁.primeFactors :=
              Finset.sdiff_union_inter _ _
            have e2 : d₂.primeFactors \ T ∪ d₂.primeFactors ∩ T = d₂.primeFactors :=
              Finset.sdiff_union_inter _ _
            rw [← e1, ← e2, heq', hint d₁ hd₁0 hg₁, hint d₂ hd₂0 hg₂]
          have hs₁ : Squarefree d₁ := hL.squarefree_of_dvd hd₁L
          have hs₂ : Squarefree d₂ := hL.squarefree_of_dvd hd₂L
          calc d₁ = ∏ p ∈ d₁.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hs₁).symm
            _ = ∏ p ∈ d₂.primeFactors, p := by rw [h1]
            _ = d₂ := Nat.prod_primeFactors_of_squarefree hs₂
      rw [Finset.card_powerset] at hfib
      exact le_trans hfib (Nat.pow_le_pow_right (by norm_num) hcardS)

/-! ### The per-divisor good-prime count, AGP (4.2) and the display after it -/

section PerDivisor

variable {B : ℝ}

/-- Brun--Titchmarsh, as a hypothesis (sortie Z2), with an existential
absolute threshold `y₀`.  Note: **no squarefreeness hypothesis on the
modulus** — the moduli used below are `d * q` with `q` a prime possibly
dividing `d`. -/
def BrunTitchmarsh : Prop :=
  ∃ y₀ : ℕ, ∀ y m : ℕ, y₀ ≤ y → 2 ≤ m → (m : ℝ) ≤ (y : ℝ) ^ ((19 : ℝ) / 20) →
    ((((Finset.range (y + 1)).filter (fun p => p.Prime ∧ p % m = 1 % m)).card : ℝ))
      ≤ 3 * y / (Nat.totient m * Real.log ((y : ℝ) / m))

/-- Chebyshev/PNT lower bound for `π`, as a hypothesis (sortie Z3/Z9), with
constant `11/10 ≤ 1.3`. -/
def PiLower : Prop :=
  ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y →
    (y : ℝ) / ((11 : ℝ) / 10 * Real.log y) ≤ (primePi y : ℝ)

/-- `φ(dq) ≥ φ(d)(q-1)` for prime `q`, whether or not `q ∣ d`. -/
private lemma totient_mul_prime_lower {d q : ℕ} (hq : q.Prime) :
    (Nat.totient d : ℝ) * ((q : ℝ) - 1) ≤ (Nat.totient (d * q) : ℝ) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.one_lt.le
  have hφ : (0 : ℝ) ≤ (Nat.totient d : ℝ) := by exact_mod_cast Nat.zero_le _
  by_cases hqd : q ∣ d
  · have h1 : Nat.totient (d * q) = q * Nat.totient d := by
      rw [mul_comm d q]; exact Nat.totient_mul_of_prime_of_dvd hq hqd
    rw [h1]
    push_cast
    nlinarith
  · have hcop : Nat.Coprime d q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqd).symm
    rw [Nat.totient_mul hcop, Nat.totient_prime hq]
    rw [Nat.cast_mul, Nat.cast_sub hq.one_lt.le, Nat.cast_one]

set_option maxHeartbeats 1000000 in
/-- AGP p. 716, the good-shift count for a single divisor `d` of `L'`: at least
`x^{1-B}/(20 log x)` integers `k ≤ x^{1-B}` coprime to `L` have `dk+1` prime.
The constant `1/20` is the §1.5 budget `1/(2·(11/10)) - (4·3/(1-B))·(1-B)/32`
with the `⌈d x^{1-B}⌉` rounding loss paid (`0.0758 ≥ 0.05`). -/
theorem per_divisor_lower {B : ℝ} (hB : 1/5 < B) (hB' : B ≤ 2/5)
    (𝓑 : BMembership B) {y₀ y₁ : ℕ}
    (hBT : ∀ y m : ℕ, y₁ ≤ y → 2 ≤ m → (m : ℝ) ≤ (y : ℝ) ^ ((19 : ℝ) / 20) →
      ((((Finset.range (y + 1)).filter (fun p => p.Prime ∧ p % m = 1 % m)).card : ℝ))
        ≤ 3 * y / (Nat.totient m * Real.log ((y : ℝ) / m)))
    (hpi : ∀ y : ℕ, y₀ ≤ y → (y : ℝ) / ((11 : ℝ) / 10 * Real.log y) ≤ (primePi y : ℝ))
    {x L d : ℕ}
    (hL0 : L ≠ 0)
    (hqx : ∀ q : ℕ, q.Prime → q ∣ L → (q : ℝ) ≤ (x : ℝ) ^ ((1 - B) / 2))
    (hS : (∑ q ∈ L.primeFactors, (1 : ℝ) / q) ≤ (1 - B) / 32)
    (hx2 : 𝓑.x₂ ≤ x) (hx3 : 3 ≤ x)
    (h100 : (100 : ℝ) ≤ (x : ℝ) ^ (1 - B)) (hy0 : (y₀ : ℝ) ≤ (x : ℝ) ^ (1 - B))
    (hy1 : (y₁ : ℝ) ≤ (x : ℝ) ^ (1 - B))
    (hdpos : 0 < d) (hdB : (d : ℝ) ≤ (x : ℝ) ^ B)
    (hdbad : ∀ m ∈ 𝓑.bad x, ¬ m ∣ d) :
    (1 : ℝ) / 20 * ((x : ℝ) ^ (1 - B) / Real.log x) ≤
      ((((Finset.Icc 1 ⌊(x : ℝ) ^ (1 - B)⌋₊).filter (fun k => k.Coprime L)).filter
          (fun k => (d * k + 1).Prime ∧ d * k + 1 ≤ x)).card : ℝ) := by
  classical
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hx1 : (1 : ℝ) < (x : ℝ) := by linarith
  have hLg : 0 < Real.log x := Real.log_pos hx1
  have hXp : (0 : ℝ) < (x : ℝ) ^ (1 - B) := Real.rpow_pos_of_pos hx0 _
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
  have hdR0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hφpos : (0 : ℝ) < (Nat.totient d : ℝ) := by
    have h : 0 < Nat.totient d := Nat.totient_pos.mpr hdpos
    exact_mod_cast h
  have hφle : (Nat.totient d : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
  have htB : (0 : ℝ) < 1 - B := by linarith
  -- the cutoff `y = ⌈d x^{1-B}⌉`
  have hprod_nonneg : (0 : ℝ) ≤ (d : ℝ) * (x : ℝ) ^ (1 - B) :=
    mul_nonneg (by linarith) hXp.le
  set y : ℕ := ⌈(d : ℝ) * (x : ℝ) ^ (1 - B)⌉₊ with hydef
  have hy_lb : (d : ℝ) * (x : ℝ) ^ (1 - B) ≤ (y : ℝ) := Nat.le_ceil _
  have hxB_mul : (x : ℝ) ^ B * (x : ℝ) ^ (1 - B) = (x : ℝ) := by
    rw [← Real.rpow_add hx0]
    norm_num
  have hy_ub : (y : ℝ) ≤ (x : ℝ) := by
    have hle : (d : ℝ) * (x : ℝ) ^ (1 - B) ≤ (x : ℝ) := by
      calc (d : ℝ) * (x : ℝ) ^ (1 - B) ≤ (x : ℝ) ^ B * (x : ℝ) ^ (1 - B) :=
            mul_le_mul_of_nonneg_right hdB hXp.le
        _ = (x : ℝ) := hxB_mul
    have : y ≤ x := Nat.ceil_le.mpr hle
    exact_mod_cast this
  have hdXp100 : (100 : ℝ) ≤ (d : ℝ) * (x : ℝ) ^ (1 - B) := by nlinarith
  have hy_slack : (y : ℝ) ≤ (101 / 100) * ((d : ℝ) * (x : ℝ) ^ (1 - B)) := by
    have h1 : (y : ℝ) < (d : ℝ) * (x : ℝ) ^ (1 - B) + 1 := Nat.ceil_lt_add_one hprod_nonneg
    linarith
  have hy100 : (100 : ℝ) ≤ (y : ℝ) := le_trans hdXp100 hy_lb
  have hylog : 0 < Real.log y := Real.log_pos (by linarith)
  have hylogle : Real.log y ≤ Real.log x := Real.log_le_log (by linarith) hy_ub
  -- the weight `W = d x^{1-B} / (φ(d) log x)`
  set W : ℝ := (d : ℝ) * (x : ℝ) ^ (1 - B) / ((Nat.totient d : ℝ) * Real.log x) with hWdef
  have hWpos : 0 < W := by
    rw [hWdef]
    exact div_pos (mul_pos hdR0 hXp) (mul_pos hφpos hLg)
  have hWge : (x : ℝ) ^ (1 - B) / Real.log x ≤ W := by
    rw [hWdef, div_le_div_iff₀ hLg (mul_pos hφpos hLg)]
    nlinarith [mul_le_mul_of_nonneg_left hφle (mul_pos hXp hLg).le]
  -- (4.2): the main term
  set A : Finset ℕ := (Finset.range (y + 1)).filter (fun p => p.Prime ∧ p % d = 1 % d) with hAdef
  have hmain : (primePi y : ℝ) / (2 * Nat.totient d) ≤ (A.card : ℝ) :=
    𝓑.lower x y d 1 hx2 hdpos (Nat.coprime_one_left d) hdB hy_lb hy_ub hdbad
  have hpiy : (y : ℝ) / ((11 : ℝ) / 10 * Real.log y) ≤ (primePi y : ℝ) := by
    refine hpi y ?_
    have h : (y₀ : ℝ) ≤ (y : ℝ) := by nlinarith
    exact_mod_cast h
  have h2φ : (0 : ℝ) < 2 * (Nat.totient d : ℝ) := by linarith
  have hmain2 : (5 / 11 : ℝ) * W ≤ (A.card : ℝ) := by
    refine le_trans ?_ (le_trans ((div_le_div_iff_of_pos_right h2φ).mpr hpiy) hmain)
    have hRHS : (y : ℝ) / ((11 : ℝ) / 10 * Real.log y) / (2 * (Nat.totient d : ℝ))
        = (5 / 11) * ((y : ℝ) / ((Nat.totient d : ℝ) * Real.log y)) := by
      field_simp
      ring
    rw [hRHS]
    have hWle : W ≤ (y : ℝ) / ((Nat.totient d : ℝ) * Real.log y) := by
      rw [hWdef, div_le_div_iff₀ (mul_pos hφpos hLg) (mul_pos hφpos hylog)]
      have key : (d : ℝ) * (x : ℝ) ^ (1 - B) * Real.log y ≤ (y : ℝ) * Real.log x :=
        mul_le_mul hy_lb hylogle hylog.le (le_trans hprod_nonneg hy_lb)
      nlinarith
    linarith
  -- Brun--Titchmarsh: the primes to be discarded, one modulus `d*q` per prime `q ∣ L`
  set Aq : ℕ → Finset ℕ := fun q =>
    (Finset.range (y + 1)).filter (fun p => p.Prime ∧ p % (d * q) = 1 % (d * q)) with hAqdef
  have hbadq : ∀ q ∈ L.primeFactors,
      ((Aq q).card : ℝ) ≤ (303 / 25) / (1 - B) * W * (1 / (q : ℝ)) := by
    intro q hq
    have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqL : q ∣ L := Nat.dvd_of_mem_primeFactors hq
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp.two_le
    have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
    have hqx' : (q : ℝ) ≤ (x : ℝ) ^ ((1 - B) / 2) := hqx q hqp hqL
    have hcast : ((d * q : ℕ) : ℝ) = (d : ℝ) * (q : ℝ) := by push_cast; ring
    -- the modulus is at most `y^{19/20}`
    have hm2 : 2 ≤ d * q := by
      have : 1 * 2 ≤ d * q := Nat.mul_le_mul hdpos hqp.two_le
      simpa using this
    have hd_split : (d : ℝ) = (d : ℝ) ^ ((19 : ℝ) / 20) * (d : ℝ) ^ ((1 : ℝ) / 20) := by
      rw [← Real.rpow_add hdR0, show (19 : ℝ) / 20 + 1 / 20 = 1 by norm_num, Real.rpow_one]
    have h1 : (d : ℝ) ^ ((1 : ℝ) / 20) ≤ (x : ℝ) ^ (B / 20) := by
      have h := Real.rpow_le_rpow hdR0.le hdB (by norm_num : (0:ℝ) ≤ (1:ℝ)/20)
      rw [← Real.rpow_mul hx0.le] at h
      calc (d : ℝ) ^ ((1 : ℝ) / 20) ≤ (x : ℝ) ^ (B * (1 / 20)) := h
        _ = (x : ℝ) ^ (B / 20) := by rw [show B * (1/20) = B / 20 by ring]
    have h3 : (d : ℝ) ^ ((1 : ℝ) / 20) * (q : ℝ) ≤ (x : ℝ) ^ (B / 20 + (1 - B) / 2) := by
      rw [Real.rpow_add hx0]
      exact mul_le_mul h1 hqx' hq0.le (Real.rpow_nonneg hx0.le _)
    have h4 : (x : ℝ) ^ (B / 20 + (1 - B) / 2) ≤ (x : ℝ) ^ (19 * (1 - B) / 20) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
    have h6 : ((d : ℝ) * (x : ℝ) ^ (1 - B)) ^ ((19 : ℝ) / 20)
        = (d : ℝ) ^ ((19 : ℝ) / 20) * (x : ℝ) ^ (19 * (1 - B) / 20) := by
      rw [Real.mul_rpow hdR0.le hXp.le, ← Real.rpow_mul hx0.le,
        show (1 - B) * ((19 : ℝ) / 20) = 19 * (1 - B) / 20 by ring]
    have h5 : ((d : ℝ) * (x : ℝ) ^ (1 - B)) ^ ((19 : ℝ) / 20) ≤ (y : ℝ) ^ ((19 : ℝ) / 20) :=
      Real.rpow_le_rpow hprod_nonneg hy_lb (by norm_num)
    have hmy : ((d * q : ℕ) : ℝ) ≤ (y : ℝ) ^ ((19 : ℝ) / 20) := by
      rw [hcast]
      calc (d : ℝ) * (q : ℝ)
          = (d : ℝ) ^ ((19 : ℝ) / 20) * ((d : ℝ) ^ ((1 : ℝ) / 20) * (q : ℝ)) := by
            rw [← mul_assoc, ← hd_split]
        _ ≤ (d : ℝ) ^ ((19 : ℝ) / 20) * (x : ℝ) ^ (19 * (1 - B) / 20) :=
            mul_le_mul_of_nonneg_left (le_trans h3 h4) (Real.rpow_nonneg hdR0.le _)
        _ = ((d : ℝ) * (x : ℝ) ^ (1 - B)) ^ ((19 : ℝ) / 20) := h6.symm
        _ ≤ (y : ℝ) ^ ((19 : ℝ) / 20) := h5
    have hy₁y : y₁ ≤ y := by
      have h : (y₁ : ℝ) ≤ (y : ℝ) := by nlinarith
      exact_mod_cast h
    have hBTq := hBT y (d * q) hy₁y hm2 hmy
    -- the logarithm in the Brun--Titchmarsh denominator
    have hydq : (x : ℝ) ^ ((1 - B) / 2) ≤ (y : ℝ) / ((d * q : ℕ) : ℝ) := by
      rw [hcast, le_div_iff₀ (mul_pos hdR0 hq0)]
      calc (x : ℝ) ^ ((1 - B) / 2) * ((d : ℝ) * (q : ℝ))
          ≤ (x : ℝ) ^ ((1 - B) / 2) * ((d : ℝ) * (x : ℝ) ^ ((1 - B) / 2)) := by
            have := mul_le_mul_of_nonneg_left hqx' hdR0.le
            exact mul_le_mul_of_nonneg_left this (Real.rpow_nonneg hx0.le _)
        _ = (d : ℝ) * ((x : ℝ) ^ ((1 - B) / 2) * (x : ℝ) ^ ((1 - B) / 2)) := by ring
        _ = (d : ℝ) * (x : ℝ) ^ (1 - B) := by
            rw [← Real.rpow_add hx0, show (1 - B) / 2 + (1 - B) / 2 = 1 - B by ring]
        _ ≤ (y : ℝ) := hy_lb
    have hlogq : (1 - B) / 2 * Real.log x ≤ Real.log ((y : ℝ) / ((d * q : ℕ) : ℝ)) := by
      have h := Real.log_le_log (Real.rpow_pos_of_pos hx0 ((1 - B) / 2)) hydq
      rwa [Real.log_rpow hx0] at h
    have hLqpos : 0 < Real.log ((y : ℝ) / ((d * q : ℕ) : ℝ)) := by
      have : (0 : ℝ) < (1 - B) / 2 * Real.log x := by positivity
      linarith
    -- the totient in the Brun--Titchmarsh denominator
    have hφdq : (Nat.totient d : ℝ) * ((q : ℝ) / 2) ≤ (Nat.totient (d * q) : ℝ) := by
      have h := totient_mul_prime_lower (d := d) hqp
      nlinarith
    have hΦpos : (0 : ℝ) < (Nat.totient (d * q) : ℝ) := by
      have : (0 : ℝ) < (Nat.totient d : ℝ) * ((q : ℝ) / 2) := by positivity
      linarith
    refine le_trans hBTq ?_
    rw [div_le_iff₀ (mul_pos hΦpos hLqpos)]
    have hmul : ((Nat.totient d : ℝ) * ((q : ℝ) / 2)) * ((1 - B) / 2 * Real.log x)
        ≤ (Nat.totient (d * q) : ℝ) * Real.log ((y : ℝ) / ((d * q : ℕ) : ℝ)) :=
      mul_le_mul hφdq hlogq (by positivity) hΦpos.le
    have hcoef : (0 : ℝ) ≤ (303 / 25) / (1 - B) * W * (1 / (q : ℝ)) := by positivity
    calc 3 * (y : ℝ) ≤ (303 / 100) * ((d : ℝ) * (x : ℝ) ^ (1 - B)) := by linarith
      _ = ((303 / 25) / (1 - B) * W * (1 / (q : ℝ)))
            * (((Nat.totient d : ℝ) * ((q : ℝ) / 2)) * ((1 - B) / 2 * Real.log x)) := by
          rw [hWdef]
          field_simp
          ring
      _ ≤ ((303 / 25) / (1 - B) * W * (1 / (q : ℝ)))
            * ((Nat.totient (d * q) : ℝ) * Real.log ((y : ℝ) / ((d * q : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hmul hcoef
  -- summing the discarded primes over `q ∣ L`
  have hsumbad : (∑ q ∈ L.primeFactors, ((Aq q).card : ℝ)) ≤ (303 / 800) * W := by
    calc (∑ q ∈ L.primeFactors, ((Aq q).card : ℝ))
        ≤ ∑ q ∈ L.primeFactors, (303 / 25) / (1 - B) * W * (1 / (q : ℝ)) :=
          Finset.sum_le_sum hbadq
      _ = (303 / 25) / (1 - B) * W * ∑ q ∈ L.primeFactors, (1 : ℝ) / q := by
          rw [Finset.mul_sum]
      _ ≤ (303 / 25) / (1 - B) * W * ((1 - B) / 32) := by
          have hc : (0 : ℝ) ≤ (303 / 25) / (1 - B) * W := by positivity
          exact mul_le_mul_of_nonneg_left hS hc
      _ = (303 / 800) * W := by field_simp; ring
  -- the arithmetic of `p = dk+1` for the primes counted by `A`
  have hyx : y ≤ x := by exact_mod_cast hy_ub
  have hkey : ∀ p ∈ A, d * ((p - 1) / d) + 1 = p ∧ 1 ≤ (p - 1) / d ∧
      (p - 1) / d ≤ ⌊(x : ℝ) ^ (1 - B)⌋₊ ∧ p ≤ y := by
    intro p hp
    rw [hAdef, Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hpy, hpp, hpmod⟩ := hp
    have hmodeq : Nat.ModEq d p 1 := hpmod
    have hp2 : 2 ≤ p := hpp.two_le
    have hdvd : d ∣ p - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hmodeq.symm
    have hdk : d * ((p - 1) / d) = p - 1 := Nat.mul_div_cancel' hdvd
    have hk1 : 1 ≤ (p - 1) / d :=
      (Nat.one_le_div_iff hdpos).mpr (Nat.le_of_dvd (by omega) hdvd)
    refine ⟨by omega, hk1, ?_, by omega⟩
    have h1 : (d : ℝ) * (((p - 1) / d : ℕ) : ℝ) + 1 ≤ (y : ℝ) := by
      have h : d * ((p - 1) / d) + 1 ≤ y := by omega
      exact_mod_cast h
    have h2 : (y : ℝ) < (d : ℝ) * (x : ℝ) ^ (1 - B) + 1 := Nat.ceil_lt_add_one hprod_nonneg
    have h3 : (d : ℝ) * (((p - 1) / d : ℕ) : ℝ) < (d : ℝ) * (x : ℝ) ^ (1 - B) := by linarith
    exact Nat.le_floor (le_of_lt (lt_of_mul_lt_mul_left h3 hdR0.le))
  -- the good primes: `(p-1)/d` coprime to `L`
  set A₀ : Finset ℕ := A.filter (fun p => ((p - 1) / d).Coprime L) with hA₀def
  have hsplit : (A.card : ℝ) ≤ (A₀.card : ℝ) + ∑ q ∈ L.primeFactors, ((Aq q).card : ℝ) := by
    have hsub : A.filter (fun p => ¬ ((p - 1) / d).Coprime L) ⊆ L.primeFactors.biUnion Aq := by
      intro p hp
      rw [Finset.mem_filter] at hp
      obtain ⟨hpA, hncop⟩ := hp
      obtain ⟨hrec, -, -, hpley⟩ := hkey p hpA
      have hpA' := hpA
      rw [hAdef, Finset.mem_filter, Finset.mem_range] at hpA'
      obtain ⟨-, hpp, -⟩ := hpA'
      have hg1 : Nat.gcd ((p - 1) / d) L ≠ 1 := hncop
      have hqp : (Nat.gcd ((p - 1) / d) L).minFac.Prime := Nat.minFac_prime hg1
      have hqk : (Nat.gcd ((p - 1) / d) L).minFac ∣ (p - 1) / d :=
        (Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _)
      have hqL : (Nat.gcd ((p - 1) / d) L).minFac ∣ L :=
        (Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
      refine Finset.mem_biUnion.mpr ⟨(Nat.gcd ((p - 1) / d) L).minFac,
        Nat.mem_primeFactors.mpr ⟨hqp, hqL, hL0⟩, ?_⟩
      rw [hAqdef]
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hpp, ?_⟩
      have hdvd2 : d * (Nat.gcd ((p - 1) / d) L).minFac ∣ p - 1 := by
        have : d * (Nat.gcd ((p - 1) / d) L).minFac ∣ d * ((p - 1) / d) :=
          mul_dvd_mul_left d hqk
        rwa [show d * ((p - 1) / d) = p - 1 by omega] at this
      exact (Nat.ModEq.symm ((Nat.modEq_iff_dvd' (by omega : 1 ≤ p)).mpr hdvd2))
    have hnat : A.card ≤ A₀.card + ∑ q ∈ L.primeFactors, (Aq q).card := by
      have hcards := Finset.card_filter_add_card_filter_not (s := A)
        (p := fun p => ((p - 1) / d).Coprime L)
      have h2 : (A.filter (fun p => ¬ ((p - 1) / d).Coprime L)).card
          ≤ ∑ q ∈ L.primeFactors, (Aq q).card :=
        le_trans (Finset.card_le_card hsub) Finset.card_biUnion_le
      rw [hA₀def]
      omega
    exact_mod_cast hnat
  -- the injection `p ↦ (p-1)/d` into the set of admissible shifts
  have hinj : (A₀.card : ℝ) ≤
      ((((Finset.Icc 1 ⌊(x : ℝ) ^ (1 - B)⌋₊).filter (fun k => k.Coprime L)).filter
          (fun k => (d * k + 1).Prime ∧ d * k + 1 ≤ x)).card : ℝ) := by
    have hnat : A₀.card ≤ (((Finset.Icc 1 ⌊(x : ℝ) ^ (1 - B)⌋₊).filter
        (fun k => k.Coprime L)).filter (fun k => (d * k + 1).Prime ∧ d * k + 1 ≤ x)).card := by
      refine Finset.card_le_card_of_injOn (fun p => (p - 1) / d) ?_ ?_
      · intro p hp
        have hp' := Finset.mem_coe.mp hp
        rw [hA₀def, Finset.mem_filter] at hp'
        obtain ⟨hpA, hcop⟩ := hp'
        obtain ⟨hrec, hk1, hkle, hpley⟩ := hkey p hpA
        have hpA' := hpA
        rw [hAdef, Finset.mem_filter, Finset.mem_range] at hpA'
        obtain ⟨-, hpp, -⟩ := hpA'
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨⟨hk1, hkle⟩, hcop⟩, ?_, ?_⟩
        · rw [hrec]; exact hpp
        · rw [hrec]; omega
      · intro p₁ h₁ p₂ h₂ heq
        have e₁ := (hkey p₁ (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).1).1
        have e₂ := (hkey p₂ (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).1).1
        have : d * ((p₁ - 1) / d) + 1 = d * ((p₂ - 1) / d) + 1 := by
          rw [show (p₁ - 1) / d = (p₂ - 1) / d from heq]
        omega
    exact_mod_cast hnat
  -- the constant budget
  have hgood : (1 : ℝ) / 20 * W ≤ (A₀.card : ℝ) := by linarith
  calc (1 : ℝ) / 20 * ((x : ℝ) ^ (1 - B) / Real.log x) ≤ (1 : ℝ) / 20 * W := by linarith
    _ ≤ (A₀.card : ℝ) := hgood
    _ ≤ _ := hinj

end PerDivisor

/-! ### AGP Theorem 4.1: the pigeonhole -/

set_option maxHeartbeats 1000000 in
/-- AGP Theorem 4.1 at a generic `B ∈ (1/5, 2/5]`, from `𝓑`-membership plus
Brun--Titchmarsh and a Chebyshev lower bound for `π`. -/
theorem pigeonhole_of_BMembership (B : ℝ) (hB : 1 / 5 < B) (hB' : B ≤ 2 / 5)
    (𝓑 : BMembership B) (hBT : BrunTitchmarsh) (hpiL : PiLower) :
    ∃ D z₃ : ℕ, ∀ x L : ℕ, z₃ < x → 1 < L → Squarefree L →
      (∀ q : ℕ, q.Prime → q ∣ L → (q : ℝ) ≤ (x : ℝ) ^ ((1 - B) / 2)) →
      (∑ q ∈ L.primeFactors, (1 : ℝ) / q) ≤ (1 - B) / 32 →
      ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ (x : ℝ) ^ (1 - B) ∧ k.Coprime L ∧
        (2 : ℝ) ^ (-(D : ℝ) - 2) / Real.log x *
          ((L.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (x : ℝ) ^ B)).card : ℝ)
        ≤ ((L.divisors.filter (fun d => d * k + 1 ≤ x ∧ (d * k + 1).Prime)).card : ℝ) := by
  classical
  obtain ⟨y₀, hpi⟩ := hpiL
  obtain ⟨y₁, hBT'⟩ := hBT
  set C : ℝ := max 100 (max (y₀ : ℝ) (y₁ : ℝ)) with hCdef
  have hC100 : (100 : ℝ) ≤ C := le_max_left _ _
  have hCy : (y₀ : ℝ) ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hCy1 : (y₁ : ℝ) ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have hCpos : (0 : ℝ) < C := by linarith
  refine ⟨𝓑.D + 3, max (max 𝓑.x₂ 3) ⌈C ^ ((5 : ℝ) / 3)⌉₊, ?_⟩
  intro x L hxz hL1 hL hqx hS
  -- the thresholds
  have hx2 : 𝓑.x₂ ≤ x :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_left _ _)) hxz)
  have hx3 : 3 ≤ x :=
    le_of_lt (lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_left _ _)) hxz)
  have hxR : (3 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx3
  have hx0 : (0 : ℝ) < (x : ℝ) := by linarith
  have hx1 : (1 : ℝ) < (x : ℝ) := by linarith
  have hLg : 0 < Real.log x := Real.log_pos hx1
  have hXp : (0 : ℝ) < (x : ℝ) ^ (1 - B) := Real.rpow_pos_of_pos hx0 _
  have hxC : C ^ ((5 : ℝ) / 3) ≤ (x : ℝ) := by
    have h1 : (⌈C ^ ((5 : ℝ) / 3)⌉₊ : ℝ) ≤ (x : ℝ) := by
      have : ⌈C ^ ((5 : ℝ) / 3)⌉₊ ≤ x :=
        le_of_lt (lt_of_le_of_lt (le_max_right _ _) hxz)
      exact_mod_cast this
    exact le_trans (Nat.le_ceil _) h1
  have hXpC : C ≤ (x : ℝ) ^ (1 - B) := by
    have h2 : C ≤ (x : ℝ) ^ ((3 : ℝ) / 5) := by
      have h := Real.rpow_le_rpow (le_of_lt (Real.rpow_pos_of_pos hCpos _)) hxC
        (by norm_num : (0 : ℝ) ≤ (3 : ℝ) / 5)
      rwa [← Real.rpow_mul hCpos.le, show (5 : ℝ) / 3 * ((3 : ℝ) / 5) = 1 by norm_num,
        Real.rpow_one] at h
    exact le_trans h2 (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith))
  have h100 : (100 : ℝ) ≤ (x : ℝ) ^ (1 - B) := le_trans hC100 hXpC
  have hy0 : (y₀ : ℝ) ≤ (x : ℝ) ^ (1 - B) := le_trans hCy hXpC
  have hy1 : (y₁ : ℝ) ≤ (x : ℝ) ^ (1 - B) := le_trans hCy1 hXpC
  -- the reduced modulus `L'` (AGP (4.1))
  obtain ⟨L', hL'pos, hL'dvd, hL'bad, hL'count⟩ :=
    exists_reduced_modulus hL (𝓑.bad x) 𝓑.D (𝓑.bad_card x) (𝓑.bad_ge_two x)
  set K₀ : ℕ := ⌊(x : ℝ) ^ (1 - B)⌋₊ with hK₀def
  set Kfin : Finset ℕ := (Finset.Icc 1 K₀).filter (fun k => k.Coprime L) with hKdef
  set Dfin : Finset ℕ := L'.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (x : ℝ) ^ B) with hDdef
  -- the per-divisor count
  have hper : ∀ d ∈ Dfin, (1 : ℝ) / 20 * ((x : ℝ) ^ (1 - B) / Real.log x) ≤
      ((Kfin.filter (fun k => (d * k + 1).Prime ∧ d * k + 1 ≤ x)).card : ℝ) := by
    intro d hd
    rw [hDdef, Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdL', -⟩, hdB⟩ := hd
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdL' hL'pos
    have hdbad : ∀ m ∈ 𝓑.bad x, ¬ m ∣ d := fun m hm hmd => hL'bad m hm (hmd.trans hdL')
    exact per_divisor_lower hB hB' 𝓑 hBT' hpi hL.ne_zero hqx hS hx2 hx3 h100 hy0 hy1
      hdpos hdB hdbad
  -- double counting the pairs `(d, k)`
  have hcount : ∑ k ∈ Kfin, ((Dfin.filter (fun d => (d * k + 1).Prime ∧ d * k + 1 ≤ x)).card : ℝ)
      = ∑ d ∈ Dfin, ((Kfin.filter (fun k => (d * k + 1).Prime ∧ d * k + 1 ≤ x)).card : ℝ) := by
    have hnat : ∑ k ∈ Kfin, (Dfin.filter (fun d => (d * k + 1).Prime ∧ d * k + 1 ≤ x)).card
        = ∑ d ∈ Dfin, (Kfin.filter (fun k => (d * k + 1).Prime ∧ d * k + 1 ≤ x)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    exact_mod_cast hnat
  have hsum_lb : (Dfin.card : ℝ) * ((1 : ℝ) / 20 * ((x : ℝ) ^ (1 - B) / Real.log x))
      ≤ ∑ d ∈ Dfin, ((Kfin.filter (fun k => (d * k + 1).Prime ∧ d * k + 1 ≤ x)).card : ℝ) := by
    calc (Dfin.card : ℝ) * ((1 : ℝ) / 20 * ((x : ℝ) ^ (1 - B) / Real.log x))
        = ∑ _d ∈ Dfin, ((1 : ℝ) / 20 * ((x : ℝ) ^ (1 - B) / Real.log x)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hper
  -- the shift range
  have hK₀pos : 1 ≤ K₀ := Nat.le_floor (by exact_mod_cast (by linarith : (1:ℝ) ≤ (x:ℝ)^(1-B)))
  have hKne : Kfin.Nonempty := by
    refine ⟨1, ?_⟩
    rw [hKdef]
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_refl 1, hK₀pos⟩, Nat.coprime_one_left L⟩
  have hKcard : (Kfin.card : ℝ) ≤ (x : ℝ) ^ (1 - B) := by
    have h1 : Kfin.card ≤ K₀ := by
      calc Kfin.card ≤ (Finset.Icc 1 K₀).card := by
            rw [hKdef]; exact Finset.card_filter_le _ _
        _ = K₀ := by rw [Nat.card_Icc]; omega
    exact le_trans (by exact_mod_cast h1) (Nat.floor_le hXp.le)
  -- the pigeonhole over `k`
  have hex : ∃ k ∈ Kfin, (1 : ℝ) / 20 * (Dfin.card : ℝ) / Real.log x
      ≤ ((Dfin.filter (fun d => (d * k + 1).Prime ∧ d * k + 1 ≤ x)).card : ℝ) := by
    refine Finset.exists_le_of_sum_le hKne ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hnn : (0 : ℝ) ≤ (1 : ℝ) / 20 * (Dfin.card : ℝ) / Real.log x :=
      div_nonneg (by positivity) hLg.le
    calc (Kfin.card : ℝ) * ((1 : ℝ) / 20 * (Dfin.card : ℝ) / Real.log x)
        ≤ (x : ℝ) ^ (1 - B) * ((1 : ℝ) / 20 * (Dfin.card : ℝ) / Real.log x) :=
          mul_le_mul_of_nonneg_right hKcard hnn
      _ = (Dfin.card : ℝ) * ((1 : ℝ) / 20 * ((x : ℝ) ^ (1 - B) / Real.log x)) := by ring
      _ ≤ ∑ d ∈ Dfin, ((Kfin.filter (fun k => (d * k + 1).Prime ∧ d * k + 1 ≤ x)).card : ℝ) :=
          hsum_lb
      _ = ∑ k ∈ Kfin, ((Dfin.filter (fun d => (d * k + 1).Prime ∧ d * k + 1 ≤ x)).card : ℝ) :=
          hcount.symm
  obtain ⟨k, hkK, hk⟩ := hex
  have hkK' := hkK
  rw [hKdef, Finset.mem_filter, Finset.mem_Icc] at hkK'
  obtain ⟨⟨hk1, hkK₀⟩, hkcop⟩ := hkK'
  refine ⟨k, hk1, le_trans (by exact_mod_cast hkK₀) (Nat.floor_le hXp.le), hkcop, ?_⟩
  -- the constant bookkeeping
  have hsubset : Dfin.filter (fun d => (d * k + 1).Prime ∧ d * k + 1 ≤ x)
      ⊆ L.divisors.filter (fun d => d * k + 1 ≤ x ∧ (d * k + 1).Prime) := by
    intro d hd
    rw [Finset.mem_filter, hDdef, Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨⟨hdL', -⟩, -⟩, hpr, hle⟩ := hd
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdL'.trans hL'dvd, hL.ne_zero⟩, hle, hpr⟩
  have hcards : ((Dfin.filter (fun d => (d * k + 1).Prime ∧ d * k + 1 ≤ x)).card : ℝ)
      ≤ ((L.divisors.filter (fun d => d * k + 1 ≤ x ∧ (d * k + 1).Prime)).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsubset
  have htransfer : ((L.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (x : ℝ) ^ B)).card : ℝ)
      ≤ 2 ^ 𝓑.D * (Dfin.card : ℝ) := by
    have h := hL'count ((x : ℝ) ^ B)
    rw [← hDdef] at h
    exact_mod_cast h
  have hpow : (2 : ℝ) ^ (-((𝓑.D + 3 : ℕ) : ℝ) - 2) * 2 ^ 𝓑.D = 1 / 32 := by
    have e1 : (2 : ℝ) ^ (-((𝓑.D : ℕ) : ℝ)) = ((2 : ℝ) ^ 𝓑.D)⁻¹ := by
      rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
    have e2 : (2 : ℝ) ^ (-5 : ℝ) = 1 / 32 := by
      rw [show (-5 : ℝ) = ((-5 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      norm_num
    rw [show (-((𝓑.D + 3 : ℕ) : ℝ) - 2) = -5 + -((𝓑.D : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add (by norm_num : (0:ℝ) < 2), e1, e2]
    have h2 : ((2 : ℝ) ^ 𝓑.D) ≠ 0 := by positivity
    field_simp
  have hDfin_nonneg : (0 : ℝ) ≤ (Dfin.card : ℝ) := by positivity
  calc (2 : ℝ) ^ (-((𝓑.D + 3 : ℕ) : ℝ) - 2) / Real.log x *
        ((L.divisors.filter (fun d : ℕ => (d : ℝ) ≤ (x : ℝ) ^ B)).card : ℝ)
      ≤ (2 : ℝ) ^ (-((𝓑.D + 3 : ℕ) : ℝ) - 2) / Real.log x * (2 ^ 𝓑.D * (Dfin.card : ℝ)) := by
        refine mul_le_mul_of_nonneg_left htransfer ?_
        exact div_nonneg (Real.rpow_nonneg (by norm_num) _) hLg.le
    _ = (1 / 32) * (Dfin.card : ℝ) / Real.log x := by
        rw [← hpow]; ring
    _ ≤ (1 : ℝ) / 20 * (Dfin.card : ℝ) / Real.log x := by
        have hnum : (1 / 32 : ℝ) * (Dfin.card : ℝ) ≤ (1 : ℝ) / 20 * (Dfin.card : ℝ) := by
          nlinarith [hDfin_nonneg]
        exact (div_le_div_iff_of_pos_right hLg).mpr hnum
    _ ≤ ((Dfin.filter (fun d => (d * k + 1).Prime ∧ d * k + 1 ≤ x)).card : ℝ) := hk
    _ ≤ _ := hcards

end Carmichael
