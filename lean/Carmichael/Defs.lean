/-
Definitions for "A deterministic quasi-polylogarithmic algorithm for
constructing Carmichael numbers" (carmichael.tex).

This file defines the objects of Sections 1 and 3 of the paper: the iterated
logarithms, Carmichael numbers, smoothness, and the scales and search spaces
of the algorithm (steps 1-4).
-/
import Mathlib

namespace Carmichael

/-- `ℓ₂(n) = log log n` (natural logarithms throughout). -/
noncomputable def ell2 (n : ℕ) : ℝ := Real.log (Real.log n)

/-- `ℓ₃(n) = log log log n`. -/
noncomputable def ell3 (n : ℕ) : ℝ := Real.log (ell2 n)

/-- A Carmichael number: a composite `m` with `a ^ m ≡ a (mod m)` for every
integer `a`. -/
def IsCarmichael (m : ℕ) : Prop :=
  1 < m ∧ ¬ m.Prime ∧ ∀ a : ℤ, (m : ℤ) ∣ a ^ m - a

/-- `k` is `y`-smooth: every prime factor of `k` is at most `y`
(`P⁺(k) ≤ y` in the paper's notation). -/
def SmoothUpTo (y k : ℕ) : Prop := ∀ q : ℕ, q.Prime → q ∣ k → q ≤ y

/-- The prime-counting function `π(x)`, as a `Finset` count. -/
def primePi (x : ℕ) : ℕ := ((Finset.range (x + 1)).filter Nat.Prime).card

/-- The reciprocal sum `∑_{p ≤ x} 1/p` over primes, for Mertens' theorem. -/
noncomputable def primeRecipSum (x : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, (1 : ℝ) / p

/-! ### Step 1: scales -/

section Scales

variable (C₁ : ℝ) (n : ℕ)

/-- Step 1: `z = ⌈C₁ ℓ₂ ℓ₃⌉`. -/
noncomputable def zscale : ℕ := ⌈C₁ * ell2 n * ell3 n⌉₊

/-- Step 1, generic in the AGP smoothness parameter `E`:
`y = ⌈z^{1-E}⌉`. -/
noncomputable def yscaleE (E : ℝ) : ℕ :=
  ⌈(zscale C₁ n : ℝ) ^ ((1 : ℝ) - E)⌉₊

/-- Step 1: `y = ⌈z^{2/3}⌉` (the paper's `E = 1/3` instance). -/
noncomputable def yscale : ℕ := ⌈(zscale C₁ n : ℝ) ^ ((2 : ℝ) / 3)⌉₊

theorem yscale_eq_yscaleE : yscale C₁ n = yscaleE C₁ n (1 / 3) := by
  unfold yscale yscaleE
  norm_num

/-- Step 1: `T = ⌈3 ℓ₂⌉`. -/
noncomputable def Tscale : ℕ := ⌈(3 : ℝ) * ell2 n⌉₊

open Classical in
/-- Step 2 reservoir, generic in `E`: the primes `q ∈ (z^{99/100}, z]` with
`q - 1` smooth up to `yscaleE E`. -/
noncomputable def goodPrimesE (E : ℝ) : Finset ℕ :=
  (Finset.range (zscale C₁ n + 1)).filter
    (fun q => q.Prime ∧ (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) < (q : ℝ) ∧
      SmoothUpTo (yscaleE C₁ n E) (q - 1))

open Classical in
/-- Step 2 reservoir: the primes `q ∈ (z^{99/100}, z]` with `q - 1` being
`y`-smooth. The floor `z^{99/100}` keeps the reciprocal sum `∑ 1/q` below
the `3/160` demanded by AGP Theorem 3.1, via Mertens. The algorithm takes
`Q` to be the `T` largest of these; the proofs only use that `Q` is a
subset of this reservoir of cardinality `T`. This is the paper's `E = 1/3`
instance of `goodPrimesE`. -/
noncomputable def goodPrimes : Finset ℕ :=
  (Finset.range (zscale C₁ n + 1)).filter
    (fun q => q.Prime ∧ (zscale C₁ n : ℝ) ^ ((99 : ℝ) / 100) < (q : ℝ) ∧
      SmoothUpTo (yscale C₁ n) (q - 1))

theorem goodPrimes_eq_goodPrimesE : goodPrimes C₁ n = goodPrimesE C₁ n (1 / 3) := by
  unfold goodPrimes goodPrimesE
  rw [yscale_eq_yscaleE]

end Scales

/-! ### Steps 2-4: modulus, prime pool, extraction parameters -/

section Modulus

variable (Q : Finset ℕ)

/-- Step 2: the modulus `L = ∏_{q ∈ Q} q`. -/
def Lmod : ℕ := ∏ q ∈ Q, q

/-- Step 2: the prime search ceiling `x = L^5`. -/
def xceil : ℕ := Lmod Q ^ 5

/-- `λ(L) = lcm {q - 1 : q ∈ Q}`. The exponent of `(ℤ/Lℤ)ˣ` divides this
(proved in `Extraction.lean`), which is all the development uses. -/
def lambdaL : ℕ := Q.lcm (fun q => q - 1)

/-- Step 4: `N* = ⌈λ(L)(1 + log L)⌉ + 1`, the van Emde Boas--Kruyswijk
batch size. -/
noncomputable def Nstar : ℕ := ⌈(lambdaL Q : ℝ) * (1 + Real.log (Lmod Q))⌉₊ + 1

/-- Step 3 pool: `P_k = {dk+1 : d ∣ L, dk+1 ≤ x, dk+1 prime, dk+1 > z}`. -/
def pool (z k : ℕ) : Finset ℕ :=
  ((Lmod Q).divisors.filter
    (fun d => d * k + 1 ≤ xceil Q ∧ (d * k + 1).Prime ∧ z < d * k + 1)).image
    (fun d => d * k + 1)

end Modulus

end Carmichael
