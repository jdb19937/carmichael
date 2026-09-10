/-
The Turing-machine form of the main theorem (Route T).

A Mathlib `TM2ComputableInTime` machine computes, from `n` in binary, a
Carmichael number `m ∈ (n, n^{1+ε}]` together with its prime factorisation,
in time `exp(C · log N · log log N)` of the input length `N`.  The proof is
in `Carmichael/TM/MainProof.lean`; this file holds the statement.
-/
import Mathlib
import Carmichael.TM.MainProof

open Computability Turing

/-- Output encoding over Mathlib's alphabet `Γ'`: `m`, then its prime factors,
each number in binary least-significant bit first (Mathlib's `encodeNat`),
each followed by a comma. -/
def encodeOutput : ℕ × List ℕ → List Γ'
  | (m, S) => (encodeNat m).map inclusionBoolΓ' ++ Γ'.comma ::
      S.flatMap (fun p => (encodeNat p).map inclusionBoolΓ' ++ [Γ'.comma])

/-- **Carmichael numbers are quickly findable, on a Turing machine.** There is a
function `f` computed by a stack Turing machine (Mathlib's `FinTM2`, eight stacks, input
`n` as `encodingNatΓ'`, output as `encodeOutput`) whose running time on inputs
of length `N` is at most `exp(C · log N · log log N)` (quasipolynomial in the
length), and for every `ε > 0` and every `n` large enough `f n = (m, S)` where
`S` is a list of three or more distinct primes, `m = ∏ S` is a Carmichael
number (composite, with `m ∣ a^m - a` for every integer `a`), and
`n < m ≤ n^{1+ε}`. -/
theorem main_theorem :
    ∃ (f : ℕ → ℕ × List ℕ)
      (h : TM2ComputableInTime encodingNatΓ'.encode encodeOutput f),
      (∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
          (h.time N : ℝ) ≤ Real.exp (C * Real.log N * Real.log (Real.log N))) ∧
      (∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ n ≥ n₀,
          (f n).2.Nodup ∧ (∀ p ∈ (f n).2, p.Prime) ∧ 3 ≤ (f n).2.length ∧
          (f n).1 = (f n).2.prod ∧
          (1 < (f n).1 ∧ ¬ (f n).1.Prime ∧
            ∀ a : ℤ, ((f n).1 : ℤ) ∣ a ^ (f n).1 - a) ∧
          n < (f n).1 ∧ ((f n).1 : ℝ) ≤ (n : ℝ) ^ (1 + ε)) :=
  Carmichael.TM.main_theorem_of encodeOutput (fun _ _ => rfl)
