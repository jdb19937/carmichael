/-
The main theorem of the paper, conditional on the assumption pack:

For every ε > 0 there is C > 0 such that for all sufficiently large n, a
Carmichael number m ∈ (n, n^{1+ε}] exists together with its full prime
factorization (the certificate of step 5), and opBudget n ≤ exp(C ℓ₂ ℓ₃).
`opBudget` is the explicit operation budget of the paper's Section-3
search; the correspondence between that expression and the search's
operation count is the documented convention of `Budget.lean`, not itself
a Lean theorem (no machine model is formalized).

`∀ᶠ n in atTop` is the paper's "for n ≥ n₀, n₀ computable in principle":
each threshold traces back to the named constants of the assumption pack
and finitely many explicit comparisons.
-/
import Carmichael.Lemmas

namespace Carmichael

open Filter

/-- Main theorem (operation-count form). The budget constant `C` is
uniform: it does not depend on `ε`. -/
theorem carmichael_exists_of_assumptions (A : Assumptions) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n : ℕ in atTop,
        (∃ m : ℕ, ∃ S : Finset ℕ,
          (∀ p ∈ S, p.Prime) ∧ 3 ≤ S.card ∧ m = ∏ p ∈ S, p ∧
          IsCarmichael m ∧
          n < m ∧ (m : ℝ) ≤ (n : ℝ) ^ (1 + ε)) ∧
        opBudget A n ≤ Real.exp (C * ell2 n * ell3 n) := by
  obtain ⟨C, hC, hbudget⟩ := opBudget_le A
  refine ⟨C, hC, fun ε hε => ?_⟩
  filter_upwards [step2_succeeds A, step3_halts A, extraction A,
    output_carmichael A ε hε, hbudget] with n h2 h3 h4 h5 hb
  refine ⟨?_, hb⟩
  -- Step 2: choose Q ⊆ goodPrimes with |Q| = T.
  obtain ⟨Q, hQsub, hQcard⟩ :=
    Finset.exists_subset_card_eq h2
  -- Step 3: choose the shift k.
  obtain ⟨k, hk, hkx, hkL, hpool⟩ := h3 Q hQsub hQcard
  -- Step 4: extract S.
  obtain ⟨S, hSsub, hSne, hSmod, hSgt, hSle⟩ :=
    h4 Q hQsub hQcard k hk hkL hpool
  -- Step 5: the certificate.
  obtain ⟨hprime, hcard, hcarm, hupper⟩ :=
    h5 Q hQsub hQcard k hk hkL S hSsub hSne hSmod hSgt hSle
  exact ⟨∏ p ∈ S, p, S, hprime, hcard, rfl, hcarm, hSgt, hupper⟩

end Carmichael
