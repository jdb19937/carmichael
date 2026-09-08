/- Verification harness. Each `#guard_msgs` block FAILS ELABORATION unless
`#print axioms` reports exactly Lean's three standard axioms, so
`lake env lean AxiomCheck.lean` exits nonzero if any declaration below
picks up `sorryAx`, `Lean.ofReduceBool` (native_decide), or a custom axiom.
Uses only core Lean commands — no custom metaprogramming. -/
import Carmichael.Main
import Carmichael.MainWeak
import Carmichael.Unconditional

/-- info: 'Carmichael.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.main_theorem

/-- info: 'Carmichael.step2_succeeds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.step2_succeeds

/-- info: 'Carmichael.step3_halts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.step3_halts

/-- info: 'Carmichael.extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.extraction

/-- info: 'Carmichael.output_carmichael' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.output_carmichael

/-- info: 'Carmichael.opBudget_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.opBudget_le

/-- info: 'Carmichael.korselt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.korselt

/-- info: 'Carmichael.vebk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.vebk

/-- info: 'Carmichael.chebyshev_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.chebyshev_lower

/-- info: 'Carmichael.primeRecipSum_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.primeRecipSum_sub_le

/-- info: 'Mertens.sum_mangoldt_div_eq_log' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Mertens.sum_mangoldt_div_eq_log

/-- info: 'Carmichael.main_theorem_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.main_theorem_weak

/-- info: 'Carmichael.smooth_shifted_weak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.smooth_shifted_weak

/-- info: 'Carmichael.twin_type_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.twin_type_bound

/-- info: 'Carmichael.selberg_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.selberg_bound

/-- info: 'Carmichael.main_theorem_weak_of_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.main_theorem_weak_of_logged

/-- info: 'Carmichael.main_theorem_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.main_theorem_unconditional

/-- info: 'Carmichael.pigeonhole_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.pigeonhole_unconditional

/-- info: 'Carmichael.LoggedDensity.loggedDensity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.LoggedDensity.loggedDensity

/-- info: 'Carmichael.ZeroDensity.logfree_of_logged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.ZeroDensity.logfree_of_logged

/-- info: 'Carmichael.CensusMid.midCensusHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Carmichael.CensusMid.midCensusHyp
