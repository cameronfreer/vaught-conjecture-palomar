module

public import Palomar.Solution
public import Lean

/-! A focused standard-axiom check of the independent statement's solution. -/

@[expose] public section

open Lean in
run_cmd do
  let roots := #[``PalomarChallenge.independent_challenge,
    ``PalomarChallenge.isomorphic_iff_library, ``PalomarChallenge.knight_modelSetoid_eq]
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for root in roots do
    for ax in ← collectAxioms root do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {root}"
  logInfo "Independent-statement solution and both bridges use standard axioms only."
