module

public import VaughtConjecture.CountableCover
public import Lean

/-! Separate-module export regression for the first migrated leaf. -/

@[expose] public section

namespace PalomarMigrationTests

theorem countableCoverConsumer {ι κ : Type*} [Countable κ] (P : κ → ι → Prop)
    (hsub : ∀ c i j, P c i → P c j → i = j) (hcover : ∀ i, ∃ c, P c i) :
    Countable ι :=
  VaughtConjecture.CountableCover.countable_of_cover P hsub hcover

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for root in #[``VaughtConjecture.CountableCover.countable_of_cover,
      ``countableCoverConsumer] do
    for ax in ← collectAxioms root do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {root}"
  logInfo "Migrated leaf and separate importing consumer use standard axioms only."

end PalomarMigrationTests
