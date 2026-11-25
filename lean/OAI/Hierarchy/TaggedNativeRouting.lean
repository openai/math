import OAI.Hierarchy.TaggedPruning

namespace OAI
/-! # Physical terminal routings at a fixed tagged parent format -/

noncomputable section
namespace Hierarchy.Tagged
open TaggedPrune
open scoped BigOperators

/-- The protocol before configuring any shorter calls. Its globally scheduled
terminal terms give one exact per-tag routing sum, and every terminal coefficient
has a local restriction to the installed physical chord widths. -/
structure NativeRouting (F : Type*) [Field F] (k h w M : ℕ) where
  catalyst : Fin k → ℕ
  selectors : ℕ
  Shared : Type
  [finiteShared : Fintype Shared]
  layout : TaggedPrune.Layout h w catalyst
  count : Equiv.Perm (Row h) → ℕ
  encoding : Encoding count selectors
  route : Index count → Table F h w catalyst
  links : Index count → Links layout M
  routing : ∀ perm, (∑ i : Fin (count perm),route ⟨perm,i⟩) = perTag perm
  tables : ∀ a, ((CorrectionProducts.raw (route a)).group layout.port).Restricts
    (LinearAlgebra.SpectralBooks.ChordGraph.raw F
      (AdaptiveProbe.installedWidths (links a).ends (links a).bits))
attribute [instance] NativeRouting.finiteShared

end Hierarchy.Tagged

end
end OAI
