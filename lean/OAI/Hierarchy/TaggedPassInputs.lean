import OAI.Hierarchy.TaggedPassHoles
import OAI.Hierarchy.TaggedPassExit
import OAI.Hierarchy.TaggedBlockRecords

namespace OAI
/-! # Rectangular input wiring and retained block prefixes of a radix pass -/

noncomputable section
namespace Hierarchy.Tagged.Radix.PassShape
open ThreeFlat Routing SortNetwork RadixStage
open scoped Classical

abbrev LocalData (s : PassShape) (w : ℕ) := Fin s.blocks × SortRelation.Data s.localBits w

/-- Padding the local banks uses dummy literals for each nonphysical source. -/
def enter (s : PassShape) {w : ℕ} (dummy : Fin w → Bool) : StaticMap (RowBits s.rows w) (s.LocalData w) :=
  fun (b,i) => blockScatter s.rows s.blocks s.block (2^s.localBits) w dummy
    (b,(Fintype.equivFin (Payload s.localBits w)).symm i)

/-- Read the fixed retained block prefixes into the contiguous pack words.
The remaining global pack addresses are all dummy, with the same word format. -/
def wideInput (s : PassShape) {w : ℕ} (dummy : Fin w → Bool) : StaticMap (s.LocalData w) (s.WideData w) := fun p =>
  let r := (Fintype.equivFin (Payload s.globalHeight (s.pack*w))).symm p
  let l : Fin s.pack × Fin w := finProdFinEquiv.symm r.2
  let slot := r.1.val*s.pack+l.1.val
  let b := slot/s.perBlock
  let i := slot%s.perBlock
  if h : b < s.blocks ∧ i < 2^s.localBits then
    .inl (⟨b,h.1⟩, Fintype.equivFin _ (⟨i,h.2⟩,l.2))
  else .inr (dummy l.2)

end Hierarchy.Tagged.Radix.PassShape
end

end OAI
