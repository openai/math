import OAI.Hierarchy.TaggedSortedKeys
import OAI.Hierarchy.TaggedPassGeometry
import OAI.Hierarchy.TaggedRadixStatic

namespace OAI
/-! # Outgoing row layout of a packed radix pass -/

noncomputable section
namespace Hierarchy.Tagged.Radix.PassShape

open ThreeFlat Routing SortNetwork RadixStage
open scoped Classical

abbrev WideData (s : PassShape) (w : ℕ) := Fin (Fintype.card (Payload s.globalHeight (s.pack*w)))

/-- Drop dyadic surplus packs after the global stable sort and expose the
next pass's fixed number of logical row words. -/
def leave (s : PassShape) {w : ℕ} : StaticMap (s.WideData w) (RowBits s.nextRows w) := fun ⟨i,b⟩ =>
  let r := i.val/s.pack
  let lane := i.val%s.pack
  if ok : r < 2^s.globalHeight then
    .inl (Fintype.equivFin _ (⟨r,ok⟩,finProdFinEquiv (⟨lane,Nat.mod_lt _ (Nat.two_pow_pos _)⟩,b)))
  else .inr false

def wideDigit (s : PassShape) {w : ℕ} (digit : Fin s.digitBits → Fin w) (isDummy : Fin w) :
    Fin (s.digitBits+1) → Fin (s.pack*w) :=
  fun i => finProdFinEquiv (⟨0,Nat.two_pow_pos _⟩, maskedDigit digit isDummy i)

end Hierarchy.Tagged.Radix.PassShape

end
end OAI
