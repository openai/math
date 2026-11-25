import OAI.Computability.NearSquareRoot.PrecisionBlockPhaseRank
import OAI.Computability.NearSquareRoot.SynchronizedAxisLayout

/-! # Physical size of a block measured in borrowing-batch coordinates -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

open SynchronizedBlocks ShortFourier
variable {k l : ℕ} {box : List (ℕ × ℕ)} (hb : BoxShape.Valid k l box)
  [∀ i, NeZero (modulus box i)]

include hb

/-- Each block rank represents exactly one padded multidimensional address. -/
theorem card_blockAddress (j : Fin (box.length/4)) :
    Fintype.card (BlockAddress (BoxAxis box) j) = blockRadix box j := by
  simpa using Fintype.card_congr (blockAddressRank hb j)

/-- The row-major rectangular work tape used when one axis is active
contains the entire physical block, including unused cells. -/
theorem spectator_mul_axis (j : Fin (box.length/4)) (i : Fin (count j)) :
    Fintype.card (Spectators (fun t => modulus box (axis j t)) (fun t => padding box (axis j t)) i) *
      (modulus box (axis j i) + padding box (axis j i)) = blockRadix box j := by
  let a := fun t => modulus box (axis j t)
  let c := fun t => padding box (axis j t)
  let x := Equiv.piSplitAt i (BlockAxis a c)
  have he : Fintype.card (BlockAddress (BoxAxis box) j) =
      (a i+c i)*Fintype.card (Spectators a c i) := by
    simpa [BlockAxis, Spectators, a, c] using Fintype.card_congr x
  exact (Nat.mul_comm ..).trans (he.symm.trans (card_blockAddress hb j))

end BoxFin

end NearSquareRoot
end Computability
end OAI
