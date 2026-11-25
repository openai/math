import OAI.Computability.BorderVNP.DiagonalPhysicalAssignments

/-! # Changing unused inputs on an assigned physical cube path -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing Diagonal Diagonal.CellEntries
open scoped Classical

set_option synthInstance.maxSize 900

variable {D B n d b h K s : ℕ} {A Team Param Gadget : Type} {width : A → ℕ}
    [Fintype Team] [Fintype Param] [Fintype Gadget]
    {N : Network D A width} (t : Tracked Team Param Gadget B N)
    (packet : PacketPlacement Team n d b h K N) (pos : TableEntry n b h K s → Gadget)
    (x y : Ports width)
    (tags : ∀ v a, t.tags v a (fun p => x p.val) = t.tags v a (fun p => y p.val))
    (words : ∀ v a, t.words.selected v a (fun p => x p.val) = t.words.selected v a (fun p => y p.val))

omit [Fintype Gadget] in
include tags in
/-- Agreement at each actual local table preserves the complete path check. -/
theorem input_tag_congr (a : Path N packet.cell n d packet.blocks b h K s) :
    pathTag N packet.cell packet.slot t.tags x (fun _ => pos) a =
      pathTag N packet.cell packet.slot t.tags y (fun _ => pos) a := by
  have hh : host N packet.cell packet.slot t.tags x a.1 = host N packet.cell packet.slot t.tags y a.1 := by
    funext single ends
    simp only [host,cellTag,tags]
  simp only [pathTag,hh]

omit [Fintype Gadget] in
include tags words in
/-- Agreement on tagged local reads and their use words preserves the tally. -/
theorem input_tally_congr (a : Path N packet.cell n d packet.blocks b h K s) :
    pathTally packet.slot t.tags x (fun _ => pos) t.words packet.label (packet.team a.2.2.2.1) a =
      pathTally packet.slot t.tags y (fun _ => pos) t.words packet.label (packet.team a.2.2.2.1) a := by
  have hh : t.words.localUse (pathEdges packet.slot a) (fun _ p => x p.val) =
      t.words.localUse (pathEdges packet.slot a) (fun _ p => y p.val) := by
    funext team p j
    simp only [PowerWords.localUse,words]
  simp only [pathTally,PowerWords.localTally,tags,hh]

include tags in
/-- The equivalence on passing paths acts as the identity on their bits. -/
def inputPassingEquiv : packet.Passing t x pos ≃ packet.Passing t y pos :=
  Equiv.subtypeEquivRight fun a => by rw [input_tag_congr t packet pos x y tags a]

omit [Fintype Gadget] in
include words in
/-- Replacing the input leaves all reported counts of the passing path intact. -/
theorem inputPassingEquiv_tally (a : packet.Passing t x pos) :
    packet.tally t y pos (inputPassingEquiv t packet pos x y tags a) = packet.tally t x pos a :=
  (input_tally_congr t packet pos x y tags words a.val).symm

end Cube.Physical

end BorderVNP
end Computability
end OAI
