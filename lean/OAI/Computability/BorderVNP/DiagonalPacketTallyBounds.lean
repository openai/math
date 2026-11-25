import OAI.Computability.BorderVNP.DiagonalPayloadBound
import OAI.Computability.BorderVNP.DiagonalNumberedTallies
import OAI.Computability.BorderVNP.CubePhysicalTally
import OAI.Computability.BorderVNP.DiagonalTallyPacketRecipe

/-! # Counting all scalar occurrences on an assigned packet path -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing Diagonal Diagonal.CellEntries
open scoped BigOperators Classical

set_option synthInstance.maxSize 1000

variable {n d blocks b h K s D B : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type}
    [Fintype Cell] [DecidableEq Cell] {Team Param Gadget : Type*} [Fintype Team] [Fintype Param]
    {N : Network D P bits} {cell : N.Site → Cell}
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (tags : N.Tables (Entry Param Gadget))
    (x : Ports bits) (pos : Packet n d blocks → TableEntry n b h K s → Gadget)
    (words : PowerWords Team Param Gadget B N tags) (label : Cell → Label (n+1) d)
    (team : Fin d → Team)

omit [Fintype Cell] [DecidableEq Cell] [Fintype Param] in
/-- On any actual path, a cube vertex selects exactly one local table
position. The public owner of this vertex can depend on the entire selector. -/
theorem pathExtra_count_le_one (a : Path N cell n d blocks b h K s)
    (v : Packet n d blocks × Vertex (n+1)) (g : Gadget) :
    (counters (pathExtra (Param := Param) pos a v)).2 g ≤ 1 := by
  let selected := pos v.1 (Cube.Tally.packetEntry D b s (a.2.2.2.1 v.1) v.2 (a.2.2.1 v.1) (a.2.2.2.2 v.1))
  change (Finsupp.single selected (1:ℕ)) g ≤ 1
  classical
  by_cases h : selected = g <;> simp [h]

omit [Fintype Cell] in
/-- Every global scalar multiplicity fits the total expanded host payload
plus one table use for each packet vertex, independent of owner and field. -/
theorem pathTally_count_le {payload : N.Site → ℕ} (ht : PayloadBound tags payload)
    (a : Path N cell n d blocks b h K s) (g : Gadget) :
    (∑ t, (pathTally slot tags x pos words label team a).counts t g) ≤
      (∑ v, payload v) + Fintype.card (Packet n d blocks × Vertex (n+1)) :=
  words.counts_le_payload (pathEdges slot a) (fun _ p => x p.val) (pathExtra pos a)
    (pathOwner label team a) ht (pathExtra_count_le_one pos a) g

end Cube.Physical

namespace Diagonal.Tally

open scoped BigOperators Classical

/-- Numbering teams and parameter labels for the entry reader preserves each
scalar's exact total multiplicity. -/
theorem sum_renumber_counts {T U P Q G : Type*} [Fintype T] [Fintype U]
    {b : ℕ} (teams : T ≃ U) (params : P ≃ Q) (t : Tally T P G b) (g : G) :
    (∑ u, (t.renumber teams params).counts u g) = ∑ v, t.counts v g :=
  Fintype.sum_equiv teams.symm _ _ (fun _ => rfl)

end Diagonal.Tally

end BorderVNP
end Computability
end OAI
