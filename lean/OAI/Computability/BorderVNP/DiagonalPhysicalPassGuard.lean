import OAI.Computability.BorderVNP.CubePhysicalTally
import OAI.Computability.BorderVNP.CubePhysicalNativeAssignments
import OAI.Computability.BorderVNP.PackedInheritedMergedEnds

/-! # Native zero-padding and original site checks for a physical cube path -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing Diagonal.CellEntries
open scoped Classical BigOperators

variable {n d blocks b h K s D : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type} {Param Gadget : Type*}
    [Fintype Cell] [DecidableEq Cell] (N : Network D P bits) (cell : N.Site → Cell)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (tags : N.Tables (Entry Param Gadget))
    (ports : Ports bits) (pos : Packet n d blocks → TableEntry n b h K s → Gadget)

/-- The two real endpoint pins on all padded physical slots, including
every unused slot of the common packet capacity. -/
def Path.Pins (a : Path N cell n d blocks b h K s) : Prop :=
  ∀ i ∉ Set.range slot, readEnd a.2.1 a.2.2.1 false i = false ∧ readEnd a.2.1 a.2.2.1 true i = false

/-- The physical path's tagged guard consists exactly of all native
padding pins and all original site checks. Each selected cube table
address is a passing scalar occurrence, irrespective of its field value. -/
theorem pathTag_nonzero_iff (a : Path N cell n d blocks b h K s) :
    pathTag N cell slot tags ports pos a ≠ 0 ↔ Path.Pins N cell slot a ∧
      ∀ v, tags v (pathEdges slot a v) (fun p => ports p.val) ≠ 0 := by
  unfold pathTag globalEntry
  have cubes : ∏ i, assignmentEntry (packetNetwork D b s (a.2.2.2.1 i))
      (packetTables (fun p => gadget (Param:=Param) (pos i p)) D (a.2.2.2.1 i))
      (a.2.2.2.2 i) (a.2.2.1 i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro v _
    exact WithZero.coe_ne_zero
  rw [mul_ne_zero_iff]
  refine (and_iff_left cubes).trans ?_
  unfold host
  split_ifs with pad
  · change (∏ c, ∏ v : {v : N.Site // cell v=c}, _) ≠ 0 ↔ _
    constructor
    · intro nz
      refine ⟨pad,fun v => ?_⟩
      have hc := Finset.prod_ne_zero_iff.mp nz (cell v) (Finset.mem_univ _)
      exact Finset.prod_ne_zero_iff.mp hc ⟨v,rfl⟩ (Finset.mem_univ _)
    · rintro ⟨_,sites⟩
      exact Finset.prod_ne_zero_iff.mpr fun c _ => Finset.prod_ne_zero_iff.mpr fun v _ => sites v.val
  · exact ⟨fun h => (h rfl).elim,fun h => (pad h.1).elim⟩

end Cube.Physical

end BorderVNP
end Computability
end OAI
