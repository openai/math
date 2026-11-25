import OAI.Hierarchy.DescentDatedPrimitiveRead
import OAI.Hierarchy.DescentOrdinaryFinalCount

namespace OAI
/-! The final ordinary counter preserves the exact primitive bank required by the next numbered date. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentPackedColony DescentOrdinaryPrimitiveCheckpoint ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) {w : ℕ}
local notation "L" => v.paletteShape
local notation "edge" => v.operandEnd floor
local notation "b" x => v.primitiveBank edge x

theorem primitiveBank_placed (room : v.primitiveEnd floor<2^w) (x : Fin (L).blocks) :
    (b x).Fits w (v.primitiveEnd floor) ∧ (L).successors*chunks (L).groups v.palette.nextLanes≤(b x).size:=
  (L).durable.placed ((L).durableStart (v.primitiveFirst edge)) room x

theorem primitive_return (m : Memory w) (x : Fin (L).blocks)
    (values : Fin (L).successors→Fin (L).groups→Cell ((L).primitiveBits*(L).newNodes))
    (top : (v.area.matcher v.old floor).layout.topology.Fits w (v.primitiveEnd floor))
    (room : v.returnedEnd floor<2^w) (endRoom : v.primitiveEnd floor<2^w)
    (posted : Reads (b x) values v.palette.nextLanes m) :
    Reads (b x) values v.palette.nextLanes ((v.counter floor w).image m):=by
  obtain ⟨fit,rows⟩:=v.primitiveBank_placed floor endRoom x
  exact Layout.carry_reads fit rows (fun a ha=>(v.counter_run floor m top room).2 a (.inl ha)) posted

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
