import OAI.Hierarchy.DescentDatedOrdinaryCountRoof
import OAI.Hierarchy.DescentStageVenueAny
import OAI.Hierarchy.DescentPackedMatchChunk
import OAI.Hierarchy.DescentDatedVenueBelow

namespace OAI
/-! # The final ordinary count from the retained original matcher topology -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch DescentPacking.PackedMatch.Local.Stage DescentOrdinaryCountScan DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ)
set_option quotPrecheck false
local notation "top" => (v.area.matcher v.old floor).layout.topology
local notation "f" => chunkCount v.area.shapeAt v.area.lanesAt
local notation "N" => v.area.batch
local notation "countAt" => v.primitiveEnd floor

def counter (w : ℕ) : NativePhase w where
  program:=DescentOrdinaryCountScan.program w top f countAt N
  ticks:=DescentOrdinaryCountScan.clock v.countBits N
  image:=DescentOrdinaryCountScan.output top f countAt N
  cheap:=(DescentOrdinaryCountScan.hardware w top f countAt N).1

theorem counter_run {w : ℕ} (m : Memory w) (source : (top).Fits w countAt) (room : v.returnedEnd floor<2^w) :
    (v.counter floor w).Runs m ∧
    ∀a,a<countAt ∨ v.returnedEnd floor≤a → (v.counter floor w).image m a=m a :=
  DescentOrdinaryCountScan.run top f countAt N m source room

theorem counter_read {w : ℕ} (m : Memory w) (source : (top).Fits w countAt) (rows : N≤(top).size)
    (room : v.returnedEnd floor<2^w) (actual : Fin N→Cell v.countBits)
    (read : ∀i,m ((top).base+i.val)=((actual i).val:Word w)) :
    (v.counter floor w).image m (DescentOrdinaryCountScan.address v.countBits countAt N)=
      ((∑i : Fin N,f (actual i)):Word w) :=
  DescentOrdinaryCountScan.read top f countAt N m actual source rows read room

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
