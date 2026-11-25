import OAI.Hierarchy.DescentPrintedOrdinaryResult
import OAI.Hierarchy.DescentDatedOperandNativePreparation
import OAI.Hierarchy.DescentOrdinaryBooksAtDate

namespace OAI
/-! # The ordinary successor with the physical sources of all eight routed fields -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (root : ℕ) (prior : DatePorts)
variable (A : ArgumentEntry v) (c : v.SignedChart) (w : ℕ)
local notation "floor" => v.stageStart root
variable (matched : A.Match v (v.stageStart root)) (sh : v.VectorShape) (blocks : v.resolver.blocks=v.material.blocks)
variable (paths : A.clip.venue.paths=StageVenueTail.OrdinaryRaster.paths v.area) (args : 0<v.vector.operands)
local notation "pg" => (⟨0,Nat.mul_pos (by decide : 0<7) args⟩ : Fin (7*v.vector.operands))
local notation "fields" => v.nativeTicketExpr floor c A matched sh blocks
local notation "prepare" => v.nativeTicketPreparation floor w c A matched sh blocks pg
local notation "returned" => v.reachedSources floor
local notation "fund" => v.fundedFromEntry floor A paths

/-- The same deterministic program is used for every byte assignment, including
the scan which obtains each route and orientation from the retained edge rows. -/
def issuedResult : OrdinaryResultCode w :=
  v.resultCode root prior.io prior.archive.count A c matched paths fields prepare returned

def issuedSteps (chip : (A.chipBank v floor).Fits w (v.refsStart floor))
    (fit : v.endAddress floor<2^w) (packed : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (radix : v.vector.radix=2^v.reference.k) (ok : v.FundedRoom floor fund prior.io w) :=
  v.ordinaryResultSteps floor prior.io A matched paths fields prepare chip sh fit packed radix ok

theorem issued_printed (chip : (A.chipBank v floor).Fits w (v.refsStart floor))
    (fit : v.endAddress floor<2^w) (packed : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (radix : v.vector.radix=2^v.reference.k) (ok : v.FundedRoom floor fund prior.io w) :
    v.printedResult root prior.io prior.archive.count (v.signedInput floor c) returned
        (v.issuedSteps root prior A c w matched sh blocks paths args chip fit packed radix ok) =
      v.issuedResult root prior A c w matched sh blocks paths args :=
  v.result_printed root prior.io prior.archive.count A c matched paths fields prepare returned
    chip sh fit packed radix ok

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
