import OAI.Hierarchy.DescentDatedSampledMaterialValues
import OAI.Hierarchy.DescentDatedOperandMatchedFields
import OAI.Hierarchy.DescentDatedOperandRawFields
import OAI.Hierarchy.DescentDatedOperandNarrowSockets
import OAI.Hierarchy.DescentDatedOperandTransferredRead
import OAI.Hierarchy.DescentDatedReturnedTicketDigits

namespace OAI
/-! # All widened ticket inputs read one actual signed host and its selected earlier donor -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentPackedZip DescentSIMDLookup DescentHaloWalkRAM
open DescentSharedCableNames DescentPackedColony DescentDatedOperandReadPipeline DescentHaloPackedRebase
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I)
local notation "e₀" => v.material
local notation "fmt₀" => v.ticket.depotShape v.short
local notation "l₀" => v.resolver
local notation "g₀" => v.ticketReadGeometry
local notation "H" => (e₀).oldHosts
local notation "K" => (e₀).hosts
local notation "D" => (fmt₀).degree
local notation "P₀" => breadth D
local notation "O" => DepotRAM.Material.roles fmt₀
local notation "G" => (e₀).groups
local notation "M" => (e₀).lanes
local notation "B" => (e₀).blocks
local notation "b" => (e₀).fieldBits
local notation "J" => (l₀).jobs
local notation "d" => v.operandShortBits
local notation "val₀" => Fin K → Fin G → Cell b
variable (R : Fin v.material.oldHosts → Fin (v.ticket.depotShape v.short).degree → Option (Fin v.material.oldHosts))
  (state : Fin v.material.oldHosts → Fin v.material.oldGroups → DepotRAM.Parts (v.ticket.depotShape v.short))
variable (bands : v.material.oldGroups = v.material.groups * v.material.blocks)
  (serial peer : Fin v.material.blocks →
    Fin (breadth (v.ticket.depotShape v.short).degree * DepotRAM.Material.roles (v.ticket.depotShape v.short)) →
    Fin v.material.hosts → Fin v.material.groups → Cell v.material.fieldBits)

variable (floor : ℕ) (c : v.SignedChart) (A : v.ArgumentEntry) (mat : A.Match v floor) (shape : v.VectorShape)
    (blocks : v.resolver.blocks=v.material.blocks) (bound : v.resolver.hosts≤v.material.hosts)
    (groups : v.resolver.groups=v.material.groups)
variable (orig : Fin v.resolver.jobs → Fin 6 → Values v.ticketReadGeometry v.operandShortBits) (prior : Fin v.resolver.jobs → Fin 4 → Values v.ticketReadGeometry (v.resolver.size+2))
    (born : Fin v.resolver.jobs → Fin 3 → Values v.ticketReadGeometry v.bornBook.bits)
local notation "wide₀" => v.wideMaterialValues R state bands serial peer
local notation "narrow₀" => v.narrowValue R
local notation "data₀" => v.sampleHeads blocks bound groups orig prior born wide₀ narrow₀
local notation "start₀" => v.operandHeaderEnd floor
local notation "end₀" => v.preparedUntil floor

variable {w : ℕ} (m : Memory w) (pg : Fin (7*v.vector.operands))
local notation "plain₀" => (v.originAndMouth floor w A mat d ((A.directory v floor mat).refs pg)).image m
local notation "here" => (v.operandEarlyPhase floor w A).image plain₀

set_option maxHeartbeats 600000 in
theorem sourced_ticket
    (positive : 0<M) (space : end₀<2^w) (rosters : v.WalkBanks floor A (Gather.reaching R) start₀ here)
    (matched : ∀j p x,(v.operandDatum floor x p j).Fits w start₀ ∧ Source (v.operandDatum floor x p j)
      (v.matchedFieldValue R state bands j p x) M here)
    (raw : ∀x f i,(v.rawFieldHead floor x f i).Fits w start₀ ∧ Source (v.rawFieldHead floor x f i)
      (v.rawMaterialValue R state bands x f i) M here)
    (retained : ∀x i,((v.parentSerial floor c x i).Fits w start₀ ∧ Source (v.parentSerial floor c x i) (serial x i) M here) ∧
      ((v.parentPeer floor c x i).Fits w start₀ ∧ Source (v.parentPeer floor c x i) (peer x i) M here))
    (narrow : ∀i,(v.narrowHead floor i).Fits w start₀ ∧ Source (v.narrowHead floor i) ((narrow₀) i) M here)
    (actor : ∀j f,Held (g₀) start₀ here (v.originAt floor d shape j f) (orig j f))
    (old : ∀j f,Held (g₀) start₀ here (v.oldHeaderAt floor j f) (prior j f))
    (birth : ∀j f,Held (g₀) start₀ here (v.mouthAt floor A mat shape j f) (born j f)) :
    let data:=SortedInput.values (g₀) (v.originalValues data₀) (v.walkValues (Gather.reaching R))
    ∀j f,Held (g₀) end₀ ((v.nativeTicketPreparation floor w c A mat shape blocks pg).image m)
      (v.nativeTicketExpr floor c A mat shape blocks j f) (fun h k=>((ticketAt (g₀) data j h k f:ℕ):Cell (g₀).resultBits)) :=by
  intro data
  let tail:=v.headTransferPhase floor c w
  have origs:=v.old_and_anchor floor R state bands here matched
  have wide (key : v.WideHead) : (v.wideHead floor c key).Fits w start₀ ∧
      Source (v.wideHead floor c key) ((wide₀) key) M here :=by
    rcases key with ⟨x,f,i⟩|rest
    · exact origs.1 x f i
    rcases rest with ⟨x,f,i⟩|⟨x,f,i⟩
    · exact origs.2 x f i
    · by_cases live : f.val<6
      · simpa only [wideHead,signedRawHead,wideMaterialValues,live,↓reduceDIte] using raw x ⟨f.val,live⟩ i
      by_cases first : f.val=6
      · simpa only [wideHead,signedRawHead,wideMaterialValues,live,↓reduceDIte,first,↓reduceIte,Nat.lt_irrefl] using (retained x i).1
      · simpa only [wideHead,signedRawHead,wideMaterialValues,live,↓reduceDIte,first,↓reduceIte] using (retained x i).2
  have budget : v.headTransferEnd floor<2^w:=by
    have left : v.headTransferEnd floor≤v.operandRootBase floor:=Nat.le_add_right ..
    have right : v.operandRootBase floor≤end₀:=by
      obtain ⟨toCoord,toPath,toEnd⟩:=SortedInput.ceilings (g₀) (v.operandRootBase floor)
      exact toCoord.trans (toPath.trans toEnd)
    exact left.trans_lt (right.trans_lt space)
  have moved:=v.transferred_reads blocks bound groups orig prior born wide₀ narrow₀ floor c A mat shape here
    (fun i=>(wide i).1) (fun i=>(narrow i).1) budget positive (fun i=>(wide i).2) (fun i=>(narrow i).2) actor old birth
  have read:=v.native_source_returns floor c A mat shape blocks data₀ (tail.image here) (Gather.reaching R) (rosters.keep v moved.1) moved.2 space
  intro j f
  have digits : (fun h k=>finalLaw (g₀) f (fun i=>finalInputs (g₀) data j i h k)) =
      (fun h k=>((ticketAt (g₀) data j h k f : ℕ) : Cell (g₀).resultBits)) :=
    funext fun h=>funext fun k=>final_ticket (g₀) data j h k f
  exact (congrArg (Held (g₀) end₀ ((v.nativeTicketPreparation floor w c A mat shape blocks pg).image m)
    (v.nativeTicketExpr floor c A mat shape blocks j f)) digits).mp (read.2 j f)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
