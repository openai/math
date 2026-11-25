import OAI.Hierarchy.DescentDatedMaterialReceiver
import OAI.Hierarchy.DescentDatedMaterialFits
import OAI.Hierarchy.DescentDatedPriorHeaderHeld
import OAI.Hierarchy.DescentDatedBeforeSignedMaterial

namespace OAI
/-! Derive every receiving-socket source from the original measured depot and one-hop neighbors. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentSharedCableNames DescentHaloWalkRAM DescentHaloPackedRebase DescentParallelBase.ParentFilter
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DepotRAM.Material.Route
open scoped Classical
open scoped Fin.CommRing
noncomputable section
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
local notation "e" => v.material
local notation "fmt" => v.ticket.depotShape v.short
local notation "H" => v.material.oldHosts
local notation "D" => DepotRAM.Shape.degree (v.ticket.depotShape v.short)
local notation "P₀" => breadth D
local notation "M" => v.material.lanes
local notation "b" => v.material.fieldBits
local notation "G" => v.material.groups
local notation "B" => v.material.blocks
local notation "Q" => v.signed.lowSites
local notation "K" => v.signed.tickets
local notation "L" => v.signed.cap
variable (base : ℕ) (parts adj : Bank) {w : ℕ}
local notation "start" => PriorHeader.endAddress H G M D base
local notation "first" => PriorHeader.phase H G M D base adj w
local notation "raw" => PriorHeader.ports H G M D base
local notation "geo" => PriorHeader.rankBanks H G M D base
local notation "second" => v.materialAt start parts (PriorHeader.reverseRank H G M D base) w
local notation "cpu" => NativePhase.seq first second
variable (pre : PriorHeader.Room adj v.material.oldHosts v.material.groups v.material.lanes (v.ticket.depotShape v.short).degree base w) (paid : v.MaterialRoom (PriorHeader.endAddress v.material.oldHosts v.material.groups v.material.lanes (v.ticket.depotShape v.short).degree base) parts (PriorHeader.reverseRank v.material.oldHosts v.material.groups v.material.lanes (v.ticket.depotShape v.short).degree base) w)
    (previous : parts.base+parts.size≤base) (pos : 0<v.material.oldLanes) (hm : 0<v.material.lanes) (hb : 0<v.material.blocks)
    (bands : v.material.oldGroups=v.material.groups*v.material.blocks) (grows : v.material.oldHosts≤v.material.hosts)
    (m : Memory w) (R : Fin v.material.oldHosts→Fin (v.ticket.depotShape v.short).degree→Option (Fin v.material.oldHosts)) (state : Fin v.material.oldHosts→Fin v.material.oldGroups→DepotRAM.Parts (v.ticket.depotShape v.short))
    (neighbors : ∀h j,m (adj.base+h.val*(v.ticket.depotShape v.short).degree+j.val)=(number (R h j):Word w))
    (board : Reads parts (fun h g=>DepotRAM.combine (v.ticket.depotShape v.short) (state h g)) v.material.oldLanes m)
    (room : Fused.capacity (v.ticket.depotShape v.short).degree v.signed.lowSites v.signed.tickets v.signed.cap≤2^v.material.fieldBits) (pitch : 0<v.materialPitch) (inside : v.materialPitch≤v.signed.lowSites)
    (bound : ∀h g z,DepotRAM.Material.ParentRoom (v.ticket.depotShape v.short) v.materialFormat (state h g)
        (digest (DepotRAM.Material.reverseEntries (v.ticket.depotShape v.short) R h)) z v.signed.lowSites v.signed.tickets v.signed.cap)
include pre paid previous pos hm hb bands grows neighbors board in
theorem real_parent_sources (p : Fin P₀) (z : DepotRAM.Material.Seat fmt) (x : Fin B) (f : Port) :
    Source (v.materialSocket start geo raw p z x f)
      (fun h g=>atPort R (v.incoming R state bands room pitch inside bound p z x h g) f) M ((cpu).image m) :=by
  let run:=(first).image m
  let done:=(second).image run
  let out:=(e).endAddress start
  have head:=PriorHeader.any H G M D base adj pre m
  have continuation:=v.material_any paid run
  have keep (a : ℕ) (lt : a<start) : done a=PriorHeader.image H G M D base adj m a:=by
    rw [←PriorHeader.phase_image H G M D base adj w m];exact continuation.2 a (Or.inl lt)
  have mount:=PriorHeader.held_ports base adj pre m R neighbors done keep
  have directory:=PriorHeader.held_directory base adj pre m R neighbors done keep
  have prior : Reads parts (fun h g=>DepotRAM.combine fmt (state h g)) (e).oldLanes run:=by
    intro p
    rw [show run=PriorHeader.image H G M D base adj m from PriorHeader.phase_image ..]
    refine (head.2 _ (Or.inl ?_)).trans (board p)
    exact (Nat.add_lt_add_left ((row H (e).oldGroups (e).oldLanes p).isLt.trans_le paid.sourceSize) _).trans_le previous
  have ranks : DescentOrdinaryDonorRankDirectory.Reads R geo run:=by
    rw [show run=PriorHeader.image H G M D base adj m from PriorHeader.phase_image ..]
    exact PriorHeader.directory base adj pre m R neighbors
  let j:=DepotRAM.Material.Sheets.id fmt (donorField f) z
  have bank:=v.received_fit start out w le_rfl paid.range hm hb bands grows j
  have stop:start≤out:=by dsimp only [out];rw [MaterialExtent.translated];exact Nat.le_add_right ..
  have available:= (PriorHeader.accessible base adj pre (v.receivedBank start j) out stop bank.1 bank.2).2
  have safe:H*chunks G M<2^w:=bank.2.trans_lt bank.1.2.1
  have read:=v.material_socket_issued start geo raw run R state paid pos hm hb bands ranks.reverse prior p z x f out
    le_rfl paid.range safe available mount.1 directory
  rw [v.actual_socket R state bands room pitch inside bound] at read
  exact read

theorem material_to_issued (floor : ℕ) (degree : v.signed.degree=D) :
    v.beforeSignedMaterial floor parts adj w=
      (PriorHeader.phase H G M D (v.donorEnd floor) adj w).seq
        (v.materialAt (PriorHeader.endAddress H G M D (v.donorEnd floor)) parts
          (PriorHeader.reverseRank H G M D (v.donorEnd floor)) w) :=by
  unfold beforeSignedMaterial
  rw [degree]
  rfl

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
