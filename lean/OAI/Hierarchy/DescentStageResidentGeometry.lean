import OAI.Hierarchy.DescentResidentGeometryRead
import OAI.Hierarchy.DescentOrdinaryRootTables
import OAI.Hierarchy.DescentOrdinaryDonorInputs
import OAI.Hierarchy.DescentPackedMatchOrdinary
import OAI.Hierarchy.DescentPublishedHubBits

namespace OAI
/-! # The previous real host/actor record supplies every dynamic ordinary donor field -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentStageEdgeReceipt DescentRawCablePanel DescentPackedZip DescentSIMDLookup DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentHaloWalkRAM DescentIssuedTerminalId DescentHostDirectory
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (group : J≃Fin G) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a)
local notation "gk" => group.toEmbedding.trans Fin.valEmbedding
local notation "vk" => hosts.trans Fin.valEmbedding
local notation "rk" => groupRank gk vk
local notation "peers" => rotor A rk
local notation "D" => A.degree
local notation "r" => 2^k
local notation "p" => 2*A.cap
local notation "named" => cableNames k rk
local notation "real" => spread group.toEmbedding hosts (terrain (short:=short) A native S ready named win peers)
local notation "roster" => hostRotor hosts (DescentGroupPeerOrder.hostRoster A vk)
local notation "P₄" => breadth D
local notation "hub" => fun j : Fin H=>if hv : ∃v,hosts v=j then A.hub hv.choose else false
variable (L : DepotRAM.Resident.Dynamic.Layout) (Q : Owners.LayoutBit.Banks) (wh : Fin (2^k)→Bank) (mk : Fin (2^k)→Fin (2*A.cap)→Bank)
  (ports : Ports A.degree) (join_ : Fin (DescentPacking.PackedMatch.Local.fields (2^k) A.degree (2*A.cap))→Tables) (profile : ℕ)
local notation "fx" => Gather.expr wh mk ports H
local notation "mix" => Gather.assembly join_ fx
local notation "term" => Owners.LayoutBit.field Q mix
local notation "procedure" => DepotRAM.Resident.Dynamic.phase L r D p short A.cap profile H G M w term
local notation "first" => L.ownerBase
local notation "bytes" => Owners.inputBits r D p short
local notation "ownerAt" => Owners.Board.venue bytes M first (H*chunks G M)

theorem resident_dynamic (m : Memory w) (rootBase : ℕ) (lay : Bool)
    (room : DepotRAM.Resident.Dynamic.Room L r D p short H G M w term) (early : DepotRAM.Resident.Dynamic.Prior L)
    (orig : Owners.LayoutBit.Room Q mix H G M (short*DescentPacking.PackedMatch.Local.fields r D p) w first)
    (root : RootTables.Present H G M D rootBase m) (chart : L.walks=RootTables.walks H D rootBase ports.roster)
    (offset : L.ranks.start=RootTables.bank H D rootBase 5) (mask : Q.live=RootTables.liveBank H G M D rootBase)
    (hw : H≤L.hub.size) (saved : ∀h:Fin H,m (L.hub.base+h.val)=((Census.hub A hosts h).val:Computability.VPVNP.BurstRAM.Word w))
    (gate : m Q.gate.base=(if lay then (1:Computability.VPVNP.BurstRAM.Word w) else 0)) (wide : Static Q.widen (Owners.LayoutBit.join (short*DescentPacking.PackedMatch.Local.fields r D p)) M m)
    (packed : Gather.Bounds (w:=w) (d:=short) (M:=M) join_ fx first)
    (literal : ∀j,Static (join_ j) (Gather.setField (d:=short) j) M m)
    (rs : Mounted ports roster m G M)
    (ok : ∀x : Fin r,Accessible ports (wh x) H G M w first)
    (bounds : ∀(x : Fin r) (i : Fin p),(mk x i).Fits w first) (sizes : ∀(x : Fin r) (i : Fin p),H*chunks G M≤(mk x i).size)
    (winner : ∀x : Fin r,Reads (wh x) (fun h g=>(real h g).winner x) M m)
    (marked : ∀(x : Fin r) (i : Fin p),Reads (mk x i) (fun h g=>(real h g).neighbor x i) M m) :
    let dest:=(procedure).image m
    (procedure).Runs m ∧ Source term (fun h g=>Owners.register lay (real h g)) M dest ∧
      Reads (Owners.Board.bank ownerAt (H*chunks G M)) (ownerWord (short:=short) A native S ready rk win group hosts profile lay) M dest ∧
      DescentHaloPackedRebase.Reads (DonorHeaders.shelf H G M D L.literal L.rankOut) (ordinalChart A roster) M G dest ∧
      DescentHaloPackedRebase.Reads (DonorHeaders.shelf H G M D L.literal L.hubOut)
        (hubChart (A:=A) («roster»:=roster) (hosts:=hosts) («hub»:=A.hub)) M G dest ∧
      ∀x,x<first→dest x=m x := by
  intro dest
  have cells:=gathered_fields A native S ready named win peers group.toEmbedding hosts (DescentGroupPeerOrder.hostRoster A vk)
    (DescentGroupPeerOrder.rotor_group A gk vk) wh mk ports first m rs ok bounds sizes winner marked
  have raw:=Gather.assembled join_ fx first packed real m literal cells
  obtain ⟨neighbors,starts,maskRead⟩:=RootTables.row_data H G M D rootBase roster ports.roster m root (fun h j=>by simpa [Nat.add_assoc,DescentPackedColony.target,DescentHaloWalkRAM.number] using rs.roster h j)
  have flags (i : Fin H) : m (L.hub.base+i.val)=((hub i).toNat:Computability.VPVNP.BurstRAM.Word w) := by
    rw [saved]
    by_cases present:∃v,hosts v=i
    · obtain ⟨v,rfl⟩:=present
      have hit:∃u,hosts u=hosts v:=⟨v,rfl⟩
      simp only [dite_eq_left hit,hosts.injective hit.choose_spec,DescentHubBits.live]
    · simp [present,DescentHubBits.absent A hosts i present]
  apply DepotRAM.Resident.Dynamic.resident_dynamic L Q mix lay real roster hub m room orig early hw gate
    (fun j=>by rw [mask];exact maskRead j) wide raw (by rw [chart];exact neighbors)
    (fun h j=>by rw [offset];exact starts h j) flags

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
