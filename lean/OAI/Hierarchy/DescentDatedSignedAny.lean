import OAI.Hierarchy.DescentDatedSignedInput
import OAI.Hierarchy.DescentDatedMaterialFits
import OAI.Hierarchy.DescentDatedSignedPrefixFits
import OAI.Hierarchy.DescentDatedSignedHeaderFits

namespace OAI
/-! All signed source windows fit from public date addresses, also on malformed memory. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentSIMDLookup DescentPackedColony DescentDyadicSpan
open DescentHaloWalkRAM DescentOrdinaryMarkProject ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P : Type} [Field F] (v:PhysicalOrdinary F P)
local notation "s"=>v.signed
local notation "fmt"=>v.ticket.depotShape v.short
local notation "e"=>v.material
local notation "ms"=>v.markShape
variable (floor w:ℕ) (c:v.SignedChart)
local notation "header"=>v.donorEnd floor
local notation "b₀"=>v.materialStart floor
local notation "start"=>v.markEnd floor
local notation "I"=>v.signedInput floor c
local notation "geo"=>PriorHeader.rankBanks v.area.H v.signed.groups v.signed.lanes v.signed.degree header
local notation "raw"=>PriorHeader.ports v.area.H v.signed.groups v.signed.lanes v.signed.degree header

structure SignedRoom:Prop where
  hosts:(s).priorHosts=v.area.H
  nextHosts:(s).hosts=v.venue.hosts
  lanes:0 < (s).lanes
  blocks:0<(fmt).blocks
  groups:(e).oldGroups=(s).groups*(fmt).blocks
  growth:v.area.H ≤ (s).hosts
  order:b₀≤ start
  material:v.materialEnd floor≤ start
  «header»:PriorHeader.endAddress v.area.H (s).groups (s).lanes (s).degree header<2^w
  combined:start+(s).priorHosts*((s).reach*(s).reach)<2^w
  old:(s).priorHosts<2^w
  current:(s).hosts<2^w
  paths:(s).reach*(s).reach<2^w
  span:(s).priorHosts*v.materialPitch+(s).lowSites<2^w
  neighbor:(DescentOrdinaryPeerRows.peers (v.materialEnd floor) v.area.H v.area.D v.venue.hosts v.venue.degree).Fits w start
  wide:0<w
  room:(s).roof start+max (s).slab (s).oldSlab<2^w

variable (r:v.SignedRoom floor w)
include r in
private theorem begin_room:start<2^w:= ((s).room start).trans_lt ((Nat.le_add_right ..).trans_lt r.room)

include r in
private theorem earlier_bank (i:ℕ) (small:i < (s).reach+20):
    (PriorHeader.bank v.area.H (s).groups (s).lanes (s).degree header i).Fits w start:=by
  have a:=PriorHeader.at_bank v.area.H (s).groups (s).lanes (s).degree header i _ small r.header
  exact ⟨a.1,a.2.1,a.2.2.trans r.order⟩

include r in
private theorem mark_fitted (x:Fin (s).blocks) (j:Fin (s).candidates):((I).mark (x,j)).Fits w start:=by
  let t:=(ms).markStart (v.peerTail floor)
  let mid:=region t (s).reach (ms).slots v.area.H (s).groups (s).blocks (ms).degree (ms).cap (ms).oldLanes (s).lanes
  let old:=DescentResetStemProject.bank (DescentOrdinarySignedMeta.MarkGather.stop t (ms).degree (ms).cap (ms).oldLanes)
    ((s).reach*(ms).slots) v.area.H (s).groups (s).blocks 1 (ms).oldLanes (s).lanes
    (Fin.cast (congrArg (fun y=>(s).reach*y) c.markSlots) j) x
  have rr:=begin_room v floor w r
  have order:mid≤ start:=Nat.le_add_right ..
  have b:old.Fits w mid:=DescentResetStemProject.page_fits _ _ (order.trans_lt rr)
  have addrFit:(addr mid (s).hosts (s).groups (s).lanes).Fits w start:=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt rr,le_rfl⟩
  have kept:old.Fits w start:=⟨b.1,b.2.1,b.2.2.trans order⟩
  exact ⟨⟨addrFit,trivial⟩,trivial,trivial,kept,addrFit,trivial⟩

include r in
theorem signed_peer_inputs:(s).PeerInputs I start w:=by
  have cap:=PriorHeader.limits v.area.H (s).groups (s).lanes (s).degree
  refine ⟨⟨earlier_bank v floor w r ((s).reach+19) (by omega),?_⟩,⟨?_,?_⟩,⟨r.neighbor,?_⟩,r.old,r.current,r.paths,?_,r.wide⟩
  · rw [r.hosts];exact cap.2.2.2.1
  · exact earlier_bank v floor w r ((s).reach+18) (by omega)
  · rw [r.hosts];exact cap.2.2.2.1
  · rw [r.nextHosts];exact Nat.le_pow_clog (by decide) _
  · intro h l;have one:=Nat.mul_le_mul_right v.materialPitch h.isLt.le
    have two:=l.isLt;exact (Nat.add_lt_add_of_le_of_lt one two).trans r.span

private theorem ports_cast_keep {D D' U G M t w:ℕ} (h:D=D') (q:DescentOrdinaryDonorRankDirectory.Banks)
    (ports:Ports (breadth D)) (B:Bank) (a:Accessible (DepotRAM.Material.Route.keepPorts q ports) B U G M w t):
    Accessible (DepotRAM.Material.Route.keepPorts q (cast (congrArg Ports (congrArg breadth h)) ports)) B U G M w t:=by
  cases h
  exact a

include r in
theorem signed_prior_sources:(s).Prior I start w:=by
  have reach_eq : (s).reach = breadth (s).degree := rfl
  have dated_reach : breadth (v.signedProgram floor).signed.degree = (s).reach := rfl
  have fits:=earlier_bank v floor w r
  have rr:=begin_room v floor w r
  have cap:=PriorHeader.limits v.area.H (s).groups (s).lanes (s).degree
  let auxiliary:=PriorHeader.bank v.area.H (s).groups (s).lanes (s).degree header 11
  have auxFit:=fits 11 (by omega)
  have archive (B:Bank) (bf:B.Fits w start) (br:v.area.H*chunks (s).groups (s).lanes≤B.size):
      Accessible raw B v.area.H (s).groups (s).lanes w start ∧
      Accessible (PriorHeader.uniquePorts v.area.H (s).groups (s).lanes (s).degree header) B v.area.H (s).groups (s).lanes w start:=by
    exact PriorHeader.accessible_at (D:=(s).degree) header r.header B start r.order bf br
  have kept (p:Fin (s).reach) (z:DepotRAM.Material.Seat fmt) (x:Fin (s).blocks) (f:Fin 9):
      (v.materialSocket b₀ geo (cast (congrArg Ports (congrArg breadth c.degree)) raw) (c.ray p) z (Fin.cast c.blocks x) f).Fits w start:=by
    let page:=DepotRAM.Material.Sheets.id fmt (DepotRAM.Material.Route.donorField f) z
    have data:=v.received_fit b₀ start w r.material rr r.lanes r.blocks r.groups r.growth page
    have ports:= (archive _ data.1 data.2).2
    apply v.material_socket_fits b₀ start w r.material rr (congrArg breadth c.degree) geo _ _ _ _ _
    exact ports_cast_keep c.degree geo raw _ ports
  have original:=v.origin_socket_fits b₀ start w r.material rr r.lanes r.blocks r.groups r.growth
  have rankings:DescentOrdinaryDonorRankDirectory.Fits geo start (s).priorHosts (s).reach w:=by
    rw [r.hosts]
    exact ⟨⟨fits _ (by omega),fits _ (by omega),fits _ (by omega),fits _ (by omega),
      cap.2.2.1,cap.2.2.2.1,cap.2.2.2.1,cap.2.1,by simpa only [←r.hosts] using r.old,by simpa only [←r.hosts] using r.combined⟩,
      fits _ (by omega),fits _ (by omega),fits _ (by omega),cap.2.2.1,cap.2.2.1,cap.2.2.2.1⟩
  refine ⟨rankings,fun z=>kept ..,fun z side=>kept ..,fun z f=>kept ..,fun z=>mark_fitted v floor w c r z.1 z.2,
    fun x o=>original ..,fun x o=>original ..,fits _ (by omega),?_,?_⟩
  · rw [r.hosts];exact cap.2.2.1
  · rw [r.hosts];exact ⟨auxiliary,(archive _ auxFit cap.2.2.2.2).1⟩

include r in
theorem signed_any (m:Memory w):
    (v.signedPhase floor c w).Runs m ∧
    (∀a,a<start ∨ (s).roof start≤a→(v.signedPhase floor c w).image m a=m a):=by
  have ok:=signed_prior_sources v floor w c r
  have peerInputs:=signed_peer_inputs v floor w c r
  have all_:=(s).fits_from_prior I start ok r.room ((s).peer_head_fits I start r.room peerInputs)
    ((s).signed_header_fits I start ok r.room) ((s).flags_fits I start ok r.room)
  have high:(s).phaseEnd start<2^w:=by rw [(s).calibrated start];exact (Nat.le_add_right ..).trans_lt r.room
  have result:=(s).phase_any I start w m all_ high
  exact ⟨result.1,fun i h=>result.2.1 i (by simpa only [(s).calibrated] using h)⟩
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
