import OAI.Hierarchy.DescentRegisteredOrdinaryStep
import OAI.Hierarchy.DescentDatedSignedAny
import OAI.Hierarchy.DescentDatePortHeaderRoom
import OAI.Hierarchy.DescentOrdinaryMarkIssuedRoom

namespace OAI
/-! # Fits and final read ranges for the original host count, neighbor and hub registers -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
namespace DatePorts
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (op : RotorSpec) (gain tail p f drift degree payload seats root : ℕ)
    (ordinary : ℕ→Dated.Ordinary)
local notation "books" => OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats prior
local notation "base" => (books).onTicket ticket gain tail p f payload seats prior.venue.lanes prior.io.roster ordinary
local notation "floor" => (base).stageStart root

local notation "v" => ordinaryModel prior ticket op gain tail p f drift degree payload seats root ordinary


local notation "B" => (⟨prior.archive.count,prior.io.roster,prior.io.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "address₀" => (v).materialEnd floor
local notation "H" => (v).area.H
local notation "D₀" => (v).area.D
local notation "V" => (v).venue.hosts
local notation "E" => (v).venue.degree
local notation "peers" => DescentOrdinaryPeerRows.peers address₀ H D₀ V E
local notation "hubs" => DescentOrdinaryVenueReturn.hubs address₀ H D₀ V E
local notation "newCount" => DescentOrdinaryPeerCount.newCount address₀ H D₀ V E
local notation "roof" => (v).peerTail floor

theorem ordinary_peer_room {w:ℕ} (source:prior.HeaderRoom w root) (wire:(v).SignedRoom floor w) :
    DescentOrdinaryVenueReturn.Room B address₀ H D₀ V E w:=by
  have start:root≤floor:=by
    change root≤(base).profileRepack.endAddress root
    rw [(base).profileRepack.translate];exact Nat.le_add_right ..
  have donor:floor≤(v).donorEnd floor:=by rw [(v).donor_shift];exact Nat.le_add_right ..
  have header:(v).donorEnd floor≤(v).materialStart floor:=PriorHeader.lower ..
  have middle:(v).materialStart floor≤address₀:=by
    change _≤(v).material.endAddress _
    rw [(v).material.translated];exact Nat.le_add_right ..
  have old:=source.mono (start.trans (donor.trans (header.trans middle)))
  have marked:roof≤(v).markEnd floor:=(v).markShape.low _
  exact ⟨old.count,old.roster,old.hubs,marked.trans_lt ((Nat.le_add_right ..).trans_lt wire.combined)⟩

theorem ordinary_peer_ranges {w:ℕ} (safe:DescentOrdinaryVenueReturn.Room B address₀ H D₀ V E w) :
    (peers).base+V*E≤roof ∧ (hubs).base+V≤roof ∧ (newCount).base<roof:=by
  have early:DescentOrdinaryPeerCount.roof address₀ H D₀ V E≤roof:=by
    change _≤DescentOrdinaryPeerCount.roof address₀ H D₀ V E+2*DescentDyadicSpan.span V+DescentDyadicSpan.span V
    omega
  have charged:=DescentOrdinaryPeerCount.output_fit address₀ H D₀ V E (early.trans_lt safe.safe)
  refine ⟨(Nat.add_le_add_left charged.2.1 _).trans (charged.1.2.2.trans early),?_,?_⟩
  · exact Nat.add_le_add_left (DescentDyadicSpan.span_ge _) _
  · have size:=charged.2.2.1
    have bound:=charged.2.2.2.2
    omega

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
