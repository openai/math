import OAI.Hierarchy.DescentPrivateMatchedDate
import OAI.Hierarchy.DescentIssuedDonorTotal
import OAI.Hierarchy.DescentChronologicalGrains

namespace OAI
/-! # Register one real matched ordinary date on the same traced and metered path -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentHostDegree
open DescentPacking DescentPacking.PackedMatch DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage
open DescentPackedZip DescentPackedColony DescentTerminalEpochChart DescentPackedProfileWide
open DescentSixParty.StarKeys DescentKernelHistory
open DescentHostDirectory DescentTerminalEpochDecoder DescentPackedProfileArchive
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 800000
attribute [local irreducible] Stage.nativeParts DescentPacking.PackedMatch.topologyWords
  Gather.assembly Owners.LayoutBit.field Gather.ROM.place Prepare.ROM.sortBase Stage.slot
  DescentPacking.pairNumber DescentPacking.slabPacking
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist w : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
local notation "A" => prior.placement
local notation "J" => S.groupCount i
local notation "H" => DescentCompiler.TerminalScale.hostRows (S.hostSize i)
local notation "pad" => prior.valid.host.trans (DescentCompiler.TerminalScale.hostPad _)
local notation "grp" => Equiv.refl (Fin J)
local notation "e" => dense prior.vertex
local notation "vid" => GroupStage.plane e pad
local notation "orig" => prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)
local notation "r" => 2^k
local notation "cm" => 2*(A).cap
local notation "K" => 2^(k+1)
local notation "dim" => (A).degree
local notation "short" => max (k+3) (Nat.clog 2 (dim+1))
local notation "prof" => DescentTerminalEpochBits.width G.C
local notation "s" => shape r dim cm prof
variable {he : 0≤ε} {c : (prior.placement.stage.result he).Choice} {n : Normalize ((prior.placement.stage.result he).state c)}
variable {z' D' : ℕ} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he prior.placement.stage c n target)
variable (h base : ℕ) (C : Chooser.Layout) (grain seats romBase : ℕ)
variable (prev : Ports prior.placement.degree) (wireBank : Fin (2^k)→Fin (2*prior.placement.cap)→Bank) (hubBank : Bank)
local notation "fmt" => ticket.depotShape short
local notation "amount" => ticket.installedDonorWidth short prof
local notation "M" => lanes h amount
local notation "rows" => H*chunks J M
local notation "rootAt" => ticket.donorStart short prof H h base
local notation "span₀" => DepotRAM.Resident.Dynamic.Placement.endAddress H J M dim (DepotRAM.rawBits fmt) 0
local notation "src" => ticket.donorSource short prof H h base span₀
local notation "bump" => Prepare.ROM.sortBase romBase k dim (A).cap (k+3) M H J
local notation "bits₀" => Prepare.bits H J M
local notation "peerBank" => Prepare.rosterBank bump H dim
local notation "nextBase" => Prepare.next k H J M dim (A).cap bump
local notation "wins" => Prepare.gatedBank (k:=k) bump H J M dim bits₀
local notation "marks" => Prepare.markedBank (k:=k) (cap:=(A).cap) bump H J M dim bits₀
local notation "plan" => Gather.ROM.place s short r dim cm K H J M amount nextBase seats
local notation "table" => (Gather.ROM.chart s short r dim cm K H J M (M*(s).pairs) amount nextBase (plan).source).joins
local notation "N" => (K*H)*chunks J M
local notation "top" => (plan).layout.topology
local notation "profiles" => (plan).layout.out
local notation "finish" => LayoutSum.Finish.chart s M top profiles N
local notation "births" => LayoutSum.Finish.births s M top profiles N

local notation "old" => matchedBanks ticket h seats romBase prev wireBank hubBank
local notation "address" => issuedAddressed ticket h base old
local notation "ptr" => DepotRAM.Resident.addressed fmt address H
local notation "postgeom" => DepotRAM.Resident.Dynamic.Placement.layout H J M dim (DepotRAM.rawBits fmt) rootAt peerBank hubBank
local notation "donor" => Gather.ROM.donorExpr s short r dim cm K H J M amount nextBase seats
  (Gather.expr wins marks {prev with roster:=peerBank} H)
local notation "R" => hostRotor vid (DescentGroupPeerOrder.hostRoster A ((vid).trans Fin.valEmbedding))
local notation "whole" => ticket.setupWords short prof H h
local notation "slotCount" => 2^(packExponent 20 (A).stage.Δ)+2

variable {header factor p j z₀ D₀ finishAge finishGrain finishDegree : ℕ}
variable {firstWorld lastWorld : MarkedWorld F d P bits}
variable {first : Reached firstWorld G q ε S k j z₀ D₀ wire hist}
variable {last : Reached lastWorld G q ε S k finishAge finishGrain finishDegree wire hist}
variable (before : Path first prior) (tail : Path target last) {history : Path first last}
variable (cut : (before.ordinary ticket).append tail=history) (dates : history.GrainDates p)
variable (cal : MeterCalendar first header w before) (prep : NativePhase w) (initial : Memory w)
local notation "in₀" => cal.memory initial
local notation "matched" => prep.image in₀
local notation "grainAt" => ticket.grain_on_cut before tail cut dates

theorem matched_calendar_date (headerLow : header<base) (positive : 0<amount) (wide : 2*amount≤h)
    (word : h≤w) (overhead : w≤factor*h) (room : ticket.wholeDonorEnd short prof H h base≤2^w)
    (rs : DescentColonies.DynamicSplit.Roster (Nat.clog 2 (S.hostSize i)) dim) (reserved : ℕ→Prop)
    (actual : LayoutReportAt A orig S prior.valid he grp e pad C grain h amount prof seats romBase prev
      c rs in₀ prep.program prep.ticks reserved matched)
    (headerStored : reserved header) (allPrep : ∀m,prep.Runs m)
    (historyReady : cal.Ready factor initial) (historyTotal : cal.Total factor)
    (diary : DonorDiary first header h w factor p cal)
    (names : (A).SiteNamed rank ∧ ∀x y,orig x<orig y ↔ originalId W.graph.Edge x<originalId W.graph.Edge y)
    (oldEnd : nextBase≤base ∧ (plan).source.base≤base ∧ (finish).out<base ∧ (top).base+N≤base ∧ births+N≤base)
    (ready : ReadRoom ticket h base old w)
    (rawFits : Owners.LayoutBit.Room (address).layout donor H J M (short*DescentPacking.PackedMatch.Local.fields r dim cm) w (postgeom).ownerBase)
    (keysLow : (address).layout.widen.shift.base+(address).layout.widen.shift.size≤rootAt ∧
      (address).layout.widen.apply.base+(address).layout.widen.apply.size≤rootAt)
    (adjacency : (peerBank).base+(peerBank).size≤rootAt)
    (hubRoom : hubBank.base+hubBank.size≤base) (hubCount : H≤hubBank.size)
    (hubRead : ∀j:Fin H,in₀ (hubBank.base+j.val)=((Census.hub A vid j).val:Computability.VPVNP.BurstRAM.Word w))
    (hubFrame : ∀j:Fin H,reserved (hubBank.base+j.val))
    (cables : ∀x j,Reads (wireBank x j) (fun v g=>DescentSignedCableCodec.encode
      (Prepare.signed A orig S prior.valid (grp).toEmbedding vid x j v g)) M in₀)
    (guarded : ∀x j (t : Row H J M),reserved ((wireBank x j).base+(row H J M t).val))
    (fits : ∀x j,(wireBank x j).Fits w base) (capacity : ∀x j,rows≤(wireBank x j).size)
    (sumSize : (s).outputBits*M≤w) :
    let visit:=issuedVisit ticket h base old headerLow.le positive wide word overhead room grainAt
    let code:=prep.seq ((visit.install.seq visit.venue).seq visit.gather)
    let next:=cal.ordinary ticket visit.port code
    Nonempty (DonorDiary first header h w factor p next) ∧ next.Ready factor initial ∧ next.Total factor := by
  intro visit code next
  have record:=actual
  obtain ⟨index,paint,nz,run,_,_,_,_,_,_,_,_,_,_,_,saved⟩:=record
  have retained:=fun (j:Fin H)=>(saved _ (hubFrame j)).trans (hubRead j)
  have physical:=matched_depot_date ticket h base C grain seats romBase prev wireBank hubBank headerLow.le positive wide
    word overhead room grainAt rs in₀ matched prep.program prep.ticks reserved actual names.1 names.2 oldEnd ready.geometry
    rawFits keysLow adjacency hubRoom hubCount retained cables guarded fits capacity ready.terrain ready.peers
    ready.ranks ready.hubs ready.sourceTopology ready.sourceBirths ready.topRows ready.birthWidth sumSize ready.packed
  exact ⟨⟨.ordinary diary visit prep⟩,
    issued_ready_date ticket h base old headerLow.le positive wide word overhead room grainAt cal prep
      historyReady run (saved _ headerStored) headerLow physical,
    issued_total_date ticket h base old headerLow.le positive wide word overhead room grainAt cal prep
      ready historyTotal allPrep⟩

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
