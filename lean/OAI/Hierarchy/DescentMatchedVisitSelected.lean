import OAI.Hierarchy.DescentSelectedMatchedBanks
import OAI.Hierarchy.DescentMatchedDonorCalendar
import OAI.Hierarchy.DescentIssuedDonorReadRoom

namespace OAI
/-! # Chronological ordinary counter sourced entirely through the actual physical matcher -/
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
  Gather.assembly Owners.LayoutBit.field Prepare.ROM.sortBase Stage.slot
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
variable (input : Dated.Operands)
local notation "prev" => input.ports dim
local notation "wireBank" => fun (x : Fin r) (j : Fin cm)=>input.wire x.val j.val
local notation "hubBank" => input.hubs
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

local notation "old" => matchedBanks ticket h seats romBase prev (wireBank) hubBank
local notation "address" => issuedAddressed ticket h base old
local notation "ptr" => DepotRAM.Resident.addressed fmt address H
local notation "postgeom" => DepotRAM.Resident.Dynamic.Placement.layout H J M dim (DepotRAM.rawBits fmt) rootAt peerBank hubBank
local notation "donor" => Gather.ROM.donorExpr s short r dim cm K H J M amount nextBase seats
  (Gather.expr wins marks {prev with roster:=peerBank} H)
local notation "R" => hostRotor vid (DescentGroupPeerOrder.hostRoster A ((vid).trans Fin.valEmbedding))
local notation "whole" => ticket.setupWords short prof H h
local notation "slotCount" => 2^(packExponent 20 (A).stage.Δ)+2

variable {header factor p : ℕ} (prep : NativePhase w) (m : Memory w)
local notation "matched" => prep.image m

/-- The paid topology, six births and the retaining donor shelf all use the
same winning pair on the public donor program's actual image. -/
theorem matched_visit_selected (headerLow : header≤base) (positive : 0<amount) (wide : 2*amount≤h)
    (word : h≤w) (overhead : w≤factor*h) (room : ticket.wholeDonorEnd short prof H h base≤2^w)
    (grainAt : (A).stage.z=S.grainAt G.b p i)
    (rs : DescentColonies.DynamicSplit.Roster (Nat.clog 2 (S.hostSize i)) dim) (reserved : ℕ→Prop)
    (actual : LayoutReportAt A orig S prior.valid he grp e pad C grain h amount prof seats romBase prev
      c rs m prep.program prep.ticks reserved matched)
    (names : (A).SiteNamed rank ∧ ∀x y,orig x<orig y ↔ originalId W.graph.Edge x<originalId W.graph.Edge y)
    (earlier : LayoutSum.Finish.stop s M top profiles N≤base)
    (hubRoom : (hubBank).base+(hubBank).size≤base) (hubCount : H≤(hubBank).size)
    (hubRead : ∀j:Fin H,m ((hubBank).base+j.val)=((Census.hub A vid j).val:Computability.VPVNP.BurstRAM.Word w))
    (hubFrame : ∀j:Fin H,reserved ((hubBank).base+j.val))
    (cables : ∀x j,Reads ((wireBank) x j) (fun v g=>DescentSignedCableCodec.encode
      (Prepare.signed A orig S prior.valid (grp).toEmbedding vid x j v g)) M m)
    (guarded : ∀x j (t : Row H J M),reserved (((wireBank) x j).base+(row H J M t).val))
    (fits : ∀x j,((wireBank) x j).Fits w base) (capacity : ∀x j,rows≤((wireBank) x j).size) :
    let visit:=issuedVisit ticket h base old headerLow positive wide word overhead room grainAt
    let phase:=ticket.donorDate.matchedPhase h seats input romBase base w
    (phase.Runs matched ∧ (∀x,x<base→phase.image matched x=matched x) ∧ MeterPort.Pins ticket visit.port (phase.image matched)) ∧
      ∃i₀ : Fin (2^k-1),∃j₀ : DescentAffineColors.Candidate k,∃hm : 0<M,
        let win:=fun hv : Fin J×prior.V=>(A).publishedTicket grp e rs i₀ j₀ (vid hv.2) hv.1
        let freq:=BitDescription.scannedRows he (A).stage
        let lay:=bestLayout (branchWidth G (fun _ : freq.pairs=>(A).stage.z) (freq.profile c))
        let active:=((visit.install.seq visit.venue).image matched)
        DescentColonies.seedAt k i₀=freq.μ ∧ j₀=DescentAffineColors.code freq.α freq.β ∧
        (∀u,(win ((A).pos u) ((A).block u)).val=1+2*heap (nativeAddress he (A).stage (scanHomeAt he (A).stage u)).2+
          (scanColorAt he (A).stage u).toNat) ∧
        (∀rowIx : Fin N,
          active ((top).base+rowIx.val)=((topologyWords («M»:=M) s (Gather.flat (Gather.descriptorInputs («K»:=K) s (A).cap
            (spread (grp).toEmbedding vid (terrain («short»:=short) A orig S prior.valid (cableNames k rank) win (rotor A rank))))) rowIx).val:Computability.VPVNP.BurstRAM.Word w)) ∧
        (∀col : ScanColonies he (A).stage,∀edge : Matched (nativeTraffic W.graph W.core (scanHomeAt he (A).stage)) (A).cap
            (thinList (scanHomeAt he (A).stage) (scanColorAt he (A).stage) col)
            (thickList (scanHomeAt he (A).stage) (scanColorAt he (A).stage) col),
          ∃n₀ : Fin (s).pairs,n₀.val=(pairNumber (DescentPacking.amount (live (nativeTraffic W.graph W.core (scanHomeAt he (A).stage))))
            (slabPacking (nativeTraffic W.graph W.core (scanHomeAt he (A).stage)) (A).cap
              (thinList (scanHomeAt he (A).stage) (scanColorAt he (A).stage) col)
              (thickList (scanHomeAt he (A).stage) (scanColorAt he (A).stage) col)).decisions edge).val ∧
            ∀role : Fin 6,let rowId:=slot he A (grp).toEmbedding vid hm col
              let ix:=SixBirths.slot rowId.2 n₀ role
              SixBirths.atom (A).stage.z (digit ((s).digit+1) ix.val (active (births+rowId.1.val)).val) ix.val=
                some ((A).stage.z,DescentTerminalEpochFlags.encode (freq.profile c ⟨col,edge⟩),role.val)) ∧
        Reads src (fun v g=>DepotRAM.combine fmt (Stage.nativeParts («short»:=short) A orig S prior.valid rank win grp vid hm prof
          births active R (A).hub lay (donorNameBits (A).stage.k (A).stage.Δ) v g)) M (phase.image matched) := by
  have capTop : N≤(top).size := Gather.ROM.column_size _ _
  have capBorn : N≤2^(Nat.clog 2 N) := Nat.le_pow_clog (by decide) _
  have stopRead : (finish).out+1≤base:=earlier
  have left : nextBase≤(plan).source.base:=by
    change nextBase≤(nextBase+_+_+_)+_
    simp only [Nat.add_assoc]
    exact Nat.le_add_right _ _
  have right : (plan).source.base≤(top).base:=Nat.le_add_right ..
  have roomLast : births+2^(Nat.clog 2 N)≤(finish).out:=by
    exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have first : (top).base+(top).size≤births:=(le_max_left ..).trans (Nat.le_add_right ..)
  have endCap : nextBase≤base ∧ (plan).source.base≤base ∧ (finish).out<base ∧ (top).base+N≤base ∧ births+N≤base := by omega
  have report:=actual
  obtain ⟨μ,j,nz,exec,pick,u₁,u₂,p₁,p₂,wins₀,rails,fromRAM,extra⟩:=report
  let p₀ := rails.access (0:Fin r)
  have mono (bank : Bank) (small : bank.Fits w nextBase) : bank.Fits w base :=
    ⟨small.1,small.2.1,small.2.2.trans endCap.1⟩
  have route : Accessible {prev with roster:=peerBank} (wins (0:Fin r)) H J M w base :=
    ⟨fun j=>mono _ (p₀.ids j),p₀.idsRoom,mono _ p₀.roster,p₀.rosterRoom,mono _ p₀.offsets,p₀.offRoom,
      mono _ p₀.chunks,p₀.chunkRoom,mono _ p₀.source,p₀.srcRoom⟩
  have cpu:0<w:=by omega
  have hostWord:=route.offRoom.trans_lt route.offsets.2.1
  have degreeWord:dim<2^w:=by
    have hd : dim≤H*dim:=by
      have pos : 0<H:=Nat.two_pow_pos _
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right dim pos
    exact (hd.trans route.rosterRoom).trans_lt route.roster.2.1
  have topEnd : (top).base+(top).size≤base :=
    first.trans ((Nat.le_add_right _ _).trans endCap.2.2.2.2)
  have bornEnd : births+2^(Nat.clog 2 N)≤base :=
    roomLast.trans (Nat.le_of_succ_le stopRead)
  have columnFit : (donor).Fits w base :=
    ProtocolRAMGeneratedWrite.fits_mono _ endCap.2.1 fromRAM.fits
  have signedFit (j : Fin (r*cm)) : ((address).cable j).Fits w base := by
    let ij := (finProdFinEquiv (m:=r) (n:=cm)).symm j
    exact fits ij.1 ij.2
  have fullRoom := ticket.issued_read_room h base old cpu word room
    columnFit stopRead signedFit (wins (0:Fin r)) route hubRoom hostWord degreeWord
    topEnd bornEnd capTop capBorn
  obtain ⟨healthy,raw,kb⟩ := fullRoom
  have below : base≤rootAt:=by change base≤base+_;omega
  have mainSize : (s).outputBits≤amount:=by
    have bank:= (ticket.installed_donor_widths short prof).2.1
    unfold DepotRAM.Fresh.laneWidth at bank
    omega
  have width : (s).outputBits*M≤w:=(Nat.mul_le_mul_right M mainSize).trans
    ((by simpa only [Nat.mul_comm M amount] using lanes_fit h amount :amount*M≤h/2).trans
      ((Nat.div_le_self h 2).trans word))

  dsimp only
  let visit:=ticket.issuedVisit h base old headerLow positive wide word overhead room grainAt
  have same : (visit.install.seq visit.venue).seq visit.gather=
      ticket.donorDate.matchedPhase h seats input romBase base w:=
    ticket.matched_phase_eq h seats romBase base input headerLow positive wide word overhead room grainAt
  simp only [←same]
  have keepReport := actual
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,held⟩:=keepReport
  exact ticket.matched_depot_date_sources h base C grain seats romBase prev (wireBank) hubBank
    headerLow positive wide word overhead room grainAt rs m matched prep.program prep.ticks reserved actual
    names.1 names.2 endCap healthy.geometry raw kb (route.roster.2.2.trans below)
    hubRoom hubCount (fun j=>(held _ (hubFrame j)).trans (hubRead j)) cables guarded fits capacity
    healthy.terrain healthy.peers healthy.ranks healthy.hubs healthy.sourceTopology healthy.sourceBirths
    healthy.topRows healthy.birthWidth width healthy.packed
end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
