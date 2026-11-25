import OAI.Hierarchy.DescentIssuedDonorVisit
import OAI.Hierarchy.DescentPrivateInstalledDate
import OAI.Hierarchy.DescentMatchedResidentGeometry
import OAI.Hierarchy.DescentPrivateRetainedCable

namespace OAI
/-! # Read the dated private donor panel from the actual packed matcher report -/
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

def matchedBanks : PriorBanks r dim (A).cap K where
  gate:=⟨(finish).out,0⟩
  hub:=hubBank
  peers:={prev with roster:=peerBank}
  winners:=wins
  marked:=marks
  signed:=wireBank
  operands:=table
  topology:=top
  born:=⟨births,Nat.clog 2 N⟩

local notation "old" => matchedBanks ticket h seats romBase prev wireBank hubBank
local notation "address" => issuedAddressed ticket h base old
local notation "ptr" => DepotRAM.Resident.addressed fmt address H
local notation "postgeom" => DepotRAM.Resident.Dynamic.Placement.layout H J M dim (DepotRAM.rawBits fmt) rootAt peerBank hubBank
local notation "donor" => Gather.ROM.donorExpr s short r dim cm K H J M amount nextBase seats
  (Gather.expr wins marks {prev with roster:=peerBank} H)
local notation "R" => hostRotor vid (DescentGroupPeerOrder.hostRoster A ((vid).trans Fin.valEmbedding))
local notation "whole" => ticket.setupWords short prof H h
local notation "slotCount" => 2^(packExponent 20 (A).stage.Δ)+2

theorem matched_depot_date_sources {header factor p : ℕ} (headerLow : header≤base) (positive : 0<amount)
    (wide : 2*amount≤h) (word : h≤w) (overhead : w≤factor*h)
    (room : ticket.wholeDonorEnd short prof H h base≤2^w) (grainAt : (A).stage.z=S.grainAt G.b p i)
    (rs : DescentColonies.DynamicSplit.Roster (Nat.clog 2 (S.hostSize i)) dim)
    (m matched : Memory w) (code : Procedure w) (time : ℕ) (protectedAt : ℕ→Prop)
    (actual : LayoutReportAt A orig S prior.valid he grp e pad C grain h amount prof seats romBase prev c rs m code time protectedAt matched)
    (named : (A).SiteNamed rank) (order : ∀x y,orig x<orig y ↔ originalId W.graph.Edge x<originalId W.graph.Edge y)
    (oldEnd : nextBase≤base ∧ (plan).source.base≤base ∧ (finish).out<base ∧ (top).base+N≤base ∧ births+N≤base)
    (dynamic : DepotRAM.Resident.Dynamic.Room postgeom r dim cm short H J M w (ptr).terrain)
    (rawFits : Owners.LayoutBit.Room (address).layout donor H J M (short*DescentPacking.PackedMatch.Local.fields r dim cm) w (postgeom).ownerBase)
    (keysLow : (address).layout.widen.shift.base+(address).layout.widen.shift.size≤rootAt ∧
      (address).layout.widen.apply.base+(address).layout.widen.apply.size≤rootAt)
    (adjacency : (peerBank).base+(peerBank).size≤rootAt)
    (hubRoom : hubBank.base+hubBank.size≤base) (hubCount : H≤hubBank.size)
    (oldHub : ∀j:Fin H,matched (hubBank.base+j.val)=((Census.hub A vid j).val:Computability.VPVNP.BurstRAM.Word w))
    (cables : ∀x j,Reads (wireBank x j) (fun v g=>DescentSignedCableCodec.encode
      (Prepare.signed A orig S prior.valid (grp).toEmbedding vid x j v g)) M m)
    (guarded : ∀x j (t : Row H J M),protectedAt ((wireBank x j).base+(row H J M t).val))
    (fits : ∀x j,(wireBank x j).Fits w base) (capacity : ∀x j,rows≤(wireBank x j).size)
    (terrainFit : (ptr).terrain.Fits w (src).base)
    (portsFit : Accessible (ptr).peers (ptr).owner H J M w (src).base)
    (ordFit : DescentHaloPackedRebase.Fits (ptr).ranks H J M w (src).base)
    (flagFit : DescentHaloPackedRebase.Fits (ptr).hubs H J M w (src).base)
    (topFit : (top).Fits w (src).base) (birthFit : (old).born.Fits w (src).base)
    (topRows : N≤(top).size) (bornWidth : SixBirths.width s M≤w) (sumSize : (s).outputBits*M≤w)
    (packed : M*max (DepotRAM.totalBits fmt) (DepotRAM.outputBits fmt)≤w/2) :
    let visit:=issuedVisit ticket h base old headerLow positive wide word overhead room grainAt
    let phase:=(visit.install.seq visit.venue).seq visit.gather
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
  intro visit phase
  let boot:=visit.install
  let geometry:=visit.venue
  let warm:=boot.image matched
  have front : rootAt=base+2*(whole+1) := rfl
  have leaves:=DonorSpace.leaves base whole span₀ rows h
  have last : visit.base+1+rows<2^w := leaves.2.2.2.trans_le room
  have space : base+whole<2^w := by
    have h₁ : rootAt≤ (src).base:=leaves.2.1
    have h₂ : (src).base+(src).size≤visit.base+1:=leaves.2.2.1
    omega
  have large:=(ticket.installed_donor_widths short prof).2.2
  have put:=DepotRAM.Setup.mount fmt s K H J M amount base (A).cap prof G.C G.k (A).z G.b slotCount
    src top (old).born matched large space
  have before (x : ℕ) (hx : x<base) : warm x=matched x := put.2.2.2.2 x (.inl hx)
  have below : base≤rootAt:=by omega
  have hub (j:Fin H) : warm (hubBank.base+j.val)=((Census.hub A vid j).val:Computability.VPVNP.BurstRAM.Word w) :=
    (before _ ((Nat.add_lt_add_left (j.isLt.trans_le hubCount) _).trans_le hubRoom)).trans (oldHub j)
  have resident := LayoutReportAt.resident A orig S prior.valid he grp e pad C grain h amount prof seats romBase prev
    rootAt base hubBank (address).layout c rs m matched warm code time protectedAt actual before below oldEnd
  have readyTerrain : (ptr).terrain = Owners.LayoutBit.field (address).layout donor := rfl
  have terrainRoom := readyTerrain ▸ dynamic
  have laid := resident terrainRoom rawFits
  have sameGate : (address).layout.gate.base = (finish).out := rfl
  have sameLive : (address).layout.live = RootTables.liveBank H J M dim rootAt := rfl
  have stepReport := laid sameGate sameLive put.2.2.1.2.2.2 keysLow adjacency (hubRoom.trans below) hub hubCount
  obtain ⟨step,stable,i₀,j₀,hm,mu,paint,winner,terrain₀,owner,rank₀,hubs,mates,topology,birth⟩ := stepReport
  let win:=fun hv : Fin J×prior.V=>(A).publishedTicket grp e rs i₀ j₀ (vid hv.2) hv.1
  have ownerMap (z : Fin J×prior.V) (j:Fin dim) : R (vid z.2) j=(rotor A rank z j).map (fun y=>vid y.2) := by
    rcases z with ⟨g,v⟩
    have mem : ∃u,vid u=vid v:=⟨v,rfl⟩
    have vRank : (vid).trans Fin.valEmbedding = prior.vertex.trans Fin.valEmbedding := by
      ext x
      rfl
    rw [hostRotor, dite_eq_left mem, (vid).injective mem.choose_spec, vRank,
      DescentGroupPeerOrder.rotor_group A Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding) g v j]
    cases DescentGroupPeerOrder.hostRoster A (prior.vertex.trans Fin.valEmbedding) v j <;> rfl
  have oldCables : ∀x j,Reads (wireBank x j) (fun v g=>DescentSignedCableCodec.encode
      (Prepare.signed A orig S prior.valid (grp).toEmbedding vid x j v g)) M matched := by
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,keep⟩:=actual
    exact fun x j t=>(keep _ (guarded x j t)).trans (cables x j t)
  have signed:=Stage.signed_retained A orig S prior.valid grp vid wireBank base matched (geometry.image warm)
    oldCables fits capacity (fun x hx=>(stable x (hx.trans_le below)).trans (before x hx))
  have readFit (j) : ((ptr).signed j).Fits w (src).base := by
    let ix:=(finProdFinEquiv (m:=r) (n:=cm)).symm j
    have h₁:=fits ix.1 ix.2
    exact ⟨⟨h₁.1,h₁.2.1,h₁.2.2.trans (below.trans leaves.2.1)⟩,trivial⟩
  have df : dim<2^short := (Nat.lt_succ_self dim).trans_le ((Nat.le_pow_clog (by decide : 1<2) _).trans
    (Nat.pow_le_pow_right (by decide : 0<2) (le_max_right ..)))
  have setupBefore : base+whole ≤ rootAt := by
    rw [front]
    omega
  have printed:=installed_depot_date_board ticket visit.port win hm named
    (fun u=>(win ((A).pos u) ((A).block u)).isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) (le_max_left ..)))
    winner df order prof amount base src top (old).born matched geometry R ownerMap ptr
    large leaves.2.1 leaves.1 leaves.2.2.1 last packed readFit terrainFit portsFit ordFit flagFit topFit birthFit
    topRows (Nat.le_pow_clog (by decide) N) bornWidth sumSize step (fun x hx=>stable x (hx.trans_le setupBefore)) topology birth
    terrain₀ signed mates owner rank₀ hubs
  exact ⟨printed.1,i₀,j₀,hm,mu,paint,winner,topology,birth,printed.2⟩

theorem matched_depot_date_board {header factor p : ℕ} (headerLow : header≤base) (positive : 0<amount)
    (wide : 2*amount≤h) (word : h≤w) (overhead : w≤factor*h)
    (room : ticket.wholeDonorEnd short prof H h base≤2^w) (grainAt : (A).stage.z=S.grainAt G.b p i)
    (rs : DescentColonies.DynamicSplit.Roster (Nat.clog 2 (S.hostSize i)) dim)
    (m matched : Memory w) (code : Procedure w) (time : ℕ) (protectedAt : ℕ→Prop)
    (actual : LayoutReportAt A orig S prior.valid he grp e pad C grain h amount prof seats romBase prev c rs m code time protectedAt matched)
    (named : (A).SiteNamed rank) (order : ∀x y,orig x<orig y ↔ originalId W.graph.Edge x<originalId W.graph.Edge y)
    (oldEnd : nextBase≤base ∧ (plan).source.base≤base ∧ (finish).out<base ∧ (top).base+N≤base ∧ births+N≤base)
    (dynamic : DepotRAM.Resident.Dynamic.Room postgeom r dim cm short H J M w (ptr).terrain)
    (rawFits : Owners.LayoutBit.Room (address).layout donor H J M (short*DescentPacking.PackedMatch.Local.fields r dim cm) w (postgeom).ownerBase)
    (keysLow : (address).layout.widen.shift.base+(address).layout.widen.shift.size≤rootAt ∧
      (address).layout.widen.apply.base+(address).layout.widen.apply.size≤rootAt)
    (adjacency : (peerBank).base+(peerBank).size≤rootAt)
    (hubRoom : hubBank.base+hubBank.size≤base) (hubCount : H≤hubBank.size)
    (oldHub : ∀j:Fin H,matched (hubBank.base+j.val)=((Census.hub A vid j).val:Computability.VPVNP.BurstRAM.Word w))
    (cables : ∀x j,Reads (wireBank x j) (fun v g=>DescentSignedCableCodec.encode
      (Prepare.signed A orig S prior.valid (grp).toEmbedding vid x j v g)) M m)
    (guarded : ∀x j (t : Row H J M),protectedAt ((wireBank x j).base+(row H J M t).val))
    (fits : ∀x j,(wireBank x j).Fits w base) (capacity : ∀x j,rows≤(wireBank x j).size)
    (terrainFit : (ptr).terrain.Fits w (src).base)
    (portsFit : Accessible (ptr).peers (ptr).owner H J M w (src).base)
    (ordFit : DescentHaloPackedRebase.Fits (ptr).ranks H J M w (src).base)
    (flagFit : DescentHaloPackedRebase.Fits (ptr).hubs H J M w (src).base)
    (topFit : (top).Fits w (src).base) (birthFit : (old).born.Fits w (src).base)
    (topRows : N≤(top).size) (bornWidth : SixBirths.width s M≤w) (sumSize : (s).outputBits*M≤w)
    (packed : M*max (DepotRAM.totalBits fmt) (DepotRAM.outputBits fmt)≤w/2) :
    let visit:=issuedVisit ticket h base old headerLow positive wide word overhead room grainAt
    let phase:=(visit.install.seq visit.venue).seq visit.gather
    (phase.Runs matched ∧ (∀x,x<base→phase.image matched x=matched x) ∧ MeterPort.Pins ticket visit.port (phase.image matched)) ∧
      ∃i₀ : Fin (2^k-1),∃j₀ : DescentAffineColors.Candidate k,∃hm : 0<M,
        let win:=fun hv : Fin J×prior.V=>(A).publishedTicket grp e rs i₀ j₀ (vid hv.2) hv.1
        let freq:=BitDescription.scannedRows he (A).stage
        let lay:=bestLayout (branchWidth G (fun _ : freq.pairs=>(A).stage.z) (freq.profile c))
        let active:=((visit.install.seq visit.venue).image matched)
        DescentColonies.seedAt k i₀=freq.μ ∧ j₀=DescentAffineColors.code freq.α freq.β ∧
        (∀u,(win ((A).pos u) ((A).block u)).val=1+2*heap (nativeAddress he (A).stage (scanHomeAt he (A).stage u)).2+
          (scanColorAt he (A).stage u).toNat) ∧
        Reads src (fun v g=>DepotRAM.combine fmt (Stage.nativeParts («short»:=short) A orig S prior.valid rank win grp vid hm prof
          births active R (A).hub lay (donorNameBits (A).stage.k (A).stage.Δ) v g)) M (phase.image matched) := by
  obtain ⟨run,i₀,j₀,hm,mu,paint,winner,_,_,board⟩:=matched_depot_date_sources ticket h base C grain seats romBase prev wireBank hubBank headerLow positive wide word overhead
    room grainAt rs m matched code time protectedAt actual named order oldEnd dynamic rawFits keysLow
    adjacency hubRoom hubCount oldHub cables guarded fits capacity terrainFit portsFit ordFit flagFit
    topFit birthFit topRows bornWidth sumSize packed
  exact ⟨run,i₀,j₀,hm,mu,paint,winner,board⟩

theorem matched_depot_date {header factor p : ℕ} (headerLow : header≤base) (positive : 0<amount)
    (wide : 2*amount≤h) (word : h≤w) (overhead : w≤factor*h)
    (room : ticket.wholeDonorEnd short prof H h base≤2^w) (grainAt : (A).stage.z=S.grainAt G.b p i)
    (rs : DescentColonies.DynamicSplit.Roster (Nat.clog 2 (S.hostSize i)) dim)
    (m matched : Memory w) (code : Procedure w) (time : ℕ) (protectedAt : ℕ→Prop)
    (actual : LayoutReportAt A orig S prior.valid he grp e pad C grain h amount prof seats romBase prev c rs m code time protectedAt matched)
    (named : (A).SiteNamed rank) (order : ∀x y,orig x<orig y ↔ originalId W.graph.Edge x<originalId W.graph.Edge y)
    (oldEnd : nextBase≤base ∧ (plan).source.base≤base ∧ (finish).out<base ∧ (top).base+N≤base ∧ births+N≤base)
    (dynamic : DepotRAM.Resident.Dynamic.Room postgeom r dim cm short H J M w (ptr).terrain)
    (rawFits : Owners.LayoutBit.Room (address).layout donor H J M (short*DescentPacking.PackedMatch.Local.fields r dim cm) w (postgeom).ownerBase)
    (keysLow : (address).layout.widen.shift.base+(address).layout.widen.shift.size≤rootAt ∧
      (address).layout.widen.apply.base+(address).layout.widen.apply.size≤rootAt)
    (adjacency : (peerBank).base+(peerBank).size≤rootAt)
    (hubRoom : hubBank.base+hubBank.size≤base) (hubCount : H≤hubBank.size)
    (oldHub : ∀j:Fin H,matched (hubBank.base+j.val)=((Census.hub A vid j).val:Computability.VPVNP.BurstRAM.Word w))
    (cables : ∀x j,Reads (wireBank x j) (fun v g=>DescentSignedCableCodec.encode
      (Prepare.signed A orig S prior.valid (grp).toEmbedding vid x j v g)) M m)
    (guarded : ∀x j (t : Row H J M),protectedAt ((wireBank x j).base+(row H J M t).val))
    (fits : ∀x j,(wireBank x j).Fits w base) (capacity : ∀x j,rows≤(wireBank x j).size)
    (terrainFit : (ptr).terrain.Fits w (src).base)
    (portsFit : Accessible (ptr).peers (ptr).owner H J M w (src).base)
    (ordFit : DescentHaloPackedRebase.Fits (ptr).ranks H J M w (src).base)
    (flagFit : DescentHaloPackedRebase.Fits (ptr).hubs H J M w (src).base)
    (topFit : (top).Fits w (src).base) (birthFit : (old).born.Fits w (src).base)
    (topRows : N≤(top).size) (bornWidth : SixBirths.width s M≤w) (sumSize : (s).outputBits*M≤w)
    (packed : M*max (DepotRAM.totalBits fmt) (DepotRAM.outputBits fmt)≤w/2) :
    let visit:=issuedVisit ticket h base old headerLow positive wide word overhead room grainAt
    let phase:=(visit.install.seq visit.venue).seq visit.gather
    phase.Runs matched ∧ (∀x,x<base→phase.image matched x=matched x) ∧ MeterPort.Pins ticket visit.port (phase.image matched) := by
  exact (matched_depot_date_board ticket h base C grain seats romBase prev wireBank hubBank headerLow positive wide word overhead
    room grainAt rs m matched code time protectedAt actual named order oldEnd dynamic rawFits keysLow
    adjacency hubRoom hubCount oldHub cables guarded fits capacity terrainFit portsFit ordFit flagFit
    topFit birthFit topRows bornWidth sumSize packed).1

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
