import OAI.Hierarchy.DescentIssuedDonorTotal
import OAI.Hierarchy.DescentResidentDonorReadRoom

namespace OAI
/-! # Numerical room of the true venue, donor input and six-birth table -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentRawCablePanel DescentPackedZip DescentSIMDLookup DescentPacking.PackedMatch.Local
open DescentPackedColony DescentHostDegree ProtocolRAM Computability.VPVNP.BurstRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε u : ℝ} {k i z D wire hist w : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he T c n target)
local notation "A" => prior.placement
local notation "H" => DescentCompiler.TerminalScale.hostRows (S.hostSize i)
local notation "J" => S.groupCount i
local notation "K" => 2^(k+1)
local notation "r" => 2^k
local notation "cm" => 2*(A).cap
local notation "D₀" => (A).degree
local notation "short" => max (k+3) (Nat.clog 2 (D₀+1))
local notation "prof" => DescentTerminalEpochBits.width G.C
local notation "fmt" => ticket.depotShape short
local notation "s" => shape r D₀ cm prof
local notation "amount" => ticket.installedDonorWidth short prof
variable (h base : ℕ) (old : PriorBanks (2^k) prior.placement.degree prior.placement.cap (2^(k+1)))
local notation "M" => lanes h amount
local notation "rows" => H*chunks J M
local notation "N" => (K*H)*chunks J M
local notation "rootAt" => ticket.donorStart short prof H h base
local notation "span₀" => DepotRAM.Resident.Dynamic.Placement.endAddress H J M D₀ (DepotRAM.rawBits fmt) 0
local notation "src" => ticket.donorSource short prof H h base span₀
local notation "address" => issuedAddressed ticket h base old
local notation "inputs" => DepotRAM.Resident.addressed fmt address H
local notation "postgeom" => DepotRAM.Resident.Dynamic.Placement.layout H J M D₀ (DepotRAM.rawBits fmt) rootAt old.peers.roster old.hub

local notation "pad" => prior.valid.host.trans (DescentCompiler.TerminalScale.hostPad _)
local notation "whole" => ticket.setupWords short prof H h
local notation "second" => base+DescentSIMDLookup.Book.words (DepotRAM.totalBits fmt) H J M
local notation "bin" => DepotRAM.Binary.count fmt*(2*2^(amount*M))
local notation "venueBase" => (postgeom).ownerBase
local notation "donor" => Gather.assembly old.operands (Gather.expr old.winners old.marked old.peers H)
local notation "obits" => (Owners.digits r D₀ short*3)*r

theorem issued_read_room (cpu : 0<w) (word : h≤w)
    (room : ticket.wholeDonorEnd short prof H h base≤2^w)
    (donorFit : (donor).Fits w base) (gate : old.gate.base+old.gate.size≤base)
    (inputsFit : ∀j,((address).cable j).Fits w base)
    (parent : Bank) (earlier : Accessible old.peers parent H J M w base)
    (hub : old.hub.base+old.hub.size≤base)
    (hostWord : H<2^w) (degreeWord : D₀<2^w)
    (toplow : old.topology.base+old.topology.size≤base) (bornLow : old.born.base+old.born.size≤base)
    (tops : N≤old.topology.size) (births : N≤old.born.size) :
    ReadRoom ticket h base old w ∧
    Owners.LayoutBit.Room (address).layout donor H J M (short*DescentPacking.PackedMatch.Local.fields r D₀ cm) w venueBase ∧
    ((address).layout.widen.shift.base+(address).layout.widen.shift.size≤rootAt ∧
     (address).layout.widen.apply.base+(address).layout.widen.apply.size≤rootAt) := by
  have leaves:=DonorSpace.leaves base whole span₀ rows h
  have done : ticket.donorMeter short prof H h base span₀+1+rows<2^w:=leaves.2.2.2.trans_le room
  have srcLimit : (src).base<2^w:=by
    have lim : (src).base+(src).size≤ticket.donorMeter short prof H h base span₀+1:=leaves.2.2.1
    omega
  have geom :=(ticket.venue_addresses short prof H h base).1
  have packedEnd : DepotRAM.Resident.Dynamic.Placement.endAddress H J M D₀ (DepotRAM.rawBits fmt) rootAt≤ (src).base:=geom.symm.le
  have stop:=DepotRAM.Resident.Dynamic.Placement.earlier H J M D₀ (DepotRAM.rawBits fmt)
    rootAt old.peers.roster old.hub packedEnd
  have rlimit:=stop.trans_lt srcLimit
  have lower : rootAt≤venueBase:=by change rootAt≤rootAt+_;omega
  have placed : base≤rootAt:=by change base≤base+_;omega
  have printed : second+bin≤rootAt:=by
    dsimp [OrdinaryLink.donorStart,DonorSpace.dynamicStart,OrdinaryLink.setupWords,DepotRAM.Setup.words,DepotRAM.Binary.words]
    omega
  have early : base≤venueBase:=placed.trans lower
  have mono (B₀ : Bank) (ok : B₀.Fits w base) : B₀.Fits w venueBase :=⟨ok.1,ok.2.1,ok.2.2.trans early⟩
  have increasing : Accessible old.peers parent H J M w venueBase :=
    ⟨fun j=>mono _ (earlier.ids j),earlier.idsRoom,mono _ earlier.roster,earlier.rosterRoom,
      mono _ earlier.offsets,earlier.offRoom,mono _ earlier.chunks,earlier.chunkRoom,mono _ earlier.source,earlier.srcRoom⟩
  have active:=DepotRAM.Resident.Dynamic.Placement.activeRoom H J M D₀ (DepotRAM.rawBits fmt)
    rootAt old.peers.roster old.hub le_rfl rlimit
  have gateFit : (address).layout.gate.Fits w venueBase := DepotRAM.bankFits _ (gate.trans early) rlimit
  have broadcast : (Owners.LayoutBit.broadcast (address).layout).Fits w venueBase:=
    ⟨⟨gateFit,trivial⟩,trivial,trivial,active.1,trivial⟩
  have donor₀:=ProtocolRAMGeneratedWrite.fits_mono _ early donorFit
  have big:=(ticket.installed_donor_widths short prof).2.2
  have zip:=DepotRAM.Binary.layout_room fmt M amount second venueBase big (printed.trans lower) rlimit broadcast donor₀
  have observe : (inputs).terrain.Fits w venueBase:=⟨zip.apply,zip.right,zip.shift,zip.left⟩
  have trueZip : Owners.LayoutBit.Room (address).layout donor H J M (short*DescentPacking.PackedMatch.Local.fields r D₀ cm) w venueBase :=
    ⟨gateFit,active.1,active.2,zip,cpu⟩
  have codeSize : max (Owners.inputBits r D₀ cm short) obits≤amount :=by
    have bound:obits≤DepotRAM.ownerBits fmt :=by
      change obits≤obits*(D₀+1)
      exact Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ _)
    have total:DepotRAM.ownerBits fmt≤DepotRAM.totalBits fmt:=by unfold DepotRAM.totalBits;omega
    exact max_le (ticket.ownerCode_fit short prof) (bound.trans (total.trans (by omega)))
  have area := (lanes_fit h amount).trans (Nat.div_le_div_right word)
  have birthWidth : DescentPacking.PackedMatch.SixBirths.width s M≤w:=by
    have letters : ((s).digit+1)*((s).pairs*6)≤DepotRAM.Fresh.laneWidth fmt s:=by
      unfold DepotRAM.Fresh.laneWidth;omega
    have lim:=(Nat.mul_le_mul_left M (letters.trans (ticket.installed_donor_widths short prof).2.1)).trans
      (area.trans (Nat.div_le_self w 2))
    simpa only [DescentPacking.PackedMatch.SixBirths.width,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using lim
  have packed := (Nat.mul_le_mul_left M codeSize).trans area
  have lookup:=DepotRAM.Resident.Dynamic.Placement.room H J M D₀ (DepotRAM.rawBits fmt) rootAt
    old.peers.roster old.hub rfl (inputs).terrain observe packed (earlier.roster.2.2.trans placed) (hub.trans placed)
    earlier.rosterRoom hostWord degreeWord (packedEnd.trans srcLimit.le)
  obtain ⟨ranks,hubs⟩:=DepotRAM.Resident.Dynamic.Placement.directories H J M D₀ (DepotRAM.rawBits fmt)
    rootAt old.peers.roster old.hub packedEnd srcLimit
  have neighbor:=DepotRAM.Resident.Dynamic.Placement.ownerAccessible H J M D₀ (DepotRAM.rawBits fmt)
    rootAt old.peers.roster old.hub packedEnd srcLimit old.peers parent increasing
  have weights:=le_trans (show DepotRAM.totalBits fmt≤ticket.depotWidth short from le_max_left ..)
    (ticket.installed_donor_widths short prof).1
  have raw : DepotRAM.outputBits fmt≤ticket.depotWidth short:=by
    rw [DepotRAM.outputBits,Nat.mul_comm]
    exact (Nat.mul_le_mul_left _ (le_max_left ..)).trans (le_max_right ..)
  have fit := (Nat.mul_le_mul_left M (max_le weights (raw.trans (ticket.installed_donor_widths short prof).1))).trans area
  have lock:=DepotRAM.Binary.layout_room fmt M amount second rootAt big printed (lower.trans_lt rlimit)
    (l:=.row) («r»:=.row) trivial trivial
  exact ⟨⟨lookup,fun j=>⟨⟨(inputsFit j).1,(inputsFit j).2.1,(inputsFit j).2.2.trans (early.trans stop)⟩,trivial⟩,
    ProtocolRAMGeneratedWrite.fits_mono _ stop observe,neighbor,ranks,hubs,
    DepotRAM.bankFits _ (toplow.trans (early.trans stop)) srcLimit,
    DepotRAM.bankFits _ (bornLow.trans (early.trans stop)) srcLimit,tops,births,birthWidth,fit⟩,
    trueZip,lock.shift.2.2,lock.apply.2.2⟩

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
