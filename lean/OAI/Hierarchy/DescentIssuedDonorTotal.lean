import OAI.Hierarchy.DescentIssuedDonorVisit
import OAI.Hierarchy.DescentPrivateCalendarAny

namespace OAI
/-! # The same allocated ordinary donor instructions terminate on every input -/
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

/-- Only static interval, expression-access and word-size facts occur here. -/
structure ReadRoom (w : ℕ) : Prop where
  geometry : DepotRAM.Resident.Dynamic.Room postgeom r D₀ cm short H J M w (inputs).terrain
  signed : ∀j,((inputs).signed j).Fits w (src).base
  terrain : (inputs).terrain.Fits w (src).base
  peers : Accessible (inputs).peers (inputs).owner H J M w (src).base
  ranks : DescentHaloPackedRebase.Fits (inputs).ranks H J M w (src).base
  hubs : DescentHaloPackedRebase.Fits (inputs).hubs H J M w (src).base
  sourceTopology : old.topology.Fits w (src).base
  sourceBirths : old.born.Fits w (src).base
  topRows : N≤old.topology.size
  birthRows : N≤old.born.size
  birthWidth : DescentPacking.PackedMatch.SixBirths.width s M≤w
  packed : M*max (DepotRAM.totalBits fmt) (DepotRAM.outputBits fmt)≤w/2

variable {header factor p : ℕ} (cut : header≤base) (positive : 0<ticket.installedDonorWidth (max (k+3) (Nat.clog 2 (prior.placement.degree+1))) (DescentTerminalEpochBits.width G.C))
    (wide : 2*ticket.installedDonorWidth (max (k+3) (Nat.clog 2 (prior.placement.degree+1))) (DescentTerminalEpochBits.width G.C)≤h)
variable (word : h≤w) (overhead : w≤factor*h) (room : ticket.wholeDonorEnd (max (k+3) (Nat.clog 2 (prior.placement.degree+1))) (DescentTerminalEpochBits.width G.C) (DescentCompiler.TerminalScale.hostRows (S.hostSize i)) h base≤2^w)
variable (grain : T.z=S.grainAt G.b p i)
local notation "v" => issuedVisit ticket h base old cut positive wide word overhead room grain

theorem issued_total (ok : ReadRoom ticket h base old w) (m : Memory w) :
    (((v).install.seq (v).venue).seq (v).gather).Runs m := by
  have leaves:=DonorSpace.leaves base (ticket.setupWords short prof H h) span₀ rows h
  have mounted:=DepotRAM.Resident.Dynamic.Placement.any H J M D₀ r cm short (A).cap prof w
    rootAt old.peers.roster old.hub (inputs).terrain ok.geometry
  intro pcs regs pubs cpu
  exact DepotRAM.Setup.date_any fmt s K H J M amount base (A).cap prof G.C G.k (A).z G.b
    (2^(packExponent 20 T.Δ)+2) src old.topology old.born inputs (v).venue (fun raw=>(mounted raw).1)
    (ticket.installed_donor_widths short prof).2.2 leaves.2.1 leaves.1 leaves.2.2.1 (leaves.2.2.2.trans_le room)
    ok.packed ok.signed ok.terrain ok.peers ok.ranks ok.hubs ok.sourceTopology ok.sourceBirths ok.topRows ok.birthRows ok.birthWidth m cpu

variable {j z₀ D₁ : ℕ} {W₀ : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₁ wire hist}
variable {path : Path start prior} (cal : MeterCalendar start header w path) (prep : NativePhase w)
local notation "allCPU" => prep.seq (((v).install.seq (v).venue).seq (v).gather)

theorem issued_total_date (ok : ReadRoom ticket h base old w) (earlier : cal.Total factor)
    (run : ∀m,prep.Runs m) : (cal.ordinary ticket (v).port allCPU).Total factor := by
  exact ⟨earlier,fun m=>NativePhase.seq_runs _ _ m (run m)
    (issued_total ticket h base old cut positive wide word overhead room grain ok _),(v).fits⟩

/-- The actual bank page updates nested in the chronological state keep the earlier
counter word and expose the same computed panel that MeterPort reads next. -/
theorem issued_ready_date {m : Memory w} (earlier : cal.Ready factor m)
    (run : prep.Runs (cal.memory m))
    (protect : prep.image (cal.memory m) header=cal.memory m header)
    (strict : header<base)
    (physical : let stage:=(((v).install.seq (v).venue).seq (v).gather); let matched:=prep.image (cal.memory m)
      stage.Runs matched ∧ (∀x,x<base→stage.image matched x=matched x) ∧
      MeterPort.Pins ticket (v).port (stage.image matched)) :
    (cal.ordinary ticket (v).port allCPU).Ready factor m := by
  exact cal.ready_ordinary earlier ticket (v).port prep _ run physical.1 protect
    (physical.2.1 header strict) (v).fits physical.2.2

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
