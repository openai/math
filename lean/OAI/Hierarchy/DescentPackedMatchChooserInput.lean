import OAI.Hierarchy.DescentPackedCensusReturn
import OAI.Hierarchy.DescentPackedMatchingWords

namespace OAI
/-! # The chooser's fixed program and the predecessor words it actually reads -/

namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Chooser
open DescentSixParty DescentCompiler DescentColonies DescentAffineColors DescentPackedColony DescentSIMDLookup ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

structure Layout where
  chart : Frame.Chart
  source : Bank
  marked : Bank
  origin : ℕ

namespace Layout
def shelves (C : Layout) (D k b M : ℕ) := Phase.Arena.shelves C.chart C.marked D k b (2*Phase.unit k b*M)
def census (C : Layout) (k b quota H G M : ℕ) := Phase.CensusTables.banks C.source C.origin ((1+b+2*quota)*2^k) M H G

def program (C : Layout) (D k b quota H G M w : ℕ) : Procedure w :=
  (PackedCensus.histograms (C.census k b quota H G M false) (C.census k b quota H G M true)
    C.chart.weights.base C.marked.base H G M w).seq (Phase.program (C.shelves D k b M) w H G M)

def ticks (C : Layout) (D k b quota H G M w : ℕ) :=
  PackedCensus.clocks (C.census k b quota H G M false) (C.census k b quota H G M true) H G M+
    Phase.cost (C.shelves D k b M) w H G M

def last (C : Layout) (D k b H G M : ℕ) := (C.shelves D k b M).output+2^k*(H*chunks G M)
def winners (C : Layout) (D k b H G M : ℕ) (x : Fin (2^k)) : Bank :=
  ⟨PackedWinnerRAM.slot (C.shelves D k b M).output (H*chunks G M) x,Nat.clog 2 (H*chunks G M+1)⟩
end Layout

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k age L G ℓ w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (groups : J≃Fin G) (hosts : V≃Fin L) (hv : L≤2^ℓ)
variable (C : Layout) (b quota payload unit ratio : ℕ)
local notation "H" => 2^ℓ
local notation "M" => lanes payload unit
local notation "fee" => A.wire*(A.z*gadget.b)
local notation "gap" => DescentHostDegree.gap A.degree
local notation "exp" => DescentHostDegree.packExponent 20 A.degree
local notation "cap" => 2^exp*(fee*A.cap)
local notation "roster" => DynamicSplit.Roster ℓ A.degree

structure Geometry (rs : roster) : Prop where
  covered : Phase.recordWidth k b quota≤unit
  wide : 2*unit≤payload
  hardware : w≤ratio*payload
  embed : payload≤w
  neighbors : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v u : V,i=(hosts v).castLE hv ∧ j=(hosts u).castLE hv ∧ v∈A.near u
  room : Phase.Arena.Room C.chart C.marked A.degree k b (2*Phase.unit k b*M) w H G
  weights : fee*A.cap<2^b
  positions : G*H*2^k<2^w
  core : W.core.card<2^w
  sourceFits : C.source.Fits w C.chart.weights.base
  sourceRows : H*chunks G M≤C.source.size
  censusEnd : Phase.CensusTables.finish C.origin ((1+b+2*quota)*2^k) M H G≤C.chart.weights.base
  extent : C.marked.base+H*chunks G M<2^w
  apart : C.chart.weights.base+H*chunks G M≤C.marked.base
  earlier : C.chart.roster.base+C.chart.roster.size≤C.chart.weights.base

structure Setup (rs : roster) (m : Memory w) : Prop extends
    Geometry (G:=G) (w:=w) A hosts hv C b quota payload unit ratio rs where
  censusROM : (Phase.CensusTables.image C.origin ((1+b+2*quota)*2^k) (b*2^k) M H G
    (fun fl=>PackedCensus.lookup fl b quota k A.wire 256 (A.z*gadget.b) A.hist)).Resident m
  phaseROM : (Phase.Arena.image C.chart A.fieldBits A.degree H G b (2*Phase.unit k b*M) gap cap).Resident m
  stored : ∀v i,m (C.chart.roster.base+(v.val*A.degree+i.val))=(target (rs v i):Word w)

structure Ready (rs : roster) (m : Memory w) : Prop extends Setup (G:=G) A hosts hv C b quota payload unit ratio rs m where
  input : ∃slots : A.PortOrder quota,Reads C.source (A.rawCensus (GroupStage.plane hosts hv) groups slots b) M m

set_option maxHeartbeats 4000000 in
set_option Elab.async false in
theorem execute (S : AtomSchedule) (ready : A.StateBounds S age) (he : 0≤ε)
    (rs : DynamicSplit.Roster ℓ A.degree) (m : Memory w) (start : Ready A groups hosts hv C b quota payload unit ratio rs m) :
    ∃mid : Memory w,∃i : Fin (2^k-1),∃j : Candidate k,0<(lanes payload unit) ∧
      (C.program A.degree k b quota (2^ℓ) G (lanes payload unit) w).Exec m mid (C.ticks A.degree k b quota (2^ℓ) G (lanes payload unit) w) ∧
      C.ticks A.degree k b quota (2^ℓ) G (lanes payload unit) w*w≤ratio*((96+Phase.factor k A.degree)*(payload+(2^ℓ)*payload+4*(2^ℓ)*G*unit)) ∧
      DescentColonies.seedAt k i=(DescentKernelHistory.BitDescription.scannedRows he A.stage).μ ∧
      j=code (DescentKernelHistory.BitDescription.scannedRows he A.stage).α (DescentKernelHistory.BitDescription.scannedRows he A.stage).β ∧
      mid (C.shelves A.degree k b (lanes payload unit)).mu=(i.val:Word w) ∧ mid (C.shelves A.degree k b (lanes payload unit)).paint=(j.val:Word w) ∧
      (∀ x : Fin (2^k), Reads (C.winners A.degree k b (2^ℓ) G (lanes payload unit) x) (fun h g=>(A.publishedTicket groups hosts rs) i j h g x) (lanes payload unit) mid) ∧
      (∀ u : W.graph.Site, ((A.publishedTicket groups hosts rs) i j ((hosts (A.pos u).2).castLE hv) (groups (A.pos u).1) (A.block u)).val=
        1+2*heap ((DescentStageEdgeReceipt.nativeAddress he A.stage) ((DescentStageEdgeReceipt.scanHomeAt he A.stage) u)).2+((DescentStageEdgeReceipt.scanColorAt he A.stage) u).toNat) ∧
      (∀ a : ℕ, a<C.chart.weights.base ∨ C.last A.degree k b (2^ℓ) G (lanes payload unit)≤a → mid a=m a) := by
  obtain ⟨slots,input⟩:=start.input
  obtain ⟨mid,i,j,hm,first,paid,_,muWord,paintWord,low,high,seed,paint,words,_⟩:=
    A.packed_resident_census_return_at_unit groups hosts hv unit start.covered S ready he C.chart C.marked rs
      start.neighbors start.room ratio start.wide start.hardware start.weights start.positions start.core slots C.source
      C.origin m input start.sourceFits start.sourceRows start.censusROM start.censusEnd start.extent start.embed
      start.apart start.earlier start.phaseROM start.stored
  exact ⟨mid,i,j,hm,first,paid,seed,paint,muWord,paintWord,words,A.published_actor groups hosts hv he rs start.neighbors i j seed paint,
    fun a h=>h.elim (low a) (high a)⟩

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Chooser

end OAI
