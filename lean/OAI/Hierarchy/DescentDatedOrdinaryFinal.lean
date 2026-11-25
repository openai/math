import OAI.Hierarchy.DescentPhysicalOrdinaryReturn
import OAI.Hierarchy.DescentDatedOrdinarySignedPhase
import OAI.Hierarchy.DescentOrdinaryVenueMachine
import OAI.Hierarchy.DescentDatedBeforeSignedMaterial
import OAI.Hierarchy.DescentDatedOrdinaryMark

namespace OAI
/-! # Source-ordered ordinary material, compact peer roster, survivor outlets, and result banks -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) {w : ℕ}
  (input : Dated.Operands) (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources)
local notation "first" => v.donorEnd floor
local notation "mat" => v.materialEnd floor
local notation "peer" => v.peerTail floor
local notation "marked" => v.markEnd floor
local notation "sign" => v.signedEnd floor
local notation "doneArgs" => v.endAddress floor
local notation "raster" => v.rasterEnd floor
local notation "nodes" => v.operandEnd floor
local notation "stop" => v.primitiveEnd floor
local notation "old" => (⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "hosts" => DescentOrdinaryVenueReturn.phase old mat v.k v.area.H v.area.D v.venue.hosts v.venue.degree w
local notation "coded" => v.signed.phase wires marked w

structure ResultSteps (w : ℕ) where
  parts : Bank
  adjacency : Bank
  «arguments» : NativePhase w
  paid : NativePhase w
  primitive : NativePhase w

variable (s : ResultSteps w) (bank : v.ResultRoom floor B w)
def beforeCount : NativePhase w :=
  ((((((((v.beforeSignedMaterial floor s.parts s.adjacency w).seq hosts).seq (v.mark floor input w)).seq coded).seq s.arguments).seq s.paid).seq (v.returnPhase floor B w bank)).seq s.primitive)

def finish : NativePhase w :=(v.beforeCount floor input count wires B s bank).seq (v.counter floor w)

/-- Every active row above the old donor returns to the same original RAM. -/
def Span (p : NativePhase w) (start bound : ℕ) :=
  start≤ bound ∧ ∀m,p.Runs m ∧ ∀j,j< start ∨ bound≤ j→p.image m j=m j

theorem Span.join {p q : NativePhase w} {a b c : ℕ} (x : Span p a b) (y : Span q b c) :
    Span (p.seq q) a c :=by
  refine ⟨x.1.trans y.1,fun m=>⟨p.seq_runs q m (x.2 m).1 (y.2 _).1,?_⟩⟩
  intro j h
  exact ((y.2 _).2 j (h.imp_left (fun v=>v.trans_le x.1))).trans
    ((x.2 _).2 j (h.imp_right (fun v=>y.1.trans v)))

structure ResultRuns : Prop where
  ranks : PriorHeader.Room s.adjacency v.area.H v.signed.groups v.signed.lanes v.signed.degree first w
  material : v.MaterialRoom (v.materialStart floor) s.parts
    (PriorHeader.reverseRank v.area.H v.signed.groups v.signed.lanes v.signed.degree first) w
  peers : DescentOrdinaryVenueReturn.Room old mat v.area.H v.area.D v.venue.hosts v.venue.degree w
  mark : v.MarkRoom floor input w
  signed : v.signed.Fits wires marked w
  signedRoom : sign< 2^w
  «arguments» : Span s.arguments sign doneArgs
  funded : Span s.paid doneArgs raster
  primitive : Span s.primitive nodes stop

theorem before_span (ok : v.ResultRuns floor input count wires s) :
    Span (v.beforeCount floor input count wires B s bank) first stop :=by
  have hp : Span hosts mat peer:=by
    refine ⟨?_,fun m=>DescentOrdinaryVenueReturn.any old mat v.k v.area.H v.area.D v.venue.hosts v.venue.degree w m ok.peers⟩
    change mat≤ DescentOrdinaryVenueReturn.roof mat _ _ _ _
    rw [DescentOrdinaryVenueReturn.shift];exact Nat.le_add_right ..
  have bits : Span (v.mark floor input w) peer marked:=⟨v.markShape.low _,v.mark_any floor input ok.mark⟩
  have hs : Span coded marked sign:=by
    refine ⟨v.signed.room _,?_⟩
    intro m
    have mapped:=v.signed.calibrated marked
    have actual:=v.signed.phase_any wires marked w m ok.signed (mapped.le.trans_lt ok.signedRoom)
    exact ⟨actual.1,fun j h=>actual.2.1 j (h.imp_right (fun t=>mapped.le.trans t))⟩
  have hl : raster≤ nodes:=by
    have a : raster≤ v.metaStart floor:=by change raster≤ v.venue.endAddress raster;rw [v.venue.translates];omega
    have b : v.metaStart floor≤ v.metaEnd floor:=by rw [metaEnd,v.metadata.ordinary_translate];omega
    have c : v.metaEnd floor≤ nodes:=by rw [operandEnd,v.operandBook.affine];omega
    exact a.trans (b.trans c)
  have hm : Span (v.beforeSignedMaterial floor s.parts s.adjacency w) first mat :=
    ⟨(v.signed_stage_paid floor).1,v.before_signed_any floor s.parts s.adjacency ok.ranks ok.material⟩
  exact (((((((hm.join hp).join bits).join hs).join ok.arguments).join ok.funded).join
    ⟨hl,v.returnPhase_run floor B w bank⟩).join ok.primitive)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
