import OAI.Hierarchy.DescentDatedOriginalParentSource
import OAI.Hierarchy.DescentOrdinaryNamedModel

namespace OAI
/-! Original normalized presentation and incoming route banks on one actual ordinary date. -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentCableDonorNames DescentRawCablePanel DescentStageEdgeReceipt DescentSIMDLookup DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentHostDegree DescentHostDirectory StarKeys DescentPacking DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage DescentKernelHistory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q ε : ℝ} {k i z D wire hist w short a : ℕ}
variable {W : MarkedWorld F d P bits} {prior : Reached W G q ε S k i z D wire hist}
set_option quotPrecheck false
attribute [local irreducible] StarKeys.nativeKey
local notation "A" => prior.placement
local notation "J" => Fin (S.groupCount i)
local notation "V" => prior.V
local notation "native" => prior.order.trans Fin.valEmbedding
local notation "rank" => groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)
variable {he : 0≤ε} {choice : (prior.placement.stage.result he).Choice}
    {n : Normalize ((prior.placement.stage.result he).state choice)}
variable {z' D' : ℕ} {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
variable (ticket : OrdinaryLink prior he prior.placement.stage choice n next) (port : MeterPort prior)
local notation "H" => port.hosts
local notation "T" => (A).stage
local notation "home" => scanHomeAt he T
local notation "color" => scanColorAt he T
local notation "addr" => nativeAddress he T
local notation "r" => 2^k
local notation "rr" => BitDescription.scannedRows he T
local notation "lay" => bestLayout (branchWidth G (fun _ : (rr).pairs=>(T).z) ((rr).profile choice))
local notation "bytes" => donorNameBits (T).k (T).Δ
local notation "slots" => 2^(packExponent 20 (T).Δ)+2
local notation "gain" => gainExponent 20 (T).Δ
local notation "peers" => rotor A rank
local notation "grp" => Equiv.refl J
local notation "hosts" => port.vertex
variable (win : Fin (S.groupCount i)×prior.V→Fin (2^k)→Cell a) (hm : 0<port.groupsPerWord)
variable (named : prior.placement.SiteNamed (groupRank Fin.valEmbedding (prior.vertex.trans Fin.valEmbedding)))
    (fit : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val<2^short)
    (winner : ∀u,(win (prior.placement.pos u) (prior.placement.block u)).val=
      1+2*heap (nativeAddress he prior.placement.stage (scanHomeAt he prior.placement.stage u)).2+
        (scanColorAt he prior.placement.stage u).toNat)
    (df : prior.placement.degree<2^short)
    (order : ∀e f,(prior.order e).val<(prior.order f).val ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
variable (profile : ℕ)
local notation "positiveRows" => DescentRawCablePanel.Live A (rr).pick
local notation "model" => OrdinaryModel he T choice (J×V)
local notation "net" => rawGraph he T choice
local notation "place" => newSite W.graph (rr).pick lay (rr).pack
local notation:max "center" B:arg x:arg => mergeHub (B).chart.hub (T).k (gainExponent 20 (T).Δ) ((B).chart.key he T choice (place x))
local notation:max "current" x:arg => n.destination (rawInput he T choice ((rr).state choice) x)
local notation:max "oldRow" e:arg => (A).pos (W.graph.src (anchor (rr).pick (e).val))
local notation "caps" => 2^(packExponent 20 (T).Δ)+2
open DescentSixParty.MarkedWorld
variable (age:i<S.length) (radix:S.radix=2^k)

set_option maxHeartbeats 700000 in
/-- The old chart retained by the actual normalized link is enough to index both the
original roster and the entire source/target array. All equalities refer to its single physical order. -/
theorem parent_model :
    ∃B:model,HEq n (B.named he T choice prior.order) ∧
      HEq ticket.tape (B.namedTape he T choice prior.order) ∧
      ∃eqn:n.result=(B.named he T choice prior.order).result,
        (∀x:(net).Site,cast (congrArg (fun w:MarkedWorld F d P bits=>w.graph.Site) eqn)
          (current x)=B.rawSite he T choice x) ∧
        ∀x:(net).Site,let key:=splitKey (center B x)
          let u:=current x
          ((next.placement.pos u).1,next.placement.block u)=S.groupDigits age radix key.1 ∧
            (ticket.parentVenue port.enough (next.placement.pos u).2).1=hosts key.2.1 ∧
            (ticket.parentVenue port.enough (next.placement.pos u).2).2.val=SiteDecode.localNumber (T).k caps key.2 :=by
  have cuts : Normalize.CutsEqual (T).z n :=
    Eq.mpr (congrArg (fun amount => Normalize.CutsEqual amount n) ticket.quantum) ticket.cuts
  let issued := IssuedRows.named_model he T choice prior.order (n:=n) ticket.issued ticket.nameCount cuts
  let B := issued.choose
  have same : HEq n (B.named he T choice prior.order) := issued.choose_spec.1
  let loc := OrdinaryModel.locations he T choice prior.order B ((rr).state choice) same
  refine ⟨B,same,issued.choose_spec.2.1,loc.choose,loc.choose_spec,?_⟩
  intro x
  have read:=ticket.parentVenue_raw_location port.enough age radix x
  dsimp only at read ⊢
  rw [ticket.rawParentKey_donor x] at read
  have co:=B.chart.same_address he T choice ticket.donorChart (T).k (gainExponent 20 (T).Δ) (place x)
  change center B x=mergeHub ticket.donorHub (T).k (gainExponent 20 (T).Δ) (ticket.donorKey (place x)) at co
  rw [co]
  exact read

def modelPaths (e:positiveRows) : Option (Walk×Walk) :=
  let root:DescentSharedCableNames.Stage.Positive A:=⟨anchor (rr).pick e.val,e.property⟩
  Stage.parentRows (short:=short) A native S prior.valid rank win profile lay root (role e.val)

set_option maxHeartbeats 700000 in
include named fit winner df order in
theorem model_paths (B:model) (e:positiveRows) :
    let x:=place ((net).src e.val);let y:=place ((net).dst e.val)
    (modelPaths (short:=short) (prior:=prior) (choice:=choice) win profile e=none→x=y) ∧
      ∀p,modelPaths (short:=short) (prior:=prior) (choice:=choice) win profile e=some p→
        ParentIncidence.Actual (rotor A rank) (oldRow e) p ((B).chart.key he T choice x) ((B).chart.key he T choice y) :=by
  have chart : B.chart.col=addr:=eq_of_heq B.chart.native
  have nativeKey:B.chart.key he T choice=
      StarKeys.nativeKey W.graph W.core home color (T).cap addr B.chart.same lay :=by
    unfold IssuedDonorChart.key
    exact congrArg (fun loc => StarKeys.nativeKey W.graph W.core home color (T).cap loc B.chart.same lay) chart
  rw [nativeKey]
  exact Stage.parent_actual (short:=short) A native S prior.valid rank win he prior.valid.coordinates named fit winner df order profile
    B.chart.same lay e

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
