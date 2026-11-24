import OAI.Computability.VPVNP.PairRefreshHookReader
import OAI.Computability.VPVNP.PairRefreshVertexRun
import OAI.Computability.VPVNP.PairRefreshTraversalAction
import OAI.Computability.VPVNP.PairShrinkOldHalfAddresses

/-!
# Frozen row data and the refresh role parser

A selected row supplies its two graph states, site, stored term choice and
physical workspace. The reader reconstructs the newer half from the popped
packet in scratch. Its one nondeterministic input is the independently chosen
older half.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords CompressorRecords.PortRefresh CompressorRecords.PortRefresh.NewSlots RefreshMapOperands NodeArguments NodeArguments.ChildScan
open TraversalControllerInputs TraversalRoles TraversalRows VertexImage DFS
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {bits n hist t : ℕ}

/-- Input state, selected refresh term, and physical row and workspace addresses used by the
refresh hook. -/
structure Site (n hist bits : ℕ) where
  /-- Number of lane bits left after moving the port bits into the base. -/
  lanes : ℕ
  /-- Network state entering the selected refresh, with the port bits still in the lane. -/
  state : State S.portExponent (S.portExponent+lanes)
  /-- Dyadic refresh choice recorded for this input state. -/
  choice : DyadicRefreshChoice state S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh
  /-- Input base, residual lane, and promoted port identifying the output row. -/
  port : (state.Base × BitWord lanes) × Fin (2^S.portExponent)
  /-- Slot degree used to size the private argument arena. -/
  degree : ℕ
  /-- Address immediately following the traversal rows. -/
  rowEnd : ℕ
  /-- Starting address of the input layer, used to locate the child row. -/
  older : ℕ
  /-- Address of the promoted output row whose packet supplies the newer half. -/
  parent : ℕ
  /-- Address of the first entry in the parent row’s child list. -/
  listHead : ℕ
  /-- Chronological index of the input layer of this refresh. -/
  level : ℕ
  /-- Number of traversal layers following this refresh’s output layer. -/
  later : ℕ
  /-- Starting address of the stored refresh terms for this level. -/
  start : ℕ
  /-- Incidence directory for the input state. -/
  prev : IncidenceDirectory bits
  /-- Incidence directory for the state produced by the refresh. -/
  next : IncidenceDirectory bits
  /-- Private address of the geometry words used by the traversal. -/
  geometry : BurstRAM.Word bits
  /-- Offset stored in the traversal geometry for locating the role data. -/
  roleOffset : BurstRAM.Word bits
  room : TraversalPlan.Room B state choice port degree n rowEnd
    (childNode state older B.recordLimit (oldSite state port)) parent hist bits

namespace Site

variable {B} (R : Site B n hist bits)
  (ties : Fin t ≃ Tie (2^S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
  (pub : Fin 11 → BurstRAM.Word bits) (m : Memory bits)

/-- State produced by applying the selected dyadic refresh to the input state. -/
noncomputable abbrev nextState := dyadicRefreshNext R.state S.graph (Nat.two_pow_pos _)
  (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh S.port_order S.degree_bounds.2 R.choice
/-- Input site obtained by putting the promoted port back into the lane. -/
noncomputable abbrev olderSite := oldSite R.state R.port
/-- Output site with the promoted port in its base and the residual lane unchanged. -/
noncomputable abbrev newerSite := promotedSites R.port
/-- Child row address computed from the input layer start and the input site ordinal. -/
noncomputable abbrev oldNode := childNode R.state R.older B.recordLimit R.olderSite
/-- Private memory layout for the row arguments, histogram, and cache. -/
def regions := TerminalLayout.privateRegions R.degree n R.rowEnd hist
/-- Private argument arena holding the packed child and parent half-wire assignments. -/
def arena := R.regions.arguments

/-- Event prefix for locating the parent layer and reading the child’s half-wire assignment. -/
noncomputable def front (node : BurstRAM.Word bits) (old : R.state.network.Half R.olderSite) :=
  RefreshVertexAssembly.inputTrace S.portExponent R.state R.olderSite old R.prev m R.listHead pub node R.level R.later

/-- Local refresh action on the two half-wire assignments, returning the event trace and
updated scratch on success. -/
noncomputable def action (old : R.state.network.Half R.olderSite) (new : R.nextState.network.Half R.newerSite)
    (s : Scratch bits n) :=
  TraversalPlan.canonicalAction B ties stride order R.state R.choice R.port R.degree n R.rowEnd R.oldNode R.parent
    R.room old new m (levelHead pub m R.level).val (levelHead pub m (R.level+1)).val R.geometry s

/-- Refresh reader that decodes the parent packet, consumes the old half from the tape, and
runs the local action. -/
noncomputable def read := RefreshHook.reader R.state R.olderSite R.nextState R.newerSite R.arena R.oldNode R.parent
  (R.front pub m) (R.action ties stride order pub m)

/-- DFS visit parser built from the refresh reader at this row. -/
noncomputable def hook := ShrinkRole.hook (R.read ties stride order pub m)

/-- The popped packet contains a typed parent argument and the three geometry
words used by the native role. The node number ties it to this selected row. -/
def Prepared (node : BurstRAM.Word bits) (s : Scratch bits n) : Prop :=
  node.val = R.parent ∧ ResidentGeometry s R.geometry R.roleOffset (word R.regions.histBase) ∧
    ∃ new : R.nextState.network.Half R.newerSite, (Packet.mk R.parent (packed R.nextState R.newerSite new)).Stored R.arena s

/-- Published memory, scalar fits, and the selected row in the completed
traversal layers. The register and memory semantics of the role are proved
separately from these source data. -/
structure Published : Prop where
  location : ∃ (header first pitch offset base : ℕ) (initial : TaggedLayer) (ls : List (Fiber bits))
    (j : Fin (initial :: ls.map Prod.fst).length) (id : Fin (initial :: ls.map Prod.fst)[j].layer.count),
    Resident pub m header first pitch offset B.recordLimit base initial ls ∧ j.val = R.level+1 ∧
    id.val = (NewSlots.sites R.state.baseIndex (bitWordFinEquiv R.lanes) R.port).val ∧
    R.later = ls.length-(R.level+1) ∧ R.parent = address B.recordLimit
      (layerBase B.recordLimit base (initial :: ls.map Prod.fst) j) id ∧
    layerBase B.recordLimit base (initial :: ls.map Prod.fst) (ls.length+1) < 2^bits
  fields : (directory S.portExponent R.older B.recordLimit R.arena R.prev).Stored m (levelHead pub m R.level+14)
  children : Row m R.parent R.listHead [word R.oldNode]
  headers : TraversalHeaders.Geometry (Fintype.card R.state.Base) R.lanes (levelHead pub m R.level).val
    (levelHead pub m (R.level+1)).val R.start R.arena R.prev R.next m
  fit : Fintype.card R.state.Base * 2^S.portExponent * 2^R.lanes * 2^S.portExponent ≤ 2^bits
  terms : Build.Stored R.state S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order))
    B.refresh R.choice ties R.start stride fit m
  oldCols : R.prev.ActualColumns R.state m
  newCols : R.next.ActualColumns R.nextState m
  positive : 0 < R.oldNode
  before : R.oldNode < R.parent
  roleAfter : R.regions.histBase ≤ (R.geometry+10).val
  histAfter : R.regions.histBase ≤ (R.geometry+11).val
  strideFit : B.recordLimit+2 < 2^bits
  lanesFit : 2^R.lanes < 2^bits
  wide : 2^S.portExponent < 2^bits

theorem oldFit (old : R.state.network.Half R.olderSite) :
    (Packet.mk R.oldNode (packed R.state R.olderSite old)).Fits R.arena bits n := by
  have width := (packed_length_le R.state R.olderSite old).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 R.room.oldDegree) R.room.oldWidth)
  have bound := TraversalGeometry.argument_end R.degree n R.rowEnd hist R.state R.olderSite old R.oldNode
    R.room.childBound R.room.oldDegree R.room.oldWidth
  have hh : R.regions.histBase ≤ R.regions.cacheBase := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  exact ⟨Nat.le_add_right ..,width.trans (Nat.le_succ _),bound.trans (hh.trans R.room.capacity.room.le)⟩

theorem newFit (new : R.nextState.network.Half R.newerSite) :
    (Packet.mk R.parent (packed R.nextState R.newerSite new)).Fits R.arena bits n := by
  have width := (packed_length_le R.nextState R.newerSite new).trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 R.room.newDegree) R.room.newWidth)
  have bound := TraversalGeometry.argument_end R.degree n R.rowEnd hist R.nextState R.newerSite new R.parent
    R.room.parentBound R.room.newDegree R.room.newWidth
  have hh : R.regions.histBase ≤ R.regions.cacheBase := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  exact ⟨Nat.le_add_right ..,width.trans (Nat.le_succ _),bound.trans (hh.trans R.room.capacity.room.le)⟩

theorem front_choices (node : BurstRAM.Word bits) (old : R.state.network.Half R.olderSite) :
    choiceBits (R.front pub m node old) = packed R.state R.olderSite old :=
  (RefreshVertexAssembly.inputTrace_cost S.portExponent R.state R.olderSite old R.prev m R.listHead pub node R.level R.later).2.2

end Site
end PairSimulation.RefreshHook

end VPVNP
end Computability
end OAI
