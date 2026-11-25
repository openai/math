import OAI.Hierarchy.GridChosenReceiverInstalledPrefix
import OAI.Hierarchy.GridChosenReceiverExecution
import OAI.Hierarchy.TraceReceiverElectedReplay
import OAI.Hierarchy.TraceReceiverInstalledScalars

namespace OAI
/-! # Compiling the chosen tick of the actual installed receiver image -/

noncomputable section
namespace Hierarchy.GridChosenReceiver
open ThreeFlat Diagonal PhysicalStage RAM RAM.PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open TraceAdmission GridScale GridThrough GridRegisteredSetting GridInstalledEvaluator GridReceiverDirectory Filter
open scoped Classical

open scoped Fin.CommRing
variable {F : Type} [Field F] [Fintype F] {Q : ℕ→ℕ} {loss : ℕ→ℝ}
section PerStream
variable {blk : Block F} {m A w degree stageRate rootRate tariff power : ℕ}
variable {v : TickSelection F (m+1) A w Q loss} (I : Installed blk m A w degree stageRate rootRate v)
variable (R : GridInstalledFit.Receipt blk m A w degree stageRate rootRate v I tariff power)
set_option quotPrecheck false
local notation "l" => (layout m A w (overhead Q loss w) v.copies degree stageRate rootRate)
local notation "arch" => (GridDescription.capacity w)
local notation "gate" => (26*GridDescription.sector w)
local notation "W" => (64*w)
local notation "rails" => (GridControllerSimGeometry.railCount m (l).sideMinusOne (l).bank)

local notation "D" => I.D
local notation "par" => (GridReceiverDirectory.native I.D l).parameters
local notation "ct" safe:arg => (GridNativeDispatch.actualTable I.D safe).codes
local notation "sr" safe:arg => GridNativeDispatch.selectorRoom I.D l R.table R.selector safe
local notation "sel" z:arg safe:arg => GridReceiverDirectory.InputWindow I.D l z safe (sr safe)
local notation "rooms" recv:arg => (R.rooms recv 0 gate).choose
local notation "ext" => (fun i=>(v.replacement.width_le_size i).trans v.size_le)
local notation "tape" recv:arg safe:arg z:arg x:arg c:arg i:arg => streamInput I recv 0 gate R.text (rooms recv) ext (ct safe) (sr safe) z x c i
local notation "st" recv:arg safe:arg z:arg x:arg c:arg i:arg => GridReceiverDirectory.shifted l w (tape recv safe z x c i)
local notation "orig" recv:arg safe:arg z:arg x:arg c:arg i:arg =>
  GridReceiverDirectory.original I.D l (sel z safe) (tape recv safe z x c i)
local notation "plan" => GridReceiverBanks.pinPlan I.D l
local notation "Q₀" geom:arg recv:arg safe:arg z:arg => streamLayout I R geom recv safe z

/-- This cache is shared by the sparse descendant traversal and the actual terminal compiler. -/
def slotCache (geom : ElectionRoom I.D l) (recv : Machine W arch arch arch)
    (safe : GridNativeDispatch.WordRoom I.D) (z : I.D.trace) (x : GridDiagonal.Pins (Fin rails))
    (c : Cell (m+1) (l).sideMinusOne) (i : Fin v.copies) :=
  TraceReceiverElectedCache.cache I.D l geom safe z (sel z safe) (GridTicks.index (c,i))
    (st recv safe z x c i) (orig recv safe z x c i) (Q₀ geom recv safe z)

set_option maxRecDepth 32000 in
set_option maxHeartbeats 4000000 in
theorem slot_descendants (geom : ElectionRoom I.D l) (recv : Machine W arch arch arch)
    (safe : GridNativeDispatch.WordRoom I.D) (z : I.D.trace) (x : GridDiagonal.Pins (Fin rails))
    (c : Cell (m+1) (l).sideMinusOne) (i : Fin v.copies) (m₀ : Memory W)
    (elected : GridReceiverDirectory.Elected I.D l geom safe z (sel z safe) (GridTicks.index (c,i))
      (st recv safe z x c i) (orig recv safe z x c i) m₀)
    (ready : ∀ j : TraceReceiverElectedJournal.Journal I.D l geom safe z (sel z safe) (GridTicks.index (c,i))
        (st recv safe z x c i) (orig recv safe z x c i) m₀,TraceReceiverInstalledScalars.Ready I.D l j) :
    (descendants I.D l).Spec (·=m₀) (fun _=> slotCache I R geom recv safe z x c i m₀)
      (TraceReceiverElectedCache.replay I.D l z (GridTicks.index (c,i))) := by
  obtain ⟨j⟩:=TraceReceiverElectedJournal.recover I.D l geom safe z (sel z safe) (GridTicks.index (c,i))
    (st recv safe z x c i) (orig recv safe z x c i) m₀ elected
  have scalar:=ready j
  let Q₁:=Q₀ geom recv safe z
  have topo:=streamLayout_rows I R geom recv safe z
  obtain ⟨bounds,small⟩:=streamLayout_room I R geom z
  have hd:=stream_header I recv 0 gate R.text (rooms recv) ext (ct safe) (sr safe) z x c i
  have frame:=elected_pins I geom safe z (sel z safe) (GridTicks.index (c,i)) elected
  let self:=GridDescription.code (q:=w^2) recv I.D.machine
  let s:=GridTicks.index (c,i)
  have late : 7≤w := (by decide : 7≤64^10).trans scalar.big
  have actual:=TraceReceiverTablesMount.run I.D l R.text self (s.val:Word W) (sel z safe)
    (tape recv safe z x c i) m₀ (2+(l).pinWidth) hd.1 (Nat.add_le_add_left hd.1 2) hd.2 frame late
    scalar.depthFit scalar.smallTemplate scalar.inputRoom scalar.high scalar.room
  have owners:=TraceReceiverDescendantVisits.prefix I.D l j Q₁ scalar.big topo.1 bounds small scalar.librarySize
    actual.2.2.2.2
  intro _ _ _ machine
  refine TraceReceiverElectedCache.seal I.D l j Q₁ actual.2.2.2.2 owners scalar.bound ?_ machine
  intro _ _ _ inner
  exact TraceReceiverElectedCache.publish I.D l j Q₁ scalar.aligned scalar.big scalar.depthFit
    scalar.bound scalar.held scalar.metadata scalar.rev scalar.seed bounds small topo.1 topo.2.1 topo.2.2.1 topo.2.2.2
    R.text self (tape recv safe z x c i) hd.1 hd.2 frame scalar.smallTemplate scalar.inputRoom
    scalar.librarySize scalar.high scalar.room scalar.rawFit scalar.even scalar.age scalar.fixed scalar.shrink
    scalar.refresh scalar.unit scalar.paid scalar.allowance scalar.margin scalar.alphabet inner

/-- Chosen receiver operand, source program and budget for every admissible post-election memory. -/
def InstalledDescendants (geom : ElectionRoom I.D l) : Prop :=
  ∀ (recv : Machine W arch arch arch) (safe : GridNativeDispatch.WordRoom I.D)
    (z : I.D.trace) (x : GridDiagonal.Pins (Fin rails)) (c : Cell (m+1) (l).sideMinusOne)
    (i : Fin v.copies) (m₀ : Memory W),
    GridReceiverDirectory.Elected I.D l geom safe z (sel z safe) (GridTicks.index (c,i))
      (st recv safe z x c i) (orig recv safe z x c i) m₀ →
    (descendants I.D l).Spec (·=m₀) (fun _=> slotCache I R geom recv safe z x c i m₀)
      (TraceReceiverElectedCache.replay I.D l z (GridTicks.index (c,i)))

end PerStream

/-- The positive prefix of the chosen grid supplies complete cache computation on the same
word ages as the padded receiver and the final root evaluator. -/
theorem eventual_installed_descendants (blk : Block F) (env : Envelopes Q loss) (m A : ℕ)
    (q : ℕ→ℕ) (range : ∀ᶠ w : ℕ in atTop,0<q w ∧ q w≤Q w) :
    ∀ᶠ w : ℕ in atTop,∀ age : ℕ,64*w=16*age^10 → Even w →
    ∀ (v : TickSelection F (m+1) A w Q loss),v.copies=q w →
    ∀ (I : Installed blk m A w (degree blk) (stageRate blk) rootRate v)
      {fee exponent : ℕ} (R : GridInstalledFit.Receipt blk m A w (degree blk) (stageRate blk) rootRate v I fee exponent),
    ∀ geom,InstalledDescendants I R geom := by
  let scale:=trace_scale env (m+1) A 2 q range
  filter_upwards [TraceReceiverInstalledScalars.ready (F:=F) (Q:=Q) (loss:=loss) blk m A scale] with w scalar
  intro age align even v copies I fee exponent R geom recv safe z x c i m₀ selected
  have real : 64*w=16*(TraceAdmission.receiverAge w)^10 := by rw [GridReceiverClock.age_exact align];exact align
  have axes : I.axes+1=evalDepth w (m+1) A 2 (overhead Q loss w) (q w)+1-w/2 := by
    rw [←copies];exact I.axes_eq
  intro _ _ _ machine
  exact slot_descendants I R geom recv safe z x c i m₀ selected
    (scalar even real v I R axes I.passes_eq geom recv safe z x c i m₀) machine

end Hierarchy.GridChosenReceiver
end

end OAI
