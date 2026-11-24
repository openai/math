import OAI.Computability.VPVNP.PairShrinkSurvivingSelected
import OAI.Computability.VPVNP.PairShrinkCallHeader
import OAI.Computability.VPVNP.PairSimulationSliceReads
import OAI.Computability.VPVNP.PairShrinkArgumentReadBounds

/-!
# External reads of the selected surviving-field gather

The native column follows the old level's absolute CD and inverse slot tables.
The next level supplies the incoming incidence and width prefixes. Its interval
frame comes from the dense row allocated to this motif and role.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSurvivingReadBounds

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData
open CompressorRecords PhaseRecipe SlotLevel ShrinkSlots ShrinkSliceSweep SliceSchedule
open NodeArguments ShrinkSurvivingPointers ShrinkSurvivingOperands ShrinkSurvivingSelected
open SourceTransport
open private Allocation.local_stop Allocation.record_stop from
  OAI.Computability.VPVNP.CompressorShrinkSliceSweep
open scoped Fin.CommRing

variable {w H : ℕ} {pub : Fin 5 → Word w} {state : Word w} {mem : Memory w}
local notation "safe" => Expr.ReadsFrom (· < H) pub state mem
local notation "ev" => Expr.eval pub state mem

private theorem cell_safe (level : Expr) (i : ℕ) (hs : safe level)
    (room : (ev level).val + i < H) : safe (cell level i) := by
  refine ⟨⟨hs, trivial⟩, ?_⟩
  change (ev level + (i : Word w)).val < H
  rw [Fin.val_add, Fin.val_natCast]
  exact (Nat.mod_le _ _).trans_lt ((Nat.add_le_add_left (Nat.mod_le i _) _).trans_lt room)

/-- The six addresses or dimensions supplied by the old level. -/
structure TableReads (P : ShrinkSurvivingPointers.Inputs) (H : ℕ)
    (pub : Fin 5 → Word w) (state : Word w) (mem : Memory w) : Prop where
  dense : P.dense.ReadsFrom (· < H) pub state mem
  absolute : P.absoluteHead.ReadsFrom (· < H) pub state mem
  inverse : P.inverseHead.ReadsFrom (· < H) pub state mem
  lanes : P.lanes.ReadsFrom (· < H) pub state mem
  bases : P.oldBases.ReadsFrom (· < H) pub state mem
  interval : P.intervalHead.ReadsFrom (· < H) pub state mem

theorem inputs_reads (a : ℕ) (level motif arena stride node dest : Expr)
    (levelSafe : safe level) (motifSafe : safe motif) (arenaSafe : safe arena)
    (strideSafe : safe stride) (oldRoom : (ev level).val + 42 < H)
    (nextRoom : (ev (cell level 40)).val + 59 < H) :
    let K := inputs a level motif arena stride node dest
    TableReads K.tables H pub state mem ∧
      ArgumentReadBounds.FieldsReadable K.half H pub state mem := by
  intro K
  have old (i : ℕ) (h : i ≤ 42) := cell_safe level i levelSafe (by omega)
  have next (i : ℕ) (h : i ≤ 59) := cell_safe (cell level 40) i (old 40 (by decide)) (by omega)
  exact ⟨⟨motifSafe, old 39 (by decide), old 41 (by decide), old 3 (by decide),
    ⟨old 0 (by decide), trivial⟩, old 42 le_rfl⟩,
    ⟨arenaSafe, strideSafe, next 58 (by decide), next 59 le_rfl⟩⟩

/-- The job destination uses the old base and residual-lane counts. -/
theorem destination_reads (O : ShrinkCallHeader.Operands) (a : ℕ) (dir : Bool) (t : Fin 4)
    (levelSafe : safe O.level) (hiddenSafe : safe O.hidden) (strideSafe : safe O.slotStride)
    (oldRoom : (ev O.level).val + 3 < H) : safe ((O.inputs a).surviving dir t) := by
  have h₀ := cell_safe O.level 0 levelSafe (by omega)
  have h₃ := cell_safe O.level 3 levelSafe oldRoom
  have count : safe (O.count a) := ⟨⟨⟨h₀, trivial, h₃⟩, trivial⟩, trivial⟩
  exact ⟨⟨hiddenSafe, ⟨trivial, count⟩, strideSafe⟩, trivial, strideSafe⟩

variable {a b g : ℕ} {δ : ℝ} (X : State a (packingLaneBits a g))
local notation "s" => levelShape (b := b) X
local notation "sub" => Shape.subdivisions (levelShape (b := b) X)
local notation "tags" => bitWordFinEquiv (packingTagBits (2 ^ a))
local notation "lanes" => bitWordFinEquiv g

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

/-- Only one absolute CD and one inverse record are loaded to recover the
endpoint port. Repeated occurrences of these loads stay inside the same arrays. -/
theorem port_reads (P : ShrinkSurvivingPointers.Inputs) (m : X.packingData.Motif)
    (t : Fin 4) (dir : Bool) (j : Fin ((levelShape (b := b) X).subdivisions t))
    (heads : Heads) (absolute : Word w)
    (hp : Published X P m heads absolute (b := b) (pub := pub) (state := state) (mem := mem))
    (headsSafe : TableReads P H pub state mem)
    (directory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber absolute mem)
    (absFit : absolute.val + (ShrinkMotifOrder.stateNumber X m).val < 2 ^ w)
    (absRoom : absolute.val + (ShrinkMotifOrder.stateNumber X m).val < H)
    (inverseRoom : SlotLevel.targetsHead s heads ≤ H) :
    safe (port (2 ^ b) (P.rect sub t j dir)) := by
  let ordinal := (ShrinkMotifOrder.stateNumber X m).val
  have ha : safe P.absolute := by
    refine ⟨⟨headsSafe.absolute, headsSafe.dense⟩, ?_⟩
    change (ev P.absoluteHead + ev P.dense).val < H
    rw [hp.absoluteHead, hp.dense, Fin.val_add, Fin.val_natCast]
    exact (Nat.mod_le _ _).trans_lt
      ((Nat.add_le_add_left (Nat.mod_le ordinal _) _).trans_lt absRoom)
  have arcSafe : safe (P.arc sub t j) :=
    ⟨⟨⟨⟨⟨⟨ha, headsSafe.lanes⟩, headsSafe.bases, trivial⟩, trivial⟩, trivial⟩, headsSafe.lanes⟩,
      ha, headsSafe.lanes⟩
  let id := Slots.arcAddress X.packingData sub X.baseIndex tags lanes (pad s) (.inl ⟨t, m, j⟩)
  have abs := absolute_eval P X m absolute hp.dense hp.absoluteHead absFit directory
  have arc : ev (P.arc sub t j) = (id.val : Word w) :=
    arc_eval P X.packingData sub X.baseIndex tags lanes m t j abs hp.laneCount hp.oldBases
  have inside : 2 * id.val + dir.toNat < fields s := by
    let N := Slots.RecordCount (s).bases (s).tags (s).lanes (s).oldDegree (s).colors (pad s) sub
    have hi : id.val < N := id.isLt
    have side : dir.toNat < 2 := by cases dir <;> decide
    change _ < N * 2
    omega
  have rectSafe : safe (P.rect sub t j dir) := by
    refine ⟨⟨headsSafe.inverse, ⟨arcSafe, trivial⟩, trivial⟩, ?_⟩
    change (ev P.inverseHead + (ev (P.arc sub t j) * (2 : Word w) + (dir.toNat : Word w))).val < H
    rw [hp.inverseHead, arc, ← Nat.cast_ofNat (R := Word w) (n := 2), ← Nat.cast_mul,
      ← Nat.cast_add, ← Nat.cast_add, Nat.mul_comm id.val 2, Fin.val_natCast]
    exact (Nat.mod_le _ _).trans_lt ((Nat.add_lt_add_left inside _).trans_le inverseRoom)
  exact ⟨⟨⟨⟨rectSafe, trivial⟩, trivial⟩, trivial⟩, rectSafe, trivial⟩

/-- Confinement of every compiled operand in one native column, for either
endpoint of the actual selected wire. -/
theorem setup_reads (K : ShrinkSurvivingColumn.Inputs) (m : X.packingData.Motif)
    (t : Fin 4) (dir : Bool) (j : Fin ((levelShape (b := b) X).subdivisions t))
    (ready : ShrinkMotif.Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)
    (layout : Bool) (width : X.packingData.Motif → Fin 4 → ℕ)
    (heads : Heads) (absolute : Word w)
    (hp : Published X K.tables m heads absolute (b := b) (pub := pub) (state := state) (mem := mem))
    (headsSafe : TableReads K.tables H pub state mem)
    (directory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber absolute mem)
    (sorted : Build.OrderedTables X ready layout heads mem)
    (absFit : absolute.val + (ShrinkMotifOrder.stateNumber X m).val < 2 ^ w)
    (absRoom : absolute.val + (ShrinkMotifOrder.stateNumber X m).val < H)
    (inverseRoom : SlotLevel.targetsHead s heads ≤ H)
    (slotFit : finish s heads < 2 ^ w) (degreeFit : 2 ^ b < 2 ^ w) (twoFit : 2 < 2 ^ w)
    (inc : IncidenceDirectory w) (A : Arena) {layer pitch : ℕ}
    (stored : K.half.Stored inc A layer pitch pub state mem)
    (fieldHeads : ArgumentReadBounds.FieldsReadable K.half H pub state mem)
    (nodeSafe : safe K.node) (destSafe : safe K.destination) :
    let slots := X.shrinkStateIndex ready layout
    let Y := X.shrinkOutputState layout sub width slots
    let size := Fintype.card Y.Base * 2 ^ g * 2 ^ b
    inc.ActualColumns Y mem → size ≤ 2 ^ w → inc.actualIn.val + size ≤ H →
      inc.width.val + size ≤ H → ∀ i, safe ((K.setup (2 ^ b) sub t dir j).operands i) := by
  intro slots Y size cols cap inRoom widthRoom i
  let portExpr := port (2 ^ b) (K.tables.rect sub t j dir)
  let v := site X layout m t dir
  let k := slot X layout sub width slots m t dir j
  have portAt : ev portExpr = IncidenceDirectory.actualPort Y (v, k) :=
    port_eq X ready layout width K.tables m t dir j heads absolute hp directory sorted
      absFit slotFit degreeFit twoFit
  have portSafe := port_reads X K.tables m t dir j heads absolute hp headsSafe directory
    absFit absRoom inverseRoom
  have src := ArgumentReadBounds.field Y v k K.half inc A stored cols cap degreeFit
    K.node portExpr dir portAt H fieldHeads nodeSafe portSafe inRoom widthRoom
  have frame : safe (K.tables.frame sub t j) :=
    ⟨⟨headsSafe.interval, ⟨⟨headsSafe.dense, trivial⟩, trivial⟩, trivial⟩, trivial⟩
  fin_cases i <;> first | exact src | exact destSafe | exact frame | trivial

/-- Every native frame load is below the exclusive end of its dense row bank. -/
theorem frame_end {n A : ℕ} (T : Allocation w n A) (fit : T.Fits) (idx : Fin n)
    (t : Fin 4) (j : Fin (T.subdiv t)) :
    ShrinkSurvivingFrames.head (T.row (idx, t)) (T.subdiv t) j + 2 < T.last := by
  have bank := (T.row_vals fit (idx, t)).2.2.1
  have localEnd := Allocation.local_stop T (idx, t)
  have globalEnd := Allocation.record_stop T (idx, t)
  have hi := j.isLt
  apply lt_of_lt_of_le _ (localEnd.trans globalEnd)
  simp only [ShrinkSurvivingFrames.head, bank, stop, one_mul]
  omega

theorem frame_reads {n A : ℕ} (T : Allocation w n A) (fit : T.Fits) (idx : Fin n)
    (t : Fin 4) (j : Fin (T.subdiv t)) (room : T.last ≤ H) (bs : List Bool) :
    let ptr := ShrinkSurvivingFrames.head (T.row (idx, t)) (T.subdiv t) j
    Reads (· < H) (PrivateSlices.frameEvents mem (ptr : Word w) bs) := by
  intro ptr
  have h : ptr + 2 < H := (frame_end T fit idx t j).trans_le room
  have hw : ptr + 2 < 2 ^ w := (frame_end T fit idx t j).trans fit.room
  have atOne : ((ptr : Word w) + 1).val = ptr + 1 := by
    rw [← Nat.cast_add_one]
    exact Nat.mod_eq_of_lt (by omega)
  have atTwo : ((ptr : Word w) + 1 + 1).val = ptr + 2 := by
    rw [← Nat.cast_add_one, ← Nat.cast_add_one]
    exact Nat.mod_eq_of_lt hw
  apply PrivateSlices.frameEvents_reads
  · exact (Nat.mod_le _ _).trans_lt (by omega)
  · omega
  · omega

end PairSimulation.ShrinkSurvivingReadBounds

end VPVNP
end Computability
end OAI
