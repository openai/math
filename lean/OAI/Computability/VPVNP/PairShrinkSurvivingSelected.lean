import OAI.Computability.VPVNP.PairShrinkSurvivingColumn
import OAI.Computability.VPVNP.PairShrinkSurvivingRect

/-!
# Surviving slice pointers on the selected shrinking graph

The old header identifies the absolute CD array, the retained inverse slot
array and the dense interval banks. The next header supplies the incidence
and width columns of the private packet's state. Only the selected motif and
the private map-job addresses vary between visits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkSurvivingSelected

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkEnergy
open Compression.ShrinkMotif
open CompressorRecords CompressorRecords.PhaseRecipe CompressorRecords.SlotLevel
open CompressorRecords.ShrinkSlots CompressorRecords.PortRefresh.ArgumentAddress
open CompressorRecords.ShrinkSliceSweep
open ShrinkSurvivingOperands ShrinkSurvivingPointers NodeArguments
open scoped Fin.CommRing

/-- Address lookup relative to a dynamic level-header pointer. -/
def cell (header : Expr) (offset : ℕ) : Expr := .load (header.add (.lit offset))

/-- Dynamic heads used by the selected output node. The old degree exponent
fixes the local packing radices. The input base count and the remaining lanes
are read from the header at runtime. -/
def inputs (a : ℕ) (level motif arena stride node dest : Expr) : ShrinkSurvivingColumn.Inputs :=
  let next := cell level 40
  let baseRadix := 2 ^ (packingTagBits (2 ^ a)) * (2 ^ a * (2 ^ (2 * 2 ^ a + 1) * 2 ^ a))
  let H : ShrinkSurvivingPointers.Inputs :=
    ⟨motif, cell level 39, cell level 41, cell level 3, (cell level 0).mul (.lit baseRadix),
      cell level 42⟩
  let half : ShrinkOldHalves.Physical.Header :=
    ⟨arena, stride, cell next 14, cell next 15, cell next 57, cell next 58, cell next 59⟩
  ⟨H, half, node, dest⟩

variable {a b g w : ℕ} {δ : ℝ} (X : State a (packingLaneBits a g))
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ) (layout : Bool)
variable (width : X.packingData.Motif → Fin 4 → ℕ)
local notation "s" => levelShape (b := b) X
local notation "sub" => Shape.subdivisions (levelShape (b := b) X)
local notation "I" => X.shrinkStateIndex ready layout
local notation "Y" => X.shrinkOutputState layout sub width (I)
local notation "tags" => bitWordFinEquiv (packingTagBits (2 ^ a))
local notation "lanes" => bitWordFinEquiv g

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

variable (H : ShrinkSurvivingPointers.Inputs)
variable (m : X.packingData.Motif) (t : Fin 4) (dir : Bool)
variable (j : Fin ((levelShape (b := b) X).subdivisions t))
variable {pub : Fin 5 → Word w} {state : Word w} {mem : Memory w}

/-- The runtime table expressions encode the selected motif, absolute CD and inverse-slot table
heads, residual lane count, and old base-arc count. -/
structure Published (heads : Heads) (absolute : Word w) : Prop where
  dense : H.dense.eval pub state mem = ((ShrinkMotifOrder.stateNumber X m).val : Word w)
  absoluteHead : H.absoluteHead.eval pub state mem = absolute
  inverseHead : H.inverseHead.eval pub state mem = (SlotLevel.inverseHead s heads : Word w)
  laneCount : (H.lanes.eval pub state mem).val = 2 ^ g
  oldBases : H.oldBases.eval pub state mem =
    (Slots.oldBaseArcCount (Fintype.card X.Base) (2 ^ packingTagBits (2 ^ a))
      (2 ^ a) (2 * 2 ^ a + 1) : Word w)


private theorem cell_eval (header : Expr) (n offset : ℕ)
    (word : header.eval pub state mem = (n : Word w)) (fit : n + offset < 2 ^ w) :
    (cell header offset).eval pub state mem = mem (n + offset) := by
  change mem (header.eval pub state mem + (offset : Word w)).val = _
  rw [word, ← Nat.cast_add, Fin.val_natCast, Nat.mod_eq_of_lt fit]

/-- Instantiate the runtime setup from the actual header cells. The only
variable private operands are the arena, the node and the job's destination. -/
theorem inputs_readback (heads : Heads) (absolute : Word w) (old next interval : ℕ)
    (inc : IncidenceDirectory w) (A : Arena) (layer pitch : ℕ)
    (header motif arena stride node dest : Expr)
    (headerWord : header.eval pub state mem = (old : Word w))
    (motifWord : motif.eval pub state mem = ((ShrinkMotifOrder.stateNumber X m).val : Word w))
    (arenaWord : arena.eval pub state mem = (A.start : Word w))
    (strideWord : stride.eval pub state mem = (A.stride : Word w))
    (oldFit : old + 42 < 2 ^ w) (nextFit : next + 59 < 2 ^ w)
    (vertices : mem (old + 0) = (Fintype.card X.Base : Word w))
    (laneWord : (mem (old + 3)).val = 2 ^ g)
    (absWord : mem (old + 39) = absolute) (nextWord : mem (old + 40) = (next : Word w))
    (inverseWord : mem (old + 41) = (SlotLevel.inverseHead s heads : Word w))
    (intervalWord : mem (old + 42) = (interval : Word w))
    (layerWord : mem (next + 14) = (layer : Word w))
    (pitchWord : mem (next + 15) = (pitch : Word w))
    (outWord : mem (next + 57) = inc.actualOut)
    (inWord : mem (next + 58) = inc.actualIn) (widthWord : mem (next + 59) = inc.width) :
    let K := inputs a header motif arena stride node dest
    Published X K.tables m heads absolute (b := b) (pub := pub) (state := state) (mem := mem) ∧
      K.half.Stored inc A layer pitch pub state mem ∧
      K.tables.intervalHead.eval pub state mem = (interval : Word w) := by
  intro K
  have oldAt (i : ℕ) (hi : i ≤ 42) := cell_eval header old i headerWord (by omega)
  have newWord := (oldAt 40 (by decide)).trans nextWord
  have newAt (i : ℕ) (hi : i ≤ 59) := cell_eval (cell header 40) next i newWord (by omega)
  refine ⟨⟨motifWord, (oldAt 39 (by decide)).trans absWord,
    (oldAt 41 (by decide)).trans inverseWord, ?_, ?_⟩,
    ⟨arenaWord, strideWord, (newAt 14 (by decide)).trans layerWord,
      (newAt 15 (by decide)).trans pitchWord, (newAt 57 (by decide)).trans outWord,
      (newAt 58 (by decide)).trans inWord, (newAt 59 (by decide)).trans widthWord⟩,
    (oldAt 42 le_rfl).trans intervalWord⟩
  · exact (congrArg Fin.val (oldAt 3 (by decide))).trans laneWord
  · change (cell header 0).eval pub state mem * _ = _
    rw [(oldAt 0 (by decide)).trans vertices]
    exact (Nat.cast_mul ..).symm

/-- The runtime endpoint expression reads a genuine record from the retained
tables and returns the exact state port on either side of the wire. -/
theorem port_eq (heads : Heads) (absolute : Word w)
    (hp : Published X H m heads absolute (b := b) (pub := pub) (state := state) (mem := mem))
    (directory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber absolute mem)
    (tables : Build.OrderedTables X ready layout heads mem)
    (absFit : absolute.val + (ShrinkMotifOrder.stateNumber X m).val < 2 ^ w)
    (fit : finish s heads < 2 ^ w) (degreeFit : 2 ^ b < 2 ^ w) (twoFit : 2 < 2 ^ w) :
    (port (2 ^ b) (H.rect sub t j dir)).eval pub state mem =
      IncidenceDirectory.actualPort (Y)
        (site X layout m t dir, slot X layout sub width (I) m t dir j) := by
  let id := Slots.arcAddress X.packingData sub X.baseIndex tags lanes (pad s) (.inl ⟨t, m, j⟩)
  let inverse := SlotLevel.inverseHead s heads
  have abs := absolute_eval H X m absolute hp.dense hp.absoluteHead absFit directory
  have idx : (H.arc sub t j).eval pub state mem = (id.val : Word w) :=
    arc_eval H X.packingData sub X.baseIndex tags lanes m t j abs hp.laneCount hp.oldBases
  have limit : inverse + fields s ≤ finish s heads := by
    simp only [inverse, finish, widthHead, inHead, outHead, inverseBaseHead, stopAddress,
      shiftsHead, targetsHead]
    omega
  have cap : owners s * (s).newDegree ≤ 2 ^ w := by
    have r : owners s * (s).newDegree ≤ inverse := by
      change _ ≤ rowsHead s heads + (owners s + fields s) * (s).newDegree
      rw [Nat.add_mul]
      omega
    omega
  have idxLimit : 2 * id.val + dir.toNat < fields s := by
    let n := Slots.RecordCount (s).bases (s).tags (s).lanes (s).oldDegree
      (s).colors (pad s) sub
    change _ < n * 2
    have hi : id.val < n := id.isLt
    have hs : dir.toNat < 2 := by cases dir <;> decide
    omega
  have actual := rect_eval H sub t j dir inverse id.val hp.inverseHead idx (by omega)
  have read := ShrinkSurvivingRect.read_val X ready layout width m t dir j heads mem tables cap
  let v := siteOrdinal (Y) (site X layout m t dir)
  let k := slot X layout sub width (I) m t dir j
  have val : ((H.rect sub t j dir).eval pub state mem).val =
      (2 * v + dir.toNat) * 2 ^ b + k.val := by
    rw [actual]
    have side : dir.toNat = (if dir then 1 else 0) := by cases dir <;> rfl
    rw [side]
    change (mem (inverse + (2 * id.val + (if dir then 1 else 0)))).val = _
    rw [read]
    change v * 2 * 2 ^ b + _ * 2 ^ b + k.val = (2 * v + _) * 2 ^ b + k.val
    ring
  refine (port_eval (H.rect sub t j dir) (2 ^ b) v dir k degreeFit twoFit val).trans ?_
  rw [IncidenceDirectory.actualPort_number]
  exact congrArg (fun n : ℕ ↦ (n : Word w))
    (IncidenceDirectory.actualOrder_val (Y) (site X layout m t dir, k)).symm


section Column

open MotifBlocks MotifGrid MotifConversion Compression.ShrinkMotif

variable {K : Type*} [_root_.Field K] {factor : ℝ}
variable (F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable (sel : X.ShrinkSelection F) (term : Word w) (stride widthBase : ℕ)
local notation "T" => selectedAllocation F X sel term stride widthBase sub
local notation "side" => Allocation.layout (T)
local notation "wid" =>
  fun m t ↦ X.packingData.termWidths F X.shrinkNumber X.packingWidth sel m side t
local notation "slots" => X.shrinkStateIndex ready side
local notation "output" => X.shrinkOutputState side sub (wid) slots
local notation "idx" => ShrinkMotifOrder.stateNumber X m
local notation "bank" => Allocation.row (T) (idx, t)

/-- The per-piece recorded native setup follows from the final level's
absolute-ID, inverse-slot, interval and incidence tables. -/
theorem recorded (K₀ : ShrinkSurvivingColumn.Inputs) (heads : Heads) (absolute : Word w)
    (inc : IncidenceDirectory w) (A : Arena) (node dst layer pitch : ℕ)
    (z : (output).network.Half (site X side m t dir))
    (published : Published X K₀.tables m heads absolute (b := b)
      (pub := pub) (state := state) (mem := mem))
    (directory : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber absolute mem)
    (sorted : Build.OrderedTables X ready side heads mem)
    (absFit : absolute.val + (idx).val < 2 ^ w) (slotFit : finish s heads < 2 ^ w)
    (degreeFit : 2 ^ b < 2 ^ w) (twoFit : 2 < 2 ^ w)
    (allocation : (T).Fits)
    (images : ∀ i, Image ((T).row i)
      (selected X.packingData X.shrinkNumber (Shrink.packedIndex X.baseIndex) (T)
        F X.packingWidth sel i) mem)
    (half : K₀.half.Stored inc A layer pitch pub state mem)
    (columns : inc.ActualColumns (output) mem)
    (capacity : Fintype.card (output).Base * 2 ^ g * 2 ^ b ≤ 2 ^ w)
    (nodeWord : K₀.node.eval pub state mem = (node : Word w))
    (destination : K₀.destination.eval pub state mem = (dst : Word w))
    (interval : K₀.tables.intervalHead.eval pub state mem = ((T).widthEnd : Word w)) :
    (ShrinkSurvivingColumn.row X side sub (wid) slots m t dir z A node dst bank j).Recorded
      (K₀.setup (2 ^ b) sub t dir j) pub state mem := by
  have ord := port_eq X ready side (wid) K₀.tables m t dir j heads absolute published directory
    sorted absFit slotFit degreeFit twoFit
  have image := (selected_inputs X sub m t F sel term stride widthBase mem allocation images).1
  exact ShrinkSurvivingColumn.recorded X side sub (wid) slots m t dir z A node dst bank K₀
    ready.count_pos (T) allocation idx rfl rfl inc layer pitch half columns capacity degreeFit
    nodeWord destination published.dense interval image j ord

end Column

end PairSimulation.ShrinkSurvivingSelected

end VPVNP
end Computability
end OAI
