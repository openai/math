import OAI.Computability.VPVNP.PairShrinkInputRetention
import OAI.Computability.VPVNP.CompressorShrinkResidentFinal
import OAI.Computability.VPVNP.CompressorShrinkReadbackTransfer
import OAI.Computability.VPVNP.CompressorShrinkSlotRetention
import OAI.Computability.VPVNP.CompressorSelectedPayloadHistory
import OAI.Computability.VPVNP.CompressorBlockProgram
import OAI.Computability.VPVNP.CompressorCurrentGraph
import OAI.Computability.VPVNP.PairShrinkPhysicalSourceBounds
import OAI.Computability.VPVNP.PairShrinkResidentTermCapture
import OAI.Computability.VPVNP.CompressorShrinkSliceInterval

/-!
# Source records of a selected shrinking level

The input incidence, old-port lists, sorted ranks, dense demand pairs, term
words, resident directories, slice banks and ordered-slot rectangles occupy
the producing level. The copied successor incidence occupies its own
canonical bank. All components here describe one selected branch at one
chronological level and one memory snapshot.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkResidentSources

open BurstRAM Compression CompressorRecords CompressorRecords.DescriptorSpace
open CompressorRecords.ShrinkBlockInputs Compression.ShrinkMotif ShrinkSlots
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} {δ : ℝ} (X : State (a i) (packingLaneBits (a i) g))
variable (ready : Ready (2 ^ a i) (Shrink.colors (a i)) (2 ^ b i) δ)
variable (sel : SelectedScore.Selection B X) (base : Word w) (positions blocks cur : ℕ)

private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

local notation "lay" => BlockProgram.layout B base.val positions blocks
local notation "cut" => tableBase lay cur (0 : Fin 6)
local notation "first" => tableBase lay cur (1 : Fin 6)
local notation "width" => tableBase lay cur (2 : Fin 6)
local notation "slots" => tableBase lay cur (3 : Fin 6)
local notation "resident" => tableBase lay cur (5 : Fin 6)
local notation "term" => ShrinkInput.termHead (w := w) X cut
local notation "dense" => ShrinkInput.demandHead (w := w) X cut
local notation "absHead" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X cut) w
local notation "side" => SelectedFinish.chosen B X sel
local notation "shape" => levelShape (b := b i) X
local notation "heads" => ShrinkOutput.heads shape (SelectedArena.roleBase X term 10) slots
local notation "sourceInc" => packedIncidence lay w cur (DemandRAM.oldCount X)
local notation "nextInc" => packedIncidence lay w (cur + 1) (actualCount shape)

/-- Typed data consumed by resident-party handlers after the native
shrinking pass and its successor-incidence copy. -/
structure Data (mem : Memory w) : Prop where
  old : ShrinkCallHeader.OldTables X mem sourceInc cut
  pairs : ShrinkTermInputs.statePairs X dense mem
  terms : ∀ m, TermRecordScan.Fields B.shrink ShrinkSliceArrays.supplyRoles
    demandMass_pos
    (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth m) (sel m).val
    (ShrinkTermSelection.rowBase X term 10 m) mem
  residents : ∀ maps, ShrinkHistoryRows.Directory (ShrinkResidentDirectory.oldOrder X maps)
    (ShrinkHistoryRows.packedOrder X) (ShrinkResidentDirectory.place X maps side)
    (ShrinkResidentRun.outputBank X resident maps) mem
  absolute : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber absHead mem
  slices : ShrinkOutput.SliceReadbacks B i X sel term 10 first width mem
  sorted : Build.OrderedTables X ready side heads mem
  successor : (nextInc).ActualColumns (X.shrinkNext B.shrink ready sel) mem

variable {B i X ready sel base positions blocks cur}
variable {before out : Memory w}

private theorem table_range (L : Layout) (level : ℕ) (t : Fin L.shape.tables) :
    levelStart L level ≤ tableBase L level t ∧ tableBase L level t ≤ levelStart L (level + 1) :=
  ⟨((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..),
    (Nat.le_add_right ..).trans (tableEnd_le_nextLevel L level t)⟩

private theorem successor_actual
    (bounds : Bounds B i X base positions blocks cur)
    (data : (nextInc).ActualColumns (X.shrinkNext B.shrink ready sel) before)
    (agree : SourceTransport.Agree (SelectedPayloadHistory.Cells lay cur) before out) :
    (nextInc).ActualColumns (X.shrinkNext B.shrink ready sel) out := by
  let Y := X.shrinkNext B.shrink ready sel
  let j : Fin (lay).levels := ⟨cur + 1, bounds.nextLive⟩
  have total : IncidenceDirectory.slotCount Y = actualCount shape :=
    (next_counts X B.shrink ready sel).2
  have read (c : Fin 6) (e : (Y.Base × BitWord g) × Fin (2 ^ b i)) :
      out ((nextInc).column c + IncidenceDirectory.actualPort Y e).val =
        before ((nextInc).column c + IncidenceDirectory.actualPort Y e).val := by
    have hi := (IncidenceDirectory.actualPort_lt Y e (w := w)).trans_eq total
    have range := CurrentGraph.column_range lay j _ bounds.nextCapacity bounds.room c _ hi
    apply (agree _ (.inr ⟨?_, range.2⟩)).symm
    apply le_trans _ range.1
    change levelStart lay (cur + 1) + 54 ≤ levelStart lay (cur + 1) + 66
    omega
  exact ⟨fun e ↦ (read 3 e).trans (data.actualOut e),
    fun e ↦ (read 4 e).trans (data.actualIn e), fun e ↦ (read 5 e).trans (data.width e)⟩

private theorem absolute_transfer (bounds : Bounds B i X base positions blocks cur)
    (stored : MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber absHead before)
    (keep : ∀ x, cut ≤ x → x < first → out x = before x) :
    MotifAbsolute.Directory X.slots X.baseIndex X.shrinkNumber absHead out := by
  let Z := ShrinkInput.plan X cut
  have ranges := ShrinkInput.range_bounds X cut
  have room : ShrinkInput.stop X cut < 2 ^ w := by
    have tr := bounds.termRoom
    unfold ShrinkInput.termEnd at tr
    omega
  have fit := ranges.2.2.2.trans_lt room
  have rankBefore : Z.ranks ≤ ShrinkInput.widthBase X cut := Nat.le_add_right ..
  have eqn : Z.gathered + Z.B * Z.Q + Z.B * Z.Q = Z.ranks := by
    change _ = Z.gathered + (2 * Z.B) * Z.Q
    ring
  have raw : (absHead).val = Z.gathered + Z.B * Z.Q :=
    Nat.mod_eq_of_lt (show Z.gathered + Z.B * Z.Q < 2 ^ w by omega)
  have below : cut ≤ Z.gathered := by
    have lower := ranges.1.trans ranges.2.1
    change cut ≤ ShrinkInput.rankBase X cut + 2 * Z.A + 2 * Z.B + Z.rectangleSize
    omega
  intro j
  have hj : j.val < Z.B * Z.Q := j.isLt
  have upper := ranges.2.2.2.trans bounds.fresh
  rw [keep _ (by rw [raw]; omega) (by rw [raw]; omega)]
  exact stored j

/-- Transfer all typed inputs to the memory of a later parser call. Only
the producing level and the successor's pointer and incidence bank are
used, so writes to its scalar header and workspace are allowed. -/
theorem Data.transfer (d : Data B i X ready sel base positions blocks cur before)
    (bounds : Bounds B i X base positions blocks cur)
    (agree : SourceTransport.Agree (SelectedPayloadHistory.Cells lay cur) before out) :
    Data B i X ready sel base positions blocks cur out := by
  let next := levelStart lay (cur + 1)
  have keep (x : ℕ) (low : levelStart lay cur ≤ x) (high : x < next) : out x = before x :=
    (agree x (.inl ⟨low, high⟩)).symm
  have fit : next < 2 ^ w := (levelStart_mono lay bounds.nextLive.le).trans_lt bounds.room
  have header : levelStart lay cur + 66 ≤ next := by
    change levelsBase lay + cur * levelWords lay + 66 ≤ levelsBase lay + (cur + 1) * levelWords lay
    rw [Nat.succ_mul]
    have hw : 66 ≤ levelWords lay := by
      change 66 ≤ 66 + 6 * slotCapacity lay + 6 * tableWords lay
      omega
    omega
  have step : (10 : Word w).val = 10 := Nat.mod_eq_of_lt (show 10 < 2 ^ w by omega)
  have interval (x : ℕ) (lo : cut ≤ x) (hi : x < first) : out x = before x :=
    keep x ((table_range lay cur (0 : Fin 6)).1.trans lo)
      (hi.trans_le (table_range lay cur (1 : Fin 6)).2)
  have src := bounds.oldTables d.old fun x lo hi ↦
    keep x ((Nat.le_add_right ..).trans lo) (hi.trans_le (table_range lay cur (1 : Fin 6)).2)
  have denseRoom : ShrinkInput.stop X cut < 2 ^ w := by
    have tr := bounds.termRoom
    unfold ShrinkInput.termEnd at tr
    omega
  have cutBefore := ShrinkInput.range_bounds X cut
  have low : cut ≤ (dense).val := by
    change cut ≤ ShrinkInput.stop X cut % 2 ^ w
    rw [Nat.mod_eq_of_lt denseRoom]
    exact cutBefore.1.trans (cutBefore.2.1.trans (cutBefore.2.2.1.trans cutBefore.2.2.2))
  obtain ⟨pairs, terms⟩ := ShrinkTermInputs.capture_transfer B X cut 10 bounds.termRoom le_rfl
    d.pairs d.terms (fun x lo hi ↦ interval x (low.trans lo) (hi.trans_le bounds.termBefore))
  constructor
  · exact src
  · exact pairs
  · exact terms
  · intro maps
    exact ShrinkResidentRun.transfer X resident side maps (d.residents maps)
      (bounds.residentEnd.trans_lt fit) (fun x lo hi ↦
        keep x ((table_range lay cur (5 : Fin 6)).1.trans lo) (hi.trans_le bounds.residentEnd))
  · exact absolute_transfer bounds d.absolute interval
  · exact d.slices.transfer_interval (T := sourceInc) ready (step.symm ▸ bounds.termRoom)
      bounds.fresh bounds.widthAfter bounds.slotAfter
      ((table_range lay cur (3 : Fin 6)).2.trans_lt fit) step.ge bounds.packedRoom
      (fun x lo hi ↦ keep x ((table_range lay cur (1 : Fin 6)).1.trans lo)
        (hi.trans_le (table_range lay cur (3 : Fin 6)).2))
  · exact d.sorted.transfer_interval fun x lo hi ↦
      keep x ((table_range lay cur (3 : Fin 6)).1.trans lo) (hi.trans_le bounds.slotEnd)
  · exact successor_actual bounds d.successor agree

end PairSimulation.ShrinkResidentSources

end VPVNP
end Computability
end OAI
