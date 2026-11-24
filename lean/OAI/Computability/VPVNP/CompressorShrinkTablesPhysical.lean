import OAI.Computability.VPVNP.CompressorBlockCapacity
import OAI.Computability.VPVNP.CompressorRecordsShrinkBuild
import OAI.Computability.VPVNP.CompressorShrinkFieldCapacity
import OAI.Computability.VPVNP.CompressorShrinkAllocatedTables
import OAI.Computability.VPVNP.CompressorShrinkHeaderReads

/-! # Allocated tables for the AB, surviving-width and ordered-slot passes

At a live shrinking level the selected rows end in table zero. The interval
records and widths fit in the following two tables, and the native slot passes
end in table three. The calendar reads their starting addresses from the same
published header as the prefix. Scalar bounds hold uniformly on the selected
states once the input length reaches the word-capacity threshold.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkOutput

open BurstRAM Compression BlockPlanner DescriptorSpace ShrinkBlockInputs Schedule
open ShrinkSliceSweep CursorBounds Filter
open scoped Fin.CommRing
open private absolute_room from OAI.Computability.VPVNP.CompressorRecordsShrinkBuild

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g))
variable (base : Word w) (positions blocks round : ℕ)

local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "ports" => Workspace.ports (arity (Script.catalog (BlockProgram.script B))) base
local notation "pub" => Ports.data ports
local notation "blockStart" => (S.steps+1)*round
local notation "cur" => blockStart+i.val
local notation "st" => (levelStart L blockStart : Word w)
local notation "cut" => tableBase L cur (0 : Fin 6)
local notation "first" => tableBase L cur (1 : Fin 6)
local notation "width" => tableBase L cur (2 : Fin 6)
local notation "slots" => tableBase L cur (3 : Fin 6)
local notation "term" => ShrinkInput.termHead (w := w) X cut
local notation "step" => (10 : Word w)
local notation "ids" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X cut) w
local notation "role" => SelectedArena.roleBase X term step
local notation "keepEnd" => SelectedFinish.stop X term step
local notation "sh" => ShrinkSlots.levelShape (b := b i) X
local notation "abInputs" => BlockSlices.abInputs i (BlockProgram.arena B i.val 0) (BlockProgram.arena B i.val 1)
local notation "nt" => ShrinkBundlePlan.cap (a i)
local notation "ns" => ShrinkBundlePlan.thickCount (a i)

/-- The address bounds used by all three workers and by the preceding hidden-map frame. -/
structure TableSpace : Prop where
  termRoom : ShrinkInput.termEnd X cut 10 < 2^w
  fresh : ShrinkInput.stop X cut ≤ first
  selectedWithin : keepEnd ≤ cut+tableWords L
  abAfter : keepEnd ≤ first
  widthAfter : first+(ShrinkInput.plan X cut).B*IndexedStarts.capacity ns nt ≤ width
  slotAfter : slotsBase X (widthBase X (term).val (step).val role width) sh ≤ slots
  slotRoom : ShrinkSlots.finish sh (heads sh role slots) < 2^w
  packedRoom : stop (b := b i) X (term).val (step).val role width < 2^w

private theorem finish_mono (s : SlotLevel.Shape) (r : ℕ) {u v : ℕ} (h : u ≤ v) :
    ShrinkSlots.finish s (heads s r u) ≤ ShrinkSlots.finish s (heads s r v) := by
  unfold ShrinkSlots.finish ShrinkSlots.widthHead ShrinkSlots.inHead ShrinkSlots.outHead
    ShrinkSlots.inverseBaseHead SlotLevel.stopAddress SlotLevel.shiftsHead SlotLevel.targetsHead
    SlotLevel.inverseHead SlotLevel.rowsHead heads
  dsimp only
  omega

set_option maxHeartbeats 1200000 in
/-- Specialize the compiled block endpoints to the three separately allocated tables. -/
theorem table_space (live : round < blocks) (sites : X.positions ≤ positions)
    (room : endAddress L < 2^w) : TableSpace B i X base positions blocks round := by
  have active : cur < (L).levels := by
    change (S.steps+1)*round+i.val < 1+(S.steps+1)*blocks
    have h := Nat.mul_le_mul_left (S.steps+1) live
    rw [Nat.mul_succ] at h
    have hi := i.isLt
    omega
  let level : Fin (L).levels := ⟨cur,active⟩
  have amount : X.positions*ShrinkLevelSpace.tableFactor S ≤ tableWords L := by
    change _ ≤ positions*(L).shape.slots*(L).shape.fields
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul sites (BlockProgram.field_rates B base.val positions blocks).1
  obtain ⟨h₀,h₁,h₂,_,h₄,h₅,h₆⟩ := ShrinkLevelSpace.packed_ends S i X cut first width slots w
  have within (u : ℕ) := Nat.add_le_add_left amount u
  have end₀ := tableStop_lt L level (0 : Fin 6) amount room
  have end₃ := tableStop_lt L level (3 : Fin 6) amount room
  have firstAfter := tableEnd_le_tableBase L cur (show (0 : Fin 6) < 1 by decide)
  have secondAfter := tableEnd_le_tableBase L cur (show (1 : Fin 6) < 2 by decide)
  have thirdAfter := tableEnd_le_tableBase L cur (show (2 : Fin 6) < 3 by decide)
  have keep : keepEnd ≤ first := h₂.trans ((within cut).trans firstAfter)
  have abLast : first+(ShrinkInput.plan X cut).B*IndexedStarts.capacity ns nt ≤ width := h₄.trans ((within first).trans secondAfter)
  have exactBase := width_at_eq i X term step width (keep.trans ((Nat.le_add_right first _).trans abLast))
  have slotStart : slotsBase X (widthBase X (term).val (step).val role width) sh ≤ slots := by
    rw [exactBase]
    exact h₅.trans ((within width).trans thirdAfter)
  have slotRoom := h₆.trans_lt end₃
  exact ⟨h₁.trans_lt end₀,h₀.trans ((within cut).trans firstAfter),h₂.trans (within cut),
    keep,abLast,slotStart,slotRoom,(finish_mono sh role slotStart).trans_lt slotRoom⟩

/-- Uniform arithmetic capacity for the surviving and AB workers. The address
argument of `fields` is discharged by `table_space` after allocating the level. -/
structure TableArithmetic (w : ℕ) : Prop where
  widthRoom : nt*X.maxWireWidth < 2^w
  fields : ∀ (rowBase : Word w) (stride roles floor : ℕ),
    stop (b := b i) X rowBase.val stride roles floor < 2^w →
      FitsWords (b := b i) X B.shrink rowBase stride roles floor

theorem eventually_tableArithmetic (d : ℕ) (hd : 1 ≤ d) : ∀ᶠ n : ℕ in atTop,
    ∀ (i : Fin S.steps) {g : ℕ} (X : State (a i) (packingLaneBits (a i) g)),
      X.positions ≤ initialPositions d n → X.maxWireWidth ≤ n → TableArithmetic B i X (wordBits d n) := by
  let q := Finset.univ.sup fun j : Fin S.steps => ShrinkBundlePlan.cap (a j)
  filter_upwards [eventually_fitsWords B d hd,
    CursorRAM.eventual_word_room d hd ((PolynomiallyBounded.const q).mul PolynomiallyBounded.id)] with n fields product
  intro i g X sites wire
  have bound : ShrinkBundlePlan.cap (a i) ≤ q := Finset.le_sup
    (f := fun j : Fin S.steps => ShrinkBundlePlan.cap (a j)) (Finset.mem_univ i)
  exact ⟨(Nat.mul_le_mul bound wire).trans_lt product, fields i X sites wire⟩

set_option maxHeartbeats 1600000 in
/-- The post-hidden memory drives the actual three-table workers. The AB operand
readbacks refer to that memory and therefore also describe its source trace. -/
theorem withAB_physical (inc : IncidenceDirectory w) (mem : Memory w) {δ : ℝ}
    (ready : ShrinkMotif.Ready (2^(a i)) (Shrink.colors (a i)) (2^(b i)) δ)
    (sel : SelectedScore.Selection B X) (live : round < blocks) (sites : X.positions ≤ positions)
    (room : endAddress L < 2^w) (arithmetic : TableArithmetic B i X w)
    (header : ShrinkHeaderReads.Header i X inc cut L blockStart mem)
    (pitch : mem ((ports).directory-1).val = (levelWords L : Word w))
    (abHead : mem (tableHead L cur (1 : Fin 6)) = (first : Word w))
    (resident : Resident B i X sel term step ids inc cut width mem)
    (cap : ℕ) (abFuel : 95 ≤ cap) (sweepFuel : SurvivingNative.ops.length < cap) :
    ∃ r, CompleteTables B i X ready sel term step ids cut abInputs pub st mem first width slots cap mem r ∧
      ShrinkABSliceRecipe.Describes abInputs pub st mem (ShrinkInput.thickBank X inc cut)
        (ShrinkInput.piecesBank X inc cut) (ShrinkInput.plan X cut).B first := by
  have h := table_space B i X base positions blocks round live sites room
  have ten : 10 < 2^w := by have hh := header.room; omega
  have stepVal : (step).val = 10 := Nat.mod_eq_of_lt ten
  have tr : ShrinkInput.termEnd X cut (step).val < 2^w := stepVal ▸ h.termRoom
  have entry : LevelFields.Entry L blockStart pub st mem := ⟨rfl,pitch⟩
  have level := header.reads B entry
  have headFit : tableHead L cur (1 : Fin 6) < 2^w := by
    have below : tableHead L cur (1 : Fin 6) < cut := by
      change levelStart L cur+54+6+1 < levelStart L cur+66+_+_; omega
    obtain ⟨g₀,g₁,g₂,g₃⟩ := ShrinkInput.range_bounds X cut
    have tr₀ := h.termRoom
    unfold ShrinkInput.termEnd at tr₀
    omega
  let : Nontrivial (Word w) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have arena := (LevelFields.eval_table entry i.val (1 : Fin 6) headFit).trans abHead
  have hw := arithmetic.fields term (step).val role width h.packedRoom
  obtain ⟨r,run⟩ := withAB B i X ready sel term step ids inc cut first width slots cap mem level arena tr h.fresh
    arithmetic.widthRoom h.abAfter h.widthAfter h.slotAfter h.slotRoom stepVal.ge hw
    (absolute_room X cut step tr) resident abFuel sweepFuel
  have rankFit : (ShrinkInput.plan X cut).stop < 2^w := by
    change ShrinkInput.widthBase X cut < _
    change ShrinkInput.widthBase X cut+_+_+_+_ < _ at tr
    omega
  exact ⟨r,run,BlockSlices.ab_describes i X inc cut level rankFit arena⟩

end CompressorRecords.ShrinkOutput

end

end VPVNP
end Computability
end OAI
