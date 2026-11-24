import OAI.Computability.VPVNP.CompressorShrinkOutputAccess
import OAI.Computability.VPVNP.CompressorShrinkLevelSpace
import OAI.Computability.VPVNP.CompressorSlotCopiedTables

/-!
# Retaining the inverse endpoint table across canonical copies

The selected allocation fits in a table of the current descriptor level.
The canonical output is in the incidence block of the next level, after
the end of the entire current table. Thus the final six copy passes
preserve both endpoint lookup directions for later descriptor queries.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkOutput

open Compression Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifBlocks MotifGrid MotifConversion Slots SlotLevel ShrinkSlots BurstRAM

variable {a b g w : ℕ} {k : Type*} [_root_.Field k] {factor δ : ℝ}
variable (X : State a (packingLaneBits a g))
variable (F : FixedBlock k demandSource demandTarget Compression.ShrinkMotif.supply
  (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (ready : Ready (2^a) (2*2^a+1) (2^b) δ) (sel : X.ShrinkSelection F)
variable (term : Word w) (stride role retained : ℕ)

local notation "s" => levelShape (b := b) X
local notation "h" => slotHeads (b := b) X term.val stride role retained
local notation "last" => stop (b := b) X term.val stride role retained
local notation "side" => selectedLayout X F sel

/-- The sorted lookup arrays in a separately placed slot workspace are still
present after its canonical destination has been filled. -/
theorem Constructed.retained_after_copy_at (slotStart : ℕ) (gap : (h).role ≤ slotStart)
    (endFit : finish s (heads s role slotStart) < 2^w) {initial out : Memory w} {r : Build.Construction w}
    (c : Constructed X F ready sel term stride role retained initial out r slotStart)
    (hw : FitsWords (b := b) X F term stride role retained)
    (L : DescriptorSpace.Layout) (level : Fin L.levels)
    (room : DescriptorSpace.endAddress L < 2^w) (cap : actualCount s ≤ DescriptorSpace.slotCapacity L) :
    let h₀ := heads s role slotStart
    let Y := X.shrinkNext F ready sel
    let U := DescriptorSpace.packedIncidence L w level (actualCount s)
    let T := directory s h₀ w
    let start := DescriptorSpace.incidenceStart L level
    let m := after out (eventLog r.all)
    let copies := CopyIncidence.reports Y T U CopyIncidence.allColumns m
    (finish s h₀ ≤ start ∨ start+6*actualCount s ≤ rowsHead s h₀) →
      Build.OrderedTables X ready side h₀ (after out (eventLog (r.all++copies))) := by
  intro h₀ Y U T start m copies apart
  exact Build.retained_after_copy X F ready sel h₀ out r L level room endFit cap
    (c.retained_tables_at X F ready sel term stride role retained slotStart gap endFit hw) apart

/-- Retention on the actual report memory at the end of all 22 stages. -/
theorem Constructed.retained_after_copy {initial out : Memory w} {r : Build.Construction w}
    (c : Constructed X F ready sel term stride role retained initial out r)
    (hw : FitsWords (b := b) X F term stride role retained)
    (L : DescriptorSpace.Layout) (level : Fin L.levels)
    (room : DescriptorSpace.endAddress L < 2^w) (cap : actualCount s ≤ DescriptorSpace.slotCapacity L) :
    let Y := X.shrinkNext F ready sel
    let U := DescriptorSpace.packedIncidence L w level (actualCount s)
    let T := directory s h w
    let start := DescriptorSpace.incidenceStart L level
    let m := after out (eventLog r.all)
    let copies := CopyIncidence.reports Y T U CopyIncidence.allColumns m
    (last ≤ start ∨ start+6*actualCount s ≤ rowsHead s h) →
      Build.OrderedTables X ready side h (after out (eventLog (r.all++copies))) :=
  c.retained_after_copy_at X F ready sel term stride role retained (h).role le_rfl hw.room hw L level room cap

/-- The canonical following-level destination comes after every retained slot
array when the current table uses the uniform shrinking capacity. -/
theorem packed_before_next (S : BlockSchedule k) (i : Fin S.steps) {g w : ℕ}
    (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (L : DescriptorSpace.Layout) (current next : Fin L.levels) (table : Fin L.shape.tables)
    (later : current < next) (sites : X.positions ≤ L.positions)
    (capacity : ShrinkLevelSpace.tableFactor S ≤ L.shape.slots*L.shape.fields) :
    let start := DescriptorSpace.tableBase L current table
    let term := ShrinkInput.termHead (w := w) X start
    let stride := Fin.ofNat (2^w) 10
    let role := SelectedArena.roleBase X term stride
    let retained := SelectedFinish.stop X term stride
    stop (b := S.degreeExponent i.succ) X term.val stride.val role retained ≤
      DescriptorSpace.incidenceStart L next := by
  intro start term stride role retained
  have slot := (ShrinkLevelSpace.packed_ends S i X start start start start w).2.2.2.1
  have fit : X.positions*ShrinkLevelSpace.tableFactor S ≤ DescriptorSpace.tableWords L := by
    change _ ≤ L.positions*L.shape.slots*L.shape.fields
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul sites capacity
  exact slot.trans ((Nat.add_le_add_left fit start).trans ((DescriptorSpace.tableEnd_le_nextLevel L current table).trans
    ((DescriptorSpace.levelStart_mono L (show current.val+1 ≤ next.val from later)).trans (Nat.le_add_right _ _))))

/-- The same separation holds when the slot scratch is a separate table in
the current level, as in the fixed block planner's slot-arena expression. -/
theorem separate_before_next (S : BlockSchedule k) (i : Fin S.steps) {g : ℕ}
    (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
    (L : DescriptorSpace.Layout) (current next : Fin L.levels) (table : Fin L.shape.tables)
    (role : ℕ) (later : current < next) (sites : X.positions ≤ L.positions)
    (capacity : ShrinkLevelSpace.tableFactor S ≤ L.shape.slots*L.shape.fields) :
    let sh := levelShape (b := S.degreeExponent i.succ) X
    let start := DescriptorSpace.tableBase L current table
    finish sh (heads sh role start) ≤ DescriptorSpace.incidenceStart L next := by
  intro sh start
  have rate : ShrinkLevelSpace.slotRate (S.degreeExponent i.castSucc) (S.degreeExponent i.succ) ≤
      ShrinkLevelSpace.tableFactor S := by
    apply le_trans _ (ShrinkLevelSpace.levelRate_le_tableFactor S i)
    unfold ShrinkLevelSpace.levelRate; omega
  have fit : X.positions*ShrinkLevelSpace.slotRate (S.degreeExponent i.castSucc) (S.degreeExponent i.succ) ≤
      DescriptorSpace.tableWords L := by
    change _ ≤ L.positions*L.shape.slots*L.shape.fields
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul sites (rate.trans capacity)
  exact (ShrinkLevelSpace.slot_end (b := S.degreeExponent i.succ) X role start).trans
    ((Nat.add_le_add_left fit start).trans ((DescriptorSpace.tableEnd_le_nextLevel L current table).trans
      ((DescriptorSpace.levelStart_mono L (show current.val+1 ≤ next.val from later)).trans (Nat.le_add_right _ _))))

end CompressorRecords.ShrinkOutput

end VPVNP
end Computability
end OAI
