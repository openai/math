import OAI.Computability.VPVNP.CompressorSlotSelectedAccess

/-! # Persistence of sorted endpoint records in a distinct descriptor level

The canonical incidence copies write within the six live destination columns.
A distinct allocation retains every source and inverse endpoint record.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlots.Build

open Compression Compression.PackingData Compression.ShrinkMotif Compression.ShrinkEnergy
open MotifBlocks MotifGrid MotifConversion Slots SlotLevel BurstRAM

variable {a b g w : ℕ} {k : Type*} [_root_.Field k] {factor δ : ℝ}
variable (X : State a (packingLaneBits a g))
variable (F : FixedBlock k demandSource demandTarget Compression.ShrinkMotif.supply
  (realWidths demandMass) (realWidths supplyMass) (31/16) factor)
variable (ready : Ready (2^a) (2*2^a+1) (2^b) δ) (sel : X.ShrinkSelection F)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _

set_option maxHeartbeats 1000000 in
/-- Any fitting slot workspace retains its rectangular lookup tables after the
six native incidence copies if their destination avoids those two tables. -/
theorem retained_after_copy (h : Heads) (out : Memory w) (r : Construction w) (L : DescriptorSpace.Layout)
    (level : Fin L.levels) (room : DescriptorSpace.endAddress L < 2^w) :
    let s := levelShape (b := b) X
    let side := selectedLayout X F sel
    let Y := X.shrinkNext F ready sel
    let U := DescriptorSpace.packedIncidence L w level (actualCount s)
    let T := directory s h w
    let start := DescriptorSpace.incidenceStart L level
    let m := after out (eventLog r.all)
    let copies := CopyIncidence.reports Y T U CopyIncidence.allColumns m
    finish s h < 2^w → actualCount s ≤ DescriptorSpace.slotCapacity L →
    OrderedTables X ready side h (r.final out) →
    (finish s h ≤ start ∨ start+6*actualCount s ≤ rowsHead s h) →
      OrderedTables X ready side h (after out (eventLog (r.all++copies))) := by
  intro s side Y U T start m copies fit cap sorted apart
  have hm : m = r.final out := (r.final_eq out).symm
  have hb := next_counts X F ready sel
  have source := CopyIncidence.shrink_column_bounds Y s h hb.1 hb.2 fit
  have dest := CopyIncidence.packed_column_bounds Y s L level hb.2 room cap
  have live := DescriptorSpace.packed_incidence_room L room level cap
  have copied := CopyIncidence.reports_run Y T U CopyIncidence.allColumns m
  have writes := (copied.footprint (fun c ↦ (source c).2.trans fit.le)
    (fun c ↦ (dest c).2.trans live.le)).2
  have finish : targetsHead s h ≤ ShrinkSlots.finish s h := by
    unfold ShrinkSlots.finish widthHead inHead outHead inverseBaseHead stopAddress shiftsHead; omega
  have keep (x) (first : rowsHead s h ≤ x) (end_ : x < targetsHead s h) :
      after out (eventLog (r.all++copies)) x = r.final out x := by
    have empty : ¬ CopyIncidence.ColumnCell Y U x := by
      rintro ⟨i,hi⟩
      have hd : (U.column i).val=start+i.val*actualCount s ∧
        (U.column i).val+CopyIncidence.rows Y i ≤ start+6*actualCount s := dest i
      omega
    have eq : after m (eventLog copies) x = r.final out x :=
      (SourceTransport.after_outside m writes empty).trans (congrFun hm x)
    simpa only [m,eventLog,List.flatMap_append,after,List.foldl_append] using eq
  let tags := bitWordFinEquiv (packingTagBits (2^a))
  let lanes := bitWordFinEquiv g
  let D := SlotSchedule.slotDirectory X.packingData (s).subdivisions X.baseIndex tags lanes side (pad := pad s)
  let degree := fun v ↦ (SlotSchedule.slotDirectory_degree X.packingData (s).subdivisions X.baseIndex tags lanes
    (State.two_le_packingColors a) side v).trans (Nat.add_sub_of_le ready.degree_budget)
  have rect : rowsHead s h+owners s*(s).newDegree ≤ inverseHead s h :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) _
  have extent : inverseHead s h+fields s=targetsHead s h := rfl
  constructor
  · intro e
    have hi : (SlotSchedule.sortedFields D (2^b) degree e).val < owners s*(s).newDegree :=
      (SlotSchedule.sortedFields D (2^b) degree e).isLt
    exact (keep (rowsHead s h+(SlotSchedule.sortedFields D (2^b) degree e).val) (by omega) (by omega)).trans (sorted.bySlot e)
  · intro e
    have hi : (D.address e).val < fields s := (D.address e).isLt
    exact (keep (inverseHead s h+(D.address e).val) (by omega) (by omega)).trans (sorted.byField e)

end CompressorRecords.ShrinkSlots.Build

end VPVNP
end Computability
end OAI
