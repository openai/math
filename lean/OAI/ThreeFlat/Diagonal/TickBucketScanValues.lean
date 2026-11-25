import OAI.ThreeFlat.Diagonal.TickInstalledTeam
import OAI.ThreeFlat.Diagonal.TickBucketChronology
import OAI.ThreeFlat.Diagonal.BucketFiniteLabels

namespace OAI
/-! # Per-tick group checks from the finite RAM rows and old proposal bits -/

noncomputable section
namespace ThreeFlat.Diagonal.TickPhaseModel.Buckets

open HistoryContraction TickChronology TickAuxiliary PackedChunkTransfer RotatedChunkGuards
open RAM.TickActiveROM RAM.Contraction RAM.BitLayout RAM
open scoped Classical BigOperators
variable {F : Type*} [Field F] [Fintype F] {S : Shape} {P : Plan F S} {E : P.Codes} {bits : P.History → ℕ}
  {A : RAM.TickActiveROM.Layout} {c : Clock} {R : GroupRegister P E bits A.bits} {lanes span p H J w : ℕ}
  {fit : Fits (TickWeightedBank.shape F p H J) w} (T : Buckets P bits c A.bits lanes span)

def finiteRows (v : Plan.Terminal P bits) :=
  (P.bucketRows v.1 (T.group v.1) T.rows).map BucketFiniteLabels.decode

omit [Fintype F] in
theorem finite_values (v : Plan.Terminal P bits) :
    T.finiteRows v=BucketIntervalCodes.intervals (T.home v.1) (fun _=>0) T.rows :=
  BucketFiniteLabels.canonical _ _

omit [Fintype F] in
theorem bounded_codes (v : Plan.Terminal P bits) (g : ℕ) (k : Fin c.chunks) (i : Fin A.bits) :
    T.code v g k i ≤ T.length v g := PackedBucketBijection.pairCode_le_count ..

/-- The navigator may keep arbitrary values beyond the active pair count. Only
the original bucket row owning this external pin can read from the group. -/
theorem physical_guard (room : ∀ v g,1+R.capacity+2*T.length v g≤A.bits)
    (weights : ∀ v g, Aux (T.length v g) → Aux (T.length v g) → ℕ → F)
    (t : ℕ) (x : CellInput A c fit) (v : Plan.Terminal P bits) (oa oc nc : Aux A.bits)
    (rows_eq : x.intervals = T.finiteRows v) (grp : x.group=c.group t)
    (lo : x.lo = (chunk c t).val*A.bits)
    (op : ∀ i : Fin (T.length v (c.group t)), x.before i.val = before (T.data room weights) v (c.group t) oa i)
    (np : ∀ i : Fin (T.length v (c.group t)), x.after i.val = after (T.data room weights) v (c.group t) oa i) :
    TickChunkCheck.valid true (TickGroupScanBank.layout A.scan x.lo x.group) x.intervals x.before x.after
      (chunkView A x.lo x.group oc) (chunkView A x.lo x.group nc) ↔
      guard (T.code v (c.group t) (chunk c t)) (atIndex (before (T.data room weights) v (c.group t) oa))
        (atIndex (after (T.data room weights) v (c.group t) oa)) oc nc := by
  apply scan_agrees_on_count (T.data room weights) t x v oa oc nc _ (T.bounded_codes v _ _) op np
  intro i
  simp only [TickChunkCheck.codeAt,TickGroupScanBank.layout,rows_eq,T.finite_values,grp,lo]
  rfl

theorem auxiliary (room : ∀ v g,1+R.capacity+2*T.length v g≤A.bits)
    (weights : ∀ v g, Aux (T.length v g) → Aux (T.length v g) → ℕ → F)
    (v : Plan.Terminal P bits) (g : ℕ) (x : CellInput A c fit)
    (reserve : A.capacity=R.capacity) (count : x.count=T.length v g) :
    x.aux=layout (T.data room weights) v g := by
  have sameLayout {a : ℕ} (left right : TickAuxiliary.Layout a)
      (hw : left.wiresEnd=right.wiresEnd) (hp : left.pairsEnd=right.pairsEnd) : left=right := by
    cases left
    cases right
    dsimp only at hw hp
    subst_vars
    rfl
  apply sameLayout
  · change 1+A.capacity=1+R.capacity
    rw [reserve]
  · change 1+A.capacity+2*x.count=1+R.capacity+2*T.length v g
    rw [reserve,count]


end ThreeFlat.Diagonal.TickPhaseModel.Buckets

end
end OAI
