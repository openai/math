import OAI.ThreeFlat.RAM.TickChunkPredicate
import OAI.ThreeFlat.Diagonal.BucketIntervalCodes
import OAI.ThreeFlat.Diagonal.RotatedBucketScan

namespace OAI
/-! # Physical chunk indicators as chronological group transfers -/

namespace ThreeFlat.RAM.TickChunkTransfer

open TickIntervalCursor TickChunkCheck Diagonal.RotatedChunkGuards Diagonal.TickGroupIntervals
open Diagonal.BucketIntervalCodes Diagonal.HistoryContraction
open scoped Classical

variable {F : Type*} [CommSemiring F]

def codes (scan : Bool) (L : Layout) (es : List Interval) (i : Fin (chunkSize L)) :=
  if scan then codeAt L es i.val else 0

theorem valid_iff_guard (scan : Bool) (L : Layout) (es : List Interval) (op np : ℕ → Bool)
    (x y : Fin (chunkSize L) → Bool) :
    valid scan L es op np x y ↔ Diagonal.RotatedChunkGuards.guard (codes scan L es) op np x y := by
  unfold valid Diagonal.RotatedChunkGuards.guard
  apply forall_congr'
  intro i
  cases scan <;> by_cases h : codeAt L es i.val = 0 <;> simp [codes,h]

/-- The continued native checker multiplies exactly the abstract one-chunk
transfer, allowing arbitrary scheduled computation to follow it. -/
theorem weight (scan : Bool) (L : Layout) (es : List Interval) (op np : ℕ → Bool)
    (x y : Fin (chunkSize L) → Bool) (tail : F) :
    (if valid scan L es op np x y then tail else 0) =
      entry (F:=F) (codes scan L es) op np x y * tail := by
  rw [entry_eq,← valid_iff_guard]
  split <;> simp

/-- Outside the physical scan interval, the direct, allocation-free word
comparison is the identity on the complete chunk, including uncovered bits. -/
theorem preserve {a : ℕ} (op np : ℕ → Bool) (x y : Fin a → Bool) (tail : F) :
    (if x = y then tail else 0) = entry (F:=F) (fun _ => 0) op np x y * tail := by
  rw [zero_entry,Matrix.one_apply]
  split <;> simp

/-- The scan code is zero precisely when no original bucket owned by this
history's terminal group covers the selected physical bit. -/
theorem inactive_iff {S : Shape} (P : Plan F S) (h : P.History)
    (group : (P.finish h).Site → ℕ) (bs : List (Bucket S.Site)) (L : Layout) (i : Fin (chunkSize L)) :
    codes true L ((P.bucketRows h group bs).map interval) i = 0 ↔
    ∀ b ∈ bs, ¬overlaps (group ∘ P.destination h) L.group (L.chunkStart+i.val) b :=
  code_zero_iff _ _ _ _ _

theorem owned {S : Shape} (P : Plan F S) (h : P.History)
    (group : (P.finish h).Site → ℕ) (pre post : List (Bucket S.Site)) (b : Bucket S.Site)
    (L : Layout) (i : Fin (chunkSize L)) (inGroup : group (P.destination h b.site) = L.group)
    (disj : ((P.bucketRows h group (pre++b::post)).map interval).Pairwise Compatible)
    (lo : b.lo ≤ L.chunkStart+i.val) (hi : L.chunkStart+i.val < b.hi) :
    codes true L ((P.bucketRows h group (pre++b::post)).map interval) i =
      1 + BucketRows.count (group ∘ P.destination h) pre L.group + (L.chunkStart+i.val-b.lo) := by
  change pairCode L.group _ (intervals _ _ _) = _
  rw [← inGroup]
  exact code_middle _ _ _ _ _ disj lo hi

def physicalLayout (g a mapBase : ℕ) (k : ℕ) : Layout :=
  ⟨k*a,k*a+a,mapBase,g⟩

@[simp] theorem physical_size (g a base k : ℕ) : chunkSize (physicalLayout g a base k) = a :=
  Nat.add_sub_cancel_left _ _

/-- On the tick selected by the physical clock, the native per-bit code is
the packed-row coordinate used by the complete chronological transfer. -/
theorem code_at_physical_tick {S : Shape} (P : Plan F S) (h : P.History)
    (group : (P.finish h).Site → ℕ) (bs : List (Bucket S.Site))
    (c : Diagonal.TickChronology.Clock) (g a mapBase : ℕ) (j : Fin c.chunks) (i : Fin a) :
    let k := (c.base g+(1+j.val))%c.chunks
    codes true (physicalLayout g a mapBase k) ((P.bucketRows h group bs).map interval)
      (i.cast (physical_size g a mapBase k).symm) =
      Diagonal.RotatedBucketScan.code P h group bs c g a (c.scanOrder g j) i := by
  dsimp only
  exact (Diagonal.RotatedBucketScan.code_at_tick P h group bs c g a j i).symm


end ThreeFlat.RAM.TickChunkTransfer

end OAI
