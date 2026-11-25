import OAI.ThreeFlat.Diagonal.RotatedChunkGuards
import OAI.ThreeFlat.Diagonal.BucketIntervalCodes

namespace OAI
/-! # The chronological scan of actual history-owned external intervals -/

namespace ThreeFlat.Diagonal.RotatedBucketScan

open TickChronology RotatedChunkGuards TickGroupIntervals BucketIntervalCodes HistoryContraction
open scoped Classical

variable {F : Type*} [CommSemiring F] {S : Shape}

theorem descriptor_count (P : Plan F S) (h : P.History) (group : (P.finish h).Site → ℕ)
    (bs : List (Bucket S.Site)) :
    ((P.bucketRows h group bs).map interval).length = bs.length := by
  simp only [List.length_map,Plan.bucketRows,BucketRows.pack_length]

/-- Chunk-major indexing maps each visited bit to its physical offset. -/
def code (P : Plan F S) (h : P.History) (group : (P.finish h).Site → ℕ) (bs : List (Bucket S.Site))
    (c : Clock) (g a : ℕ) (i : Fin c.chunks) (j : Fin a) : ℕ :=
  pairCode g (i.val*a+j.val) ((P.bucketRows h group bs).map interval)

/-- The true clock value determines which external bits the local transition
tests, including the wrap at the boundary between the last and first chunk. -/
theorem code_at_tick (P : Plan F S) (h : P.History) (group : (P.finish h).Site → ℕ)
    (bs : List (Bucket S.Site)) (c : Clock) (g a : ℕ) (j : Fin c.chunks) (i : Fin a) :
    code P h group bs c g a (c.scanOrder g j) i =
      pairCode g (((c.base g+(1+j.val))%c.chunks)*a+i.val) ((P.bucketRows h group bs).map interval) := by
  simp only [code,Clock.scanOrder_val]

/-- The concrete canonical group rows supply exactly the single shared pair
lookup used throughout the reserved chronological interval. -/
theorem full_scan (P : Plan F S) (h : P.History) (group : (P.finish h).Site → ℕ)
    (bs : List (Bucket S.Site)) (c : Clock) (g a : ℕ) (op np : ℕ → Bool)
    (old new : Fin c.chunks → Fin a → Bool) :
    (((order c g).map fun i => chunkKernel (fun j => entry (F:=F) (code P h group bs c g a j) op np)
      {i}).prod) old new = if ∀ i, guard (code P h group bs c g a i) op np (old i) (new i) then 1 else 0 :=
  complete c g (code P h group bs c g a) op np old new


end ThreeFlat.Diagonal.RotatedBucketScan

end OAI
