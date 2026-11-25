import OAI.ThreeFlat.Diagonal.PackedChunkTransfer
import OAI.ThreeFlat.Diagonal.RotatedBucketScan

namespace OAI
/-! # Evaluating a complete physical sweep at the packed group endpoints -/

namespace ThreeFlat.Diagonal.PackedBucketTransfer

open HistoryContraction TickChronology RotatedChunkGuards PackedChunkTransfer
open scoped BigOperators Classical

variable {F : Type*} [CommSemiring F] {S : Shape}

/-- The actual packed group rows, physical rotation, and original ownership
maps determine the two endpoints at which the local kernel is evaluated. -/
theorem scheduled_sum (P : Plan F S) (h : P.History) (group : (P.finish h).Site → ℕ)
    (bs : List (Bucket S.Site)) (c : Clock) (g a : ℕ)
    (disj : PackedBucketBijection.Disjoint (group ∘ P.destination h) bs)
    (fit : ∀ b ∈ bs, b.hi ≤ c.chunks*a)
    (x y : Fin c.chunks → Fin a → Bool)
    (W : (Fin (BucketRows.count (group ∘ P.destination h) bs g) → Bool) →
      (Fin (BucketRows.count (group ∘ P.destination h) bs g) → Bool) → F) :
    let q := RotatedBucketScan.code P h group bs c g a
    let e := PackedBucketBijection.chunkEquiv (group ∘ P.destination h) g bs disj c.chunks a fit
    (∑ p, ∑ r, W p r * (((order c g).map fun i =>
      chunkKernel (fun j => entry (F:=F) (q j) (atIndex p) (atIndex r)) {i}).prod) x y) =
      if holdsOutside q x y then W (project q e x) (project q e y) else 0 := by
  dsimp only
  simp_rw [RotatedBucketScan.full_scan]
  apply sum_endpoints
  exact PackedBucketBijection.chunkEquiv_val _ _ _ _ _ _ _


end ThreeFlat.Diagonal.PackedBucketTransfer

end OAI
