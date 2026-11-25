import OAI.ThreeFlat.Diagonal.HistoryBucketRows

namespace OAI
/-! # Packing finite arrays with a prescribed prefix recurrence -/

namespace ThreeFlat.Diagonal.HistoryContraction.BucketRows

theorem pack_ofFn {V G : Type*} [DecidableEq G] {n : ℕ} (group : V → G)
    (buckets : Fin n → Bucket V) (acc : ℕ → G → ℕ)
    (next : ∀ i : Fin n, BucketRows.bump group (acc i.val) (buckets i) = acc (i.val+1)) :
    BucketRows.pack group (acc 0) (List.ofFn buckets) =
      List.ofFn (fun i => BucketRows.row group (acc i.val) (buckets i)) := by
  induction n generalizing acc with
  | zero => simp [BucketRows.pack]
  | succ n ih =>
    have zero : bump group (acc 0) (buckets 0)=acc 1 := by
      simpa only [Fin.val_zero,Nat.zero_add] using next 0
    rw [List.ofFn_succ, List.ofFn_succ, BucketRows.pack, zero]
    congr 1
    exact ih (fun i => buckets i.succ) (fun i => acc (i+1)) (fun i => next i.succ)

end ThreeFlat.Diagonal.HistoryContraction.BucketRows

end OAI
