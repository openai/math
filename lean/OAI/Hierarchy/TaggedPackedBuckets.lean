import OAI.Hierarchy.TaggedWideOrder
import OAI.Hierarchy.TaggedLocalSortBuckets

namespace OAI
/-! # Reading individual words and digit buckets from packed records -/

namespace Hierarchy.Tagged.Radix.PassShape
open ThreeFlat Routing SortNetwork RadixStage SortedBlock WideOrder
open scoped Classical
noncomputable section

/-- A valid outgoing row reads the entire indicated lane of the sorted pack. -/
theorem leave_word (s : PassShape) {w : ℕ} (X : Records s.globalHeight (s.pack*w))
    (i : Fin s.nextRows) (inside : i.val/s.pack < 2^s.globalHeight) :
    (fun j => staticRead s.leave (SortNetwork.pack X) (i,j)) =
      lane (X ⟨i.val/s.pack,inside⟩) ⟨i.val%s.pack,Nat.mod_lt _ (Nat.two_pow_pos _)⟩ := by
  funext j
  have wire : s.leave (i,j) = .inl (Fintype.equivFin (Payload s.globalHeight (s.pack*w))
      (⟨i.val/s.pack,inside⟩,finProdFinEquiv (⟨i.val%s.pack,Nat.mod_lt _ (Nat.two_pow_pos _)⟩,j))) := by
    simp only [leave,dite_eq_left inside]
  change Sum.elim (SortNetwork.pack X) id (s.leave (i,j)) = _
  rw [wire]
  simp [SortNetwork.pack,lane,Function.uncurry]

/-- Filtering the packed row stream is the lexicographic rectangular scan of
its packs and their lanes. -/
theorem packed_bucket {u p w d : ℕ} (X : Records u (p*w)) (real : Fin w)
    (digit : Fin d → Fin w) (a : ℕ) :
    bucket (readKey digit) a (observed real X) =
      sweep (2^u) (fun r => sweep p fun i => observeRow real digit a (lane (X r) i)) := by
  unfold bucket observed
  rw [List.filter_flatMap,sweep_eq_flatMap]
  apply List.flatMap_congr
  intro q _
  exact (sweep_rows (lane (X q)) real digit a).symm

end
end Hierarchy.Tagged.Radix.PassShape

end OAI
