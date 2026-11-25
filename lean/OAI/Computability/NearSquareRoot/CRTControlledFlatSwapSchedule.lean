import OAI.Computability.NearSquareRoot.CRTControlledFlatSwaps
import OAI.Computability.NearSquareRoot.BoundedIndexedSweep

/-! # Bounded linear-space iteration of supplied two-position exchanges -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Strip
open IntegerMultiplication.Code NearSquareRoot.Space

noncomputable section

private def swapDescriptor (k : ℕ) (a : Fin k × Fin k) :=
  (tally k, tally (max a.1 a.2).val, tally (min a.1 a.2).val)

private def descriptorAt (k : ℕ) (moves : List (Fin k × Fin k)) (j : ℕ) :=
  ((moves.map (swapDescriptor k))[j]?).getD ([],[],[])

private theorem descriptor_exact {k : ℕ} (moves : List (Fin k × Fin k)) (j : Fin moves.length) :
    descriptorAt k moves j.val = swapDescriptor k moves[j.val] := by
  simp [descriptorAt,j.isLt]

private theorem descriptor_forest {k : ℕ} (moves : List (Fin k × Fin k)) :
    Task.forest (fun j => send (descriptorAt k moves j)) (List.range moves.length) =
      send (moves.map (swapDescriptor k)) := by
  have e : (List.range moves.length).map (descriptorAt k moves) = moves.map (swapDescriptor k) := by
    apply List.ext_getElem
    · simp
    · intro j h₁ h₂
      simp only [List.getElem_map,List.getElem_range]
      exact descriptor_exact moves ⟨j, by simpa using h₂⟩
  rw [← Task.forest_map, e,Task.forest_send]

/-- Execute the supplied distinct-position swaps head to tail. Only one
intermediate array is parked as the table forest is scanned. -/
theorem boundedFlatSwapKeys {I : Type} (k V : I → ℕ)
    (moves : (i:I) → List (Fin (k i) × Fin (k i)))
    (distinct : ∀ i, ∀ a ∈ moves i, a.1 ≠ a.2)
    (f : (i:I) → Block 2 (k i) → Tree)
    (fileCap : ∀ i, (stripe (line 2 (k i)) (f i)).count ≤ V i)
    (tableCap : ∀ i, (send ((moves i).map (fun a =>
      (tally (k i), tally (max a.1 a.2).val, tally (min a.1 a.2).val)))).count ≤ V i) :
    BoundedTask (fun i => ((moves i).length + 1)*V i) V
      (fun i => .fork (send ((moves i).map (fun a =>
        (tally (k i), tally (max a.1 a.2).val, tally (min a.1 a.2).val))))
        (stripe (line 2 (k i)) (f i)))
      (fun i => stripe (line 2 (k i)) (f i ∘ swapsFlat (moves i))) := by
  let m i := (moves i).length
  let Q := (i:I) × Fin (m i)
  let pair (q:Q) := (moves q.1)[q.2.val]'q.2.isLt
  let fs i j := f i ∘ swapsFlat ((moves i).take j)
  let state i j := stripe (line 2 (k i)) (fs i j)
  have cap i (j:ℕ) : (state i j).count ≤ V i := by
    simpa only [state,fs,stripe_count_perm] using fileCap i
  have different (q:Q) : (pair q).1 ≠ (pair q).2 := distinct q.1 (pair q) (List.getElem_mem _)
  let hi (q:Q) := max (pair q).1 (pair q).2
  let lo (q:Q) := min (pair q).1 (pair q).2
  have ord (q:Q) : lo q < hi q := min_lt_max.mpr (different q)
  have step := flatGateFromPositions (fun q:Q => k q.1) (fun q => V q.1) hi lo ord
    (digitGate Prod.swap) (fun q => fs q.1 q.2.val) (fun q => cap q.1 q.2.val)
  have go := BoundedTask.indexedSweep m
    (fun i j => send (descriptorAt (k i) (moves i) j)) state V V V
    (step.conform (fun _ => rfl) (fun _ => rfl) (fun q => by
      rw [descriptor_exact (moves q.1) q.2]; rfl) (fun q => by
      dsimp only [state,fs]
      rw [List.take_succ_eq_append_getElem q.2.isLt,swapsFlat_append]
      apply congrArg _
      funext a
      change f q.1 (swapsFlat _ (flatGateAt (hi q) (lo q) (ord q) (digitGate Prod.swap) a)) =
        f q.1 (swapsFlat _ (swapFlat (pair q) a))
      rw [swapFlat_of_ne _ (different q)]))
    (fun i => (descriptor_forest (moves i)) ▸ tableCap i) (fun i j _ => cap i j)
  have bounded := go.bound (time' := fun i => ((moves i).length+1)*V i) (space' := V) 1 2
    (fun i => by simp [m,Nat.add_mul]) (fun i => by omega)
  exact bounded.conform (fun _ => rfl) (fun _ => rfl)
    (fun i => by rw [descriptor_forest]; rfl)
    (fun i => by simp only [state,fs,m,List.take_length])

end
end Controlled

end NearSquareRoot
end Computability
end OAI
