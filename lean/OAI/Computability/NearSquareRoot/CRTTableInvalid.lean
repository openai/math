import OAI.Computability.NearSquareRoot.CRTTableNode

/-! # Identity tables on invalid CRT controls and padded target cells -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CRTTable

open IntegerMultiplication IntegerMultiplication.Code

private theorem descriptors_zipFair {A B : Type} (a : A) (b : B) (xs : List A) (ys : List B) :
    (zipFair a b (xs,ys)).map Prod.fst = xs := by
  simp [zipFair, zipSafe, cutLists, List.map_fst_zip, Nat.add_comm xs.length ys.length]

private theorem zeroRotation (a L : Tally) : rotation ([],a,L) = Iter.lineup L := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have h : j < L.length := by simpa using hj'
    have hv := rotation_entry [] a L ⟨j,h⟩
    suffices ht : ((rotation ([],a,L))[j]).length = j by
      rw [← recover_tally ((rotation ([],a,L))[j]), ht]
      simp [Iter.lineup]
    by_cases hj : j < a.length
    · simpa [hj, Nat.mod_eq_of_lt] using hv
    · simpa [hj] using hv

/-- The raw control word consists of whole fields in decreasing axis order.
If any field represents a padded value, both forward and inverse queries
emit the identity permutation on every target axis, including its padding. -/
theorem nodeTables_invalid (fs : List (ControlAxis × List Bool)) (targets : List ControlAxis)
    (direction : Bool) (width : ∀ x ∈ fs, x.2.length = x.1.1.length)
    (invalid : ∃ x ∈ fs, x.1.2.length ≤ bitValue x.2) :
    nodeTables (direction, fs.map Prod.fst, targets, (fs.reverse.map Prod.snd).flatten) =
      targets.map (fun d => Iter.lineup (padded d)) := by
  let q : NodeQuery := (direction, fs.map Prod.fst, targets, (fs.reverse.map Prod.snd).flatten)
  have flag : (prepareRows (initialPacket q)).1 = false := by
    unfold q initialPacket
    rw [prepareRows_correct _ _ _ width]
    simpa using invalid
  let rows := zipFair ([],[]) ([],[],[]) (targets,targetRows q)
  change (rows.map (fun s => emitAxis (((prepareRows (initialPacket q)).1,direction),s))) = _
  rw [flag]
  have h : (fun s : Descriptor × Row => emitAxis ((false,direction),s)) =
      (fun d : Descriptor => Iter.lineup (padded d)) ∘ Prod.fst := by
    funext s
    exact zeroRotation _ _
  rw [h, ← List.map_map, descriptors_zipFair]

/-- Every target lookup fixes an out-of-range cell, even when the control
setting is valid and the shift is nonzero. -/
theorem emitAxis_padding (s : (Bool × Bool) × Descriptor × Row)
    (j : Fin (padded s.2.1).length) (hpad : s.2.1.2.length ≤ j.val) :
    (emitAxis s)[j.val]'(by simp [emitAxis]) = tally j.val := by
  rw [← recover_tally ((emitAxis s)[j.val]'(by simp [emitAxis]))]
  congr 1
  rw [emitAxis_entry, ite_eq_right (by omega)]

end CRTTable

end NearSquareRoot
end Computability
end OAI
