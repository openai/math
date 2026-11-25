import OAI.LinearAlgebra.SpectralBooks.PortGraph.BoundedPatchReplacementClosure

/-! # Realizing a prescribed stub order by a polygon numbering -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace PortGraph

variable {V B : Type*} {m b : ℕ}

def polygonOrder (old : V ≃ Fin m) (stubs : B ≃ Fin (b+1)) :
    V ⊕ B ≃ Fin (m+b+1) := (old.sumCongr stubs).trans finSumFinEquiv

@[simp] theorem polygonOrder_root (old : V ≃ Fin m) (stubs : B ≃ Fin (b+1)) :
    polygonOrder old stubs (.inr (stubs.symm (Fin.last b))) = Fin.last (m+b) := by
  simp [polygonOrder, finSumFinEquiv_apply_right]

theorem polygonOrder_stubs (old : V ≃ Fin m) (stubs : B ≃ Fin (b+1)) :
    (List.finRange (m+b)).filterMap (fun i => stubLabel (polygonOrder old stubs) i.castSucc) =
      (List.finRange b).map (fun i => stubs.symm i.castSucc) := by
  have split : List.finRange (m+b) =
      (List.finRange m).map (Fin.castAdd b) ++ (List.finRange b).map (Fin.natAdd m) := by
    have he : (fun i : Fin m => Fin.castLE (Nat.le_add_right m b) i) = Fin.castAdd b :=
      funext (fun _ => Fin.ext rfl)
    simpa [List.ofFn_eq_map, he] using (List.ofFn_add (f := id (α := Fin (m+b))))
  rw [split,List.filterMap_append,List.filterMap_map,List.filterMap_map]
  have hl (i : Fin m) : stubLabel (polygonOrder old stubs) (i.castAdd b).castSucc = none := by
    have pos : (i.castAdd b).castSucc = polygonOrder old stubs (.inl (old.symm i)) := by
      simp [polygonOrder, finSumFinEquiv_apply_left]
      rfl
    simp [pos,stubLabel]
  have hr (i : Fin b) : stubLabel (polygonOrder old stubs) (Fin.natAdd m i).castSucc =
      some (stubs.symm i.castSucc) := by
    have pos : (Fin.natAdd m i).castSucc = polygonOrder old stubs (.inr (stubs.symm i.castSucc)) := by
      simp [polygonOrder, finSumFinEquiv_apply_right]
    simp [pos,stubLabel]
  have hnone : (List.finRange m).filterMap
      ((fun i : Fin (m+b) => stubLabel (polygonOrder old stubs) i.castSucc) ∘ Fin.castAdd b) = [] :=
    List.filterMap_eq_nil_iff.mpr (fun i _ => hl i)
  rw [hnone, List.nil_append]
  have hh : (fun i : Fin (m+b) => stubLabel (polygonOrder old stubs) i.castSucc) ∘ Fin.natAdd m =
      some ∘ (fun i : Fin b => stubs.symm i.castSucc) := funext hr
  rw [hh, List.filterMap_eq_map]

end PortGraph

end SpectralBooks
end LinearAlgebra
end OAI
