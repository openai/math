import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentStubNames
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentOpenContraction

/-! # Reading a boundary coordinate by its original stub name -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch.TrivalentTree

variable {K V : Type*} {d : V → ℕ} {q : ℕ}

/-- Boundary readings in path order coincide with readings in the retained
label order, including zero-size alphabets whenever the assignment exists. -/
theorem map_leafRead (t : TrivalentTree K d q) (x : ∀ v, Fin (d v)) :
    t.leafPaths.map (t.leafRead x) = t.labels.map (fun v => (x v).val) := by
  induction t with
  | port => rfl
  | branch B l r hl hr =>
    simp only [leafPaths, labels, List.map_append, List.map_map, Function.comp_def, leafRead, hl, hr]

/-- The original assigned value is read by its triple-table tree leaf address. -/
theorem leafRead_eq_named (t : TrivalentTree K d q) (x : ∀ v, Fin (d v)) (p : t.Leaf) :
    t.leafRead x p.val = (x (t.leafName p)).val := by
  classical
  let i := ((t.leafPaths_nodup).getEquiv t.leafPaths).symm p
  have hget : t.leafPaths.get i = p.val := congrArg Subtype.val
    (((t.leafPaths_nodup).getEquiv t.leafPaths).apply_symm_apply p)
  have hl : i.val < t.labels.length := t.leafPaths_length ▸ i.isLt
  have he := congrArg (fun l : List ℕ => l[i.val]?) (t.map_leafRead x)
  rw [List.getElem?_map, List.getElem?_map, List.getElem?_eq_getElem i.isLt,
    List.getElem?_eq_getElem hl] at he
  exact hget ▸ Option.some.inj he

end PlanarPatch.TrivalentTree

end SpectralBooks
end LinearAlgebra
end OAI
