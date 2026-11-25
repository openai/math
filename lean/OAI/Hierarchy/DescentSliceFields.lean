import OAI.Hierarchy.DescentBundleTerminal

namespace OAI
/-! # The original affine slice descriptors of a typed gate -/
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory
noncomputable section
variable {p : ℕ} {Tag A : Type} {w : A→ℕ}

def Shape.sliceFields {r : BitRecipe Tag A w} (s : Shape p r) (v : r.Node) :=
  List.ofFn (fun j=>List.ofFn (fun g=>(s.chunk v j g).code))

theorem Shape.tag_fields (hp : 0<p) {r : BitRecipe Tag A w} (s : Shape p r) (v : r.Node) :
    ((s.recipe hp).tag v)=(r.tag v,s.sliceFields v) := by
  simp [Shape.recipe,Shape.rows,Shape.sliceFields,Function.comp_def,List.map_ofFn]


end
end Hierarchy.DescentBundleHistory

end OAI
