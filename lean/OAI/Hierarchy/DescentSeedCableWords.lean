import OAI.Hierarchy.DescentSeedSiteIndex

namespace OAI
/-! # Immutable identifiers and cable fields for a stacked copy of the original graph -/
namespace Hierarchy.DescentSeedRoot
open DescentInitialHost Catalyst
open scoped Classical
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {k p : ℕ} (X : Approximation F k p)
local notation "N" => X.network.copyGraph

def vertexID {R : ℕ} (j : Fin R) (v : Vertex X) := j.val*Fintype.card (Vertex X)+index v

def cableID {R : ℕ} (j : Fin R) (e : Cable X) := j.val*Fintype.card (Cable X)+index e

/-- Width is the actual stacked width; the matrix/site pointers in fields two and three
retain the copy number as well as the correct source and destination of the original cable. -/
def cableWords {R : ℕ} (s : ℕ) (j : Fin R) (e : Cable X) : Fin 8→ℕ :=
  ![j.val,cableID X j e,vertexID X j (source N e),vertexID X j (target N e),s,
    Sum.elim (fun _=>1) (fun _=>0) e,index e,Sum.elim (fun a=>index a) (fun b=>b.val) e]

end
end Hierarchy.DescentSeedRoot

end OAI
