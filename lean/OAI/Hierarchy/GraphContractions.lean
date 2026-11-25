import OAI.Computability.VPVNP.Classes
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation

namespace OAI
/-! # Vertex-table contractions of finite loopless multigraphs -/

namespace Hierarchy

/-- An edge has its own name, so parallel edges carry independent labels.
The order of its endpoints only serves to specify the incidence maps. -/
structure IncidenceGraph where
  V : Type
  E : Type
  [vertexFinite : Fintype V]
  [edgeFinite : Fintype E]
  left : E → V
  right : E → V
  loopless : ∀ e, left e ≠ right e

attribute [instance] IncidenceGraph.vertexFinite IncidenceGraph.edgeFinite

namespace IncidenceGraph

open scoped Classical
noncomputable section

variable (G : IncidenceGraph)

abbrev Incident (v : G.V) := {e : G.E // G.left e = v ∨ G.right e = v}

noncomputable instance incidentFintype (v : G.V) : Fintype (G.Incident v) :=
  Fintype.ofFinite _

def degree (v : G.V) : ℕ := Fintype.card (G.Incident v)

/-- A vertex has a distinct variable for each assignment to its incident edges. -/
abbrev TableVar (q : ℕ) := (v : G.V) × (G.Incident v → Fin q)

noncomputable instance tableVarFintype (q : ℕ) : Fintype (G.TableVar q) :=
  Fintype.ofFinite _

def tableIndex {q : ℕ} (a : G.E → Fin q) (v : G.V) : G.TableVar q :=
  ⟨v, fun e => a e.1⟩

def assignmentMonomial (F : Type*) [CommSemiring F] {q : ℕ} (a : G.E → Fin q) :
    MvPolynomial (G.TableVar q) F := ∏ v : G.V, MvPolynomial.X (G.tableIndex a v)

def contraction (F : Type*) [CommSemiring F] (q : ℕ) : MvPolynomial (G.TableVar q) F :=
  ∑ a : G.E → Fin q, G.assignmentMonomial F a

def Adjacent (u v : G.V) : Prop :=
  ∃ e, (G.left e = u ∧ G.right e = v) ∨ (G.left e = v ∧ G.right e = u)

def Connected : G.V → G.V → Prop := Relation.ReflTransGen G.Adjacent

def component (v : G.V) : Finset G.V := Finset.univ.filter (G.Connected v)

/-- Edges with exactly one endpoint in the prefix of the vertex order. -/
def cutEdges (ord : G.V ≃ Fin (Fintype.card G.V)) (cut : ℕ) : Finset G.E :=
  Finset.univ.filter fun e => ¬ ((ord (G.left e)).val < cut ↔ (ord (G.right e)).val < cut)

def CutwidthAtMost (b : ℕ) : Prop :=
  ∃ ord : G.V ≃ Fin (Fintype.card G.V), ∀ cut : ℕ, (G.cutEdges ord cut).card ≤ b

/-- A rooted tree decomposition. For each graph vertex, the bags which contain it
are joined to one common bag by parent paths entirely within that set. -/
structure TreeDecomposition where
  Bag : Type
  [bagFinite : Fintype Bag]
  root : Bag
  parent : Bag → Bag
  level : Bag → ℕ
  parent_root : parent root = root
  parent_lt : ∀ i, i ≠ root → level (parent i) < level i
  bag : Bag → Finset G.V
  vertex_cover : ∀ v, ∃ i, v ∈ bag i
  edge_cover : ∀ e, ∃ i, G.left e ∈ bag i ∧ G.right e ∈ bag i
  running : ∀ v, ∃ top, v ∈ bag top ∧ ∀ i, v ∈ bag i →
    ∃ k : ℕ, (parent^[k]) i = top ∧ ∀ j ≤ k, v ∈ bag ((parent^[j]) i)

def TreewidthAtMost (b : ℕ) : Prop :=
  ∃ D : TreeDecomposition G, ∀ i, (D.bag i).card ≤ b + 1

end
end IncidenceGraph

noncomputable def contractionFamily (F : Type*) [CommSemiring F] (G : ℕ → IncidenceGraph) :
    Computability.VPVNP.Family F (fun n => (G n).TableVar n) :=
  fun n => (G n).contraction F n

end Hierarchy

end OAI
