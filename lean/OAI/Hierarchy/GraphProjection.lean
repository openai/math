import OAI.Hierarchy.GraphContractions
import Mathlib.Logic.Embedding.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace OAI
/-! # Subgraph projections of vertex-table contractions

Fix every edge outside the embedded graph to a single state. A vertex table
entry inconsistent with this state is sent to zero. A remaining entry gives
the restricted vertex table at a retained vertex and the scalar one at a
deleted vertex.
-/

namespace Hierarchy.IncidenceGraph

open MvPolynomial
open scoped Classical

/-- An incidence-preserving injection on vertices and edges. -/
structure Embedding (H G : IncidenceGraph) where
  vertex : H.V ↪ G.V
  edge : H.E ↪ G.E
  map_left : ∀ e, G.left (edge e) = vertex (H.left e)
  map_right : ∀ e, G.right (edge e) = vertex (H.right e)

namespace Embedding

variable {H G K : IncidenceGraph} {q : ℕ}

protected def id (G : IncidenceGraph) : Embedding G G where
  vertex := Function.Embedding.refl _
  edge := Function.Embedding.refl _
  map_left _ := rfl
  map_right _ := rfl

def comp (j : Embedding G K) (i : Embedding H G) : Embedding H K where
  vertex := i.vertex.trans j.vertex
  edge := i.edge.trans j.edge
  map_left e := (j.map_left (i.edge e)).trans (congrArg j.vertex (i.map_left e))
  map_right e := (j.map_right (i.edge e)).trans (congrArg j.vertex (i.map_right e))

variable (φ : Embedding H G)

def mapIncident (v : H.V) (i : H.Incident v) : G.Incident (φ.vertex v) :=
  ⟨φ.edge i.val,i.prop.imp
    (fun h => (φ.map_left _).trans (congrArg φ.vertex h))
    (fun h => (φ.map_right _).trans (congrArg φ.vertex h))⟩

/-- Extend a legal labeling by fixing the deleted edges. -/
noncomputable def extendLabel (base : Fin q) (a : H.E → Fin q) : G.E → Fin q :=
  Function.extend φ.edge a (fun _ => base)

@[simp] theorem extendLabel_edge (base : Fin q) (a : H.E → Fin q) (e : H.E) :
    φ.extendLabel base a (φ.edge e) = a e :=
  φ.edge.injective.extend_apply _ _ _

theorem extendLabel_outside (base : Fin q) (a : H.E → Fin q) {e : G.E}
    (he : e ∉ Set.range φ.edge) : φ.extendLabel base a e = base :=
  Function.extend_apply' _ _ _ he

theorem extendLabel_injective (base : Fin q) : Function.Injective (φ.extendLabel base) := by
  intro a b h
  funext e
  simpa using congrFun h (φ.edge e)

def Legal (base : Fin q) (a : G.E → Fin q) : Prop :=
  ∀ e ∉ Set.range φ.edge, a e = base

theorem legal_iff_mem_range (base : Fin q) (a : G.E → Fin q) :
    φ.Legal base a ↔ a ∈ Set.range (φ.extendLabel base) := by
  constructor
  · intro h
    refine ⟨a ∘ φ.edge,?_⟩
    funext e
    by_cases he : e ∈ Set.range φ.edge
    · obtain ⟨j,rfl⟩ := he
      simp
    · exact (φ.extendLabel_outside base _ he).trans (h e he).symm
  · rintro ⟨b,rfl⟩ e he
    exact φ.extendLabel_outside base b he

private def legalAt (base : Fin q) (v : G.V) (t : G.Incident v → Fin q) : Prop :=
  ∀ e : G.Incident v, e.val ∉ Set.range φ.edge → t e = base

/-- Lift the vertex index without changing the incident-edge table at its image. -/
private def liftTable : (Σ v : H.V,G.Incident (φ.vertex v) → Fin q) ↪ G.TableVar q :=
  φ.vertex.sigmaMap (fun _ => Function.Embedding.refl _)

variable (R : Type*) [CommSemiring R]

private noncomputable def keptTable : Computability.VPVNP.Projection R (G.TableVar q) (H.TableVar q) :=
  Function.extend (φ.liftTable (q:=q))
    (fun z => Sum.inl ⟨z.1,z.2 ∘ φ.mapIncident z.1⟩) (fun _ => Sum.inr 1)

noncomputable def projection (base : Fin q) : Computability.VPVNP.Projection R (G.TableVar q) (H.TableVar q) :=
  fun z => if φ.legalAt base z.1 z.2 then φ.keptTable R z else Sum.inr 0

private theorem kept_at_image (a : G.E → Fin q) (v : H.V) :
    φ.keptTable R (G.tableIndex a (φ.vertex v)) = Sum.inl (H.tableIndex (a ∘ φ.edge) v) := by
  let z : Σ u : H.V, G.Incident (φ.vertex u) → Fin q := ⟨v,fun i => a i.val⟩
  change Function.extend (φ.liftTable (q:=q)) _ _ (φ.liftTable z) = _
  rw [(φ.liftTable (q:=q)).injective.extend_apply]
  rfl

private theorem kept_outside (a : G.E → Fin q) {v : G.V} (hv : v ∉ Set.range φ.vertex) :
    φ.keptTable R (G.tableIndex a v) = Sum.inr 1 := by
  apply Function.extend_apply'
  rintro ⟨z,h⟩
  exact hv ⟨z.1,congrArg Sigma.fst h⟩

private theorem hom_X (base : Fin q) (z : G.TableVar q) :
    (φ.projection R base).hom (X z) = (φ.projection R base z).elim X C := by
  simp [Computability.VPVNP.Projection.hom]

theorem hom_assignmentMonomial_of_legal (base : Fin q) (a : G.E → Fin q) (ha : φ.Legal base a) :
    (φ.projection R base).hom (G.assignmentMonomial R a) =
      H.assignmentMonomial R (a ∘ φ.edge) := by
  classical
  simp only [assignmentMonomial,map_prod]
  have atVertex (v : G.V) : φ.legalAt base v (fun e => a e.val) := fun e he => ha e.val he
  have projected (v : G.V) : φ.projection R base (G.tableIndex a v) =
      φ.keptTable R (G.tableIndex a v) := ite_eq_left (atVertex v)
  symm
  apply Fintype.prod_of_injective φ.vertex φ.vertex.injective
  · intro v hv
    simp only [φ.hom_X,projected,φ.kept_outside R a hv,Sum.elim_inr,map_one]
  · intro v
    simp only [φ.hom_X,projected,φ.kept_at_image R a v,Sum.elim_inl]

theorem hom_assignmentMonomial_of_not_legal (base : Fin q) (a : G.E → Fin q)
    (ha : ¬φ.Legal base a) :
    (φ.projection R base).hom (G.assignmentMonomial R a) = 0 := by
  classical
  have missing : ∃ e : G.E, e ∉ Set.range φ.edge ∧ a e ≠ base := by
    simpa [Legal] using ha
  obtain ⟨e,he,hbad⟩ := missing
  have hl : ¬φ.legalAt base (G.left e) (fun i => a i.val) :=
    fun h => hbad (h ⟨e,Or.inl rfl⟩ he)
  simp only [assignmentMonomial,map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (G.left e))
  rw [φ.hom_X]
  simp [projection,tableIndex,hl]

/-- Restricting a larger contraction to the embedded subgraph uses only
variables and the two scalars zero and one. -/
theorem hom_contraction (base : Fin q) :
    (φ.projection R base).hom (G.contraction R q) = H.contraction R q := by
  classical
  simp only [contraction,map_sum]
  symm
  apply Fintype.sum_of_injective (φ.extendLabel base) (φ.extendLabel_injective base)
  · intro a ha
    exact φ.hom_assignmentMonomial_of_not_legal R base a ((φ.legal_iff_mem_range base a).not.mpr ha)
  · intro a
    have legal := (φ.legal_iff_mem_range base (φ.extendLabel base a)).mpr ⟨a,rfl⟩
    rw [φ.hom_assignmentMonomial_of_legal R base _ legal]
    congr 1
    funext e
    simp

end Embedding
end Hierarchy.IncidenceGraph

end OAI
