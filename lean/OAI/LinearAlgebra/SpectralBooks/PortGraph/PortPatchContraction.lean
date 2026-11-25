import OAI.LinearAlgebra.SpectralBooks.PortWiring

/-! # Contraction across a partition into patches

An edge with both endpoints in the same patch is summed out there. A cut
edge carries one shared index into the two patch tensors. This separates
the original scalar contraction into open patch contractions and permits
their independent replacement by sums of open tensors.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical
noncomputable section

namespace PortGraph

variable {V E J : Type*} (G : PortGraph V E) (p : V → J)

/-- Edges whose two endpoint vertices belong to different patches. -/
abbrev CrossEdge := {e : E // p (G.tail e) ≠ p (G.head e)}

/-- The edges internal to patch `j`, including loops. -/
abbrev PatchInternal (j : J) := {e : E // p (G.tail e) = j ∧ p (G.head e) = j}

/-- The cut edges incident to patch `j`. Each contributes one stub there. -/
abbrev PatchBoundary (j : J) :=
  {e : G.CrossEdge p // p (G.tail e.val) = j ∨ p (G.head e.val) = j}

/-- Wire assignments split into one assignment on the cut edges and one
assignment on the internal edges of each patch. -/
def patchAssignmentEquiv (A : E → Type*) :
    ((e : E) → A e) ≃
      ((e : G.CrossEdge p) → A e.val) × ((j : J) → (e : G.PatchInternal p j) → A e.val) where
  toFun a := (fun e => a e.val, fun _ e => a e.val)
  invFun z e := if h : p (G.tail e) = p (G.head e) then
    z.2 (p (G.tail e)) ⟨e, rfl, h.symm⟩ else z.1 ⟨e, h⟩
  left_inv a := by funext e; dsimp; split <;> rfl
  right_inv z := by
    refine Prod.ext (funext fun e => by simp [e.property]) ?_
    funext j e
    obtain ⟨e, rfl, h⟩ := e
    simp [h]

variable {A : E → Type*}

/-- Read all local indices at a vertex from this patch's internal assignment
and its fixed stub indices. -/
def patchAtVertex {j : J} (x : (e : G.PatchBoundary p j) → A e.1.1)
    (y : (e : G.PatchInternal p j) → A e.val) (v : {v : V // p v = j}) :
    G.State A v.val := by
  rintro ⟨⟨e, b⟩, hv⟩
  have hit : p (G.tail e) = j ∨ p (G.head e) = j := by
    have h := (congrArg p hv).trans v.property
    cases b with
    | false => exact Or.inl h
    | true => exact Or.inr h
  by_cases h : p (G.tail e) = p (G.head e)
  · have inside : p (G.tail e) = j ∧ p (G.head e) = j := by
      rcases hit with ht | hh
      · exact ⟨ht, h.symm.trans ht⟩
      · exact ⟨h.trans hh, hh⟩
    exact y ⟨e, inside⟩
  · exact x ⟨⟨e, h⟩, hit⟩

private theorem patchAtVertex_of_global (a : (e : E) → A e) {j : J} (v : {v : V // p v = j}) :
    G.patchAtVertex p (fun e => a e.1.1) (fun e => a e.1) v = G.atVertex a v.1 := by
  funext port
  obtain ⟨⟨e,b⟩, hv⟩ := port
  simp only [patchAtVertex, atVertex]
  split <;> rfl

variable {K : Type*} [CommSemiring K] [Fintype V] [Fintype E] [∀ e, Fintype (A e)]

/-- Contract all internal wires of a patch with its incident stub indices fixed. -/
def patchContraction (U : (v : V) → G.State A v → K) (j : J)
    (x : (e : G.PatchBoundary p j) → A e.1.1) : K :=
  ∑ y : (e : G.PatchInternal p j) → A e.1, ∏ v : {v : V // p v = j},
    U v.val (G.patchAtVertex p x y v)

variable [Fintype J]

/-- Independent patch contractions glue to the original scalar network.
Every cut wire is identified once and summed over once. -/
theorem contraction_eq_patchContractions (U : (v : V) → G.State A v → K) :
    G.contraction U = ∑ x : (e : G.CrossEdge p) → A e.val,
      ∏ j, G.patchContraction p U j (fun e => x e.val) := by
  unfold contraction patchContraction
  simp_rw [Fintype.prod_sum]
  rw [← Fintype.sum_prod_type']
  apply Fintype.sum_equiv (G.patchAssignmentEquiv p A)
  intro a
  simp only [patchAssignmentEquiv, Equiv.coe_fn_mk, patchAtVertex_of_global]
  rw [← Fintype.prod_sigma']
  exact Fintype.prod_equiv (Equiv.sigmaFiberEquiv p).symm _ _ (fun _ => rfl)

/-- Replacing each open patch tensor by a finite sum expands the network
as a sum indexed by one choice of replacement in each patch. -/
theorem contraction_eq_sum_patchReplacements (U : (v : V) → G.State A v → K)
    (R : J → Type*) [∀ j, Fintype (R j)]
    (T : (j : J) → R j → ((e : G.PatchBoundary p j) → A e.1.1) → K)
    (h : ∀ j s, G.patchContraction p U j s = ∑ r, T j r s) :
    G.contraction U = ∑ r : (j : J) → R j, ∑ x : (e : G.CrossEdge p) → A e.val,
      ∏ j, T j (r j) (fun e => x e.val) := by
  rw [G.contraction_eq_patchContractions p U]
  simp_rw [h, Fintype.prod_sum]
  exact Finset.sum_comm

end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
