import OAI.LinearAlgebra.SpectralBooks.PortWiring
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchTriangulation

/-! # Placing port equality checks on triangulation edges

One separator table checks every original wire with those endpoints. This
includes parallel wires in either direction. A wire having a singleton state
space is automatically consistent.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical BigOperators

namespace PortGraph

variable {n : ℕ} {E K : Type*} [CommSemiring K]
variable (G : PortGraph (Fin n) E) (A : E → Type*) (S : ℕ → Type*)
variable (read : (i : Fin n) → S i.val → G.State A i)

/-- Sorted integer endpoints used to assign a wire its triangulation edge. -/
def sortedEnds (e : E) : ℕ × ℕ :=
  (min (G.tail e).val (G.head e).val, max (G.tail e).val (G.head e).val)

private def checkForward (u v : ℕ) (x : S u) (y : S v) : Prop :=
  ∀ (e : E) (hu : (G.tail e).val = u) (hv : (G.head e).val = v),
    read (G.tail e) (hu.symm ▸ x) ⟨(e,false),rfl⟩ =
      read (G.head e) (hv.symm ▸ y) ⟨(e,true),rfl⟩

/-- Local equality factor at a triangulation edge. Each direction checks the
fiber of wires with the indicated tail and head. -/
def edgeFactor (u v : ℕ) (x : S u) (y : S v) : K :=
  if G.checkForward A S read u v x y ∧ G.checkForward A S read v u y x then 1 else 0

/-- At fixed vertex states, the product of the edge tables is the indicator
of compatibility of every original wire assignment. -/
theorem wiring_eq_prod_edgeFactor {lo hi : ℕ} (T : PlanarPatch.Triangulation lo hi)
    (hT : ∀ e, ¬ Subsingleton (A e) → G.sortedEnds e ∈ T.edges) (s : ∀ i, S i) :
    G.wiring (K := K) A (fun i ↦ read i (s i.val)) =
      ∏ uv ∈ T.edges, G.edgeFactor A S read uv.1 uv.2 (s uv.1) (s uv.2) := by
  unfold wiring edgeFactor
  rw [Finset.prod_boole]
  congr 1
  apply propext
  constructor
  · rintro h ⟨u,v⟩ _
    constructor <;> rintro e ht hh <;> dsimp only at ht hh <;> subst u <;> subst v <;> exact h e
  · intro h e
    by_cases hs : Subsingleton (A e)
    · exact hs.elim _ _
    · have he := h (G.sortedEnds e) (hT e hs)
      by_cases ht : (G.tail e).val ≤ (G.head e).val
      · rw [show G.sortedEnds e = ((G.tail e).val,(G.head e).val) from
          Prod.ext (min_eq_left ht) (max_eq_right ht)] at he
        exact he.1 e rfl rfl
      · have hn := le_of_not_ge ht
        rw [show G.sortedEnds e = ((G.head e).val,(G.tail e).val) from
          Prod.ext (min_eq_right hn) (max_eq_left hn)] at he
        exact he.2 e rfl rfl

/-- Reindex the vertex states by local bijections. The contraction becomes the
sum of vertex-table products times their triangulation edge factors. -/
theorem contraction_eq_triangulation [Fintype E] [∀ e, Fintype (A e)] [∀ i, Fintype (S i)]
    (eqv : ∀ i : Fin n, S i.val ≃ G.State A i) (U : ∀ i, G.State A i → K)
    {lo hi : ℕ} (T : PlanarPatch.Triangulation lo hi)
    (hT : ∀ e, ¬ Subsingleton (A e) → G.sortedEnds e ∈ T.edges)
    (extend : ((i : Fin n) → S i.val) → (i : ℕ) → S i)
    (hext : ∀ x (i : Fin n), extend x i.val = x i) :
    G.contraction U = ∑ x : (i : Fin n) → S i.val,
      (∏ i, U i (eqv i (x i))) *
        ∏ uv ∈ T.edges, G.edgeFactor A S (fun i ↦ eqv i) uv.1 uv.2
          (extend x uv.1) (extend x uv.2) := by
  refine (G.contraction_eq_wiring A U).trans ?_
  symm
  let e : ((i : Fin n) → S i.val) ≃ ((i : Fin n) → G.State A i) := Equiv.piCongrRight eqv
  let B (x : (i : Fin n) → S i.val) := (∏ i, U i (eqv i (x i))) *
    ∏ uv ∈ T.edges, G.edgeFactor A S (fun i ↦ eqv i) uv.1 uv.2 (extend x uv.1) (extend x uv.2)
  let D (y : (i : Fin n) → G.State A i) := G.wiring A y * ∏ i,U i (y i)
  have h (x : (i : Fin n) → S i.val) : B x = D (e x) := by
    have hw := G.wiring_eq_prod_edgeFactor (K := K) A S (fun i ↦ eqv i) T hT (extend x)
    simp only [hext] at hw
    change _ = G.wiring A (fun i ↦ eqv i (x i)) * ∏ i, U i (eqv i (x i))
    rw [hw, mul_comm]
  refine (Fintype.sum_equiv e B D h).trans ?_
  refine Finset.sum_congr ?_ (fun _ _ ↦ rfl)
  ext x
  simp
end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
