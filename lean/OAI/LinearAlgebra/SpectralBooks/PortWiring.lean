import OAI.LinearAlgebra.SpectralBooks.PortNetwork
import OAI.LinearAlgebra.SpectralBooks.Crossing

/-!
# Contracting the wiring tensor against vertex tables

Writing the state of each vertex independently turns the edge identifications
into a tensor coefficient. After a local restriction of this tensor, the
original tables can be multiplied by the transposes of the restricting
matrices. The entries may lie in any commutative algebra over the field
of the restricting matrices.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical
noncomputable section

section

namespace PortGraph

variable {V E : Type*} (G : PortGraph V E) (A : E → Type*) {K : Type*} [CommSemiring K]

/-- The independent states at a vertex give one index for each incident port. -/
abbrev State (v : V) := (p : G.Port v) → A p.1.1

/-- The tensor product of the identity wires, grouped by vertex. -/
def wiring (x : (v : V) → G.State A v) : K :=
  if ∀ e : E, x (G.tail e) ⟨(e,false),rfl⟩ = x (G.head e) ⟨(e,true),rfl⟩ then 1 else 0

/-- An independent tuple of local states either fails an edge check, or
comes from exactly one global edge assignment. -/
theorem contraction_eq_wiring [Fintype V] [Fintype E] [∀ e, Fintype (A e)]
    (U : (v : V) → G.State A v → K) :
    G.contraction U = ∑ x, G.wiring A x * ∏ v, U v (x v) := by
  unfold contraction
  apply Fintype.sum_of_injective (G.atVertex (A := A))
  · exact Function.LeftInverse.injective (g := fun z e => z (G.tail e) ⟨(e,false),rfl⟩)
      (fun _ => rfl)
  · intro x hx
    have bad : ¬∀ e : E, x (G.tail e) ⟨(e,false),rfl⟩ = x (G.head e) ⟨(e,true),rfl⟩ := by
      intro h
      apply hx
      refine ⟨fun e => x (G.tail e) ⟨(e,false),rfl⟩, ?_⟩
      funext v p
      obtain ⟨⟨e,b⟩,hv⟩ := p
      subst v
      cases b with
      | false => rfl
      | true => exact h e
    simp [wiring, bad]
  · intro a
    simp [wiring, atVertex]

end PortGraph

/-- The pairing of a tensor with a family of local tables, allowing the
tables to have coefficients in an extension algebra. -/
def tablePairing {V K R : Type*} [Fintype V] [CommSemiring K] [CommSemiring R]
    (h : K →+* R) {A : V → Type*} [∀ v, Fintype (A v)] (X : (∀ v, A v) → K)
    (U : ∀ v, A v → R) : R :=
  ∑ x, h (X x) * ∏ v, U v (x v)

/-- Transpose the local matrices while keeping the ambient coefficient ring
of the circuit. This holds at each choice of the patch's free stub indices. -/
theorem tablePairing_of_restriction {V K R : Type*} [Fintype V] [CommSemiring K] [CommSemiring R]
    (h : K →+* R) {A B : V → Type*} [∀ v, Fintype (A v)] [∀ v, Fintype (B v)]
    (Y : (∀ v, B v) → K) (X : (∀ v, A v) → K) (res : Crossing.IsRestriction Y X) (U : ∀ v, B v → R) :
    ∃ M : ∀ v, B v → A v → K,
      tablePairing h Y U = tablePairing h X (fun v a => ∑ b, h (M v b a) * U v b) := by
  obtain ⟨M, hM⟩ := res
  refine ⟨M, ?_⟩
  simp only [tablePairing, hM, map_sum, map_mul, map_prod, Finset.sum_mul, Fintype.prod_sum,
    Finset.prod_mul_distrib, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end

end

end SpectralBooks
end LinearAlgebra
end OAI
