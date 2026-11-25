import OAI.Hierarchy.CatalystSubstitutionNetwork

namespace OAI
/-! # Native table product at shared exposed pins

The two networks use disjoint hidden bits and catalyst endpoints. Each call
data address is connected directly to its designated external pin. -/

noncomputable section
namespace Hierarchy.CatalystSubstitution.SharedProduct
open Catalyst ThreeFlat Routing
open scoped Classical BigOperators

variable {F : Type*} [Field F] {k p q : ℕ}

def extend (a : Fin q → Fin p) (B : Approximation F k p) (X : Approximation F k q) :
    Approximation F k p where
  width j := B.width j + X.width j
  network := plugPair (H:=Empty) B.network X.network (Sum.inl ∘ oldPort B.width X.width)
    (Sum.inl ∘ Sum.elim (Sum.inl ∘ a) (newPort B.width X.width))

theorem extend_coeff (a : Fin q → Fin p) (B : Approximation F k p)
    (X : Approximation F k q) (x : Port p (fun j => B.width j + X.width j) → Bool) :
    (extend a B X).coeff x = B.coeff (x ∘ oldPort B.width X.width) *
      X.coeff (Sum.elim (x ∘ Sum.inl ∘ a) (x ∘ newPort B.width X.width)) := by
  change TypedWiring.value (plugPair _ _ _ _) x = _
  rw [plugPair_value, Fintype.sum_unique]
  congr 1
  apply congrArg (TypedWiring.value X.network)
  funext t
  cases t <;> rfl

omit [Field F] in
theorem extend_size (a : Fin q → Fin p) (B : Approximation F k p)
    (X : Approximation F k q) : (extend a B X).size + q = B.size + X.size := by
  have pack := (Fintype.card_congr (portEquiv (p:=p) B.width X.width)).symm
  rw [Fintype.card_sum (α:=Port p B.width) (β:=Wire X.width × Bool)] at pack
  change (extend a B X).network.cells + (extend a B X).network.internal +
    Fintype.card (Port p (fun j => B.width j+X.width j)) + q =
    B.network.cells + B.network.internal + Fintype.card (Port p B.width) +
      (X.network.cells + X.network.internal + Fintype.card (Fin q ⊕ Wire X.width × Bool))
  simp only [extend, plugPair_cells, plugPair_internal, Fintype.card_empty, zero_add]
  have ports := Fintype.card_sum (α:=Fin q) (β:=Wire X.width × Bool)
  have data := Fintype.card_fin q
  omega

end Hierarchy.CatalystSubstitution.SharedProduct

end
end OAI
