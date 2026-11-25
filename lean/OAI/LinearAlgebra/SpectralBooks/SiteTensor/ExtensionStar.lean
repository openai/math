import OAI.LinearAlgebra.SpectralBooks.ContractionPrice

/-! # A pair of wires meeting at one new party

A covector at the new party has one entry for each pair of endpoint labels.
Contracting the two wires reads that entry at the two old endpoints.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical
noncomputable section

namespace SiteTensor.Raw

variable {I : Type*} (K : Type*) [Field K]

/-- The new party holds both labels, and each old endpoint holds its own label. -/
def newStar (a b : I) (A B : Type) [Fintype A] [Fintype B] : Raw.{0} (Option I) K where
  Leg := Option.rec (A × B) (fun i ↦ (i = a → A) × (i = b → B))
  finiteLeg := Option.rec (inferInstanceAs (Fintype (A × B))) (fun i ↦
    Fintype.ofFinite ((i = a → A) × (i = b → B)))
  coeff x := (if (x none).1 = (x (some a)).1 rfl then 1 else 0) *
    (if (x none).2 = (x (some b)).2 rfl then 1 else 0)

/-- Contracting the common end of the two wires gives the matrix of the covector. -/
theorem contractNew_newStar_coeff [Fintype I] (a b : I) (A B : Type) [Fintype A] [Fintype B]
    (ξ : A × B → K) (x : ∀ i, (i = a → A) × (i = b → B)) :
    ((newStar K a b A B).contractNew ξ).coeff x = ξ ((x a).1 rfl, (x b).2 rfl) := by
  change (∑ s : A × B, ξ s * ((if s.1 = (x a).1 rfl then 1 else 0) *
    (if s.2 = (x b).2 rfl then 1 else 0))) = _
  rw [Fintype.sum_prod_type]
  simp [mul_ite]

end SiteTensor.Raw

end

end SpectralBooks
end LinearAlgebra
end OAI
