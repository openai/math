import OAI.LinearAlgebra.SpectralBooks.SpectralSpace

/-! # Relabeling the ends of a placed wire -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

open scoped Classical
universe u

/-- Permuting the indices of a common-label tensor does not change its
mutual-restriction class at the occupied sites. -/
theorem grouped_diagonal_reindex {A B : Type u} {J : Type*} [Fintype A] [Fintype B] [Fintype J]
    (K D : Type*) [CommSemiring K] [Fintype D] (e : A ≃ B) (σ : B → J) :
    ((diagonal B K D).group σ).Equivalent ((diagonal A K D).group (σ ∘ e)) := by
  let fiber (j : J) : {i : A // σ (e i) = j} ≃ {i : B // σ i = j} :=
    e.subtypeEquiv (fun _ => Iff.rfl)
  apply reindex_equivalent (fun j => Equiv.arrowCongr (fiber j).symm (Equiv.refl D))
  intro x
  apply Finset.sum_congr rfl
  intro d _
  change (if (fun i => x (σ i) ⟨i, rfl⟩) = (fun _ => d) then (1 : K) else 0) =
    (if (fun i => x (σ (e i)) ⟨e i, rfl⟩) = (fun _ => d) then 1 else 0)
  let labels (i : B) : D := x (σ i) ⟨i, rfl⟩
  have heq : (labels = fun _ => d) ↔ ((labels ∘ e) = fun _ => d) := by
    constructor
    · intro h
      exact funext fun i => congrFun h (e i)
    · intro h
      exact funext fun i => by simpa [Function.comp] using congrFun h (e.symm i)
  exact if_congr heq rfl rfl

/-- Interchanging the ends of a placed wire gives a mutual restriction,
including when the two endpoints coincide. -/
theorem grouped_wire_symm {J : Type*} [Fintype J] (K D : Type*) [CommSemiring K]
    [Fintype D] (s t : J) :
    ((diagonal (Fin 2) K D).group ![s, t]).Equivalent
      ((diagonal (Fin 2) K D).group ![t, s]) := by
  have h : ![s, t] ∘ Fin.revPerm = ![t, s] := by
    funext i
    fin_cases i <;> rfl
  rw [← h]
  exact grouped_diagonal_reindex K D (Fin.revPerm (n := 2)) ![s, t]

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
