import OAI.Computability.VPVNP.Hardness

/-! # The explicit complete family in Theorem 1.1 -/

namespace OAI
namespace Computability
namespace VPVNP

/-- The algebraic and completeness assertions about the paper's integer family.
The circuit-size lower bound is a separate assertion of Theorem 1.1. -/
theorem explicit_complete_family (F : Type*) [Field F] :
    (∀ n : ℕ,
      Fintype.card (Fin n × Bool) = 2 * n ∧
      (MvPolynomial.map (Int.castRingHom F) (P n)).IsHomogeneous n ∧
      (MvPolynomial.map (Int.castRingHom F) (P n)).totalDegree = n ∧
      ∀ z : Fin n × Bool, (MvPolynomial.map (Int.castRingHom F) (P n)).degreeOf z ≤ 1) ∧
    IsVNP (σ := fun n => Fin n × Bool) (fun n => MvPolynomial.map (Int.castRingHom F) (P n)) ∧
    ∀ (V : ℕ → Type) [∀ n, Fintype (V n)] (f : Family F V),
      IsVNP f → PProjects f (fun n => MvPolynomial.map (Int.castRingHom F) (P n)) := by
  refine ⟨fun n => ⟨by simp [Nat.mul_comm], ?_, totalDegree_map_P n, ?_⟩, P_vnpComplete F⟩
  · rw [map_P]
    exact pairedPolynomial_isHomogeneous _
  · intro v
    rw [map_P]
    exact pairedPolynomial_multilinear _ v

end VPVNP
end Computability
end OAI
