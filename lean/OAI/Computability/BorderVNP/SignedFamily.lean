import OAI.Computability.BorderVNP.SignedPaths
import OAI.Computability.VPVNP.PairedFamily

/-!
# The signed polynomial of equation (2.1)

Every monomial chooses one variable at each bit position. Its integer coefficient
counts positive halts minus negative halts under the `n ^ 100` simulated-step clock.
-/

namespace OAI
namespace Computability
namespace BorderVNP

open MvPolynomial

/-- The signed universal path-count polynomial on the paired bit variables. -/
noncomputable def Pstar (n : ℕ) : MvPolynomial (Fin n × Bool) ℤ :=
  VPVNP.pairedPolynomial signedCount

/-- Base change sends the integer path sums to their images in the coefficient ring. -/
theorem map_Pstar {R : Type*} [CommRing R] (n : ℕ) :
    MvPolynomial.map (Int.castRingHom R) (Pstar n) =
      VPVNP.pairedPolynomial (fun x => (signedCount x : R)) :=
  VPVNP.map_pairedPolynomial _ _

/-- The coefficient query addressed by a bit word is its signed path sum. -/
@[simp] theorem coeff_Pstar {n : ℕ} (x : Fin n → Bool) :
    (Pstar n).coeff (VPVNP.pairedExponent x) = signedCount x :=
  VPVNP.coeff_pairedPolynomial _ _

/-- Each term has one variable from each pair and hence is homogeneous of degree `n`. -/
theorem Pstar_isHomogeneous (n : ℕ) : (Pstar n).IsHomogeneous n :=
  VPVNP.pairedPolynomial_isHomogeneous _

/-- A single bit-position variable has exponent at most one. -/
theorem Pstar_multilinear (n : ℕ) (z : Fin n × Bool) : (Pstar n).degreeOf z ≤ 1 :=
  VPVNP.pairedPolynomial_multilinear _ _

/-- The all-zero nonempty word starts already halted with value one. Its monomial
survives in every nontrivial coefficient ring, even when signed path counts cancel. -/
theorem totalDegree_map_Pstar {R : Type*} [CommRing R] [Nontrivial R] (n : ℕ) :
    (MvPolynomial.map (Int.castRingHom R) (Pstar n)).totalDegree = n := by
  rw [map_Pstar]
  by_cases hn : n = 0
  · subst n
    exact Nat.le_zero.mp (VPVNP.pairedPolynomial_isHomogeneous _).totalDegree_le
  · apply VPVNP.pairedPolynomial_totalDegree _ (fun _ => false)
    simp [signedCount_allFalse (Nat.pos_of_ne_zero hn)]

/-- The structural assertions of Theorem 1.1 hold after arbitrary field specialization. -/
theorem Pstar_structure (F : Type*) [Field F] (n : ℕ) :
    Fintype.card (Fin n × Bool) = 2 * n ∧
    (MvPolynomial.map (Int.castRingHom F) (Pstar n)).IsHomogeneous n ∧
    (MvPolynomial.map (Int.castRingHom F) (Pstar n)).totalDegree = n ∧
    ∀ z, (MvPolynomial.map (Int.castRingHom F) (Pstar n)).degreeOf z ≤ 1 := by
  have h := totalDegree_map_Pstar (R := F) n
  rw [map_Pstar] at h ⊢
  exact ⟨by simp [Nat.mul_comm], VPVNP.pairedPolynomial_isHomogeneous _, h,
    VPVNP.pairedPolynomial_multilinear _⟩

end BorderVNP
end Computability
end OAI
