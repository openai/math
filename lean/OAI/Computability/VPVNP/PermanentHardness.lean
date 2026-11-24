import OAI.Computability.VPVNP.PermanentWeighted
import OAI.Computability.VPVNP.ExactOneFamily
import OAI.Computability.VPVNP.CompletePolynomials
import OAI.Computability.VPVNP.CompleteFieldDescent

/-!
# Permanent hardness and the transfer in Corollary 1.2

Each exact-one presentation of a VNP family projects from a permanent of polynomially
bounded order. The scalar used for an occurrence gadget is available precisely when two
is invertible in the coefficient field.
-/

namespace OAI
namespace Computability
namespace VPVNP

open MvPolynomial

variable {F : Type*} [Field F] {V : ℕ → Type} [∀ n, Fintype (V n)]

/-- In characteristic different from two, every VNP family is a literal p-projection of
the generic permanent family. -/
theorem pProjects_permanent_of_isVNP (q : ℕ) [CharP F q] (hq : q ≠ 2)
    (p : Family F V) (hp : IsVNP p) : PProjects p (permanentPolynomial F) := by
  obtain ⟨k, φ, w, _, hwidth, hclauses, hlits, he⟩ := ExactOne.exists_family_of_isVNP p hp
  refine ⟨fun n => 3 * HardnessCNF.literalCount (φ n) +
      k n * (HardnessCNF.literalCount (φ n) + 2) + (φ n).length,
    (((PolynomiallyBounded.const 3).mul hlits).add (hwidth.mul (hlits.add (.const 2)))).add hclauses, ?_⟩
  intro n
  obtain ⟨ρ, hρ⟩ := PermanentReduction.weighted_projection q hq (φ n) (w n)
  exact ⟨ρ, hρ.trans (he n)⟩

/-- Section 15.1's reduction of the paper's integer family to the permanent. -/
theorem P_pProjects_permanent (F : Type*) [Field F] (q : ℕ) [CharP F q] (hq : q ≠ 2) :
    PProjects (fun n => map (Int.castRingHom F) (P n)) (permanentPolynomial F) :=
  pProjects_permanent_of_isVNP q hq _ (P_isVNP F)

/-- The permanent assertion of Corollary 1.2 follows from the eventual lower bound for
`P` over one algebraically closed field of the specified characteristic. -/
theorem permanent_uniform_of_P {K : Type*} [Field K] [IsAlgClosed K]
    (q : ℕ) [CharP K q] (hq : q ≠ 2)
    (h : EventuallySuperpolynomial fun n => circuitSize (map (Int.castRingHom K) (P n)))
    (C : ℕ) :
    ∃ N, ∀ m ≥ N, ∀ (F : Type*) [Field F] [CharP F q],
      m ^ C < circuitSize (permanentPolynomial F m) := by
  obtain ⟨N, hN⟩ := permanent_bound_of_pProjects (P_pProjects_permanent K q hq) h C
  exact ⟨N, permanentPolynomial_uniform_bound (K := K) q C N hN⟩

end VPVNP
end Computability
end OAI
