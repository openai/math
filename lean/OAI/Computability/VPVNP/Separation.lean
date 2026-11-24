import OAI.Computability.VPVNP.FamilyResult
import OAI.Computability.VPVNP.FixedPaperPairCompiler

/-! # Separation over every field

The explicit family of (1.1) is treated in `explicit_complete_family`.
Here the fixed compressed-pair compiler closes the diagonal argument. The
length threshold is chosen for each exponent and characteristic before
the coefficient field is chosen.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u

/-- The uniform exact arithmetic circuit lower bound of Theorem 1.1. -/
theorem separation_lower_bound :
    ∀ C : ℕ, 1 ≤ C → ∀ q : ℕ, ∃ N, ∀ n ≥ N, ∀ (F : Type u) [Field F] [CharP F q],
      n ^ C < circuitSize (MvPolynomial.map (Int.castRingHom F) (P n)) := by
  apply FixedProgramDiagonal.uniform_of_pair_compilers
  intro C _ q K _ _ _ _ S B _
  exact FixedProgramDiagonal.Program.paperPairCompiler B C

/-- The family on the paired variables separates the two nonuniform classes over each field. -/
theorem vp_ne_vnp (F : Type u) [Field F] :
    (IsVP : Family F (fun n => Fin n × Bool) → Prop) ≠ IsVNP :=
  vp_ne_vnp_of_uniform_P separation_lower_bound F

/-- Corollary 1.2 for directed Hamiltonian cycles and for the permanent outside characteristic two. -/
theorem corollary12 (q C : ℕ) :
    ∃ N, ∀ m ≥ N, ∀ (F : Type u) [Field F] [CharP F q],
      m ^ C < circuitSize (hamiltonianCyclePolynomial F m) ∧
        (q ≠ 2 → m ^ C < circuitSize (permanentPolynomial F m)) :=
  corollary12_of_uniform_P separation_lower_bound q C

end VPVNP
end Computability
end OAI
