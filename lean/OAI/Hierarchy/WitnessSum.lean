import OAI.Computability.VPVNP.ProjectionClosure

namespace OAI
/-! # Arithmetic circuits as Boolean witness sums -/

namespace Hierarchy

open Computability.VPVNP

/-- Every VP family over a field is a VNP family. With no witness variables
there is exactly one Boolean assignment, and its summand is the original polynomial. -/
theorem isVNP_of_isVP {F : Type*} [Field F] {σ : ℕ → Type} [∀ n, Fintype (σ n)]
    {p : Family F σ} (hp : IsVP p) : IsVNP p := by
  classical
  let φ (n : ℕ) : Projection F (σ n) (σ n ⊕ Empty) := fun i => .inl (.inl i)
  let g : Family F (fun n => σ n ⊕ Empty) := fun n => (φ n).hom (p n)
  have hg : IsVP g := hp.of_pProjects
    ⟨id, PolynomiallyBounded.id, fun n => ⟨φ n, rfl⟩⟩ (by simpa using hp.1.1)
  refine ⟨hp.1, fun _ => Empty, fun _ => inferInstance, g, ?_, hg, ?_⟩
  · simpa using PolynomiallyBounded.const 0
  · intro n
    have undo (y : Empty → Bool) :
        (witnessValue (X := σ n) (F := F) y).comp (φ n).hom = RingHom.id _ := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [Projection.hom, witnessValue]
      · intro i
        simp [φ, Projection.hom, witnessValue]
    have one (y : Empty → Bool) : witnessValue y (g n) = p n :=
      DFunLike.congr_fun (undo y) (p n)
    simp [one]


end Hierarchy

end OAI
