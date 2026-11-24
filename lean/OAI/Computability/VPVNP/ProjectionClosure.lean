import OAI.Computability.VPVNP.PolynomialBounds
import OAI.Computability.VPVNP.ProjectionDegree

/-!
# Closure of VP and VNP under p-projections

The family receiving a projection has polynomially many variables. Lift a projection
through the VNP sum by projecting the visible variables and keeping each Boolean
witness variable as a formal input to the new summand.
-/

namespace OAI
namespace Computability
namespace VPVNP

open scoped Classical

variable {F : Type*} [Field F] {X Y : ℕ → Type} [∀ n, Fintype (X n)] [∀ n, Fintype (Y n)]

/-- Formal variable-or-scalar substitution preserves a polynomial bound on the degree. -/
theorem PFamily.of_pProjects {p : Family F X} {q : Family F Y}
    (hq : PFamily q) (hpq : PProjects p q)
    (hvar : PolynomiallyBounded (fun n => Fintype.card (X n))) : PFamily p := by
  obtain ⟨r, hr, hφ⟩ := hpq
  refine ⟨hvar, (hq.2.comp hr).of_le fun n => ?_⟩
  obtain ⟨φ, he⟩ := hφ n
  rw [← he]
  exact φ.totalDegree_hom_le _

theorem IsVP.of_pProjects {p : Family F X} {q : Family F Y}
    (hq : IsVP q) (hpq : PProjects p q)
    (hvar : PolynomiallyBounded (fun n => Fintype.card (X n))) : IsVP p := by
  refine ⟨hq.1.of_pProjects hpq hvar, ?_⟩
  obtain ⟨r, hr, hφ⟩ := hpq
  apply (hq.2.comp hr).of_le
  intro n
  obtain ⟨φ, he⟩ := hφ n
  rw [← he]
  exact circuitSize_projection_le _ _

/-- Extend a projection of visible variables by the identity on witness variables. -/
def Projection.withWitness {σ τ W : Type} (φ : Projection F σ τ) :
    Projection F (σ ⊕ W) (τ ⊕ W) :=
  Sum.elim (fun i => (φ i).map Sum.inl id) (fun i => .inl (.inr i))

/-- Specializing the Boolean witness before or after the visible projection agrees. -/
theorem Projection.witnessValue_comp {σ τ W : Type} (φ : Projection F σ τ) (y : W → Bool) :
    (witnessValue (X := τ) y).comp (φ.withWitness.hom) =
      φ.hom.comp (witnessValue (X := σ) y) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [Projection.hom, witnessValue]
  · rintro (i | j)
    · cases h : φ i <;> simp [Projection.withWitness, Projection.hom, witnessValue, h]
    · cases h : y j <;> simp [Projection.withWitness, Projection.hom, witnessValue, h]

theorem IsVNP.of_pProjects {p : Family F X} {q : Family F Y}
    (hq : IsVNP q) (hpq : PProjects p q)
    (hvar : PolynomiallyBounded (fun n => Fintype.card (X n))) : IsVNP p := by
  obtain ⟨hqf, W, instW, g, hw, hg, hsum⟩ := hq
  let : ∀ n, Fintype (W n) := instW
  refine ⟨hqf.of_pProjects hpq hvar, ?_⟩
  obtain ⟨r, hr, hproj⟩ := hpq
  choose φ hφ using hproj
  let s : Family F (fun n => X n ⊕ W (r n)) := fun n => (φ n).withWitness.hom (g (r n))
  refine ⟨fun n => W (r n), fun n => instW (r n), s, hw.comp hr, ?_, ?_⟩
  · apply hg.of_pProjects ⟨r, hr, fun n => ⟨(φ n).withWitness, rfl⟩⟩
    simpa only [Fintype.card_sum] using hvar.add (hw.comp hr)
  · intro n
    rw [← hφ n, hsum, map_sum]
    apply Finset.sum_congr rfl
    intro y _
    exact DFunLike.congr_fun ((φ n).witnessValue_comp y).symm _

end VPVNP
end Computability
end OAI
