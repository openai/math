import OAI.Computability.BorderVNP.BranchCurveDVR
import OAI.Computability.BorderVNP.BranchCurveSeparable
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The place of the deformation through the chosen output

For a point on the special fiber of the affine curve and a square system
in its generic parameters, nonsingularity and generation of the function
field give a single discrete valuation ring. Every regular coordinate
specializes there to its prescribed value. No regularity of the individual
parameter functions is imposed.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial

/-- The function field of the component has a discrete place above the chosen
point of the zero fiber, with simultaneous specialization of all coordinate
functions. This combines the Jacobian separability argument and normalization
over the parameter line. -/
theorem place_at_special_point {K A L ι : Type*} [Field K] [CommRing A]
    [Field L] [Algebra K A] [Algebra A L] [IsFractionRing A L]
    [Algebra (Polynomial K) A] [Algebra (Polynomial K) L] [IsScalarTower (Polynomial K) A L]
    [Algebra (FractionRing (Polynomial K)) L]
    [IsScalarTower (Polynomial K) (FractionRing (Polynomial K)) L]
    [Fintype ι] [DecidableEq ι] (point : A →ₐ[K] K)
    (hzero : point (algebraMap (Polynomial K) A Polynomial.X) = 0)
    (g : ι → MvPolynomial ι (FractionRing (Polynomial K))) (x : ι → L)
    (hgen : IntermediateField.adjoin (FractionRing (Polynomial K)) (Set.range x) = ⊤)
    (hroot : ∀ i, aeval x (g i) = 0)
    (hjac : (Matrix.of fun i j => aeval x (pderiv j (g i))).det ≠ 0) :
    ∃ (V : ValuationSubring L) (regular : ∀ a : A, algebraMap A L a ∈ V),
      IsDiscreteValuationRing V ∧ algebraMap (Polynomial K) L Polynomial.X ∈ V.nonunits ∧
      ∀ a : A, IsLocalRing.residue V ⟨algebraMap A L a, regular a⟩ =
        IsLocalRing.residue V ⟨algebraMap A L (algebraMap K A (point a)), regular _⟩ := by
  obtain ⟨hfin, hsep⟩ := finite_separable_of_nonsingular_system g x hgen hroot hjac
  let inc := algebraMap A L
  have hker : RingHom.ker inc ≤ RingHom.ker point.toRingHom :=
    fun a ha => by
      have eq : a = 0 := IsFractionRing.injective A L (ha.trans (map_zero inc).symm)
      simp [eq]
  obtain ⟨V, hreg, hspec⟩ := valuationRing_of_kernel_le inc point.toRingHom hker
  have regular (a : A) : inc a ∈ V := hreg ⟨a, rfl⟩
  have h0 : algebraMap (Polynomial K) L Polynomial.X ∈ V.nonunits := by
    rw [IsScalarTower.algebraMap_apply (Polynomial K) A L]
    exact hspec _ hzero
  refine ⟨V, regular, discrete_place_over_parameter V (fun p => ?_) h0, h0, fun a => ?_⟩
  · rw [IsScalarTower.algebraMap_apply (Polynomial K) A L]
    exact regular _
  · rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    apply V.coe_mem_nonunits_iff.mp
    change inc a - inc (algebraMap K A (point a)) ∈ V.nonunits
    rw [← map_sub]
    apply hspec
    simp

end Branch

end BorderVNP
end Computability
end OAI
