import OAI.Computability.VPVNP.GrassmannTypes
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Independent readings on complementary planes

A linear map on the ambient binary vector space is uniquely determined by
its values on chosen bases of two complementary middle-dimensional subspaces.
Consequently a uniform linear map gives two independent uniform tuples there.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Grassmann

variable {m : ℕ}

theorem HasType.isCompl {U V : Plane m} (h : HasType m U V) : IsCompl U.val V.val := by
  change Module.finrank (ZMod 2) (U.val ⊔ V.val : Submodule _ _) = m + m at h
  apply IsCompl.of_eq
  · apply Submodule.finrank_eq_zero.mp
    have hd := Submodule.finrank_sup_add_finrank_inf_eq U.val V.val
    rw [h, U.property, V.property] at hd
    omega
  · apply Submodule.eq_top_of_finrank_eq
    simpa only [Space, Module.finrank_pi, Fintype.card_fin, two_mul] using h

/-- The fixed ordered basis used to read the restriction of a linear map. -/
noncomputable def planeBasis (U : Plane m) : Module.Basis (Fin m) (ZMod 2) U.val :=
  Module.finBasisOfFinrankEq (ZMod 2) U.val U.property

variable (E : Type*) [AddCommGroup E] [Module (ZMod 2) E]

/-- Values on the fixed ordered basis of a plane. -/
noncomputable def readPlane (U : Plane m) (f : Space m →ₗ[ZMod 2] E) : Fin m → E :=
  fun i => f (planeBasis U i)

/-- Reading both members of a complementary pair is a bijection. -/
noncomputable def readComplementEquiv {U V : Plane m} (h : HasType m U V) :
    (Space m →ₗ[ZMod 2] E) ≃ (Fin m → E) × (Fin m → E) :=
  (LinearMap.ofIsComplProdEquiv h.isCompl).symm.toEquiv.trans
    (((planeBasis U).constr (ZMod 2)).symm.toEquiv.prodCongr
      ((planeBasis V).constr (ZMod 2)).symm.toEquiv)

@[simp] theorem readComplementEquiv_apply {U V : Plane m} (h : HasType m U V)
    (f : Space m →ₗ[ZMod 2] E) :
    readComplementEquiv E h f = (readPlane E U f, readPlane E V f) := rfl

noncomputable instance [Finite E] : Fintype (Space m →ₗ[ZMod 2] E) :=
  @Fintype.ofFinite _ (Finite.of_injective (fun f : Space m →ₗ[ZMod 2] E => (f : Space m → E))
    DFunLike.coe_injective)

/-- The sum over the sampled linear map is a sum over two independent tuples. -/
theorem sum_read_complement [Fintype E] {U V : Plane m} (h : HasType m U V)
    {A : Type*} [AddCommMonoid A] (d : (Fin m → E) → (Fin m → E) → A) :
    (∑ f : Space m →ₗ[ZMod 2] E, d (readPlane E U f) (readPlane E V f)) =
      ∑ x : Fin m → E, ∑ y : Fin m → E, d x y := by
  classical
  rw [← Fintype.sum_prod_type']
  exact (readComplementEquiv E h).sum_comp (fun z => d z.1 z.2)

/-- Averaging a two-point observable on complementary planes gives the product law. -/
theorem average_read_complement [Fintype E] {U V : Plane m} (h : HasType m U V)
    (d : (Fin m → E) → (Fin m → E) → ℝ) :
    (∑ f : Space m →ₗ[ZMod 2] E, d (readPlane E U f) (readPlane E V f)) /
        Fintype.card (Space m →ₗ[ZMod 2] E) =
      (∑ x : Fin m → E, ∑ y : Fin m → E, d x y) / (Fintype.card (Fin m → E) : ℝ) ^ 2 := by
  rw [sum_read_complement E h, Fintype.card_congr (readComplementEquiv E h),
    Fintype.card_prod, Nat.cast_mul, sq]

end Grassmann

end VPVNP
end Computability
end OAI
