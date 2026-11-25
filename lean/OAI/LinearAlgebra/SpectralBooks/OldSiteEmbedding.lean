import OAI.LinearAlgebra.SpectralBooks.ContractionPrice
import OAI.LinearAlgebra.SpectralBooks.ScalarRestriction

/-! # Adjoining an unoccupied tensor site

The new leg has a single basis vector, so adjoining it preserves old
restrictions, products and nonvanishing.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped BigOperators Classical

namespace SiteTensor

universe v u w
variable {I : Type u} {K : Type w}

namespace Raw

/-- Extend a tensor on the old sites by the one-dimensional new leg. -/
def embedOld (X : Raw.{v} I K) : Raw.{v} (Option I) K where
  Leg := fun j => j.elim PUnit X.Leg
  finiteLeg := fun j => by cases j <;> dsimp <;> infer_instance
  coeff := fun x => X.coeff fun i => x (some i)

/-- The enlarged coordinates are in bijection with the original ones. -/
def embedOldCoords (X : Raw.{v} I K) :
    (∀ j, X.embedOld.Leg j) ≃ (∀ i, X.Leg i) where
  toFun x i := x (some i)
  invFun x j := match j with
    | none => PUnit.unit
    | some i => x i
  left_inv x := by funext j; cases j <;> rfl
  right_inv x := rfl

@[simp] theorem embedOld_coeff_ne_zero_iff [Zero K] (X : Raw.{v} I K) :
    X.embedOld.coeff ≠ 0 ↔ X.coeff ≠ 0 := by
  constructor
  · intro h he
    exact h (funext fun x => congrFun he (X.embedOldCoords x))
  · intro h he
    exact h (funext fun x => congrFun he (X.embedOldCoords.symm x))

variable [Fintype I] [CommSemiring K]

/-- Extend each old local map by the identity on the new scalar leg. -/
theorem embedOld_restricts {X Y : Raw.{v} I K} (h : X.Restricts Y) :
    X.embedOld.Restricts Y.embedOld := by
  let : DecidableEq (Option I) := fun _ _ ↦ Classical.propDecidable _
  obtain ⟨M, hM⟩ := h
  let N : ∀ j, X.embedOld.Leg j → Y.embedOld.Leg j → K
    | none => fun _ _ => 1
    | some i => M i
  refine ⟨N, fun x => ?_⟩
  change X.coeff (fun i => x (some i)) = _
  refine (hM (X.embedOldCoords x)).trans ?_
  apply Fintype.sum_equiv Y.embedOldCoords.symm
  intro y
  rw [Fintype.prod_option]
  simp [embedOld, embedOldCoords, N]
  rfl

/-- A map on the scalar leg acts by a scalar which an old site can absorb. -/
@[simp] theorem embedOld_restricts_iff [Nonempty I] {X Y : Raw.{v} I K} :
    X.embedOld.Restricts Y.embedOld ↔ X.Restricts Y := by
  refine ⟨?_, embedOld_restricts⟩
  rintro ⟨M, hM⟩
  let : DecidableEq (Option I) := Classical.decEq _
  let c := M none PUnit.unit PUnit.unit
  let Z : Raw.{v} I K := {Y with coeff := c • Y.coeff}
  have hZ : Z.Restricts Y := scalar_mul_restricts c Y.coeff
  refine restrict_trans (Y := Z.coeff) ?_ hZ
  refine ⟨fun i => M (some i), fun x => ?_⟩
  refine (hM (X.embedOldCoords.symm x)).trans ?_
  apply Fintype.sum_equiv Y.embedOldCoords
  intro y
  rw [Fintype.prod_option]
  let P := ∏ i, M (some i) (x i) (y (some i))
  change Y.coeff (Y.embedOldCoords y) * (c * P) = (c * Y.coeff (Y.embedOldCoords y)) * P
  ac_rfl

private theorem embedOld_one_equivalent :
    (one I K).embedOld.Equivalent (one (Option I) K : Raw.{v} _ _) := by
  refine reindex_equivalent (fun j => ?_) (fun _ => rfl)
  cases j <;> exact Equiv.refl _

private theorem embedOld_mul_equivalent (X Y : Raw.{v} I K) :
    (X.mul Y).embedOld.Equivalent (X.embedOld.mul Y.embedOld) := by
  let e : ∀ j, (X.mul Y).embedOld.Leg j ≃ (X.embedOld.mul Y.embedOld).Leg j
    | none => (Equiv.punitProd PUnit).symm
    | some i => Equiv.refl _
  exact reindex_equivalent e fun _ => rfl

end Raw

variable [Fintype I] [CommSemiring K]

/-- The old restriction class on the enlarged site set. -/
def embedOldClass : TensorClass.{v} I K → TensorClass.{v} (Option I) K :=
  Quotient.map Raw.embedOld fun _ _ h => ⟨Raw.embedOld_restricts h.1, Raw.embedOld_restricts h.2⟩

@[simp] theorem embedOldClass_ofRaw (X : Raw.{v} I K) :
    embedOldClass (ofRaw X) = ofRaw X.embedOld := rfl

theorem embedOldClass_mono : Monotone (embedOldClass (I := I) (K := K)) :=
  fun X Y => Quotient.inductionOn₂ X Y fun _ _ => Raw.embedOld_restricts

@[simp] theorem embedOldClass_one [Nonempty I] :
    embedOldClass (1 : TensorClass.{v} I K) = 1 :=
  ofRaw_eq_iff.mpr Raw.embedOld_one_equivalent

@[simp] theorem embedOldClass_mul [Nonempty I] (X Y : TensorClass.{v} I K) :
    embedOldClass (X * Y) = embedOldClass X * embedOldClass Y :=
  Quotient.inductionOn₂ X Y fun x y => ofRaw_eq_iff.mpr (Raw.embedOld_mul_equivalent x y)

/-- Restriction order on the old classes is preserved and reflected. -/
@[simp] theorem embedOldClass_le_iff [Nonempty I] (X Y : TensorClass.{v} I K) :
    embedOldClass X ≤ embedOldClass Y ↔ X ≤ Y :=
  Quotient.inductionOn₂ X Y fun _ _ => Raw.embedOld_restricts_iff

theorem embedOldClass_injective [Nonempty I] : Function.Injective (embedOldClass.{v} (I := I) (K := K)) := by
  intro X Y h
  exact le_antisymm ((embedOldClass_le_iff _ _).1 h.le) ((embedOldClass_le_iff _ _).1 h.ge)

section Field

variable {I : Type u} {K : Type w} [Fintype I] [Nonempty I] [Field K]

omit [Nonempty I] in
theorem embedOldClass_ne_zero_iff (X : TensorClass.{v} I K) :
    embedOldClass X ≠ 0 ↔ X ≠ 0 := by
  induction X using Quotient.inductionOn with | _ X =>
    change ofRaw X.embedOld ≠ 0 ↔ ofRaw X ≠ 0
    simp only [ne_eq, ofRaw_eq_zero_iff]
    exact X.embedOld_coeff_ne_zero_iff

/-- Adjoining the new scalar leg gives an additive homomorphism in log-product notation. -/
def embedOldProduct : NonzeroProduct.{v} I K →+ NonzeroProduct.{v} (Option I) K where
  toFun x := Additive.ofMul ⟨embedOldClass (classOfProduct x),
    (embedOldClass_ne_zero_iff _).2 x.toMul.property⟩
  map_zero' := Subtype.ext embedOldClass_one
  map_add' _ _ := Subtype.ext (embedOldClass_mul _ _)

@[simp] theorem classOfProduct_embedOldProduct (x : NonzeroProduct.{v} I K) :
    classOfProduct (embedOldProduct x) = embedOldClass (classOfProduct x) := rfl

theorem embedOldProduct_injective :
    Function.Injective (embedOldProduct.{v} (I := I) (K := K)) := by
  intro X Y heq
  apply Subtype.ext
  apply embedOldClass_injective
  exact congrArg classOfProduct heq

end Field

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
