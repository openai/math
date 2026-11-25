import OAI.LinearAlgebra.SpectralBooks.TensorSemiring
import OAI.LinearAlgebra.SpectralBooks.Spectrum

/-! # Restricting spectral points along scalar extension

Scalar extension applies the field homomorphism to every coefficient and every
local restricting matrix. It therefore induces an order-preserving semiring
homomorphism on tensor classes. A normalized spectral point over an extension
field restricts to a normalized spectral point on the ground tensors, with
simultaneous agreement on all their evaluations.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical NNReal

namespace SiteTensor

universe v
variable {I K L : Type*} [Fintype I] [CommSemiring K] [CommSemiring L]

/-- Apply a scalar homomorphism at every coefficient in the given format. -/
def Raw.mapScalars (h : K →+* L) (X : Raw.{v} I K) : Raw.{v} I L :=
  ⟨X.Leg, X.finiteLeg, fun a => h (X.coeff a)⟩

/-- The original local restrictions supply local restrictions after applying
the homomorphism to each matrix entry. -/
theorem Raw.mapScalars_restricts (h : K →+* L) {X Y : Raw.{v} I K} (hXY : X.Restricts Y) :
    (X.mapScalars h).Restricts (Y.mapScalars h) := by
  obtain ⟨A, hA⟩ := hXY
  refine ⟨fun i x y => h (A i x y), fun x => ?_⟩
  have t := congrArg h (hA x)
  simp only [map_sum, map_mul, map_prod] at t
  exact t

private theorem map_sumCoeff {A B : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    (h : K →+* L) (X : (∀ i, A i) → K) (Y : (∀ i, B i) → K) (a : ∀ i, A i ⊕ B i) :
    h (sumCoeff X Y a) = sumCoeff (fun b => h (X b)) (fun b => h (Y b)) a := by
  simp [sumCoeff, pushCoeff, apply_ite h]

variable [Nonempty I]

/-- Scalar extension on the tensor semiring. -/
noncomputable def mapScalars (h : K →+* L) : TensorClass.{v} I K →+* TensorClass.{v} I L where
  toFun := Quotient.map (Raw.mapScalars h) fun _ _ hXY =>
    ⟨Raw.mapScalars_restricts h hXY.1, Raw.mapScalars_restricts h hXY.2⟩
  map_zero' := Quotient.sound <| Raw.reindex_equivalent (fun _ => Equiv.refl _) (fun _ => h.map_zero)
  map_one' := Quotient.sound <| Raw.reindex_equivalent (fun _ => Equiv.refl _) (fun _ => h.map_one)
  map_mul' x y := Quotient.inductionOn₂ x y fun X Y => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.refl _) fun a =>
      map_mul h (X.coeff (fun i => (a i).1)) (Y.coeff (fun i => (a i).2))
  map_add' x y := Quotient.inductionOn₂ x y fun X Y => Quotient.sound <|
    Raw.reindex_equivalent (fun _ => Equiv.refl _) fun a => map_sumCoeff h X.coeff Y.coeff a

@[simp] theorem mapScalars_ofRaw (h : K →+* L) (X : Raw.{v} I K) :
    mapScalars h (ofRaw X) = ofRaw (X.mapScalars h) := rfl

/-- Scalar extension preserves the local restriction order. -/
theorem mapScalars_mono (h : K →+* L) :
    Monotone (mapScalars (I := I) h : TensorClass.{v} I K → TensorClass.{v} I L) := by
  intro x y
  induction x using Quotient.inductionOn
  induction y using Quotient.inductionOn
  exact Raw.mapScalars_restricts h

/-- A point over the extension evaluates every extended ground tensor at the
value of its pullback point. -/
noncomputable def pullbackSpectrum (h : K →+* L)
    (f : normalizedSpectrum (fun x y : TensorClass.{v} I L => x ≤ y)) :
    normalizedSpectrum (fun x y : TensorClass.{v} I K => x ≤ y) := by
  let g := (normalizedSpectrum.toRingHom f).comp (mapScalars h)
  refine ⟨g, g.map_zero, g.map_one, g.map_add, g.map_mul, ?_⟩
  exact fun x y hxy => f.2.2.2.2.2 _ _ (mapScalars_mono h hxy)

@[simp] theorem pullbackSpectrum_apply (h : K →+* L)
    (f : normalizedSpectrum (fun x y : TensorClass.{v} I L => x ≤ y)) (X : TensorClass.{v} I K) :
    (pullbackSpectrum h f).val X = f.val (mapScalars h X) := rfl

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
