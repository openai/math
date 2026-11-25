import OAI.LinearAlgebra.FiniteFourier.Deformation.DyadicDeformationTransport

/-! # Split multiplication for the dyadic protected cover

Both operands undergo the same diagonal change at one, Taylor lift,
diagonal change at zero, and tensor Fourier transform. All transform
entries and inverse transform entries come from the base coefficient ring.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation.Dyadic

open Polynomial Matrix
open scoped BigOperators

variable {R σ : Type*} [CommRing R] [Fintype σ]

/-- A single precomputed jet multiplier at each address. -/
def scaleLinear (m : σ → ℕ) (w : σ → Rˣ) : (Address m → R) →ₗ[R] (Address m → R) :=
  LinearMap.pi fun k => (∏ i, (w i : R) ^ (k i).val) • LinearMap.proj k

@[simp] theorem scaleLinear_apply (m : σ → ℕ) (w : σ → Rˣ) (x : Address m → R) :
    scaleLinear m w x = scale m w x := rfl

variable [DecidableEq σ]

/-- The common linear map to the pointwise products, using a tensor transform over the base. -/
noncomputable def transformInput (m : σ → ℕ) {r H : ℕ} (u : σ → (Jet R r)ˣ)
    (v : σ → (Jet R H)ˣ) (ζ : ∀ i, Fin (m i) → R) :
    (Address m → Jet R r) →ₗ[R] (Address m → Jet R H) :=
  (((evaluation m ζ).map (algebraMap R (Jet R H))).mulVecLin.restrictScalars R).comp <|
    ((scaleLinear m v).restrictScalars R).comp <|
    (((specialize 0 H).toLinearMap.comp (liftJet 1 r)).compLeft (Address m)).comp
      ((scaleLinear m (fun i => (u i)⁻¹)).restrictScalars R)

/-- Invert the base transform, undo the scaling at zero, read the product at one,
and return to the original monomial coordinates. -/
noncomputable def transformOutput (m : σ → ℕ) {r H : ℕ} (u : σ → (Jet R r)ˣ)
    (v : σ → (Jet R H)ˣ) (ζ : ∀ i, Fin (m i) → R) :
    (Address m → Jet R H) →ₗ[R] (Address m → Jet R r) :=
  ((scaleLinear m u).restrictScalars R).comp <|
    ((readAtOne H r).compLeft (Address m)).comp <|
    ((scaleLinear m (fun i => (v i)⁻¹)).restrictScalars R).comp
      (((interpolation m ζ).map (algebraMap R (Jet R H))).mulVecLin.restrictScalars R)

private theorem interpolate_base {A : Type*} [CommRing A] (φ : R →+* A) (m : σ → ℕ)
    (ζ : ∀ i, Fin (m i) → R) (hζ : ∀ i j, ζ i j ^ m i = 1)
    (hd : ∀ i, Pairwise fun j k => IsUnit (ζ i j - ζ i k)) (x y : Address m → A) :
    (interpolation m ζ).map φ *ᵥ
      (((evaluation m ζ).map φ *ᵥ x) * ((evaluation m ζ).map φ *ᵥ y)) =
        multiply (coeff (fun _ => 1) m) x y := by
  have he : (evaluation m ζ).map φ = evaluation m (fun i j => φ (ζ i j)) := by
    ext
    simp [evaluation, gridTensor, vandermonde_apply]
  have hinv : (interpolation m ζ).map φ * (evaluation m ζ).map φ = 1 := by
    change φ.mapMatrix _ * φ.mapMatrix _ = _
    rw [← map_mul, interpolation_evaluation m ζ hd, map_one]
  rw [he] at hinv ⊢
  rw [← evaluation_multiply (fun _ => 1) m _ (fun i j => by rw [← map_pow, hζ, map_one]),
    mulVec_mulVec, hinv, one_mulVec]

/-- Dyadic block multiplication at jet length `r` reduces to one pointwise
product per active address at length `2*r + card σ`. The surrounding maps
are built from the base-ring Fourier matrices, fixed jet scalings, and shifts. -/
theorem split_product (r : ℕ) (hr : 0 < r) (m : σ → ℕ) (β : σ → Rˣ)
    (hm : ∀ i, IsUnit (m i : R)) (ζ : ∀ i, Fin (m i) → R)
    (hζ : ∀ i j, ζ i j ^ m i = 1) (hd : ∀ i, Pairwise fun j k => IsUnit (ζ i j - ζ i k)) :
    let H := 2*r + Fintype.card σ
    ∃ (u : σ → (Jet R r)ˣ) (v : σ → (Jet R H)ˣ),
      ∀ x y : Address m → Jet R r,
        transformOutput m u v ζ (transformInput m u v ζ x * transformInput m u v ζ y) =
          multiply (coeff (fun i => algebraMap R (Jet R r) (β i : R)) m) x y := by
  let H := 2*r + Fintype.card σ
  let βR (i : σ) : R := β i
  let B (i : σ) := algebraMap R (Jet R r) (βR i)
  let B0 (i : σ) := specialize 0 H (binomial (βR i))
  let B1 (i : σ) := specialize 1 r (binomial (βR i))
  let L := specialize (0 : R) H ∘ liftJet 1 r
  obtain ⟨v,u,hv,hu⟩ := exists_endpoint_scales r H m β hm
  refine ⟨u,v,fun x y => ?_⟩
  let x' := scale m (fun i => (u i)⁻¹) x
  let y' := scale m (fun i => (u i)⁻¹) y
  let E := (evaluation m ζ).map (algebraMap R (Jet R H))
  let I := (interpolation m ζ).map (algebraMap R (Jet R H))
  change scale m u (readAtOne H r ∘ scale m (fun i => (v i)⁻¹)
      (I *ᵥ ((E *ᵥ scale m v (L ∘ x')) * (E *ᵥ scale m v (L ∘ y'))))) =
    multiply (coeff B m) x y
  have hp := interpolate_base (algebraMap R (Jet R H)) m ζ hζ hd
    (scale m v (L ∘ x')) (scale m v (L ∘ y'))
  have h0 := scale_multiply m v (fun _ => 1) B0 (fun i => (one_mul _).trans (hv i))
    (L ∘ x') (L ∘ y')
  have h1 := scale_multiply m u B B1 hu x' y'
  rw [hp, ← h0, inverse_scale, recover r hr βR m x' y', h1]
  simp [x', y']

end Deformation.Dyadic

end FiniteFourier
end LinearAlgebra
end OAI
