import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoEndpointTransport
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoEndpointSplit
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoTransportProduct
import OAI.LinearAlgebra.FiniteFourier.Deformation.AtTwoUniformHeight

/-! # The integral block product in undeformed coordinates

At the endpoint one, a sparse transport identifies the undeformed block with its
deformation over the short jet. At zero the Fourier nodes give independent products
in a common long jet. The same input transform is applied to both factors.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Matrix Polynomial

variable {R σ : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

private theorem transport_product_of_parameters {A : Type*} [CommRing A] [Nontrivial A]
    (φ ψ : R[X] →+* A) (ρ β : σ → R) (m : σ → ℕ) (hm : ∀ i, 0 < m i)
    {c b c' b' : σ → A}
    (hc : (fun i => φ (C (ρ i) * X)) = c) (hb : (fun i => φ (binomial (β i))) = b)
    (hc' : (fun i => ψ (C (ρ i) * X)) = c') (hb' : (fun i => ψ (binomial (β i))) = b')
    (e : Block m c b ≃ₐ[A] Block m c' b') (x y : Address m → A) :
    let B := blockBasis m hm c b
    let D := blockBasis m hm c' b'
    let G := LinearMap.toMatrix D B e.symm.toAlgHom.toLinearMap
    LinearMap.toMatrix B D e.toAlgHom.toLinearMap *ᵥ multiply
      (fun i j k => φ (integralCoeff ρ β m i j k)) (G *ᵥ x) (G *ᵥ y) =
      multiply (fun i j k => ψ (integralCoeff ρ β m i j k)) x y := by
  subst c b c' b'
  exact transport_block_multiply φ ψ ρ β m hm e x y

private theorem exists_shortTransport_product (r : ℕ) [Nontrivial (Jet R r)]
    (ρ : σ → R) (β : σ → Rˣ) (m : σ → ℕ) (hm : ∀ i, 0 < m i)
    (hwidth : ∀ i, IsUnit (m i : Jet R r))
    (hdisc : ∀ i, IsUnit (1 - 4 * algebraMap R (Jet R r) (ρ i))) :
    ∃ (w : σ → (Jet R r)ˣ) (a : σ → Jet R r) (b : σ → (Jet R r)ˣ)
      (a' : σ → Jet R r) (b' : σ → (Jet R r)ˣ), ∀ x y,
      let G := transportGrid m a' b' (fun i => (w i)⁻¹)
      transportGrid m a b w *ᵥ multiply (fun i j k =>
        specialize 1 r (integralCoeff ρ (fun i => (β i:R)) m i j k)) (G *ᵥ x) (G *ᵥ y) =
        multiply (fun i j k => algebraMap R (Jet R r)
          ((integralCoeff ρ (fun i => (β i:R)) m i j k).eval 1)) x y := by
  let g := algebraMap R (Jet R r)
  let z : Jet R r := AdjoinRoot.root (X ^ r)
  let φ := (specialize (1 : R) r).toRingHom
  let ψ := g.comp (evalRingHom (1 : R))
  let β' (i : σ) : (Jet R r)ˣ := Units.map g (β i)
  have hx : φ X = 1 + z := by
    change aeval _ (taylor 1 X) = _
    simp [taylor_X, z, add_comm]
  have hc (x : R) : φ (C x) = g x := (specialize (1 : R) r).commutes x
  have hq (i : σ) : φ (C (ρ i) * X) = g (ρ i) * (1 + z) := by rw [map_mul, hc, hx]
  have hb (i : σ) : φ (binomial (β i : R)) = 1 + ((β' i : Jet R r) - 1) * (1 + z) := by
    simp [binomial, hx, hc, β']
  have hq' (i : σ) : ψ (C (ρ i) * X) = g (ρ i) := by simp [ψ]
  have hb' (i : σ) : ψ (binomial (β i : R)) = (β' i : Jet R r) := by simp [ψ, binomial, β']
  obtain ⟨e, w, a, b, a', b', he, he'⟩ := exists_transportGridAtOne m hm z
    (fun i => g (ρ i)) β' (jetParameter_nilpotent R r) hwidth hdisc
  refine ⟨w, a, b, a', b', fun x y => ?_⟩
  have h := transport_product_of_parameters φ ψ ρ (fun i => (β i:R)) m hm
    (funext hq) (funext hb) (funext hq') (funext hb') e x y
  dsimp only at h
  rw [he, he'] at h
  exact h

/-- The two sparse maps at one and the Fourier-node maps at zero, with reciprocal
binomial scalings on the two sides of the near-one transport. -/
structure BlockProductTransforms (R σ : Type*) [CommRing R] (r H : ℕ) where
  transportScale : σ → (Jet R r)ˣ
  outputOffset : σ → Jet R r
  outputSlope : σ → (Jet R r)ˣ
  inputOffset : σ → Jet R r
  inputSlope : σ → (Jet R r)ˣ
  quadraticNodes : σ → Fin 2 → Jet R H
  binomialScale : σ → (Jet R H)ˣ

namespace BlockProductTransforms

variable {r H : ℕ} (T : BlockProductTransforms R σ r H) (m : σ → ℕ)
  (ζ : σ → (Jet R H)ˣ)

/-- Pull back the short-jet coordinates, shift to zero, and evaluate at the split nodes. -/
noncomputable def input (x : Address m → Jet R r) : Address m → Jet R H :=
  evaluationGrid m T.quadraticNodes (fun i => scaledNodes (m i) (T.binomialScale i) (ζ i)) *ᵥ
    ((specialize (0:R) H ∘ liftJet 1 r) ∘ (transportGrid m T.inputOffset T.inputSlope
      (fun i => (T.transportScale i)⁻¹) *ᵥ x))

/-- Interpolate pointwise products, read the short jet at one and restore the original basis. -/
noncomputable def output (x : Address m → Jet R H) : Address m → Jet R r :=
  transportGrid m T.outputOffset T.outputSlope T.transportScale *ᵥ
    (readAtOne H r ∘ (interpolationGrid m T.quadraticNodes
      (fun i => scaledNodes (m i) (T.binomialScale i) (ζ i)) *ᵥ x))

end BlockProductTransforms

/-- For each subset of at most `d` active axes the common height `2*r+2*d`
suffices for the full product. The right hand side uses the original structure
constants evaluated at one in the coefficient ring and then included as constants
in the short jet. Every split quadratic has two nodes separated by a unit. -/
theorem exists_blockProductTransforms (r d : ℕ) (hr : 0 < r) [Nontrivial (Jet R r)]
    (hd : Fintype.card σ ≤ d)
    (ρ : σ → R) (β : σ → Rˣ) (m : σ → ℕ) (hm : ∀ i, 0 < m i)
    (hs : ∀ i, IsUnit (m i : Jet R r))
    (hdisc : ∀ i, IsUnit (1 - 4 * algebraMap R (Jet R r) (ρ i)))
    (ζ : σ → (Jet R (2*r+2*d))ˣ) (hζ : ∀ i, (ζ i)^(m i) = 1)
    (hwidth : ∀ i, IsUnit (m i : Jet R (2*r+2*d)))
    (hsep : ∀ i, Pairwise fun j k : Fin (m i) =>
      IsUnit ((ζ i : Jet R (2*r+2*d))^j.val - (ζ i : Jet R (2*r+2*d))^k.val)) :
    ∃ T : BlockProductTransforms R σ r (2*r+2*d),
      (∀ i, Pairwise fun j k => IsUnit (T.quadraticNodes i j - T.quadraticNodes i k)) ∧
      ∀ x y, T.output m ζ (T.input m ζ x * T.input m ζ y) =
        multiply (fun i j k => algebraMap R (Jet R r)
          ((integralCoeff ρ (fun i => (β i:R)) m i j k).eval 1)) x y := by
  let H := 2*r+2*d
  let β₀ (i : σ) := (β i : R)
  obtain ⟨w, a, b, a', b', ht⟩ := exists_shortTransport_product r ρ β m hm hs hdisc
  obtain ⟨u, v, hu, hv, hdu, hdv⟩ := exists_scaledNodes_atZero H ρ β₀ m hwidth ζ hζ hsep
  refine ⟨⟨w, a, b, a', b', u, v⟩, hdu, fun x y => ?_⟩
  let G := transportGrid m a' b' (fun i => (w i)⁻¹)
  let lift := specialize (0:R) H ∘ liftJet 1 r
  let nodes (i : σ) := scaledNodes (m i) (v i) (ζ i)
  change transportGrid m a b w *ᵥ (readAtOne H r ∘ (interpolationGrid m u nodes *ᵥ
    ((evaluationGrid m u nodes *ᵥ (lift ∘ (G *ᵥ x))) * (evaluationGrid m u nodes *ᵥ (lift ∘ (G *ᵥ y)))))) = _
  rw [interpolate_pointwise (specialize 0 H).toRingHom ρ β₀ m u nodes hu hv hdu hdv]
  have hrec := funext (recover_integral_multiply_of_le r H hr (by dsimp [H]; omega)
    ρ β₀ m (G *ᵥ x) (G *ᵥ y))
  exact (congrArg ((transportGrid m a b w).mulVec) hrec).trans (ht x y)

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
