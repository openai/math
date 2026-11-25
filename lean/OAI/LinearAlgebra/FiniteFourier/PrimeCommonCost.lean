import OAI.LinearAlgebra.FiniteFourier.PrimeCommonCostPhase
import OAI.LinearAlgebra.FiniteFourier.PrimeCommonKernel
import OAI.LinearAlgebra.FiniteFourier.PrimeEndpointCost
import OAI.LinearAlgebra.FiniteFourier.PrimeTemplatePass

/-! # Cost of the charged common kernel

In coordinates for the pairing, the quadratic kernel is a transform on the
two sets of `D` common axes, with input and output chirps. It acts independently
on the fibers indexed by the spectator coordinates.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

variable {ℓ f F D : ℕ} [NeZero ℓ] {K : Type*} [CommRing K] [Invertible (ℓ : K)] {ζ : K}
variable {T : Type} [Fintype T]

/-- In dual coordinates the charged common kernel needs two calls per common
dimension. The normalization and chirps are diagonal matrix factors. -/
theorem primeTemplate_commonKernel_dot (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ)
    (hF : 0 < 2 * D → ℓ ^ ((2 * D - 1) * f) * Fintype.card T = F) :
    PrimeTemplateProgram ℓ f F ζ
      (primeCommonKernel (C := Fin f) (T := T) (V := Fin D → ZMod ℓ) hζ
        (dotProductBilin (ZMod ℓ) (ZMod ℓ)) a D) 0 (2 * D) := by
  classical
  let pi := (primeCommonPack (ℓ := ℓ) (f := f) (D := D)).prodCongr (Equiv.refl T)
  let po := ((primeCommonSwapScale (f := f) (D := D) a⁻¹).trans primeCommonPack).prodCongr
    (Equiv.refl T)
  let norm := (⅟(ℓ : K)) ^ (f * D)
  let w (x : PrimeCommonPair ℓ f D × T) := primeCommonChirp hζ a x.1
  have hp := ((primeTemplate_partialTransform ζ (2*D) T hF).reindex po.symm pi.symm).diagonal
    (fun x => norm * w x) w
  convert hp using 1
  ext ⟨o,u⟩ ⟨i,v⟩
  change (if v = u then _ * digitPhase hζ _ else 0) = (norm * w (o,u)) *
    (w (i,v) * (if u = v then primeTransform ℓ ((2*D)*f) ζ
      (primeCommonPack (primeCommonSwapScale a⁻¹ o)) (primeCommonPack i) else 0))
  by_cases huv : u = v
  · simp only [huv, ite_true, Fintype.card_fin]
    change norm * digitPhase hζ (↑(a⁻¹) * ∑ c, ∑ d,
      (i.1 c d - o.1 c d) * (o.2 c d - i.2 c d)) = _
    rw [primeCommonChirp_factor hζ a o i]
    simp only [w, mul_assoc]
  · simp [huv, Ne.symm huv]

/-- Arbitrary paired coordinate charts identifying the source pairing with a
dot product give the same template on the original register type. -/
theorem primeTemplate_commonKernel {V : Type} [AddCommGroup V] [Module (ZMod ℓ) V]
    (hζ : IsPrimitiveRoot ζ ℓ) (a : (ZMod ℓ)ˣ)
    (B : V →ₗ[ZMod ℓ] V →ₗ[ZMod ℓ] ZMod ℓ)
    (p q : V ≃ₗ[ZMod ℓ] (Fin D → ZMod ℓ)) (hpq : ∀ x y, p x ⬝ᵥ q y = B x y)
    (hF : 0 < 2 * D → ℓ ^ ((2 * D - 1) * f) * Fintype.card T = F) :
    PrimeTemplateProgram ℓ f F ζ
      (primeCommonKernel (C := Fin f) (T := T) hζ B a D) 0 (2 * D) := by
  classical
  let e := primeCommonChart (C := Fin f) (T := T) p q
  have h := (primeTemplate_commonKernel_dot hζ a hF).reindex e.symm e.symm
  exact primeCommonKernel_chart (C := Fin f) (T := T) hζ a D B (dotProductBilin (ZMod ℓ) (ZMod ℓ)) p q hpq ▸ h

end

end

end FiniteFourier
end LinearAlgebra
end OAI
