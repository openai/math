import OAI.LinearAlgebra.FiniteFourier.IntegralGridInputs
import OAI.LinearAlgebra.FiniteFourier.OpenConvolutionBilinear

/-! # Change of coefficient ring for open convolution reductions

Each output of an open reduction is bilinear in its operands. Its values on the
pairs of standard basis vectors therefore determine it after any change of ring,
including specialization to positive characteristic or extension to a polynomial ring.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace OpenConvolution

variable {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} {B : Type*} {len : B → ℕ}

/-- Apply a ring map to both linear circuits of an open reduction. -/
def mapCoeff (p : OpenConvolution R n B len) (φ : R →+* S) : OpenConvolution S n B len :=
  ⟨p.inputSize, p.outputSize, p.input.mapCoeff φ, p.output.mapCoeff φ⟩

/-- Evaluation commutes with coefficient change on inputs from the original ring. -/
theorem eval_mapCoeff (p : OpenConvolution R n B len) (φ : R →+* S)
    (x y : Fin n → R) (k : Fin (2*n-1)) :
    (p.mapCoeff φ).eval (φ ∘ x) (φ ∘ y) k = φ (p.eval x y k) := by
  have hc : (p.mapCoeff φ).children (φ ∘ x) (φ ∘ y) = φ ∘ p.children x y := by
    funext z
    change openConv S (len z.1) _ _ z.2 = φ (openConv R (len z.1) _ _ z.2)
    rw [openConv_map]
    simp only [mapCoeff, Function.comp_def, Circuit.eval_mapCoeff]
  unfold eval
  rw [hc]
  exact p.output.eval_mapCoeff φ (p.children x y) k

/-- Checking the pairs of standard basis vectors tests the entire reduction. -/
theorem realizesMultiple_iff_basis (p : OpenConvolution R n B len) (D : R) :
    p.RealizesMultiple D ↔
      ∀ i j k, p.eval (Pi.single i 1) (Pi.single j 1) k =
        D * openConv R n (Pi.single i 1) (Pi.single j 1) k := by
  refine ⟨fun h i j k => h _ _ k, ?_⟩
  intro h x y k
  have he : p.bilinear k = D • openConvBilinear R n k := by
    apply LinearMap.ext_basis (Pi.basisFun R (Fin n)) (Pi.basisFun R (Fin n))
    intro i j
    simpa only [Pi.basisFun_apply, bilinear_apply, LinearMap.smul_apply,
      openConvBilinear_apply, smul_eq_mul] using h i j k
  have hxy := DFunLike.congr_fun (DFunLike.congr_fun he x) y
  simpa only [bilinear_apply, LinearMap.smul_apply, openConvBilinear_apply, smul_eq_mul] using hxy

/-- The scaled convolution identity holds on all inputs in the new ring. -/
theorem RealizesMultiple.mapCoeff {p : OpenConvolution R n B len} {D : R}
    (h : p.RealizesMultiple D) (φ : R →+* S) : (p.mapCoeff φ).RealizesMultiple (φ D) := by
  apply (realizesMultiple_iff_basis _ _).2
  intro i j k
  have hsingle (a : Fin n) : (Pi.single a 1 : Fin n → S) = φ ∘ (Pi.single a 1 : Fin n → R) := by
    funext b
    by_cases hab : b = a <;> simp [hab]
  rw [hsingle i, hsingle j, eval_mapCoeff, h, map_mul, openConv_map]

end OpenConvolution

end FiniteFourier
end LinearAlgebra
end OAI
