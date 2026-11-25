import OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionContraction
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionPlacement
import OAI.LinearAlgebra.SpectralBooks.CutSpectrum

/-! # Wire generators for inserting an interval point -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Classical NNReal
noncomputable section

namespace SiteTensor

variable {I : Type} {K : Type*} [Fintype I] [Nonempty I] [Field K]

/-- The binary wire from the new party to an old site. -/
def intervalWire (K : Type*) [Field K] (a : I) : NonzeroProduct.{0} (Option I) K := by
  let W := Raw.diagonal (Fin 2) K (Fin 2)
  have hn : W.coeff ≠ 0 := by
    intro he
    have h : W.coeff (fun _ => (0 : Fin 2)) = (0 : K) := congrFun he (fun _ => (0 : Fin 2))
    simp [W, Raw.diagonal, funext_iff] at h
  let X := W.group ![none, some a]
  exact Additive.ofMul ⟨ofRaw X, fun h ↦ (W.group_ne_zero_iff _).mpr hn ((ofRaw_eq_zero_iff X).mp h)⟩

@[simp] theorem classOfProduct_intervalWire (a : I) :
    classOfProduct (intervalWire K a) =
      ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none, some a]) := rfl

variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))

theorem contractionPrice_intervalWires_le (a b : I) (m n : ℕ) :
    classContractionPrice φ (classOfProduct (m • intervalWire K a + n • intervalWire K b)) ≤
      min (m : ℝ) n * rawWireDistance φ 1 a b :=
  classContractionPrice_wire_powers_le φ a b m n

theorem contractionPrice_intervalWires_equal (a b : I) (m : ℕ) :
    classContractionPrice φ (classOfProduct (m • intervalWire K a + m • intervalWire K b)) =
      m * rawWireDistance φ 1 a b :=
  classContractionPrice_wire_powers_self φ a b m

/-- Agreement on old products gives agreement on every old raw tensor, including zero. -/
theorem group_some_logPrice_of_old_logPoint
    (ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I) K → _ → Prop))
    (hold : ∀ X, logPoint ψ (embedOldProduct X) = logPoint φ X) (T : Raw.{0} I K) :
    rawLogPrice ψ 1 (T.group some) = rawLogPrice φ 1 T := by
  by_cases h : T.coeff = 0
  · have hh : (T.group some).coeff = 0 := not_not.mp (fun hn => ((T.group_ne_zero_iff some).mp hn) h)
    rw [rawLogPrice_zero _ _ _ h, rawLogPrice_zero _ _ _ hh]
  let X : NonzeroProduct.{0} I K := Additive.ofMul ⟨ofRaw T, fun he => h ((ofRaw_eq_zero_iff _).mp he)⟩
  have he := hold X
  change Real.logb 2 (ψ.val (ofRaw T.embedOld) : ℝ) = Real.logb 2 (φ.val (ofRaw T) : ℝ) at he
  simpa only [rawLogPrice, one_mul, ofRaw_embedOld_eq_group_some] using he

theorem logPoint_intervalWire_eq
    (ψ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Option I) K → _ → Prop)) (a : I) :
    logPoint ψ (intervalWire K a) = rawWireDistance ψ 1 none (some a) := by
  simp only [rawWireDistance, rawLogPrice, one_mul]
  rfl

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
