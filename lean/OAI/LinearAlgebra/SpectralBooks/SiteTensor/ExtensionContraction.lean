import OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionGenerator
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionMatrix
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.ExtensionPower
import OAI.LinearAlgebra.SpectralBooks.RawPriceTransport

/-! # Contraction prices for the two wires through the new party

A contraction yields an arbitrary matrix on the two old endpoints. Both the
row-label and the column-label wire supply this matrix. When the two label
types agree, the equality covector attains the old wire.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped BigOperators Classical NNReal
noncomputable section

namespace SiteTensor

variable {I : Type} {K : Type*} [Fintype I] [Nonempty I] [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} I K → _ → Prop))

omit [Nonempty I] in
private theorem contractNew_newStar_eq (a b : I) (A B : Type) [Fintype A] [Fintype B]
    (ξ : A × B → K) :
    (Raw.newStar K a b A B).contractNew ξ =
      Raw.endpointMatrix a b A B (fun s t ↦ ξ (s,t)) := by
  exact congrArg (Raw.mk _ _) (funext (Raw.contractNew_newStar_coeff K a b A B ξ))

/-- Every covector on the two new-party wires yields a matrix supplied by
either old endpoint wire. -/
theorem contractionPrice_newStar_le (a b : I) (A B : Type) [Fintype A] [Fintype B] :
    contractionPrice φ (Raw.newStar K a b A B) ≤
      min (rawLogPrice φ 1 ((Raw.diagonal (Fin 2) K A).group ![a,b]))
          (rawLogPrice φ 1 ((Raw.diagonal (Fin 2) K B).group ![a,b])) := by
  apply ciSup_le
  intro ξ
  rw [contractNew_newStar_eq a b A B ξ]
  exact le_min (rawLogPrice_mono φ zero_le_one (Raw.endpointMatrix_restricts_leftWire a b _))
    (rawLogPrice_mono φ zero_le_one (Raw.endpointMatrix_restricts_rightWire a b _))

/-- Choosing the equality covector on a pair of wires with the same label
space realizes exactly the old wire joining their other endpoints. -/
theorem contractionPrice_newStar_self (a b : I) (A : Type) [Fintype A] :
    contractionPrice φ (Raw.newStar K a b A A) =
      rawLogPrice φ 1 ((Raw.diagonal (Fin 2) K A).group ![a,b]) := by
  apply le_antisymm ((contractionPrice_newStar_le φ a b A A).trans (min_le_left _ _))
  let ξ (s : A × A) : K := if s.1 = s.2 then 1 else 0
  have h := le_contractionPrice φ (Raw.newStar K a b A A) ξ
  rw [contractNew_newStar_eq, rawLogPrice, Raw.ofRaw_endpointMatrix_diagonal] at h
  exact h

private theorem logPrice_wire_power (a b : I) (n : ℕ) :
    rawLogPrice φ 1 ((Raw.diagonal (Fin 2) K (Fin n → Fin 2)).group ![a,b]) =
      n * rawWireDistance φ 1 a b := by
  rw [rawLogPrice, ofRaw_group_diagonal_fun_fin]
  change 1 * Real.logb 2 (normalizedSpectrum.toRingHom φ (_ ^ n) : ℝ≥0) = _
  rw [map_pow, NNReal.coe_pow, Real.logb_pow, one_mul]
  simp [rawWireDistance, rawLogPrice, normalizedSpectrum.toRingHom]

private theorem ofRaw_newStar_words (a b : I) (m n : ℕ) :
    ofRaw (Raw.newStar K a b (Fin m → Fin 2) (Fin n → Fin 2)) =
      ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some a]) ^ m *
      ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some b]) ^ n := by
  rw [ofRaw_newStar, ofRaw_group_diagonal_fun_fin, ofRaw_group_diagonal_fun_fin]

/-- The smaller of the two wire multiplicities bounds the old contraction
price in units of the old endpoint distance. -/
theorem classContractionPrice_wire_powers_le (a b : I) (m n : ℕ) :
    classContractionPrice φ
      (ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some a]) ^ m *
       ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some b]) ^ n) ≤
      min (m : ℝ) n * rawWireDistance φ 1 a b := by
  rw [← ofRaw_newStar_words]
  have h := contractionPrice_newStar_le φ a b (Fin m → Fin 2) (Fin n → Fin 2)
  have hdist : 0 ≤ rawWireDistance φ 1 a b := rawLogPrice_nonneg φ zero_le_one _
  rw [logPrice_wire_power, logPrice_wire_power, ← min_mul_of_nonneg _ _ hdist] at h
  exact h

/-- Equal powers of the new wires attain the prescribed old distance. -/
theorem classContractionPrice_wire_powers_self (a b : I) (m : ℕ) :
    classContractionPrice φ
      (ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some a]) ^ m *
       ofRaw ((Raw.diagonal (Fin 2) K (Fin 2)).group ![none,some b]) ^ m) =
      (m : ℝ) * rawWireDistance φ 1 a b := by
  rw [← ofRaw_newStar_words]
  exact (contractionPrice_newStar_self φ a b (Fin m → Fin 2)).trans
    (logPrice_wire_power φ a b m)

end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
