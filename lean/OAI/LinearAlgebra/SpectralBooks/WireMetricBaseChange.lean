import OAI.LinearAlgebra.SpectralBooks.CopyLabelGroundField
import OAI.LinearAlgebra.SpectralBooks.FinitePlaneCriterion
import Mathlib.Algebra.Algebra.ZMod

/-! # Characteristic invariance of the tree four-point condition

Restriction and extension of a spectral point preserve its entire matrix of
binary wire distances. In particular a witness over the algebraic closure of
the prime field gives a witness over each field of that characteristic.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open SiteTensor

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Pullback along the field map preserves every binary wire distance. -/
theorem rawWireDistance_pullbackSpectrum {J : Type} [Fintype J] [Nonempty J]
    (ψ : normalizedSpectrum (S := TensorClass.{0} J L) (· ≤ ·)) (c : ℝ) (s t : J) :
    rawWireDistance (pullbackSpectrum (algebraMap K L) ψ) c s t = rawWireDistance ψ c s t := by
  simp only [rawWireDistance, rawLogPrice, pullbackSpectrum_apply, mapScalars_ofRaw,
    Raw.mapScalars_group_diagonal]

/-- A non-tree witness exists over the extension precisely when one exists
over the ground field. Both directions keep the same finite set of sites. -/
theorem hasNonTreeWireMetric_baseChange (K L : Type*) [Field K] [Field L] [Algebra K L] :
    HasNonTreeWireMetric K ↔ HasNonTreeWireMetric L := by
  constructor
  · rintro ⟨J, _, _, φ, a, b, z, w, h⟩
    obtain ⟨ψ, hψ⟩ := exists_spectrum_mapScalars (K := L) φ
    have heq : pullbackSpectrum (algebraMap K L) ψ = φ := Subtype.ext (funext hψ)
    refine ⟨J, inferInstance, inferInstance, ψ, a, b, z, w, ?_⟩
    simpa only [← heq, rawWireDistance_pullbackSpectrum] using h
  · rintro ⟨J, _, _, ψ, a, b, z, w, h⟩
    refine ⟨J, inferInstance, inferInstance, pullbackSpectrum (algebraMap K L) ψ, a, b, z, w, ?_⟩
    simpa only [rawWireDistance_pullbackSpectrum] using h

/-- The tree four-point condition on normalized spectral points is a property
of the characteristic, including in characteristic zero. -/
theorem hasNonTreeWireMetric_iff_of_ringChar_eq {K L : Type*} [Field K] [Field L]
    (hchar : ringChar K = ringChar L) : HasNonTreeWireMetric K ↔ HasNonTreeWireMetric L := by
  by_cases hzero : ringChar K = 0
  · let : CharZero K := (CharP.ringChar_zero_iff_CharZero K).mp hzero
    let : CharZero L := (CharP.ringChar_zero_iff_CharZero L).mp (hchar.symm.trans hzero)
    exact (hasNonTreeWireMetric_baseChange ℚ K).symm.trans (hasNonTreeWireMetric_baseChange ℚ L)
  · let : Fact (ringChar K).Prime :=
      ⟨(CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hzero⟩
    let : CharP L (ringChar K) := ringChar.eq_iff.mp hchar.symm
    let : Algebra (ZMod (ringChar K)) K := ZMod.algebra _ _
    let : Algebra (ZMod (ringChar K)) L := ZMod.algebra _ _
    exact (hasNonTreeWireMetric_baseChange (ZMod (ringChar K)) K).symm.trans
      (hasNonTreeWireMetric_baseChange (ZMod (ringChar K)) L)

end SpectralBooks
end LinearAlgebra
end OAI
