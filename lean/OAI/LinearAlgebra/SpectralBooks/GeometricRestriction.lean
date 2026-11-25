import OAI.LinearAlgebra.SpectralBooks.PolynomialOverhead
import OAI.LinearAlgebra.SpectralBooks.RestrictionProfiles
import OAI.LinearAlgebra.SpectralBooks.ScalarSpanDescent
import OAI.LinearAlgebra.SpectralBooks.SpanValue

/-! # Ground-field spectral values respect geometric border restriction

In a tensor power of fixed format the matrix-entry profiles give polynomially
many restrictions defined over the ground field. Their linear span contains
the powers of all restrictions over the extension field and consequently
of their Zariski closure. Descending span membership and taking powers
bounds the value at each individual spectral point of the ground field.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor

open scoped NNReal

universe v

variable {I K E : Type*} [Fintype I] [Nonempty I] [Field K] [Field E] [Algebra K E]
    {A B : I → Type v} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

omit [Nonempty I] in
/-- The power of a geometric degeneration of `S` belongs to the ground-field
span of the profile restrictions in every degree. -/
theorem groupedPower_mem_span_of_geometric_restriction (T : (∀ i, B i) → K) (S : (∀ i, A i) → K)
    (hTS : (fun b ↦ algebraMap K E (T b)) ∈ affineZariskiClosure
      {Y | Crossing.IsRestriction Y (fun a ↦ algebraMap K E (S a))}) (n : ℕ) :
    groupedPower n T ∈ Submodule.span K (Set.range (profileRestriction (B := B) n S)) := by
  classical
  apply mem_span_of_map_mem_span (E := E)
  let U := Submodule.span E (Set.range (fun p : RestrictionProfile A B n ↦
    fun x ↦ algebraMap K E (profileRestriction n S p x)))
  let f (b : ∀ i, Fin n → B i) : MvPolynomial (∀ i, B i) E := ∏ j, MvPolynomial.X (fun i ↦ b i j)
  have hmap : Set.MapsTo (fun Y w ↦ MvPolynomial.eval Y (f w))
      {Y | Crossing.IsRestriction Y (fun a ↦ algebraMap K E (S a))} (U : Set _) := by
    intro Y hY
    have heval : (fun w ↦ MvPolynomial.eval Y (f w)) = groupedPower n Y := by
      funext w
      simp [f, groupedPower, coordinatePower]
    change (fun w ↦ MvPolynomial.eval Y (f w)) ∈ U
    rw [heval]
    exact groupedPower_mem_span_profileRestrictions n S hY
  have hh := mapsTo_affineZariskiClosure_of_polynomial f hmap hTS
  simpa [affineZariskiClosure_submodule, groupedPower, coordinatePower, f, U] using hh

/-- If a tensor belongs after scalar extension to the Zariski closure of the
sitewise linear restrictions of another tensor, its value at every spectral
point of the ground field is bounded by the value of the source. -/
theorem coeffValue_le_of_geometric_restriction
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{v} I K → _ → Prop))
    (T : (∀ i, B i) → K) (S : (∀ i, A i) → K)
    (hTS : (fun b ↦ algebraMap K E (T b)) ∈ affineZariskiClosure
      {Y | Crossing.IsRestriction Y (fun a ↦ algebraMap K E (S a))}) :
    coeffValue φ T ≤ coeffValue φ S := by
  classical
  apply nnreal_le_of_pow_le_polynomial_mul_pow (Fintype.card (Σ i, B i × A i))
  intro n _
  have hb (p : RestrictionProfile A B n) :
      coeffValue φ (profileRestriction n S p) ≤ coeffValue φ S ^ n := by
    rw [← coeffValue_groupedPower φ n S]
    exact φ.2.2.2.2.2 _ _ (ofRaw_le_iff.mpr (profileRestriction_restricts n S p))
  have ht := coeffValue_span_le φ (profileRestriction n S)
    (groupedPower_mem_span_of_geometric_restriction T S hTS n) hb
  simpa [RestrictionProfile, coeffValue_groupedPower] using ht

end SiteTensor

end SpectralBooks
end LinearAlgebra
end OAI
