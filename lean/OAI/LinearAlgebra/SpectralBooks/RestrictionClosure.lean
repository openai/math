import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Restriction
import OAI.LinearAlgebra.SpectralBooks.ZariskiCurve

/-! # Zariski closure under local linear maps -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- A local linear map of the target preserves membership in the Zariski
closure of restrictions of the source. Its coordinates are linear polynomials
in the intermediate tensor's coefficients. -/
theorem mem_restrictionClosure_of_isRestriction {K I : Type*} [Field K] [Fintype I]
    {A B C : I → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
    {X : (∀ i, A i) → K} {Y : (∀ i, B i) → K} {Z : (∀ i, C i) → K}
    (hZY : Crossing.IsRestriction Z Y)
    (hYX : Y ∈ affineZariskiClosure {T | Crossing.IsRestriction T X}) :
    Z ∈ affineZariskiClosure {T | Crossing.IsRestriction T X} := by
  classical
  obtain ⟨M, hM⟩ := hZY
  let p (c : ∀ i, C i) := ∑ b : (∀ i, B i),
    MvPolynomial.X b * MvPolynomial.C (∏ i, M i (c i) (b i))
  have heval (T : (∀ i, B i) → K) (c : ∀ i, C i) :
      MvPolynomial.eval T (p c) = ∑ b, T b * ∏ i, M i (c i) (b i) := by simp [p]
  have hm : Set.MapsTo (fun T c ↦ MvPolynomial.eval T (p c))
      {T | Crossing.IsRestriction T X} {T | Crossing.IsRestriction T X} := by
    intro T hT
    exact SiteTensor.restrict_trans ⟨M, heval T⟩ hT
  have hz : Z = (fun c ↦ MvPolynomial.eval Y (p c)) :=
    funext fun c ↦ (hM c).trans (heval Y c).symm
  exact hz ▸ mapsTo_affineZariskiClosure_of_polynomial p hm hYX

end SpectralBooks
end LinearAlgebra
end OAI
