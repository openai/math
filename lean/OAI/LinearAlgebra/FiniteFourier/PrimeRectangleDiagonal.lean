import OAI.LinearAlgebra.FiniteFourier.PrimeRectangleTransfer
import OAI.LinearAlgebra.FiniteFourier.PrimeCommonQuery

/-! # The ordinary query on the diagonal label blocks -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section
namespace BitRoutingGeometry
variable {ℓ L b : ℕ} [Fact ℓ.Prime] (G : BitRoutingGeometry ℓ L b)

/-- Matrix entries are independent of the chosen finite enumeration and decision procedure. -/
theorem toMatrixEntry_congr {K I : Type*} [CommRing K]
    (d d' : DecidableEq I) (f f' : Fintype I) (M : Module.End K (I → K)) (x y : I) :
    (@LinearMap.toMatrix' K _ I I d f M) x y = (@LinearMap.toMatrix' K _ I I d' f' M) x y := by
  cases Subsingleton.elim d d'
  cases Subsingleton.elim f f'
  rfl

/-- On its own label the transfer is the ordinary query power. -/
theorem transfer_self {K : Type*} [CommRing K] [Invertible (ℓ : K)] {ζ : K}
    (hζ : IsPrimitiveRoot ζ ℓ) [PrimeSpectrumOrthogonal hζ] {m : ℕ} (f : ℕ) (a : (ZMod ℓ)ˣ) (j : Fin m) (v : BitLabel L b) :
    G.transfer hζ f a j v v =
      ((primeSpectrumQuery hζ (fun ω : G.RowAddress m f => primeCommonQueryExponents ω j)) ^
        (a : ZMod ℓ).val).toMatrix' := by
  have hd := G.dim_pos
  have hdim : Fintype.card (Unit ⊕ Fin (G.D-1)) = G.D := by simp; omega
  have h := primeCommonKernel_eq_queryPower (C := Fin f) hζ G.form _ _
      (primeCommonLabelMap_pair _ _ _ (G.labelCharts v).pair) j a
  simp only [hdim] at h
  ext x y
  rw [transfer, queryChart, h]
  exact toMatrixEntry_congr _ _ _ _ _ _ _

end BitRoutingGeometry
end

end

end FiniteFourier
end LinearAlgebra
end OAI
