import OAI.LinearAlgebra.FiniteFourier.Deformation.ConvolutionCyclotomicNodes
import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyCoordinates

/-! # Two-coordinate encoding of the jets at two -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

open Polynomial

/-- The coordinates on the quadratic order are the coefficients of one and the cube root. -/
theorem atTwoCoefficientEncoding_bijective :
    Function.Bijective (fun u : Fin 2 → TwoLocalBase =>
      algebraMap TwoLocalBase TwoLocalQuadratic (u 0) + AdjoinRoot.root (cyclotomic 3 TwoLocalBase) *
        algebraMap TwoLocalBase TwoLocalQuadratic (u 1)) :=
  quadratic_root_coordinates_bijective (cyclotomic.monic 3 TwoLocalBase)
    (by rw [natDegree_cyclotomic]; decide)

/-- Fixed linear assembly around three ordinary products in the two-local jet. -/
theorem atTwoJetCircuitsOver {M h : ℕ} (hM : 0 < M) (hh : 0 < h) :
    JetCircuitsOver (algebraMap TwoLocalBase TwoLocalQuadratic) (AdjoinRoot.root (cyclotomic 3 TwoLocalBase))
      (cyclotomic M TwoLocalQuadratic) M.totient h := by
  simpa only [map_cyclotomic] using (eisenstein_cyclotomicJet_circuits TwoLocalBase hM hh).toOver

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
