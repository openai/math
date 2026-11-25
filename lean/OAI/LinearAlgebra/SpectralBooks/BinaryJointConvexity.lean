import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Joint
import OAI.LinearAlgebra.SpectralBooks.PlacedDiagonal

/-! # Joint convexity of placed binary diagonals

The coupled relocation bound for general tensors specializes to the common
binary label. Its synchronized coupling gives the geodesic price inequality.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace SiteTensor
open Relocation

variable {J : Type} [Fintype J] [Nonempty J] {K : Type*} [Field K] {r : ℕ}

/-- Binary diagonal placement prices are bounded by every coupling of the
prescribed interval parameters. -/
theorem binaryDiagonal_coupled_relocation
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ) (hc : 0 < c)
    (a z b : Fin r → J) (t : Fin r → ℝ) (ht : ∀ i, t i ∈ Set.Icc 0 1)
    (hza : ∀ i, rawWireDistance φ c (z i) (a i) = t i * rawWireDistance φ c (a i) (b i))
    (hzb : ∀ i, rawWireDistance φ c (z i) (b i) = (1-t i) * rawWireDistance φ c (a i) (b i))
    (π : CubeTable r) (hπ : CubeTable.IsCoupling π t) :
    rawLogPrice φ c ((Raw.diagonal (Fin r) K (Fin 2)).group z) ≤ CubeTable.cost π
      (fun e ↦ rawLogPrice φ c ((Raw.diagonal (Fin r) K (Fin 2)).group (cornerAt a b e))) :=
  rawLogPrice_coupled_relocation φ c hc.le _ a z b t ht hza hzb π hπ

/-- Synchronized placement convexity of the binary diagonal, over every field. -/
theorem rawDiagonalJointConvexity (K : Type*) [Field K] : RawDiagonalJointConvexity K := by
  intro J _ _ φ c hc r _ a z b t ht hza hzb
  let T := Raw.diagonal (Fin r) K (Fin 2)
  let M : CubeTable r := fun e ↦ rawLogPrice φ c (T.group (cornerAt a b e))
  have h := CubeTable.synchronized_of_forall_couplings (M := M) ht
    (binaryDiagonal_coupled_relocation φ c hc a z b (fun _ ↦ t) (fun _ ↦ ht) hza hzb)
  have h0 : cornerAt a b (fun _ ↦ false) = a := rfl
  have h1 : cornerAt a b (fun _ ↦ true) = b := rfl
  simpa only [M, h0, h1, T] using h


end SiteTensor

end

end SpectralBooks
end LinearAlgebra
end OAI
