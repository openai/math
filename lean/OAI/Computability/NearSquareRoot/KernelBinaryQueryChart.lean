import OAI.Computability.NearSquareRoot.KernelBinaryQueries
import OAI.LinearAlgebra.FiniteFourier.PrimeCommonPhysicalQuery

/-! # The active coordinates and spectators of a binary column query -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BinaryQuery
open OAI.LinearAlgebra.FiniteFourier KernelPass KernelNormalization Matrix
noncomputable section

variable {E : Type} [AddCommGroup E] [Module (ZMod 2) E] {m u : ℕ}

def physicalChart (j : Fin (m+1)) (p q : E ≃ ZMod 2 × (Fin u → ZMod 2)) :
    Bits (Arity (m+1) u) ≃ ((Fin 1 → E) × (Fin 1 → E)) × EndpointDigitPairs (Fin 1) (Fin m) (ZMod 2) :=
  (halves (m+1) u).trans (endpointDigitCurry.trans (endpointQueryPhysicalChart j p q))

/-- The column query is exactly the active common kernel on the selected
pair and all auxiliary positions. Every other distinguished pair is fixed. -/
theorem physical_query (j : Fin (m+1)) (B : E →ₗ[ZMod 2] E →ₗ[ZMod 2] ZMod 2)
    (p q : E ≃ₗ[ZMod 2] ZMod 2 × (Fin u → ZMod 2))
    (hpq : ∀ x y, B x y = (p x).1 * (q y).1 + ∑ k, (p x).2 k * (q y).2 k) :
    query (u:=u) j = (primeCommonKernel binaryRoot B 1 (u+1)).submatrix
      (physicalChart j p.toEquiv q.toEquiv) (physicalChart j p.toEquiv q.toEquiv) := by
  ext y x
  have eq := primeCommonKernel_physical_queryPower (C:=Fin 1) binaryRoot B p q hpq j (1 : (ZMod 2)ˣ)
  simp only [Units.val_one, ZMod.val_one, pow_one] at eq
  have en := congrFun (congrFun eq (halves (m+1) u y)) (halves (m+1) u x)
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1 u,
    LinearMap.toMatrix'_apply, query, localize_apply, physicalChart, Equiv.trans_apply,
    primeCommonQueryExponents, Matrix.submatrix_apply] at en ⊢
  convert en.symm using 1
  congr! 10

end
end BinaryQuery

end NearSquareRoot
end Computability
end OAI
