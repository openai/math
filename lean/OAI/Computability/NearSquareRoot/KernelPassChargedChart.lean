import OAI.Computability.NearSquareRoot.KernelBinaryQueryChart

/-! # Binary linear coordinates of the active kernel and its spectators

The physical coordinates select one distinguished pair and all auxiliary
positions. The paired bases act linearly on that active part. The remaining
distinguished coordinates retain their common order for every query.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BinaryQuery

open OAI.LinearAlgebra.FiniteFourier KernelPass Matrix
noncomputable section

variable {E : Type} [AddCommGroup E] [Module (ZMod 2) E] {m u : ℕ}

private def active (j : Fin (m+1)) (z : Index (m+1) u → ZMod 2) (c : Fin 1) :
    ZMod 2 × (Fin u → ZMod 2) := (z (c, .inl j), fun a => z (c, .inr a))

/-- The linear map underlying the ordinary physical chart of a binary query. -/
def physicalLinear (j : Fin (m+1)) (p q : E ≃ₗ[ZMod 2] ZMod 2 × (Fin u → ZMod 2)) :
    Bits (Arity (m+1) u) ≃ₗ[ZMod 2] ((Fin 1 → E) × (Fin 1 → E)) × EndpointDigitPairs (Fin 1) (Fin m) (ZMod 2) where
  toEquiv := physicalChart j p.toEquiv q.toEquiv
  map_add' x y := by
    refine Prod.ext (Prod.ext ?_ ?_) rfl
    · funext c
      exact map_add p.symm (active j (halves (m+1) u x).1 c) (active j (halves (m+1) u y).1 c)
    · funext c
      exact map_add q.symm (active j (halves (m+1) u x).2 c) (active j (halves (m+1) u y).2 c)
  map_smul' r x := by
    refine Prod.ext (Prod.ext ?_ ?_) rfl
    · funext c
      exact map_smul p.symm r (active j (halves (m+1) u x).1 c)
    · funext c
      exact map_smul q.symm r (active j (halves (m+1) u x).2 c)

@[simp] theorem physicalLinear_toEquiv (j : Fin (m+1))
    (p q : E ≃ₗ[ZMod 2] ZMod 2 × (Fin u → ZMod 2)) :
    (physicalLinear j p q).toEquiv = physicalChart j p.toEquiv q.toEquiv := rfl

/-- The actual query in its linear chart on both endpoint addresses. -/
theorem physical_query_linear (j : Fin (m+1)) (B : LinearMap.BilinForm (ZMod 2) E)
    (p q : E ≃ₗ[ZMod 2] ZMod 2 × (Fin u → ZMod 2))
    (hpq : ∀ x y, B x y = (p x).1 * (q y).1 + ∑ k, (p x).2 k * (q y).2 k) :
    query (u := u) j = (primeCommonKernel KernelNormalization.binaryRoot B 1 (u+1)).submatrix
      (physicalLinear j p q) (physicalLinear j p q) :=
  physical_query j B p q hpq

end
end BinaryQuery

end NearSquareRoot
end Computability
end OAI
