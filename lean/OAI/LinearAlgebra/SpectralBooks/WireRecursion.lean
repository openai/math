import OAI.LinearAlgebra.SpectralBooks.SiteTensor.NodeSplit
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.WireRoot
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.WireIndependent
import OAI.LinearAlgebra.SpectralBooks.EndpointTable.Recursion
import OAI.LinearAlgebra.SpectralBooks.SpectralPlacementPrices.Wire

/-! # Coupled wire transport at a spectral point

The exterior splitting tree starts from the wire of dimension `2^n`. Its
root price is `n` times the binary-wire distance at every placement.
The two-coordinate relocation bound holds at every selected child. The
finite-depth estimate and its limits therefore apply to any coupling of
the two prescribed endpoint distributions.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SiteTensor

open Relocation

variable {J : Type} [Fintype J] [Nonempty J] {K : Type*} [Field K]
variable (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J K → _ → Prop)) (c : ℝ)

/-- Equation `wire-coupling` in the transport appendix, for arbitrary
endpoint marginals and arbitrary couplings of those marginals. -/
theorem rawWireDistance_coupling (hc : 0 ≤ c) (A B : Fin 2 → J) (z w : J) (u v : ℝ)
    (hu : u ∈ Set.Icc 0 1) (hv : v ∈ Set.Icc 0 1)
    (hz₀ : rawWireDistance φ c (A 0) z = u * rawWireDistance φ c (A 0) (A 1))
    (hz₁ : rawWireDistance φ c z (A 1) = (1-u) * rawWireDistance φ c (A 0) (A 1))
    (hw₀ : rawWireDistance φ c (B 0) w = v * rawWireDistance φ c (B 0) (B 1))
    (hw₁ : rawWireDistance φ c w (B 1) = (1-v) * rawWireDistance φ c (B 0) (B 1))
    (π : EndpointTable) (hπ : EndpointTable.IsCoupling π u v) :
    rawWireDistance φ c z w ≤ EndpointTable.cost π (fun i j ↦ rawWireDistance φ c (A i) (B j)) := by
  let M : EndpointTable := fun i j ↦ rawWireDistance φ c (A i) (B j)
  let endpoint (n : ℕ) (N : WireNode K J (2^n)) : EndpointTable :=
    fun i j ↦ WireNode.cost φ c N (A i) (B j)
  let interior (n : ℕ) (N : WireNode K J (2^n)) := WireNode.cost φ c N z w
  apply EndpointTable.coupling_of_exterior_splits endpoint interior hc hu hv hπ M
    (EndpointTable.gapBound_of_triangle (rawWireDistance φ c) (rawWireDistance_symm φ c)
      (rawWireDistance_triangle φ c hc) A B)
  · intro n hn
    exact WireNode.hasSplit φ c hc n hn A B z w
  · intro n hn N
    exact WireNode.independent φ c hc N A B z w u v hu hv hz₀ hz₁ hw₀ hw₁
  · intro n hn
    refine ⟨WireNode.root (K := K) z n, ?_, ?_⟩
    · exact (WireNode.cost_root φ c z n z w).ge
    · intro i j
      exact (WireNode.cost_root φ c z n (A i) (B j)).le

/-- Synchronized choices of the endpoints specialize the coupling inequality
to convexity of wire distance along two segments. -/
theorem rawWireDistance_synchronized (hc : 0 ≤ c) (a b a' b' z w : J) (u : ℝ)
    (hu : u ∈ Set.Icc 0 1)
    (hz₀ : rawWireDistance φ c a z = u * rawWireDistance φ c a b)
    (hz₁ : rawWireDistance φ c z b = (1-u) * rawWireDistance φ c a b)
    (hw₀ : rawWireDistance φ c a' w = u * rawWireDistance φ c a' b')
    (hw₁ : rawWireDistance φ c w b' = (1-u) * rawWireDistance φ c a' b') :
    rawWireDistance φ c z w ≤ (1-u) * rawWireDistance φ c a a' + u * rawWireDistance φ c b b' := by
  simpa [EndpointTable.cost_synchronized] using rawWireDistance_coupling φ c hc
    ![a,b] ![a',b'] z w u u hu hu hz₀ hz₁ hw₀ hw₁ _ (EndpointTable.synchronized_isCoupling hu)

end SiteTensor

namespace SpectralPlacementPrices

/-- Every metric spectral placement space has convex distance along
synchronized segments. -/
theorem sectorBusemann {K X : Type*} [Field K] [MetricSpace X]
    (P : SpectralPlacementPrices K X) : SectorBusemann X :=
  P.sectorBusemann_of_rawWireDistance (fun φ c hc a b a' b' z w u hu ↦
    SiteTensor.rawWireDistance_synchronized φ c hc a b a' b' z w u hu)

end SpectralPlacementPrices

end SpectralBooks
end LinearAlgebra
end OAI
