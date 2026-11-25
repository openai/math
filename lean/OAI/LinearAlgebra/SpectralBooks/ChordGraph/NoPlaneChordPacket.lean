import OAI.LinearAlgebra.SpectralBooks.ChordGraph.ChordWiring
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.TreeFourPoint

/-! # Uncrossing graph tensors over a field with no spectral plane -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section

namespace ChordGraph

open SiteTensor
open scoped BigOperators

variable {k : ℕ} (K : Type*) [Field K] [Nonempty (Fin k)] {a b c d : Fin k}

/-- Absence of a spectral plane supplies a graph uncrossing packet with
arbitrarily small overhead per bit. -/
theorem exists_chord_packet_of_no_plane
    (noPlane : ¬ Nonempty (SpectralPlacementPrices K (EuclideanSpace ℝ (Fin 2))))
    (hab : a < b) (hbc : b < c) (hcd : c < d) {σ : ℝ} (hσ : 0 < σ) :
    ∃ m : ℕ, 0 < m ∧ ∃ L : ℕ, (L : ℝ) ≤ (2 : ℝ) ^ (σ * m) ∧
      ∃ u v : Fin L → ℕ, (∀ l, u l + v l = m) ∧
        graphClass K (m • crossing hab hbc hcd) ≤
          ∑ l, graphClass K (u l • parallel hab hbc hcd + v l • nested hab hbc hcd) :=
  chord_packet_of_wire_packet K hab hbc hcd (exists_wire_packet_of_no_plane noPlane a b c d hσ)

end ChordGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
