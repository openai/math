import OAI.LinearAlgebra.SpectralBooks.PortWiring

namespace OAI
namespace ThreeFlat.Diagonal.RefreshMotif

open LinearAlgebra.SpectralBooks

/-- Two families of dense ties, including the free local ties. -/
def denseGraph (m : ℕ) : PortGraph (Fin m) (Bool × (Fin m × Fin m)) :=
  ⟨fun e => e.2.1, fun e => e.2.2⟩

end ThreeFlat.Diagonal.RefreshMotif

end OAI
