import OAI.LinearAlgebra.SpectralBooks.SpectralSpace

/-! # Appending a shared basis label

The extra index at its receiving site is given by the fiber of a one-element
placement. This keeps the original tensor format visible even when two
designated sites coincide.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

noncomputable section
open scoped Classical

variable {I : Type} [Fintype I] {K : Type*} [CommSemiring K]

/-- Append at `s` the specified label of each old coefficient. -/
def appendLabel (T : Raw.{0} I K) (s : I) (D : Type) [Fintype D] (label : (∀ i, T.Leg i) → D) :
    Raw.{0} I K where
  Leg i := T.Leg i × ({_u : Unit // s = i} → D)
  finiteLeg _ := inferInstance
  coeff x := if (x s).2 ⟨(), rfl⟩ = label (fun i => (x i).1)
    then T.coeff (fun i => (x i).1) else 0

/-- The output of the copying degeneration: an independent equal pair of
labels at the first two sites, with a copy of the old label at the third. -/
def copyOutput (T : Raw.{0} I K) (σ : Fin 3 → I) {q : ℕ} (hA : T.Leg (σ 0) → Fin q) :
    Raw.{0} I K where
  Leg i := T.Leg i × ({r : Fin 3 // σ r = i} → Fin q)
  finiteLeg _ := inferInstance
  coeff x := T.coeff (fun i => (x i).1) *
    (if (x (σ 0)).2 ⟨0, rfl⟩ = (x (σ 1)).2 ⟨1, rfl⟩ ∧
        (x (σ 2)).2 ⟨2, rfl⟩ = hA (x (σ 0)).1 then 1 else 0)

end
end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
