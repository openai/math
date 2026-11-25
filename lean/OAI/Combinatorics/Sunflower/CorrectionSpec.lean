import OAI.Combinatorics.Sunflower.Control
import OAI.Combinatorics.Sunflower.Binary

/-! # Local maps for correcting the binary equality test -/

open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks.SiteTensor

namespace OAI
namespace Combinatorics
namespace Sunflower

noncomputable section

open Binary Control

variable {I : Type*} [Fintype I]

/-- The correction block emits the shared difference when the promised labels disagree. -/
def CorrectionMaps (P T : Finset I) (b : ℕ) (U V : Raw.{0} I ℂ) : Prop :=
  ∃ M : Map (fun _ : I => Word (b+1)) U.Leg
      (V.mul (Raw.maskDiagonal ℂ (P ∪ T) (Direction (b+1)))).Leg,
    ∀ x y (c : I → Word (b+1)), (∀ i ∈ P, c i = x) → (∀ i ∈ T, c i = y) →
      ∀ o, eval M c U.coeff o = V.coeff (fun i => (o i).1) *
        ∑ p : Direction (b+1), if p.val = x + y then
          (if (fun i => (o i).2) = (fun _ _ => p) then 1 else 0) else 0

end

end Sunflower
end Combinatorics
end OAI
