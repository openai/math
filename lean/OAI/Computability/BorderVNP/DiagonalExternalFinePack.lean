import OAI.Computability.BorderVNP.DiagonalExternalFineView
import OAI.Computability.BorderVNP.PackedGridExternal

/-! # Returning from grouped external words to the original public bits

A grouped network reads only the lanes assigned to its original ports. Passing its
tables through the fine view therefore recovers their tensor on every setting of
the width-one ports, including layouts with unused lanes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew.FineView

open Crossing CellEntries

variable {D : ℕ} {P A : Type} (N : Network D P (fun _ => 1)) (width : A → ℕ)
  (lane : P ↪ Σ a, Fin (width a)) (owner : A → N.Site)
  (aligned : ∀ p, owner (lane p).1 = N.attach p)

/-- Restricting the zero extension to its named lanes recovers every original bit. -/
theorem readExternal_extend (x : Ports (fun _ : P => 1)) :
    Network.readExternal width lane (extend lane x) = x := by
  funext p i
  obtain rfl := Subsingleton.elim i 0
  exact extend_lane lane x p

/-- Grouping the public ports and exposing their fine lanes again preserves the
original contraction for arbitrary local tables and public inputs. -/
theorem value_after_pack {K : Type*} [CommSemiring K] (table : N.Tables K)
    (x : Ports (fun _ : P => 1)) :
    (layout (N.packExternal width owner) lane).value
      (tables _ lane (N.externalTables width lane owner aligned table)) x = N.value table x := by
  rw [value, Network.value_packExternal, readExternal_extend]

variable {Team Param Gadget : Type*} [Fintype Team] [Fintype Param] {b : ℕ}

/-- The same round trip preserves the polynomial tensor of a tracked term for every
interpretation of the gadgets and every fine input. -/
theorem tracked_tensor_after_pack {K : Type*} [CommSemiring K]
    (t : Tracked Team Param Gadget b N) (values : Gadget → K) (x : Ports (fun _ : P => 1)) :
    ((tracked (N.packExternal width owner) lane (t.packExternal width lane owner aligned)).valued
      values).tensor x = (t.valued values).tensor x := by
  rw [tracked_tensor]
  change (t.valued values).tensor (Network.readExternal width lane (extend lane x)) = _
  rw [readExternal_extend]

end Diagonal.ExternalSew.FineView

end BorderVNP
end Computability
end OAI
