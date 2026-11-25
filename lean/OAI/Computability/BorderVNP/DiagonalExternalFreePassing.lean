import OAI.Computability.BorderVNP.CubePhysicalInputCongr
import OAI.Computability.BorderVNP.PackedGridExternal

/-! # Passing assignments are independent of unused receiver lanes

A port group supplies only its injected fine lanes to the original box.
Thus changing the other entries of its buffer preserves the pass check,
each unary use bit, and each local scalar multiplicity on an individual
fully assigned path.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing CellEntries BorderVNP.Cube Physical
open scoped Classical BigOperators

variable {D B n d b h K s : ℕ} {P A Team Param Gadget : Type}
    [Fintype Team] [Fintype Param]
    {N : Network D P (fun _ => 1)}
    (width : A → ℕ) (lane : P ↪ (a : A) × Fin (width a)) (owner : A → N.Site)
    (aligned : ∀ p, owner (lane p).1 = N.attach p)
    (t : Tracked Team Param Gadget B N)
    (x y : Ports width) (agree : ∀ p, x (lane p).1 (lane p).2 = y (lane p).1 (lane p).2)

set_option maxHeartbeats 1100000
set_option synthInstance.maxSize 1500
include agree

local notation "G" => N.packExternal width owner
local notation "tg" => t.packExternal width lane owner aligned

omit [Fintype Team] [Fintype Param] in
private theorem external_read {T : Type*} (f : N.Tables T) (v : N.Site)
    (a : Ports (fun j : {e : N.Edge // N.src e = v ∨ N.dst e = v} => N.width j.val)) :
    N.externalTables width lane owner aligned f v a (fun p => x p.val) =
      N.externalTables width lane owner aligned f v a (fun p => y p.val) := by
  unfold Network.externalTables
  apply congrArg (f v a)
  funext p j
  exact agree p.val

variable (packet : PacketPlacement (D := D) (P := A) (bits := width) Team n d b h K (N.packExternal width owner)) (pos : TableEntry n b h K s → Gadget)

/-- On the packed external input words the identity on all path bits
gives a bijection of the native and canonical passing assignments. -/
noncomputable def groupedPassingEquiv : packet.Passing (tg) x pos ≃ packet.Passing (tg) y pos :=
  Physical.inputPassingEquiv (N := (G)) (tg) packet pos x y (external_read (N := N) width lane owner aligned x y agree t.tags)

/-- The original power selections and all scalar counts of the path agree
after changing its unused grouped lanes. -/
theorem grouped_passing_tally (a : packet.Passing (tg) x pos) :
    packet.tally (tg) y pos (groupedPassingEquiv (N := N) width lane owner aligned t x y agree packet pos a) =
      packet.tally (tg) x pos a :=
  Physical.inputPassingEquiv_tally (N := (G)) (tg) packet pos x y
    (external_read (N := N) width lane owner aligned x y agree t.tags)
    (external_read (N := N) width lane owner aligned x y agree t.words.selected) a

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
