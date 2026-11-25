import OAI.Computability.BorderVNP.DiagonalPrivatePathRead

/-! # Recovering both routed endpoints at the original receiving team -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.Inherited Packing.Inherited.Placement Diagonal.CellEntries

variable {n d blocks K h b s : ℕ} {Team : Type}
    {registered resident : (Packet n d blocks → Selector n K h) → Fin d → Team}

/-- The entire returned route, including every assigned word, indexed by the equal registered owner. -/
def Routed.atRegisteredOwner (physical : Routed (b:=b) (s:=s) resident) (names : registered=resident) :
    Routed (b:=b) (s:=s) registered := by
  cases names
  exact physical

/-- The heterogeneously equal physical return recovers the submitted route at its original type. -/
theorem Routed.atRegisteredOwner_eq (physical : Routed (b:=b) (s:=s) resident)
    (names : registered=resident) {original : Routed (b:=b) (s:=s) registered} (same : HEq physical original) :
    physical.atRegisteredOwner names=original := by
  cases names
  exact eq_of_heq same

/-- Both endpoint words at every live bit agree after changing the owner index of the original route. -/
theorem Routed.ends_atRegisteredOwner {D : ℕ} {P Cell : Type}
    {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Cell)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b))
    (physical : Routed (b:=b) (s:=s) resident) (names : registered=resident) :
    routedEnds N cell registered slot (physical.atRegisteredOwner names)=routedEnds N cell resident slot physical := by
  cases names
  rfl

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
