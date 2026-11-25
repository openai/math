import OAI.Computability.BorderVNP.DiagonalPinnedGuards
import OAI.Computability.BorderVNP.DiagonalRegisteredRoutedEnds
import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily
import OAI.Computability.BorderVNP.RoutingISASignedPrepOwned

/-! # The original host reader on its registered routed assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open BorderVNP.Cube Cube.Physical Cube.Physical.NativeAssignments

/-- Apply a registered reader to the matching physical transmission and its same native
observation. The requested output keeps both endpoint payloads of the original route. -/
theorem registeredHostScan {R w : Nat} {ar : CubeArena.Layout}
    {registered resident : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) →
      Fin ar.header.d → Fin (R+1)}
    {decl : LengthDeclaration ar.n ar.header.d} {raw : Symbols ar.header.d → List Bool}
    {group : Fin ar.header.d → Fin (R+1)} {owned : TeamRows.Returns (Fin (R+1)) ar w}
    (names : registered=resident) (matched : Matching ar resident decl raw)
    (seen : ObservedOwned ar decl group owned resident raw matched.val)
    {claim : Routed (b:=ar.b) (s:=ar.s) registered → Prop}
    (read : ∀ mat : Matching ar registered decl raw, ObservedOwned ar decl group owned registered raw mat.val →
      claim mat.val) :
    claim (matched.val.atRegisteredOwner names) := by
  cases names
  exact read matched seen

end TeamContraction

namespace Cube.Physical.NativeAssignments

open Crossing Packing.CellAddresses Packing.Inherited

/-- Padding outside the live slots reads the same complete payload after recovering the registered owner. -/
theorem Routed.pins_atRegisteredOwner {D C n d blocks K h b s : Nat} {P Team : Type}
    {bits : P → Nat} (N : Network D P bits) (cell : N.Site → Fin C)
    {registered resident : (Packet n d blocks → Selector n K h) → Fin d → Team}
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b))
    (physical : Routed (b:=b) (s:=s) resident) (names : registered=resident) :
    RoutedPins N cell registered slot (physical.atRegisteredOwner names) ↔ RoutedPins N cell resident slot physical := by
  cases names
  rfl

end Cube.Physical.NativeAssignments

end BorderVNP
end Computability
end OAI
