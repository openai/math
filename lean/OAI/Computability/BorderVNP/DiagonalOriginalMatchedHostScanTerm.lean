import OAI.Computability.BorderVNP.DiagonalOriginalOwnerReplayTerm
import OAI.Computability.BorderVNP.DiagonalRegisteredHostScan

/-! # Reading the registered route on the rows actually returned by the writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep
open BorderVNP.Cube Cube.Physical Cube.Physical.NativeAssignments

/-- The shared row equality restores the first matching predicate on the actual output.
The owner equality then reindexes the same assignment and its physical observation together. -/
theorem registeredHostScanAtReturnedRows {R w : ℕ} {ar : CubeArena.Layout}
    {registered resident : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) →
      Fin ar.header.d → Fin (R+1)}
    {decl : LengthDeclaration ar.n ar.header.d} {actual original : Symbols ar.header.d → List Bool}
    {group : Fin ar.header.d → Fin (R+1)} {owned : TeamRows.Returns (Fin (R+1)) ar w}
    (names : registered=resident) (received : Matching ar resident decl original)
    (rows : actual=original) (seen : ObservedOwned ar decl group owned resident actual received.val)
    {claim : Routed (b:=ar.b) (s:=ar.s) registered → Prop}
    (read : ∀ mat : Matching ar registered decl actual, ObservedOwned ar decl group owned registered actual mat.val →
      claim mat.val) : claim (received.val.atRegisteredOwner names) :=
  let matched : Matching ar resident decl actual := ⟨received.val, received.property.1, received.property.2.trans rows.symm⟩
  registeredHostScan (claim:=claim) names matched seen read

open Lean Meta Elab Term
open private replayParameters replayParameter from OAI.Computability.BorderVNP.DiagonalOriginalOwnerReplayTerm

/-- Specialize the route transport to the owner, arena, original row and returned row carried
by the native observation. The remaining argument is the reader on the registered assignment. -/
elab "actualRegisteredHostScan% " owner:term:max received:term:max equal:term:max report:term:max : term => do
  let names ← elabTerm owner none
  let old ← elabTerm received none
  let rows ← elabTerm equal none
  let seen ← elabTerm report none
  let some owners ← whnfUntil (← inferType names) ``Eq | throwError "expected the original owner equality"
  let some same ← whnfUntil (← inferType rows) ``Eq | throwError "expected the returned row equality"
  let fields ← replayParameters seen ``ObservedOwned
  let parameters := #[← replayParameter fields `R, ← replayParameter fields `w, ← replayParameter fields `ar,
    owners.getAppArgs[1]!, owners.getAppArgs[2]!, ← replayParameter fields `decl,
    same.getAppArgs[1]!, same.getAppArgs[2]!, ← replayParameter fields `group, ← replayParameter fields `F,
    names, old, rows, seen]
  return mkAppN (Lean.mkConst ``registeredHostScanAtReturnedRows) parameters

end TeamContraction

end BorderVNP
end Computability
end OAI
