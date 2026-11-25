import OAI.Computability.BorderVNP.DiagonalOriginalWriterOwnerCast
import OAI.Computability.BorderVNP.DiagonalRoutedOriginalOwnerWords

/-! # The original writer and its complete cell-owner array -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment DiagonalTallyPacketEmit

variable {R r teams d link inner n w : ℕ} {Edge : Type} {G : Wiring R r teams d link inner n Edge}
    {L : WireLayout (R+1) r link} {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
    {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {F : PreparationFrame G L ar decl header pin pub mac reg mem}
    {fixed : Block (R+1)} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ}
    {registered resident : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) →
      Fin ar.header.d → Fin (R+1)} {template : Frame} {count : ℕ}
    {raw : SharedWords ar decl} {scan after : TeamRows.Returns (Fin (R+1)) ar w}


/-- Retain the observed original transmission at the resident owner and identify
all its owner words, for the same routed payload and physical scan. -/
theorem PreparationFrame.originalWriterAndWords {q : Matching ar registered decl raw.val}
    {packetLabel residentLabel : Fin ar.cells → Label (ar.n+1) ar.header.d}
    (physical : F.OwnedRouteOn fixed id registered template count raw q scan ∧ after=scan)
    (names : registered=resident) (labels : packetLabel=residentLabel) :
    let real := originalMatchAtOwner (raw:=raw) q names
    (F.OwnedRouteOn fixed id resident template count raw real scan ∧ after=scan) ∧
      (real.val.1=q.val.1 ∧ HEq real.val q.val) ∧
      routedOwnerWord ar registered packetLabel q.val=routedOwnerWord ar resident residentLabel real.val := by
  let data := PreparationFrame.originalWriterAtOwner physical names
  exact ⟨data.1, data.2, SignedPrep.routedOwnerWord_of_original (packet:=q.val)
    (resident:=(originalMatchAtOwner (raw:=raw) q names).val) names labels data.2.1.symm⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
