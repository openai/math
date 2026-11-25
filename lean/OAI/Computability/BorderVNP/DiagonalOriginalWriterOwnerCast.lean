import OAI.Computability.BorderVNP.DiagonalPinnedRouteObservation

/-! # The original writer's matching selector under equal team assignments -/

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

/-- The same routed choice at the same shared row, typed using the equal native team assignment. -/
def originalMatchAtOwner (q : Matching ar registered decl raw.val) (same : registered=resident) :
    Matching ar resident decl raw.val := same ▸ q

/-- Carry the table, row map, complete writer history and original owner scan to
the resident assignment. The selector and the full dependent routed payload are preserved. -/
theorem PreparationFrame.originalWriterAtOwner {q : Matching ar registered decl raw.val}
    (physical : F.OwnedRouteOn fixed id registered template count raw q scan ∧ after=scan)
    (names : registered=resident) :
    (F.OwnedRouteOn fixed id resident template count raw (originalMatchAtOwner (raw:=raw) q names) scan ∧ after=scan) ∧
      (originalMatchAtOwner (raw:=raw) q names).val.1=q.val.1 ∧ HEq (originalMatchAtOwner (raw:=raw) q names).val q.val := by
  subst resident
  exact ⟨physical,rfl,HEq.rfl⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
