import OAI.Computability.BorderVNP.DiagonalBootLookupOwnership

/-! # The exact exterior and publication frame indexed by a returned owner -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Scatter Scatter.Assignment SignedPrep TeamRows Tally
open DiagonalTallyPacketEmit CellMacro.Generator JointHeader ProcessorSlots SignedTaskArena FiniteEvaluator

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} (sa : SignedTaskArena.Layout) {decl : LengthDeclaration sa.cube.n sa.cube.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w}
    {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {owners : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks →
      Selector sa.cube.n sa.cube.K sa.cube.h) → Fin sa.cube.header.d → Fin (R+1)}
    (F : PreparationFrame G L sa.cube decl header pin pub mac reg mem)

variable {sa F}
/-- The writer's source exterior is indexed by the returned ownership
itself, before any independent report or cube consistency test. -/
def PreparationFrame.ReturnedOwnershipAt.sourceExterior {origin : HeaderExterior L header}
    {x : Exterior R r link → Bool} {template : DiagonalTallyPacketEmit.Frame} {count : ℕ}
    {v : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) owners}
    {before : TeamRows.Returns (Fin (R+1)) sa.cube w} (_receipt : F.ReturnedOwnershipAt sa origin x template count v before) :
    HeaderExterior L header := origin

end TeamContraction

end BorderVNP
end Computability
end OAI
