import OAI.Computability.BorderVNP.RoutingISASignedPrepSourceRows

/-! # The shared native exterior reconstructed by the signed prefix decoder -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ}
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    (S : SourceReports ar owners) (F : PreparationFrame G L ar decl header pin pub mac reg mem)
    (B : F.Builders fixed id owners)

/-- Before the private reports are interpreted, the inverse route fixes every
physical input wire. This includes the common header and both legs of the
relayed payload, with the unused physical positions filled by zero. -/
theorem PreparationFrame.replay_exterior (raw : SharedWords ar decl) :
    (F.replay fixed raw).1.val = cubeExterior G L F.tab F.row F.dataDir F.privatePlacement F.livePlacement
      F.guess F.rows raw.val header F.length := rfl

/-- Replaying the source reports through the entire pre-call prefix restores
the exact shared wires of their routed assignment, independently of the
report guesses. -/
theorem PreparationFrame.sourceEquiv_exterior (agree : F.SourceAgreement fixed S B)
    (q : {v : Declared ar owners decl // S.pins v.val}) (reports : S.actual q.val.val) :
    ((F.sourceEquiv fixed S B agree).symm ⟨q,reports⟩).1.val =
      cubeExterior G L F.tab F.row F.dataDir F.privatePlacement F.livePlacement F.guess F.rows
        (Scatter.Assignment.Routed.encode owners q.val.val).shared header F.length := by
  change (F.replay fixed (declaredWords ar owners decl q.val)).1.val = _
  exact F.replay_exterior fixed (declaredWords ar owners decl q.val)

end TeamContraction

end BorderVNP
end Computability
end OAI
