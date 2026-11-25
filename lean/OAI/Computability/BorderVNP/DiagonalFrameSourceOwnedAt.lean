import OAI.Computability.BorderVNP.DiagonalSourceOwnedVisit

/-! # The public arguments and complete ownership return of a prepared source -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ}
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    (S : SourceReports ar owners) (F : PreparationFrame G L ar decl header pin pub mac reg mem)
    (builders : F.Builders fixed id owners) (agree : F.SourceAgreement fixed S builders)
    (q : {v : Declared ar owners decl // S.pins v.val}) (reports : S.actual q.val.val)

/-- The decoded source provides its own public words and ownership return.
The trace, register bank and RAM come from splitting its original native
preparation on the actual source exterior. -/
noncomputable def PreparationFrame.sourceOwnedAt (u : Fin (R+1)) :
    (Arg → Word w) × List (TeamRAM.Event w) × Bank w × Memory w :=
  let original := (F.sourceEquiv fixed S builders agree).symm ⟨q,reports⟩
  let v := (visitsEquiv id (pub original.1 u) (mac original.1 u) (reg original.1 u)
    (mem original.1 u)).symm (original.2 u)
  (pub original.1 u,v.owned.val)

end TeamContraction

end BorderVNP
end Computability
end OAI
