import OAI.Computability.BorderVNP.DiagonalFrameSourceOwnedAt

/-! # Reindexing the actual issued ownership state at the common frame -/

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
    {Φ : Type} (atFrame : Φ → SourceReports ar owners) {physical uniform : Φ}
    (F : PreparationFrame G L ar decl header pin pub mac reg mem) (builders : F.Builders fixed id owners)

/-- The native ownership register bank, trace and memory are the same after
the installed frame coordinates are replaced by their common value. The cast
carries the original report proposal and the selected padded route. -/
theorem PreparationFrame.sourceOwnedAt_onUniform (alignment : physical=uniform)
    (agree : F.SourceAgreement fixed (atFrame physical) builders)
    (q : {v : Declared ar owners decl // (atFrame physical).pins v.val})
    (reports : (atFrame physical).actual q.val.val) (u : Fin (R+1)) :
    let canonical := (congrArg (fun f => F.SourceAgreement fixed (atFrame f) builders) alignment).mp agree
    let padded : {v : Declared ar owners decl // (atFrame uniform).pins v.val} :=
      ⟨q.val,(congrArg (fun f => (atFrame f).pins q.val.val) alignment).mp q.property⟩
    let tape := cast (congrArg (fun f => (atFrame f).actual q.val.val) alignment) reports
    F.sourceOwnedAt fixed (atFrame physical) builders agree q reports u =
      F.sourceOwnedAt fixed (atFrame uniform) builders canonical padded tape u := by
  cases alignment
  rfl

end TeamContraction

end BorderVNP
end Computability
end OAI
