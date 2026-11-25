import OAI.Computability.BorderVNP.DiagonalFundedOwnerReindex

/-! # The original and funded ownership reads on a single routed assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open _root_.OAI.Computability.BorderVNP.Cube _root_.OAI.Computability.BorderVNP.Cube.Physical _root_.OAI.Computability.BorderVNP.Cube.Scatter
open _root_.OAI.Computability.BorderVNP.Cube.Scatter.Assignment RoutingISA

/-- The registered packet's owner and the native owner use the same host
word on the actual selectors. The transported observation retains its
original team family, raw words, and assignment selectors. -/
theorem reportedFundedOwnership {R w : ℕ} {ar : CubeArena.Layout}
    {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R+1)}
    {family : TeamRows.Returns (Fin (R+1)) ar w} {raw : Symbols ar.header.d → List Bool}
    {semantic original funded : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) →
      Fin ar.header.d → Fin (R+1)}
    {q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) original}
    {selectors : Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h}
    {Cell : Type*} {packetLabel originalLabel : Cell → Label (ar.n+1) ar.header.d}
    (registered : semantic=original) (placed : semantic=funded) (names : packetLabel=originalLabel)
    (observed : ObservedOwned ar decl group family original raw q) (same : q.1=selectors)
    (word : Cell → ℕ) (read : ∀ c, word c=(original q.1 (originalLabel c (chosen ar.b ar.s q.1))).val) :
    (∀ c, word c=(semantic selectors (packetLabel c (chosen ar.b ar.s selectors))).val) ∧
    ∃ issued : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) funded,
      issued.1=selectors ∧ ObservedOwned ar decl group family funded raw issued ∧
      ∀ c, word c=(funded issued.1 (packetLabel c (chosen ar.b ar.s issued.1))).val := by
  subst selectors semantic originalLabel
  exact ⟨read,reindexIssuedOwner placed rfl observed read⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
