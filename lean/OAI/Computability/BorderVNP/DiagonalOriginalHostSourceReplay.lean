import OAI.Computability.BorderVNP.DiagonalPinnedRouteObservation

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Reuse a replay observation on the actual jointly issued owner traversal -/

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment DiagonalTallyPacketEmit

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    (F : PreparationFrame G L ar decl header pin pub mac reg mem)
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (template : Frame) (count : ℕ)

variable {F fixed id owners template count}

/-- Identify the full replay witness at the attained joint owner return. -/
theorem PreparationFrame.OwnedRouteOn.atVisitedRows
    {operands : SharedWords ar decl} {q : Matching ar owners decl operands.val}
    {scan actual : TeamRows.Returns (Fin (R+1)) ar w}
    (seen : F.OwnedRouteOn fixed id owners template count operands q scan) (same : actual=scan) :
    F.OwnedRouteOn fixed id owners template count operands q actual := same ▸ seen

/-- The original visit carries the same writer, substitutions, raw shared word and owner
handoff as the replay. A property established from these observations transfers to the attained table. -/
theorem PreparationFrame.OwnedRouteOn.applyAtVisit
    {operands : SharedWords ar decl} {q : Matching ar owners decl operands.val}
    {scan actual : TeamRows.Returns (Fin (R+1)) ar w}
    (seen : F.OwnedRouteOn fixed id owners template count operands q scan) (atVisit : actual=scan)
    {P : Routed (b:=ar.b) (s:=ar.s) owners → TeamRows.Returns (Fin (R+1)) ar w → Prop}
    (fromWriter :
      let z := F.replay fixed operands
      ∀ (H : Fin (R+1) → TeamHistory w)
        (delivery : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner
          F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
        delivery.table=F.tab → delivery.row=F.row → SharedWriters delivery F.rows (F.source z.1) →
        (∀ u, (H u).pub=pub z.1 u ∧ (H u).macros=mac z.1 u ∧ (H u).history.val.2=(z.2 u).val.2) →
        (∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
          (F.guess u) (H u).initial) → delivery.receivedRows F.rows F.group=operands.val →
        ∀ (match' : Matching ar owners decl (delivery.receivedRows F.rows F.group))
          (returned : TeamRows.Returns (Fin (R+1)) ar w),
          OwnedHandoff delivery F.rows (F.source z.1) ar decl F.group template id count returned →
          ObservedOwned ar decl F.group returned owners (delivery.receivedRows F.rows F.group) match'.val →
          P match'.val returned) : P q.val actual := by
  subst actual
  obtain ⟨H,delivery,ht,hr,writer,history,pins,stored,handoff,observed⟩ := seen
  exact fromWriter H delivery ht hr writer history pins stored
    ⟨q.val,q.property.1,q.property.2.trans stored.symm⟩ scan handoff observed

end TeamContraction

end BorderVNP
end Computability
end OAI
