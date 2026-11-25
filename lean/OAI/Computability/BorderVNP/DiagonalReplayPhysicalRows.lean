import OAI.Computability.BorderVNP.DiagonalReturnedRouteState
import OAI.Computability.BorderVNP.RoutingISASignedPrepFrame

/-! # Canonical delivery of a length-correct shared word on the replayed exterior -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Scatter

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    (F : PreparationFrame G L ar decl header pin pub mac reg mem) (raw : SharedWords ar decl)

local notation3 (prettyPrint := false) "z" => F.replay fixed raw
local notation3 (prettyPrint := false) "callMem" => fun u => (F.schedule z.1 u).val.2.2
local notation3 (prettyPrint := false) "callReg" => fun u => (F.schedule z.1 u).val.2.1

/-- Read the same original shared bits after replaying the real route at
the reconstructed exterior, including all choices made by co-owned rows. -/
theorem PreparationFrame.replay_receivedRows :
    readRouteRows F.row F.rows F.group (fun u => (z.2 u).val.2.2) = raw.val := by
  let E := exteriorNativeRoutesEquiv G L F.tab F.row F.dataDir F.privatePlacement F.livePlacement F.guess
    F.rows decl fixed header F.length pub mac (fun x u => (F.schedule x u).val.2.1)
    (fun x u => (F.schedule x u).val.2.2) F.initialized F.copies F.emitted F.fitted F.records F.count
    F.dataCount F.room F.frame
  exact congrArg Subtype.val (E.apply_symm_apply raw)

/-- The inverse pre-call route has a genuine delivered-row witness on its own
receiver. Its instruction operands, both final banks and all shared words
match the issued native returns before the constant table is installed. -/
theorem PreparationFrame.replayDelivery :
    ∃ (H : Fin (R+1) → TeamHistory w)
      (f : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner
        F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
      f.table=F.tab ∧ f.row=F.row ∧ SharedWriters f F.rows (F.source z.1) ∧
      (∀ u, (H u).pub=pub z.1 u ∧ (H u).macros=mac z.1 u ∧ (H u).history.val.2=(z.2 u).val.2) ∧
      (∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
        (F.guess u) (H u).initial) ∧ f.receivedRows F.rows F.group=raw.val := by
  obtain ⟨H,f,tab,row,_,writer,endState,pinned,read⟩ :=
    (F.initialized z.1).ownedDelivery (mac z.1) callReg z.2
      (F.emitted z.1) (F.fitted z.1) F.records F.count F.room
  exact ⟨H,f,tab,row,writer,endState,pinned,(read F.group).trans (F.replay_receivedRows fixed raw)⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
