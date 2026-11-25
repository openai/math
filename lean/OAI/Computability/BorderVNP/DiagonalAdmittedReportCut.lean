import OAI.Computability.BorderVNP.DiagonalAdmittedPinnedFrames
import OAI.Computability.BorderVNP.DiagonalRoutedReportCutPinned

/-! # Reading report inputs on an admitted joint preparation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator SignedPrep Routing ProcessorSlots JointHeader
open CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports

variable {R r t d link inner n w reserve dim tally : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (args : Fin (R+1) → UnitAddresses)
    (live : Fin d → Bool) (L : WireLayout (R+1) r link) (fixed : Block (R+1))
    (hw : 0<w) (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (ar : CubeArena.Layout)
local notation "cap" => declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s
variable (width : L.header=PositiveFields.width reserve ar.n ar.header.d
      (declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s) (R+1) dim tally)
    {gen : Fragment IO}
    (U : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext} → Fin (R+1) → PinStart gen n w)
    (ib hb sb : Fin (R+1) → ℕ)
    (pinWidth : ∀ x u, (U x u).guessWidth=(G.pinLayout u (ib u) (hb u) (sb u)).guessWidth)
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (S : SourceReports ar owners) (rawPin : Fin d → Bool)
    (profile : Fin reserve → Bool) (claim : Fin ((R+1)*dim*tally) → Bool)

local notation "Fields" => PositiveFields reserve ar.n ar.header.d cap (R+1) dim tally
local notation3 (prettyPrint := false) "p(" c ")" => (⟨profile,c,claim⟩ : Fields)
local notation3 (prettyPrint := false) "head" => fun c : RawBroadcast ar => (p(c)).bits
local notation "headers" => positiveExteriorFieldsEquiv G args live L fixed hw size base fit width
variable (allowed : RawBroadcast ar → Prop) (template : DiagonalTallyPacketEmit.Frame) (entries : ℕ)
local notation3 (prettyPrint := false) "runs(" c ")" => ((ext : HeaderExterior L (p(c)).bits) ×
  pinnedPreps G args live U ib hb sb pinWidth id ((headers).symm ⟨p(c),ext⟩) rawPin)

/-- Read the native control and report outputs on a single positive
joint preparation, using its own parsed cube, external wire and pin. -/
def pinnedReportCutAt (full : Σ c : RawBroadcast ar, runs(c)) (u : Fin (R+1))
    {l : ReportLayout} {cs : List (ReportCell l)} (rows : ReportAssignments cs) : Prop :=
  let ext := (headers).symm ⟨p(full.1),full.2.1⟩
  let pr : (U ext u).Prefix id := ⟨_,full.2.2 u⟩
  ∃ cur desc, Nonempty (ReportArgumentCut ((U ext u).visited pr).reports rows cur desc)

variable (candidates : AdmittedPinnedFrames G args live L fixed hw size base fit ar width U ib hb sb pinWidth
    id owners S rawPin profile claim allowed template entries)

set_option maxHeartbeats 380000 in
/-- The admitted frame recovers the native scanner and sparse inputs for
every source proposal on its jointly restored preparation. -/
theorem AdmittedPinnedFrames.reportCut
    (checked : ∀ c, runs(c) → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners, allowed (routeBroadcast ar owners q).val)
    (v : {v : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners // S.pins v}) (reports : S.actual v.val) (u : Fin (R+1)) :
    pinnedReportCutAt G args live L fixed hw size base fit ar width U ib hb sb pinWidth id rawPin profile claim
      ((candidates.preparations G args live L fixed hw size base fit ar width U ib hb sb pinWidth id owners
        S rawPin profile claim allowed template entries checked honest).symm ⟨v,reports⟩) u (reports u) :=
  routedPinnedPreparations_reportCut G args live L fixed hw size base fit ar width U ib hb sb pinWidth id owners
    S rawPin profile claim candidates.wire candidates.extent allowed checked honest candidates.frame
    candidates.builder candidates.source v reports u

end TeamContraction

end BorderVNP
end Computability
end OAI
