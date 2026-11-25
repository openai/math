import OAI.Computability.BorderVNP.DiagonalAdmittedEquatedReportCut

/-! # Reading the original physical rows after reindexing the source -/

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

variable (candidates : AdmittedPinnedFrames G args live L fixed hw size base fit ar width U ib hb sb pinWidth
    id owners S rawPin profile claim allowed template entries)

set_option maxHeartbeats 1000000 in
/-- Read the chronological report on its owning cell list, using the actual source
assignment as the result index. This also recovers tentative count and use bits. -/
theorem AdmittedPinnedFrames.preparedReceivedRowsCut
    (checked : ∀ c, runs(c) → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners, allowed (routeBroadcast ar owners q).val)
    {Route : Type} {C : ℕ} {charts : Fin (R+1) → ReportLayout} (rows : Route → ReceivedRows charts C)
    (recode : S.Proposals ≃ (Σ v : Route, (u : Fin (R+1)) → ReportAssignments ((rows v).cells u)))
    (same : ∀ z u, ReportInputKey.ofRows ((recode.symm z).2 u)=ReportInputKey.ofRows (z.2 u))
    (original : (Σ c : RawBroadcast ar, runs(c)) ≃ (Σ v : Route, (u : Fin (R+1)) → ReportAssignments ((rows v).cells u)))
    (identified : original = (candidates.preparations G args live L fixed hw size base fit ar width U ib hb sb
      pinWidth id owners S rawPin profile claim allowed template entries checked honest).trans recode)
    (v : Route) (reports : (u : Fin (R+1)) → ReportAssignments ((rows v).cells u)) (u : Fin (R+1)) :
    pinnedReportCutAt G args live L fixed hw size base fit ar width U ib hb sb pinWidth id rawPin profile claim
      (original.symm ⟨v,reports⟩) u (reports u) :=
  candidates.preparedReportCut G args live L fixed hw size base fit ar width U ib hb sb pinWidth id owners S
    rawPin profile claim allowed template entries checked honest recode (fun z t => ReportInputKey.ofRows (z.2 t))
    same original identified v reports u

end TeamContraction

end BorderVNP
end Computability
end OAI
