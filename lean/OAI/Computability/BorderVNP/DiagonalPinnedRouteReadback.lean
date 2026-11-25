import OAI.Computability.BorderVNP.DiagonalCheckedRouteReadback
import OAI.Computability.BorderVNP.DiagonalPinnedLookupSiteSelection

/-! # A checked route with the exact chosen native publication at every admitted broadcast -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator SignedPrep Routing ProcessorSlots JointHeader
open CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports

variable {R r t d link inner n w reserve dim tally : ℕ} {Edge : Type}
    {G : Wiring R r t d link inner n Edge} {args : Fin (R+1) → UnitAddresses}
    {live : Fin d → Bool} {L : WireLayout (R+1) r link} {fixed : Block (R+1)}
    {hw : 0<w} {size : ∀ u, (args u).header=L.header} {base : Fin (R+1) → ℕ}
    {fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u)}
    {ar : CubeArena.Layout}
local notation "cap" => declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s
variable {width : L.header=PositiveFields.width reserve ar.n ar.header.d
      (declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s) (R+1) dim tally}
    {gen : Fragment IO}
    {U : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext} → Fin (R+1) → PinStart gen n w}
    {ib hb sb : Fin (R+1) → ℕ}
    {pinWidth : ∀ x u, (U x u).guessWidth=(G.pinLayout u (ib u) (hb u) (sb u)).guessWidth}
    {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ}
    {owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1)}
    {S : SourceReports ar owners} {rawPin : Fin d → Bool}
    {profile : Fin reserve → Bool} {claim : Fin ((R+1)*dim*tally) → Bool}

local notation "Fields" => PositiveFields reserve ar.n ar.header.d cap (R+1) dim tally
local notation3 (prettyPrint := false) "p(" c ")" => (⟨profile,c,claim⟩ : Fields)
local notation3 (prettyPrint := false) "head" => fun c : RawBroadcast ar => (p(c)).bits
local notation "headers" => positiveExteriorFieldsEquiv G args live L fixed hw size base fit width
local notation3 (prettyPrint := false) "PF(" c "," wire "," same ")" =>
  pinnedBroadcastFrame G args live L fixed hw size base fit ar width U ib hb sb pinWidth rawPin profile claim c wire same
variable {allowed : RawBroadcast ar → Prop} {template : DiagonalTallyPacketEmit.Frame} {entries : ℕ}


set_option maxRecDepth 8000
set_option maxHeartbeats 1600000

/-- A decoder supplied with its own per-broadcast native builders and its
successful public tests. Each returned publication and report cut belongs to
the frame selected once for that very broadcast. -/
noncomputable def checkedReadbackOfPinnedBuilders {Passed : Prop} {Result : Sort*}
    (route : AdmittedPinnedFrames G args live L fixed hw size base fit ar width U ib hb sb pinWidth id owners S
      rawPin profile claim allowed template entries → Passed → Result)
    {Publication : ∀ (c : CheckedBroadcast ar) (_ : allowed c.val) (wire : WireLayout (R+1) r link)
      (same : wire.header=L.header), PF(c.val,wire,same) → Type*}
    {K : ∀ (c : CheckedBroadcast ar) (ok : allowed c.val) (wire : WireLayout (R+1) r link)
      (same : wire.header=L.header) (F : PF(c.val,wire,same)), F.Builders fixed id owners →
        Publication c ok wire same F → Prop}
    (real : ∀ (c : CheckedBroadcast ar) (ok : allowed c.val),
      ∃ (wire : WireLayout (R+1) r link) (same : wire.header=L.header) (F : PF(c.val,wire,same))
        (B : F.Builders fixed id owners), F.SourceAgreement fixed S B ∧ F.ObservedBuilders fixed id owners template entries B ∧
          ∃ sites : Publication c ok wire same F, K c ok wire same F B sites) (checks : Passed) :
    Diagonal.CheckedRouteReadback route
      (fun chosen => ∀ (c : CheckedBroadcast ar) (ok : allowed c.val),
        Publication c ok (chosen.wire c.val) (chosen.extent c.val) (chosen.frame c ok))
      (fun chosen sites => ∀ (c : CheckedBroadcast ar) (ok : allowed c.val),
        K c ok (chosen.wire c.val) (chosen.extent c.val) (chosen.frame c ok) (chosen.builder c ok) (sites c ok) ∧
        (chosen.frame c ok).ReportCutsOn fixed S (chosen.builder c ok) (chosen.source c ok)) := by
  exact Diagonal.CheckedRouteReadback.ofReturns route
    (admittedPinnedFrames_with_publications G args live L fixed hw size base fit ar width U ib hb sb pinWidth
      id owners S rawPin profile claim allowed template entries Publication K real) checks

end TeamContraction

end BorderVNP
end Computability
end OAI
