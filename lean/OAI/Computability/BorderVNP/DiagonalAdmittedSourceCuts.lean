import OAI.Computability.BorderVNP.DiagonalSourceReportInputs
import OAI.Computability.BorderVNP.DiagonalAdmittedPinnedFrames

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # The report observations of the selected admitted writer frames -/

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

set_option maxHeartbeats 500000
set_option maxRecDepth 7000

/-- The source reports are the ones read by the chosen writer frame, on
its own preparation inverse. This statement ranges over every source
proposal, including those later rejected by private computation. -/
def PreparationFrame.ReportCutsOn (agree : F.SourceAgreement fixed S B) : Prop :=
  ∀ (q : {v : Declared ar owners decl // S.pins v.val}) (r : S.actual q.val.val) (u : Fin (R+1)),
    let full := (F.sourceEquiv fixed S B agree).symm ⟨q,r⟩
    let visit := (visitsEquiv id (pub full.1 u) (mac full.1 u) (reg full.1 u) (mem full.1 u)).symm (full.2 u)
    ∃ cursor description, Nonempty (ReportArgumentCut visit.reports (r u) cursor description)

/-- Observing the original physical source inverse supplies the cut for
every team, uniformly in the proposed report tape. -/
theorem PreparationFrame.reportCutsOn (agree : F.SourceAgreement fixed S B) :
    F.ReportCutsOn fixed S B agree := by
  intro q r u
  exact ⟨_,_,F.sourceEquiv_report_cut fixed S B agree q r u⟩

end TeamContraction

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
local notation3 (prettyPrint := false) "PF(" c "," wire "," same ")" =>
  pinnedBroadcastFrame G args live L fixed hw size base fit ar width U ib hb sb pinWidth rawPin profile claim c wire same
variable (allowed : RawBroadcast ar → Prop) (template : DiagonalTallyPacketEmit.Frame) (entries : ℕ)

set_option maxRecDepth 7000
set_option maxHeartbeats 1200000

/-- Select the implementation, its extra writer properties, and the actual
unscreened report cuts simultaneously. Source observations use precisely
the builder and agreement proofs retained by the chosen frame. -/
theorem admittedPinnedFrames_with_report_cuts
    (Q : ∀ (c : CheckedBroadcast ar) (_ : allowed c.val) (wire : WireLayout (R+1) r link)
      (same : wire.header=L.header) (F : PF(c.val,wire,same)), F.Builders fixed id owners → Prop)
    (real : ∀ (c : CheckedBroadcast ar) (a : allowed c.val),
      ∃ (wire : WireLayout (R+1) r link) (same : wire.header=L.header) (F : PF(c.val,wire,same))
        (B : F.Builders fixed id owners), F.SourceAgreement fixed S B ∧ F.ObservedBuilders fixed id owners template entries B ∧
        Q c a wire same F B) :
    ∃ chosen : AdmittedPinnedFrames G args live L fixed hw size base fit ar width U ib hb sb pinWidth id owners S
      rawPin profile claim allowed template entries,
      ∀ (c : CheckedBroadcast ar) (a : allowed c.val),
        Q c a (chosen.wire c.val) (chosen.extent c.val) (chosen.frame c a) (chosen.builder c a) ∧
        (chosen.frame c a).ReportCutsOn fixed S (chosen.builder c a) (chosen.source c a) := by
  obtain ⟨chosen,held⟩ := admittedPinnedFrames_with G args live L fixed hw size base fit ar width U ib hb sb pinWidth
    id owners S rawPin profile claim allowed template entries Q real
  exact ⟨chosen,fun c a => ⟨held c a,(chosen.frame c a).reportCutsOn fixed S (chosen.builder c a) (chosen.source c a)⟩⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
