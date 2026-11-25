import OAI.Computability.BorderVNP.DiagonalPinnedBroadcastRouting
import OAI.Computability.BorderVNP.DiagonalRoutedReportCutBroadcast
import OAI.Computability.BorderVNP.DiagonalBareOwnedHandoff

/-! # Actual report inputs at the positive pinned preparation -/

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
variable (wire : RawBroadcast ar → WireLayout (R+1) r link) (extent : ∀ c, (wire c).header=L.header)
local notation3 (prettyPrint := false) "extentEquiv(" c ")" =>
  HeaderExterior.changeLayout L (wire c) (extent c) (p(c)).bits
local notation3 (prettyPrint := false) "team(" c "," ext "," u ")" => U ((headers).symm ⟨p(c),(extentEquiv(c)).symm ext⟩) u
local notation3 (prettyPrint := false) "afterPin(" c "," ext "," u ")" => (team(c,ext,u)).pins
  ((Equiv.arrowCongr (finCongr (pinWidth ((headers).symm ⟨p(c),(extentEquiv(c)).symm ext⟩) u).symm) (Equiv.refl Bool))
    ((G.jointGuess ib hb sb).symm rawPin u))
local notation3 (prettyPrint := false) "pubAt" => fun (c : RawBroadcast ar) (ext : HeaderExterior (wire c) (p(c)).bits)
  (u : Fin (R+1)) => (team(c,ext,u)).pub
local notation3 (prettyPrint := false) "macAt" => fun (c : RawBroadcast ar) (ext : HeaderExterior (wire c) (p(c)).bits)
  (u : Fin (R+1)) => CompactMachine.install gen n (team(c,ext,u)).routines
local notation3 (prettyPrint := false) "regAt" => fun (c : RawBroadcast ar) (ext : HeaderExterior (wire c) (p(c)).bits)
  (u : Fin (R+1)) => (afterPin(c,ext,u)).val.2.1
local notation3 (prettyPrint := false) "memAt" => fun (c : RawBroadcast ar) (ext : HeaderExterior (wire c) (p(c)).bits)
  (u : Fin (R+1)) => (afterPin(c,ext,u)).val.2.2
local notation3 (prettyPrint := false) "runs(" c ")" => ((ext : HeaderExterior L (p(c)).bits) ×
  pinnedPreps G args live U ib hb sb pinWidth id ((headers).symm ⟨p(c),ext⟩) rawPin)


set_option maxHeartbeats 400000
set_option maxRecDepth 7800

/-- The restored physical source follows the same pin digits, register bank
and memory as the positive preparation. Its report scanner and sparse
argument launcher realize the original report assignment on that prefix. -/
theorem routedPinnedPreparations_reportCut
    (allowed : RawBroadcast ar → Prop)
    (checked : ∀ c, runs(c) → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners,
      allowed (routeBroadcast ar owners q).val)
    (frames : ∀ c : CheckedBroadcast ar, allowed c.val → PreparationFrame G (wire c.val) ar (decodedBroadcast ar c.val)
      (p(c.val)).bits live (pubAt c.val) (macAt c.val) (regAt c.val) (memAt c.val))
    (builders : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).Builders fixed id owners)
    (source : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).SourceAgreement fixed S (builders c a))
    (q : {v : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners // S.pins v}) (reports : S.actual q.val) (u : Fin (R+1)) :
    let E := routedPinnedPreparations G args live L fixed hw size base fit ar width U ib hb sb pinWidth id owners
      S rawPin profile claim wire extent allowed checked honest frames builders source
    let full := E.symm ⟨q,reports⟩
    let ext := (headers).symm ⟨p(full.1),full.2.1⟩
    let starts := U ext
    let prefixes := fun u => (⟨_,full.2.2 u⟩ : (starts u).Prefix id)
    ∃ cur desc, Nonempty (ReportArgumentCut ((starts u).visited (prefixes u)).reports (reports u) cur desc) := by
  intro E full ext starts prefixes
  let retitle (k : RawBroadcast ar) : runs(k) ≃ BroadcastPreparations ar id wire head pubAt macAt regAt memAt k :=
    Equiv.sigmaCongr (extentEquiv(k)) (fun _ => Equiv.refl _)
  let accepted := fun k z => checked k ((retitle k).symm z)
  let relay := allBroadcastPreparedEquiv G ar owners id S wire fixed head live pubAt macAt regAt memAt
    allowed accepted honest frames builders source
  let observe (z : Σ c : RawBroadcast ar, runs(c)) :=
    let x := (headers).symm ⟨p(z.1),z.2.1⟩
    let pr : (U x u).Prefix id := ⟨_,z.2.2 u⟩
    ∃ cur desc, Nonempty (ReportArgumentCut ((U x u).visited pr).reports (reports u) cur desc)
  let read (z : Σ k : RawBroadcast ar, BroadcastPreparations ar id wire head pubAt macAt regAt memAt k) :=
    ∃ cur desc, broadcastReportCutAt ar id wire head pubAt macAt regAt memAt u (reports u) cur desc z
  have move (z : Σ k : RawBroadcast ar, BroadcastPreparations ar id wire head pubAt macAt regAt memAt k) :
      observe ((Equiv.sigmaCongrRight retitle).symm z) = read z := by
    obtain ⟨k,x,r⟩ := z
    rfl
  have restore : full=(Equiv.sigmaCongrRight retitle).symm (relay.symm ⟨q,reports⟩) := by
    dsimp only [full,E,routedPinnedPreparations,relay,accepted,retitle]
    simp only [Equiv.symm_trans_apply]
  change observe full
  apply ((congrArg observe restore).trans (move _)).mpr
  exact allBroadcastPreparedEquiv_exists_reportCut G ar owners id S wire fixed head live pubAt macAt regAt memAt
    allowed accepted honest frames builders source q reports u

end TeamContraction

end BorderVNP
end Computability
end OAI
