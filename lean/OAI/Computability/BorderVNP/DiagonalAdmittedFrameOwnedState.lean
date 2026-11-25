import OAI.Computability.BorderVNP.DiagonalSupportedParsedFields
import OAI.Computability.BorderVNP.DiagonalAdmittedReportCut
import OAI.Computability.BorderVNP.DiagonalPinnedLookupMemory

/-! # Reading the native ownership return on the source of an admitted frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator SignedPrep Routing ProcessorSlots JointHeader
open CellMacro.Generator BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports
open FiniteEvaluator SignedTaskArena Scatter.Assignment

variable {R r t d link inner n w reserve dim tally : ℕ} {Edge : Type}
    (G : Wiring R r t d link inner n Edge) (args : Fin (R+1) → UnitAddresses)
    (live : Fin d → Bool) (L : WireLayout (R+1) r link) (fixed : Block (R+1))
    (hw : 0<w) (size : ∀ u, (args u).header=L.header) (base : Fin (R+1) → ℕ)
    (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (sa : SignedTaskArena.Layout)
local notation "cap" => declarationCap sa.cube.n sa.cube.header.d sa.cube.header.blocks sa.cube.b sa.cube.h sa.cube.s
variable (width : L.header=PositiveFields.width reserve sa.cube.n sa.cube.header.d
      (declarationCap sa.cube.n sa.cube.header.d sa.cube.header.blocks sa.cube.b sa.cube.h sa.cube.s) (R+1) dim tally)
    {gen : Fragment IO}
    (U : {ext : Exterior R r link → Bool // PositiveExterior G args live w ext} → Fin (R+1) → PinStart gen n w)
    (ib hb sb : Fin (R+1) → ℕ)
    (pinWidth : ∀ x u, (U x u).guessWidth=(G.pinLayout u (ib u) (hb u) (sb u)).guessWidth)
    (owners : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks → Selector sa.cube.n sa.cube.K sa.cube.h) → Fin sa.cube.header.d → Fin (R+1))
    (S : SourceReports sa.cube owners) (rawPin : Fin d → Bool)
    (profile : Fin reserve → Bool) (claim : Fin ((R+1)*dim*tally) → Bool)

local notation "Fields" => PositiveFields reserve sa.cube.n sa.cube.header.d cap (R+1) dim tally
local notation3 (prettyPrint := false) "p(" c ")" => (⟨profile,c,claim⟩ : Fields)
local notation3 (prettyPrint := false) "head" => fun c : RawBroadcast sa.cube => (p(c)).bits
local notation "headers" => positiveExteriorFieldsEquiv G args live L fixed hw size base fit width
variable (allowed : RawBroadcast sa.cube → Prop) (template : DiagonalTallyPacketEmit.Frame) (entries : ℕ)
    (F : AdmittedPinnedFrames G args live L fixed hw size base fit sa.cube width U ib hb sb pinWidth sa.id
      owners S rawPin profile claim allowed template entries)

local notation3 (prettyPrint := false) "wire" => F.wire
local notation3 (prettyPrint := false) "extent" => F.extent
local notation3 (prettyPrint := false) "extentEquiv(" c ")" =>
  HeaderExterior.changeLayout L (wire c) (extent c) (p(c)).bits
local notation3 (prettyPrint := false) "team(" c "," ext "," u ")" => U ((headers).symm ⟨p(c),(extentEquiv(c)).symm ext⟩) u
local notation3 (prettyPrint := false) "afterPin(" c "," ext "," u ")" => (team(c,ext,u)).pins
  ((Equiv.arrowCongr (finCongr (pinWidth ((headers).symm ⟨p(c),(extentEquiv(c)).symm ext⟩) u).symm) (Equiv.refl Bool))
    ((G.jointGuess ib hb sb).symm rawPin u))
local notation3 (prettyPrint := false) "pubAt" => fun (c : RawBroadcast sa.cube) (ext : HeaderExterior (wire c) (p(c)).bits)
  (u : Fin (R+1)) => (team(c,ext,u)).pub
local notation3 (prettyPrint := false) "macAt" => fun (c : RawBroadcast sa.cube) (ext : HeaderExterior (wire c) (p(c)).bits)
  (u : Fin (R+1)) => CompactMachine.install gen n (team(c,ext,u)).routines
local notation3 (prettyPrint := false) "regAt" => fun (c : RawBroadcast sa.cube) (ext : HeaderExterior (wire c) (p(c)).bits)
  (u : Fin (R+1)) => (afterPin(c,ext,u)).val.2.1
local notation3 (prettyPrint := false) "memAt" => fun (c : RawBroadcast sa.cube) (ext : HeaderExterior (wire c) (p(c)).bits)
  (u : Fin (R+1)) => (afterPin(c,ext,u)).val.2.2
local notation3 (prettyPrint := false) "sourceBroadcast(" x ")" => routeBroadcast sa.cube owners x
set_option maxHeartbeats 700000
set_option maxRecDepth 9000

/-- The actual source ownership return reconstructed for this proposed
route and report. It records the public registers and the full native trace,
register bank, and memory on the admitted broadcast. -/
noncomputable def AdmittedPinnedFrames.sourceOwnedState
    (honest : ∀ q : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners, allowed (routeBroadcast sa.cube owners q).val)
    (q : {v : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners // S.pins v}) (reports : S.actual q.val) (u : Fin (R+1)) :
    (Arg → Word w) × List (TeamRAM.Event w) × Bank w × Memory w :=
    let c := routeBroadcast sa.cube owners q.val
    let original := (PreparationFrame.sourceEquiv (G:=G) (L:=wire (sourceBroadcast(q.val)).val) (ar:=sa.cube)
      (decl:=decodedBroadcast sa.cube (sourceBroadcast(q.val)).val) (header:=head (sourceBroadcast(q.val)).val) (pin:=live)
      (pub:=pubAt (sourceBroadcast(q.val)).val) (mac:=macAt (sourceBroadcast(q.val)).val) (reg:=regAt (sourceBroadcast(q.val)).val) (mem:=memAt (sourceBroadcast(q.val)).val)
      (id:=sa.id) (owners:=owners) fixed S (F.frame (sourceBroadcast(q.val)) (honest q.val)) (F.builder (sourceBroadcast(q.val)) (honest q.val))
      (F.source (sourceBroadcast(q.val)) (honest q.val))).symm
      ⟨⟨⟨q.val,(decoded_routeBroadcast sa.cube owners q.val).symm⟩,q.property⟩,reports⟩
    let v := (visitsEquiv sa.id (pubAt c.val original.1 u) (macAt c.val original.1 u)
      (regAt c.val original.1 u) (memAt c.val original.1 u)).symm (original.2 u)
    (pubAt c.val original.1 u,v.owned.val)

/-- Restoring the admitted frame's report preparation gives the exact
ownership return observed on its source-equivalence inverse. -/
theorem AdmittedPinnedFrames.pinned_ownedSourceState
    (checked : ∀ c, ParsedPreCall G args live L fixed hw size base fit width U ib hb sb pinWidth sa.id rawPin
      ⟨profile,c,claim⟩ → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners, allowed (routeBroadcast sa.cube owners q).val)
    (q : {v : Routed (b:=sa.cube.b) (s:=sa.cube.s) owners // S.pins v}) (reports : S.actual q.val) (u : Fin (R+1)) :
    let E := F.preparations G args live L fixed hw size base fit sa.cube width U ib hb sb pinWidth sa.id owners S
      rawPin profile claim allowed template entries checked honest
    pinnedOwnedStateAt G args live L fixed hw size base fit sa width U ib hb sb pinWidth rawPin profile claim
      (E.symm ⟨q,reports⟩) u = F.sourceOwnedState G args live L fixed hw size base fit sa width U ib hb sb pinWidth
      owners S rawPin profile claim allowed template entries honest q reports u := by
  have seen := routedPinnedPreparations_ownedState G args live L fixed hw size base fit sa width U ib hb sb pinWidth
    owners S rawPin profile claim F.wire F.extent allowed checked honest F.frame F.builder F.source q reports u
  dsimp only [AdmittedPinnedFrames.preparations, AdmittedPinnedFrames.sourceOwnedState]
  dsimp only at seen
  with_reducible exact seen

end TeamContraction

end BorderVNP
end Computability
end OAI
