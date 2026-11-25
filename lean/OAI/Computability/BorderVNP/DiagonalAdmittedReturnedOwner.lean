import OAI.Computability.BorderVNP.DiagonalPinnedRouteObservation
import OAI.Computability.BorderVNP.DiagonalBootLookupOwnership
import OAI.Computability.BorderVNP.DiagonalAdmittedPinnedFrames

/-! # A returned ownership receipt from the actual admitted pinned writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Scatter Scatter.Assignment SignedPrep TeamRows Tally
open DiagonalTallyPacketEmit CellMacro.Generator JointHeader ProcessorSlots SignedTaskArena FiniteEvaluator

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} (sa : SignedTaskArena.Layout) {decl : LengthDeclaration sa.cube.n sa.cube.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w}
    {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    {owners : (Packet sa.cube.n sa.cube.header.d sa.cube.header.blocks →
      Selector sa.cube.n sa.cube.K sa.cube.h) → Fin sa.cube.header.d → Fin (R+1)}
    (F : PreparationFrame G L sa.cube decl header pin pub mac reg mem)

/-- Recover the native receipt on the original exterior, with the exact routed shared words. -/
theorem PreparationFrame.OwnedRouteOn.returned (template : DiagonalTallyPacketEmit.Frame) (count : ℕ)
    (raw : SharedWords sa.cube decl) (q : Matching sa.cube owners decl raw.val)
    (run : TeamRows.Returns (Fin (R+1)) sa.cube w) (ext : Exterior R r link → Bool)
    (same : ext=(F.replay fixed raw).1.val)
    (issued : F.OwnedRouteOn fixed sa.id owners template count raw q run) :
    F.ReturnedOwnershipAt sa (F.replay fixed raw).1 ext template count q.val run := by
  subst ext
  obtain ⟨H,f,_,_,writer,_,_,rows,handoff,observed⟩ := issued
  exact ⟨H,f,writer,rows.trans q.property.2.symm,handoff,observed⟩

end TeamContraction

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
variable (wire : RawBroadcast sa.cube → WireLayout (R+1) r link) (extent : ∀ c, (wire c).header=L.header)
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
local notation3 (prettyPrint := false) "runs(" c ")" => ((ext : HeaderExterior L (p(c)).bits) ×
  pinnedPreps G args live U ib hb sb pinWidth sa.id ((headers).symm ⟨p(c),ext⟩) rawPin)

set_option maxHeartbeats 1000000 in
/-- The admitted frame's observed builder suffices for the returned owner at this native prefix.
The exterior is the one on the source of the actual pinned equivalence. -/
theorem routedPinnedPreparations_returnedObserved
    (allowed : RawBroadcast sa.cube → Prop)
    (checked : ∀ c, runs(c) → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) owners, allowed (routeBroadcast sa.cube owners q).val)
    (frames : ∀ c : CheckedBroadcast sa.cube, allowed c.val → PreparationFrame G (wire c.val) sa.cube (decodedBroadcast sa.cube c.val)
      (p(c.val)).bits live (pubAt c.val) (macAt c.val) (regAt c.val) (memAt c.val))
    (builders : ∀ (c : CheckedBroadcast sa.cube) (a : allowed c.val), (frames c a).Builders fixed sa.id owners)
    (source : ∀ (c : CheckedBroadcast sa.cube) (a : allowed c.val), (frames c a).SourceAgreement fixed S (builders c a))
    (template : DiagonalTallyPacketEmit.Frame) (count : ℕ)
    (observed : ∀ c (a : allowed c.val), (frames c a).ObservedBuilders fixed sa.id owners template count (builders c a))
    (q : {v : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) owners // S.pins v}) (reports : S.actual q.val) :
    let E := routedPinnedPreparations G args live L fixed hw size base fit sa.cube width U ib hb sb pinWidth sa.id owners
      S rawPin profile claim wire extent allowed checked honest frames builders source
    let full := E.symm ⟨q,reports⟩
    let c := routeBroadcast sa.cube owners q.val
    let f := frames c (honest q.val)
    let raw := declaredWords sa.cube owners (decodedBroadcast sa.cube c.val) ⟨q.val,(decoded_routeBroadcast sa.cube owners q.val).symm⟩
    let origin := (f.replay fixed raw).1
    f.ReturnedOwnershipAt sa origin full.2.1.val template count q.val
      (pinnedOwnedHistory G args live L fixed hw size base fit sa.cube width U ib hb sb pinWidth sa.id rawPin profile claim full) := by
  intro E full c f raw origin
  let selected : Matching sa.cube owners (decodedBroadcast sa.cube c.val) raw.val :=
    ⟨q.val,(decoded_routeBroadcast sa.cube owners q.val).symm,rfl⟩
  have eqExt : full.2.1.val=origin.val := (routedPinnedPreparations_inverse G args live L fixed hw size base fit sa.cube
    width U ib hb sb pinWidth sa.id owners S rawPin profile claim wire extent allowed checked honest frames builders source
    q reports).2.trans (f.replay_exterior fixed raw).symm
  apply PreparationFrame.OwnedRouteOn.returned sa fixed f template count raw selected _ _ eqExt
  exact routedPinnedPreparations_observed G args live L fixed hw size base fit sa.cube width U ib hb sb pinWidth sa.id
    owners S rawPin profile claim wire extent allowed checked honest frames builders source template count observed q reports

variable {G args live L fixed hw size base fit sa width U ib hb sb pinWidth owners S rawPin profile claim}
variable {allowed : RawBroadcast sa.cube → Prop} {template : DiagonalTallyPacketEmit.Frame} {count : ℕ}

/-- Evaluate this very candidate's stored observation on the source reconstructed by its own route equivalence. -/
theorem AdmittedPinnedFrames.returnedOwner
    (candidates : AdmittedPinnedFrames G args live L fixed hw size base fit sa.cube width U ib hb sb pinWidth
      sa.id owners S rawPin profile claim allowed template count)
    (checked : ∀ c, runs(c) → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) owners,
      allowed (routeBroadcast sa.cube owners q).val)
    (q : {v : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) owners // S.pins v}) (reports : S.actual q.val) :
    let E := candidates.preparations G args live L fixed hw size base fit sa.cube width U ib hb sb pinWidth sa.id owners
      S rawPin profile claim allowed template count checked honest
    let full := E.symm ⟨q,reports⟩
    let c := routeBroadcast sa.cube owners q.val
    let f := candidates.frame c (honest q.val)
    let raw := declaredWords sa.cube owners (decodedBroadcast sa.cube c.val) ⟨q.val,(decoded_routeBroadcast sa.cube owners q.val).symm⟩
    let origin := (f.replay fixed raw).1
    f.ReturnedOwnershipAt sa origin full.2.1.val template count q.val
      (pinnedOwnedHistory G args live L fixed hw size base fit sa.cube width U ib hb sb pinWidth sa.id rawPin profile claim full) :=
  routedPinnedPreparations_returnedObserved G args live L fixed hw size base fit sa width U
    ib hb sb pinWidth owners S rawPin profile claim candidates.wire candidates.extent allowed checked honest candidates.frame
    candidates.builder candidates.source template count candidates.observed q reports

end TeamContraction

end BorderVNP
end Computability
end OAI
