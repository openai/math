import OAI.Computability.BorderVNP.DiagonalAdmittedReturnedOwner

/-! # The full original writer and its observed ownership scan -/

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


variable {G args live L fixed hw size base fit ar width U ib hb sb pinWidth id owners S rawPin profile claim}
variable {allowed : RawBroadcast ar → Prop} {template : DiagonalTallyPacketEmit.Frame} {count : ℕ}

/-- The complete writer, including its stored row and substitution array,
on the original preparation inverse of the admitted frames. -/
theorem AdmittedPinnedFrames.originalObservation
    (candidates : AdmittedPinnedFrames G args live L fixed hw size base fit ar width U ib hb sb pinWidth
      id owners S rawPin profile claim allowed template count)
    (checked : ∀ c, runs(c) → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners,
      allowed (routeBroadcast ar owners q).val)
    (q : {v : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners // S.pins v}) (reports : S.actual q.val) :
    let E := candidates.preparations G args live L fixed hw size base fit ar width U ib hb sb pinWidth id owners
      S rawPin profile claim allowed template count checked honest
    let full := E.symm ⟨q,reports⟩
    let c := routeBroadcast ar owners q.val
    let f := candidates.frame c (honest q.val)
    let raw := declaredWords ar owners (decodedBroadcast ar c.val) ⟨q.val,(decoded_routeBroadcast ar owners q.val).symm⟩
    let selected : Matching ar owners (decodedBroadcast ar c.val) raw.val :=
      ⟨q.val,(decoded_routeBroadcast ar owners q.val).symm,rfl⟩
    f.OwnedRouteOn fixed id owners template count raw selected
      (pinnedOwnedHistory G args live L fixed hw size base fit ar width U ib hb sb pinWidth id rawPin profile claim
        full) :=
  routedPinnedPreparations_observed G args live L fixed hw size base fit ar width U ib hb sb pinWidth
    id owners S rawPin profile claim candidates.wire candidates.extent allowed checked honest candidates.frame
    candidates.builder candidates.source template count candidates.observed q reports

end TeamContraction

end BorderVNP
end Computability
end OAI
