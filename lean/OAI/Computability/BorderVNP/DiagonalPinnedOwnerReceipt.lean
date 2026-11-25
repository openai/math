import OAI.Computability.BorderVNP.DiagonalPinnedBroadcastRouting
import OAI.Computability.BorderVNP.DiagonalBroadcastOwnerReceipt
import OAI.Computability.BorderVNP.DiagonalBareOwnedHandoff

/-! # Actual owned returns at the pinned original source -/

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

/-- The complete prefix assembled from its actual exterior, restored raw pin, and native return. -/
noncomputable def pinnedOwnedHistory (full : Σ c : RawBroadcast ar,runs(c)) :=
  let ext := (headers).symm ⟨p(full.1),full.2.1⟩
  let starts := U ext
  let prefixes := fun u => (⟨(Equiv.arrowCongr (finCongr (pinWidth ext u).symm) (Equiv.refl Bool))
    ((G.jointGuess ib hb sb).symm rawPin u),full.2.2 u⟩ : (starts u).Prefix id)
  PinStart.ownedVisits (ar:=ar) starts prefixes

private theorem restoredAfterLayoutChange {teams rank legs : ℕ}
    (l m : WireLayout (teams+1) rank legs) (length : m.header=l.header) (h : List Bool)
    (F : HeaderExterior l h → Type) (y : HeaderExterior m h)
    (v : F ((HeaderExterior.changeLayout l m length h).symm y)) :
    let e := HeaderExterior.changeLayout l m length h
    (Equiv.sigmaCongr (β₁:=F) (β₂:=fun x => F (e.symm x)) e (fun x => Equiv.refl (F x))).symm ⟨y,v⟩ =
      ⟨e.symm y,v⟩ := by rfl

private theorem ownedAfterRetitle
    (full : Σ k : RawBroadcast ar,BroadcastPreparations ar id wire head pubAt macAt regAt memAt k) :
    let retitle (k : RawBroadcast ar) : runs(k) ≃ BroadcastPreparations ar id wire head pubAt macAt regAt memAt k :=
      Equiv.sigmaCongr (extentEquiv(k)) (fun _ => Equiv.refl _)
    pinnedOwnedHistory G args live L fixed hw size base fit ar width U ib hb sb pinWidth id rawPin profile claim
        ((Equiv.sigmaCongrRight retitle).symm full) =
      broadcastOwnedHistory ar id wire head pubAt macAt regAt memAt full := by
  intro retitle
  obtain ⟨k,ext,ret⟩ := full
  let steps := fun x : HeaderExterior L (p(k)).bits =>
    pinnedPreps G args live U ib hb sb pinWidth id ((headers).symm ⟨p(k),x⟩) rawPin
  have read := restoredAfterLayoutChange L (wire k) (extent k) (p(k)).bits steps ext ret
  change pinnedOwnedHistory G args live L fixed hw size base fit ar width U ib hb sb pinWidth id rawPin profile claim
    ⟨k,(retitle k).symm ⟨ext,ret⟩⟩ = _
  rw [show (retitle k).symm ⟨ext,ret⟩ = ⟨(extentEquiv(k)).symm ext,ret⟩ from read]
  rfl

set_option maxHeartbeats 1600000 in
/-- The same original native ownership history, with its real direction-specific
macro environment, is reached when the pinned prepared source is restored.
Its public registers, before/after state and all choices agree literally. -/
theorem routedPinnedPreparations_owned_history
    (allowed : RawBroadcast ar → Prop)
    (checked : ∀ c, runs(c) → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners,
      allowed (routeBroadcast ar owners q).val)
    (frames : ∀ c : CheckedBroadcast ar, allowed c.val → PreparationFrame G (wire c.val) ar (decodedBroadcast ar c.val)
      (p(c.val)).bits live (pubAt c.val) (macAt c.val) (regAt c.val) (memAt c.val))
    (builders : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).Builders fixed id owners)
    (source : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).SourceAgreement fixed S (builders c a))
    (q : {v : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners // S.pins v}) (reports : S.actual q.val) :
    let E := routedPinnedPreparations G args live L fixed hw size base fit ar width U ib hb sb pinWidth id owners
      S rawPin profile claim wire extent allowed checked honest frames builders source
    let c := routeBroadcast ar owners q.val
    let f := frames c (honest q.val)
    let raw := declaredWords ar owners (decodedBroadcast ar c.val) ⟨q.val,(decoded_routeBroadcast ar owners q.val).symm⟩
    let z := f.replay fixed raw
    let B := builders c (honest q.val) raw
    let owned := B.owned.symm ⟨q.val,(decoded_routeBroadcast ar owners q.val).symm,rfl⟩
    pinnedOwnedHistory G args live L fixed hw size base fit ar width U ib hb sb pinWidth id rawPin profile claim
        (E.symm ⟨q,reports⟩) =
      RoutingISA.Evaluator.SignedPrep.ownedHistory ar (pubAt c.val z.1) (macAt c.val z.1) (fun u => (B.constants u).val.2.1)
        (fun u => (B.constants u).val.2.2) owned := by
  intro E c f raw z B owned
  let retitle (k : RawBroadcast ar) : runs(k) ≃ BroadcastPreparations ar id wire head pubAt macAt regAt memAt k :=
    Equiv.sigmaCongr (extentEquiv(k)) (fun _ => Equiv.refl _)
  let accepted := fun k z => checked k ((retitle k).symm z)
  have seen := allBroadcastPreparedEquiv_ownedHistory G ar owners id S wire fixed head live pubAt macAt regAt memAt
    allowed accepted honest frames builders source q reports
  let route := allBroadcastPreparedEquiv G ar owners id S wire fixed head live pubAt macAt regAt memAt
    allowed accepted honest frames builders source
  have first := ownedAfterRetitle G args live L fixed hw size base fit ar width U ib hb sb pinWidth id rawPin
    profile claim wire extent (route.symm ⟨q,reports⟩)
  have composed : E = (Equiv.sigmaCongrRight retitle).trans route := by
    dsimp only [E, routedPinnedPreparations, retitle, route, accepted]
  have restored := congrArg (fun equiv : _ ≃ _ => equiv.symm ⟨q,reports⟩) composed
  have front := congrArg (pinnedOwnedHistory G args live L fixed hw size base fit ar width U ib hb sb pinWidth id
    rawPin profile claim) (restored.trans (Equiv.symm_trans_apply (Equiv.sigmaCongrRight retitle) route ⟨q,reports⟩))
  refine front.trans (first.trans ?_)
  with_reducible exact seen

end TeamContraction

end BorderVNP
end Computability
end OAI
