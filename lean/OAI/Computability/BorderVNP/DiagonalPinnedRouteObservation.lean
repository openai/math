import OAI.Computability.BorderVNP.DiagonalObservedFrameBuilders
import OAI.Computability.BorderVNP.DiagonalPinnedOwnerReceipt

/-! # A genuine physical selector and writer at each restored pinned prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment DiagonalTallyPacketEmit

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {L : WireLayout (R+1) r link} {ar : CubeArena.Layout} {decl : LengthDeclaration ar.n ar.header.d}
    (fixed : Block (R+1)) {header : List Bool} {pin : Fin d → Bool}
    {pub : HeaderExterior L header → Fin (R+1) → Arg → Word w}
    {mac : HeaderExterior L header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior L header → Fin (R+1) → Bank w} {mem : HeaderExterior L header → Fin (R+1) → Memory w}
    (F : PreparationFrame G L ar decl header pin pub mac reg mem)
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (template : Frame) (count : ℕ)

/-- The delivery and observed owner held by one actual restored family of native scanner visits. -/
def PreparationFrame.OwnedRouteOn (raw : SharedWords ar decl) (q : Matching ar owners decl raw.val)
    (endRows : TeamRows.Returns (Fin (R+1)) ar w) : Prop :=
  let z := F.replay fixed raw
  ∃ (H : Fin (R+1) → TeamHistory w)
    (f : ReturnedDelivery G pin z.1.val L F.dataDir F.privatePlacement F.livePlacement F.cellOwner
      F.origin F.stride H (fun u => G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))),
    f.table=F.tab ∧ f.row=F.row ∧ SharedWriters f F.rows (F.source z.1) ∧
    (∀ u, (H u).pub=pub z.1 u ∧ (H u).macros=mac z.1 u ∧ (H u).history.val.2=(z.2 u).val.2) ∧
    (∀ u, Pins.SubstitutionAt (G.pinLayout u (F.inputBase u) (F.columnBase u) (F.referenceBase u))
      (F.guess u) (H u).initial) ∧ f.receivedRows F.rows F.group=raw.val ∧
    OwnedHandoff f F.rows (F.source z.1) ar decl F.group template id count endRows ∧
      ObservedOwned ar decl F.group endRows owners (f.receivedRows F.rows F.group) q.val

theorem PreparationFrame.ObservedBuilders.onFamily {B : F.Builders fixed id owners}
    (data : F.ObservedBuilders fixed id owners template count B)
    (raw : SharedWords ar decl) (q : Matching ar owners decl raw.val)
    {family : TeamRows.Returns (Fin (R+1)) ar w} (same : family=(B raw).ownedAt q) :
    F.OwnedRouteOn fixed id owners template count raw q family := by
  subst family
  obtain ⟨H,f,table,row,writer,banks,pins,values,accepted⟩ := data raw
  obtain ⟨handoff,selected⟩ := accepted q
  refine ⟨H,f,table,row,writer,banks,pins,values,handoff,?_⟩
  rw [values]
  exact selected

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

/-- The actual restored pin tuple has its own received-writer handoff, owner selection, and the
entire physical input from which the emitted owner table is read. -/
theorem routedPinnedPreparations_observed
    (allowed : RawBroadcast ar → Prop)
    (checked : ∀ c, runs(c) → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners,
      allowed (routeBroadcast ar owners q).val)
    (frames : ∀ c : CheckedBroadcast ar, allowed c.val → PreparationFrame G (wire c.val) ar (decodedBroadcast ar c.val)
      (p(c.val)).bits live (pubAt c.val) (macAt c.val) (regAt c.val) (memAt c.val))
    (builders : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).Builders fixed id owners)
    (source : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).SourceAgreement fixed S (builders c a))
    (template : DiagonalTallyPacketEmit.Frame) (count : ℕ)
    (observed : ∀ (c : CheckedBroadcast ar) (a : allowed c.val),
      (frames c a).ObservedBuilders fixed id owners template count (builders c a))
    (q : {v : NativeAssignments.Routed (b:=ar.b) (s:=ar.s) owners // S.pins v}) (reports : S.actual q.val) :
    let E := routedPinnedPreparations G args live L fixed hw size base fit ar width U ib hb sb pinWidth id owners
      S rawPin profile claim wire extent allowed checked honest frames builders source
    let c := routeBroadcast ar owners q.val
    let f := frames c (honest q.val)
    let raw := declaredWords ar owners (decodedBroadcast ar c.val) ⟨q.val,(decoded_routeBroadcast ar owners q.val).symm⟩
    let selected : Matching ar owners (decodedBroadcast ar c.val) raw.val :=
      ⟨q.val,(decoded_routeBroadcast ar owners q.val).symm,rfl⟩
    f.OwnedRouteOn fixed id owners template count raw selected
      (pinnedOwnedHistory G args live L fixed hw size base fit ar width U ib hb sb pinWidth id rawPin profile claim
        (E.symm ⟨q,reports⟩)) := by
  intro E c f raw selected
  apply PreparationFrame.ObservedBuilders.onFamily fixed f id owners template count (observed c (honest q.val))
  have read := routedPinnedPreparations_owned_history G args live L fixed hw size base fit ar width U ib hb sb pinWidth
    id owners S rawPin profile claim wire extent allowed checked honest frames builders source q reports
  unfold SignedPrep.DeliveredBuilder.ownedAt
  with_reducible exact read

end TeamContraction

end BorderVNP
end Computability
end OAI
