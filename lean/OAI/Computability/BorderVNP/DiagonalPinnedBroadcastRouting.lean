import OAI.Computability.BorderVNP.DiagonalExteriorParsedPrefixes
import OAI.Computability.BorderVNP.DiagonalCommonHeaderExtent
import OAI.Computability.BorderVNP.DiagonalAllBroadcastReadback

/-! # Native routed preparations on the actual substituted pin and parsed header -/

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

/-- At one true profile and an arbitrary claimed subtotal word, extract the
routed assignment and the actual report tapes from every simultaneously
returning pre-call prefix. The inverse starts all processors with precisely
the local guesses of the same substituted raw pin. -/
noncomputable def routedPinnedPreparations (allowed : RawBroadcast ar → Prop)
    (checked : ∀ c, runs(c) → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners,
      allowed (routeBroadcast ar owners q).val)
    (frames : ∀ c : CheckedBroadcast ar, allowed c.val → PreparationFrame G (wire c.val) ar (decodedBroadcast ar c.val)
      (p(c.val)).bits live (pubAt c.val) (macAt c.val) (regAt c.val) (memAt c.val))
    (builders : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).Builders fixed id owners)
    (source : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).SourceAgreement fixed S (builders c a)) :
    (Σ c : RawBroadcast ar, runs(c)) ≃
      Σ q : {v : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners // S.pins v}, S.actual q.val := by
  let retitle (c : RawBroadcast ar) : runs(c) ≃ BroadcastPreparations ar id wire head pubAt macAt regAt memAt c :=
    Equiv.sigmaCongr (extentEquiv(c)) (fun _ => Equiv.refl _)
  let route := allBroadcastPreparedEquiv G ar owners id S wire fixed head live pubAt macAt regAt memAt
    allowed (fun c z => checked c ((retitle c).symm z)) honest frames builders source
  exact (Equiv.sigmaCongrRight retitle).trans route

set_option maxHeartbeats 180000 in
/-- Replaying a source assignment determines both the parsed cube bits and
the complete raw physical exterior, even though the checked relay widths
vary with the public declaration. -/
theorem routedPinnedPreparations_inverse
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
    (E.symm ⟨q,reports⟩).1 = c.val ∧
      (E.symm ⟨q,reports⟩).2.1.val = cubeExterior G (wire c.val) f.tab f.row f.dataDir f.privatePlacement
        f.livePlacement f.guess f.rows (Scatter.Assignment.Routed.encode owners q.val).shared (p(c.val)).bits f.length := by
  intro E c f
  let retitle (k : RawBroadcast ar) : runs(k) ≃ BroadcastPreparations ar id wire head pubAt macAt regAt memAt k :=
    Equiv.sigmaCongr (extentEquiv(k)) (fun _ => Equiv.refl _)
  let accepted := fun k z => checked k ((retitle k).symm z)
  constructor
  · rfl
  · exact allBroadcastPreparedEquiv_exterior G ar owners id S wire fixed head live pubAt macAt regAt memAt
      allowed accepted honest frames builders source q reports

end TeamContraction

end BorderVNP
end Computability
end OAI
