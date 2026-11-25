import OAI.Computability.BorderVNP.DiagonalPinnedBroadcastRouting
import OAI.Computability.BorderVNP.DiagonalBroadcastPreparationRestore
import OAI.Computability.BorderVNP.DiagonalBareOwnedHandoff
import OAI.Computability.BorderVNP.DiagonalTallyGadgetReadback

/-! # The selected gadget lookup in the inverse of the pinned route -/

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

/-- The public words and chronological ownership return at a specified
team of the joint positive pinned preparation. -/
noncomputable def pinnedOwnedStateAt (full : Σ c : RawBroadcast sa.cube, runs(c)) (u : Fin (R+1)) :=
  let ext := (headers).symm ⟨p(full.1),full.2.1⟩
  let start := U ext u
  let pr : start.Prefix sa.id := ⟨(Equiv.arrowCongr (finCongr (pinWidth ext u).symm) (Equiv.refl Bool))
    ((G.jointGuess ib hb sb).symm rawPin u),full.2.2 u⟩
  (start.pub,(start.visited pr).owned.val)

local notation3 (prettyPrint := false) "snap" => pinnedOwnedStateAt G args live L fixed hw size base fit sa width U ib hb sb
  pinWidth rawPin profile claim

local notation3 (prettyPrint := false) "sourceBroadcast(" x ")" => routeBroadcast sa.cube owners x

set_option maxHeartbeats 850000
set_option maxRecDepth 7800

/-- Recover all public argument words and the complete ownership return
from the checked source in the actual pinned machine. This simultaneously
identifies the selected register bank and its physical RAM. -/
theorem routedPinnedPreparations_ownedState
    (allowed : RawBroadcast sa.cube → Prop)
    (checked : ∀ c, runs(c) → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b := sa.cube.b) (s := sa.cube.s) owners,
      allowed (routeBroadcast sa.cube owners q).val)
    (frames : ∀ c : CheckedBroadcast sa.cube, allowed c.val → PreparationFrame G (wire c.val) sa.cube (decodedBroadcast sa.cube c.val)
      (p(c.val)).bits live (pubAt c.val) (macAt c.val) (regAt c.val) (memAt c.val))
    (builders : ∀ (c : CheckedBroadcast sa.cube) (a : allowed c.val), (frames c a).Builders fixed sa.id owners)
    (source : ∀ (c : CheckedBroadcast sa.cube) (a : allowed c.val), (frames c a).SourceAgreement fixed S (builders c a))
    (q : {v : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) owners // S.pins v}) (reports : S.actual q.val) (u : Fin (R+1)) :
    let route := routedPinnedPreparations G args live L fixed hw size base fit sa.cube width U ib hb sb pinWidth sa.id owners
      S rawPin profile claim wire extent allowed checked honest frames builders source
    let full := route.symm ⟨q,reports⟩
    let c := routeBroadcast sa.cube owners q.val
    let original := (PreparationFrame.sourceEquiv (G:=G) (L:=wire (sourceBroadcast(q.val)).val) (ar:=sa.cube)
      (decl:=decodedBroadcast sa.cube (sourceBroadcast(q.val)).val) (header:=head (sourceBroadcast(q.val)).val) (pin:=live)
      (pub:=pubAt (sourceBroadcast(q.val)).val) (mac:=macAt (sourceBroadcast(q.val)).val) (reg:=regAt (sourceBroadcast(q.val)).val) (mem:=memAt (sourceBroadcast(q.val)).val)
      (id:=sa.id) (owners:=owners) fixed S (frames (sourceBroadcast(q.val)) (honest q.val)) (builders (sourceBroadcast(q.val)) (honest q.val))
      (source (sourceBroadcast(q.val)) (honest q.val))).symm
      ⟨⟨⟨q.val,(decoded_routeBroadcast sa.cube owners q.val).symm⟩,q.property⟩,reports⟩
    let v := (visitsEquiv sa.id (pubAt c.val original.1 u) (macAt c.val original.1 u)
      (regAt c.val original.1 u) (memAt c.val original.1 u)).symm (original.2 u)
    snap full u = (pubAt c.val original.1 u,v.owned.val) := by
  let retitle (k : RawBroadcast sa.cube) :
      runs(k) ≃ BroadcastPreparations sa.cube sa.id wire head pubAt macAt regAt memAt k :=
    Equiv.sigmaCongr (extentEquiv(k)) (fun _ => Equiv.refl _)
  let accepted := fun k z => checked k ((retitle k).symm z)
  let read (v : (k : RawBroadcast sa.cube) × BroadcastPreparations sa.cube sa.id wire head pubAt macAt regAt memAt k) :=
    let visits := (visitsEquiv sa.id (pubAt v.1 v.2.1 u) (macAt v.1 v.2.1 u) (regAt v.1 v.2.1 u)
      (memAt v.1 v.2.1 u)).symm (v.2.2 u)
    (pubAt v.1 v.2.1 u,visits.owned.val)
  have move (full : (k : RawBroadcast sa.cube) × BroadcastPreparations sa.cube sa.id wire head pubAt macAt regAt memAt k) :
      snap ((Equiv.sigmaCongrRight retitle).symm full) u = read full := by
    obtain ⟨k,ext,ret⟩ := full
    rfl
  let relay := allBroadcastPreparedEquiv G sa.cube owners sa.id S wire fixed head live pubAt macAt regAt memAt
    allowed accepted honest frames builders source
  intro route full c original v
  have restore : full = (Equiv.sigmaCongrRight retitle).symm (relay.symm ⟨q,reports⟩) := by
    dsimp only [full,route,routedPinnedPreparations,relay,accepted,retitle]
    simp only [Equiv.symm_trans_apply]
  rw [restore]
  refine (move (relay.symm ⟨q,reports⟩)).trans ?_
  change read (relay.symm ⟨q,reports⟩)=read ⟨c.val,original⟩
  apply congrArg
  dsimp only [relay,accepted,retitle,c,original]
  exact allBroadcastPreparedEquiv_restored G sa.cube owners sa.id S wire fixed head live pubAt macAt
    regAt memAt allowed (fun k z => checked k ((retitle k).symm z)) honest frames builders source q reports

/-- The word-by-word lookup certified at the source ownership return applies
at the actual positive pinned prefix, with that route's payload and owner
numbers and its very public words. -/
theorem routedPinnedPreparations_ownedLookup
    (allowed : RawBroadcast sa.cube → Prop)
    (checked : ∀ c, runs(c) → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b := sa.cube.b) (s := sa.cube.s) owners,
      allowed (routeBroadcast sa.cube owners q).val)
    (frames : ∀ c : CheckedBroadcast sa.cube, allowed c.val → PreparationFrame G (wire c.val) sa.cube (decodedBroadcast sa.cube c.val)
      (p(c.val)).bits live (pubAt c.val) (macAt c.val) (regAt c.val) (memAt c.val))
    (builders : ∀ (c : CheckedBroadcast sa.cube) (a : allowed c.val), (frames c a).Builders fixed sa.id owners)
    (source : ∀ (c : CheckedBroadcast sa.cube) (a : allowed c.val), (frames c a).SourceAgreement fixed S (builders c a))
    (q : {v : NativeAssignments.Routed (b:=sa.cube.b) (s:=sa.cube.s) owners // S.pins v}) (reports : S.actual q.val) (u : Fin (R+1)) (demand : ℕ) :
    let route := routedPinnedPreparations G args live L fixed hw size base fit sa.cube width U ib hb sb pinWidth sa.id owners
      S rawPin profile claim wire extent allowed checked honest frames builders source
    let full := route.symm ⟨q,reports⟩
    let ext := (headers).symm ⟨p(full.1),full.2.1⟩
    let start := U ext u
    let pr : start.Prefix sa.id := ⟨(Equiv.arrowCongr (finCongr (pinWidth ext u).symm) (Equiv.refl Bool))
      ((G.jointGuess ib hb sb).symm rawPin u),full.2.2 u⟩
    let c := routeBroadcast sa.cube owners q.val
    let original := (PreparationFrame.sourceEquiv (G:=G) (L:=wire (sourceBroadcast(q.val)).val) (ar:=sa.cube)
      (decl:=decodedBroadcast sa.cube (sourceBroadcast(q.val)).val) (header:=head (sourceBroadcast(q.val)).val) (pin:=live)
      (pub:=pubAt (sourceBroadcast(q.val)).val) (mac:=macAt (sourceBroadcast(q.val)).val) (reg:=regAt (sourceBroadcast(q.val)).val) (mem:=memAt (sourceBroadcast(q.val)).val)
      (id:=sa.id) (owners:=owners) fixed S (frames (sourceBroadcast(q.val)) (honest q.val)) (builders (sourceBroadcast(q.val)) (honest q.val))
      (source (sourceBroadcast(q.val)) (honest q.val))).symm
      ⟨⟨⟨q.val,(decoded_routeBroadcast sa.cube owners q.val).symm⟩,q.property⟩,reports⟩
    let v := (visitsEquiv sa.id (pubAt c.val original.1 u) (macAt c.val original.1 u)
      (regAt c.val original.1 u) (memAt c.val original.1 u)).symm (original.2 u)
    let numbers := Fin.valEmbedding ∘ owners q.val.1
    let banks := bankData q.val.2 sa.cube.header.packetBase sa.cube.singleBank
    CubePacket.WordPrepared (gadgetLookup sa (pubAt c.val original.1 u) numbers u.val demand banks) sa.id
      (pubAt c.val original.1 u) v.owned.val.2.2 →
      CubePacket.WordPrepared (gadgetLookup sa start.pub numbers u.val demand banks) sa.id
        start.pub (start.visited pr).owned.val.2.2 := by
  let test (s : (Arg → Word w) × (List (TeamRAM.Event w) × Bank w × Memory w)) :=
    CubePacket.WordPrepared (gadgetLookup sa s.1 (Fin.valEmbedding ∘ owners q.val.1) u.val demand
      (bankData q.val.2 sa.cube.header.packetBase sa.cube.singleBank)) sa.id s.1 s.2.2.2
  exact (congrArg test (routedPinnedPreparations_ownedState G args live L fixed hw size base fit sa width U ib hb sb
    pinWidth owners S rawPin profile claim wire extent allowed checked honest frames builders source q reports u)).mpr

end TeamContraction

end BorderVNP
end Computability
end OAI
