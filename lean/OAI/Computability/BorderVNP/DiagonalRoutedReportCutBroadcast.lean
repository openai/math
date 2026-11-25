import OAI.Computability.BorderVNP.DiagonalBroadcastPreparationRestore
import OAI.Computability.BorderVNP.DiagonalSourceReportInputs

/-! # The observed report tape after restoring the physical broadcast -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator SignedPrep Routing
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Tally DiagonalTallyCellReports

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge) (ar : CubeArena.Layout)
    (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Fin (R+1))
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ) (S : SourceReports ar owners)
    (L : RawBroadcast ar → WireLayout (R+1) r link) (fixed : Block (R+1)) (header : RawBroadcast ar → List Bool)
    (pin : Fin d → Bool)

variable (pub : ∀ c : RawBroadcast ar, HeaderExterior (L c) (header c) → Fin (R+1) → Arg → Word w)
    (mac : ∀ c : RawBroadcast ar, HeaderExterior (L c) (header c) → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : ∀ c : RawBroadcast ar, HeaderExterior (L c) (header c) → Fin (R+1) → Bank w) (mem : ∀ c : RawBroadcast ar, HeaderExterior (L c) (header c) → Fin (R+1) → Memory w)

/-- The report scanner and argument launcher of one specified joint return.
All native registers and RAM addresses are obtained by splitting that return. -/
def broadcastReportCutAt (u : Fin (R+1)) {l : ReportLayout} {cells : List (ReportCell l)}
    (rows : ReportAssignments cells) (cursor : ReportCursor) (description : ℕ)
    (full : Σ c : RawBroadcast ar, BroadcastPreparations ar id L header pub mac reg mem c) : Prop :=
  let v := (visitsEquiv id (pub full.1 full.2.1 u) (mac full.1 full.2.1 u) (reg full.1 full.2.1 u)
    (mem full.1 full.2.1 u)).symm (full.2.2 u)
  Nonempty (ReportArgumentCut v.reports rows cursor description)

variable (allowed : RawBroadcast ar → Prop)
    (checked : ∀ c : RawBroadcast ar, BroadcastPreparations ar id L header pub mac reg mem c → LocalRow.declarationInRange c ∧ allowed c)
    (honest : ∀ q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners,
      allowed (routeBroadcast ar owners q).val)
    (frames : ∀ c : CheckedBroadcast ar, allowed c.val → PreparationFrame G (L c.val) ar (decodedBroadcast ar c.val)
      (header c.val) pin (pub c.val) (mac c.val) (reg c.val) (mem c.val))
    (builders : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).Builders fixed id owners)
    (source : ∀ (c : CheckedBroadcast ar) (a : allowed c.val), (frames c a).SourceAgreement fixed S (builders c a))

local notation3 (prettyPrint := false) "joint" => allBroadcastPreparedEquiv G ar owners id S L fixed header pin
  pub mac reg mem allowed checked honest frames builders source


local notation3 (prettyPrint := false) "broadcast(" x ")" => routeBroadcast ar owners (Subtype.val x)

set_option maxHeartbeats 350000
set_option maxRecDepth 7500

/-- Decoding the full broadcast preserves the chronological report return.
The sparse launcher on its output and the chosen source tape are fitted to
that same preparation memory. -/
theorem allBroadcastPreparedEquiv_reportCut
    (q : {v : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners // S.pins v}) (reports : S.actual q.val)
    (u : Fin (R+1)) :
    let c := routeBroadcast ar owners q.val
    let raw := declaredWords ar owners (decodedBroadcast ar c.val) ⟨q.val,(decoded_routeBroadcast ar owners q.val).symm⟩
    let B := builders c (honest q.val) raw
    let a : Matching ar owners (decodedBroadcast ar c.val) raw.val := ⟨q.val,(decoded_routeBroadcast ar owners q.val).symm,rfl⟩
    let checkedRows : Subtype B.pins := ⟨a,((source c (honest q.val)).pins raw a).mpr q.property⟩
    let data := B.localRows checkedRows u
    broadcastReportCutAt ar id L header pub mac reg mem u (reports u) data.cursor data.description
      ((joint).symm ⟨q,reports⟩) := by
  intro c raw B a checkedRows data
  let observed := broadcastReportCutAt ar id L header pub mac reg mem u (reports u) data.cursor data.description
  change observed ((joint).symm ⟨q,reports⟩)
  apply (congrArg observed (allBroadcastPreparedEquiv_restored G ar owners id S L fixed header pin pub mac reg mem
    allowed checked honest frames builders source q reports)).mpr
  have sourceCut := PreparationFrame.sourceEquiv_report_cut (G:=G) (L:=L (broadcast(q)).val) (ar:=ar) (decl:=decodedBroadcast ar (broadcast(q)).val)
    (header:=header (broadcast(q)).val) (pin:=pin) (pub:=pub (broadcast(q)).val) (mac:=mac (broadcast(q)).val) (reg:=reg (broadcast(q)).val) (mem:=mem (broadcast(q)).val)
    (id:=id) (owners:=owners) fixed S (frames (broadcast(q)) (honest q.val)) (builders (broadcast(q)) (honest q.val)) (source (broadcast(q)) (honest q.val))
    ⟨⟨q.val,(decoded_routeBroadcast ar owners q.val).symm⟩,q.property⟩ reports u
  dsimp only at sourceCut
  dsimp only [observed,broadcastReportCutAt]
  dsimp only [data,checkedRows,a,B,raw,c] at sourceCut ⊢
  exact sourceCut

/-- Both the initial cursor and the source-description width can be retained
with the fitted inputs when the control frame will subsequently supply their
physical addresses. -/
theorem allBroadcastPreparedEquiv_exists_reportCut
    (q : {v : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners // S.pins v})
    (reports : S.actual q.val) (u : Fin (R+1)) :
    ∃ cur desc, broadcastReportCutAt ar id L header pub mac reg mem u (reports u) cur desc
      ((joint).symm ⟨q,reports⟩) :=
  ⟨_,_,allBroadcastPreparedEquiv_reportCut G ar owners id S L fixed header pin pub mac reg mem
    allowed checked honest frames builders source q reports u⟩


end TeamContraction

end BorderVNP
end Computability
end OAI
