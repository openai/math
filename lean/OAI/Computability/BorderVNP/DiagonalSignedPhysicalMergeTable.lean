import OAI.Computability.BorderVNP.DiagonalSignedPreparedPlacements
import OAI.Computability.BorderVNP.CellPacketGeometrySignedPublished

/-! # The physical row fields on the published signed task table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.ScheduleClock
open CellSparse CellSparse.Packet CellSparse.Packet.Source SiteWords CellPacket CellPacket.Supplement
open CellPacket.Supplement.Batch TypedTaskBuilder FragmentRows SignedTaskArena DiagonalTallyCellReports DiagonalTallyAllocation

variable {w n p d H description frame ctl offsets : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout}
    {O E : Type} (G : SiteWords.Directory (Fin n) O (a.cube.cells+1)) (ptr : O → E)
    (base : ℕ → ℕ) (slot : O → ℕ) (fs : O → List Factor)
set_option quotPrecheck false
local notation "top" => descriptorBank (ctl+37) p
local notation "pubRoom" => a.cube.cells+1+G.words.length+(a.cube.cells+1)≤2^p
local notation "descRoom" => a.cube.cells+1+(Schema.coords (G.referenceRows ptr).length).length+(a.cube.cells+1)≤2^d

variable {team live ports : ℕ} {source : ℕ → ℕ}
local notation "R" => a.controlRows team frame offsets ctl live ports

variable {pub : Arg → Word w} {m : Memory w} {s : RoutingISA.Bank w} {mac : TeamOpcode.Macros w 8}
    {banks : CellBanks.Layout} {rl : ReportLayout} {reports : List (ReportCell rl)} {q : ReportCursor}

open private prefix_original from OAI.Computability.BorderVNP.CellPacketGeometrySignedPublished

/-- On the single published geometry, choose every before-patch placement
and actual supplemental row. Any native task return for this table obtains
the actual row fields, original private bytes, report counters, and installed
metadata required by the sparse call launcher. -/
theorem Published.signed_merge_table {args : E → ℕ} (out : Published G p d (ctl+37) H ptr args base)
    (addresses : ∀ i, args (ptr i)=slot i) (alloc : ReportAllocation a.before a.after banks rl reports q)
    (seed : PreparedReportInput pub m reports q description) (r : Returns prepareCellReports pub mac s m)
    {fit : f.Fits w (readings r.val.2.2)} {cells : a.fragments.cells=f.cells} (e : SparseEmission a f r.val.2.2 fit cells)
    (place : a.SparsePlacement frame ctl) (gp : SparseGeometry a f offsets ctl)
    (fromControls : ∀ z, ctl+37≤z → z<a.cube.header.header → readings m z=base z)
    (physical : banks.bankStart=a.cube.cellBank) (frameEq : rl.frame=frame)
    (sorted : (R).sorted=top) (padded : (R).padded=2^d)
    (stops : (R).stops=a.cube.cells+1+(Schema.coords (G.referenceRows ptr).length).length)
    (tableRoom : top+2*(2^d)≤a.cube.header.header)
    (ranks : ∀ i : Fin (2^d), base (top+(2^d+i.val))<2^d)
    (controls : (R).Room w) (image : readings m=(R).published source) (fitBefore : a.before.limit<2^w)
    (order : (R).before (readings e.output) (R).cells=reports.length)
    (ordinal : ∀ j : Fin reports.length, reports[j].number=globalCell (R).toLayout (readings e.output) j.val)
    (numeric : ∀ u, a.cube.cellBank≤ slot u ∧ slot u+description≤a.cube.stop)
    (body : ∀ u, H+(boxBody (fs u)).length≤description) (widths : ∀ u, (boxBody (fs u)).length<2^H)
    (reportsAt : ∀ c : Fin a.cube.cells, ∃ b, G.reports c.castSucc=countFields b a.before.bound.gadgets a.before.bound.countWidth)
    (bodiesAt : ∀ c : Fin a.cube.cells, (R).owner (readings e.output) c.val=(R).team →
      ∀ u, Sum.inr u∈G.cellBoxes c.castSucc →
      Delivered (description:=description) (readings r.val.2.2) (slot u) H (fs u)) :
    ∃ hf : pubRoom, ∃ hs : descRoom,
    let raw := readings e.output
    let pl := signedPlaces (ctl:=ctl) (H:=H) G ptr base slot fs (R) raw hf hs
    let p := Terminal.placeAt pl
    let geometry := fun c => (p c).publicBase+((prefixParts (p c)).flatMap Part.publicBuffer).length
    let extra := seedExtras reports q
    TypedBatch.SourceShape pl G ∧
    (∀ c < (R).cells, raw ((R).sorted+(R).padded+((R).stops+c))-raw ((R).sorted+(R).padded+c)-1=3*((p c).parts.length+3)) ∧
    (∀ c < (R).cells, (p c).publicBase+((p c).parts.flatMap Part.publicBuffer).length≤(R).sorted) ∧
    (∀ c < (R).cells, ∀ u, Sum.inr u∈(p c).boxes → (R).sorted+(R).padded≤(p c).slot u ∧
      (p c).slot u+description≤a.fragments.external ∧ (p c).headerWidth+(boxBody ((p c).factors u)).length≤description) ∧
    (∀ c < (R).cells, ((extra c).flatMap record).length≤(R).stride) ∧
    ∀ patch : SparsePatch (w:=w) O (R) raw, patch.placed=p → patch.geometry=geometry → patch.extra=extra →
      ∀ i < (R).before raw (R).cells,
        MergeFields (produced (R) raw patch.placed patch.geometry patch.extra i) (R).tasks (R).four i patch.built := by
  obtain ⟨hf,hs,shape,all⟩ := out.signed_prepared_placements G ptr base slot fs (R) addresses alloc seed r e place gp
    fromControls physical frameEq sorted padded stops tableRoom ranks
  refine ⟨hf,hs,?_⟩
  intro raw pl p geometry extra
  have same (c : Fin a.cube.cells) : p c.val=pl c.castSucc :=
    congrArg pl (Fin.ext (Nat.min_eq_left c.isLt.le))
  have bound := a.sparse_order place.cells
  have fragmentEnd : a.fragments.start≤a.fragments.external := by
    unfold FragmentArena.Layout.external FragmentArena.Layout.cursors
      FragmentArena.Layout.triples FragmentArena.Layout.pairs FragmentArena.Layout.quads
    omega
  refine ⟨shape,?_,?_,?_,?_,?_⟩
  · intro c hc
    let pos : Fin a.cube.cells := ⟨c,hc⟩
    rw [show p c=pl pos.castSucc from same pos]
    exact (all pos).1
  · intro c hc
    let pos : Fin a.cube.cells := ⟨c,hc⟩
    obtain ⟨_,_,_,hi,_⟩ := out.ordinary_region place.beforeControl pos
    rw [show p c=pl pos.castSucc from same pos,sorted]
    exact hi
  · intro c hc u _
    let pos : Fin a.cube.cells := ⟨c,hc⟩
    rw [show p c=pl pos.castSucc from same pos]
    change _≤ slot u ∧ slot u+description≤a.fragments.external ∧ H+(boxBody (fs u)).length≤description
    exact ⟨place.sortedBank.trans (numeric u).1,(numeric u).2.trans (bound.2.1.trans fragmentEnd),body u⟩
  · intro c _
    change ((seedExtras reports q c).flatMap record).length≤a.before.bound.supplementStride
    by_cases h : ∃ j : Fin reports.length, reports[j].number=c
    · obtain ⟨j,atCell⟩ := h
      rw [←atCell,alloc.seedExtras_owned,binding_words]
      exact alloc.supplements reports[j] (List.getElem_mem j.isLt)
    · rw [seedExtras,dite_eq_right h]
      simp
  · intro patch placed geom extras i hi
    let j : Fin reports.length := ⟨i,hi.trans_eq order⟩
    let c := globalCell (R).toLayout raw i
    let pos : Fin a.cube.cells := ⟨c,(global_spec (R).toLayout raw hi).1⟩
    have eqj : reports[j].number=c := ordinal j
    obtain ⟨_,extent,marker,cell,descriptorBounds,wordBounds,geometryBounds⟩ := all pos
    have chosen : patch.placed c=pl pos.castSucc := (congrFun placed c).trans (same pos)
    have rowG : patch.geometry c=(pl pos.castSucc).publicBase+((prefixParts (pl pos.castSucc)).flatMap Part.publicBuffer).length := by
      rw [geom]
      change (p c).publicBase+((prefixParts (p c)).flatMap Part.publicBuffer).length=_
      rw [same pos]
    have launch := signed_participant_merge alloc seed r e patch controls image physical frameEq place gp fitBefore j hi
      (top+base (top+(2^d+(Markers.stop hs pos.castSucc).val))) eqj
    change _ = (patch.placed c).external.length → _ at launch
    apply launch
    · rw [chosen]; exact extent
    · rw [chosen]; exact marker
    · change CellMemory (patch.placed c) (patch.geometry c) _ _
      rw [chosen,rowG]; exact cell
    · rw [chosen]; exact descriptorBounds
    · rw [chosen]; exact wordBounds
    · change ctl+37≤patch.geometry c ∧ patch.geometry c+(fieldList record (patch.placed c).rows++fieldList vector (patch.placed c).reports).length≤_
      rw [chosen,rowG]; exact geometryBounds
    · intro u present
      change Part.original u∈prefixParts (patch.placed c) at present
      rw [chosen] at present
      obtain ⟨box,inBox,pick⟩ := List.mem_filterMap.mp ((prefix_original _ _).mp present)
      have rightBox : Sum.inr u∈(pl pos.castSucc).boxes := by
        cases box with
        | inl v => contradiction
        | inr v => exact (Option.some.inj pick) ▸ inBox
      change Delivered (description:=description) _ ((patch.placed c).slot u) (patch.placed c).headerWidth ((patch.placed c).factors u)
      rw [chosen]
      exact bodiesAt pos (global_spec (R).toLayout raw hi).2.1 u rightBox
    · intro u _
      change a.cube.cellBank≤(patch.placed c).slot u ∧ (patch.placed c).slot u+description≤_
      rw [chosen]
      exact ⟨(numeric u).1,(numeric u).2.trans bound.2.1⟩
    · intro u
      change (patch.placed c).headerWidth+(boxBody ((patch.placed c).factors u)).length≤description
      rw [chosen]
      exact body u
    · intro u
      change (boxBody ((patch.placed c).factors u)).length<2^(patch.placed c).headerWidth
      rw [chosen]
      exact widths u
    · change patch.extra c=_
      rw [extras,←eqj]
      exact alloc.seedExtras_owned j
    · change ∃ b, (patch.placed c).reports=_
      rw [chosen]
      exact reportsAt pos

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
