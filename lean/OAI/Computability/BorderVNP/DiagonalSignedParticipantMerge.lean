import OAI.Computability.BorderVNP.DiagonalSignedProducerMergeRows
import OAI.Computability.BorderVNP.DiagonalSignedBuilderMergeFields
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenRoom
import OAI.Computability.BorderVNP.FiniteEvaluatorProducedCellMemory

/-! # All native supplemental parser fields at a compact signed cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM FragmentRows SignedTaskArena CellPacket CellPacket.Supplement CellPacket.Supplement.Batch
open DiagonalTallyAllocation DiagonalTallyCellReports TypedTaskBuilder CellSparse CellSparse.Packet CellSparse.Packet.Source
open CellPacketGeometry.History.Native

variable {w description team frame offsets ctl live ports : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout}
    {banks : CellBanks.Layout} {rl : ReportLayout} {reports : List (ReportCell rl)} {q : ReportCursor}
    {pub : Arg → Word w} {m : Memory w} {s : Bank w} {mac : TeamOpcode.Macros w 8}
    {source : ℕ → ℕ}
local notation "R" => a.controlRows team frame offsets ctl live ports

/-- The public counter address vectors contribute exactly the word count installed
in the native supplemental task control row. -/
theorem count_packet_words (base gadgets digits : ℕ) :
    (fieldList vector (countFields base gadgets digits)).length=1+gadgets*(1+digits) := by
  simp [fieldList,vector,countFields,List.length_flatMap,List.map_ofFn,List.sum_ofFn,Nat.add_comm]

/-- Instantiate the complete private parser receipt on the physical source and
destination of the signed typed-task builder. All seven and four header words,
supplemental counters, emitted binding records and original body exposures
refer to the same compact ordinal of the actual report return. -/
theorem signed_participant_merge {Site : Type} (alloc : ReportAllocation a.before a.after banks rl reports q)
    (seed : PreparedReportInput pub m reports q description) (r : Returns prepareCellReports pub mac s m)
    {fit : f.Fits w (readings r.val.2.2)} {cells : a.fragments.cells=f.cells}
    (e : SparseEmission a f r.val.2.2 fit cells)
    (patch : SparsePatch (w:=w) Site (R) (readings e.output))
    (controls : (R).Room w) (image : readings m=(R).published source)
    (physical : banks.bankStart=a.cube.cellBank) (frameEq : rl.frame=frame)
    (place : a.SparsePlacement frame ctl) (gp : SparseGeometry a f offsets ctl)
    (fitBefore : a.before.limit<2^w)
    (j : Fin reports.length) (owned : j.val<(R).before (readings e.output) (R).cells) (last : ℕ) :
    let raw := readings e.output
    let c := globalCell (R).toLayout raw j.val
    let p := patch.placed c
    let o := produced (R) raw patch.placed patch.geometry patch.extra j.val
    reports[j].number=c →
    raw ((R).offsets+2*(R).cables+c)+raw ((R).tails+c)=p.external.length →
    (R).sorted+raw ((R).sorted+(R).padded+c)+1=p.descriptorBase →
    CellMemory p (patch.geometry c) last (readings r.val.2.2) →
    ctl+37≤p.descriptorBase ∧ last≤a.cube.header.header →
    ctl+37≤p.publicBase ∧ p.publicBase+((prefixParts p).flatMap Part.publicBuffer).length≤a.cube.header.header →
    ctl+37≤patch.geometry c ∧ patch.geometry c+(fieldList record p.rows++fieldList vector p.reports).length≤a.cube.header.header →
    (∀ u, Part.original u∈prefixParts p →
      Delivered (description:=description) (readings r.val.2.2) (p.slot u) p.headerWidth (p.factors u)) →
    (∀ u, Part.original u∈prefixParts p → a.cube.cellBank≤p.slot u ∧ p.slot u+description≤a.fragments.start) →
    (∀ u, p.headerWidth+(boxBody (p.factors u)).length≤description) →
    (∀ u, (boxBody (p.factors u)).length<2^p.headerWidth) →
    patch.extra c=bindingRows reports[j].bundles (reports[j].localStart ((reports.take j.val).foldl (fun z row => row.after z) q)) →
    (∃ base, p.reports=countFields base a.before.bound.gadgets a.before.bound.countWidth) →
    MergeFields o (R).tasks (R).four j.val patch.built := by
  intro raw c p o num extent marker packet desc words geometry delivery slots bodies widths bindings reportSize
  have member := (global_spec (R).toLayout raw owned).1
  have zlt : c < a.cube.cells := member
  have beforeCount : a.cube.cells≤a.before.bound.cells := place.cells
  obtain ⟨countBase,countSet⟩ := reportSize
  have order := a.sparse_order place.cells
  have placeFrame := place.beforeControl
  have placeHeader := gp.controller
  have placeBank := place.beforeBank
  have startBound : a.fragments.start≤a.fragments.limit := by rw [a.fragments.footprint]; omega
  have bankRoom := a.open_table_order.1
  have parts := signed_producer_merge_rows alloc seed r e patch controls image physical frameEq place gp owned extent
  have original : CellMemory o.placed o.geometry last (readings r.val.2.2) :=
    packet.atTask (R) raw patch.placed marker
  obtain ⟨s₁,s₂,s₃,s₄,s₅,s₆,s₇,s₈⟩ := a.before.ordered
  have step : a.before.start=a.fragments.limit := rfl
  have post : a.before.tailWidths=a.fragments.limit := rfl
  have promised : c+1≤a.before.bound.cells := by omega
  have byCell := Nat.mul_le_mul_right a.before.bound.supplementStride promised
  rw [Nat.succ_mul] at byCell
  have cap := alloc.supplements reports[j] (List.getElem_mem j.isLt)
  have count : ((patch.extra c).flatMap record).length≤a.before.bound.supplementStride := by
    rw [bindings,binding_words]
    exact cap
  apply signedBuilder_mergeFields (R).toLayout patch.built alloc seed r j e patch.image
    (by change frame+112≤a.fragments.limit; omega)
    (by rw [gp.control]; omega)
    (by exact ⟨le_rfl,Nat.le_add_right ..⟩) o original parts.1 parts.2.1 parts.2.2 (ctl+37) a.cube.header.header
  · change _ ∧ (frame+90<_ ∨ _) ∧ _
    rw [gp.control]
    exact ⟨by omega,Or.inl (by omega),Or.inl (by omega)⟩
  · change ctl+37≤(R).sorted+raw ((R).sorted+(R).padded+c)+1 ∧ _
    rw [marker]
    exact desc
  · exact words
  · exact geometry
  · exact delivery
  · intro u yes
    obtain ⟨lo,hi⟩ := slots u yes
    change p.slot u+description≤a.fragments.start ∧ (frame+90<p.slot u ∨ _) ∧ _
    rw [gp.control]
    refine ⟨hi,Or.inl (by omega),Or.inl ?_⟩
    change ctl+29<p.slot u
    omega
  · exact bodies
  · exact widths
  · exact bindings
  · change a.before.supplement+a.before.bound.supplementStride*c=rl.supplement+reports[j].number*rl.supplementStride
    rw [alloc.supplement,alloc.stride,num,Nat.mul_comm]
  · change a.before.counters+2*c=rl.counters+2*reports[j].number
    rw [alloc.counters,num]
  · change 1+a.before.bound.gadgets*(1+a.before.bound.countWidth)=(fieldList vector p.reports).length
    rw [countSet,count_packet_words]
  · change a.before.counters+2*c+1<2^w
    omega
  · change last≤a.before.merged+c
    omega
  · change a.cube.header.header≤a.before.supplement+a.before.bound.supplementStride*c
    omega
  · change a.before.supplement+a.before.bound.supplementStride*c+((patch.extra c).flatMap record).length<2^w
    rw [Nat.mul_comm a.before.bound.supplementStride c]
    omega

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
