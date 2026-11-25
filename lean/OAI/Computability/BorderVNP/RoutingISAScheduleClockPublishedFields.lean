import OAI.Computability.BorderVNP.RoutingISAScheduleClockProducedInput
import OAI.Computability.BorderVNP.RoutingISAScheduleClockReportWords
import OAI.Computability.BorderVNP.CellPacketGeometryPublishedCell
import OAI.Computability.BorderVNP.FragmentRowsSparseReadback

/-! # The geometry and signed-report words at each owned merge row

The geometry publication supplies the original descriptor, public and
private source sections. Each real report return supplies the two sidecar
counters and concatenated binding records. These words survive the
fragment directory, stable bucket and task-row writes in the fixed arena.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube DiagonalTallyCellReports DiagonalTallyAllocation CellPacket CellSparse
open CellSparse.Packet CellSparse.Packet.Source CellPacket.Supplement.Batch CellPacketGeometry.History.Native

private theorem records_le_words (rs : List Record) : rs.length ≤ (rs.flatMap record).length := by
  induction rs with
  | nil => rfl
  | cons x xs ih =>
    have pos : 1≤(record x).length := by cases x <;> simp [record]
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

/-- The complete binding records and both counters of the actual sampled
report are still present at the word memory returned by the task builder. -/
theorem supplement_at_builder {w description : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m} {a : SignedTaskArena.Layout} {banks : CellBanks.Layout} {rl : ReportLayout} {cs : List (ReportCell rl)}
    {q : ReportCursor} (alloc : ReportAllocation a.before a.after banks rl cs q)
    (seed : PreparedReportInput pub m cs q description) (r : Returns prepareCellReports pub mac s m) (i : Fin cs.length)
    {f : FragmentRows.Layout} {fit : f.Fits w (readings r.val.2.2)} {cells : a.fragments.cells=f.cells}
    (e : FragmentRows.SparseEmission a f r.val.2.2 fit cells) (b : TypedTaskBuilder.Layout) (next : Memory w)
    (image : readings next=b.published (readings e.output))
    (low : b.frame+112≤a.fragments.limit) (control : f.control+37≤a.fragments.limit)
    (high : a.before.limit≤b.calls ∧ a.before.limit≤b.tasks) :
    cs[i].SupplementStored ((cs.take i.val).foldl (fun z c => c.after z) q) (readings next) := by
  let c := cs[i]
  let cursor := (cs.take i.val).foldl (fun z c => c.after z) q
  let rows := bindingRows c.bundles (c.localStart cursor)
  have input := report_return_supplement alloc seed r i
  obtain ⟨source,number,length⟩ := input
  have keep (z : ℕ) (hz : a.fragments.limit ≤ z) (top : z<a.before.limit) :
      readings next z=readings r.val.2.2 z := by
    rw [image,TypedTaskBuilder.Layout.published,Function.update_of_ne (by omega : z≠b.frame+90)]
    rw [b.image_outside _ _ le_rfl z (by
      rintro (h|⟨j,_,h⟩|h)
      · change b.tasks≤z ∧ _ at h; omega
      · change z=b.calls+3*j at h; omega
      · omega)]
    exact e.original z (by omega) (.inr hz)
  have mem : c∈cs := List.getElem_mem _
  have num := alloc.number_lt c mem
  have extent := alloc.supplements c mem
  have scaled := Nat.mul_le_mul_right a.before.bound.supplementStride (Nat.succ_le_of_lt num)
  rw [Nat.succ_mul] at scaled
  have srcBase := alloc.supplement
  have stride := alloc.stride
  have ctrBase := alloc.counters
  have srcLo : a.fragments.limit≤a.before.supplement := Nat.le_add_right ..
  have srcEnd : a.before.supplement+a.before.bound.cells*a.before.bound.supplementStride=a.before.counters := rfl
  have ctrEnd : a.before.counters+2*a.before.bound.cells≤a.before.limit := by
    simp only [BeforeTasks.limit,BeforeTasks.bundleTable,BeforeTasks.ranges,BeforeTasks.six,BeforeTasks.four,BeforeTasks.merged]
    omega
  have width : (rows.flatMap record).length ≤ a.before.bound.supplementStride := (binding_words ..).le.trans extent
  change WordsAt (readings next) (rl.supplement+c.number*rl.supplementStride) (rows.flatMap record) ∧
    readings next (rl.counters+2*c.number)=rows.length ∧ readings next (rl.counters+2*c.number+1)=(rows.flatMap record).length
  refine ⟨?_,(keep _ (by omega) (by omega)).trans number,(keep _ (by omega) (by omega)).trans length⟩
  intro j
  have lt := j.isLt
  have dst := keep (rl.supplement+c.number*rl.supplementStride+j.val) (by omega) (by rw [srcBase,stride]; omega)
  exact dst.trans (source j)

/-- The final original descriptor, real private box sources and signed
sidecar words establish a merge row before compression. Only the two
needed scalar words of the original tail and the original chunk sources
are read from the geometry publication. -/
theorem MergeFields.ofPublished {Site : Type} {w table controls i exclusive description : ℕ}
    (o : Owned Site) (m : Memory w) (origin : ℕ → ℕ)
    (geo : CellMemory o.placed o.geometry exclusive origin) (row : o.typed.Stored m table i)
    (ctl : WordsAt (readings m) (controls+4*i) [o.layout.supplement,o.layout.counters,o.layout.merged,o.layout.reportWords])
    (endPrefix : o.placed.descriptorBase+(CellPacket.descriptors (Supplement.prefixChunks o.placed)).length=o.layout.tail)
    (descKept : ∀ j : Fin (CellPacket.descriptors (Supplement.prefixChunks o.placed)).length,
      readings m (o.placed.descriptorBase+j.val)=origin (o.placed.descriptorBase+j.val))
    (pubKept : ∀ j : Fin ((Supplement.prefixParts o.placed).flatMap Part.publicBuffer).length,
      readings m (o.placed.publicBase+j.val)=origin (o.placed.publicBase+j.val))
    (geomKept : ∀ j : Fin (fieldList record o.placed.rows++fieldList vector o.placed.reports).length,
      readings m (o.geometry+j.val)=origin (o.geometry+j.val))
    (tailKept : ∀ j ∈ [1,2], readings m (o.layout.tail+j)=origin (o.layout.tail+j))
    (delivered : ∀ j, Part.original j∈Supplement.prefixParts o.placed →
      Delivered (description:=description) (readings m) (o.placed.slot j) o.placed.headerWidth (o.placed.factors j))
    (bodies : ∀ j, o.placed.headerWidth+(boxBody (o.placed.factors j)).length≤description)
    (sizes : ∀ j, (boxBody (o.placed.factors j)).length<2^o.placed.headerWidth)
    {rl : ReportLayout} (c : ReportCell rl) (cursor : ReportCursor) (saved : c.SupplementStored cursor (readings m))
    (bindings : o.extra=bindingRows c.bundles (c.localStart cursor))
    (supplement : o.layout.supplement=rl.supplement+c.number*rl.supplementStride)
    (counters : o.layout.counters=rl.counters+2*c.number)
    (reports : o.layout.reportWords=(fieldList vector o.placed.reports).length)
    (counterFit : o.layout.counters+1<2^w)
    (separated : exclusive≤o.layout.merged)
    (geometryEnd : o.geometry+(fieldList record o.placed.rows++fieldList vector o.placed.reports).length≤o.layout.supplement)
    (supplementEnd : o.layout.supplement+(o.extra.flatMap record).length<2^w) : MergeFields o table controls i m := by
  have supp : WordsAt (readings m) o.layout.supplement (o.extra.flatMap record) := by
    rw [bindings,supplement]; exact saved.1
  have source := geo.metadata o m descKept pubKept geomKept delivered bodies sizes supp
  have tail := geo.tail
  rw [endPrefix] at tail
  have ptr := (tailKept 1 (by decide)).trans (tail ⟨1,by simp⟩)
  have words := (tailKept 2 (by decide)).trans (tail ⟨2,by simp⟩)
  have count : readings m o.layout.counters=o.extra.length := by rw [bindings,counters]; exact saved.2.1
  have len : readings m (o.layout.counters+1)=(o.extra.flatMap record).length := by rw [bindings,counters]; exact saved.2.2
  have ex := geo.endAddress
  rw [endPrefix] at ex
  have last := tailEnd_of_taskRow m o.placed o.layout o.geometry o.callRow o.extra endPrefix row
  have tailFit := last.symm.trans_lt (m (table+7*i+1)).isLt
  have head := records_le_words o.placed.rows
  have extra := records_le_words o.extra
  simp only [List.length_append,fieldList,List.length_cons] at geometryEnd
  refine ⟨row,ctl,ptr,?_,count,len,reports,endPrefix,source,⟨tailFit,counterFit,?_,?_⟩,Or.inr (ex ▸ separated)⟩
  · rw [reports]; exact words
  · change o.geometry+1+(o.placed.rows.flatMap record).length<2^w; omega
  · change o.placed.rows.length+o.extra.length<2^w; omega

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
