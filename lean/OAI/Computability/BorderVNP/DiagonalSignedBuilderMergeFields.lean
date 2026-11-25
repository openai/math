import OAI.Computability.BorderVNP.RoutingISAScheduleClockPublishedFields
import OAI.Computability.BorderVNP.CellTeamPreparedPaths
import OAI.Computability.BorderVNP.CellPacketSupplementalProducerRows

/-! # Reading the original and supplemental packets on a real signed builder return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube DiagonalTallyCellReports DiagonalTallyAllocation CellPacket CellSparse
open CellSparse.Packet CellSparse.Packet.Source CellPacket.Supplement.Batch CellPacketGeometry.History.Native

variable {w : ℕ} {a : SignedTaskArena.Layout} {f : FragmentRows.Layout} {orig : Memory w}
    {fit : f.Fits w (readings orig)} {cells : a.fragments.cells=f.cells}
    (e : FragmentRows.SparseEmission a f orig fit cells) (l : TypedTaskBuilder.Layout) (next : Memory w)
    (image : readings next=l.published (readings e.output))
    (calls : a.fragments.start≤l.calls) (tasks : a.fragments.start≤l.tasks)

include image calls tasks in
/-- The two stable fragment passes and compact task publisher retain each
original word below the fragment reservation, outside their two control stores. -/
theorem signedBuilder_original {addr : ℕ} (low : addr < a.fragments.start) (root : addr ≠ l.frame+90)
    (control : addr ≠ f.control+29) : readings next addr = readings orig addr := by
  rw [image,task_published_outside]
  · exact e.original addr control (Or.inl low)
  · rintro (h|⟨c,_,rfl⟩|h)
    · omega
    · change l.calls+3*c < a.fragments.start at low
      omega
    · exact root h

/-- The canonical descriptors, public geometry words and delivered opaque
strings survive the fragment emitter, stable bucket, and compact builder.
The final four-word source and the original seven-word row refer to the
same sampled report cursor. -/
theorem signedBuilder_mergeFields {Site : Type} {description : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s m} {banks : CellBanks.Layout} {rl : ReportLayout} {reports : List (ReportCell rl)} {cursor : ReportCursor}
    (allocation : ReportAllocation a.before a.after banks rl reports cursor)
    (seed : PreparedReportInput pub m reports cursor description)
    (r : Returns prepareCellReports pub mac s m) (j : Fin reports.length)
    {fit₀ : f.Fits w (readings r.val.2.2)} (emitted : FragmentRows.SparseEmission a f r.val.2.2 fit₀ cells)
    (built : readings next=l.published (readings emitted.output))
    (lowFrame : l.frame+112≤a.fragments.limit) (lowControl : f.control+37≤a.fragments.limit)
    (high : a.before.limit≤l.calls ∧ a.before.limit≤l.tasks)
    {table four i endAddr : ℕ} (o : Owned Site) (geo : CellMemory o.placed o.geometry endAddr (readings r.val.2.2))
    (row : o.typed.Stored next table i)
    (controls : WordsAt (readings next) (four+4*i) [o.layout.supplement,o.layout.counters,o.layout.merged,o.layout.reportWords])
    (prefixEnd : o.placed.descriptorBase+(CellPacket.descriptors (Supplement.prefixChunks o.placed)).length=o.layout.tail)
    (pubLow pubHigh : ℕ)
    (range : pubHigh≤a.fragments.start ∧ (l.frame+90<pubLow ∨ pubHigh≤l.frame+90) ∧
      (f.control+29<pubLow ∨ pubHigh≤f.control+29))
    (desc : pubLow≤o.placed.descriptorBase ∧ endAddr≤pubHigh)
    (words : pubLow≤o.placed.publicBase ∧ o.placed.publicBase+((Supplement.prefixParts o.placed).flatMap Part.publicBuffer).length ≤ pubHigh)
    (geom : pubLow≤o.geometry ∧ o.geometry+(fieldList record o.placed.rows++fieldList vector o.placed.reports).length≤pubHigh)
    (delivered : ∀ j, Part.original j∈Supplement.prefixParts o.placed →
      Delivered (description:=description) (readings r.val.2.2) (o.placed.slot j) o.placed.headerWidth (o.placed.factors j))
    (slot : ∀ j, Part.original j∈Supplement.prefixParts o.placed →
      let addr := o.placed.slot j
      addr+description≤a.fragments.start ∧ (l.frame+90<addr ∨ addr+description≤l.frame+90) ∧
        (f.control+29<addr ∨ addr+description≤f.control+29))
    (bodies : ∀ j, o.placed.headerWidth+(boxBody (o.placed.factors j)).length≤description)
    (sizes : ∀ j, (boxBody (o.placed.factors j)).length<2^o.placed.headerWidth)
    (bindings : o.extra=bindingRows reports[j].bundles (reports[j].localStart ((reports.take j.val).foldl (fun z c => c.after z) cursor)))
    (supplement : o.layout.supplement=rl.supplement+reports[j].number*rl.supplementStride)
    (counters : o.layout.counters=rl.counters+2*reports[j].number)
    (reportWords : o.layout.reportWords=(fieldList vector o.placed.reports).length)
    (counterFit : o.layout.counters+1<2^w) (apart : endAddr≤o.layout.merged)
    (suppLo : pubHigh≤o.layout.supplement) (suppHi : o.layout.supplement+(o.extra.flatMap record).length<2^w) :
    MergeFields o table four i next := by
  have after : a.fragments.start ≤ a.before.limit := by
    rw [a.before.footprint]
    have top : a.fragments.start ≤ a.before.start := by
      change a.fragments.start ≤ a.fragments.limit
      rw [a.fragments.footprint]
      omega
    omega
  have fromOutput {addr : ℕ} (below : addr < a.fragments.start) (root : addr ≠ l.frame+90) (control : addr ≠ f.control+29) :
      readings next addr = readings r.val.2.2 addr :=
    signedBuilder_original emitted l next built (after.trans high.1) (after.trans high.2) below root control
  have read (addr : ℕ) (lo : pubLow≤addr) (hi : addr<pubHigh) : readings next addr=readings r.val.2.2 addr :=
    fromOutput (hi.trans_le range.1) (by rcases range.2.1 with h|h <;> omega) (by rcases range.2.2 with h|h <;> omega)
  have last := geo.endAddress
  have ptr := prefixEnd
  have saved := supplement_at_builder allocation seed r j emitted l next built lowFrame lowControl high
  refine MergeFields.ofPublished o next (readings r.val.2.2) geo row controls prefixEnd ?_ ?_ ?_ ?_ ?_
    bodies sizes reports[j] _ saved bindings supplement counters reportWords counterFit apart (geom.2.trans suppLo) suppHi
  · intro d
    exact read _ (desc.1.trans (Nat.le_add_right ..)) (by have := d.isLt; have := desc.2; omega)
  · intro d
    exact read _ (words.1.trans (Nat.le_add_right ..)) (Nat.add_lt_add_left d.isLt _ |>.trans_le words.2)
  · intro d
    exact read _ (geom.1.trans (Nat.le_add_right ..)) (Nat.add_lt_add_left d.isLt _ |>.trans_le geom.2)
  · intro k hk
    have low₀ := desc.1
    have high₀ := desc.2
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rw [←prefixEnd]
    exact read _ (by omega) (by omega)
  · intro u member b used
    obtain ⟨before,root,control⟩ := slot u member
    have bit := b.isLt
    have eqn := fromOutput (addr := o.placed.slot u+b.val) (by omega) (by rcases root with h|h <;> omega)
      (by rcases control with h|h <;> omega)
    exact eqn.trans (delivered u member b used)

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
