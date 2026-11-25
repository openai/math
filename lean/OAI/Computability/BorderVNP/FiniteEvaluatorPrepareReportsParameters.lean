import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsSources

/-! # The seven finite task parameters from the sorted geometry and real report image

Report preparation changes tail lengths and supplies new bits. Original ownership,
descriptor markers, supplied-bank addresses and canonical widths survive. Thus the
task producer sees the same owned ordinal as the six-word producer and the correct
external length in the actual seven-word initializer.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open RoutingISA RoutingISA.CellPacket RoutingISA.CellPacket.Supplement TeamRAM

variable {Site : Type}

/-- All local ownership ranks remain valid after the native field report pass. -/
theorem before_after_reports (l : Layout) (b : TypedTaskBuilder.Layout) (rows : List Row) (m : ℕ → ℕ)
    (owners : ∀ c < b.cells, ∀ z ∈ rows, z.Outside l (b.banks+2*c)) {c : ℕ} (hc : c ≤ b.cells) :
    b.before (image l rows m) c=b.before m c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    have own : b.owner (image l rows m) c=b.owner m c := image_outside l rows m (owners c (by omega))
    simp only [TypedTaskBuilder.Layout.before,own,ih (by omega)]

/-- The local six-word header and the subsequently produced seven-word task
refer to the same global cell, using the actual unchanged owner column. -/
theorem global_after_reports (l : Layout) (b : TypedTaskBuilder.Layout) (rows : List Row) (m : ℕ → ℕ)
    (owners : ∀ c < b.cells, ∀ z ∈ rows, z.Outside l (b.banks+2*c)) {i : ℕ} (rank : i < b.before m b.cells) :
    TypedTaskBuilder.globalCell b (image l rows m) i=TypedTaskBuilder.globalCell b m i := by
  let c := TypedTaskBuilder.globalCell b m i
  obtain ⟨size,own,position⟩ := TypedTaskBuilder.global_spec b m rank
  have same : b.owner (image l rows m) c=b.owner m c := image_outside l rows m (owners c size)
  have pos : b.before (image l rows m) c=i := (before_after_reports l b rows m owners size.le).trans position
  have result := TypedTaskBuilder.global_at b (image l rows m) size (same.trans own)
  change TypedTaskBuilder.globalCell b (image l rows m) (b.before (image l rows m) c)=c at result
  rwa [pos] at result

/-- The physical layout of one ordinary finite task before report preparation.
The sorted geometry reserves four descriptors for the supplemental splice. -/
structure TaskGeometry (b : TypedTaskBuilder.Layout) (r : Row) (o : Batch.Owned Site) (m : ℕ → ℕ) : Prop where
  /-- The descriptor range begins after its true sorted start marker. -/
  first : b.sorted+m (b.sorted+b.padded+r.number)+1=o.placed.descriptorBase
  /-- The exclusive stop marker includes the immutable prefix and four tail descriptors. -/
  past : b.sorted+m (b.sorted+b.padded+(b.stops+r.number))=o.placed.descriptorBase+3*((prefixChunks o.placed).length+4)
  /-- The physical delivered bank starts at the address emitted by the bank producer. -/
  bank : m (b.banks+2*r.number+1)=r.base
  /-- The external width emitted by the edge-offset scan counts the preexisting supplied bits. -/
  canonical : m (b.offsets+2*b.cables+r.number)=r.canonical
  /-- The placed task starts in that physical supplied bank. -/
  start : r.base=o.placed.externalBase
  /-- The reserved scratch arena of this global cell. -/
  scratch : b.scratch+b.scratchStride*r.number=o.placed.scratchBase
  /-- The retained private-burst arena of this global cell. -/
  burst : b.bursts+b.burstStride*r.number=o.placed.burstBase
  /-- Actual global three-word private-call row selected by the owned initializer. -/
  call : b.call r.number=o.callRow

/-- All seven words emitted after the real scalar report pass match the
argument of the supplemental initializer. The fourth word includes both
the canonical width and the true appended tail read from its updated bank. -/
theorem parameters_after_reports (l : Layout) (b : TypedTaskBuilder.Layout) (early late : List Row)
    (r : Row) (o : Batch.Owned Site) (supplied : List Bool) (m : ℕ → ℕ) {i : ℕ}
    (rank : i < b.before m b.cells) (number : TypedTaskBuilder.globalCell b m i=r.number)
    (owners : ∀ c < b.cells, ∀ z ∈ early++r::late, z.Outside l (b.banks+2*c))
    (geom : TaskGeometry b r o m) (tails : b.tails=l.tails) (width : r.canonical=supplied.length)
    (external : o.placed.external=supplied++r.bits) (sep : r.Separated l)
    (apart : ∀ z ∈ late, ∀ a, ¬ r.Outside l a → z.Outside l a)
    (stable : ∀ a ∈ [b.sorted+b.padded+r.number,b.sorted+b.padded+(b.stops+r.number),
        b.banks+2*r.number+1,b.offsets+2*b.cables+r.number], ∀ z ∈ early++r::late, z.Outside l a) :
    let mt := image l (early++r::late) m
    b.row mt (TypedTaskBuilder.globalCell b mt i)=TypedTaskBuilder.parameters o.typed := by
  intro mt
  rw [global_after_reports l b (early++r::late) m owners rank,number]
  have keep (a : ℕ) (h : a ∈ [b.sorted+b.padded+r.number,b.sorted+b.padded+(b.stops+r.number),
      b.banks+2*r.number+1,b.offsets+2*b.cables+r.number]) : mt a=m a := image_outside _ _ _ (stable _ h)
  have tail : mt (b.tails+r.number)=r.bits.length := tails ▸ (final_readback l early late r m sep apart).1
  have length : (o.typed.cell.chunks).length=(prefixChunks o.placed).length+4 := by
    simp [Batch.Owned.typed,Supplement.task,tailChunks]
  change [b.sorted+mt (b.sorted+b.padded+r.number)+1,b.sorted+mt (b.sorted+b.padded+(b.stops+r.number)),
    mt (b.banks+2*r.number+1),mt (b.offsets+2*b.cables+r.number)+mt (b.tails+r.number),
    b.scratch+b.scratchStride*r.number,b.bursts+b.burstStride*r.number,b.call r.number]=
    [o.placed.descriptorBase,o.placed.descriptorBase+3*o.typed.cell.chunks.length,o.placed.externalBase,
    o.placed.external.length,o.placed.scratchBase,o.placed.burstBase,o.callRow]
  rw [keep _ (by simp),keep _ (by simp),keep _ (by simp),keep _ (by simp),tail,length,geom.first,geom.past,
    geom.bank,geom.start,geom.canonical,width,external,List.length_append,geom.scratch,geom.burst,geom.call]

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
