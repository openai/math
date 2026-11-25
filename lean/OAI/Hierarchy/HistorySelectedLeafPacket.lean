import OAI.Hierarchy.HistorySelectedSeedArm

namespace OAI
/-! # Recorded operands of the genuine seed replay at the reached cursor -/

namespace Hierarchy.HistorySelectedSeed
open ThreeFlat RAM RAM.DescriptorExpr RAM.HistoryInitialSeed
open RAM.PhysicalProcedure RAM.HistoryStageBody.Physical RAM.HistoryNodeDirectory
open Diagonal.TickWorkspace Diagonal.PhysicalStage Computability.VPVNP.BurstRAM PrivateRAM
open HistorySelectedReceiverLoop RAM.NavigationNodeRows
open scoped Fin.CommRing
noncomputable section

variable {F : Type} [Field F] [Fintype F] {W n u count : ℕ}
structure Operands (shape : TraceBucketAtom.Layout) (rom : TraceRawLookup.Layout)
    (rest : Fin 1→Word W) (tag : ((Fin 3→Bool)→F)→ℕ) (src : Memory W)
    (values : Fin n→NodeValue F) (j : Fin n) (b : Banks) (paidMem : ℕ→ℕ) (u count : ℕ) where
  site : Site
  ar : ℕ
  net : BitNetwork F ar
  slot : ℕ
  kernel : ℕ
  index : site.index=j.val
  value : values j=node net site.extPins slot (streamAt u count site.index) (endsAt u count site.index)
  active : 1≤archiveColumn b paidMem j.val 0/b.unitWork
  rowMass : site.rows (initial u shape)≤archiveColumn b paidMem j.val 0/b.unitWork
  pinMass : site.extPins≤2*(archiveColumn b paidMem j.val 0/b.unitWork)
  zero : (src (base u 44+8*site.index)).val=0
  control : ControlImage (initial u shape) site kernel src
  separate : Separated (initial u shape) site
  room : (initial u shape).ctrl+42<2^W
  four : 4<2^W
  early : site.index<count
  arity : ar=site.extPins+2*shape.bank
  cells : net.cells=site.rows (initial u shape)
  hidden : net.internal=site.bits (initial u shape)
  headerFit : ∀j : Fin 6,site.words (initial u shape) ⟨36+j.val,by omega⟩<2^W
  fit : (initial u shape).intervals+4*site.lane+3<2^W
  safe : ¬site.writes (initial u shape) ((initial u shape).intervals+4*site.lane+3)
  offset : src ((initial u shape).intervals+4*site.lane+3)=(slot:Word W)
  size : 4*site.rows (initial u shape)≤volume u
  ext : site.extPins≤volume u
  volume : 2≤RAM.HistoryStageBody.Physical.volume u
  scratch : RAM.HistoryStageBody.Physical.volume u+42≤ stride u
  raw : RawReads (initial u shape) site (TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W))
    (TraceBucketAtom.publicData shape rest) src (recordAt tag net (site.stream (initial u shape)))

theorem Operands.emitted {shape : TraceBucketAtom.Layout} {rom : TraceRawLookup.Layout} {rest : Fin 1→Word W}
    {tag : ((Fin 3→Bool)→F)→ℕ} {src : Memory W} {values : Fin n→NodeValue F} {j : Fin n}
    {b : Banks} {paidMem : ℕ→ℕ} (s : Operands shape rom rest tag src values j b paidMem u count)
    (B : Block F) (bank : Archive) (D : HistoryNodeDirectory.Selected.Directory W n) (start pages height coeff : ℕ) (unit : 1≤coeff) :
    let arm:=fun i : Fin n=>B.nativeArmTime height coeff b paidMem i.val
    let leaf:=procedure (initial u shape) (TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W))
      (TraceBucketAtom.publicData shape rest)
    Emitted (u:=u) bank leaf (families B start pages) D values tag (B.nativeVisitCost height coeff b paidMem)
      arm (fun i _=>arm i) j src :=
  emitReceiver B bank shape rom s.site rest tag s.net src s.slot D values j s.index s.value b paidMem
    start pages height coeff unit s.active s.rowMass s.pinMass s.zero s.control s.separate s.room s.four
    s.early s.arity s.cells s.hidden s.headerFit s.fit s.safe s.offset s.size s.ext s.volume s.scratch s.raw

end
end Hierarchy.HistorySelectedSeed

end OAI
