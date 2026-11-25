import OAI.Hierarchy.GridReceiverHardware
import OAI.Hierarchy.TraceReceiverScheduledSource

namespace OAI
/-! # The padded hardware of the complete receiving program -/

noncomputable section
namespace Hierarchy.TraceReceiverTasks

open private range_size from OAI.Hierarchy.TraceReceiverBeforeShape in
private theorem rangeSeed_size_eq (W head count commands : ℕ) :
    size (rangeSeed W head count commands 0 7) = size (rangeSeed 1 0 0 0 0 7) :=
  (range_size W head count commands 0 7).trans (range_size 1 0 0 0 0 7).symm

end Hierarchy.TraceReceiverTasks

namespace Hierarchy.TraceReceiverProgram
open ThreeFlat Diagonal PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM Filter
open NavigationPass NodePublication PhysicalProcedure RAM.HistoryStageBody.Physical TraceFactorReceiver
open scoped Classical

private def rangeHardware := resources (TraceReceiverTasks.rangeSeed 1 0 0 0 0 7)

private theorem range_size (W head count commands : ℕ) :
    resources (TraceReceiverTasks.rangeSeed W head count commands 0 7)=rangeHardware :=
  TraceReceiverTasks.rangeSeed_size_eq W head count commands

variable {F : Type} [Field F] [Fintype F]

/-- This is the actual common receiver's full instruction and operand count.
Its sparse compiler contains all arms of the fixed compressor. Its setup
also includes S5, S11/S45, template masks and both S17 projections. -/
theorem full_source_hardware (B : Block F) : ∃ H,∀
    (w age text argCount roots dim teams : ℕ) (dir : Directory)
    (firstFinal start pages templateSrc gateBase templateSize axes low dict masks tmp : ℕ)
    (bank : RAM.HistoryStageBody.Physical.Archive) (shape : TraceBucketAtom.Layout)
    (rom : TraceRawLookup.Layout) (rest : Fin 1→Word (64*w))
    (pins : GridPinPublisher.Plan) (intervalBase cap : ℕ) (D : TraceReceiverTasks.Layout)
    (A : TickTerminalRoot.Arena) (mapHeader commands cursor : ℕ) (width : Fin 3→ℕ),
    dir.archive.K=B.alphabetCap → dir.archive.initialDegree=2^(B.exponent 0) →
    dir.node.childCap=directoryCap B → dir.node.halfCap=directoryCap B → dir.node.motifCap=directoryCap B →
    resources (fullSource B w age text argCount roots dim teams dir firstFinal start pages templateSrc gateBase
      templateSize axes low dict masks tmp bank shape rom rest pins intervalBase cap D A mapHeader commands cursor width)≤H := by
  obtain ⟨navSize,nav⟩:=navigation_hardware B
  refine ⟨navSize+selectedResources (families B 0 0)+TraceReceiverTasks.hardware+rangeHardware+5000,?_⟩
  intro w age text argCount roots dim teams dir firstFinal start pages templateSrc gateBase templateSize
    axes low dict masks tmp bank shape rom rest pins intervalBase cap D A mapHeader commands cursor width
    alpha degree children halves motifs
  let W:=64*w
  let count:=A.control+1
  let fixedRows:=((20*(w+1)+2)^dim)*roots
  let g:=GridPinArena.slab w
  let J:=GridDescription.sector w
  have navBound:=nav W dir alpha degree children halves motifs
  have elected:=GridReceiverTickDirectory.receiver_hardware w age text argCount roots dim teams
  have parentSize := TraceAdmission.Resources.mount_size W D.parent [A.metadata,A.physicalPins,0,0]
  change resources (TraceAdmission.Resources.mount W D.parent [A.metadata,A.physicalPins,0,0])=30 at parentSize
  have packed : resources (PhysicalInputPhases.packing W templateSrc gateBase templateSize)=27 := rfl
  have librarySize : resources (PhysicalInputPhases.packing W
      (templateSrc+W*(templateSize+64*(dir.stages.length+2))) start (libraryWords B pages))=27 := rfl
  obtain ⟨ml,mr,ms⟩:=TraceReceiverMaskLoop.fixed_size W axes low dict masks tmp
  obtain ⟨il,ir,is⟩:=pins.interval_architecture W intervalBase
  have owner:=TraceReceiverOwnerMount.hardware W age firstFinal roots (15*J+3*g) (15*J+20*g+1)
  have stage:=HistorySelectedReceiverLoop.block_resources B start pages W age bank shape rom rest
  obtain ⟨secondL,secondR,secondS⟩:=GridReceiverTickDirectory.hardware (GridReceiverTickDirectory.banks w age)
    W (2+text) roots fixedRows
  have summarize:=TraceReceiverTasks.dimensions W D count cap width A mapHeader
  have header:=range_size W D.current count commands
  have finalCursor:=Cursor.hardware W cursor commands count
  obtain ⟨cmdL,cmdR,cmdS⟩:=Commands.dimensions W D.current commands D.tasks
  obtain ⟨firstL,firstR,firstS⟩:=elected
  simp only [fullSource,terminal,descendants,resources_seq]
  simp only [resources] at navBound packed librarySize header parentSize ⊢
  dsimp only [W,count,fixedRows,g,J] at *
  omega

/-- The same bound is available for every actual public address and every
choice of the padded field-contraction board. -/
theorem full_machine_capacity (B : Block F) : ∀ᶠ w : ℕ in atTop,∀
    (age text argCount roots dim teams : ℕ) (dir : Directory)
    (firstFinal start pages templateSrc gateBase templateSize axes low dict masks tmp : ℕ)
    (bank : RAM.HistoryStageBody.Physical.Archive) (shape : TraceBucketAtom.Layout)
    (rom : TraceRawLookup.Layout) (rest : Fin 1→Word (64*w))
    (pins : GridPinPublisher.Plan) (intervalBase cap : ℕ) (D : TraceReceiverTasks.Layout)
    (A : TickTerminalRoot.Arena) (mapHeader commands cursor : ℕ) (width : Fin 3→ℕ),
    dir.archive.K=B.alphabetCap → dir.archive.initialDegree=2^(B.exponent 0) →
    dir.node.childCap=directoryCap B → dir.node.halfCap=directoryCap B → dir.node.motifCap=directoryCap B →
    ∀ {p H J : ℕ} (fit : Contraction.Fits (TickWeightedBank.shape F p H J) (64*w))
      (control header row lut : ℕ),
      GridEvaluatorHardware.FitsCapacity (machine fit
        (fullSource B w age text argCount roots dim teams dir firstFinal start pages templateSrc gateBase
          templateSize axes low dict masks tmp bank shape rom rest pins intervalBase cap D A mapHeader commands
          cursor width) cursor control header row lut) := by
  obtain ⟨N,all⟩:=full_source_hardware B
  filter_upwards [eventual_machine (F:=F) N 0] with w room
  intro age text argCount roots dim teams dir firstFinal start pages templateSrc gateBase templateSize
    axes low dict masks tmp bank shape rom rest pins intervalBase cap D A mapHeader commands cursor width
    alpha degree children halves motifs p H J fit control header row lut
  apply room
  simpa only [pow_zero,Nat.mul_one] using all w age text argCount roots dim teams dir firstFinal start
    pages templateSrc gateBase templateSize axes low dict masks tmp bank shape rom rest pins intervalBase cap D A
    mapHeader commands cursor width alpha degree children halves motifs

end Hierarchy.TraceReceiverProgram
end

end OAI
