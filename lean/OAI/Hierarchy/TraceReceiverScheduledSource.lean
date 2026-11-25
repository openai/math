import OAI.Hierarchy.TraceReceiverProgram
import OAI.Hierarchy.TraceReceiverCursor
import OAI.Hierarchy.TraceReceiverTaskProgram
import OAI.Hierarchy.TraceReceiverOwnerMount
import OAI.Hierarchy.GridReceiverTickDirectory
import OAI.Hierarchy.GridPinReceiverPrefix
import OAI.Hierarchy.TraceReceiverMaskLoop
import OAI.Hierarchy.HistorySelectedArchitecture

namespace OAI
/-! # The uniform receiver source program in execution order -/
noncomputable section
namespace Hierarchy.TraceReceiverProgram

open ThreeFlat Diagonal PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open RAM.PhysicalProcedure RAM.HistoryStageBody.Physical
open TraceFactorReceiver

/-- Mount the static verifier template, initialize its dictionary, translate
the assigned input intervals to S5, publish the genuine S45 reverse owners,
and run the same selected chronological interpreter on all reached nodes. -/
def descendants {F : Type} [Field F] [Fintype F] (B : Block F)
    (w age firstFinal rootCount start pages templateSrc gateBase templateSize directoryWords axes low dict masks tmp : ℕ)
    (bank : RAM.HistoryStageBody.Physical.Archive) (shape : TraceBucketAtom.Layout)
    (rom : TraceRawLookup.Layout) (rest : Fin 1→Word (64*w))
    (pins : GridPinPublisher.Plan) (intervalBase : ℕ) : Procedure (64*w) :=
  let W:=64*w
  let g:=GridPinArena.slab w
  let J:=GridDescription.sector w
  let decode:=(PhysicalInputPhases.packing W templateSrc gateBase templateSize).seq
    (TraceReceiverMaskLoop.program W axes low dict masks tmp)
  let lib:=PhysicalInputPhases.packing W (templateSrc+W*(templateSize+directoryWords)) start (libraryWords B pages)
  let owners:=TraceReceiverOwnerMount.procedure W age firstFinal rootCount (15*J+3*g) (15*J+20*g+1)
  let leaf:=HistorySelectedSeed.procedure (initial age shape)
    (TraceRawLookup.virtual W rom (TraceBucketAtom.publicProgram W)) (TraceBucketAtom.publicData shape rest)
  let loop:=HistorySelectedReceiverLoop.selected age bank leaf (families B start pages)
  decode.seq (lib.seq ((pins.intervalProgram W intervalBase).seq (owners.seq loop)))

/-- Reclassifying is unnecessary on return from the interior compiler. Its
scratch includes S17/S18, so the genuine projection is run again to restore
the selected order, persistent count, and zero initial row/bit counters. -/
def terminal (w age text roots dim cap : ℕ) (D : TraceReceiverTasks.Layout) (A : TickTerminalRoot.Arena)
    (count mapHeader commands cursor : ℕ) (width : Fin 3→ℕ) : Procedure (64*w) :=
  let W:=64*w
  let writeIds:=GridReceiverTickDirectory.build (GridReceiverTickDirectory.banks w age)
    W (2+text) roots (((20*(w+1)+2)^dim)*roots)
  let parent:=TraceAdmission.Resources.mount W D.parent [A.metadata,A.physicalPins,0,0]
  let columns:=TraceReceiverTasks.before W D count cap width
  let maps:=TraceReceiverTasks.maps W A D.tasks mapHeader
  let cmdHeader:=TraceReceiverTasks.rangeSeed W D.current count commands 0 7
  let writeCmds:=Commands.procedure W D.current commands D.tasks
  let startGather:=Cursor.program W cursor commands count
  writeIds.seq (parent.seq (columns.seq (maps.seq (cmdHeader.seq (writeCmds.seq startGather)))))

/-- The arrays and addresses are static architectural inputs. Only native
RAM instructions obtain the tick's ordinal, choices, roots, and row counts. -/
def fullSource {F : Type} [Field F] [Fintype F] (B : Block F) (w age text argCount roots dim teams : ℕ)
    (dir : Directory) (firstFinal start pages templateSrc gateBase templateSize axes low dict masks tmp : ℕ)
    (bank : RAM.HistoryStageBody.Physical.Archive) (shape : TraceBucketAtom.Layout)
    (rom : TraceRawLookup.Layout) (rest : Fin 1→Word (64*w))
    (pins : GridPinPublisher.Plan) (intervalBase cap : ℕ) (D : TraceReceiverTasks.Layout)
    (A : TickTerminalRoot.Arena) (mapHeader commands cursor : ℕ) (width : Fin 3→ℕ) : Procedure (64*w) :=
  let W:=64*w
  let count:=A.control+1
  let choose:=GridReceiverTickDirectory.receiver w age text argCount roots dim teams
  let compileRoots:=descendants B w age firstFinal roots start pages templateSrc gateBase templateSize
    (64*(dir.stages.length+2)) axes low dict masks tmp bank shape rom rest pins intervalBase
  let tables:=terminal w age text roots dim cap D A count mapHeader commands cursor width
  ((navigation B W dir).seq choose).seq (compileRoots.seq tables)


end Hierarchy.TraceReceiverProgram
end

end OAI
