import OAI.Hierarchy.TraceReceiverLeafSetup
import OAI.Hierarchy.TraceReceiverTablesMount
import OAI.Hierarchy.TraceReceiverOwnerRun
import OAI.Hierarchy.GridReceiverDirectoryFrame
import OAI.Hierarchy.TraceReceiverScheduledSource

namespace OAI
/-! # Executing the native receiver up to its compiled chronological caches -/

namespace Hierarchy.TraceReceiverDescendantExecution
open ThreeFlat Diagonal PhysicalStage RAM Computability.VPVNP.BurstRAM PrivateRAM
open PhysicalProcedure HistoryStageBody.Physical TickWorkspace
open NavigationPass HistoryContraction GridRegisteredSetting
open TraceReceiverLeafSetup
noncomputable section

open scoped Fin.CommRing
variable {F : Type} [Field F] [Fintype F] {w pc regs slots S baseAddr fuel axes : ℕ}
variable (D : RunData F (64*w) pc regs slots S baseAddr fuel axes (w/2)) (l : GridNativeImage.Layout)
set_option quotPrecheck false
local notation "W" => 64*w
local notation "u" => TraceAdmission.receiverAge w
local notation "A" => GridReceiverTickDirectory.banks w u

local notation "args" => GridStructuralHeader.parameters D.block (axes+1) D.passes l.selectorCap
  D.machine D.fit D.field D.state 0 (gateBase D)

def program (first count : ℕ) (P : GridPinPublisher.Plan) : Procedure W :=
  TraceReceiverProgram.descendants D.block w u first count (start w) (pages w)
    (templateSrc D l) (gateBase D) (templateSize D) (64*((GridReceiverDirectory.native D l).stages.length+2))
    (axes+1) (w/2) (dict D) (masks D) (tmp D) (bank D l) (shape D) (rom D) (rest D) P (intervalBase w)

def leaf : Procedure W := HistorySelectedSeed.procedure (initial u (shape D))
  (TraceRawLookup.virtual W (rom D) (TraceBucketAtom.publicProgram W)) (TraceBucketAtom.publicData (shape D) (rest D))

def sliced (P : GridPinPublisher.Plan) (m : Memory W) : Memory W :=
  P.intervalMemory (intervalBase w) (TraceReceiverTablesMount.output D m)

def entry (first count : ℕ) (P : GridPinPublisher.Plan) (m : Memory W) : Memory W :=
  TraceReceiverOwnerMount.output u first count (A).owners ((A).scratch+1) (sliced D P m)

def cost (first count : ℕ) (P : GridPinPublisher.Plan) (selectedWork : ℕ) : ℕ :=
  TraceReceiverTablesMount.decodeWork D+(TraceReceiverTablesMount.libWork D+
    (P.intervalCost+(TraceReceiverOwnerMount.ticks first count+selectedWork)))

private theorem prepend {width a b : ℕ} {P Q : Procedure width}
    {m m' : Memory width} {post : Memory width → Prop}
    (run : P.Exec m m' a) (body : Q.Spec (·=m') (fun _ o=>post o) b) :
    (P.seq Q).Spec (·=m) (fun _ o=>post o) (a+b) := by
  have joined : (P.seq Q).Spec (·=m) (fun _ o => ∃ tmp, tmp=m' ∧ post o) (a+b) :=
    Procedure.Spec.seq («A»:=P) (B:=Q) (mid:=fun v => v=m')
      (left:=fun _ v => v=m') (right:=fun _ o => post o) run body (fun _ _ h => h)
  intro labels regs slots machine
  exact Procedure.Spec.mono joined (fun _ h => h) (fun _ _ h => h.elim fun _ pair => pair.2)
    le_rfl machine

/-- Each pass starts in the exact output memory of the previous pass, including
the classifier's genuine incoming memory and every interval and owner write. -/
theorem execute {first count work p : ℕ} {P : GridPinPublisher.Plan}
    (textFit : SelfAdvice.textSize W pc slots≤w^2) (self : Fin (w^2)→Bool) (index : Word W)
    (sel : Fin (l.selectorCap+1)→Bool) (input : ℕ→Bool) (m : Memory W) (safe : ℕ)
    (headerFit : (GridReceiverHeader.header _ textFit self index args sel).length≤p)
    (covered : 2+(GridReceiverHeader.header _ textFit self index args sel).length≤ safe)
    (read : ∀ i : Fin (GridReceiverHeader.header _ textFit self index args sel).length,
      input i.val=(GridReceiverHeader.header _ textFit self index args sel)[i.val])
    (frame : ∀ z,z< safe → m z=TickMountedPins.memory (w:=W) (fun j : Fin p=>input j.val) z)
    (large : 7≤w) (depth : (axes+1)+w/2≤2*w+1) (small : templateSize D≤2^(w/100))
    (inputRoom : 2+p≤ start w) (high : start w+libraryWords D.block W≤gateBase D)
    (room : start w+libraryWords D.block W<2^W)
    (ticks : P.ticks<2^W) (factors : P.factors<2^W) (lanes : P.lanes<2^W)
    (owner : (TraceReceiverOwnerMount.procedure W u first count (A).owners ((A).scratch+1)).Exec
      (sliced D P m) (entry D first count P m) (TraceReceiverOwnerMount.ticks first count))
    (post : Memory W→Prop)
    (loop : (HistorySelectedReceiverLoop.selected u (bank D l) (leaf D) (families D.block (start w) W)).Spec
      (·=entry D first count P m) (fun _ o=>post o) work) :
    (program D l first count P).Spec (·=m) (fun _ o=>post o) (cost D first count P work) := by
  obtain ⟨dec,lib,_,_,_⟩:=TraceReceiverTablesMount.run D l textFit self index sel input m safe
    headerFit covered read frame large depth small inputRoom high room
  have slice : (P.intervalProgram W (intervalBase w)).Exec
      (TraceReceiverTablesMount.output D m) (sliced D P m) P.intervalCost :=
    P.interval_exec (intervalBase w) (TraceReceiverTablesMount.output D m) ticks factors lanes
  let owners := TraceReceiverOwnerMount.procedure W u first count (A).owners ((A).scratch+1)
  let selected := HistorySelectedReceiverLoop.selected u (bank D l) (leaf D) (families D.block (start w) W)
  have stages : ((TraceReceiverTablesMount.decode D l).seq ((TraceReceiverTablesMount.lib D l).seq
      ((P.intervalProgram W (intervalBase w)).seq (owners.seq selected)))).Spec
      (·=m) (fun _ o=>post o) (cost D first count P work) :=
    prepend dec (prepend lib (prepend slice (prepend owner loop)))
  unfold program TraceReceiverProgram.descendants
  simp only [TraceReceiverTablesMount.decode,TraceReceiverTablesMount.lib,librarySrc_eq,leaf,
    pages,GridReceiverTickDirectory.banks,GridPinArena.assignmentBanks,cost,owners,selected] at stages ⊢
  exact @stages

end
end Hierarchy.TraceReceiverDescendantExecution

end OAI
