import OAI.Hierarchy.TraceReceiverPreparedReturn
import OAI.Hierarchy.TraceReceiverParentReturn
import OAI.Hierarchy.TraceReceiverCommandRoom
import OAI.Hierarchy.TraceReceiverTerminalExecution

namespace OAI
/-! # One terminal RAM execution from the re-elected S17 roster to the physical field evaluator -/
noncomputable section
namespace Hierarchy.TraceReceiverForward
open ThreeFlat Diagonal PhysicalStage RAM
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure HistoryContraction TickTerminalRoot HistoryTerminalTape
open HistoryStageBody.Physical HistoryCompiledRows HistoryCommandTable TraceFactorReceiver TraceReceiverTasks
open scoped Fin.CommRing Classical BigOperators

variable {F Pins : Type} [Field F] [Fintype F] {w u p suffix n d l : ℕ}
variable (P : Source F Pins w u p suffix n d l)
set_option quotPrecheck false
local notation "W" => 64*w
local notation "B" => GridReceiverBanks.base w
local notation "G" => GridReceiverBanks.gap w
local notation "D" => GridReceiverBanks.tasks w
local notation "regCursor" => GridReceiverBanks.cursor w
local notation "cmd" => GridReceiverBanks.commands w
local notation "hdr" => GridReceiverBanks.mapHeader w
local notation "cap" => GridReceiverBanks.limit w
local notation "widths" => GridReceiverBanks.width w
local notation "S" => TickWorkspace.base u
local notation "count" => S 18+1
local notation "ranged" => rangeImage (D).current count cmd 0 7 (P.images n)
local notation "out" => Issued.image regCursor cmd (D).tasks n ranged
local notation "tag" => (fun t : (Fin 3→Bool)→F=>(Fintype.equivFin _ t).val)

private def writerProcedure (wordSize : ℕ) (layout : TraceReceiverTasks.Layout) (arena : TickTerminalRoot.Arena)
    (howMany limit header commands cursor : ℕ) (width : Fin 3→ℕ) : Procedure wordSize :=
  (TraceAdmission.Resources.mount wordSize layout.parent [arena.metadata,arena.physicalPins,0,0]).seq
    ((before wordSize layout howMany limit width).seq ((maps wordSize arena layout.tasks header).seq
      ((rangeSeed wordSize layout.current howMany commands 0 7).seq
        ((Commands.procedure wordSize layout.current commands layout.tasks).seq
          (Cursor.program wordSize cursor commands howMany)))))

private theorem writer_execution {wordSize : ℕ} (layout : TraceReceiverTasks.Layout) (arena : TickTerminalRoot.Arena)
    (howMany limit header commands cursor : ℕ) (width : Fin 3→ℕ) (dst len : ℕ→ℕ)
    (roots : ℕ) (initial : Memory wordSize)
    (space : TraceReceiverProgram.TerminalWriterRoom layout arena howMany limit header commands cursor
      width dst len roots initial) :
    (writerProcedure wordSize layout arena howMany limit header commands cursor width).Spec (·=initial)
      (fun _ z=>z=TraceReceiverProgram.terminalOutput layout arena howMany limit header commands cursor width
        dst len roots initial)
      (TraceReceiverProgram.terminalClock layout arena howMany limit header commands cursor width dst len roots initial) := by
  intro _ _ _ machine
  exact TraceReceiverProgram.terminal_writes layout arena howMany limit header commands cursor width
    dst len roots initial space machine

private theorem result_spec {wordSize : ℕ} (program : Procedure wordSize) (initial first second : Memory wordSize)
    (cost : ℕ) (same : first=second) (executed : program.Spec (·=initial) (fun _ z=>z=first) cost) :
    program.Spec (·=initial) (fun _ z=>z=second) cost := by
  subst second
  intro _ _ _ machine
  exact executed machine

def Source.writers : Procedure W := writerProcedure W D P.arena count cap hdr cmd regCursor widths

def Source.writerCost (elected : Memory (64*w)) :=
  TraceReceiverProgram.terminalClock D P.arena count cap hdr cmd regCursor widths P.dst P.len n elected

local notation "parentAt" m => TraceAdmission.Resources.mounted (D).parent [S 9,p,0,0] m

private structure ScalarRoom (page base gap roots limit : ℕ) : Prop where
  mapHead : page+4<base+24
  maps : page+4<base+2*gap
  headerFit : base+7<limit
  cursorFit : base+32+2<limit
  countFit : page+1<limit
  countHead : page+1<base
  countCursor : page+1<base+32
  countCommands : page+1<base+9*gap
  commandFit : base+9*gap+7*roots<limit

private theorem scalar_room {page base gap roots limit : ℕ} (front : page+1<base)
    (roof : base+16*gap<limit) (space : 128≤gap) (jobs : 5*roots≤gap) :
    ScalarRoom page base gap roots limit := by constructor <;> omega

include P in
private theorem Source.scalar_geometry : ScalarRoom (S 18) B G n (2^W) := by
  obtain ⟨bank,roof,gap⟩:=Gather.grid_window P.large P.age
  have front:=TickWorkspace.apart (u:=u) (by decide : 18<45)
  have positive : 0<TickWorkspace.stride u := by unfold TickWorkspace.stride;positivity
  exact scalar_room (by omega) roof gap P.jobs

private theorem Source.separate_commands : Commands.Separate (D).tasks cmd n ranged := by
  apply Commands.separate_grid P.large P.age P.jobs _ (fun i=>S 13+8*P.O.id (P.site i))
    (fun i=>(P.final_root_bounds i).2.2)
  intro i
  rw [P.ranged_task,P.task]
  exact ⟨rfl,rfl⟩

private structure MapObservations {bits : ℕ} (layout : TraceReceiverTasks.Layout) (arena : TickTerminalRoot.Arena)
    (countAddr header commands roots : ℕ) (dst len : ℕ → ℕ) (input : Memory bits) : Prop where
  initial : (input (@TickTerminalRoot.countdown bits arena).val).val=roots
  root : ∀ i<roots, MapBounds arena layout.tasks header (dst i) (len i)
    (mapImages arena layout.tasks header dst len input i)
  kept : ∀ i<roots, KeptByRoot arena
    (mapSeed arena layout.tasks header (mapImages arena layout.tasks header dst len input i))
    (@TickTerminalRoot.countdown bits arena).val
  finalCount : mapImages arena layout.tasks header dst len input roots countAddr=(roots:Word bits)
  separate : Commands.Separate layout.tasks commands roots
    (rangeImage layout.current countAddr commands 0 7 (mapImages arena layout.tasks header dst len input roots))

private theorem MapObservations.transport {bits : ℕ} {layout : TraceReceiverTasks.Layout} {arena : TickTerminalRoot.Arena}
    {countAddr header commands roots : ℕ} {dst len : ℕ → ℕ} {a b : Memory bits} (same : a=b)
    (witness : MapObservations layout arena countAddr header commands roots dst len a) :
    MapObservations layout arena countAddr header commands roots dst len b := same ▸ witness

private theorem Source.map_observations :
    MapObservations D P.arena count hdr cmd n P.dst P.len P.initial := by
  refine ⟨?_,fun i hi => P.bounds ⟨i,hi⟩,?_,?_,P.separate_commands⟩
  · exact (congrArg (fun a : ℕ => (P.initial a).val) P.countdown_val).trans
      ((congrArg Fin.val P.counts.2.2.2.2).trans (Fin.val_cast_of_lt P.countFits))
  · exact fun i hi => TraceReceiverRootBounds.counter (P.iteration ⟨i,hi⟩).2.2.1 P.page
  · exact Fin.ext (P.final_observations.2.1.trans (Fin.val_cast_of_lt P.countFits).symm)

set_option maxHeartbeats 800000 in
private theorem Source.writer_room (elected : Memory (64*w)) (boot : P.initial=beforeImage D count cap widths n (parentAt elected))
    (room : BeforeBounds D count cap widths n W) (num : ((parentAt elected) count).val=n)
    (caches : ∀ j (i : Fin n),(amountAddress (D).selected (D).first (D).results j (parentAt elected) (i.val:Word W)).val<(D).current) :
    TraceReceiverProgram.TerminalWriterRoom D P.arena count cap hdr cmd regCursor widths
      P.dst P.len n elected := by
  have g:=P.scalar_geometry
  have obs:=MapObservations.transport boot P.map_observations
  refine ⟨room,num,caches,obs.initial,obs.root,?_,?_,obs.kept,g.headerFit,g.cursorFit,g.countFit,
    Or.inl g.countHead,Or.inl g.countCursor,Or.inl g.countCommands,obs.finalCount,g.commandFit,obs.separate⟩
  · exact Or.inl (lt_of_eq_of_lt P.countdown_val g.mapHead)
  · intro i _
    exact Or.inl (lt_of_eq_of_lt P.countdown_val (lt_of_lt_of_le g.maps (Nat.le_add_right _ (scanned P.ports i))))

private theorem Source.output_eq (elected : Memory (64*w)) (boot : P.initial = beforeImage D count cap widths n (parentAt elected)) :
    TraceReceiverProgram.terminalOutput D P.arena count cap hdr cmd regCursor widths P.dst P.len n elected = out := by
  exact congrArg (fun m : Memory W => Issued.image regCursor cmd (D).tasks n
    (rangeImage (D).current count cmd 0 7
      (mapImages P.arena (D).tasks hdr P.dst P.len m n))) boot.symm

set_option maxHeartbeats 800000 in
theorem Source.run_writers (elected : Memory (64*w)) (boot : P.initial=beforeImage D count cap widths n (parentAt elected))
    (room : BeforeBounds D count cap widths n W) (num : ((parentAt elected) count).val=n)
    (caches : ∀ j (i : Fin n),(amountAddress (D).selected (D).first (D).results j (parentAt elected) (i.val:Word W)).val<(D).current) :
    P.writers.Spec (·=elected) (fun _ z=>z=out) (P.writerCost elected) := by
  intro _ _ _ machine
  exact result_spec P.writers elected (TraceReceiverProgram.terminalOutput D P.arena count cap hdr cmd regCursor
    widths P.dst P.len n elected) out (P.writerCost elected) (P.output_eq elected boot)
    (by intro _ _ _ M
        exact writer_execution D P.arena count cap hdr cmd regCursor widths P.dst P.len n elected
          (P.writer_room elected boot room num caches) M) machine

/-- The output value, gate addresses, offsets and command pointers all
come from the actual RAM execution. This also covers an empty tick. -/
theorem Source.ready (elected : Memory (64*w)) (boot : P.initial=beforeImage D count cap widths n (parentAt elected))
    (room : BeforeBounds D count cap widths n W) (num : ((parentAt elected) count).val=n)
    (caches : ∀ j (i : Fin n),(amountAddress (D).selected (D).first (D).results j (parentAt elected) (i.val:Word W)).val<(D).current)
    (nets : ∀ i,BitNetwork F (P.ports i)) (wires : ∀ i,Fin (P.ports i)→Fin p)
    (pin : Fin p→Bool) (H : ℕ) (ext : ∀ z,Fin (P.L.ext z)→Fin p)
    (fits : suffix+P.X.widthSum≤p) (canonical : P.tag=tag)
    (network : ∀ i,HEq (P.value i).net (nets i))
    (connected : ∀ (i : Fin n) (j : Fin (P.ports i)),wires i j=
      P.L.ports.physicalSource ext (TraceReceiverTerminalMap.shared P.X suffix fits) (P.site i) j)
    (origin : ∀ (i : Fin n) (k : Fin (P.L.ext (P.site i))),
      (P.value i).endpoint (k.cast (P.original i).external.symm)=2+(ext (P.site i) k).val)
    (fieldTables : ∀ f,tag f<2^W) (hidden : ∀ i,(nets i).internal≤G)
    (inputRoom : BitLayout.cellsBase p H≤S 9) (actualInput : ∀ a<BitLayout.cellsBase p H,
      P.initial a=TickMountedPins.memory pin a) :
    P.writers.Spec (·=elected)
      (fun _ z=>Gather.Prepared nets (ctrl:=regCursor) (control:=S 18) (H:=H) (atCmd:=cmd) wires pin
        (S 9) (List.ofFn (Gather.rootSpan (S 9) fun i=>(nets i).cells)) z) (P.writerCost elected) := by
  have beginEnd:=P.returned_cursor
  have totals:=P.returned_totals
  intro pp rr kk M pc reg pub exit installed data cfg input here eqn
  obtain ⟨t,paid,c,z,adv,done,ident⟩:=
    P.run_writers elected boot room num caches M pc reg pub exit installed data cfg input here eqn
  subst z
  refine ⟨t,paid,c,out,adv,done,?_⟩
  apply P.prepared nets wires pin H ext fits canonical network connected origin fieldTables hidden inputRoom actualInput
    (P.parent_node elected boot) beginEnd.1 beginEnd.2
  · exact (Fin.cast_val_eq_self _).symm.trans (congrArg (fun a:ℕ=>(a:Word W)) totals.1)
  · exact (Fin.cast_val_eq_self _).symm.trans (congrArg (fun a:ℕ=>(a:Word W)) totals.2)

/-- Transport the chosen public arities from the actual compiled S13 headers. -/
theorem Source.ready_cast (elected : Memory (64*w)) (boot : P.initial=beforeImage D count cap widths n (parentAt elected))
    (room : BeforeBounds D count cap widths n W) (num : ((parentAt elected) count).val=n)
    (caches : ∀ j (i : Fin n),(amountAddress (D).selected (D).first (D).results j (parentAt elected) (i.val:Word W)).val<(D).current)
    (a : Fin n→ℕ) (eqn : P.ports=a) (nets : ∀ i,BitNetwork F (a i)) (wires : ∀ i,Fin (a i)→Fin p)
    (pin : Fin p→Bool) (H : ℕ) (ext : ∀ z,Fin (P.L.ext z)→Fin p)
    (fits : suffix+P.X.widthSum≤p) (canonical : P.tag=tag)
    (network : ∀ i,HEq (P.value i).net (nets i))
    (connected : ∀ (i : Fin n) (j : Fin (P.ports i)),wires i (j.cast (congrFun eqn i))=
      P.L.ports.physicalSource ext (TraceReceiverTerminalMap.shared P.X suffix fits) (P.site i) j)
    (origin : ∀ (i : Fin n) (k : Fin (P.L.ext (P.site i))),
      (P.value i).endpoint (k.cast (P.original i).external.symm)=2+(ext (P.site i) k).val)
    (fieldTables : ∀ f,tag f<2^W) (hidden : ∀ i,(nets i).internal≤G)
    (inputRoom : BitLayout.cellsBase p H≤S 9) (actualInput : ∀ a<BitLayout.cellsBase p H,
      P.initial a=TickMountedPins.memory pin a) :
    P.writers.Spec (·=elected)
      (fun _ z=>Gather.Prepared nets (ctrl:=regCursor) (control:=S 18) (H:=H) (atCmd:=cmd) wires pin
        (S 9) (List.ofFn (Gather.rootSpan (S 9) fun i=>(nets i).cells)) z) (P.writerCost elected) := by
  subst a
  intro _ _ _ machine
  exact P.ready elected boot room num caches nets wires pin H ext fits canonical network
    (fun i a=>connected i a) origin fieldTables hidden inputRoom actualInput machine

end Hierarchy.TraceReceiverForward
end

end OAI
