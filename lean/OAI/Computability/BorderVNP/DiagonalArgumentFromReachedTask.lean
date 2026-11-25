import OAI.Computability.BorderVNP.FragmentArgumentInputArena

/-! # Preparing an argument input from its reached task-builder memory

The first two deterministic native producers can run before any sparse call
has returned. A sparse input on their one reached memory suffices on every
published image in the report continuation.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM ScheduleClock FragmentRows

variable {w u v k ctl team offsets live ports : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (a : SignedTaskArena.Layout)

local notation "head" => readings pub 0
local notation "mem" => readings m
local notation "f" => FragmentRows.Layout.fromFrame head mem
local notation "task" => a.tasks team head offsets ctl

/-- Run the emitter, stable bucket and typed task builder on the post-report
memory, then use the sparse source at their actual return. Observing a full
argument return is unnecessary for constructing the inverse report fiber. -/
theorem ArgumentInput.ofOwnedTask (fit : (f).Fits w mem) (ptr : mem (head+92)=ctl)
    (words : ∀ i : Fin 37, mem (ctl+i.val)=a.controls i.val)
    (place : a.SparsePlacement head ctl) (cables : (f).host.count=a.cube.cables)
    (raw : mem (head+9)≤a.cube.maxRows) (cellCount : mem (head+11)=a.cube.cells)
    (high : a.endAddress w u v k<2^w)
    (outer : (a.controlRows team head offsets ctl live ports).Fields mem)
    (calls : mem (head+14)=a.before.limit) (tasks : mem (head+89)=(task).tasks)
    (geometry : TaskSourceGeometry a head offsets ctl mem (some team))
    (sparse : ∀ (first : Returns emitBucket pub mac s m) (e : SparseEmission a f m fit cellCount.symm),
      e.bank=first.val.2.1 → e.output=first.val.2.2 →
      ∀ next : Returns TypedTaskBuilder.program pub mac e.bank e.output,
        readings next.val.2.2=(task).published (readings e.output) → Nonempty (SparseCallInput pub next.val.2.2)) :
    Nonempty (ArgumentInput pub mac s m) := by
  have order := a.sparse_order place.cells
  have below := place.beforeBank.trans (order.1.trans order.2.1)
  let fr := FragmentDirectoryInput.ofArena pub m a fit ptr words place.beforeControl below cables raw cellCount high
  obtain ⟨events,bank,bucket,run,_,_⟩ := fragmentDirectory_run pub mac s m fr.layout fr.bucket fr.control fr.loaded fr.fit
    fr.base fr.rows fr.cells fr.room fr.header fr.frame fr.controlRoom
  let first : Returns emitBucket pub mac s m := ⟨(events,bank,bucket),run⟩
  obtain ⟨e,hb,hm⟩ := emission_of_return pub mac s m a fit ptr words place.beforeControl below cables raw cellCount high run
  have fields := e.task_fields ptr place outer calls tasks words
  have room := e.task_room_owned (team:=team) ptr place geometry high
  obtain ⟨trace,r,mt,rb,_,image⟩ := TypedTaskBuilder.program_run pub mac e.bank e.output task rfl fields room
  let next : Returns TypedTaskBuilder.program pub mac e.bank e.output := ⟨(trace,r,mt),rb⟩
  obtain ⟨arg⟩ := sparse first e hb hm next image
  refine ⟨ArgumentInput.ofOwnedArena pub mac s m a fit ptr words place cables raw cellCount high outer calls tasks geometry ?_⟩
  intro x result published
  have settled := (x.property.unique_of_deterministic (by decide) run).2.2
  have eqReads : readings result=readings mt :=
    published.trans ((congrArg (fun z : Memory w => (task).published (readings z)) (settled.trans hm.symm)).trans image.symm)
  have eqMemory : mt=result := funext fun z => Fin.ext (congrFun eqReads z).symm
  exact eqMemory ▸ arg

/-- Specialize the reached-task construction when all global extents are fitted. -/
theorem ArgumentInput.ofReachedTask (fit : (f).Fits w mem) (ptr : mem (head+92)=ctl)
    (words : ∀ i : Fin 37, mem (ctl+i.val)=a.controls i.val)
    (place : a.SparsePlacement head ctl) (cables : (f).host.count=a.cube.cables)
    (raw : mem (head+9)≤a.cube.maxRows) (cellCount : mem (head+11)=a.cube.cells)
    (high : a.endAddress w u v k<2^w)
    (outer : (a.controlRows team head offsets ctl live ports).Fields mem)
    (calls : mem (head+14)=a.before.limit) (tasks : mem (head+89)=(task).tasks)
    (geometry : TaskSourceGeometry a head offsets ctl mem)
    (sparse : ∀ (first : Returns emitBucket pub mac s m) (e : SparseEmission a f m fit cellCount.symm),
      e.bank=first.val.2.1 → e.output=first.val.2.2 →
      ∀ next : Returns TypedTaskBuilder.program pub mac e.bank e.output,
        readings next.val.2.2=(task).published (readings e.output) → Nonempty (SparseCallInput pub next.val.2.2)) :
    Nonempty (ArgumentInput pub mac s m) := by
  exact ArgumentInput.ofOwnedTask pub mac s m a fit ptr words place cables raw cellCount high outer calls tasks
    (geometry.atTeam team) sparse

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
