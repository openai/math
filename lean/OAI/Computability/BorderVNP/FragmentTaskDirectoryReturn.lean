import OAI.Computability.BorderVNP.FragmentTaskDirectoryRoom

/-! # Typed input fields and numerical room on each native stable-bucket return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM FragmentRows

variable {w u v k ctl team offsets live ports : ℕ} (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) (a : SignedTaskArena.Layout)
local notation "head" => readings pub 0
local notation "mem" => readings m
local notation "f" => FragmentRows.Layout.fromFrame head mem
local notation "task" => a.tasks team head offsets ctl

/-- Every native return of the joined fragment emitter and bucket has the
exact field loads and numeric room used by the next task builder. The two
predicates refer to the actual output memory of that particular return. -/
theorem task_inputs_of_return_owned (fit : (f).Fits w mem) (ptr : mem (head+92)=ctl)
    (words : ∀ i : Fin 37, mem (ctl+i.val)=a.controls i.val)
    (place : a.SparsePlacement head ctl) (cables : (f).host.count = a.cube.cables)
    (raw : mem (head+9) ≤ a.cube.maxRows) (cellCount : mem (head+11)=a.cube.cells)
    (high : a.endAddress w u v k < 2^w)
    (outer : (a.controlRows team head offsets ctl live ports).Fields mem)
    (calls : mem (head+14)=a.before.limit) (tasks : mem (head+89)=(task).tasks)
    (geometry : TaskSourceGeometry a head offsets ctl mem (some team))
    (x : Returns (.seq FragmentRows.program FragmentBucket.program) pub mac s m) :
    (task).Fields (readings x.val.2.2) ∧ (task).Room (readings x.val.2.2) w := by
  have order := a.sparse_order place.cells
  have below : ctl+37 ≤ a.fragments.quads := place.beforeBank.trans (order.1.trans order.2.1)
  obtain ⟨e,_,out⟩ := emission_of_return pub mac s m a fit ptr words place.beforeControl below
    cables raw cellCount high x.property
  rw [←out]
  exact ⟨e.task_fields ptr place outer calls tasks words,e.task_room_owned ptr place geometry high⟩

/-- A source bounded at every cell supplies the same native task-builder input. -/
theorem task_inputs_of_return (fit : (f).Fits w mem) (ptr : mem (head+92)=ctl)
    (words : ∀ i : Fin 37, mem (ctl+i.val)=a.controls i.val)
    (place : a.SparsePlacement head ctl) (cables : (f).host.count = a.cube.cables)
    (raw : mem (head+9) ≤ a.cube.maxRows) (cellCount : mem (head+11)=a.cube.cells)
    (high : a.endAddress w u v k < 2^w)
    (outer : (a.controlRows team head offsets ctl live ports).Fields mem)
    (calls : mem (head+14)=a.before.limit) (tasks : mem (head+89)=(task).tasks)
    (geometry : TaskSourceGeometry a head offsets ctl mem)
    (x : Returns (.seq FragmentRows.program FragmentBucket.program) pub mac s m) :
    (task).Fields (readings x.val.2.2) ∧ (task).Room (readings x.val.2.2) w :=
  task_inputs_of_return_owned pub mac s m a fit ptr words place cables raw cellCount high outer calls tasks (geometry.atTeam team) x

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
