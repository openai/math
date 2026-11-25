import OAI.Computability.BorderVNP.FragmentTaskDirectoryReturn
import OAI.Computability.BorderVNP.RoutingISASignedPrepArguments

/-! # Real public argument inputs on the signed fragment and task arenas -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM ScheduleClock FragmentRows

variable {w u v k ctl team offsets live ports : ℕ} (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w) (a : SignedTaskArena.Layout)
local notation "head" => readings pub 0
local notation "mem" => readings m
local notation "f" => FragmentRows.Layout.fromFrame head mem
local notation "task" => a.tasks team head offsets ctl

/-- Place the emitter, stable bucket and task builder in the actual signed
argument stage. The final sparse continuation is queried at its own builder's
published image for each returning bucket memory. -/
noncomputable def ArgumentInput.ofOwnedArena (fit : (f).Fits w mem) (ptr : mem (head+92)=ctl)
    (words : ∀ i : Fin 37, mem (ctl+i.val)=a.controls i.val)
    (place : a.SparsePlacement head ctl) (cables : (f).host.count=a.cube.cables)
    (raw : mem (head+9) ≤ a.cube.maxRows) (cellCount : mem (head+11)=a.cube.cells)
    (high : a.endAddress w u v k < 2^w)
    (outer : (a.controlRows team head offsets ctl live ports).Fields mem)
    (calls : mem (head+14)=a.before.limit) (tasks : mem (head+89)=(task).tasks)
    (geometry : TaskSourceGeometry a head offsets ctl mem (some team))
    (continuation : ∀ x : Returns (.seq FragmentRows.program FragmentBucket.program) pub mac s m,
      ∀ result : Memory w, readings result=(task).published (readings x.val.2.2) → SparseCallInput pub result) :
    ArgumentInput pub mac s m := by
  have order := a.sparse_order place.cells
  have below : ctl+37 ≤ a.fragments.quads := place.beforeBank.trans (order.1.trans order.2.1)
  have src := task_inputs_of_return_owned pub mac s m a fit ptr words place cables raw cellCount high outer calls tasks geometry
  exact ⟨FragmentDirectoryInput.ofArena pub m a fit ptr words place.beforeControl below cables raw cellCount high,
    task,rfl,fun x => (src x).1,fun x => (src x).2,continuation⟩

/-- Construct the public argument input when every cell extent is already fitted. -/
noncomputable def ArgumentInput.ofArena (fit : (f).Fits w mem) (ptr : mem (head+92)=ctl)
    (words : ∀ i : Fin 37, mem (ctl+i.val)=a.controls i.val)
    (place : a.SparsePlacement head ctl) (cables : (f).host.count=a.cube.cables)
    (raw : mem (head+9) ≤ a.cube.maxRows) (cellCount : mem (head+11)=a.cube.cells)
    (high : a.endAddress w u v k < 2^w)
    (outer : (a.controlRows team head offsets ctl live ports).Fields mem)
    (calls : mem (head+14)=a.before.limit) (tasks : mem (head+89)=(task).tasks)
    (geometry : TaskSourceGeometry a head offsets ctl mem)
    (continuation : ∀ x : Returns (.seq FragmentRows.program FragmentBucket.program) pub mac s m,
      ∀ result : Memory w, readings result=(task).published (readings x.val.2.2) → SparseCallInput pub result) :
    ArgumentInput pub mac s m :=
  ArgumentInput.ofOwnedArena pub mac s m a fit ptr words place cables raw cellCount high outer calls tasks
    (geometry.atTeam team) continuation

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
