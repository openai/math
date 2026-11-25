import OAI.Computability.BorderVNP.RoutingISAScheduleClockArgumentVisits
import OAI.Computability.BorderVNP.FragmentBucketArena

/-! # The schedule clock's fragment inputs at the actual signed-arena addresses -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM

variable {w u v k ctl : ℕ} (pub : Arg → Word w) (m : Memory w) (a : SignedTaskArena.Layout)
local notation "head" => readings pub 0
local notation "mem" => readings m
local notation "f" => FragmentRows.Layout.fromFrame head mem

/-- Construct the argument stage's real fragment input from its post-report RAM.
The emitter's three scans determine the occupied row count. Its count store and
the signed arena's preserved scalar controls supply the bucketer's header. -/
noncomputable def FragmentDirectoryInput.ofArena (fit : (f).Fits w mem) (ptr : mem (head+92)=ctl)
    (words : ∀ i : Fin 37, mem (ctl+i.val)=a.controls i.val)
    (low : head+112 ≤ ctl) (below : ctl+37 ≤ a.fragments.quads)
    (cables : (f).host.count = a.cube.cables) (raw : mem (head+9) ≤ a.cube.maxRows)
    (cellCount : mem (head+11)=a.cube.cells) (high : a.endAddress w u v k < 2^w) :
    FragmentDirectoryInput pub m := by
  let info := FragmentArena.bucket_after_emitter a mem ptr words low below cables raw high
  refine ⟨f,a.fragments.bucket ((f).stream mem).length,ctl,rfl,fit,?_,rfl,cellCount.symm,
    info.1,info.2.1,info.2.2.1,info.2.2.2⟩
  change a.fragments.quads = mem (mem (head+92)+28)
  rw [ptr]
  exact (words ⟨28,by decide⟩).symm

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
