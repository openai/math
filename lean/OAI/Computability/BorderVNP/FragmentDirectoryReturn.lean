import OAI.Computability.BorderVNP.FragmentDirectoryInputArena
import OAI.Computability.BorderVNP.FragmentRowsSparseReadback

/-! # The real fragment emitter and stable bucket on every returning path -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM Evaluator.ScheduleClock

variable {w u v k ctl : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (a : SignedTaskArena.Layout)
local notation "head" => readings pub 0
local notation "mem" => readings m
local notation "f" => Layout.fromFrame head mem

/-- Recover the sparse emitter's actual intermediate image and the stable bucket
result at the final registers and memory of the given native return. -/
theorem emission_of_return (fit : (f).Fits w mem) (ptr : mem (head+92)=ctl)
    (words : ∀ i : Fin 37, mem (ctl+i.val)=a.controls i.val)
    (low : head+112 ≤ ctl) (below : ctl+37 ≤ a.fragments.quads)
    (cables : (f).host.count = a.cube.cables) (raw : mem (head+9) ≤ a.cube.maxRows)
    (cellCount : mem (head+11)=a.cube.cells) (high : a.endAddress w u v k < 2^w)
    {es t mt} (run : Runs pub mac emitBucket s m es t mt) :
    ∃ e : SparseEmission a f m fit cellCount.symm, e.bank=t ∧ e.output=mt := by
  obtain ⟨_,_,_,rr,_,_,r,middle,_,image,_,result⟩ :=
    emitBucket_run pub mac s m a ctl u v k fit ptr words low below cables raw cellCount high
  obtain ⟨_,rfl,rfl⟩ := run.unique_of_deterministic (by decide) rr
  have quads : (f).quads=a.fragments.quads := by
    change mem (mem (head+92)+28)=_
    rw [ptr]
    exact words ⟨28,by decide⟩
  exact ⟨⟨.ofWords r middle,_,_,image,result,quads,cables,raw⟩,rfl,rfl⟩

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
