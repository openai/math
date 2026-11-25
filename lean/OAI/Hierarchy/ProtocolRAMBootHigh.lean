import OAI.Hierarchy.ProtocolRAMCalendarBoot

namespace OAI
/-! # High original words and enlarged finite input tapes for the physical subdivision -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen
open scoped Classical Fin.CommRing

theorem Boot.Layout.extend {z d k jobs small large : ℕ} {v : Fin jobs→Market z d k}
    (layout : Boot.Layout v small) (enlarge : small≤large) : Boot.Layout v large :=
  ⟨layout.subdivision.trans enlarge,layout.afterHeap,fun i=>(layout.extent i).trans enlarge,layout.threshold,layout.apart⟩

/-- A later private page on the enlarged *original* input reaches the actual
post-subdivision memory even when the original header slice was shorter. -/
theorem Boot.Receipt.high {z d k jobs size x : ℕ} {v : Fin jobs→Market z d k} {π : Equiv.Perm (Fin (2^z))}
    {words mid : Boot.Tape z d} (h : Boot.Receipt v π (Computability.VPVNP.RAMMemory.initialMemory size words) mid)
    (inTape : x<size) (heap : heapEnd z d copies≤x) (high : ∀i,Boot.high (v i)≤x) :
    mid x=words x := by
  have kept:=h.kept x heap (fun i hit=>hit.2.not_ge (high i))
  simpa only [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left inTape] using kept

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
