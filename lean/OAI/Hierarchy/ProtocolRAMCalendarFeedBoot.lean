import OAI.Hierarchy.ProtocolRAMCalendarFeedStock
import OAI.Hierarchy.ProtocolRAMCalendarBoot
import OAI.Hierarchy.ProtocolRAMCalendarFeedLifetime

namespace OAI
/-! # Installing the actual reserve-slice ROM in the finite permutation header -/

namespace Hierarchy.ProtocolRAM.Calendar.Boot
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen
open ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section
variable {z d k q goods jobs : ℕ}

/-- The external permutation occupies the leading words. The public reserve ROM
is written into the same finite header that feeds the native subdivision. -/
def feedHeader (π : Equiv.Perm (Fin (2^z))) (table : Bank) (steps stride : ℕ) (rest : Tape z d) : Tape z d :=
  permutationWords π (feedAdvice table steps stride rest)

theorem booted_slice (v : Fin jobs→Market z d k) {size : ℕ} (layout : Layout v size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (table : Bank) (steps stride : ℕ) (rest : Tape z d)
    (afterPermutation : 2^z≤table.base) (afterHeap : heapEnd z d copies≤table.base)
    (fits : table.base+steps*stride≤ size) (low : ∀ i,table.base+steps*stride≤Boot.low (v i)) :
    ∀ x,table.base≤x → x<table.base+steps*stride →
      booted v size (feedHeader π table steps stride rest) x=feedAdvice table steps stride rest x := by
  let header := feedHeader π table steps stride rest
  obtain ⟨_,receipt⟩ := start v layout hd π header
    (fun i=>permutationWords_get π (feedAdvice table steps stride rest) i)
  intro x lo hi
  have old := receipt.kept x (afterHeap.trans lo) (fun i inside=>(hi.trans_le (low i)).not_ge inside.1)
  have high : ¬x<2^z := not_lt.mpr (afterPermutation.trans lo)
  simpa only [header,feedHeader,Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (hi.trans_le fits),permutationWords,
    dite_eq_right high] using old

/-- The typed lookup used at an actual calendared reserve feed reads precisely
the initially supplied public integer. No per-trial copy of the table is needed. -/
theorem live_slice (v : Fin jobs→Market z d k) {size : ℕ} (layout : Layout v size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (C : Chart (wordBits z d copies) q goods) (arena : Arena)
    (table : Bank) (stride : ℕ) (rest : Tape z d) (p a j b : ℕ)
    (afterPermutation : 2^z≤table.base) (afterHeap : heapEnd z d copies≤table.base)
    (fits : table.base+C.mesh.reserveSteps*stride≤ size)
    (low : ∀ i,table.base+C.mesh.reserveSteps*stride≤Boot.low (v i))
    (floor : ∀ e u,u<arena.base C.mesh e→protected C u e)
    (first : table.base+C.mesh.reserveSteps*stride≤arena.first)
    (mounted : Calendar.mounted C (FeedLayout.beforeInner C.mesh p a j b)
      (booted v size (feedHeader π table C.mesh.reserveSteps stride rest))) :
    ∀ x,table.base≤x → x<table.base+C.mesh.reserveSteps*stride →
      innerState C (booted v size (feedHeader π table C.mesh.reserveSteps stride rest)) p a j b x =
        feedAdvice table C.mesh.reserveSteps stride rest x := by
  intro x hx hi
  rw [FeedLayout.inner_as_run]
  exact (run_frame C _ _ x mounted (fun e _=>floor e x
    ((hi.trans_le first).trans_le (Nat.le_add_right ..)))).trans
    (booted_slice v layout hd π table _ stride rest afterPermutation afterHeap fits low x hx hi)

end
end Hierarchy.ProtocolRAM.Calendar.Boot

end OAI
