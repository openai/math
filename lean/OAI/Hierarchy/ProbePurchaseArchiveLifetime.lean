import OAI.Hierarchy.ProbePurchaseArchiveCellBound
import OAI.Hierarchy.ProbePurchaseArchiveOrigin
import OAI.Hierarchy.ProbePurchaseArchiveReads
import OAI.Hierarchy.ProbeInstalledReplayStock

namespace OAI
/-! # One allocated arena interval preserves every selected path through each later purchase replay -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen
open scoped Fin.CommRing Classical
variable {z d k q goods : ℕ}

namespace Calendar
open StripDirectory
theorem purchased_replay_archive {sh : Shelf} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^z))}
    {depth start : ℕ} {old : PhasePrice} {T : ℝ} {kind : ℕ} {frozen : Shelf.Mem z d}
    (C : Chart (wordBits z d copies) q goods) (m : Shelf.Mem z d) (arena : Arena) (p a j b : ℕ)
    (saved : ArchiveReads sh S π depth start old T kind frozen (reserveState C m p a 0) k)
    (whole : mounted C (events C.mesh) m) (hp : p< C.mesh.inject+C.mesh.cool) (ha : a< C.mesh.outerFuel)
    (hj : j< C.mesh.reserveSteps) (hb : b< C.mesh.innerFuel) (hd : 1≤ d)
    (header : (stratumHeader z d k S.degree depth start).stop≤ sh.firstBase)
    (allocated : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth≤ arena.base C.mesh (.attempt (.outer p a))+arena.stride)
    (floor : ∀e x,x< arena.base C.mesh e→protected C x e) :
    ArchiveReads sh S π depth start old T kind frozen (replayScoreMemory C m p a j b) k := by
  apply saved.change
  intro x used
  have initial:=(archiveCell_lt hd header used).trans_le allocated
  have later:=purchaseTail_safe C arena p a j b x floor initial
  have under : x< arena.base C.mesh (.attempt (.inner p a j b)) := by
    apply initial.trans_le (arena.apart C.mesh _)
    dsimp only [position,sliceBase]
    omega
  rw [replay_prior C m p a j b x (inner_head_ready whole hp ha hj hb) (floor _ _ under)]
  exact purchase_archive C m p a j b x (purchaseTail_mounted whole hp ha hj hb.le) later

end Calendar
end Hierarchy.ProtocolRAM
end

end OAI
