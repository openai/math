import OAI.Hierarchy.ProbePurchaseArchiveCellBound
import OAI.Hierarchy.ProtocolRAMCalendarPurchaseTailSafe
import OAI.Hierarchy.ProtocolRAMCalendarRemainders
import OAI.Hierarchy.ProtocolRAMCalendarMount
import OAI.Hierarchy.ProtocolRAMCatalystChargedDates

namespace OAI
/-! # The original purchased shelf at the finite prefix of a priced inner attempt -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen StripDirectory CatalystArchive
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {z d k q goods w r edges : ℕ}

theorem Slot.entryMemory {C : Chart w q goods} {initial current : Memory w} {a : Attempt} {pre post : List Event}
    (cut : Slot C initial (.attempt a) pre post current) : entryMemory C initial a=current := by
  rw [CatalystArchive.entryMemory,cut.ordinal,cut.events,List.take_left]
  exact cut.entry

/-- Every original tile, flag and stratum-header word has exactly its
post-purchase value at entry to the priced inner attempt. -/
theorem purchased_entry_archive {sh : Shelf} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^z))}
    {depth start : ℕ} {old : PhasePrice} {price : ℝ} {kind : ℕ} {frozen : Shelf.Mem z d}
    (C : Chart (wordBits z d copies) q goods) (initial : Shelf.Mem z d) (arena : Arena) (p a j t : ℕ)
    (saved : ArchiveReads sh S π depth start old price kind frozen (reserveState C initial p a 0) k)
    (whole : mounted C (events C.mesh) initial) (hp : p<C.mesh.inject+C.mesh.cool) (ha : a<C.mesh.outerFuel)
    (hj : j<C.mesh.reserveSteps) (ht : t<C.mesh.innerFuel) (hd : 1≤d)
    (keys : (stratumHeader z d k S.degree depth start).stop≤ sh.firstBase)
    (allocated : sh.flagsBase S z d k depth+count z d k*paths z S.degree depth≤arena.base C.mesh (.attempt (.outer p a))+arena.stride)
    (floor : ∀e x,x<arena.base C.mesh e→protected C x e) :
    ArchiveReads sh S π depth start old price kind frozen (entryMemory C initial (.inner p a j t)) k := by
  obtain ⟨tail,slot⟩ := inner_slot C initial p a j t hp ha hj ht whole
  rw [slot.entryMemory]
  apply saved.change
  intro x used
  have fit := (archiveCell_lt hd keys used).trans_le allocated
  exact purchase_archive C initial p a j t x (purchaseTail_mounted whole hp ha hj ht.le)
    (purchaseTail_safe C arena p a j t x floor fit)

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
