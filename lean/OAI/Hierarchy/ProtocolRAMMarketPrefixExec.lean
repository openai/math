import OAI.Hierarchy.ProtocolRAMPurchaseMarketResult
import OAI.Hierarchy.ProtocolRAMCalendarMarketTypes
import OAI.Hierarchy.ProtocolRAMCalendarRun

namespace OAI
/-! # Execution and readback of the actual frozen chronological market prefix -/
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT ProtocolRAMPurchaseAllocation
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}

def Market.ready (v : Market z d k) (m : Shelf.Mem z d) : Prop :=
  v.failures.pass.Fits (wordBits z d copies) ∧ v.failures.base+v.failures.rows≤v.shelf.firstBase ∧
  1≤d ∧ v.flags+v.rows<2^wordBits z d copies ∧
    ∃ π : Equiv.Perm (Fin (2^z)), ∃ fixture : Shelf.Mem z d,
      v.shelf.Incoming (k:=k) v.sampler π v.depth v.phase v.temperature v.kind (v.failures.pass.apply m) ∧
      ∀ i : Key z d k,v.shelf.Prepared v.sampler v.depth fixture i (v.failures.pass.apply m)

def Market.prefix (v : Market z d k) : Prefix (wordBits z d copies) where
  native := (v.failures.pass.procedure _).seq (v.shelf.program v.sampler z d k v.depth)
  after := fun m=>v.shelf.result v.sampler k v.depth (v.failures.pass.apply m)
  ticks := v.failures.pass.clock+v.shelf.clock v.sampler z d k v.depth
  ready := v.ready
  runs := by
    rintro m ⟨fit,_,hd,room,π,fixture,incoming,rom⟩
    apply Procedure.Exec.then (v.failures.exec m fit)
    exact (v.shelf.run v.sampler π v.depth hd v.phase v.temperature v.kind _ fixture incoming rom room).1
  cheap := @cheap_seq (wordBits z d copies) (v.failures.pass.procedure _) (v.shelf.program v.sampler z d k v.depth)
    (@scan_cheap (wordBits z d copies) v.failures.base v.failures.rows v.failures.test)
    (@Shelf.cheap v.shelf v.sampler z d k v.depth)
  start := min v.failures.base v.shelf.firstBase
  stop := max (v.failures.base+v.failures.rows) (v.flags+v.rows)
  frame := by
    rintro m a ⟨_,_,hd,room,π,fixture,incoming,rom⟩ loc
    have stamp := (v.shelf.run v.sampler π v.depth hd v.phase v.temperature v.kind _ fixture incoming rom room).2.1
    have inside : a<v.shelf.firstBase ∨ v.flags+v.rows≤a := by rcases loc with h|h <;> omega
    exact (stamp a inside).trans (v.failures.frame m a (by rcases loc with h|h <;> omega))

theorem Market.failed_word (v : Market z d k) (m : Shelf.Mem z d) (h : v.ready m)
    (cut : v.failures.cut<2^wordBits z d copies) (i : Fin v.failures.rows) :
    v.prefix.after m (v.failures.base+i.val)=if v.failures.cut<v.failures.value m i then 1 else 0 := by
  obtain ⟨_,lo,hd,room,π,fixture,incoming,rom⟩ := h
  have stamp := (v.shelf.run v.sampler π v.depth hd v.phase v.temperature v.kind _ fixture incoming rom room).2.1
  exact (stamp _ (Or.inl (by have := i.isLt; omega))).trans (v.failures.read m i cut)


end
end Hierarchy.ProtocolRAM.Calendar

end OAI
