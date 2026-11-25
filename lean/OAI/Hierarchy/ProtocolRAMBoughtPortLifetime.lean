import OAI.Hierarchy.ProtocolRAMPurchaseMarketPorts
import OAI.Hierarchy.ProtocolRAMPreparedFrame

namespace OAI
/-! # Read the original CT sockets and path tiles after the calendar suffix -/

namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen ProtocolRAMPurchaseAllocation
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}

theorem PurchaseFrozen.Shelf.PortData.of_frame {sh : Shelf} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^z))}
    {depth : ℕ} {i : Key z d k} {before after : Shelf.Mem z d} (data : sh.PortData S π depth i before)
    (room : (sh.L S depth i).endAddress<2^wordBits z d Native.copies)
    (unchanged : ∀a,a<heapEnd z d Native.copies ∨ ((sh.L S depth i).start≤a ∧ a<(sh.L S depth i).endAddress) → after a=before a) :
    sh.PortData S π depth i after := by
  let L:=sh.L S depth i
  obtain ⟨a₀,a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈⟩ := L.regions
  have read (c : Fin 3) (r : Word (wordBits z d Native.copies)) :=
    unchanged ((stageBank z d (stageNumber (stage i)) c).base+r.val%(stageBank z d (stageNumber (stage i)) c).size)
      (.inl ((Nat.add_lt_add_left (Nat.mod_lt _ (Nat.two_pow_pos _)) _).trans_le (stageBank_end z d _ c)))
  refine ⟨?_,?_,fun r=>(read 1 _).trans (data.inputSocket r),fun r=>(read 2 _).trans (data.outputSocket r),?_⟩
  · intro r j
    have range:=L.source_range r j
    exact (unchanged _ (.inr range)).trans (data.tiles r j)
  · apply data.directory.of_frame
    intro a lo hi
    change a < L.directory + (L.height + 1) * PurchaseDirectory.span L.rows L.degree L.height at hi
    have endBound : a < L.endAddress := by omega
    exact unchanged a (.inr ⟨a₀.trans lo, endBound⟩)
  · intro j
    dsimp only
    intro o
    let b:=ProtocolRAMPurchaseSampler.backward L.start L.groups L.sockets S.degree j
    let addr:=b.base+(o.val:Word (wordBits z d Native.copies)).val%b.size
    have limit : L.start+ProtocolRAMPurchaseSampler.words L.groups L.sockets L.degree<2^wordBits z d Native.copies := by
      change L.directory<_
      change L.endAddress<_ at room
      omega
    have fit:=ProtocolRAMPurchaseSampler.backward_fits L.start L.groups j limit
    have low : L.start≤addr := by dsimp [addr,b,ProtocolRAMPurchaseSampler.backward,ProtocolRAMPurchaseSampler.lane];omega
    have hi : addr<L.directory := (Nat.add_lt_add_left (Nat.mod_lt _ fit.1) _).trans_le fit.2.2
    have endBound : addr < L.endAddress := by omega
    exact (unchanged addr (.inr ⟨low,endBound⟩)).trans (data.back j o)

end
end Hierarchy.ProtocolRAM

end OAI
