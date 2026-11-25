import OAI.Hierarchy.ProtocolRAMPurchaseShelfGeometry
import OAI.Hierarchy.ProtocolRAMPurchaseAllocation
import OAI.Hierarchy.ProbeStageTemplateSize
import OAI.Hierarchy.ProbeAdvisedPurchase

namespace OAI
/-! The upper end of the actual allocated frozen-purchase shelf. -/
namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT ProtocolRAMPurchaseAllocation Filter
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}
theorem end_le (sh : Shelf) (S : PurchaseSampler) (depth : ℕ) (i : Key z d k) (hd : 1≤d) :
    (sh.L S depth i).endAddress ≤ sh.hi S depth i := by
  let B := sh.L S depth i
  let shape := stageAt z d (stage i)
  let : Nonempty shape.Group := ⟨(advisedStage z d (Equiv.refl _) (stage i)).group 0⟩
  have dim := template_dyadic hd shape (List.get_mem ..)
  have big := B.end_linear (4^(rounds d+1)) (Nat.two_pow_pos z) (Fintype.card_pos (α:=shape.Group))
    ((Nat.two_pow_pos _).trans_le dim.span_lower) rfl dim.2
  have small : Layout.linearFactor (4^(rounds d+1)) S.degree depth*2^z≤blockSize z d S.degree depth :=
    Nat.mul_le_mul_right _ (Nat.le_succ _)
  change B.endAddress ≤ sh.lo S depth i+Layout.linearFactor (4^(rounds d+1)) S.degree depth*2^z at big
  change B.endAddress ≤ sh.hi S depth i
  simp only [hi,lo,Nat.succ_mul] at big ⊢
  omega
end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

end OAI
