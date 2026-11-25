import OAI.Hierarchy.ProtocolRAMCatalystPurchasedBirth
import OAI.Hierarchy.ProtocolRAMPurchaseShelfUpper
import OAI.Hierarchy.ProtocolRAMPurchaseSlabFrame

namespace OAI
/-! The physical cells occupied by one retained DFS purchase and its signed flag. -/
noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen
open scoped Fin.CommRing Classical
variable {z d k : ℕ}
theorem archiveCell_lt {sh : Shelf} {S : PurchaseSampler} {depth start x : ℕ}
    (hd : 1≤ d) (header : (stratumHeader z d k S.degree depth start).stop≤ sh.firstBase)
    (used : ArchiveCell (z:=z) (d:=d) (k:=k) sh S depth start x) :
    x< sh.flagsBase S z d k depth+count z d k*paths z S.degree depth := by
  rcases used with ⟨key,i,j,rfl⟩|⟨key,i,rfl⟩|h
  · have localRange:=(sh.L S depth key).source_range i j
    have last:=(sh.end_le S depth key hd).trans (sh.final_after S depth key)
    dsimp only [Shelf.flagsBase]
    exact localRange.2.trans_le (by omega)
  · have range : key.val<count z d k :=key.isLt
    have last:=Nat.mul_le_mul_right (paths z S.degree depth) range
    rw [Nat.succ_mul] at last
    have hi:=i.isLt
    omega
  · have lo:=h.2.trans_le header
    dsimp only [Shelf.flagsBase]
    omega
end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
