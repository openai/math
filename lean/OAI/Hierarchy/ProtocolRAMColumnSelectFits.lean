import OAI.Hierarchy.ProtocolRAMRowChoiceFits
import OAI.Hierarchy.ProtocolRAMStripColumnInputs
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! Bounds of the native finite column selector and its group directory. -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage PurchaseFrozen PurchaseCT Calendar CatalogueRows
open scoped Classical Fin.CommRing
variable {z d k w attempts : ℕ}

private theorem bank_fits (b : Bank) {out : ℕ} (room : out<2^w) (endAt : b.base+b.size≤ out) : b.Fits w out :=
  ⟨Nat.two_pow_pos _,by omega,endAt⟩

theorem select_fits (h : StockCommit.PortHeader) {n out : ℕ} (xs : Fin n→Expr)
    (room : out<2^w) (head : h.stop≤ out) (terms : ∀i,(xs i).Fits w out) : (select h xs).Fits w out := by
  have address : h.start+2*h.small+2*h.large≤ out := by
    simp only [StockCommit.PortHeader.stop,StockCommit.PortHeader.parity,StockCommit.PortHeader.owner] at head
    omega
  have ball : h.ballTerm.Fits w out := ⟨bank_fits _ room (by change h.start+h.small≤ out;omega),trivial⟩
  have field : h.fieldTerm.Fits w out :=
    ⟨bank_fits _ room (by change h.start+h.small+h.small≤ out;omega),trivial⟩
  exact choose_fits_bound n 0 _ _ (fun i=>fits_atRow _ _ (terms i) field) ball

theorem remap_end (start : ℕ) (t : StageAt z d) :
    (ReportGroupROM.bank start z d t).base+(ReportGroupROM.bank start z d t).size≤ start+ReportGroupROM.words z d := by
  have bound := Nat.mul_le_mul_right (ReportGroupROM.stride z d) t.isLt
  rw [Nat.succ_mul] at bound
  change start+t.val*ReportGroupROM.stride z d+ReportGroupROM.stride z d≤ start+_
  unfold ReportGroupROM.words
  omega

end Hierarchy.ProtocolRAM.BoughtSockets
end

end OAI
