import OAI.Hierarchy.ProtocolRAMCalendarStockBanks
import OAI.Hierarchy.ProtocolRAMPurchaseInventory

namespace OAI
/-! # The active and purchased stock address at a dated event -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DatedGoods
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {W : ℕ}

def phase (c : Mesh) : Option Event→ℕ
  | some (.attempt (.outer p _)) | some (.attempt (.inner p _ _ _)) |
    some (.feed (.outer p)) | some (.feed (.inner p _ _)) =>p
  | none=>c.inject+c.cool

def releases : Option Event→ℕ
  | some (.attempt (.inner _ _ j _)) | some (.feed (.inner _ _ j)) => j
  | _=>0

def previous (c : Mesh) (b : StockBound.Banks) (j : ℕ) : ℕ :=
  if h : 0<j ∧ j≤(events c).length then b.active ((events c)[j-1]'(by omega)) else b.initial

def parent (e : Option Event) : Option Attempt := e.bind StockBound.parent

def stash (b : StockBound.Banks) (e : Option Event) : ℕ := (parent e).elim b.zeroReserve b.saved

def bought (modeAt : Attempt→ℕ) (e : Option Event) (m : Memory W) : Bool :=
  (parent e).elim false (fun a=>decide (m (modeAt a)=(3:Word W)))

end Hierarchy.ProtocolRAM.Calendar.DatedGoods
end

end OAI
