import OAI.Hierarchy.ProtocolRAMNativePricedChart
import OAI.Hierarchy.ProtocolRAMMarketPrefixExec
import OAI.Hierarchy.ProtocolRAMNativeFormat
import OAI.Hierarchy.ProtocolRAMStockCommitProgram
import OAI.Hierarchy.ProtocolRAMCalendarMarketShape
import OAI.Hierarchy.ProtocolRAMStockPortPlan
import OAI.Hierarchy.ProtocolRAMCalendarSettlement
import OAI.Hierarchy.ProtocolRAMCalendarTime
import OAI.Hierarchy.ProtocolRAMPurchaseMarketResult
import OAI.Hierarchy.ProtocolRAMRepairCharges
import OAI.Hierarchy.ProtocolRAMFailureWords

namespace OAI
/-! # The actual all-sign chronological purchase prefix at each mesh site -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT ProtocolRAMPurchaseAllocation
open ThreeFlat.RAM PhysicalProcedure
open PurchaseFrozen
open scoped Fin.CommRing Classical
noncomputable section
variable {z d k : ℕ}

def chart {q goods : ℕ} (c : Mesh) (modeAt stopAt : Attempt→ℕ) (market : Attempt→Market z d k)
    (stock : Attempt→StockCommit) (boards : Attempt→PurchaseStage.Repair q goods)
    (columns : Boundary→List CommodityColumn) : Chart (wordBits z d copies) q goods :=
  chartWith c modeAt stopAt market (fun a b=>(stock a).native _ (market a).rows b) boards columns

/-- A fixed public phase table changes its time coordinate on every scheduled
boundary, including the half-time start of every prospective purchase. -/
def timedChart {q goods : ℕ} (c : Mesh) (finish : ℝ) (prices : PhasePrice) (modeAt stopAt : Attempt→ℕ)
    (market : Attempt→Market z d k) (stock : Attempt→StockCommit)
    (boards : Attempt→PurchaseStage.Repair q goods) (columns : Boundary→List CommodityColumn) :=
  chart (z := z) (d := d) (k := k) c modeAt stopAt
    (fun a=>{market a with phase:=deadline c finish prices a}) stock boards columns

theorem union_word (v : Market z d k) (π : Equiv.Perm (Fin (2^z))) (m fixture : Shelf.Mem z d)
    (hd : 1≤d) (incoming : v.shelf.Incoming (k:=k) v.sampler π v.depth v.phase v.temperature v.kind (v.failures.pass.apply m))
    (rom : ∀ i : Key z d k,v.shelf.Prepared v.sampler v.depth fixture i (v.failures.pass.apply m))
    (space : v.flags+v.rows<2^wordBits z d copies) (i : Key z d k)
    (u : Fin (paths z v.sampler.degree v.depth)) :
    v.prefix.after m (v.flags+i.val*paths z v.sampler.degree v.depth+u.val)=
    MarkTape.encode (wordBits z d copies)
      ((v.shelf.decisions v.sampler π v.depth v.phase v.temperature v.kind (v.failures.pass.apply m) i)[u.val]'(by simp)) :=
  (v.shelf.run v.sampler π v.depth hd v.phase v.temperature v.kind _ fixture incoming rom space).2.2.2 i u

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
