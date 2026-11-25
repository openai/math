import OAI.Hierarchy.ProtocolRAMMarketPrefixExec
import OAI.Hierarchy.ProtocolRAMNativeFormat
import OAI.Hierarchy.ProtocolRAMNativePriceLabels
import OAI.Hierarchy.ProtocolRAMSinkData

namespace OAI
/-! # The physical chronological chart with a native signed-stock commit -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseStage
noncomputable section
variable {z d k r edges : ℕ}

def chartWith {q goods : ℕ} (c : Mesh) (modeAt stopAt : Attempt→ℕ) (market : Attempt→Market z d k)
    (commit : Attempt→Batch q goods → Commit (wordBits z d copies))
    (boards : Attempt→PurchaseStage.Repair q goods) (columns : Boundary→List CommodityColumn) :
    Chart (wordBits z d copies) q goods :=
  let B := fun a=>testedBoard (market a).failures (boards a)
  ⟨c,modeAt,stopAt,fun a=>(market a).prefix,
    fun a=>commit a (PurchaseStage.enabledBatch (market a).layout (B a)),
    B,fun a=>(market a).layout,columns⟩

variable {q goods : ℕ}

/-- The same reporter geometry used at terminal settlement is the sole source of
the length code. Its row is resolved from the runtime declared common link ID. -/
def Format.labelSource (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ)
    (role : Expr) (ids : Fin goods→Expr) :=
  StockCommit.LabelSource.fromPorts p.labelStart idBase sink.geometry role ids

def Format.pricedCommit (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ)
    (role : Expr) (ids : Fin goods→Expr) (b : Batch q goods) : Commit (wordBits z d copies) :=
  StockCommit.pricedSegment p.pricedArea p.stockSource (p.labelSource sink idBase role ids) _ b

def pricedInstalled (c : Mesh) (finish : ℝ) (prices : PhasePrice) (format : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) : Chart (wordBits z d copies) q goods :=
  chartWith c (fun a=>(format a).board.modeOut) (fun a=>(format a).testsStart)
    (fun a=>(format a).atTime c finish prices a)
    (fun a b=>(format a).pricedCommit sink idBase (role a) (ids a) b)
    (fun a=>(format a).board) feeds

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
