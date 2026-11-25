import OAI.Hierarchy.ProtocolRAMNativeFormat
import OAI.Hierarchy.ProtocolRAMCalendarPostLayout
import OAI.Hierarchy.ProtocolRAMCalendarCommitLayout
import OAI.Hierarchy.ProtocolRAMCalendarBill

namespace OAI
/-! # Placing one actual frozen purchase, histogram receipt and signed commodity update -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseStage
open scoped Classical Fin.CommRing
noncomputable section

variable {z d k q goods : ℕ}

/-- The complete procedure has no caller-supplied instruction sequence or transition.
The market, post and signed commit addresses are calculated in their actual write order. -/
def installed (c : Mesh) (finish : ℝ) (prices : PhasePrice) (layout : Attempt→Format z d k q goods)
    (feeds : Boundary→List CommodityColumn) : Chart (wordBits z d copies) q goods :=
  chartWith c (fun a=>(layout a).board.modeOut) (fun a=>(layout a).testsStart)
    (fun a=>(layout a).atTime c finish prices a)
    (fun a b=>StockCommit.freshSegment (layout a).area (layout a).stockSource _ b)
    (fun a=>(layout a).board) feeds

/-- The extent and snapshots checked by calendar.run_exec use the post area's actual
published mode and never an independently chosen selector-controlled decision. -/
@[simp] theorem installed_mode (c : Mesh) (finish : ℝ) (prices : PhasePrice)
    (s : Attempt→Format z d k q goods) (feeds) (a : Attempt) :
    (repair (installed c finish prices s feeds) a).modeOut=(s a).board.modeOut := rfl

@[simp] theorem installed_stock_source (p : Format z d k q goods) :
    p.stockSource.old.base=p.market.shelf.stockBase := rfl

theorem Format.public_board (p : Format z d k q goods) (w : ℕ)
    (readers : ∀ b∈writes p.market.layout p.board,b.term.inputEnd≤p.board.keys)
    (key : p.board.keys<2^w) : Board p.market.layout p.board w :=
  PostLayout.board p.market.layout p.checkedBoard p.maskStart p.indexBits w readers key

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
