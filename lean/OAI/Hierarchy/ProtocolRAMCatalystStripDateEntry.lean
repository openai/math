import OAI.Hierarchy.ProbeCatalystCashEntry
import OAI.Hierarchy.ProtocolRAMCatalystChargedDates

namespace OAI
/-! # The physical paid strip input supplies its owner and posted debit at the same date -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM Calendar Calendar.StockCommit PurchaseStage RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical Fin.CommRing

variable {w q D count payload : ℕ}

namespace Date
variable {F : Type*} {A B C H : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype H] [Field F]
  {z d k N K sites : ℕ} [Nonempty (Fin sites)] [Nonempty (Fin k)] [Nonempty (Role C H (A⊕B) k)]
  {M ε tree : ℝ} {len : H→ℝ} {cap : A→ℝ}
variable {e : Role C H (A ⊕ B) k → Chord sites}
  {menu : Probe.FixedMenu F e
    (demand (I := C) (H := H) (k := k) (Sum.inl (α := A) (β := B)))
    ((fun y : A → ℝ => quote (I := C) (k := k) M len (LocalCommodity.extraPrice (B := B) y)) ''
      Set.Icc 0 cap)
    ε tree N}

/-- Build the dated receipt from the actual selector, released bit count, per-copy
prices and geometric owner. No room is assigned from a future attempted purchase. -/
def ofStrip (x : StripInput menu w z d q D) {R G : Type} {J : Type*} [Fintype J]
    (ballsAt : R ↪ Fin x.raw.market.rows) (columns : R×C ↪ G) (keys : G×Fin k ↪ Fin count)
    (idle : Fin count) (scale : 0<K) (stock : x.Addresses) (catalogue : PacketWidths J)
    (includeMenu : menu.index→J) (widths : ∀i,catalogue.width (includeMenu i)=(menu.packet i).width)
    (mass : x.board.copies=catalogue.copiesAt K payload) (chart : Chart w q D)
    (event : Attempt) (before : Memory w) (owner : Expr) (labels : LabelSource)
    (commit : chart.commit event=pricedSegment x.form.pricedArea x.form.stockSource labels w x.ballot)
    (ready : Calendar.ready chart (.attempt event) before) (room : EventBoard (fresh x.form.pricedArea x.form.stockSource) w)
    (snapshot : x.mem=stageInput x.form.pricedArea x.form.stockSource labels
      (postOutput (chart.layout event) (repair chart event) (prepared chart event before)))
    (covered : ∀j,j∈liveRows x.ballot x.mem x.raw.market.rows→∃r,ballsAt r=j)
    (read : ∀v,owner.eval before ((finProdFinEquiv (portCell ballsAt x.ports v)).val:Word w)=
      ((keys (physical columns v)).val:Word w)) :
    Date chart event before owner (x.form.pricedArea.direct+x.form.occurrences)
      (x.raw.market.rows*D) count payload :=
  Date.of_priced chart event before x.form.pricedArea x.form.stockSource labels x.ballot commit ready room
    x.mem snapshot x.plan (fun _=>rfl) ballsAt x.ports columns keys idle scale (fun r=>x.nominal (ballsAt r))
    (fun r=>x.nominal_copies catalogue includeMenu widths mass scale (ballsAt r))
    (fun r live c axis=>(x.actual stock (ballsAt r) live (.catalyst c axis)).le.trans
      (Nat.mul_le_mul_left _ (x.rate_le (ballsAt r))))
    (fun j hit=>positive_cell x.plan ballsAt x.ports covered (fun j=>x.ballot.copies*x.rate j)
      (fun j live=>x.actual stock j live) x.padding j hit) owner read

end Date

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
