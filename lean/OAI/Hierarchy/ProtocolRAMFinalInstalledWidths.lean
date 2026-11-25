import OAI.Hierarchy.ProtocolRAMPaidWidthCore
import OAI.Hierarchy.ProtocolRAMReportedChargeKeys
import OAI.Hierarchy.ProtocolRAMCalendarDepletedSink

namespace OAI
/-! # Native aggregation of all paid installed widths on the physical edge bank -/

noncomputable section
namespace Hierarchy.ProtocolRAM.PaidWidths
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram Calendar.StockCommit
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical
variable {W edges : ℕ}

/-- Actual paid physical link credits. The same occurrence edge expression archives
its toll in `pricedSegment`. Catalyst uses are carried by the separate `ReserveUse`. -/
def direct (a : Area) (h : Sources) (g : LabelSource) (saved : Bank) : Slice :=
  ⟨a.occurrences,h.owner,h.parity,g.edge,.lookup saved .row⟩

/-- One row per actual tree-edge traversal. The selector width lives in the original
broadcast bank. The bound covers the number of selector bits of the finite menu. -/
def broadcast (n : ℕ) (owner parity saved : Bank) (edge ball : Expr) (copies maxBits : ℕ) : Slice :=
  ⟨n,owner,parity,edge,boundedMul maxBits (.lit copies) (.lookup saved ball)⟩

/-- Paid overflow routing on the core, including scheduled time/feed boundaries.
Each occupied path position is a separate occurrence, including repeated edges. -/
def spill (n : ℕ) (owner parity saved : Bank) (edge commodity : Expr) : Slice :=
  ⟨n,owner,parity,edge,.lookup saved commodity⟩

def archivedBank (base rows : ℕ) : Bank := ⟨base,ProtocolRAMPurchaseSampler.bits rows⟩

def paidDirect (a : Area) (s : Sources) (g : LabelSource) : Slice :=
  direct a s g (archivedBank a.direct a.occurrences)

def paidBroadcast (a : Area) (n : ℕ) (owner parity : Bank) (edge ball : Expr) (copies maxBits : ℕ) : Slice :=
  broadcast n owner parity (archivedBank a.broadcast a.rows) edge ball copies maxBits

def paidSpill (a : Area) (n : ℕ) (owner parity : Bank) (edge commodity : Expr) : Slice :=
  spill n owner parity (archivedBank (a.output+a.goods+a.goods) a.goods) edge commodity

/-- The opposite endpoint of a catalyst installation uses a *second* radial
hop of the same width. For all other direct roles this slice carries zero. -/
def paidMate (a : Area) (s : Sources) (catalyst secondRadius : Expr) : Slice :=
  ⟨a.occurrences,s.owner,s.parity,secondRadius,
    .branch .eq catalyst (.lit 0) (.lit 0) (.lookup (archivedBank a.direct a.occurrences) .row)⟩

theorem direct_bits (a : Area) (h : Sources) (g : LabelSource) (saved : Bank) (m : Memory W)
    (i : Fin a.occurrences) (base : saved.base=a.direct) (wide : a.occurrences≤2^W) (fit : a.occurrences≤ saved.size) :
    ((direct a h g saved).amount.eval m (i.val:Word W)).val=(m (a.direct+i.val)).val := by
  simp only [direct,Expr.eval,Bank.read,Fin.val_cast_of_lt (i.isLt.trans_le wide),Nat.mod_eq_of_lt (i.isLt.trans_le fit),base]

theorem broadcast_bits (n : ℕ) (owner parity saved : Bank) (edge ball : Expr) (copies maxBits : ℕ) (m : Memory W)
    (r : Word W) (bound : (saved.read m (ball.eval m r)).val≤ maxBits) (room : maxBits<2^W) (copyFit : copies<2^W)
    (full : copies*(saved.read m (ball.eval m r)).val<2^W) :
    ((broadcast n owner parity saved edge ball copies maxBits).amount.eval m r).val=copies*(saved.read m (ball.eval m r)).val := by
  rw [broadcast,eval_boundedMul m r _ _ _ bound room]
  change ((copies:Word W)*(saved.read m (ball.eval m r))).val=_
  rw [Fin.val_mul,Fin.val_cast_of_lt copyFit,Nat.mod_eq_of_lt full]

theorem spill_bits (n : ℕ) (owner parity saved : Bank) (edge commodity : Expr) (m : Memory W) (r : Word W) :
    (spill n owner parity saved edge commodity).amount.eval m r=saved.read m (commodity.eval m r) := rfl

theorem paidDirect_bits (a : Area) (s : Sources) (g : LabelSource) (m : Memory W) (i : Fin a.occurrences)
    (wide : a.occurrences≤2^W) : ((paidDirect a s g).amount.eval m (i.val:Word W)).val=(m (a.direct+i.val)).val :=
  direct_bits a s g (archivedBank a.direct a.occurrences) m i rfl wide (ProtocolRAMPurchaseSampler.lt_span _).le

theorem paidMate_bits (a : Area) (s : Sources) (isCatalyst secondRadius : Expr)
    (m : Memory W) (i : Fin a.occurrences) (wide : a.occurrences≤2^W) :
    ((paidMate a s isCatalyst secondRadius).amount.eval m (i.val:Word W)).val =
      if isCatalyst.eval m (i.val:Word W)=0 then 0 else (m (a.direct+i.val)).val := by
  have fits : a.occurrences≤(archivedBank a.direct a.occurrences).size := (ProtocolRAMPurchaseSampler.lt_span _).le
  by_cases off : isCatalyst.eval m (i.val:Word W)=0
  · simp [paidMate,Expr.eval,ThreeFlat.RAM.DescriptorExpr.Comparison.test,off]
  · simp only [paidMate,Expr.eval,ThreeFlat.RAM.DescriptorExpr.Comparison.test,beq_iff_eq,off,
      Nat.cast_zero,ite_false,Bank.read,Fin.val_cast_of_lt (i.isLt.trans_le wide)]
    rw [Nat.mod_eq_of_lt (i.isLt.trans_le fits)]
    rfl

theorem paidBroadcast_bits (a : Area) (n : ℕ) (owner parity : Bank) (edge ball : Expr) (copies maxBits : ℕ)
    (m : Memory W) (r : Word W) (j : Fin a.rows) (index : (ball.eval m r).val=j.val)
    (size : maxBits<2^W) (bounded : (m (a.broadcast+j.val)).val≤ maxBits) (copyFit : copies<2^W)
    (full : copies*(m (a.broadcast+j.val)).val<2^W) : ((paidBroadcast a n owner parity edge ball copies maxBits).amount.eval m r).val=
      copies*(m (a.broadcast+j.val)).val := by
  let b := archivedBank a.broadcast a.rows
  have enough : a.rows≤b.size := (ProtocolRAMPurchaseSampler.lt_span _).le
  have old : b.read m (ball.eval m r)=m (a.broadcast+j.val) := by
    rw [Bank.read,index,Nat.mod_eq_of_lt (j.isLt.trans_le enough)]
    rfl
  exact (broadcast_bits n owner parity b edge ball copies maxBits m r (by rwa [old]) size copyFit (by rwa [old])).trans (by rw [old])

theorem paidSpill_bits (a : Area) (n : ℕ) (owner parity : Bank) (edge commodity : Expr) (m : Memory W) (r : Word W)
    (j : Fin a.goods) (index : (commodity.eval m r).val=j.val) : (paidSpill a n owner parity edge commodity).amount.eval m r=
      m (a.output+a.goods+a.goods+j.val) := by
  let b := archivedBank (a.output+a.goods+a.goods) a.goods
  have enough : a.goods≤b.size := (ProtocolRAMPurchaseSampler.lt_span _).le
  change b.read m (commodity.eval m r)=_
  rw [Bank.read,index,Nat.mod_eq_of_lt (j.isLt.trans_le enough)]
  rfl

end Hierarchy.ProtocolRAM.PaidWidths

end
end OAI
