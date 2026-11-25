import OAI.Hierarchy.ProbeFixedPaidDirectCells
import OAI.Hierarchy.ProbeFixedPaidEconomicRows
import OAI.Hierarchy.ProbePaidEventBounds

namespace OAI
/-! # The five charged components of each original paid event -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockCommit StockBound
open CatalystArchive PurchaseStage RepairHistogram
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
set_option quotPrecheck false
local notation "w" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "A" => v.privateArena P z width
local notation "fmt" => v.nativeFormats P z width
local notation "gs" => v.stamp P z width r banks src tab dst owners
local notation "tr" => v.nativeTrees P z width

private theorem count_le_stop (h : PortHeader) : h.count≤h.stop := by
  have bound:=ProtocolRAMPurchaseSampler.lt_span (2*h.count)
  change h.count≤h.parity.base+ProtocolRAMPurchaseSampler.span (2*h.count)
  omega

set_option maxHeartbeats 1200000 in
/-- Cost on an arbitrary physical edge. Every direct role, mate and broadcast
is bounded even if all of its labels coincide on that edge. -/
theorem paid_attempt_ceiling {n edges : ℕ} (a : Attempt) (mem entry : Memory w) (prior tail : List Event)
    (cut : Slot C mem (.attempt a) prior tail entry)
    (layout : TrialLayout C a (fmt a).pricedArea (fmt a).stockSource (gs a) v.keepLimit width
      ((A).base v.mesh (.attempt a)))
    (age : v.stripHeight≤z) (small : width≤2^z) (space : (A).endAddress v.mesh<2^w)
    (sink : Sink n edges) (idBase : ℕ) (role : Expr)
    (ids : Fin (max (Fintype.card (StripDirectory.PayloadRole (CoreBoard.Stages z (2^v.W)) k))
      (Fintype.card (StripDirectory.PurchasedRole v.depth k)))→Expr) (core : Traversals) (bits K : ℕ) (e : Fin edges)
    (spill : (PaidWidths.paidSpill (fmt a).pricedArea core.positions core.owner core.parity core.edge core.sourceRow).load
      (checkedOut C ((A).endAddress v.mesh) mem) e≤K*width) :
    PaidWidths.total ((fmt a).paidSlices sink idBase role ids (tr a) core bits)
      (checkedOut C ((A).endAddress v.mesh) mem) e≤((A).first*(2*v.menu.maximum+bits)+K)*width := by
  let f:=fmt a
  let out:=checkedOut C ((A).endAddress v.mesh) mem
  have alive : Event.attempt a∈events v.mesh := by
    change Event.attempt a∈events (C).mesh
    rw [cut.events]
    simp
  obtain ⟨⟨_,_,occ,low⟩,⟨_,_,trials,top⟩⟩:=v.paid_economic_headers P z width a alive
  have occurrences : f.pricedArea.occurrences≤(A).first:=occ.le.trans ((count_le_stop _).trans low)
  have tree : (tr a).positions≤(A).first:=trials.le.trans ((count_le_stop _).trans top)
  have cap : f.pricedArea.occurrences≤2^w:=occurrences.trans ((Nat.le_add_right _ _).trans space.le)
  have cells:=v.paid_direct_cell P z width r banks src tab dst owners a mem entry prior tail cut layout age small
  have copies : f.board.batch.copies≤width :=
    (v.ordinary_dimensions P z width a).2.le.trans (Nat.div_le_self ..)
  let D:=(A).first*(v.menu.maximum*width)
  let T:=(A).first*(bits*width)
  apply f.per_row_bound sink idBase role ids (tr a) core bits out e D T (K*width) _
  · refine (PaidWidths.Slice.load_le_cells _ _ _ (v.menu.maximum*width) ?_).trans (Nat.mul_le_mul_right _ occurrences)
    intro i
    rw [PaidWidths.paidDirect_bits _ _ _ out i cap]
    exact cells i
  · intro mask other _
    refine (PaidWidths.Slice.load_le_cells _ _ _ (v.menu.maximum*width) ?_).trans (Nat.mul_le_mul_right _ occurrences)
    intro i
    rw [PaidWidths.paidMate_bits _ _ _ _ out i cap]
    split <;> first | exact cells i | exact Nat.zero_le _
  · exact (PaidWidths.broadcast_load_bound _ _ _ _ _ _ _ _ _ _).trans
      (Nat.mul_le_mul tree (Nat.mul_le_mul_left _ copies))
  · exact spill
  · dsimp only [D,T]
    exact le_of_eq (by ring)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
