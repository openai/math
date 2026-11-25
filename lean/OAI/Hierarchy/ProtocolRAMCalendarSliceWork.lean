import OAI.Hierarchy.ProtocolRAMPaidSliceWork
import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices
import OAI.Hierarchy.TaggedWidePaidRun

namespace OAI
/-! # Billing every native paid-width clause in the actual calendar -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage RepairHistogram
open scoped Classical
variable {z d k q goods r edges : ℕ}

structure AttemptSliceWork (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ)
    (role : Expr) (ids : Fin goods→Expr) (tree core : Traversals) (u : ℕ) : Prop where
  direct : (p.labelSource sink idBase role ids).edge.work≤u
  mate : ∀a b,tree.catalystMate=some (a,b) → a.work≤u ∧ b.work≤u
  link : tree.edge.work≤u
  ball : tree.sourceRow.work≤u
  spill : core.edge.work≤u
  spillRow : core.sourceRow.work≤u

theorem AttemptSliceWork.issued {p : Format z d k q goods} {sink : Sink r edges} {idBase : ℕ}
    {role : Expr} {ids : Fin goods→Expr} {tree core : Traversals} {u : ℕ}
    (h : AttemptSliceWork p sink idBase role ids tree core u) (bits : ℕ) (bank : Bank)
    (s : PaidWidths.Slice) (used : s∈p.paidSlices sink idBase role ids tree core bits) :
    (pair (s.columns bank edges)).work≤PaidWidths.issueWork u bits := by
  have one:=PaidWidths.direct_work p.pricedArea p.stockSource (p.labelSource sink idBase role ids) bank edges u bits h.direct
  have two:=PaidWidths.tree_work p.pricedArea tree.positions tree.owner tree.parity bank tree.edge tree.sourceRow
    p.board.batch.copies edges u bits h.link h.ball
  have three:=PaidWidths.spill_work core.positions core.owner core.parity
    (PaidWidths.archivedBank (p.pricedArea.output+p.pricedArea.goods+p.pricedArea.goods) p.pricedArea.goods)
    bank core.edge core.sourceRow edges u bits h.spill h.spillRow
  cases field : tree.catalystMate with
  | none =>
    simp [Format.paidSlices,Format.mateSlices,field] at used
    rcases used with h|h|h
    · subst s;exact one
    · subst s;exact two
    · subst s;exact three
  | some operand =>
    obtain ⟨a,b⟩:=operand
    have both:=h.mate a b field
    have four:=PaidWidths.mate_work p.pricedArea p.stockSource a b bank edges u bits both.1 both.2
    simp [Format.paidSlices,Format.mateSlices,field] at used
    rcases used with h|h|h|h
    · subst s;exact one
    · subst s;exact four
    · subst s;exact two
    · subst s;exact three

theorem paid_issues_work (mesh : Mesh) (fmt : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (tree core : Attempt→Traversals) (boundary : Boundary → CommodityColumn→Traversals) (bits u : ℕ) (bank : Bank)
    (active : ∀a,.attempt a∈events mesh → AttemptSliceWork (fmt a) sink idBase (role a) (ids a) (tree a) (core a) u)
    (feed : ∀b,.feed b∈events mesh → ∀c∈feeds b,(boundary b c).edge.work≤u ∧ (boundary b c).sourceRow.work≤u) :
    ∀s∈paidSlices mesh fmt feeds sink idBase role ids tree core boundary bits,
      (pair (s.columns bank edges)).work≤PaidWidths.issueWork u bits := by
  intro s member
  obtain ⟨e,scheduled,printed⟩:=List.mem_flatMap.mp member
  cases e with
  | attempt a => exact (active a scheduled).issued bits bank s printed
  | feed b =>
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp printed
    have bounds:=feed b scheduled c hc
    exact PaidWidths.spill_work (boundary b c).positions (boundary b c).owner (boundary b c).parity
      (PaidWidths.archivedBank c.overflow c.rows) bank (boundary b c).edge (boundary b c).sourceRow edges u bits
      bounds.1 bounds.2

end Hierarchy.ProtocolRAM.Calendar
end

end OAI
