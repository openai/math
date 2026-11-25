import OAI.Hierarchy.ProtocolRAMCalendarPaidReporter
import OAI.Hierarchy.ProtocolRAMCalendarPriced

namespace OAI
/-! # Deriving the paid occurrence list from the exact installed calendar -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native
open scoped BigOperators Fin.CommRing
noncomputable section
variable {z d k q goods r edges W : ℕ}

/-- Physical positions on a priced walk, addressed by its owner or commodity row.
The forest, core, and boundary data may depend on the matching through `edge`. -/
structure Traversals where
  positions : ℕ
  owner : Bank
  parity : Bank
  edge : Expr
  sourceRow : Expr
  catalystMate : Option (Expr×Expr) := none

/-- A catalyst width is immediately routed on both M-length radii through the
column center. The first hop uses the primary direct edge ID. -/
def Format.mateSlices (p : Format z d k q goods) (tree : Traversals) : List PaidWidths.Slice :=
  tree.catalystMate.toList.map fun t=>PaidWidths.paidMate p.pricedArea p.stockSource t.1 t.2

/-- All three kinds of earlier paid widths are recovered even if their physical
edge sets overlap. Ordinary installations and the terminal fee use the same source
of original common edge IDs. -/
def Format.paidSlices (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ) (role : Expr)
    (ids : Fin goods→Expr) (tree core : Traversals) (maxBroadcastBits : ℕ) : List PaidWidths.Slice :=
  [PaidWidths.paidDirect p.pricedArea p.stockSource (p.labelSource sink idBase role ids)] ++ p.mateSlices tree ++
   [PaidWidths.paidBroadcast p.pricedArea tree.positions tree.owner tree.parity tree.edge tree.sourceRow p.board.batch.copies maxBroadcastBits,
   PaidWidths.paidSpill p.pricedArea core.positions core.owner core.parity core.edge core.sourceRow]

def CommodityColumn.paidSlice (c : CommodityColumn) (path : Traversals) : PaidWidths.Slice :=
  PaidWidths.spill path.positions path.owner path.parity (PaidWidths.archivedBank c.overflow c.rows) path.edge path.sourceRow

/-- A concrete source list for `paidReporter`. The actual calendar determines its
order, all timestamped archive addresses, the physical geometry, and the copies count.
When a guarded repair or reserve feed is inactive, it contributes its stored zero. -/
def eventSlices (format : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (tree core : Attempt→Traversals) (boundary : Boundary → CommodityColumn→Traversals) (maxBroadcastBits : ℕ) :
    Event→List PaidWidths.Slice
  | .attempt a => (format a).paidSlices sink idBase (role a) (ids a) (tree a) (core a) maxBroadcastBits
  | .feed b => (feeds b).map (fun c=>c.paidSlice (boundary b c))

def paidSlices (mesh : Mesh) (format : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (tree core : Attempt→Traversals) (boundary : Boundary → CommodityColumn→Traversals) (maxBroadcastBits : ℕ) :=
  (events mesh).flatMap (eventSlices format feeds sink idBase role ids tree core boundary maxBroadcastBits)

theorem installed_load (mesh : Mesh) (format : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (tree core : Attempt→Traversals) (boundary : Boundary → CommodityColumn→Traversals) (maxBroadcastBits : ℕ)
    (m : Memory W) (e : Fin edges) :
    PaidWidths.total (paidSlices mesh format feeds sink idBase role ids tree core boundary maxBroadcastBits) m e=
      ((events mesh).map (fun ev=>PaidWidths.total
        (eventSlices format feeds sink idBase role ids tree core boundary maxBroadcastBits ev) m e)).sum := by
  let compile := eventSlices format feeds sink idBase role ids tree core boundary maxBroadcastBits
  show PaidWidths.total ((events mesh).flatMap compile) m e=((events mesh).map (fun ev=>PaidWidths.total (compile ev) m e)).sum
  generalize events mesh=xs
  induction xs with
  | nil => rfl
  | cons ev xs ih =>
    simpa only [List.flatMap_cons,List.map_cons,List.sum_cons,PaidWidths.total,List.map_append,List.sum_append] using
      (congrArg (fun n => PaidWidths.total (compile ev) m e + n) ih)

/-- The actual port/tile words in a walk-position table. No toll or load is part
of this readback: both are derived by summing the physical positions. -/
def Traversals.Reads (t : Traversals) (m : Memory W) {rows : ℕ} (walk : Fin rows→List (Fin edges)) : Prop :=
  ∃ enum : Fin t.positions≃(Σ j,Fin (walk j).length),
    (∀ i,(t.edge.eval m (i.val:Word W)).val=((walk (enum i).1)[(enum i).2.val]'(enum i).2.isLt).val) ∧
    ∀ i,(t.sourceRow.eval m (i.val:Word W)).val=(enum i).1.val

namespace Traversals.Reads

variable {t : Traversals} {m : Memory W} {rows : ℕ} {walk : Fin rows→List (Fin edges)}

/-- Fix one enumeration witnessing the two physical word reads. -/
noncomputable def enum (read : t.Reads m walk) : Fin t.positions≃(Σ j,Fin (walk j).length) :=
  Classical.choose read

theorem edgeAt (read : t.Reads m walk) (i : Fin t.positions) :
    (t.edge.eval m (i.val:Word W)).val=((walk (read.enum i).1)[(read.enum i).2.val]'(read.enum i).2.isLt).val :=
  (Classical.choose_spec read).1 i

theorem ownerAt (read : t.Reads m walk) (i : Fin t.positions) :
    (t.sourceRow.eval m (i.val:Word W)).val=(read.enum i).1.val :=
  (Classical.choose_spec read).2 i

end Traversals.Reads

theorem Format.direct_toll (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ) (role : Expr) (ids : Fin goods→Expr)
    (m : Memory W) (len : Fin edges→ℝ) (payload : ℕ) (physical : Fin p.occurrences → Fin edges) (width : p.occurrences≤2^W)
    (ordinal : ∀ i,((p.labelSource sink idBase role ids).edge.eval m (i.val:Word W)).val=(physical i).val) :
    (PaidWidths.paidDirect p.pricedArea p.stockSource (p.labelSource sink idBase role ids)).toll m len payload=
      (∑ i : Fin p.occurrences,((m (p.pricedArea.direct+i.val)).val:ℝ)*len (physical i))/payload := by
  let s := PaidWidths.paidDirect p.pricedArea p.stockSource (p.labelSource sink idBase role ids)
  refine (PaidWidths.physical_toll s m len payload physical ordinal).trans ?_
  change (∑ i : Fin p.occurrences, ((s.amount.eval m (i.val : Word W)).val:ℝ)*len (physical i))/payload = _
  apply congrArg (fun x : ℝ => x/payload)
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun n : ℕ => (n:ℝ)*len (physical i))
    (PaidWidths.paidDirect_bits p.pricedArea p.stockSource (p.labelSource sink idBase role ids) m i width)

theorem Format.visible_direct_toll (p : Format z d k q goods) (sink : Sink r edges) (idBase : ℕ) (role : Expr) (ids : Fin goods→Expr)
    (m : Memory W) (len : Fin edges→ℝ) (payload : ℕ) (price : Fin p.occurrences → ℝ) (width : p.occurrences≤2^W)
    (hit : ∀ i : Fin p.occurrences,(m (p.pricedArea.direct+i.val)).val≠0 → ∃ e : Fin edges,
      ((p.labelSource sink idBase role ids).edge.eval m (i.val:Word W)).val=e.val ∧ len e=price i) :
    (PaidWidths.paidDirect p.pricedArea p.stockSource (p.labelSource sink idBase role ids)).toll m len payload=
      (∑ i : Fin p.occurrences,((m (p.pricedArea.direct+i.val)).val:ℝ)*price i)/payload := by
  let s := PaidWidths.paidDirect p.pricedArea p.stockSource (p.labelSource sink idBase role ids)
  have read (i : Fin p.occurrences) : (s.amount.eval m (i.val:Word W)).val=(m (p.pricedArea.direct+i.val)).val :=
    PaidWidths.paidDirect_bits p.pricedArea p.stockSource (p.labelSource sink idBase role ids) m i width
  have found (i : Fin s.count) (active : (s.amount.eval m (i.val:Word W)).val≠0) :
      ∃ e : Fin edges, (s.edge.eval m (i.val:Word W)).val=e.val ∧ len e=price i := by
    change Fin p.occurrences at i
    exact hit i (fun zero => active ((read i).trans zero))
  refine (PaidWidths.visible_toll s m len payload price found).trans ?_
  change (∑ i : Fin p.occurrences, ((s.amount.eval m (i.val : Word W)).val:ℝ)*price i)/payload = _
  apply congrArg (fun x : ℝ => x/payload)
  apply Finset.sum_congr rfl
  exact fun i _ => congrArg (fun n : ℕ => (n:ℝ)*price i) (read i)

/-- The stored positive direct width is used a second time on the opposite
radius exactly on actual catalyst roles. Its price is that of the second
radius. The inactive branch neither allocates width nor requests a price. -/
theorem Format.mate_toll (p : Format z d k q goods) (forest : Traversals) (mask second : Expr)
    (m : Memory W) (len : Fin edges→ℝ) (M : ℝ) (payload : ℕ) (width : p.occurrences≤2^W)
    (entry : forest.catalystMate=some (mask,second))
    (hit : ∀ i : Fin p.occurrences,mask.eval m (i.val:Word W)≠0 → (m (p.pricedArea.direct+i.val)).val≠0 →
      ∃ e : Fin edges,(second.eval m (i.val:Word W)).val=e.val ∧ len e=M) :
    ((p.mateSlices forest).map (fun s=>s.toll m len payload)).sum=
      (∑ i : Fin p.occurrences,((m (p.pricedArea.direct+i.val)).val:ℝ)*
        (if mask.eval m (i.val:Word W)=0 then 0 else M))/payload := by
  let s:=PaidWidths.paidMate p.pricedArea p.stockSource mask second
  have read (i : Fin p.occurrences) := PaidWidths.paidMate_bits p.pricedArea p.stockSource mask second m i width
  have found (i : Fin s.count) (on : (s.amount.eval m (i.val:Word W)).val≠0) :
      ∃ e : Fin edges,(s.edge.eval m (i.val:Word W)).val=e.val ∧ len e=M := by
    have v := read i
    change (s.amount.eval m (i.val:Word W)).val=_ at v
    rw [v] at on
    by_cases off : mask.eval m (i.val:Word W)=0
    · simp [off] at on
    · exact hit i off (by simpa [off] using on)
  simp only [mateSlices,entry,Option.toList_some,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
  rw [PaidWidths.visible_toll s m len payload (fun _=>M) found]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [read i]
  split_ifs <;> simp

theorem Traversals.broadcast_toll (t : Traversals) (a : StockCommit.Area) (m : Memory W) (payload copies maxBits : ℕ)
    (len : Fin edges→ℝ) (tree : Fin a.rows→List (Fin edges)) (h : t.Reads m tree)
    (size : maxBits<2^W) (copyFits : copies<2^W) (bound : ∀ j : Fin a.rows,(m (a.broadcast+j.val)).val≤ maxBits)
    (full : ∀ j : Fin a.rows,copies*(m (a.broadcast+j.val)).val<2^W) :
    (PaidWidths.paidBroadcast a t.positions t.owner t.parity t.edge t.sourceRow copies maxBits).toll m len payload=
      ∑ j : Fin a.rows,((tree j).map len).sum*((copies*(m (a.broadcast+j.val)).val:ℕ):ℝ)/payload := by
  let bits := fun j : Fin a.rows=>copies*(m (a.broadcast+j.val)).val
  rw [PaidWidths.walks_toll _ m len payload tree bits h.enum h.edgeAt (fun i=>
    PaidWidths.paidBroadcast_bits a t.positions t.owner t.parity t.edge t.sourceRow copies maxBits m (i.val:Word W) (h.enum i).1
      (h.ownerAt i) size (bound _) copyFits (full _))]
  exact Finset.sum_congr rfl (fun j _=>by dsimp [bits];ring)

theorem Traversals.spill_toll (t : Traversals) (a : StockCommit.Area) (m : Memory W) (payload : ℕ) (len : Fin edges→ℝ)
    (core : Fin a.goods→List (Fin edges)) (h : t.Reads m core) :
    (PaidWidths.paidSpill a t.positions t.owner t.parity t.edge t.sourceRow).toll m len payload=
      ∑ j : Fin a.goods,((core j).map len).sum*((m (a.output+a.goods+a.goods+j.val)).val/payload:ℝ) := by
  apply PaidWidths.walks_toll _ m len payload core (fun j=>(m (a.output+a.goods+a.goods+j.val)).val) h.enum h.edgeAt
  exact fun i=> congrArg Fin.val (PaidWidths.paidSpill_bits a t.positions t.owner t.parity t.edge t.sourceRow m (i.val:Word W) (h.enum i).1 (h.ownerAt i))

theorem Traversals.boundary_toll (t : Traversals) (c : CommodityColumn) (m : Memory W) (payload : ℕ) (len : Fin edges→ℝ)
    (walk : Fin c.rows→List (Fin edges)) (h : t.Reads m walk) :
    (c.paidSlice t).toll m len payload=∑ j : Fin c.rows,((walk j).map len).sum*((m (c.overflow+j.val)).val/payload:ℝ) := by
  apply PaidWidths.walks_toll _ m len payload walk (fun j=>(m (c.overflow+j.val)).val) h.enum h.edgeAt
  intro i
  let saved := PaidWidths.archivedBank c.overflow c.rows
  have enough : c.rows≤ saved.size := (ProtocolRAMPurchaseSampler.lt_span _).le
  change (saved.read m (t.sourceRow.eval m (i.val:Word W))).val=_
  change (m (saved.base + (t.sourceRow.eval m (i.val:Word W)).val % saved.size)).val = _
  rw [h.ownerAt i, Nat.mod_eq_of_lt ((h.enum i).1.isLt.trans_le enough)]
  rfl

theorem toll_from_history (mesh : Mesh) (format : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn)
    (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (tree core : Attempt→Traversals) (boundary : Boundary → CommodityColumn→Traversals) (maxBroadcastBits : ℕ)
    (m : Memory W) (len : Fin edges→ℝ) (payload : ℕ) :
    (∑ e : Fin edges,len e*((PaidWidths.total (paidSlices mesh format feeds sink idBase role ids tree core boundary maxBroadcastBits) m e:ℝ)/payload))=
      ((events mesh).map (fun ev=> ((eventSlices format feeds sink idBase role ids tree core boundary maxBroadcastBits ev).map
        (fun slice=>slice.toll m len payload)).sum)).sum := by
  rw [PaidWidths.total_toll]
  let compile := eventSlices format feeds sink idBase role ids tree core boundary maxBroadcastBits
  change (((events mesh).flatMap compile).map (fun s=>s.toll m len payload)).sum=_
  generalize events mesh=xs
  induction xs with
  | nil => rfl
  | cons ev xs ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih,compile]

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
