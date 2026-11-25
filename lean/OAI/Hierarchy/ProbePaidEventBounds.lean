import OAI.Hierarchy.ProbePaidOccupancy
import OAI.Hierarchy.ProtocolRAMCalendarFeedLayout

namespace OAI
/-! # Adding all three native repair charges and earlier overflows at every event -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe
open scoped BigOperators Fin.CommRing Classical
noncomputable section
variable {w h d k n q goods r edges : ℕ}

/-- The ordinary reporter adds one direct, at most one second-radius, one tree
and one early core-spill slice. These four caps are in native bit units of the
exact same physical row, with no cancellation between repeated edge labels. -/
theorem Format.per_row_bound (p : Format h d k q goods) (sink : Sink r edges) (idBase : ℕ)
    (role : Expr) (ids : Fin goods→Expr) (tree core : Traversals) (maxBits : ℕ) (m : Memory w) (e : Fin edges)
    (D T R A : ℕ)
    (direct : (PaidWidths.paidDirect p.pricedArea p.stockSource (p.labelSource sink idBase role ids)).load m e≤D)
    (mate : ∀ mask other,tree.catalystMate=some (mask,other) → (PaidWidths.paidMate p.pricedArea p.stockSource mask other).load m e≤D)
    (broadcast : (PaidWidths.paidBroadcast p.pricedArea tree.positions tree.owner tree.parity tree.edge tree.sourceRow p.board.batch.copies maxBits).load m e≤T)
    (overflow : (PaidWidths.paidSpill p.pricedArea core.positions core.owner core.parity core.edge core.sourceRow).load m e≤R)
    (aperture : 2*D+T+R≤A) : PaidWidths.total (p.paidSlices sink idBase role ids tree core maxBits) m e≤A := by
  cases eq : tree.catalystMate with
  | none => simpa [Format.paidSlices,Format.mateSlices,eq,PaidWidths.total] using
      (Nat.add_le_add direct (Nat.add_le_add broadcast overflow)).trans (by omega)
  | some t =>
    obtain ⟨mask,other⟩ := t
    have second := mate mask other eq
    simpa [Format.paidSlices,Format.mateSlices,eq,PaidWidths.total] using
      (Nat.add_le_add direct (Nat.add_le_add second (Nat.add_le_add broadcast overflow))).trans (by omega)

/-- On a boundary the physical program scans one column per actual commodity
lane. This bounds their overlaps at a public row with changing matching and
simultaneous outer/inner actions. -/
theorem boundary_per_row (L : FeedLayout h n k) (tape : CommodityColumn→Traversals) (m : Memory w)
    (cap : ℕ) (e : Fin edges) (bounded : ∀c∈L.columns,(c.paidSlice (tape c)).load m e≤cap) :
    PaidWidths.total (L.columns.map (fun c=>c.paidSlice (tape c))) m e≤FeedLayout.lanes n k*cap := by
  have scan (cols : List CommodityColumn) (within : ∀c∈cols,c∈L.columns) :
      PaidWidths.total (cols.map (fun c=>c.paidSlice (tape c))) m e≤cols.length*cap := by
    induction cols with
    | nil => simp [PaidWidths.total]
    | cons c cs ih =>
      have prior := ih (fun x hx=>within _ (by simp [hx]))
      have this := bounded c (within c (by simp))
      simpa only [List.map_cons,PaidWidths.total,List.sum_cons,List.length_cons,Nat.succ_mul,Nat.add_comm cap] using Nat.add_le_add this prior
  simpa [FeedLayout.columns] using scan L.columns (fun _ h=>h)

/-- Each checked prefix of the *actual* eventSlices array is bounded at each
physical row by the same public constant times the payload width. The coefficient
includes the real finite branch length and the real number of feed lanes. -/
theorem paid_event_prefix (mesh : Mesh) (format : Attempt→Format h d k q goods)
    (feeds : Boundary→FeedLayout h n k) (sink : Sink r edges) (idBase : ℕ) (role : Attempt→Expr)
    (ids : Attempt→Fin goods→Expr) (tree core : Attempt→Traversals) (boundary : Boundary → CommodityColumn→Traversals)
    (maxBits : ℕ) (m : Memory w) (e : Fin edges) (width directCap treeCap coreCap : ℕ)
    (direct : ∀ a,(PaidWidths.paidDirect (format a).pricedArea (format a).stockSource
      ((format a).labelSource sink idBase (role a) (ids a))).load m e≤directCap*width)
    (mate : ∀ a x y,(tree a).catalystMate=some (x,y) →
      (PaidWidths.paidMate (format a).pricedArea (format a).stockSource x y).load m e≤directCap*width)
    (broadcast : ∀ a,(PaidWidths.paidBroadcast (format a).pricedArea (tree a).positions (tree a).owner (tree a).parity
      (tree a).edge (tree a).sourceRow (format a).board.batch.copies maxBits).load m e≤treeCap*width)
    (spent : ∀ a,(PaidWidths.paidSpill (format a).pricedArea (core a).positions (core a).owner (core a).parity
      (core a).edge (core a).sourceRow).load m e≤coreCap*width)
    (pushed : ∀ b c,c∈(feeds b).columns → (c.paidSlice (boundary b c)).load m e≤coreCap*width) :
    let C := max (2*directCap+treeCap+coreCap) (FeedLayout.lanes n k*coreCap)
    let slices := eventSlices format (fun b=>(feeds b).columns) sink idBase role ids tree core boundary maxBits
    (∀ ev,PaidWidths.total (slices ev) m e≤C*width) ∧ ∀stop,
      PaidWidths.total (((events mesh).take stop).flatMap slices) m e≤
        ((mesh.inject+mesh.cool)*(mesh.outerFuel*(1+mesh.reserveSteps*(mesh.innerFuel+1))+1)*C)*width := by
  intro C slices
  have per (ev : Event) : PaidWidths.total (slices ev) m e≤C*width := by
    cases ev with
    | attempt a =>
      apply (format a).per_row_bound sink idBase (role a) (ids a) (tree a) (core a) maxBits m e _ _ _ _
        (direct a) (mate a) (broadcast a) (spent a)
      calc 2*(directCap*width)+(treeCap*width)+coreCap*width=(2*directCap+treeCap+coreCap)*width := by ring
           _ ≤ _ := Nat.mul_le_mul_right _ (le_max_left ..)
    | feed b =>
      calc
        _ ≤ FeedLayout.lanes n k * (coreCap * width) :=
          boundary_per_row (feeds b) (boundary b) m _ e (pushed b)
        _ = (FeedLayout.lanes n k * coreCap) * width := (Nat.mul_assoc ..).symm
        _ ≤ C * width := Nat.mul_le_mul_right width (le_max_right ..)
  exact ⟨per,fun stop=>paid_history_prefix mesh slices m e C width stop (fun t _=>per t)⟩


end
end Hierarchy.ProtocolRAM.Calendar

end OAI
