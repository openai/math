import OAI.Hierarchy.ProtocolRAMCalendarFeedCharge

namespace OAI
/-! # The exact paid occurrences for one clipped or fed inventory -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {W h N k edges : ℕ}

theorem Traversals.spill_load (t : Traversals) (a : StockCommit.Area) (m : Memory W) (e : Fin edges)
    (core : Fin a.goods→List (Fin edges)) (h : t.Reads m core) :
    (PaidWidths.paidSpill a t.positions t.owner t.parity t.edge t.sourceRow).load m e=
      routeLoad core (fun j=>(m (a.output+a.goods+a.goods+j.val)).val) e := by
  apply PaidWidths.walks_load _ m e core (fun j=>(m (a.output+a.goods+a.goods+j.val)).val) h.enum h.edgeAt
  exact fun i=> congrArg Fin.val (PaidWidths.paidSpill_bits a t.positions t.owner t.parity t.edge t.sourceRow m (i.val:Word W) (h.enum i).1 (h.ownerAt i))

theorem Traversals.boundary_load (t : Traversals) (c : CommodityColumn) (m : Memory W) (e : Fin edges)
    (walk : Fin c.rows→List (Fin edges)) (h : t.Reads m walk) :
    (c.paidSlice t).load m e=
      routeLoad walk (fun j=>(m (c.overflow+j.val)).val) e := by
  apply PaidWidths.walks_load _ m e walk (fun j=>(m (c.overflow+j.val)).val) h.enum h.edgeAt
  intro i
  let saved := PaidWidths.archivedBank c.overflow c.rows
  have enough : c.rows≤ saved.size := (ProtocolRAMPurchaseSampler.lt_span _).le
  change (saved.read m (t.sourceRow.eval m (i.val:Word W))).val=_
  simp only [Bank.read,h.ownerAt i]
  change (m (c.overflow+(h.enum i).1.val % saved.size)).val=(m (c.overflow+(h.enum i).1.val)).val
  rw [Nat.mod_eq_of_lt ((h.enum i).1.isLt.trans_le enough)]


theorem FeedLayout.installed_load (L : FeedLayout h N k) (paths : CommodityColumn→Traversals)
    (m : Memory W) (e : Fin edges) (walk : Fin (lanes N k*2^h)→List (Fin edges))
    (reads : ∀l : Fin (lanes N k),(paths (L.column l)).Reads m
      (fun i : Fin (2^h)=>walk (finProdFinEquiv (l,i)))) :
    PaidWidths.total (L.columns.map (fun c=>c.paidSlice (paths c))) m e=
      routeLoad walk (fun i=>(m (L.overflow+i.val)).val) e := by
  let charge (i : Fin (lanes N k*2^h)) := (walk i).count e*(m (L.overflow+i.val)).val
  have piece (l : Fin (lanes N k)) :
      ((L.column l).paidSlice (paths (L.column l))).load m e=
        ∑i : Fin (2^h),charge (finProdFinEquiv (l,i)) := by
    rw [(paths (L.column l)).boundary_load (L.column l) m e _ (reads l)]
    apply Finset.sum_congr rfl
    intro i _
    change _*(m (L.overflow+l.val*2^h+i.val)).val=
      _*(m (L.overflow+(i.val+2^h*l.val))).val
    rw [show L.overflow+(i.val+2^h*l.val)=L.overflow+l.val*2^h+i.val by
      rw [Nat.mul_comm (2^h)];omega]
  change _=∑i,charge i
  rw [←finProdFinEquiv.sum_comp charge,Fintype.sum_prod_type]
  simp only [PaidWidths.total,columns,List.finRange,List.map_ofFn,Function.comp_def,List.sum_ofFn,piece]

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
