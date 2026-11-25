import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices
import OAI.Hierarchy.ProtocolRAMCalendarFeedRead
import OAI.Hierarchy.ProtocolRAMCalendarPhysicalCharges

namespace OAI
/-! # Charging every actual boundary overflow by its physical core walk -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {W h N k edges : ℕ}

/-- One finite inventory ordinal per physical (lane, record) pair. The same
row-major ordinal is used by both the charged event and the native overflow
scatter, including lanes with no discharged stock. -/
theorem FeedLayout.installed_charge (L : FeedLayout h N k) (paths : CommodityColumn→Traversals)
    (m : Memory W) (payload : ℕ) (len : Fin edges→ℝ)
    (walk : Fin (lanes N k*2^h)→List (Fin edges))
    (reads : ∀l : Fin (lanes N k),(paths (L.column l)).Reads m
      (fun i : Fin (2^h)=>walk (finProdFinEquiv (l,i)))) :
    ((L.columns.map (fun c=>c.paidSlice (paths c))).map (fun t=>t.toll m len payload)).sum=
      ∑i : Fin (lanes N k*2^h),((m (L.overflow+i.val)).val:ℝ)/payload*((walk i).map len).sum := by
  let price (i : Fin (lanes N k*2^h)) := ((m (L.overflow+i.val)).val:ℝ)/payload*((walk i).map len).sum
  have piece (l : Fin (lanes N k)) :
      ((L.column l).paidSlice (paths (L.column l))).toll m len payload=
        ∑i : Fin (2^h),price (finProdFinEquiv (l,i)) := by
    rw [(paths (L.column l)).boundary_toll (L.column l) m payload len _ (reads l)]
    apply Finset.sum_congr rfl
    intro i _
    unfold price
    change _*(((m (L.overflow+l.val*2^h+i.val)).val:ℝ)/payload)=
      (((m (L.overflow+(i.val+2^h*l.val))).val:ℝ)/payload)*_
    rw [show L.overflow+(i.val+2^h*l.val)=L.overflow+l.val*2^h+i.val by
      rw [Nat.mul_comm (2^h)];omega]
    exact mul_comm ..
  change _=∑i,price i
  rw [←finProdFinEquiv.sum_comp price,Fintype.sum_prod_type]
  simp only [columns,List.finRange,List.map_ofFn,Function.comp_def,List.sum_ofFn,piece]

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
