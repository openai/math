import OAI.Hierarchy.ProbeArchiveRowBound

namespace OAI
/-! # Native core occupancy for a partial commodity bank at a feed boundary -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage
open scoped BigOperators Fin.CommRing Classical
noncomputable section
variable {w h d k n edges : ℕ} {S : PurchaseSampler}

/-- Each feed column supplies only one lane from the permanent commodity bank.
Any injective subfamily of the actual core walks satisfies the full board bound. -/
theorem mapped_lane_bound (π : Equiv.Perm (Fin (2^h))) (label : CoreBoard.Edges S h d k ↪ Fin edges)
    (idx : Fin n ↪ Commodity (Fin (2^h)) (CoreBoard.Stages h d) k) (bits : Fin n→ℕ) (B : ℕ)
    (bound : ∀i,bits i≤B) (e : Fin edges) :
    routeLoad (fun j=>(CoreBoard.commodityWalk (S:=S) π (idx j)).map label) bits e≤
      (1+CoreBoard.Stages h d*(2*k))*((2*CoreBoard.Stages h d+2)*B) := by
  by_cases onBoard : ∃ b,label b=e
  · obtain ⟨b,rfl⟩ := onBoard
    let load := fun i=>(CoreBoard.occurrences b (CoreBoard.commodityWalk (S:=S) π i))*B
    have whole := CoreBoard.core_load_bound π b (fun _=>B) B (fun _=>le_rfl)
    unfold routeLoad at whole ⊢
    change (∑j, CoreBoard.occurrences (label b) ((CoreBoard.commodityWalk (S:=S) π (idx j)).map label)*bits j)≤_
    calc _ ≤ ∑j : Fin n,load (idx j) := Finset.sum_le_sum fun j _=>by
                simpa only [load,occurrences_map] using
                  Nat.mul_le_mul_left (CoreBoard.occurrences b (CoreBoard.commodityWalk (S:=S) π (idx j))) (bound j)
         _ = ∑ i ∈ Finset.univ.map idx,load i := (Finset.sum_map ..).symm
         _ ≤ ∑ i,load i := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
         _ ≤ _ := whole
  · have zero (i : Fin n) : e∉(CoreBoard.commodityWalk (S:=S) π (idx i)).map label := by
      intro yes
      obtain ⟨a,_,eq⟩ := List.mem_map.mp yes
      exact onBoard ⟨a,eq⟩
    simp [routeLoad,fun i=>List.count_eq_zero.mpr (zero i)]

/-- The archived overflow word reached by each native feed traversal is bounded
at every physical row, for the true recorded walk occurrence, including repeats. -/
theorem Traversals.boundary_spill_bound (t : Traversals) (c : CommodityColumn) (m : Memory w) (e : Fin edges)
    (π : Equiv.Perm (Fin (2^h))) (label : CoreBoard.Edges S h d k ↪ Fin edges)
    (idx : Fin c.rows ↪ Commodity (Fin (2^h)) (CoreBoard.Stages h d) k) (B : ℕ)
    (positions : t.Reads m (fun j=>(CoreBoard.commodityWalk (S:=S) π (idx j)).map label))
    (cap : ∀i:Fin c.rows,(m (c.overflow+i.val)).val≤B) :
    (c.paidSlice t).load m e≤(1+CoreBoard.Stages h d*(2*k))*((2*CoreBoard.Stages h d+2)*B) := by
  let walk := fun i : Fin c.rows=>(CoreBoard.commodityWalk (S:=S) π (idx i)).map label
  let bits := fun i : Fin c.rows=>(m (c.overflow+i.val)).val
  have read (i : Fin t.positions) : ((c.paidSlice t).amount.eval m (i.val:Word w)).val=bits (positions.enum i).1 := by
    let saved := PaidWidths.archivedBank c.overflow c.rows
    have enough : c.rows ≤ saved.size := (ProtocolRAMPurchaseSampler.lt_span _).le
    change (saved.read m (t.sourceRow.eval m (i.val:Word w))).val=_
    simp only [Bank.read,positions.ownerAt i]
    rw [Nat.mod_eq_of_lt ((positions.enum i).1.isLt.trans_le enough)]
    simp only [saved,PaidWidths.archivedBank,bits]
  rw [PaidWidths.walks_load _ m e walk bits positions.enum positions.edgeAt read]
  exact mapped_lane_bound π label idx bits B cap e


end
end Hierarchy.ProtocolRAM.Calendar

end OAI
