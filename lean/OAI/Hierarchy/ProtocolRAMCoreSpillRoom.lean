import OAI.Hierarchy.ProtocolRAMCoreSpillTraversal
import OAI.Hierarchy.ProtocolRAMCoreFeedTraversal
import OAI.Hierarchy.ProtocolRAMRepairCommodity
import OAI.Hierarchy.ProtocolRAMCalendarFeedRead

namespace OAI
/-! # Uniform native word cost and identity of each earlier-spill commodity lane -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped BigOperators Classical Fin.CommRing
variable {z W k w R K attempts edges out : ℕ} {S : PurchaseSampler}
local notation "D" => 2^W
local notation "N" => Stages z D

theorem earlyFits (p : Recipes) (x : Source) (o : Orders z D k) (owner parity : Bank)
    (s : Safe x S z W k attempts w out)
    (header : p.kind.Fits w out ∧ p.mode.Fits w out ∧ p.operand.Fits w out) :
    let t:=earlyTraversal p x S z W k attempts o owner parity
    t.edge.Fits w out ∧ t.sourceRow.Fits w out :=
  ⟨CatalogueRows.fits_atRow _ _ (index_fits p x s header) ⟨trivial,trivial⟩,
    ⟨header.2.2,⟨⟨trivial,trivial⟩,trivial⟩⟩⟩

theorem early_field_work (p : Recipes) (x : Source) (o : Orders z D k) (owner parity : Bank) :
    let t:=earlyTraversal p x S z W k attempts o owner parity
    t.edge.work≤operationBound N k attempts*6 ∧ t.sourceRow.work=12 := by
  change _ ∧ _; constructor
  · exact (CatalogueRows.substitute_work _ _).trans (Nat.mul_le_mul_right 6 (index_work p x))
  · rfl

theorem lane_fits (x : Source) (l : Lane N k) (owner parity : Bank)
    (s : Safe x S z W k attempts w out) :
    let t:=laneTraversal x S z W k attempts l owner parity
    t.edge.Fits w out ∧ t.sourceRow.Fits w out := by
  refine ⟨blocks_fits _ _ _ _ (fun j=>?_),blocks_fits _ _ _ _ (fun _=>trivial)⟩
  rcases (laneAction l j) with e|a|⟨a,b⟩|b
  · exact s.payload e
  · exact s.tile a
  · exact s.quote a b
  · exact s.center b

theorem lane_field_work (x : Source) (l : Lane N k) (owner parity : Bank) :
    let t:=laneTraversal x S z W k attempts l owner parity
    t.edge.work≤blockWork (63+8*ReportSockets.copies k attempts) (laneWidth l) ∧
      t.sourceRow.work≤blockWork 2 (laneWidth l) :=
  ⟨blocks_work _ _ _ _ (fun j=>operator_work x (laneAction l j)),blocks_work _ _ _ _ (fun _=>le_rfl)⟩

def indexLanes («N» k : ℕ) : Fin 1 ⊕ (Fin «N» × Fin (2*k)) ≃ Fin (FeedLayout.lanes «N» k) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

def decodeLane (l : Fin (FeedLayout.lanes N k)) : Lane N k :=
  match (indexLanes N k).symm l with
  | .inl _=>none
  | .inr (t,a)=>some (t,PurchaseMarks.signedDirection k a)

theorem decode_slot (l : Fin (FeedLayout.lanes N k)) (i : Fin (2^z)) :
    PurchaseInventory.slotEquiv z N k (laneGood (decodeLane l) i)=finProdFinEquiv (l,i) := by
  obtain ⟨j,rfl⟩ := (indexLanes N k).surjective l
  unfold decodeLane
  rw [Equiv.symm_apply_apply]
  rcases j with f | ⟨t,a⟩
  · have e : f=0 := Subsingleton.elim _ _
    subst f
    apply Fin.ext
    change 0*2^z+i.val=i.val+2^z*0
    simp
  · apply Fin.ext
    change (1+t.val*(2*k)+((PurchaseMarks.signedDirection k).symm (PurchaseMarks.signedDirection k a)).val)*2^z+i.val =
      i.val+2^z*(1+(a.val+(2*k)*t.val))
    rw [Equiv.symm_apply_apply]
    ring

/-- Extract the public lane from the fixed overflow address of the physical feed
column. This computation is performed when the procedure text is built. -/
def feedLane (L : FeedLayout z N k) (c : CommodityColumn) : Fin (FeedLayout.lanes N k) :=
  ⟨min ((c.kept-L.kept)/2^z) (FeedLayout.lanes N k-1),
    Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (by unfold FeedLayout.lanes; omega)⟩

@[simp] theorem feedLane_column (L : FeedLayout z N k) (l : Fin (FeedLayout.lanes N k)) :
    feedLane L (L.column l)=l := by
  apply Fin.ext
  change min ((L.kept+l.val*2^z-L.kept)/2^z) (FeedLayout.lanes N k-1)=l.val
  have offset : L.kept+l.val*2^z-L.kept=l.val*2^z := by omega
  rw [offset,Nat.mul_div_cancel _ (Nat.two_pow_pos z)]
  exact Nat.min_eq_left (by have bound := l.isLt; omega)

def boundaryTraversal (x : Source) (S : PurchaseSampler) (z W k attempts : ℕ)
    (L : FeedLayout z (Stages z (2^W)) k) (owner parity : Bank) (c : CommodityColumn) : Traversals :=
  laneTraversal x S z W k attempts (decodeLane (feedLane L c)) owner parity

theorem boundary_reads (x : Source) (π : Equiv.Perm (Fin (2^z))) (place : Site z D k→Fin K)
    (B : Mount (S:=S) π place edges) (order : Fin R≃Edges S z D k)
    (physical : ∀e,(B.row e).val=(order.symm e).val) (m : Memory w)
    (data : Readable x S z W k attempts order π m) (L : FeedLayout z N k)
    (l : Fin (FeedLayout.lanes N k)) (room : laneWidth (decodeLane l)*2^z<2^w)
    (edgeFit : edges≤2^w) (owner parity : Bank) :
    (boundaryTraversal x S z W k attempts L owner parity (L.column l)).Reads m
      (fun i=>B.ordinary ((PurchaseInventory.slotEquiv z N k).symm (finProdFinEquiv (l,i)))) := by
  simp only [boundaryTraversal,feedLane_column]
  have undo (i : Fin (2^z)) : (PurchaseInventory.slotEquiv z N k).symm (finProdFinEquiv (l,i))=
      laneGood (decodeLane l) i := by rw [←decode_slot l i,Equiv.symm_apply_apply]
  simpa only [undo] using laneTraversal_reads x π place B order physical m data (decodeLane l) room edgeFit owner parity

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
