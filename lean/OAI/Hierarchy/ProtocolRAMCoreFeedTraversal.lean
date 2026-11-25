import OAI.Hierarchy.ProtocolRAMFeedBlocks
import OAI.Hierarchy.ProtocolRAMCoreRouteCost
import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices

namespace OAI
/-! # Actual boundary-feed walks on one physical commodity column -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage AdaptiveProbe CoreBoard
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped BigOperators Classical Fin.CommRing
variable {n z W k w R K attempts edges : ℕ} {S : PurchaseSampler}
local notation "D" => 2^W
local notation "N" => Stages z D

abbrev Lane (n k : ℕ) := Option (Fin n × (Fin k × Bool))

def laneGood (l : Lane n k) (p : Fin (2^z)) : Commodity (Fin (2^z)) n k :=
  match l with
  | none => .inl p
  | some (t,a) => .inr ((p,t),a)

def laneWidth (l : Lane n k) := l.elim (2*n+1) (fun _=>2)

def laneAction (l : Lane n k) : Fin (laneWidth l)→Actions n k :=
  match l with
  | none => fun j=>.inl j
  | some (t,a) => fun j=>if j.val=0 then .inr (.inl t) else .inr (.inr (.inl (t,a)))

def laneTraversal (x : Source) (S : PurchaseSampler) (z W k attempts : ℕ)
    (l : Lane (Stages z (2^W)) k) (owner parity : Bank) : Traversals :=
  let span:=2^z
  ⟨laneWidth l*span,owner,parity,
    blocks span (laneWidth l) (fun j=>operator x S z W k attempts (laneAction l j)),
    blocks span (laneWidth l) (fun _=>.row),none⟩

private theorem lane_length (π : Equiv.Perm (Fin (2^z))) (place : Site z D k→Fin K)
    (B : Mount (S:=S) π place edges) (l : Lane N k) (p : Fin (2^z)) :
    laneWidth l=(B.ordinary (laneGood l p)).length := by
  cases l with
  | none => simp [laneWidth,laneGood,Mount.ordinary,commodityWalk,payload_length]
  | some a => rcases a with ⟨t,a⟩; rfl

theorem laneTraversal_reads (x : Source) (π : Equiv.Perm (Fin (2^z)))
    (place : Site z D k→Fin K) (B : Mount (S:=S) π place edges) (order : Fin R≃Edges S z D k)
    (physical : ∀e,(B.row e).val=(order.symm e).val) (m : Memory w)
    (data : Readable x S z W k attempts order π m) (l : Lane N k)
    (room : laneWidth l*2^z<2^w) (edgeFit : edges≤2^w) (owner parity : Bank) :
    (laneTraversal x S z W k attempts l owner parity).Reads m (fun i=>B.ordinary (laneGood l i)) := by
  let layout : (Fin (laneWidth l) × Fin (2^z)) ≃ (Σ p,Fin (B.ordinary (laneGood l p)).length) :=
    (Equiv.prodComm _ _).trans ((Equiv.sigmaEquivProd _ _).symm.trans
      (Equiv.sigmaCongrRight fun p=>finCongr (lane_length π place B l p)))
  have selected (u : Fin (laneWidth l) × Fin (2^z)) :
      (finProdFinEquiv.symm.trans layout) (finProdFinEquiv u)=layout u :=
    congrArg layout (finProdFinEquiv.symm_apply_apply u)
  let readAt (u : Σ p,Fin (B.ordinary (laneGood l p)).length) :=
    ((B.ordinary (laneGood l u.1))[u.2.val]'u.2.isLt).val
  refine ⟨finProdFinEquiv.symm.trans layout,?_,?_⟩
  · intro i
    obtain ⟨⟨t,p⟩,rfl⟩:=finProdFinEquiv.surjective i
    change ((blocks (2^z) (laneWidth l) (fun j=>operator x S z W k attempts (laneAction l j))).eval m _).val =
      readAt ((finProdFinEquiv.symm.trans layout) (finProdFinEquiv (t,p)))
    rw [blocks_eval _ _ _ _ t p room,selected (t,p)]
    have atHop (g : Commodity (Fin (2^z)) N k) (j : Fin (arity g)) :=
      physical_hop π place B order physical data (Sum.inl ⟨g,j⟩)
    cases l with
    | none =>
      have got:=atHop (.inl p) t
      exact (congrArg Fin.val got).trans (Fin.val_cast_of_lt (Fin.isLt _ |>.trans_le edgeFit))
    | some pair =>
      rcases pair with ⟨u,a⟩
      have got:=atHop (.inr ((p,u),a)) t
      exact (congrArg Fin.val got).trans (Fin.val_cast_of_lt (Fin.isLt _ |>.trans_le edgeFit))
  · intro i
    obtain ⟨⟨t,p⟩,rfl⟩:=finProdFinEquiv.surjective i
    change ((blocks (2^z) (laneWidth l) (fun _=>.row)).eval m _).val =
      ((finProdFinEquiv.symm.trans layout) (finProdFinEquiv (t,p))).1.val
    rw [blocks_eval _ _ _ _ t p room,selected (t,p)]
    have positive : 0<laneWidth l := by cases l <;> simp [laneWidth]
    have dim : 2^z≤laneWidth l*2^z := by simpa using Nat.mul_le_mul_right (2^z) positive
    exact Fin.val_cast_of_lt (p.isLt.trans (dim.trans_lt room))

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
