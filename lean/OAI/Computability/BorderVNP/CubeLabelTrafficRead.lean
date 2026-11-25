import OAI.Computability.BorderVNP.CubeLabelTraffic
import OAI.Computability.BorderVNP.CubeLabelISAEdgeRows
import OAI.Computability.BorderVNP.CubeLabelISABins

/-! # Reading the incident bin subtotals from the actual label directory

The native edge test consults an opposite cell's stored label precisely when it precedes the
current cell. Incoming data uses its aggregated cell word. The following identities account
for every affected row, in either cable orientation, with the common `Z²` denominator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open Cube Cube.MeanChoice Cube.LabelIndex Finset
open scoped BigOperators

variable {n z : ℕ}

private def side (after : Bool) (ab : ℕ × ℕ) := if after then ab.2 else ab.1

private def oneQuery (c : Fin n) (v u t : Fin (z+1)) (lab nodes : ℕ) : Query :=
  ⟨z+1,c.val,v.val,u.val,t.val,lab,nodes⟩

private theorem one_weight (s : Finset (Fin n)) (x : Fin n → Fin (z+1)) (c o : Fin n)
    (v u t : Fin (z+1)) (lab nodes dir w : ℕ) (m : ℕ → ℕ) (hc : c ∉ s) (ho : o ≠ c)
    (prior : o ∈ s ↔ o < c) (read : o < c → m (lab+o.val) = (x o).val) (after : Bool) :
    side after ((oneQuery c v u t lab nodes).weights m ⟨dir,o.val,w⟩) =
      rowNat (if after then insert c s else s) (if after then Function.update x c v else x)
        (.inl (u,t)) (orientedCable dir c o w) := by
  have h := edgeContrib_rows s x c o v u t dir w hc ho prior
  have old : edgeBefore (z+1) c.val o.val (m (lab+o.val)) (if dir = 0 then t.val else u.val) w =
      edgeBefore (z+1) c.val o.val (x o).val (if dir = 0 then t.val else u.val) w := by
    by_cases hp : o < c
    · rw [read hp]
    · simp only [edgeBefore,(show ¬o.val < c.val from hp),ite_false]
  cases after
  · simpa only [side,Bool.false_eq_true,ite_false,Query.weights,oneQuery,old] using h.1
  · simpa only [side,ite_true,Query.weights,oneQuery,old] using h.2

private theorem one_atCell (e : Cable) (hs : e.src < n) (hd : e.dst < n) (c : Fin n)
    (s : Finset (Fin n)) (x : Fin n → Fin (z+1)) (v u t : Fin (z+1)) (lab nodes : ℕ) (m : ℕ → ℕ)
    (prior : ∀ o, o ∈ s ↔ o < c) (read : ∀ o : Fin n, o < c → m (lab+o.val) = (x o).val)
    (after : Bool) :
    e.atCell c.val (fun i => side after ((oneQuery c v u t lab nodes).weights m i)) =
      if touches c (e.traffic hs hd) then
        rowNat (if after then insert c s else s) (if after then Function.update x c v else x)
          (.inl (u,t)) (e.traffic hs hd) else 0 := by
  let a : Fin n := ⟨e.src,hs⟩
  let b : Fin n := ⟨e.dst,hd⟩
  have hc : c ∉ s := (prior c).not.mpr (lt_irrefl c)
  by_cases hsame : e.src = e.dst
  · simp [Cable.atCell,Cable.traffic,liveWidth,hsame,rowNat]
  by_cases ha : a = c
  · subst c
    have hb : b ≠ a := fun h => hsame (congrArg Fin.val h).symm
    have h := one_weight s x a b v u t lab nodes 0 e.width m hc hb (prior b) (read b) after
    simpa [Cable.atCell,Cable.traffic,liveWidth,orientedCable,touches,a,b,hsame] using h
  by_cases hb : b = c
  · subst c
    have h := one_weight s x b a v u t lab nodes 1 e.width m hc ha (prior a) (read a) after
    simpa [Cable.atCell,Cable.traffic,liveWidth,orientedCable,touches,a,b,hsame,Ne.symm hsame] using h
  · have ha' : c.val ≠ e.src := fun h => ha (Fin.ext h.symm)
    have hb' : c.val ≠ e.dst := fun h => hb (Fin.ext h.symm)
    simp [Cable.atCell,hsame,ha',hb',Cable.traffic,touches,Fin.ext_iff,Ne.symm ha',Ne.symm hb']

private theorem cable_side (l : Layout) (before : ℕ → ℕ) (ep : Endpoints l before) (m : ℕ → ℕ)
    (c : Fin l.cells) (s : Finset (Fin l.cells)) (x : Fin l.cells → Fin (z+1)) (v u t : Fin (z+1))
    (lab nodes : ℕ) (prior : ∀ o, o ∈ s ↔ o < c)
    (read : ∀ o : Fin l.cells, o < c → m (lab+o.val) = (x o).val) (after : Bool) :
    ((incidents (cableAt l before) c.val l.cableCount).map
      (fun i => side after ((oneQuery c v u t lab nodes).weights m i))).sum =
      incidentSum (fromTables l before ep) c (if after then insert c s else s)
        (if after then Function.update x c v else x) (.inl (u,t)) := by
  rw [incidents_sum,incidentSum,sum_filter,Fintype.sum_sum_type]
  conv_rhs => rhs; equals 0 =>
    apply sum_eq_zero
    intro j _
    split_ifs <;> rfl
  rw [add_zero]
  apply sum_congr rfl
  intro i _
  exact one_atCell (cableAt l before i) (ep.cables i i.isLt).1
    (ep.cables i i.isLt).2 c s x v u t lab nodes m prior read after

/-- Old and new cable subtotals from the actual indexed incident list. -/
theorem cable_subtotals (l : Layout) (before : ℕ → ℕ) (ep : Endpoints l before) (m : ℕ → ℕ)
    (c : Fin l.cells) (s : Finset (Fin l.cells)) (x : Fin l.cells → Fin (z+1)) (v u t : Fin (z+1))
    (lab nodes : ℕ) (prior : ∀ o, o ∈ s ↔ o < c)
    (read : ∀ o : Fin l.cells, o < c → m (lab+o.val) = (x o).val) :
    (Query.mk (z+1) c.val v.val u.val t.val lab nodes).sums m (incidents (cableAt l before) c.val l.cableCount) =
      (incidentSum (fromTables l before ep) c s x (.inl (u,t)),
       incidentSum (fromTables l before ep) c (insert c s) (Function.update x c v) (.inl (u,t))) := by
  apply Prod.ext
  · exact cable_side l before ep m c s x v u t lab nodes prior read false
  · exact cable_side l before ep m c s x v u t lab nodes prior read true

/-- The summed delivery rows in one bin use exactly the per-cell data word written during indexing. -/
theorem data_subtotal (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m) (c : Fin l.cells)
    (s : Finset (Fin l.cells)) (x : Fin l.cells → Fin (z+1)) (u : Fin (z+1)) :
    incidentSum (fromTables l m ep) c s x (.inr u) =
      sumWidth (fun i => if (deliveryAt l m i).1 = c.val then (deliveryAt l m i).2 else 0) l.deliveryCount *
        (z+1)*factor s x c u := by
  rw [incidentSum,Finset.sum_filter,Fintype.sum_sum_type]
  conv_lhs => lhs; equals 0 =>
    apply sum_eq_zero
    intro i _
    split_ifs <;> rfl
  rw [zero_add,sumWidth_eq_fin,Finset.sum_mul,Finset.sum_mul]
  apply sum_congr rfl
  intro i _
  let a : Fin l.cells := ⟨(deliveryAt l m i).1,ep.deliveries i i.isLt⟩
  change (if a = c then (deliveryAt l m i).2*(z+1)*factor s x a u else 0) = _
  by_cases h : a = c
  · have e := congrArg Fin.val h
    change (deliveryAt l m i).1 = c.val at e
    rw [h,ite_eq_left rfl,ite_eq_left e]
  · have e : (deliveryAt l m i).1 ≠ c.val := fun eq => h (Fin.ext eq)
    rw [ite_eq_right h,ite_eq_right e]; simp

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
