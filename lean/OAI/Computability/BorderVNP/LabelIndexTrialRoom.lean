import OAI.Computability.BorderVNP.LabelIndexAllocation
import OAI.Computability.BorderVNP.CubeLabelISABins

/-! # Space and width bounds for all linked scans of the sparse directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open RoutingISA.LabelTrial

/-- Scoring and committing consume exactly the arrays constructed by initialization. -/
def Layout.trialFrame (l : Layout) (labels : ℕ) : Frame :=
  ⟨l.labels,l.cells,labels,l.heads,l.nodes,l.data,l.cableMean,l.dataMean⟩

/-- The frame decoders for the constructor and consumer agree definitionally. -/
theorem trialFrame_decode (b : ℕ) (m : ℕ → ℕ) :
    (layout b m).trialFrame (m (b+48)) = Frame.decode b m := rfl

/-- Every opposite endpoint in the scan is a cell and the sum of the widths at
a cell is bounded by the sum of the original cable widths. -/
theorem incidents_bounded (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m) (c : ℕ)
    {j : ℕ} (hj : j ≤ l.cableCount) :
    let es := incidents (cableAt l m) c j
    (∀ e ∈ es, e.other < l.cells) ∧ (es.map Incident.width).sum ≤ sumWidth (Cable.width ∘ cableAt l m) j := by
  induction j with
  | zero => simp [incidents,sumWidth]
  | succ j ih =>
    have old := ih (Nat.le_of_succ_le hj)
    have ⟨hs,hd⟩ := ep.cables j hj
    dsimp only at old ⊢
    by_cases eq : (cableAt l m j).src = (cableAt l m j).dst
    · simp only [incidents,Cable.prepend,ite_eq_left eq,sumWidth,Function.comp_apply]
      exact ⟨old.1,old.2.trans (Nat.le_add_right ..)⟩
    · by_cases src : c = (cableAt l m j).src <;> by_cases dst : c = (cableAt l m j).dst
      · exact (eq (src.symm.trans dst)).elim
      · simp only [incidents,Cable.prepend,ite_eq_right eq,ite_eq_left src,ite_eq_right dst,
          List.forall_mem_cons,List.map_cons,List.sum_cons,sumWidth,Function.comp_apply]
        exact ⟨⟨hd,old.1⟩,by omega⟩
      · simp only [incidents,Cable.prepend,ite_eq_right eq,ite_eq_right src,ite_eq_left dst,
          List.forall_mem_cons,List.map_cons,List.sum_cons,sumWidth,Function.comp_apply]
        exact ⟨⟨hs,old.1⟩,by omega⟩
      · simp only [incidents,Cable.prepend,ite_eq_right eq,ite_eq_right src,ite_eq_right dst,sumWidth]
        exact ⟨old.1,old.2.trans (Nat.le_add_right ..)⟩

private theorem weight_bounds (q : Query) (m : ℕ → ℕ) (e : Incident) (hz : 0 < q.Z) :
    (q.weights m e).1 ≤ e.width*q.Z^2 ∧ (q.weights m e).2 ≤ e.width*q.Z^2 := by
  let f := if e.dir = 0 then q.dst else q.src
  let old := edgeBefore q.Z q.cell e.other (m (q.labels+e.other)) f e.width
  have lo : old ≤ e.width*q.Z := by
    dsimp [old,edgeBefore]
    split
    · split <;> first | exact Nat.zero_le _ | exact le_rfl
    · exact Nat.le_mul_of_pos_right _ hz
  have bigger := Nat.le_mul_of_pos_right (e.width*q.Z) hz
  rw [pow_two, ← Nat.mul_assoc]
  refine ⟨lo.trans bigger,?_⟩
  change edgeAfter q.Z q.cand _ old ≤ _
  unfold edgeAfter
  split_ifs <;> first | exact Nat.mul_le_mul_right _ lo | exact Nat.zero_le _

/-- Every prefix and full incidence sum fits once the width sum scaled by `Z²` fits. -/
theorem sums_le (q : Query) (m : ℕ → ℕ) (es : List Incident) (hz : 0 < q.Z) :
    (q.sums m es).1 ≤ (es.map Incident.width).sum*q.Z^2 ∧
    (q.sums m es).2 ≤ (es.map Incident.width).sum*q.Z^2 := by
  induction es with
  | nil => simp [Query.sums]
  | cons e es ih =>
    simp only [Query.sums,List.map_cons,List.sum_cons,Nat.add_mul] at ih ⊢
    have both := weight_bounds q m e hz
    exact ⟨Nat.add_le_add both.1 ih.1,Nat.add_le_add both.2 ih.2⟩

/-- All native probes and row products along a linked list fit the allocated word. -/
theorem Linked.queryRoom {m : ℕ → ℕ} (q : Query) {bound ptr : ℕ} {es : List Incident}
    (h : Linked m q.nodes bound ptr es) (w cells : ℕ) (nodes : q.nodes+4*bound ≤ 2^w)
    (labels : q.labels+cells ≤ 2^w) (other : ∀ e ∈ es, e.other < cells)
    (width : (es.map Incident.width).sum*q.Z^2 < 2^w) : q.room w m ptr es := by
  induction es generalizing ptr with
  | nil => trivial
  | cons e es ih =>
    have own := other e (by simp)
    have cap := h.2.1
    have live := h.1
    simp only [List.map_cons,List.sum_cons,Nat.add_mul] at width
    refine ⟨?_,by omega,by omega,ih h.2.2.2.2.2 (fun b hb => other b (by simp [hb])) (by omega)⟩
    unfold nodeAddr; omega

/-- Across arbitrary trials and commits the label and mean words can change.
Agreement on the heads, linked nodes and per-cell delivery widths is sufficient
for all remaining address and overflow guards. -/
theorem frame_room {l : Layout} {m : ℕ → ℕ} {a : Acc}
    (view : View l m a l.cells l.cableCount l.deliveryCount (l.labels*l.labels) l.labels)
    (al : Allocated l) (ep : Endpoints l m) (t : ℕ → ℕ) (labelBase w c v i : ℕ)
    (hz : 0 < l.labels) (hc : c < l.cells) (hi : i < l.labels^2+l.labels)
    (heads : t (l.heads+c) = a.mem (l.heads+c))
    (nodes : ∀ x, l.nodes ≤ x → x < l.nodes+8*l.cableCount → t x = a.mem x)
    (data : t (l.data+c) = a.mem (l.data+c)) (addr : l.dataMean+l.labels ≤ 2^w)
    (labs : labelBase+l.cells ≤ 2^w)
    (cw : sumWidth (Cable.width ∘ cableAt l m) l.cableCount*l.labels^2 < 2^w)
    (dw : sumWidth (Prod.snd ∘ deliveryAt l m) l.deliveryCount*l.labels^2 < 2^w) :
    (l.trialFrame labelBase).room w c v i t (incidents (cableAt l m) c l.cableCount) := by
  let es := incidents (cableAt l m) c l.cableCount
  have hh := al.heads
  have hn := al.nodes
  have hd := al.data
  have hb := al.cableMean
  have link : Linked t l.nodes (2*l.cableCount) (t (l.heads+c)) es := by
    rw [heads]; exact (view.lists c hc).copy le_rfl (fun x hx hy => nodes x hx (by omega))
  obtain ⟨other,widths⟩ := incidents_bounded l m ep c le_rfl
  have mass := (Nat.mul_le_mul_right (l.labels^2) widths).trans_lt cw
  have de := view.data c hc
  have demand := sumWidth_le (f := fun j => if (deliveryAt l m j).1 = c then (deliveryAt l m j).2 else 0)
    (g := Prod.snd ∘ deliveryAt l m) (i := l.deliveryCount) le_rfl
    (fun _ _ => by simp only [Function.comp_apply]; split <;> omega)
  let p := l.trialFrame labelBase
  let q := p.query c v i
  change p.room w c v i t es
  have square : l.labels*l.labels = l.labels^2 := (pow_two _).symm
  refine ⟨hz,?_,?_⟩
  · change (if i < l.labels^2 then l.cableMean+i else l.dataMean+(i-l.labels^2)) < 2^w
    split <;> omega
  · change if i < l.labels^2 then l.heads+c < 2^w ∧ Chain t l.nodes (t (l.heads+c)) es ∧
      q.room w t (t (l.heads+c)) es ∧ (q.sums t es).1 < 2^w ∧ (q.sums t es).2 < 2^w
      else l.data+c < 2^w ∧ t (l.data+c)*l.labels^2 < 2^w
    split
    · have sum := sums_le q t es hz
      exact ⟨by omega,link.chain,link.queryRoom q w l.cells (show l.nodes+4*(2*l.cableCount) ≤ 2^w by omega)
        labs other mass,sum.1.trans_lt mass,sum.2.trans_lt mass⟩
    · rw [data,de]
      exact ⟨by omega,(Nat.mul_le_mul_right _ demand).trans_lt dw⟩

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
