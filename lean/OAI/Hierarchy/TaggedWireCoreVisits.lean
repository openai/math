import OAI.Hierarchy.TaggedWireWordSeats
import OAI.Hierarchy.TaggedWireVisitOrder

namespace OAI
/-! # Boundary sites of the actual core-board walk occurrences -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.WordSeats
open AdaptiveProbe WireTelescope VisitOrder
open scoped Classical
open private joint from OAI.Hierarchy.ProbeCoreWalks

variable {h d k : ℕ} {S : PurchaseSampler} (π : Equiv.Perm (Fin (2^h)))

def clip (n j : ℕ) : Fin (n+1) := ⟨min j n,by omega⟩

def payloadAt (p : Fin (2^h)) (j : ℕ) : Site h d k :=
  payloadSite π (p,clip (PayloadStrip.edgeCount (Stages h d)) j)

private theorem at_even (p : Fin (2^h)) (j : Fin (Stages h d+1)) :
    payloadAt (k:=k) π p (2*j.val) = (payloadFreeFrom π p j,none) := by
  have bound : 2*j.val≤PayloadStrip.edgeCount (Stages h d) := by
    have := j.isLt
    unfold PayloadStrip.edgeCount
    omega
  have pos : clip (PayloadStrip.edgeCount (Stages h d)) (2*j.val) =
      ⟨2*j.val,by omega⟩ := Fin.ext (Nat.min_eq_left bound)
  unfold payloadAt payloadSite
  dsimp only
  rw [pos]
  exact Prod.ext (payloadPlace_free π p j).1 rfl

private theorem at_odd (p : Fin (2^h)) (j : Fin (Stages h d+1)) :
    payloadAt (k:=k) π p (2*j.val+1) = (payloadFreeTo π p j,none) := by
  have bound : 2*j.val+1≤PayloadStrip.edgeCount (Stages h d) := by
    have := j.isLt
    unfold PayloadStrip.edgeCount
    omega
  have pos : clip (PayloadStrip.edgeCount (Stages h d)) (2*j.val+1) =
      ⟨2*j.val+1,by omega⟩ := Fin.ext (Nat.min_eq_left bound)
  unfold payloadAt payloadSite
  dsimp only
  rw [pos]
  exact Prod.ext (payloadPlace_free π p j).2.1 rfl

private theorem joint_between (p : Fin (2^h)) (j : Fin (Stages h d+1)) :
    Between (ends π (jointEdge (S:=S) π p j (none : ColumnLayer k)))
      (payloadAt π p (2*j.val)) (payloadAt π p (2*j.val+1)) := by
  rw [at_even,at_odd]
  by_cases h : Fintype.equivFin (Columns _ _) (payloadFreeFrom π p j) <
      Fintype.equivFin _ (payloadFreeTo π p j)
  · left; simp [jointEdge,ends,freeEnds,joint,h]
  · right; simp [jointEdge,ends,freeEnds,joint,h]

private theorem tile_between (p : Fin (2^h)) (t : StageAt h d) :
    Between (ends π (tileEdge (S:=S) p t (none : ColumnLayer k)))
      (payloadAt π p (2*t.val+1)) (payloadAt π p (2*t.val+1+1)) := by
  have atOdd := at_odd (k:=k) π p t.castSucc
  change payloadAt π p (2*t.val+1) = _ at atOdd
  rw [atOdd,
    show 2*t.val+1+1=2*t.succ.val by change 2*t.val+1+1=2*(t.val+1); omega,at_even (k:=k) π p t.succ]
  left
  simp [ends,tileEdge,payloadFreeTo,payloadFreeFrom,inputCol,outputCol]

private theorem prefix_length (p : Fin (2^h)) (j : Fin (Stages h d+1)) :
    (prefixWalk (S:=S) (k:=k) π p j).length = 2*j.val := by
  induction j using Fin.induction with
  | zero => rfl
  | succ t ih =>
    change (prefixWalk (S:=S) (k:=k) π p t.castSucc ++ [_,_]).length=_
    rw [List.length_append,ih]
    change 2*t.val+2=2*(t.val+1)
    omega

theorem payload_length (p : Fin (2^h)) : (payloadWalk (S:=S) (d:=d) (k:=k) π p).length =
    PayloadStrip.edgeCount (Stages h d) := by simp [payloadWalk,prefix_length,PayloadStrip.edgeCount]

private theorem prefix_steps (p : Fin (2^h)) (j : Fin (Stages h d+1)) :
    Steps (ends π) (payloadAt (k:=k) π p) 0 (prefixWalk (S:=S) π p j) := by
  induction j using Fin.induction with
  | zero => intro n hn; simp [prefixWalk] at hn
  | succ t ih =>
    change Steps _ _ _ (_ ++ [_,_])
    apply Steps.append ih
    intro n hn
    have bound : n<2 := by simpa using hn
    rw [Nat.zero_add,prefix_length]
    interval_cases n
    · simpa using joint_between (S:=S) (k:=k) π p t.castSucc
    · simpa using tile_between (S:=S) (k:=k) π p t

theorem payload_steps (p : Fin (2^h)) :
    Steps (ends π) (payloadAt (k:=k) π p) 0 (payloadWalk (S:=S) (d:=d) π p) := by
  apply Steps.append (prefix_steps (S:=S) (k:=k) π p (Fin.last _))
  intro j hj
  have zero : j=0 := by simp at hj; omega
  subst j
  simpa [prefix_length] using joint_between (S:=S) (k:=k) π p (Fin.last (Stages h d))

def commodityTurn (i : Commodity (Fin (2^h)) (Stages h d) k) (j : ℕ) : Turn h d k :=
  match i with
  | .inl p => .inl (p,clip (PayloadStrip.edgeCount (Stages h d)) j)
  | .inr (u,l) => .inr (.inl ((u,l),clip 2 j))

def reserveTurn (c : Columns h d × Fin k) (j : ℕ) : Turn h d k := .inr (.inr (c,clip 2 j))

theorem clip_val {n j : ℕ} (bound : j≤n) : (clip n j).val=j := Nat.min_eq_left bound

theorem commodity_eq {i i' : Commodity (Fin (2^h)) (Stages h d) k} {j j' : ℕ}
    (left : j≤(commodityWalk (S:=S) π i).length) (right : j'≤(commodityWalk (S:=S) π i').length)
    (same : commodityTurn i j=commodityTurn i' j') : i=i' ∧ j=j' := by
  rcases i with p|⟨⟨p,t⟩,l⟩ <;> rcases i' with q|⟨⟨q,t'⟩,m⟩ <;> try contradiction
  · obtain ⟨pq,c⟩ := Prod.mk.inj (Sum.inl.inj same)
    have ej := congrArg Fin.val c
    change j≤(payloadWalk (S:=S) (d:=d) (k:=k) π p).length at left
    change j'≤(payloadWalk (S:=S) (d:=d) (k:=k) π q).length at right
    rw [payload_length] at left right
    exact ⟨congrArg Sum.inl pq,(clip_val left).symm.trans (ej.trans (clip_val right))⟩
  · obtain ⟨uv,c⟩ := Prod.mk.inj (Sum.inl.inj (Sum.inr.inj same))
    exact ⟨congrArg Sum.inr uv,(clip_val left).symm.trans ((congrArg Fin.val c).trans (clip_val right))⟩

theorem reserve_eq {c c' : Columns h d × Fin k} {j j' : ℕ} (left : j≤2) (right : j'≤2)
    (same : reserveTurn c j=reserveTurn c' j') : c=c' ∧ j=j' := by
  obtain ⟨cc,positions⟩ := Prod.mk.inj (Sum.inr.inj (Sum.inr.inj same))
  exact ⟨cc,(clip_val left).symm.trans ((congrArg Fin.val positions).trans (clip_val right))⟩

theorem commodity_ne_reserve (i : Commodity (Fin (2^h)) (Stages h d) k) (c : Columns h d × Fin k)
    (j j' : ℕ) : commodityTurn i j ≠ reserveTurn c j' := by
  rcases i with p|⟨u,l⟩ <;> simp [commodityTurn,reserveTurn]

theorem commodity_steps (i : Commodity (Fin (2^h)) (Stages h d) k) :
    Steps (ends π) (fun j=>site π (commodityTurn i j)) 0 (commodityWalk (S:=S) π i) := by
  rcases i with p|⟨⟨p,t⟩,l⟩
  · exact payload_steps π p
  · intro j hj
    have bound : j<2 := hj
    interval_cases j <;> exact Or.inl ⟨rfl,rfl⟩

theorem reserve_steps (c : Columns h d × Fin k) :
    Steps (ends π) (fun j=>site π (reserveTurn c j)) 0 (catalystWalk (S:=S) c) := by
  intro j hj
  have bound : j<2 := hj
  interval_cases j
  · exact Or.inr ⟨rfl,rfl⟩
  · exact Or.inl ⟨rfl,rfl⟩

theorem commodity_start (i : Commodity (Fin (2^h)) (Stages h d) k) :
    site π (commodityTurn i 0)=(commodityEnds π i).1 := by
  rcases i with p|⟨⟨p,t⟩,l⟩ <;> rfl

theorem commodity_end (i : Commodity (Fin (2^h)) (Stages h d) k) :
    site π (commodityTurn i (commodityWalk (S:=S) π i).length)=(commodityEnds π i).2 := by
  rcases i with p|⟨⟨p,t⟩,l⟩
  · change payloadAt π p (payloadWalk (S:=S) (k:=k) π p).length = _
    rw [payload_length]
    exact (at_odd (k:=k) π p (Fin.last (Stages h d))).trans (by simp [commodityEnds,payloadFreeTo])
  · rfl

end Hierarchy.ProbeStage.CoreBoard.WordSeats

end
end OAI
