import OAI.Hierarchy.ProbeCoreBoard
import OAI.Hierarchy.ProbePayloadFixedJoins
import OAI.Hierarchy.TaggedWireRoutes

namespace OAI
/-! # Residual and catalyst walks in the same charged edge catalogue -/

namespace Hierarchy.ProbeStage.CoreBoard
open AdaptiveProbe WireTelescope LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped Classical
noncomputable section

variable {S : PurchaseSampler} {h d k K : ℕ}

def graph (π : Equiv.Perm (Fin (2^h))) (place : Site h d k → Fin K) :
    PortGraph (Fin K) (Edges S h d k) :=
  ⟨fun e => place (ends π e).1, fun e => place (ends π e).2⟩

def tileEdge (p : Fin (2^h)) (t : StageAt h d) (l : ColumnLayer k) : Edges S h d k :=
  .inr ((p,t),l)

def radiusEdge (c : Columns h d) (l : Fin k × Bool) : Edges S h d k := .inl (.inl (c,l))

private theorem joinApart (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (j : Fin (Stages h d+1)) :
    payloadFreeFrom π p j≠payloadFreeTo π p j := by
  obtain ⟨left,right,_⟩ := payloadPlace_free π p j
  rw [←left,←right]
  exact (payloadPlace π p).injective.ne (Strip.horizontal _ _).apart

private def joint (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (j : Fin (Stages h d+1)) : Fixed h d :=
  let x := payloadFreeFrom π p j
  let y := payloadFreeTo π p j
  let ord := Fintype.equivFin (Columns h d)
  let adj := payloadFree_fixed π p j
  if before : ord x<ord y then ⟨(x,y),adj,before⟩
  else ⟨(y,x),(permutationFabric h d).fixedAll_symm _ _ adj,
    lt_of_le_of_ne (le_of_not_gt before) (ord.injective.ne (joinApart π p j).symm)⟩

def jointEdge (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (j : Fin (Stages h d+1))
    (l : ColumnLayer k) : Edges S h d k := .inl (.inr (.inr (.inl (joint π p j,l))))

private theorem joint_trace (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (j : Fin (Stages h d+1))
    (l : ColumnLayer k) (place : Site h d k → Fin K) :
    Traverses (graph (S:=S) π place) (place (payloadFreeFrom π p j,l)) [jointEdge π p j l]
      (place (payloadFreeTo π p j,l)) := by
  let e : Edges S h d k := jointEdge π p j l
  by_cases order : Fintype.equivFin (Columns h d) (payloadFreeFrom π p j) <
      Fintype.equivFin (Columns h d) (payloadFreeTo π p j)
  · simpa [e,graph,jointEdge,ends,freeEnds,joint,order] using
      (Traverses.forward (G:=graph π place) e (Traverses.nil _))
  · simpa [e,graph,jointEdge,ends,freeEnds,joint,order] using
      (Traverses.backward (G:=graph π place) e (Traverses.nil _))

def prefixWalk (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) :
    Fin (Stages h d+1) → List (Edges S h d k) :=
  Fin.induction [] (fun t xs => xs++[jointEdge π p t.castSucc none,tileEdge p t none])

def payloadWalk (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) : List (Edges S h d k) :=
  prefixWalk π p (Fin.last (Stages h d)) ++ [jointEdge π p (Fin.last (Stages h d)) none]

private theorem prefix_spec (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (place : Site h d k → Fin K)
    (M : ℝ) (j : Fin (Stages h d+1)) :
    Traverses (graph (S:=S) π place) (place (.inl p,none)) (prefixWalk π p j)
      (place (payloadFreeFrom π p j,none)) ∧
    ((prefixWalk (S:=S) (k:=k) π p j).map (coreLength (freeLength M))).sum = (j.val:ℝ) := by
  let : Nonempty (Fin K) := ⟨place (.inl p,none)⟩
  induction j using Fin.induction with
  | zero => exact ⟨Traverses.nil _,by simp [prefixWalk]⟩
  | succ t ih =>
    let a := advisedStage h d π t
    have jt := joint_trace (S:=S) π p t.castSucc none place
    have tj : Traverses (graph (S:=S) π place) (place (inputCol t (a.group p) (a.input p),none))
        [tileEdge p t none] (place (outputCol t (a.group p) (a.output p),none)) :=
      Traverses.forward (G:=graph (S:=S) π place) (tileEdge p t none) (Traverses.nil _)
    have both := Traverses.append (graph (S:=S) π place) ih.1 jt
    rw [payloadFreeTo,Fin.lastCases_castSucc] at both
    exact ⟨by simpa [prefixWalk,payloadFreeFrom,List.append_assoc,outputCol,a] using
      (Traverses.append (graph (S:=S) π place) both tj), by
      simpa [prefixWalk, tileEdge,jointEdge,coreLength,freeLength] using congrArg (fun y:ℝ=>y+1) ih.2⟩

theorem payload_walk (π : Equiv.Perm (Fin (2^h))) (p : Fin (2^h)) (place : Site h d k → Fin K)
    (M : ℝ) :
    Traverses (graph (S:=S) π place) (place (.inl p,none)) (payloadWalk π p) (place (.inr (.inr (π p)),none)) ∧
    ((payloadWalk (S:=S) (d:=d) (k:=k) π p).map (coreLength (freeLength M))).sum = (Stages h d:ℝ) := by
  let : Nonempty (Fin K) := ⟨place (.inl p,none)⟩
  have segment := prefix_spec (S:=S) π p place M (Fin.last (Stages h d))
  have last := joint_trace (S:=S) π p (Fin.last (Stages h d)) none place
  rw [payloadFreeTo,Fin.lastCases_last] at last
  exact ⟨Traverses.append _ segment.1 last, by simpa [payloadWalk,jointEdge,coreLength,freeLength] using segment.2⟩

def commodityEnds (π : Equiv.Perm (Fin (2^h))) :
    Commodity (Fin (2^h)) (Stages h d) k → Site h d k × Site h d k
  | .inl p => ((.inl p,none),(.inr (.inr (π p)),none))
  | .inr ((p,t),l) =>
    let a := advisedStage h d π t
    ((inputCol t (a.group p) (a.input p),none),(outputCol t (a.group p) (a.output p),some l))

def commodityWalk (π : Equiv.Perm (Fin (2^h))) :
    Commodity (Fin (2^h)) (Stages h d) k → List (Edges S h d k)
  | .inl p => payloadWalk π p
  | .inr ((p,t),l) =>
    let a := advisedStage h d π t
    [tileEdge p t none,radiusEdge (outputCol t (a.group p) (a.output p)) l]

def commodityLength (M : ℝ) : Commodity (Fin (2^h)) (Stages h d) k → ℝ :=
  Sum.elim (fun _=> Stages h d) (fun _=>M+1)

theorem commodity_walk (π : Equiv.Perm (Fin (2^h))) (place : Site h d k → Fin K) (M : ℝ)
    (i : Commodity (Fin (2^h)) (Stages h d) k) :
    Traverses (graph (S:=S) π place) (place (commodityEnds π i).1) (commodityWalk π i)
      (place (commodityEnds π i).2) ∧
    ((commodityWalk (S:=S) π i).map (coreLength (freeLength M))).sum=commodityLength M i := by
  rcases i with p|⟨⟨p,t⟩,l⟩
  · exact payload_walk π p place M
  · let a := advisedStage h d π t
    exact ⟨Traverses.forward (G:=graph (S:=S) π place) (tileEdge p t none)
      (Traverses.forward (radiusEdge (outputCol t (a.group p) (a.output p)) l) (Traverses.nil _)),by
      simp [commodityWalk,tileEdge,radiusEdge,coreLength,freeLength,commodityLength,add_comm]⟩

def catalystWalk (c : Columns h d × Fin k) : List (Edges S h d k) :=
  [radiusEdge c.1 (c.2,false),radiusEdge c.1 (c.2,true)]

theorem catalyst_walk (π : Equiv.Perm (Fin (2^h))) (place : Site h d k → Fin K) (M : ℝ)
    (c : Columns h d × Fin k) :
    Traverses (graph (S:=S) π place) (place (c.1,some (c.2,false))) (catalystWalk c)
      (place (c.1,some (c.2,true))) ∧
    ((catalystWalk (S:=S) c).map (coreLength (freeLength M))).sum=2*M := by
  exact ⟨Traverses.backward (G:=graph (S:=S) π place) (radiusEdge c.1 (c.2,false))
    (Traverses.forward (radiusEdge c.1 (c.2,true)) (Traverses.nil _)), by
    simp [catalystWalk,radiusEdge,coreLength,freeLength,two_mul]⟩

end
end Hierarchy.ProbeStage.CoreBoard

end OAI
