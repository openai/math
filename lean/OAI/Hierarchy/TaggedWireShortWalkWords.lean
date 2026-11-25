import OAI.Hierarchy.TaggedWireSideSites

namespace OAI
/-! # Computing the literal sites and signed references of one- and two-hop packet turns -/

noncomputable section
namespace Hierarchy.WireTelescope.ShortWalk
open LinearAlgebra.SpectralBooks SiteTensor
open scoped Classical

variable {S : ℕ} {E : Type} (G : PortGraph (Fin S) E) {a b : Fin S} {es : List E}

/-- The sole possible internal turn is at the other end of the first
physical edge. Source, target, and both tails are actual site words. -/
def site (a b : Fin S) (xs : List E) (j : ℕ) : Fin S :=
  if j=0 then a else if j=xs.length then b else
    if has : 0<xs.length then
      let first := xs[0]'has
      if G.tail first=a then G.head first else G.tail first
    else a

def left (s : Fin S) (xs : List E) (j : ℕ) : TurnRef :=
  if j=0 then .inl false else if h : j-1<xs.length then
    .inr (j-1,decide (G.tail (xs[j-1]'h)≠s)) else .inl false

def right (s : Fin S) (xs : List E) (j : ℕ) : TurnRef :=
  if h : j<xs.length then .inr (j,decide (G.tail (xs[j]'h)≠s)) else .inl true

theorem site_eq (sp : Spine G a es b) (short : es.length≤2) (j : Fin (es.length+1)) :
    site G a b es j.val=sp.visit j := by
  by_cases start : j.val=0
  · have eq : j=0 := Fin.ext start
    simp [site,eq]
  by_cases last : j.val=es.length
  · have eq : j=Fin.last es.length := Fin.ext last
    simpa only [site,ite_eq_right start,ite_eq_left last] using ((congrArg sp.visit eq).trans sp.visit_last).symm
  have len : es.length=2 := by have := j.isLt;omega
  let q : Fin es.length := ⟨0,by omega⟩
  have one : q.succ=j := Fin.ext (by have := j.isLt;change 0+1=j.val;omega)
  obtain ⟨t,_,_,before,after⟩ := Spine.adjacent sp (.inl false) (.inl true) 0 q
  have zero : q.castSucc=0 := Fin.ext rfl
  rw [zero,Spine.visit_zero] at before
  rw [one] at after
  simp only [site,ite_eq_right start,ite_eq_right last,dite_eq_left (by omega : 0<es.length)]
  change (if G.tail (es.get q)=a then G.head (es.get q) else G.tail (es.get q))=_
  calc
    _ = (if G.tail (es.get q)=G.vertex (es.get q) t then G.head (es.get q) else G.tail (es.get q)) :=
      congrArg (fun start => if G.tail (es.get q)=start then G.head (es.get q) else G.tail (es.get q)) before
    _ = G.vertex (es.get q) (!t) := by
      have other (v : E) (side : Bool) :
          (if G.tail v=G.vertex v side then G.head v else G.tail v) = G.vertex v (!side) := by
        cases side <;> by_cases loop : G.tail v=G.head v <;> simp [PortGraph.vertex,loop]
      exact other _ _
    _ = _ := after.symm

theorem sides_eq (sp : Spine G a es b) (diff : ∀i,G.tail i≠G.head i) (j : Fin (es.length+1)) :
    (left G (sp.visit j) es j.val,right G (sp.visit j) es j.val)=sp.sides (.inl false) (.inl true) 0 j := by
  apply Prod.ext
  · by_cases h : j.val=0
    · have q : j=0 := Fin.ext h
      simp [q,left]
    · let q : Fin es.length := ⟨j.val-1,by have := j.isLt;omega⟩
      have eq : q.succ=j := Fin.ext (by change j.val-1+1=j.val;omega)
      have rr := Spine.signed_in sp diff (.inl false) (.inl true) 0 q
      rw [eq] at rr
      have below : j.val-1<es.length := q.isLt
      simpa only [left,ite_eq_right h,dite_eq_left below,Nat.zero_add,List.get_eq_getElem,q] using rr.symm
  · by_cases h : j.val<es.length
    · let q : Fin es.length := ⟨j.val,h⟩
      have eq : q.castSucc=j := Fin.ext rfl
      have rr := Spine.signed_out sp diff (.inl false) (.inl true) 0 q
      rw [eq] at rr
      simpa only [right,dite_eq_left h,Nat.zero_add,List.get_eq_getElem,q] using rr.symm
    · have eq : j=Fin.last es.length := Fin.ext (by change j.val=es.length;have := j.isLt;omega)
      rw [show right G (sp.visit j) es j.val=Sum.inl true by simp [right,h],eq,Spine.sides_last]

end Hierarchy.WireTelescope.ShortWalk

end
end OAI
