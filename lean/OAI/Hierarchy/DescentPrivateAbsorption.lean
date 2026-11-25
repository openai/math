import OAI.Hierarchy.DescentNetworkPartition

namespace OAI
/-! # Identifying the precise physical cables absorbed by a pair of site quotients -/

namespace Hierarchy.DescentHistoryOrder
open Computability.BorderVNP.Crossing DescentNetworkPartition
open scoped Classical BigOperators
noncomputable section

variable {P U V K : Type} {D d : ℕ} {bits : P→ℕ} (N : Network D P bits)
section
variable [Fintype V] (loc : N.Site→V)

/-- Every internalized cable is named by both its actual old edge and its unique receiving site. -/
def absorbed := ∑v,∑e : PrivateEdge N loc v,N.width e.val

end

variable [Fintype U] [Fintype V] (loc : N.Site→U)

private def absorbedEdges : (Σu,PrivateEdge N loc u) ≃ {e : N.Edge // loc (N.src e)=loc (N.dst e)} where
  toFun t := ⟨t.2.val,t.2.property.1.trans t.2.property.2.symm⟩
  invFun e := ⟨loc (N.src e.val),⟨e.val,rfl,e.property.symm⟩⟩
  left_inv := by rintro ⟨u,⟨e,hs,hd⟩⟩; subst u; rfl
  right_inv _ := rfl

theorem absorbed_eq_test : absorbed N loc=∑e,if loc (N.src e)=loc (N.dst e) then N.width e else 0 := by
  unfold absorbed
  rw [←Fintype.sum_sigma' (fun u (e : PrivateEdge N loc u)=>N.width e.val)]
  let same (e : N.Edge) := loc (N.src e)=loc (N.dst e)
  calc
    _ = ∑e : {e // same e},N.width e.val := (absorbedEdges N loc).sum_comp (fun e=>N.width e.val)
    _ = _ := by
      rw [←Finset.sum_subtype (Finset.univ.filter same) (fun _=>by simp) N.width,Finset.sum_filter]

/-- Collapsing two quotients charges each raw edge whose composite endpoints coincide exactly once. -/
theorem absorbed_comp (next : U→V) (pos : U→EuclideanSpace ℝ (Fin d)) (room : ∀u,‖pos u‖≤1) :
    absorbed N loc+absorbed (quotient N loc pos room) next=absorbed N (next ∘ loc) := by
  let same (e : N.Edge) := loc (N.src e)=loc (N.dst e)
  let weight (e : N.Edge) := if next (loc (N.src e))=next (loc (N.dst e)) then N.width e else 0
  rw [absorbed_eq_test N (next ∘ loc),absorbed_eq_test (quotient N loc pos room) next]
  change absorbed N loc+(∑e : {e // ¬same e},weight e.val)=∑e,weight e
  rw [←Fintype.sum_subtype_add_sum_subtype same weight]
  congr 1
  calc
    _ = ∑e : {e // same e},N.width e.val := by
      unfold absorbed
      rw [←Fintype.sum_sigma' (fun u (e : PrivateEdge N loc u)=>N.width e.val)]
      exact (absorbedEdges N loc).sum_comp (fun e=>N.width e.val)
    _ = _ := Finset.sum_congr rfl (fun e _=>by
      have h : loc (N.src e.val)=loc (N.dst e.val) := e.property
      simp only [weight,h,ite_true])

/-- Machine words store an injective name of each site of the final quotient. -/
theorem two_owner_sum [DecidableEq K] (next : U→V) (id : V↪K)
    (pos : U→EuclideanSpace ℝ (Fin d)) (room : ∀u,‖pos u‖≤1) :
    (∑e,if id (next (loc (N.src e)))=id (next (loc (N.dst e))) then N.width e else 0)=
      absorbed N loc+absorbed (quotient N loc pos room) next := by
  rw [absorbed_comp N loc next pos room,absorbed_eq_test]
  simp only [Function.comp_apply,EmbeddingLike.apply_eq_iff_eq]

end
end Hierarchy.DescentHistoryOrder

end OAI
