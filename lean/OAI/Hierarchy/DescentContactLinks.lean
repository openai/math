import OAI.Hierarchy.DescentContactTree

namespace OAI
/-! # Exceptional-side direct links and the two terminal trees -/

namespace Hierarchy.DescentContactTree
open scoped Classical BigOperators
noncomputable section
variable {I C : Type*} [Fintype I] [Fintype C]
variable {A : I → Type*} [∀ i,Fintype (A i)] {K : Type*} [CommSemiring K]

/-- Every old bundle is stored in the ordered sublist at its actual potential
contact. Empty contact lists carry the singleton alphabet. -/
def links (contact : I → C) (x y : ∀ i,A i) : K :=
  ∏ c : C, if ∀ i : {i // contact i=c},x i.val=y i.val then 1 else 0

omit [(i : I) → Fintype (A i)] in
theorem links_eq (contact : I → C) (x y : ∀ i,A i) :
    links (K:=K) contact x y=if x=y then 1 else 0 := by
  classical
  by_cases hit : x=y
  · subst y; simp [links]
  · rw [ite_eq_right hit]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hit
    apply Finset.prod_eq_zero (Finset.mem_univ (contact i))
    apply ite_eq_right
    intro all
    exact hi (all ⟨i,rfl⟩)

/-- Contract all inter-terminal leaves and internal tree variables. The one
surviving assignment is the prescribed tuple on every original bundle.
The two endpoints may use completely different destination codes. -/
theorem two_tree_contraction (contact : I → C) (l r : I → ℕ → Bool) (s t : ℕ)
    (x y : (i : I) → A i) :
    (∑ z : State A l s, ∑ w : State A r t,
      route (K:=K) s (packed A l 0 x) z *
      links (K:=K) contact ((packed A l s).symm z) ((packed A r t).symm w) *
      route t (packed A r 0 y) w) = if x=y then 1 else 0 := by
  classical
  rw [Finset.sum_eq_single_of_mem (packed A l s x) (Finset.mem_univ _)]
  · rw [Finset.sum_eq_single_of_mem (packed A r t y) (Finset.mem_univ _)]
    · simp [route_eq,links_eq]
    · intro w _ ne
      have diff : y≠(packed A r t).symm w := by
        intro h; apply ne; simpa using (congrArg (packed A r t) h).symm
      simp [route_eq,diff]
  · intro z _ ne
    have diff : x≠(packed A l s).symm z := by
      intro h; apply ne; simpa using (congrArg (packed A l s) h).symm
    simp [route_eq,diff]

/-- Contact direct-link and both relay-tree alphabets together spend one hop
per old bundle on the direct link and one hop per tree level on either end. -/
theorem two_tree_cost (contact : I → C) (wt : I → ℕ) (l r : I → ℕ → Bool) (s t : ℕ) :
    (∑ d∈Finset.range (s+1),∑ v : Node d,∑ i : Cell l d v,wt i.val)+
      (∑ c : C,∑ i : {i // contact i=c},wt i.val)+
      (∑ d∈Finset.range (t+1),∑ v : Node d,∑ i : Cell r d v,wt i.val)=
      (s+t+3)*(∑ i,wt i) := by
  rw [route_cost,route_cost,←Fintype.sum_sigma' (fun c (i : {i // contact i=c}) => wt i.val)]
  have bridge := (Equiv.sigmaFiberEquiv contact).sum_comp wt
  change (∑ e : Σ c,{i // contact i=c},wt e.2.val)=∑i,wt i at bridge
  rw [bridge]
  ring

end
end Hierarchy.DescentContactTree

end OAI
