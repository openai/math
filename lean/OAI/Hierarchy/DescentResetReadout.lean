import OAI.Hierarchy.DescentResetAttachments
import OAI.Hierarchy.DescentNetworkWorld
import OAI.Hierarchy.DescentResetSplicePrice

namespace OAI
/-! # Coefficient preservation and the tether invoice of the configured reset -/

namespace Hierarchy.DescentResetAttachments
open DescentRouterBank DescentNamedContact DescentSixParty Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section

variable {n d : ℕ} {P : Type*} {bits : P→ℕ} (N : Network n P bits)
variable {Q : Type} [Fintype Q] (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (poolWidth N group))
variable {K : Type*} [CommSemiring K] (T : N.Tables K) (S : R.Tables K)

omit [Fintype Q] in
/-- The measured router equates the entire outgoing and incoming word of each
old cable, including loops and ports shared by several old actors. -/
theorem value_eq (bank : ∀p,R.value S p=
    if publicRows group N.width p false=publicRows group N.width p true then 1 else 0)
    (x : Ports bits) : (network N group R).value (tables N group R T S) x=N.value T x := by
  rw [value_expand,←(Equiv.boolArrowEquivProd N.Assignment).symm.sum_comp,Fintype.sum_prod_type]
  change (∑a : N.Assignment, ∑b : N.Assignment, _) =
    ∑a : N.Assignment,∏v,N.read T a x v
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · simp [bank,publicRows_words,Equiv.boolArrowEquivProd]
    rfl
  · intro b _ neq
    simp [bank,publicRows_words,Equiv.boolArrowEquivProd,Ne.symm neq]
  · simp

variable {F : Type*} [Field F] (A : MarkedWorld F n P bits)
variable (g : Bool→A.graph.Edge→Q)
variable (r : Network d (Bool×Q) (poolWidth A.graph g)) (s : r.Tables F)
variable (hub : A.graph.Site→Bool)

def nextHub : (network A.graph g r).Site→Bool := Sum.elim hub (fun _=>false)

def resetWorld : MarkedWorld F d P bits :=
  ⟨⟨network A.graph g r,tables A.graph g r A.tables s⟩,
   Finset.univ.filter (fun e=>match e with
     | .inl q=>hub (ends A.graph q.1 q.2)=false | .inr _=>True)⟩

omit [Fintype Q] [Field F] in
private theorem mem_reset_core (e : (resetWorld A g r s hub).graph.Edge) :
    e ∈ (resetWorld A g r s hub).core ↔
      match e with
      | .inl q => hub (ends A.graph q.1 q.2) = false
      | .inr _ => True := by
  cases e <;> constructor
  all_goals first
    | exact fun he => (Finset.mem_filter.mp he).2
    | exact fun h => Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩

omit [Fintype Q] in
theorem reset_value (bank : ∀p,r.value s p=
    if publicRows g A.graph.width p false=publicRows g A.graph.width p true then 1 else 0)
    (x : Ports bits) : (resetWorld A g r s hub).value x=A.value x :=
  value_eq A.graph g r A.tables s bank x

omit [Fintype Q] [Field F] in
theorem marked_endpoints (e : (resetWorld A g r s hub).graph.Edge) :
    (e∈(resetWorld A g r s hub).core →
      nextHub A g r hub ((network A.graph g r).src e)=false ∧ nextHub A g r hub ((network A.graph g r).dst e)=false) ∧
    (e∉(resetWorld A g r s hub).core →
      nextHub A g r hub ((network A.graph g r).src e)≠nextHub A g r hub ((network A.graph g r).dst e)) := by
  rcases e with q|e
  · have tag : Sum.inl q ∈ (resetWorld A g r s hub).core ↔ hub (ends A.graph q.1 q.2) = false :=
      mem_reset_core A g r s hub (.inl q)
    cases eqn : hub (ends A.graph q.1 q.2) <;> simp [nextHub,eqn]
    · exact tag.mpr eqn
    · exact fun he => Bool.noConfusion (eqn.symm.trans (tag.mp he))
  · have tag : Sum.inr e ∈ (resetWorld A g r s hub).core :=
      (mem_reset_core A g r s hub (.inr e)).2 trivial
    simp [nextHub]
    exact tag

omit [Fintype Q] [Field F] in
theorem reset_tether
    (inside : ∀e∈A.core,hub (A.graph.src e)=false ∧ hub (A.graph.dst e)=false)
    (outside : ∀e∉A.core,hub (A.graph.src e)≠hub (A.graph.dst e)) :
    (resetWorld A g r s hub).tetherWidth=A.tetherWidth := by
  let M := network A.graph g r
  let W := resetWorld A g r s hub
  have project : W.tetherWidth=
      ∑e : M.Edge,match e with
        | .inl p => if hub (ends A.graph p.1 p.2) then A.graph.width p.2 else 0 | .inr _=>0 := by
    unfold MarkedWorld.tetherWidth
    have repr : W.coreᶜ=Finset.univ.filter (fun e=>e∉W.core) := by ext; simp
    rw [repr,Finset.sum_filter]
    apply Finset.sum_congr rfl
    rintro (p|e) _
    · have tag : Sum.inl p ∈ W.core ↔ hub (ends A.graph p.1 p.2) = false :=
        mem_reset_core A g r s hub (.inl p)
      cases eqn : hub (ends A.graph p.1 p.2) with
      | false =>
        split
        · rename_i h
          exact False.elim (h (tag.mpr eqn))
        · simp [eqn]
      | true =>
        split
        · simp [W,resetWorld,network,eqn]
        · rename_i h
          exact False.elim (h (fun he => Bool.noConfusion (eqn.symm.trans (tag.mp he))))
    · have tag : Sum.inr e ∈ W.core := (mem_reset_core A g r s hub (.inr e)).2 trivial
      simp
      exact fun he => False.elim (he tag)
  rw [project,Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool]
  simp only [Finset.sum_const_zero,add_zero,←Finset.sum_add_distrib]
  unfold MarkedWorld.tetherWidth
  have repr : A.coreᶜ=Finset.univ.filter (fun e=>e∉A.core) := by ext; simp
  rw [repr,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : e∈A.core
  · obtain ⟨src,dst⟩ := inside e he
    simp [ends,src,dst,he]
  · have diff := outside e he
    cases src : hub (A.graph.src e) <;> cases dst : hub (A.graph.dst e) <;>
      simp [src,dst,he,ends] at diff ⊢

omit [Field F] [Fintype Q] in
theorem reset_cost :
    (resetWorld A g r s hub).liveWidth ≤ (∑e,r.width e)+2*(A.liveWidth+A.tetherWidth) := by
  have old : A.liveWidth+A.tetherWidth=∑e,A.graph.width e := Finset.sum_add_sum_compl A.core _
  rw [old,← total_width A.graph g r]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end
end Hierarchy.DescentResetAttachments

end OAI
