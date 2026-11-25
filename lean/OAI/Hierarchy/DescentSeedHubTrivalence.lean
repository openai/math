import OAI.Hierarchy.DescentSeedGeometry
import OAI.Hierarchy.DescentHubNetwork

namespace OAI
/-! # Trivalence of the seed network with its attached hubs -/
namespace Hierarchy.DescentSeedRoot
open Hierarchy.DescentInitialHost Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

private theorem degree_sum {D : ℕ} {P : Type} [Fintype P] (N : Network D P (fun _ => 1)) (v : N.Site) :
    N.bitDegree v = (∑ p : P, if N.attach p = v then 1 else 0) +
      ∑ e : N.Edge, ((if N.src e = v then 1 else 0) + (if N.dst e = v then 1 else 0)) := by
  have counted {α : Type} (s : Finset α) (p : α → Prop) [DecidablePred p] :
      (s.filter p).card = ∑ e ∈ s, if p e then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp
  unfold Network.bitDegree
  rw [counted]
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool,
    Sum.elim_inl,Sum.elim_inr,Bool.false_eq_true,ite_false,ite_true,Nat.add_comm]
  apply congrArg₂ Nat.add <;> apply Finset.sum_congr rfl <;> intro x _ <;> split_ifs <;> first | rfl | exact ite_eq_left (by assumption) | exact ite_eq_right (by assumption)

private theorem hub_degree {D : ℕ} {P : Type} [Fintype P] (N : Network D P (fun _=>1)) (v : Site N) :
    (hubbed N).bitDegree v=incidenceLoad N 1 1 v + (if hubFlag N v then 1 else 0) := by
  refine (degree_sum (hubbed N) v).trans ?_
  rw [Finset.sum_add_distrib,Nat.add_comm]
  apply congrArg₂ Nat.add
  · unfold incidenceLoad
    apply congrArg₂ Nat.add
    · apply Finset.sum_congr (by ext z; exact ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩)
      intro e _
      by_cases eqn : source N e = v
      · simp [hubbed,eqn]
      · simp [hubbed,eqn,Ne.symm eqn]
    · apply Finset.sum_congr (by ext z; exact ⟨fun _ => Finset.mem_univ _, fun _ => Finset.mem_univ _⟩)
      intro e _
      by_cases eqn : target N e = v
      · simp [hubbed,eqn]
      · simp [hubbed,eqn,Ne.symm eqn]
  · cases v <;> simp [hubbed,hubFlag]

theorem hubbed_trivalent {D : ℕ} {P : Type} [Fintype P] (N : Network D P (fun _=>1))
    (tri : N.Trivalent) : (hubbed N).Trivalent := by
  refine ⟨hub_unit N tri,?_⟩
  rintro (v|p)
  · simpa [hub_degree,inside_load,hubFlag] using tri.2 v
  · simp [hub_degree,hub_load,hubFlag]

end
end Hierarchy.DescentSeedRoot

end OAI
