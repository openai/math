import OAI.Hierarchy.FormulaPartitionKernelRun
import OAI.Hierarchy.FormulaPartitionSegments
import Mathlib.Data.List.OfFn

namespace OAI
/-! # Path expansion with transition guards -/

namespace Hierarchy.FormulaPartition
open scoped BigOperators Classical
noncomputable section

variable {V : Type} {τ : V → Type} {F : Type*} [Field F] [DecidableEq V] [Fintype V]

/-- Each step tests its incoming and outgoing sets. -/
def follows {L : ℕ} (guard : Fin L → Finset V → Finset V → Prop)
    (W : Fin (L+1) → Finset V) : Prop :=
  ∀ i, guard i (W i.castSucc) (W i.succ)

omit [DecidableEq V] [Fintype V] in
theorem follows_cons {L : ℕ} (guard : Fin (L+1) → Finset V → Finset V → Prop)
    (S : Finset V) (T : Fin (L+1) → Finset V) :
    follows guard (Fin.cons S T) ↔ guard 0 S (T 0) ∧ follows (fun i => guard i.succ) T := by
  exact Fin.forall_fin_succ

private theorem walk_guarded_eq_tail (ks : List (Kernel V τ F)) (a : ∀v,τ v)
    (tip : Leaf V τ F) (S : Finset V) (guard : Fin ks.length → Finset V → Finset V → Prop) :
    walk (List.ofFn fun i => (ks.get i,guard i)) a S (tip.value a) =
    ∑ T : Fin ks.length → Finset V,
      if follows guard (Fin.cons S T) then chainWeight ks a tip (Fin.cons S T) else 0 := by
  induction ks generalizing S with
  | nil => simp [walk,follows,chainWeight,stateProduct]
  | cons k ks ih =>
    let step : Fin (ks.length+1) → GuardedStep V τ F := fun i => ((k::ks).get i,guard i)
    refine (congrArg (fun path : List (GuardedStep V τ F) => walk path a S (tip.value a))
      (List.ofFn_succ (f:=step))).trans ?_
    change (∑ U : Finset V, if guard 0 S U then
        k.value a S U * walk (List.ofFn fun i : Fin ks.length => (ks.get i,guard i.succ)) a U (tip.value a)
        else 0) =
      ∑ T : Fin (ks.length+1) → Finset V,
        if follows guard (Fin.cons S T) then chainWeight (k::ks) a tip (Fin.cons S T) else 0
    rw [sum_state_head (fun T =>
      if follows guard (Fin.cons S T) then chainWeight (k::ks) a tip (Fin.cons S T) else 0)]
    apply Finset.sum_congr rfl
    intro U _
    by_cases first : guard 0 S U
    · rw [ite_eq_left first, ih, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      simp only [follows_cons guard,Fin.cons_zero,first,true_and,chainWeight_cons]
      by_cases rest : follows (fun i => guard i.succ) (Fin.cons U T) <;> simp [rest]
    · simp [follows_cons guard,first]

/-- All masks are imposed on the same tuple whose transition values form the path coefficient. -/
theorem walk_guarded_eq_sum_states (ks : List (Kernel V τ F)) (a : ∀v,τ v)
    (tip : Leaf V τ F) (S : Finset V) (guard : Fin ks.length → Finset V → Finset V → Prop) :
    walk (List.ofFn fun i => (ks.get i,guard i)) a S (tip.value a) =
      ∑ W : Fin (ks.length+1) → Finset V,
        if W 0=S ∧ follows guard W then chainWeight ks a tip W else 0 := by
  rw [walk_guarded_eq_tail, sum_state_head (fun W =>
      if W 0=S ∧ follows guard W then chainWeight ks a tip W else 0)]
  simp only [Fin.cons_zero]
  symm
  rw [Finset.sum_eq_single S]
  · simp
  · intro U _ h
    simp [h]
  · simp


end
end Hierarchy.FormulaPartition

end OAI
