import OAI.Hierarchy.FormulaPartitionGuardRun
import OAI.Hierarchy.FormulaPartitionSegmentPositions
import OAI.Hierarchy.FormulaPartitionWalk

namespace OAI
/-! # The guarded transfer at prescribed halving marks -/

namespace Hierarchy.FormulaPartition
open scoped BigOperators Classical
noncomputable section

variable {V : Type} {τ : V → Type} {F : Type*} [Field F] [DecidableEq V] [Fintype V]
local notation "d" => Fintype.card V
local notation "t" => Nat.log 2 d

private def zeroKernel : Kernel V τ F where
  value := fun _ _ _ => 0
  subset := by simp
  heavy := by simp
  locality := by simp

/-- During a marked arrival, enforce the first threshold crossing across its incoming step. -/
def routeSteps (ks : List (Kernel V τ F)) (pos : Positions t ks.length) (i : ℕ) :
    GuardedStep V τ F :=
  (if h : i < ks.length then ks.get ⟨i,h⟩ else zeroKernel,
   fun S T => ∀ j, i+1 = (pos.val j).val →
     T.card ≤ threshold d j.val ∧ threshold d j.val < S.card)

/-- At each mark record precisely the tail of the prescribed slot coloring. -/
def routePin {L : ℕ} (π : FormulaPartitionRank.Partition V (t+1)) (pos : Positions t L)
    (m : ℕ) (T : Finset V) : Prop :=
  ∀ j, m = (pos.val j).val → T=Finset.univ.filter (fun v => j≤π.val v)

omit [Fintype V] in
private theorem intervalSteps_zero_ofFn (steps : ℕ → GuardedStep V τ F) (n : ℕ) :
    intervalSteps steps 0 n = List.ofFn (fun j : Fin n => steps j.val) := by
  apply List.ext_getElem <;> simp [intervalSteps]

private theorem route_guard_list (ks : List (Kernel V τ F)) (π : FormulaPartitionRank.Partition V (t+1))
    (pos : Positions t ks.length) :
    intervalSteps (applyPin (routeSteps ks pos) (routePin π pos)) 0 ks.length =
      List.ofFn (fun i => (ks.get i,edgeGuard π pos i)) := by
  rw [intervalSteps_zero_ofFn]
  apply congrArg List.ofFn
  funext i
  apply Prod.ext
  · simp only [applyPin,routeSteps,dite_eq_left i.isLt]
  · funext S T
    apply propext
    constructor
    · rintro ⟨cross,pin⟩ j hit
      have atTime : i.val+1=(pos.val j).val := congrArg Fin.val hit
      exact ⟨pin j atTime,cross j atTime⟩
    · intro hed
      exact ⟨fun j eqn => (hed j (Fin.ext eqn)).2, fun j eqn => (hed j (Fin.ext eqn)).1⟩

/-- The coefficient selected by a particular partition and set of positions is the
guarded path transfer. Its pins fix each segment boundary, while each transition
checks the local halving inequality only when it arrives at a mark. -/
theorem markedWeight_eq_walk (ks : List (Kernel V τ F)) (tip : Leaf V τ F)
    (π : FormulaPartitionRank.Partition V (t+1)) (pos : Positions t ks.length) (a : ∀v,τ v) :
    markedWeight ks tip π pos a =
      walk (intervalSteps (applyPin (routeSteps ks pos) (routePin π pos)) 0 ks.length)
        a Finset.univ (tip.value a) := by
  rw [route_guard_list,walk_guarded_eq_sum_states]
  unfold markedWeight
  apply Finset.sum_congr rfl
  intro state _
  rw [fixedMarks_iff_edgeGuards]
  by_cases guarded : state 0=Finset.univ ∧ follows (edgeGuard π pos) state <;>
    simp only [follows] at guarded ⊢ <;> simp only [guarded,ite_false]


end
end Hierarchy.FormulaPartition

end OAI
