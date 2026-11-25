import OAI.Hierarchy.FormulaPartitionRoute
import OAI.Hierarchy.FormulaPartitionKernelRun
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace OAI
/-! # Grouping a formula walk by its halving marks and slot partition -/

namespace Hierarchy.FormulaPartition

open scoped Classical BigOperators
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {τ : V → Type} {F : Type*} [Field F]
local notation "d" => Fintype.card V
local notation "t" => Nat.log 2 d

variable (ks : List (Kernel V τ F)) (tip : Leaf V τ F)

/-- Nonzero summands in the unrolled kernel run are heavy walks ending at a singleton. -/
def chainSlotWalk (a : ∀ v, τ v) (state : Fin (ks.length+1) → Finset V)
    (start : state 0 = Finset.univ) (nonzero : chainWeight ks a tip state ≠ 0) (pos : 0<d) :
    SlotWalk V ks.length := by
  change ((∏ i : Fin ks.length, (ks.get i).value a (state i.castSucc) (state i.succ)) *
    tip.value a (state (Fin.last _))) ≠ 0 at nonzero
  have along (i : Fin ks.length) : (ks.get i).value a (state i.castSucc) (state i.succ) ≠ 0 :=
    (Finset.prod_ne_zero_iff.mp (left_ne_zero_of_mul nonzero)) i (Finset.mem_univ i)
  have heavy (i : Fin ks.length) : (state i.castSucc).card ≤ 2*(state i.succ).card :=
    (ks.get i).heavy a _ _ (along i)
  have alive : ∀ i, 0 < (state i).card := by
    apply Fin.induction
    · simpa only [start, Finset.card_univ] using pos
    · intro i prev
      have growth := heavy i
      omega
  exact {
    state := state
    start := start
    finish := Nat.le_antisymm (tip.small a _ (right_ne_zero_of_mul nonzero)) (alive _)
    shrink := fun i => (ks.get i).subset a _ _ (along i)
    heavy := heavy }

/-- The tensor summand for prescribed marks, before separating its segments. -/
def markedWeight (π : FormulaPartitionRank.Partition V (t+1)) (pos : Positions t ks.length)
    (a : ∀v,τ v) : F :=
  ∑ state : Fin (ks.length+1) → Finset V,
    if FixedMarks π pos state then chainWeight ks a tip state else 0

/-- A partition whose tail exceeds a halving threshold cannot receive a summand. -/
theorem markedWeight_eq_zero_of_tail {π : FormulaPartitionRank.Partition V (t+1)}
    (pos : Positions t ks.length) (a : ∀v,τ v) (j : Fin (t+1))
    (large : threshold d j.val < (Finset.univ.filter (fun v => j≤π.val v)).card) :
    markedWeight ks tip π pos a = 0 := by
  apply Finset.sum_eq_zero
  intro state _
  apply ite_eq_right
  intro fixed
  have cut := (fixed j).2.1
  rw [(fixed j).1] at cut
  exact large.not_ge cut

/-- Summing all marked pieces counts each nonzero parse weight exactly once. -/
theorem run_eq_sum_markedWeight (a : ∀v,τ v) (positive : 0<d) :
    run a tip ks Finset.univ = ∑ π, ∑ pos, markedWeight ks tip π pos a := by
  rw [run_eq_sum_states]
  let term (state : Fin (ks.length+1) → Finset V)
      (π : FormulaPartitionRank.Partition V (t+1)) (pos : Positions t ks.length) :=
    if FixedMarks π pos state then chainWeight ks a tip state else 0
  calc
    _ = ∑ state, ∑ π, ∑ pos, term state π pos := by
      refine Finset.sum_congr rfl ?_
      intro state _
      by_cases nz : chainWeight ks a tip state = 0
      · simp [term,nz]
      by_cases hs : state 0 = Finset.univ
      · rw [ite_eq_left hs]
        let W := chainSlotWalk ks tip a state hs nz positive
        have tag (π) (pos) : FixedMarks π pos state ↔ π=W.partition ∧ pos=W.positions :=
          W.fixedMarks_iff π pos
        rw [Finset.sum_eq_single W.partition]
        · rw [Finset.sum_eq_single W.positions]
          · exact (ite_eq_left ((tag _ _).mpr ⟨rfl,rfl⟩)).symm
          · intro p _ ne
            exact ite_eq_right fun h => ne ((tag _ _).mp h).2
          · simp
        · intro π _ different
          apply Finset.sum_eq_zero
          intro p _
          exact ite_eq_right fun h => different ((tag _ _).mp h).1
        · simp
      · rw [ite_eq_right hs]
        symm
        apply Finset.sum_eq_zero
        intro π _
        apply Finset.sum_eq_zero
        intro pos _
        exact ite_eq_right fun h => hs (FixedMarks.start h)
    _ = ∑ π, ∑ state, ∑ pos, term state π pos := Finset.sum_comm
    _ = ∑ π, ∑ pos, markedWeight ks tip π pos a :=
      Finset.sum_congr rfl fun π _ => Finset.sum_comm

end
end Hierarchy.FormulaPartition

end OAI
