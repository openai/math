import OAI.Hierarchy.FormulaPartitionMask
import OAI.Hierarchy.FormulaPartitionRank
import OAI.Hierarchy.FormulaPartitionMarks

namespace OAI
/-! # Exact identification of the marks and slot partition of a heavy walk -/

namespace Hierarchy.FormulaPartition

open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] {L : ℕ}
local notation "d" => Fintype.card V
local notation "t" => Nat.log 2 d

/-- The state at each marked position is its prescribed color tail. At each
noninitial mark the parent lies strictly above the same halving threshold. -/
def FixedMarks (π : FormulaPartitionRank.Partition V (t+1)) (pos : Positions t L)
    (state : Fin (L+1) → Finset V) : Prop :=
  ∀ j, state (pos.val j) = Finset.univ.filter (fun v => j ≤ π.val v) ∧
    (state (pos.val j)).card ≤ threshold d j.val ∧
    ∀ i : Fin L, i.succ = pos.val j → threshold d j.val < (state i.castSucc).card

theorem FixedMarks.start {π : FormulaPartitionRank.Partition V (t+1)} {pos : Positions t L}
    {state : Fin (L+1) → Finset V} (fixed : FixedMarks π pos state) :
    state 0 = Finset.univ := by
  have start := (fixed 0).1
  simpa only [pos.property.2, Fin.zero_le, Finset.filter_true] using start

/-- The arrival test at an edge is silent unless this edge reaches a mark. -/
def edgeGuard (π : FormulaPartitionRank.Partition V (t+1)) (pos : Positions t L)
    (i : Fin L) (S T : Finset V) : Prop :=
  ∀ j, i.succ = pos.val j →
    T = Finset.univ.filter (fun v => j ≤ π.val v) ∧
    T.card ≤ threshold d j.val ∧ threshold d j.val < S.card

theorem fixedMarks_iff_edgeGuards (π : FormulaPartitionRank.Partition V (t+1))
    (pos : Positions t L) (state : Fin (L+1) → Finset V) :
    FixedMarks π pos state ↔ state 0 = Finset.univ ∧
      ∀ i : Fin L, edgeGuard π pos i (state i.castSucc) (state i.succ) := by
  constructor
  · intro fixed
    refine ⟨fixed.start, ?_⟩
    intro i j hi
    exact ⟨by rw [hi]; exact (fixed j).1, by rw [hi]; exact (fixed j).2.1,
      (fixed j).2.2 i hi⟩
  · rintro ⟨start,edge⟩ j
    by_cases first : pos.val j=0
    · have origin : j=0 := pos.property.1.injective (first.trans pos.property.2.symm)
      subst j
      have hit : (state (pos.val 0)).card ≤ threshold d 0 := by
        rw [first,start,Finset.card_univ,threshold_zero]
      refine ⟨?_,hit,?_⟩
      · rw [first,start]
        simp
      · intro i impossible
        exact (Fin.succ_ne_zero i (impossible.trans first)).elim
    · have positive : 0 < (pos.val j).val := by
        by_contra! h
        exact first (Fin.ext (Nat.eq_zero_of_le_zero h))
      let i : Fin L := ⟨(pos.val j).val-1,by have := (pos.val j).isLt; omega⟩
      have hi : i.succ=pos.val j := by
        apply Fin.ext
        change (pos.val j).val-1+1=(pos.val j).val
        omega
      obtain ⟨endState,small,before⟩ := edge i j hi
      rw [hi] at endState small
      exact ⟨endState, small, fun k hk => (edge k j hk).2.2⟩

namespace SlotWalk

variable (W : SlotWalk V L)

def partition : FormulaPartitionRank.Partition V (t+1) := ⟨W.color, W.color_surjective⟩

def positions : Positions t L := ⟨W.mark, W.mark_strictMono, W.mark_zero⟩

theorem fixedMarks : FixedMarks W.partition W.positions W.state := by
  intro j
  refine ⟨W.marked_eq_color_tail j, W.mark_card j, ?_⟩
  intro i hi
  apply W.before_mark
  change i.succ = W.mark j at hi
  rw [← hi]
  exact Fin.castSucc_lt_succ

private theorem mark_eq_position {π : FormulaPartitionRank.Partition V (t+1)} {pos : Positions t L}
    (fixed : FixedMarks π pos W.state) (j : Fin (t+1)) : W.mark j = pos.val j := by
  have crossing := fixed j
  by_cases zero : pos.val j = 0
  · apply le_antisymm (W.mark_le j _ crossing.2.1)
    rw [zero]
    exact Fin.zero_le _
  · have positive : 0 < (pos.val j).val := by
      by_contra! h
      exact zero (Fin.ext (Nat.eq_zero_of_le_zero h))
    let i : Fin L := ⟨(pos.val j).val - 1,by have := (pos.val j).isLt; omega⟩
    have next : i.succ = pos.val j := by
      apply Fin.ext
      change (pos.val j).val - 1 + 1 = (pos.val j).val
      omega
    rw [← next]
    apply (W.mark_eq_iff_crossing j i).mpr
    exact ⟨by rw [next]; exact crossing.2.1, crossing.2.2 i next⟩

/-- Exactly one pair of a surjective slot coloring and a mask of positions
passes all the local crossing and endpoint tests for this walk. -/
theorem fixedMarks_iff (π : FormulaPartitionRank.Partition V (t+1)) (pos : Positions t L) :
    FixedMarks π pos W.state ↔ π = W.partition ∧ pos = W.positions := by
  constructor
  · intro fixed
    have marked := W.mark_eq_position fixed
    refine ⟨Subtype.ext (funext fun v => ?_), Subtype.ext (funext fun j => (marked j).symm)⟩
    have cuts (j : Fin (t+1)) : j ≤ W.color v ↔ j ≤ π.val v := by
      rw [← W.mem_marked]
      change v ∈ W.state (W.mark j) ↔ _
      rw [marked j, (fixed j).1]
      simp
    exact le_antisymm ((cuts (π.val v)).mpr le_rfl) ((cuts (W.color v)).mp le_rfl)
  · rintro ⟨rfl,rfl⟩
    exact W.fixedMarks

end SlotWalk
end
end Hierarchy.FormulaPartition

end OAI
