import OAI.ThreeFlat.Diagonal.HistoryReplayCost

namespace OAI
/-! # Counting each local table and guessed bit once in an adaptive history -/

namespace ThreeFlat.Diagonal.HistoryContraction

open scoped BigOperators Classical

namespace Stage

variable {F Pins : Type*} [CommSemiring F] {S : Shape} {R : Rewrite S F} {t : Fin R.count}
    {V : Form S Pins} {W : Form (R.target t) Pins}

/-- Local work includes the trivalent records and all guessed half-ports. -/
def treeWork {p : ℕ} (n : Tree F p) := n.bits + n.rows + n.nodes

def overhead (a : Stage R t V W) (v : (R.target t).Site) := 1 + a.hidden v + treeWork (a.root v)

private theorem nodes_assemble (a : Stage R t V W) (N : Forest F V) (v : (R.target t).Site) :
    (a.assemble N v).nodes = 1 + ((a.root v).nodes + ∑ i, (N (a.child v i).val).nodes) := by
  unfold assemble
  rw [Tree.nodes,Fin.sum_univ_succ]
  rfl

theorem work_assemble (a : Stage R t V W) (N : Forest F V) (v : (R.target t).Site) :
    treeWork (a.assemble N v) = a.overhead v + ∑ i, treeWork (N (a.child v i).val) := by
  simp only [treeWork, overhead, assemble_bits, assemble_rows, nodes_assemble, Finset.sum_add_distrib]
  omega

/-- No old operand with multiple wires can be charged to multiple parents. -/
theorem sum_children (a : Stage R t V W) (f : S.Site → ℕ) :
    (∑ v, ∑ i, f (a.child v i).val) = ∑ i, f i := by
  calc
    _ = ∑ v, ∑ i : {i // R.owner t i = v}, f i.val := by
      apply Finset.sum_congr rfl
      intro v _
      exact (a.child v).sum_comp (fun j => f j.val)
    _ = _ := Fintype.sum_fiberwise (R.owner t) f

theorem sum_work_assemble (a : Stage R t V W) (N : Forest F V) :
    (∑ v, treeWork (a.assemble N v)) = (∑ v, a.overhead v) + ∑ i, treeWork (N i) := by
  simp only [work_assemble, Finset.sum_add_distrib]
  rw [a.sum_children (fun i => treeWork (N i))]

/-- The maximum per-cell work grows by the explicitly bounded number of
children, irrespective of the total population at that stage. -/
theorem work_assemble_le (a : Stage R t V W) (N : Forest F V) (v : (R.target t).Site)
    (cost k d : ℕ) (current : a.overhead v ≤ cost) (children : a.count v ≤ d)
    (old : ∀ i, treeWork (N i) ≤ k) : treeWork (a.assemble N v) ≤ cost + d*k := by
  rw [work_assemble]
  apply Nat.add_le_add current
  calc
    (∑ i, treeWork (N (a.child v i).val)) ≤ ∑ _i : Fin (a.count v), k :=
      Finset.sum_le_sum fun i _ => old _
    _ = a.count v * k := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ children

end Stage

namespace Plan

variable {F Pins : Type*} [CommSemiring F] {S : Shape}

/-- A numerical work budget from the chosen records and their topologies. -/
def stageWork : {S : Shape} → (P : Plan F S) → (h : P.History) → {V : Form S Pins} →
    P.Assembly V → ℕ
  | _, .done _, _, _, _ => 0
  | _, .step _ next, h, _, A => (∑ v, (A h.1).2.1.overhead v) +
    (next h.1).stageWork h.2 (A h.1).2.2

/-- Exact global work, including every original leaf, every kernel and all
new private half-ports encountered between the leaves and the terminal cells. -/
theorem sum_work (P : Plan F S) (h : P.History) {V : Form S Pins} (A : P.Assembly V)
    (N : Forest F V) :
    (∑ j, Stage.treeWork ((P.assemble h A N).2 j)) = P.stageWork h A + ∑ i, Stage.treeWork (N i) := by
  induction P with
  | done S => exact (Nat.zero_add _).symm
  | step R next ih =>
    obtain ⟨t,h⟩ := h
    change (∑ j, Stage.treeWork (((next t).assemble h (A t).2.2 ((A t).2.1.assemble N)).2 j)) = _
    rw [ih,Stage.sum_work_assemble]
    change _ = ((∑ v, (A t).2.1.overhead v) + (next t).stageWork h (A t).2.2) + _
    omega

end Plan
end ThreeFlat.Diagonal.HistoryContraction

end OAI
