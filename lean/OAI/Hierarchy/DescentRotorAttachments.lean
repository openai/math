import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace OAI
/-! # Realizing a local rotor table on a path of three-port sites

Each tap compares two packed copies of the whole tuple and checks one coordinate
against the external row. The first end supplies the coefficient; the other end
has coefficient one. The tuple uses one bit for each bit of the original local
state. The number of taps depends only on the host degree.
-/

namespace Hierarchy.DescentRotor.Attachment
open scoped Classical BigOperators
noncomputable section
variable {n : ℕ} {A : Fin n → Type*} {K : Type*} [CommSemiring K]

/-- The two path connections and a single row are the three arguments of a tap. -/
def tap (i : Fin n) (x : A i) (left right : (j : Fin n) → A j) : K :=
  if left=right ∧ left i=x then 1 else 0

/-- Internal path wire k carries a packed tuple. The two open ends each use
one edge. Every intermediate site sees its own external row and two path wires. -/
def spine [∀ i, Fintype (A i)] (table : ((i : Fin n) → A i) → K) (x : (i : Fin n) → A i) : K :=
  ∑ h : Fin (n+1) → (i : Fin n) → A i,
    table (h 0) * ∏ i, tap i (x i) (h i.castSucc) (h i.succ)

private theorem agree {x : (i : Fin n) → A i} {h : Fin (n+1) → (i : Fin n) → A i}
    (all : ∀ i : Fin n, h i.castSucc=h i.succ ∧ h i.castSucc i=x i) :
    h=fun _ => x := by
  have same (k : Fin (n+1)) : h k=h 0 :=
    Fin.induction rfl (fun j ih => (all j).1.symm.trans ih) k
  have base : h 0=x := by
    funext i
    exact (congrFun (same i.castSucc).symm i).trans (all i).2
  funext k
  exact (same k).trans base

/-- Summing the path's internal states yields the actual arbitrary local table;
the constant assignment equal to the external tuple uniquely survives. -/
theorem spine_eq [∀ i, Fintype (A i)] (table : ((i : Fin n) → A i) → K) (x : (i : Fin n) → A i) :
    spine table x=table x := by
  unfold spine
  rw [Finset.sum_eq_single_of_mem (fun _ => x) (Finset.mem_univ _)]
  · simp [tap]
  · intro h mem diff
    have bad : ∃ i : Fin n, ¬(h i.castSucc=h i.succ ∧ h i.castSucc i=x i) := by
      by_contra! all
      exact diff (agree all)
    obtain ⟨i,hi⟩ := bad
    have z : tap (K:=K) i (x i) (h i.castSucc) (h i.succ)=0 := ite_eq_right hi
    rw [Finset.prod_eq_zero (Finset.mem_univ i) z,mul_zero]

/-- The n+1 internal path wires carry the entire tuple, and the n external
wires carry one coordinate apiece. Tensoring u times repeats every bit u times. -/
def bitCost (w : Fin n → ℕ) (u : ℕ) :=
  (∑ _ : Fin (n+1), (∑ i, w i)*u) + ∑ i, w i*u

theorem bitCost_eq (w : Fin n → ℕ) (u : ℕ) :
    bitCost w u=(n+2)*(∑ i, w i)*u := by
  simp [bitCost,← Finset.sum_mul]
  ring

/-- The two end sites have one path neighbor. Each interior site has two path
neighbors and one external neighbor, including the sites that carry the two
attachment rows. Overlaps among these neighbors can only lower the degree. -/
theorem degree_le_three {S : Type*} [DecidableEq S] (left right external : Option S) :
    (left.toFinset ∪ right.toFinset ∪ external.toFinset).card≤3 := by
  calc
    _ ≤ (left.toFinset ∪ right.toFinset).card + external.toFinset.card := Finset.card_union_le _ _
    _ ≤ left.toFinset.card + right.toFinset.card + external.toFinset.card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ 3 := by cases left <;> cases right <;> cases external <;> simp

end
end Hierarchy.DescentRotor.Attachment

end OAI
