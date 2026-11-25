import OAI.Computability.NearSquareRoot.KernelPassAxes
import OAI.Computability.NearSquareRoot.KernelPassBank

/-! # Indexed banks of independent singleton plans

Fixed finite row sets can be numbered before the address width is selected.
The entry blocks of the resulting plan multiply over the intermediate row set.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass.Rect

open Matrix Finset
open scoped BigOperators

variable {A h : ℕ} {I J O K : Type} [Fintype I] [Fintype J] [Fintype O] [Fintype K]

abbrev Mat (A h : ℕ) := Matrix (Addr A h) (Addr A h) ℚ
abbrev On (A : ℕ) (I O : Type) [Fintype I] [Fintype O] := Plan A (Fintype.card I) (Fintype.card O)

noncomputable def block (p : On A I O) (h : ℕ) : Matrix O I (Mat A h) :=
  fun b a y x => p.eval h (Fintype.equivFin O b,y) (Fintype.equivFin I a,x)

theorem block_seq (p : On A J O) (q : On A I J) (h : ℕ) :
    block (I := I) (O := O) (p.seq q) h = block (I := J) (O := O) p h * block (I := I) (O := J) q h := by
  ext b a y x
  simp only [block, Plan.eval, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  exact (Fintype.equivFin J).sum_comp _ |>.symm

/-- Numbered diagonal of a (possibly empty) family of distinct singleton plans. -/
def rows : (n : ℕ) → (Fin n → Plan A 1 1) → Plan A n n
  | 0, _ => .mix Fin.elim0
  | n+1, p => (rows n fun j => p j.castSucc).parallel (p (Fin.last n))

theorem calls_rows (n : ℕ) (p : Fin n → Plan A 1 1) :
    (rows n p).calls = ∑ j, (p j).calls := by
  induction n with
  | zero => simp [rows, Plan.calls]
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    exact congrArg (· + (p (Fin.last n)).calls) (ih _)

theorem eval_rows (n : ℕ) (p : Fin n → Plan A 1 1) (h : ℕ) (b a : Fin n) (y x : Addr A h) :
    (rows n p).eval h (b,y) (a,x) = if b = a then oneRow ((p b).eval h) y x else 0 := by
  induction n with
  | zero => exact Fin.elim0 b
  | succ n ih =>
    refine Fin.addCases (m := n) (n := 1) (fun i => ?_) (fun i => ?_) b <;>
      refine Fin.addCases (m := n) (n := 1) (fun j => ?_) (fun j => ?_) a
    · simp only [rows, Plan.eval, directSum, Fin.addCases_left, Fin.castAdd_inj]
      rw [show Fin.castAdd 1 i = i.castSucc from Fin.ext rfl]
      exact ih _ _ _
    · have hn : Fin.castAdd 1 i ≠ Fin.natAdd n j := fun he => by
        have hv := congrArg Fin.val he
        simp at hv
        omega
      simp [rows, Plan.eval, directSum, hn]
    · have hn : Fin.natAdd n i ≠ Fin.castAdd 1 j := fun he => by
        have hv := congrArg Fin.val he
        simp at hv
        omega
      simp [rows, Plan.eval, directSum, hn]
    · obtain rfl := Subsingleton.elim i 0
      obtain rfl := Subsingleton.elim j 0
      simp only [rows, Plan.eval, directSum, Fin.addCases_right, ite_true, oneRow]
      rw [show Fin.natAdd n (0 : Fin 1) = Fin.last n from Fin.ext (by simp)]

noncomputable def diagonal (p : I → Plan A 1 1) : On A I I :=
  rows (Fintype.card I) (p ∘ (Fintype.equivFin I).symm)

theorem calls_diagonal (p : I → Plan A 1 1) :
    (diagonal p).calls = ∑ j, (p j).calls := by
  rw [diagonal, calls_rows]
  exact (Fintype.equivFin I).symm.sum_comp (fun i => (p i).calls)

theorem block_diagonal [DecidableEq I] (p : I → Plan A 1 1) (h : ℕ) :
    block (I := I) (O := I) (diagonal p) h = Matrix.diagonal (fun j => oneRow ((p j).eval h)) := by
  ext b a y x
  unfold block diagonal
  rw [eval_rows]
  by_cases e : b = a <;> simp [Matrix.diagonal, e]

noncomputable def mixing (c : O → I → Coefficient) : On A I O :=
  .mix fun b a => c ((Fintype.equivFin O).symm b) ((Fintype.equivFin I).symm a)

theorem block_mixing (c : O → I → Coefficient) (h : ℕ) :
    block (I := I) (O := O) (mixing c) h = Matrix.of fun b a => (value (c b a)) • (1 : Mat A h) := by
  classical
  ext b a y x
  simp [block, mixing, Plan.eval, Matrix.one_apply, eq_comm]

/-- Realize a rectangular array of arbitrary singleton plans. The input rows are
copied to the array, processed independently, and summed by output row. -/
noncomputable def entries (p : O → I → Plan A 1 1) : On A I O := by
  classical
  exact (mixing (A := A) (fun b (k : O × I) => if k.1 = b then (1,0) else (0,0))).seq
    ((diagonal (fun k : O × I => p k.1 k.2)).seq
      (mixing (fun (k : O × I) a => if k.2 = a then (1,0) else (0,0))))

theorem calls_entries (p : O → I → Plan A 1 1) :
    (entries p).calls = ∑ b, ∑ a, (p b a).calls := by
  classical
  simp [entries, Plan.calls, mixing, calls_diagonal, Fintype.sum_prod_type]

theorem block_entries (p : O → I → Plan A 1 1) (h : ℕ) :
    block (I := I) (O := O) (entries p) h = Matrix.of fun b a => oneRow ((p b a).eval h) := by
  classical
  unfold entries
  rw [block_seq (J := O × I), block_seq (J := O × I), block_mixing, block_diagonal,
    block_mixing]
  funext b a
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_mul, Matrix.of_apply, Fintype.sum_prod_type]
  have pick (b : Prop) [Decidable b] : value (if b then (1,0) else (0,0)) = if b then 1 else 0 := by
    split <;> simp [value]
  simp [pick, ite_smul, ite_mul, mul_ite]

end KernelPass.Rect

end NearSquareRoot
end Computability
end OAI
