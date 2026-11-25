import OAI.Computability.IntegerMultiplication.Strip.Kernel

/-! Grid phases. Expose a block of one bit per column as a single child,
without reordering spectator fields. Lemmas for telescoping lenses and rows.-/

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Tensor Net.Walsh Strip Strip.Optic Matrix Finset
variable {O A C I J K L R : Type} [CommRing R] [DecidableEq J] [Fintype J]
  [DecidableEq I] [Fintype I]
variable [DecidableEq K] [Fintype K]

omit [CommRing R] [DecidableEq J] [Fintype J] [DecidableEq I] [Fintype I] [DecidableEq K] [Fintype K] in
/-- two forms of specifying the same field, not constrained by layout. -/
theorem same_on (a : Lens O I J) (b : Lens O I K)
    (hf : ∀ i,(a i).1=(b i).1)
    (hs : ∀ i j,(a i).2=(a j).2 → (b i).2=(b j).2)
    (m : (I→R)→I→R) :
    everywhere a m = everywhere b m := by
  funext x y
  change m (fiber a x (a y).2) _ = m (fiber b x (b y).2) _
  rw [hf y]
  suffices e : fiber a x (a y).2 = fiber b x (b y).2 by rw [e]
  funext t
  unfold fiber
  suffices a.symm (t,(a y).2) = b.symm (t,(b y).2) by rw [this]
  apply b.injective
  rw [Equiv.apply_symm_apply]
  refine Prod.ext ?_ ?_
  · rw [← hf,Equiv.apply_symm_apply]
  change (b _).2=(b y).2
  exact hs _ y (by simp)

def grid (s : Lens I J K) (m : Mat J R) : Mat I R :=
  Matrix.of fun x y => if (s x).2=(s y).2 then m (s x).1 (s y).1 else 0

omit [DecidableEq J] [DecidableEq I] in
theorem align (s : Lens I J K) (m : Mat J R) :
    (grid s m *ᵥ ·) = everywhere s (m *ᵥ ·) := by
  funext x y
  change ∑ i, (grid s m) y i * x i = ∑ j, m _ j*x (s.symm (j,(s y).2))
  let q i := (grid s m) y i * x i
  change ∑ i, q i = _
  rw [← s.symm.sum_comp q, Fintype.sum_prod_type]
  simp [grid,q,eq_comm] -- check
omit [DecidableEq J] [DecidableEq I] in
theorem beneath (f : Lens O I L) (s : Lens I J K) (m : Mat J R) :
    operate f (grid s m) = operate (Strip.Optic.dig f s) m := by
  rw [operate,align,Strip.Optic.focus]
  rfl

variable {N : Type} [Fintype N] [DecidableEq N]

/-- parallel lens, one per outer index -/
def gang (s : Lens I J K) : Lens (N→I) (N→J) (N→K) where
  toFun x := (fun n => (s (x n)).1,fun n => (s (x n)).2)
  invFun x := fun n => s.symm (x.1 n,x.2 n)
  left_inv x := by funext n; dsimp; exact s.symm_apply_apply _
  right_inv x := by
    rcases x with ⟨x,y⟩
    dsimp; simp

omit [DecidableEq J] [Fintype J] [DecidableEq I] [Fintype I] [Fintype K] [DecidableEq N] in
theorem grid_batch (s : Lens I J K) (m : N→ Mat J R) :
    Net.Tensor.mat (fun n => grid s (m n)) = grid (gang s) (Net.Tensor.mat m) := by
  classical
  ext x y
  change ∏ n, (if (s (x n)).2=(s (y n)).2 then m n (s (x n)).1 (s (y n)).1 else 0) = _
  by_cases h : (gang s x).2=(gang s y).2
  · have e (n : N) : (s (x n)).2=(s (y n)).2 := congrFun h n
    simp only [e, ite_true, grid,of_apply,h,app]
    rfl --?
  have e : ∃ n, (s (x n)).2 ≠ (s (y n)).2 :=
    not_forall.mp (fun t => h (funext t))
  obtain ⟨n,t⟩ := e
  rw [grid,of_apply, ite_eq_right h, Finset.prod_eq_zero (Finset.mem_univ n)]
  simp [t]

abbrev Board (j : J) := {z : J // z ≠ j} → B
def pier (j : J) : Lens (Addr J) B (Board j) where
  toFun x := (x j,fun i => x i)
  invFun x := fun i => if h : i=j then x.1 else x.2 ⟨i,h⟩
  left_inv x := by
    funext i; dsimp
    split <;> simp_all
  right_inv x := by
    refine Prod.ext (by simp) (funext fun i => ?_)
    simp [i.property]

/-- e_j for direction basis -/
def lad (j : J) : Addr J := fun t => if t=j then 1 else 0
omit [Fintype J] in
theorem split_lad (x : Addr J) (j) :
    pier j (x+lad j) = ((pier j x).1+1,(pier j x).2) := by
  apply Prod.ext
  · change x j+lad j j=x j+1; rw [lad,ite_eq_left rfl]
  funext i
  change x i.val + lad j i.val = x i.val
  simp [lad,i.property]

theorem harbour (c : Quarter R) (b : Bool) (j : J) :
    kernel c b (lad j) = grid (pier j) (Walsh.A c b) := by
  ext x y
  simp only [kernel,shade,grid,Walsh.A,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,of_apply]
  have z : pier j x = pier j y ↔ x = y := (pier j).apply_eq_iff_eq
  have d : y=x+lad j ↔ (pier j y).1=(pier j x).1+1 ∧ (pier j y).2=(pier j x).2 := by
    rw [← (pier j).apply_eq_iff_eq,split_lad,Prod.ext_iff]
  simp only [d]
  have c0 : ∀ a b : B, a=b+1 ↔ b≠a := by decide
  simp only [c0]
  by_cases e : (pier j x).1=(pier j y).1 <;>
    by_cases f : (pier j x).2=(pier j y).2
  all_goals
    simp only [← z, Prod.ext_iff]
    simp [e,f,eq_comm]

omit [DecidableEq K] [Fintype K] in
theorem lone (o : Optic.Layout O N J K) (c : Quarter R) (b : Bool) (j : J) :
    pipe o (kernel c b (lad j)) = operate (dig o (gang (pier j))) (allC c (fun _ => b)) := by
  unfold pipe broadcast
  rw [harbour, grid_batch, beneath]
  rfl
end Phase

end IntegerMultiplication
end Computability
end OAI
