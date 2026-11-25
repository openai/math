import OAI.Hierarchy.FormulaPartitionKernel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

namespace OAI
/-! # Expansion of a kernel run over its intermediate slot sets -/

namespace Hierarchy.FormulaPartition

open scoped BigOperators Classical
noncomputable section

variable {X : Type} [Fintype X] {F : Type*} [Field F] {A : Type*}

theorem sum_state_head {L : ℕ} (f : (Fin (L+1) → X) → F) :
    ∑ W, f W = ∑ x : X, ∑ T : Fin L → X, f (Fin.cons x T) := by
  let split := Fin.consEquiv (fun _ : Fin (L+1) => X)
  calc
    ∑ W, f W = ∑ p : X × (Fin L → X), f (split p) := (split.sum_comp f).symm
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

/-- Evaluate a succession of finite transition matrices from a fixed state. -/
def stateSum (val : A → X → X → F) (tip : X → F) : List A → X → F
  | [], x => tip x
  | k :: ks, x => ∑ y : X, val k x y * stateSum val tip ks y

/-- The weight along one particular tuple of intermediate states. -/
def stateProduct (ks : List A) (val : A → X → X → F) (tip : X → F)
    (W : Fin (ks.length+1) → X) : F :=
  (∏ i : Fin ks.length, val (ks.get i) (W i.castSucc) (W i.succ)) * tip (W (Fin.last _))

omit [Fintype X] in
private theorem stateProduct_cons (k : A) (ks : List A) (val : A → X → X → F)
    (tip : X → F) (x : X) (T : Fin (ks.length+1) → X) :
    stateProduct (k::ks) val tip (Fin.cons x T) = val k x (T 0) * stateProduct ks val tip T := by
  let W : Fin (ks.length+2) → X := Fin.cons (α:=fun _ => X) x T
  let f (i : Fin (ks.length+1)) := val ((k::ks).get i) (W i.castSucc) (W i.succ)
  have peel := Fin.prod_univ_succ f
  exact (congrArg (fun z => z * tip (T (Fin.last ks.length))) peel).trans (mul_assoc _ _ _)

private theorem stateSum_eq_tail (ks : List A) (val : A → X → X → F) (tip : X → F) (x : X) :
    stateSum val tip ks x = ∑ T : Fin ks.length → X, stateProduct ks val tip (Fin.cons x T) := by
  induction ks generalizing x with
  | nil => simp [stateSum,stateProduct]
  | cons k ks ih =>
    change (∑ y : X, val k x y * stateSum val tip ks y) =
      ∑ T : Fin (ks.length+1) → X, stateProduct (k::ks) val tip (Fin.cons x T)
    rw [sum_state_head (fun T => stateProduct (k::ks) val tip (Fin.cons x T))]
    apply Finset.sum_congr rfl
    intro y _
    rw [ih,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    rw [stateProduct_cons,Fin.cons_zero]

theorem stateSum_eq_sum_states [DecidableEq X] (ks : List A) (val : A → X → X → F)
    (tip : X → F) (x : X) :
    stateSum val tip ks x =
      ∑ W : Fin (ks.length+1) → X, if W 0=x then stateProduct ks val tip W else 0 := by
  rw [stateSum_eq_tail, sum_state_head (fun W => if W 0=x then stateProduct ks val tip W else 0)]
  simp only [Fin.cons_zero]
  symm
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ h
    simp [h]
  · simp

variable {V : Type} {τ : V → Type} [Fintype V] [DecidableEq V]

/-- Product of all kernel transition values, followed by the terminal leaf coefficient. -/
def chainWeight (ks : List (Kernel V τ F)) (a : ∀ v, τ v) (tip : Leaf V τ F)
    (W : Fin (ks.length+1) → Finset V) : F :=
  stateProduct ks (fun k => k.value a) (tip.value a) W

omit [Fintype V] in
theorem chainWeight_cons (k : Kernel V τ F) (ks : List (Kernel V τ F)) (a : ∀v,τ v)
    (tip : Leaf V τ F) (S : Finset V) (T : Fin (ks.length+1) → Finset V) :
    chainWeight (k::ks) a tip (Fin.cons S T) = k.value a S (T 0) * chainWeight ks a tip T :=
  stateProduct_cons k ks (fun j => j.value a) (tip.value a) S T

/-- Sum of the parse path coefficients over all slot-state tuples with the prescribed start. -/
theorem run_eq_sum_states (a : ∀ v, τ v) (tip : Leaf V τ F) (ks : List (Kernel V τ F)) (S : Finset V) :
    run a tip ks S = ∑ W : Fin (ks.length+1) → Finset V, if W 0=S then chainWeight ks a tip W else 0 := by
  have expand (ls : List (Kernel V τ F)) (U : Finset V) :
      run a tip ls U = stateSum (fun k => k.value a) (tip.value a) ls U := by
    induction ls generalizing U with
    | nil => rfl
    | cons k ls ih => simp only [run,Kernel.act,stateSum,ih]
  exact (expand ks S).trans (stateSum_eq_sum_states ks _ _ S)


end
end Hierarchy.FormulaPartition

end OAI
