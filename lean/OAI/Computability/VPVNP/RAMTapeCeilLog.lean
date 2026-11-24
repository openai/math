import OAI.Computability.VPVNP.RAMTapeCeilLogCost
import OAI.Computability.VPVNP.RAMTapeStacks
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.DeriveFintype

/-!
# A finite stack control for the physical site address width

The source stack holds the input length in unary. A round consumes pairs
of marks, returning one mark per pair, including a final singleton. Every
round with at least two source marks prepends a fixed number of output
marks. The last round consumes zero or one source mark and returns.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.CeilLog

/-- Stack labels for the unary length, its rounded half, and accumulated address-width marks. -/
inductive Port where
  | src | tmp | out
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Control of the repeated ceiling-halving rounds, with a finite counter for the fixed output
marks per nontrivial round. -/
inductive Phase (B : ℕ) where
  | scan | second | firstHalf
  | pair | save | skip
  | emit (marks : Fin (B+1))
  | transfer | put | done
  deriving DecidableEq, Fintype

/-- Each nontrivial round emits the fixed `B` bits. The changing count is
stored in unary on the stacks. -/
def code (B : ℕ) : StackCode Port (Phase B)
  | .scan => .pop .src fun b ↦ b.elim .done (fun _ ↦ .second)
  | .second => .pop .src fun b ↦ b.elim .done (fun _ ↦ .firstHalf)
  | .firstHalf => .push .tmp true .pair
  | .pair => .pop .src fun b ↦ b.elim (.emit (Fin.last B)) (fun _ ↦ .save)
  | .save => .push .tmp true .skip
  | .skip => .pop .src fun b ↦ b.elim (.emit (Fin.last B)) (fun _ ↦ .pair)
  | .emit i => if h : i.val = 0 then .goto .transfer
    else .push .out true (.emit ⟨i.val - 1, by have := i.isLt; omega⟩)
  | .transfer => .pop .tmp fun b ↦ b.elim .scan (fun _ ↦ .put)
  | .put => .push .src true .transfer
  | .done => .halt true

/-- Place the supplied bit lists on the length, intermediate, and width-output stacks. -/
def store (src tmp out : List Bool) : Stacks Port
  | .src => src
  | .tmp => tmp
  | .out => out

private abbrev ones (n : ℕ) := List.replicate n true

private theorem update_store (x t o v : List Bool) (k : Port) :
    Function.update (store x t o) k v = match k with
      | .src => store v t o
      | .tmp => store x v o
      | .out => store x t v := by
  funext i
  cases k <;> cases i <;> simp [store]

local macro "stack_step" : tactic => `(tactic|
  (first | refine StackRuns.cons (.pop rfl) ?_ | refine StackRuns.cons (.push rfl) ?_)
  <;> simp only [store, List.head?_cons, List.tail_cons, List.head?_nil, List.tail_nil,
    Option.elim_some, Option.elim_none, update_store])

private theorem pairs_run (B n : ℕ) (t o : List Bool) :
    StackRuns (code B) (n + (n+1)/2 + 1) .pair (store (ones n) t o)
      (.emit (Fin.last B)) (store [] (ones ((n+1)/2) ++ t) o) := by
  induction n using Nat.twoStepInduction generalizing t with
  | zero => stack_step; exact .nil ..
  | one => stack_step; stack_step; stack_step; exact .nil ..
  | more n ih _ =>
    have hhalf : (n+2+1)/2 = (n+1)/2 + 1 := by omega
    rw [hhalf, show n+2+((n+1)/2+1)+1 = (n+(n+1)/2+1)+1+1+1 by omega]
    change StackRuns _ _ _ (store (true :: true :: ones n) t o) _ _
    stack_step
    stack_step
    stack_step
    simpa only [ones, List.replicate_succ', List.append_assoc, List.singleton_append] using
      ih (true :: t)

private theorem emit_run (B : ℕ) (k : ℕ) (hk : k ≤ B) (t o : List Bool) :
    StackRuns (code B) (k+1) (.emit ⟨k, by omega⟩) (store [] t o)
      .transfer (store [] t (ones k ++ o)) := by
  induction k generalizing o with
  | zero => exact .cons (.goto (by simp [code])) (.nil ..)
  | succ k ih =>
    have h : code B (.emit ⟨k+1, by omega⟩) = .push .out true (.emit ⟨k, by omega⟩) := by
      simp [code]
    refine .cons (.push h) ?_
    simpa only [ones, store, update_store, List.replicate_succ', List.append_assoc, List.singleton_append]
      using ih (by omega) (true :: o)

private theorem transfer_run (B k : ℕ) (x o : List Bool) :
    StackRuns (code B) (2*k+1) .transfer (store x (ones k) o) .scan (store (ones k ++ x) [] o) := by
  induction k generalizing x with
  | zero => stack_step; exact .nil ..
  | succ k ih =>
    simp only [Nat.mul_succ]
    change StackRuns _ _ _ (store x (true :: ones k) o) _ _
    stack_step
    stack_step
    simpa only [ones, List.replicate_succ', List.append_assoc, List.singleton_append] using ih (true :: x)

private theorem round_run (B n : ℕ) (o : List Bool) :
    let m := (n+2+1)/2
    StackRuns (code B) (n+2 + 3*m + B + 3) .scan (store (ones (n+2)) [] o)
      .scan (store (ones m) [] (ones B ++ o)) := by
  let m := (n+2+1)/2
  have hp := pairs_run B n [true] o
  have hstack : ones ((n+1)/2) ++ [true] = ones m := by
    rw [show m = (n+1)/2+1 by dsimp [m]; omega]
    exact List.replicate_succ'.symm
  rw [hstack] at hp
  have he := emit_run B B le_rfl (ones m) o
  have ht := transfer_run B m [] (ones B ++ o)
  rw [List.append_nil] at ht
  have h := (hp.trans he).trans ht
  change StackRuns _ (n+2+3*m+B+3) _ (store (true :: true :: ones n) [] o) _ _
  rw [show n+2+3*m+B+3 = ((n+(n+1)/2+1 + (B+1)) + (2*m+1))+1+1+1 by dsimp [m]; omega]
  stack_step
  stack_step
  stack_step
  exact h

/-- The output stack receives exactly the site's address width
`B * Nat.clog 2 n` in unary. The source and temporary stacks finish empty.
The exact instruction count is `cost B n`, bounded by `cost_le`. -/
theorem runs (B n : ℕ) (out : List Bool) :
    StackRuns (code B) (cost B n) .scan (store (List.replicate n true) [] out)
      .done (store [] [] (List.replicate (B * Nat.clog 2 n) true ++ out)) := by
  induction n using Nat.strong_induction_on generalizing out with
  | h n ih =>
    match n with
    | 0 =>
      simp only [cost_zero, Nat.clog_zero_right, Nat.mul_zero, List.replicate_zero, List.nil_append]
      stack_step
      exact .nil ..
    | 1 =>
      simp only [cost_one, Nat.clog_one_right, Nat.mul_zero, List.replicate_zero, List.nil_append]
      stack_step
      stack_step
      exact .nil ..
    | n + 2 =>
      let m := (n+2+1)/2
      have h := (round_run B n out).trans (ih m (by dsimp [m]; omega) (ones B ++ out))
      rw [cost_step B (by omega : 2 ≤ n+2), clog_step (by omega : 2 ≤ n+2), Nat.mul_succ,
        List.replicate_add (B * Nat.clog 2 m) B, List.append_assoc]
      exact h

end RAMTape.CeilLog

end VPVNP
end Computability
end OAI
