import OAI.Computability.BorderVNP.FiniteProductReplay

/-! # Neutral field weights on protected regions of a stack program

A forward-closed region protects a closing or sorting execution. A region with
forward-closed complement protects an execution that ends in its startup phase.
Both proofs lift the original choice string, stacks and exact elapsed time.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldStack

open VPVNP.RAMTape TeamPrivateFragment
open private lift_step from OAI.Computability.BorderVNP.FiniteProductReplay

variable {K Q : Type} [DecidableEq K] {F : Type*} [Field F] [Fintype F]

/-- Every continuing successor of a primitive instruction has the stated property. -/
def AllNext (P : Q → Prop) : StackOp K Q → Prop
  | .goto q | .push _ _ q => P q
  | .pop _ f => ∀ b, P (f b)
  | .choose q r => P q ∧ P r
  | .halt _ => True

omit [DecidableEq K] in
/-- A routine whose labels all lie in a region has no successor outside it. -/
theorem allNext_rename {L R : Type} (P : Q → Prop) (op : StackOp L R) (ports : L → K) (labels : R → Q)
    (h : ∀ z, P (labels z)) : AllNext P (op.rename ports labels) := by
  cases op <;> simp only [AllNext,StackOp.rename,Function.comp_apply] <;> first | exact h _ | exact ⟨h _,h _⟩ | exact fun _ => h _

private theorem next_of_step {C : StackCode K Q} {q s u out} (h : StackStep C q s u out)
    (P : Q → Prop) (hn : AllNext P (C q)) : P u := by
  cases h with
  | push op | goto op => rwa [op] at hn
  | pop op => rw [op] at hn; exact hn _

private theorem next_of_replay {C : StackCode K Q} {q s u out} (h : StackStep (replay C) q s u out)
    (P : Q → Prop) (hn : AllNext P (C q.1)) : P u.1 := by
  apply next_of_step h (fun z => P z.1)
  rcases q with ⟨q,bs⟩
  cases op : C q with
  | choose l r =>
    rw [op] at hn
    cases bs with
    | nil => simp [replay,op,AllNext]
    | cons b bs => cases b <;> simp [replay,op,AllNext,hn.1,hn.2]
  | halt b => simp [replay,op,AllNext]
  | push _ _ _ | pop _ _ | goto _ => simpa [replay,op,AllNext,StackOp.rename,Function.comp_def] using hn

/-- Lift a replay starting in a neutral forward-closed region without changing
the field element. -/
theorem neutral_forward (C : StackCode K Q) (w : Q → F) (P : Q → Prop) (acc : F)
    (neutral : ∀ q, P q → w q = 1) (closed : ∀ q, P q → AllNext P (C q))
    {q s u out t} (h : StackRuns (replay C) t q s u out) (hq : P q.1) :
    StackRuns (replay (productCode C w)) t ((q.1,Fintype.equivFin F acc),q.2) s ((u.1,Fintype.equivFin F acc),u.2) out := by
  induction h with
  | nil => exact .nil ..
  | cons step _ ih =>
    have hs := lift_step C w step acc
    rw [neutral _ hq,mul_one] at hs
    exact .cons hs (ih (next_of_replay step P (closed _ hq)))

/-- Lift a replay ending in a neutral region whose complement is forward-closed.
This applies to startup even when the program subsequently contains weighted calls. -/
theorem neutral_backward (C : StackCode K Q) (w : Q → F) (P : Q → Prop) (acc : F)
    (neutral : ∀ q, P q → w q = 1) (closed : ∀ q, ¬P q → AllNext (fun z => ¬P z) (C q))
    {q s u out t} (h : StackRuns (replay C) t q s u out) (hu : P u.1) :
    StackRuns (replay (productCode C w)) t ((q.1,Fintype.equivFin F acc),q.2) s ((u.1,Fintype.equivFin F acc),u.2) out := by
  have aux {q' s' u' out' t'} (run : StackRuns (replay C) t' q' s' u' out') (endGood : P u'.1) : P q'.1 := by
    induction run with
    | nil => exact endGood
    | cons step _ ih => exact of_not_not (fun hbad => next_of_replay step _ (closed _ hbad) (ih endGood))
  induction h with
  | nil => exact .nil ..
  | cons step tail ih =>
    have hs := lift_step C w step acc
    rw [neutral _ (aux (.cons step tail) hu),mul_one] at hs
    exact .cons hs (ih hu)

end FieldStack

end BorderVNP
end Computability
end OAI
