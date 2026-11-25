import OAI.ThreeFlat.Diagonal.TickSlotForest
import OAI.ThreeFlat.RAM.HistoryCompiledRows
import OAI.ThreeFlat.RAM.HeaderScan

namespace OAI
/-! # The final selected-root concatenation uses a common physical input -/

namespace ThreeFlat.RAM.HistoryFinalCopy

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr BitNetwork.Ordered BitLayout Diagonal.TickSlotForest
open scoped Fin.CommRing BigOperators

variable {F : Type*} {p n w k : ℕ}

/-- Shared physical pins retain their addresses. Only a private bit of a
later selected root is advanced by the preceding private row allocation. -/
def move (p offset source : ℕ) := if source < 2+p then source else source+offset

def before (N : Fin n → BitNetwork F p) (i : Fin n) := ∑ j : Fin i.val, (N (Fin.castLE i.isLt.le j)).internal

private theorem move_resolve (N : Fin n → BitNetwork F p) (i : Fin n) (s : BitSource (N i).internal p) :
    move p (before N i) (sourceAddress s) =
    sourceAddress (resolve N (fun _ a => (BitSource.pin a : BitSource 0 p)) i s) := by
  cases s with
  | constant b => cases b <;> simp [move,resolve,sourceAddress,show 1 < 2 + p by omega]
  | pin j => have := j.isLt; simp [move,resolve,sourceAddress,show 2+j.val<2+p by omega]
  | hidden j =>
    change move p (before N i) (2+p+j.val) = (2+p)+(privateEquiv (h:=0) N (.inr ⟨i,j⟩)).val
    rw [private_offset]
    simp only [move,ite_eq_right (show ¬2+p+j.val < 2+p by omega),before,Nat.zero_add]
    omega

/-- Concatenating directly into the final buffer takes four words per factor
and skips the potentially large public-pin map of every selected root. -/
theorem row (tag : ((Fin 3 → Bool) → F) → ℕ) (N : Fin n → BitNetwork F p) (i : Fin n) (j : Fin (N i).cells) (c : Fin 4) :
    let src := HistoryCompiledRows.metadata tag (N i) j c
    (if c.val<3 then move p (before N i) src else src) =
      HistoryCompiledRows.metadata tag (network N) (finSigmaFinEquiv ⟨i,j⟩) c := by
  dsimp only
  by_cases field : c.val<3
  · simp only [ite_eq_left field,HistoryCompiledRows.metadata,dite_eq_left field,network,source_at]
    exact move_resolve N i _
  · simp [HistoryCompiledRows.metadata,field,network,table_at]

/-- Native source/column relocation at a terminal join. The four input
registers hold the word offset in the current root, its source base, the
private-address threshold, the private prefix increment.
There is no per-root bank of pass-through pin addresses. -/
def term : Term w k 4 :=
  let old := (Term.binary .add (.result 1) (.result 0) : Term w k 4).load
  let field := Term.binary .mod (.result 0) (.literal 4)
  let shifted := Term.select .lt old (.result 2) old (Term.binary .add old (.result 3))
  Term.select .lt field (.literal 3) shifted old

set_option maxRecDepth 2048 in
theorem term_eval (pub : Fin k → Word w) (m : Memory w) (x : Fin 4 → Word w) :
    term.eval pub m x =
    let old := m (x 1+x 0).val
    if BinaryOp.eval .mod (x 0) 4 < (3:Word w) then (if old<x 2 then old else old+x 3) else old := by
  simp only [term, Term.eval_select, Term.eval_load, Term.eval_binary, Term.eval_literal,
    Term.eval, Comparison.test, decide_eq_true_eq]
  rfl

theorem term_binds : (term (w:=w) (k:=k)).binds ≤ 18 := by
  simp [term, Term.select, Term.binary, Term.load, Term.literal, Term.binds]

end ThreeFlat.RAM.HistoryFinalCopy

end OAI
