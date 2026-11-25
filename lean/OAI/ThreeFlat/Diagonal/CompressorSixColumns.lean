import OAI.ThreeFlat.Diagonal.CompressorStageMachine
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Selecting the native row of each of the six dense graph columns -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.DescriptorExpr RAM.PhysicalPinsExpr Placement
open scoped Fin.NatCast
variable {w k n : ℕ}
variable (pub : Fin k → Word w) (m : Memory w) (vs : Fin 1 → Word w)

private theorem eval_fold (row : Fin 6 → Term w k 1) (select : Term w k 1) (i : Fin 6)
    (fit : 6≤2^w) (hs : (Term.eval pub m select vs)=(i.val:Word w)) (xs : List (Fin 6)) (mem : i∈xs) :
    (Term.eval pub m (xs.foldr (fun j z => Term.select .eq select (.literal (j.val:Word w)) (row j) z) (.literal 0)) vs) =
      (Term.eval pub m (row i) vs) := by
  induction xs with
  | nil => simp at mem
  | cons x xs ih =>
    have eq : (i.val:Word w) = (x.val:Word w) ↔ i=x := by
      rw [Fin.ext_iff,Fin.val_cast_of_lt (i.isLt.trans_le fit),Fin.val_cast_of_lt (x.isLt.trans_le fit),Fin.ext_iff]
    by_cases h : i=x
    · subst x
      simp [hs,Comparison.test]
    · simp [hs,Comparison.test,eq,h,ih (List.mem_cons.mp mem |>.resolve_left h)]

theorem eval_sixColumns_index (start length : Term w k 1) (row : Fin 6 → Term w k 1 → Term w k 1)
    (i : Fin 6) (fit : 6 ≤ 2^w)
    (h : BinaryOp.div.eval (vs 0 - (Term.eval pub m start vs)) ((Term.eval pub m length vs)) = (i.val : Word w)) :
    (Term.eval pub m (sixColumns start length row) vs) =
      (Term.eval pub m (row i (.binary .add start (.binary .mul length (.literal (i.val:Word w))))) vs) := by
  unfold sixColumns
  apply eval_fold pub m vs _ _ i fit _ _ (List.mem_finRange i)
  simpa [terms,Term.eval,BinaryOp.eval] using h

theorem eval_sixColumns (start length : Term w k 1) (row : Fin 6 → Term w k 1 → Term w k 1)
    (i : Fin 6) (lo len j : ℕ) (fit : 6 ≤ 2^w) (lenFits : len<2^w) (part : j<len)
    (inside : lo+i.val*len+j<2^w) (hs : (Term.eval pub m start vs)=(lo:Word w)) (hl : (Term.eval pub m length vs)=(len:Word w))
    (hp : vs 0 = ((lo+i.val*len+j:ℕ):Word w)) :
    (Term.eval pub m (sixColumns start length row) vs) = (Term.eval pub m (row i (.binary .add start
      (.binary .mul length (.literal (i.val:Word w))))) vs) := by
  apply eval_sixColumns_index pub m vs start length row i fit
  rw [hs,hl,hp,Nat.cast_add,Nat.cast_add]
  have e (a b c : Word w) : a+b+c-a=b+c := by abel
  rw [e,← Nat.cast_add,op_cast .div (i.val*len+j) len ⟨by omega,lenFits⟩]
  simp only [natOp,Nat.mul_comm i.val len,Nat.mul_add_div (Nat.zero_lt_of_lt part),Nat.div_eq_of_lt part,
    Nat.add_zero]

end ThreeFlat.Diagonal.CompressorPacking.Native

end OAI
