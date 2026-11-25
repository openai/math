import OAI.ThreeFlat.RAM.TickBitRelation
import OAI.ThreeFlat.Diagonal.TickGroupIntervals
import Mathlib.Data.Fin.VecNotation

namespace OAI
/-! # Chunk comparison rule computed from the dense local pair-offset map -/

namespace ThreeFlat.RAM.TickChunkRule

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr Diagonal.TickAuxiliary TickBitRelation
open scoped Fin.CommRing

/-- A covered bit must agree with both proposed endpoints. -/
def fixedRule : Bool → Bool → Rule
  | false,false => .bothZero | false,true => .zeroOne
  | true,false => .oneZero | true,true => .bothOne

theorem holds_fixedRule (x y a b : Bool) :
    (fixedRule x y).holds a b ↔ a = x ∧ b = y := by cases x <;> cases y <;> rfl

def rule (code : ℕ) (oldPair newPair : ℕ → Bool) : Rule :=
  if code = 0 then .same else fixedRule (oldPair (code-1)) (newPair (code-1))

theorem rule_holds (code : ℕ) (op np : ℕ → Bool) (a b : Bool) :
    (rule code op np).holds a b ↔
      if code = 0 then a = b else a = op (code-1) ∧ b = np (code-1) := by
  by_cases h : code = 0
  · simp only [rule,ite_eq_left h,Rule.holds]
  · simpa only [rule,ite_eq_right h] using holds_fixedRule (op (code-1)) (np (code-1)) a b

/-- Given a code and the old/new pair-array base addresses, read the two
shared guesses for a covered bit. An uncovered bit returns equality. -/
def lookup (w k : ℕ) : Term w k 3 :=
  let q := Term.result 0
  let off := Term.binary .sub q (.literal 1)
  let old := (Term.binary .add (.result 1) off).load
  let new := (Term.binary .add (.result 2) off).load
  .select .eq q (.literal 0) (.literal 1)
    (.binary .add (.binary .add (.literal 4) (.binary .mul old (.literal 2))) new)

theorem lookup_binds (w k : ℕ) : (lookup w k).binds ≤ 24 := by
  simp [lookup,Term.select,Term.binary,Term.literal,Term.load,Term.binds]

theorem lookup_eval {w k : ℕ} (par : Fin k → Word w) (m : Memory w)
    (code : ℕ) (op np : ℕ → Bool) (old new : Word w) (size : code < 2^w)
    (old_ok : code ≠ 0 → m (old+((code : Word w)-1)).val = bitWord w (op (code-1)))
    (new_ok : code ≠ 0 → m (new+((code : Word w)-1)).val = bitWord w (np (code-1))) :
    (lookup w k).eval par m ![(code : Word w), old, new] = ((rule code op np).tag : Word w) := by
  have cz : (code : Word w) = 0 ↔ code = 0 := by simp [Fin.ext_iff, Fin.val_cast_of_lt size]
  simp only [lookup, Term.eval_select, Term.eval_binary, Term.eval_literal, Term.eval_load,
    Term.eval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Comparison.test,
    BinaryOp.eval, beq_iff_eq, cz, rule]
  by_cases h : code = 0
  · simp [h,Rule.tag]
  · have oo := old_ok h
    have nn := new_ok h
    simp only [ite_eq_right h,oo]
    cases ha : op (code-1) <;> cases hb : np (code-1) <;>
      simp [nn,hb,bitWord,fixedRule,Rule.tag] <;> norm_num

/-- The group interval cursor has already written one natural pair code at
each offset. Only the two pointers to the currently packed groups are dynamic. -/
def atRow (w k mapBase oldPtr newPtr : ℕ) : Term w k 1 :=
  (lookup w k).instantiate ![(Term.binary .add (.literal (mapBase : Word w)) (.result 0)).load,
    (Term.literal (oldPtr : Word w)).load, (Term.literal (newPtr : Word w)).load]

theorem atRow_eval {w k : ℕ} (par : Fin k → Word w) (m : Memory w)
    (mapBase oldPtr newPtr : ℕ) (i : Word w) (q : ℕ) (op np : ℕ → Bool) (size : q < 2^w)
    (map_ok : m ((mapBase : Word w)+i).val = (q : Word w))
    (old_ok : q ≠ 0 → m (m (oldPtr : Word w).val+((q : Word w)-1)).val = bitWord w (op (q-1)))
    (new_ok : q ≠ 0 → m (m (newPtr : Word w).val+((q : Word w)-1)).val = bitWord w (np (q-1))) :
    (atRow w k mapBase oldPtr newPtr).eval par m (fun _ => i) = ((rule q op np).tag : Word w) := by
  rw [atRow,Term.eval_instantiate]
  let env : Fin 3 → Word w := ![(q : Word w),m (oldPtr : Word w).val,m (newPtr : Word w).val]
  convert lookup_eval par m q op np _ _ size old_ok new_ok using 2
  funext j
  fin_cases j <;> simp [BinaryOp.eval,Term.eval,map_ok]

end ThreeFlat.RAM.TickChunkRule

end OAI
