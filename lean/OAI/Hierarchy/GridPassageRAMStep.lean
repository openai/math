import OAI.Hierarchy.GridPassageRAMRow
import OAI.Hierarchy.GridPassageRAMState
import Mathlib.Tactic.Ring

namespace OAI
/-! # Natural-address semantics of the native passage row -/

namespace Hierarchy.GridPassageRAMRow
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {w : ℕ}

private theorem nonzeroBit_eq (x : Word w) :
    nonzeroBit x = if x=0 then 0 else 1 := by
  by_cases h : x=0
  · subst x
    simp [nonzeroBit,BinaryOp.eval]
  · have pos : 0 < x.val := Nat.pos_of_ne_zero (fun hz => h (Fin.ext hz))
    simp [nonzeroBit,BinaryOp.eval,h,Nat.div_self pos]

/-- The unsigned comparison also handles an all-ones counter. Its successor
wraps to zero and the hardware division returns zero. -/
theorem unsignedLt_eq (old B : Word w) :
    unsignedLt old B = if old.val < B.val then 1 else 0 := by
  let q := BinaryOp.div.eval B (old+1)
  have cast : old+1 = ((old.val+1:ℕ):Word w) := by push_cast; rfl
  have qzero : q=0 ↔ ¬old.val<B.val := by
    by_cases fits : old.val+1<2^w
    · have succVal : (old+(1:Word w)).val=old.val+1 := by rw [cast,Fin.val_cast_of_lt fits]
      have value : q.val=B.val/(old.val+1) := by
        change (B.val / (old+(1:Word w)).val) % (2^w) = _
        rw [succVal,Nat.mod_eq_of_lt ((Nat.div_le_self _ _).trans_lt B.isLt)]
      constructor
      · intro h less
        have pos : 0 < B.val/(old.val+1) := Nat.div_pos less (Nat.succ_pos _)
        rw [←value,h] at pos
        exact (Nat.lt_irrefl 0) pos
      · intro h
        apply Fin.ext
        rw [value,Nat.div_eq_of_lt (by omega)]; rfl
    · have top : old.val+1=2^w := by have := old.isLt; omega
      have wrap : old+1 = (0:Word w) := by
        rw [cast,top]
        exact Fin.ext (Nat.mod_self _)
      have cap := B.isLt
      have full : ¬ old.val < B.val := by omega
      simp [q,wrap,BinaryOp.eval,full]
  change nonzeroBit q = _
  by_cases room : old.val < B.val <;> simp [nonzeroBit_eq,qzero,room]

theorem active_eq (B old tag t : Word w) :
    active B old tag t = if tag ≠ t ∧ old.val < B.val then 1 else 0 := by
  by_cases hit : tag=t <;> by_cases room : old.val < B.val <;>
    simp [active,unsignedLt_eq,nonzeroBit_eq,hit,room,sub_eq_zero]

private theorem write_own (m : Memory w) (a : Word w) : writeMemory m a (m a.val) = m := by
  funext x
  by_cases h : x=a.val <;> simp [writeMemory,h]

private theorem commit_zero (v : Parameters w) (i : Word w) (z : Visit w)
    (a : Word w) (m : Memory w) :
    commit v i z a (m a.val) 0 m = writeMemory m (v 10+i) 0 := by
  simp [commit,write_own]

private theorem commit_one (v : Parameters w) (i : Word w) (z : Visit w)
    (a old : Word w) (m : Memory w) :
    commit v i z a old 1 m =
      writeMemory (writeMemory (writeMemory m (v 9+(z.key*v 3+old)) z.rail)
        a (old+1)) (v 10+i) 1 := by
  have undo (x y : Word w) : x+(y-x)=y := by ring
  simp [commit,undo]

/-- Input pages determine the rail and bucket, while word-sized addresses
identify the physical writes with the chosen-rail, counter, and mark arrays. -/
theorem wordStep_natStep (v : Parameters w) (counterBase chosenBase markBase B key rail i : ℕ)
    (untouched : Bool) (m : Memory w)
    (countBaseAt : v 8=(counterBase:Word w)) (outBaseAt : v 9=(chosenBase:Word w))
    (markBaseAt : v 10=(markBase:Word w)) (capAt : v 3=(B:Word w))
    (railAt : (visit v (i:Word w) m).rail=(rail:Word w))
    (keyAt : (visit v (i:Word w) m).key=(key:Word w))
    (touchAt : m (v 7+(visit v (i:Word w) m).rail).val ≠ (visit v (i:Word w) m).position ↔ untouched=true)
    (capFit : B<2^w) (countFit : counterBase+key<2^w) (markFit : markBase+i<2^w)
    (destFit : untouched=true ∧ (m (counterBase+key)).val<B →
      chosenBase+key*B+(m (counterBase+key)).val<2^w) :
    wordStep v (i:Word w) m = natStep counterBase chosenBase markBase B key rail i untouched m := by
  let z := visit v (i:Word w) m
  let a := v 8+z.key
  let old := m (counterBase+key)
  have addr : a=((counterBase+key:ℕ):Word w) := by
    change v 8+(visit v (i:Word w) m).key=_
    rw [countBaseAt,keyAt,Nat.cast_add]
  have oldAt : m a.val = old := by rw [addr,Fin.val_cast_of_lt countFit]
  have mark : v 10+(i:Word w)=((markBase+i:ℕ):Word w) := by rw [markBaseAt,Nat.cast_add]
  have size : (v 3).val=B := by rw [capAt,Fin.val_cast_of_lt capFit]
  have f : active (v 3) old (m (v 7+z.rail).val) z.position =
      (if untouched=true ∧ old.val<B then 1 else 0) := by
    rw [active_eq,size]
    simp only [z,touchAt]
  change commit v (i:Word w) z a (m a.val) (active (v 3) (m a.val) (m (v 7+z.rail).val) z.position) m = _
  rw [oldAt,f]
  by_cases good : untouched=true ∧ old.val<B
  · rw [ite_eq_left good,commit_one]
    have dst : v 9+(z.key*v 3+old) = ((chosenBase+key*B+old.val:ℕ):Word w) := by
      change v 9+((visit v (i:Word w) m).key*v 3+old) = _
      rw [outBaseAt,keyAt,capAt]
      push_cast; ring
    rw [dst,addr,mark,railAt,writeMemory_nat _ _ (destFit good),writeMemory_nat _ _ countFit,
      writeMemory_nat _ _ markFit]
    have actual : untouched=true ∧ (m (counterBase+key)).val<B := good
    unfold natStep
    rw [ite_eq_left actual]
    push_cast; rfl
  · rw [ite_eq_right good,←oldAt,commit_zero,mark,writeMemory_nat _ _ markFit]
    have actual : ¬(untouched=true ∧ (m (counterBase+key)).val<B) := good
    unfold natStep
    rw [ite_eq_right actual]

end Hierarchy.GridPassageRAMRow

end OAI
