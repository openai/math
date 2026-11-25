import OAI.ThreeFlat.RAM.HistoryNodeReverse

namespace OAI
/-! # Every stored ownership index follows the actual chronological parent chain -/

namespace ThreeFlat.RAM.HistoryNodeDirectory.Reverse

open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {w n : ℕ} (A : Chronology n) (B : Banks w) (m : Memory w)

/-- All root entries past the current reverse cursor already agree with
the transitive history ownership. All parent words are still available. -/
private def Ready (i : ℕ) (m : Memory w) :=
  (∀ a : Fin n, a.val<A.firstFinal → m (B.nodes.val+8*a.val+1) = (A.parent a).val) ∧
  (∀ a : Fin n, i≤a.val → m (B.roots.val+a.val) = A.root a)

private theorem sumWord (x y : Word w) (fit : x.val+y.val < 2^w) : (x+y).val=x.val+y.val := by
  rw [Fin.val_add,Nat.mod_eq_of_lt fit]

private theorem rootStep (i : Fin n) (first : B.first.val=A.firstFinal) (fit : n < 2^w)
    (oldEnd : B.nodes.val+8*n ≤ B.roots.val) (space : B.roots.val+n ≤ 2^w) (ready : Ready A B (i.val+1) m) :
    Ready A B i.val (put B i.val m) := by
  have ai := i.isLt
  have pi := (A.parent i).isLt
  have rowNat : (((i.val : Word w)*8+B.nodes+1).val) = B.nodes.val+8*i.val+1 := by
    have e : (i.val : Word w)*8 + B.nodes+1 = ((i.val*8 + B.nodes.val+1 : ℕ) : Word w) := by simp
    rw [e,Fin.val_cast_of_lt (by omega)]; omega
  have dst : (B.roots+(i.val : Word w)).val = B.roots.val+i.val := by
    apply Eq.trans (sumWord _ _ (by rw [Fin.val_cast_of_lt (ai.trans fit)]; omega))
    rw [Fin.val_cast_of_lt (ai.trans fit)]
  have field : fetch B (i.val : Word w) m = (A.root i : Word w) := by
    unfold fetch
    have test : ((i.val : Word w)<B.first) ↔ i.val<A.firstFinal := by change ((i.val : Word w)).val<_ ↔ _; rw [Fin.val_cast_of_lt (ai.trans fit),first]
    by_cases past : i.val<A.firstFinal
    · rw [ite_eq_left (test.mpr past),rowNat,ready.1 i past]
      have adr : (((A.parent i).val : Word w)+B.roots).val = B.roots.val+(A.parent i).val := by
        rw [sumWord,Fin.val_cast_of_lt (pi.trans fit),Nat.add_comm]
        rw [Fin.val_cast_of_lt (pi.trans fit)]; omega
      have follows : A.root i=A.root (A.parent i) := by rw [Chronology.root,dite_eq_left past]
      rw [adr,ready.2 (A.parent i) (A.later i past),follows]
    · rw [ite_eq_right (test.not.mpr past),Chronology.root,dite_eq_right past,Nat.cast_sub (Nat.le_of_not_gt past)]
      simp [←first]
  constructor
  · intro a ha
    have al := a.isLt
    simp only [put,writeMemory,dst,ite_eq_right (show B.nodes.val+8*a.val+1 ≠ B.roots.val+i.val by omega),ready.1 a ha]
  · intro a hi
    unfold put writeMemory
    rw [dst]
    by_cases eq : a=i
    · subst a; simp only [ite_true,field]
    · have ne : a.val≠i.val := fun e => eq (Fin.ext e)
      rw [ite_eq_right (by omega),ready.2 a (by omega)]

/-- The remaining descending sweep preserves all non-root addresses. -/
theorem sweep_frame (i : ℕ) (baseFit : B.roots.val+i ≤ 2^w) (addr : ℕ)
    (outside : addr < B.roots.val ∨ B.roots.val+i ≤ addr) : sweep B i m addr = m addr := by
  induction i generalizing m with
  | zero => rfl
  | succ i ih =>
    have lt : i<2^w := by omega
    rw [sweep,ih (put B i m) (by omega) (by omega)]
    simp only [put,writeMemory,Fin.val_add,Fin.val_cast_of_lt lt,Nat.mod_eq_of_lt (show B.roots.val+i<2^w by omega),
      ite_eq_right (show addr≠B.roots.val+i by omega)]

theorem sweep_correct_of_inner (first : B.first.val=A.firstFinal) (fit : n<2^w)
    (oldEnd : B.nodes.val+8*n ≤ B.roots.val) (space : B.roots.val+n ≤ 2^w)
    (parents : ∀ a : Fin n, a.val<A.firstFinal → m (B.nodes.val+8*a.val+1)=(A.parent a).val) (i : Fin n) :
    sweep B n m (B.roots.val+i.val) = A.root i := by
  have go (j : ℕ) (mem : Memory w) (le : j≤n) (ok : Ready A B j mem) : Ready A B 0 (sweep B j mem) := by
    induction j generalizing mem with
    | zero => exact ok
    | succ j ih =>
      exact ih (put B j mem) (by omega) (rootStep A B mem ⟨j,by omega⟩ first fit oldEnd space ok)
  exact (go n m le_rfl ⟨parents,fun a h => False.elim (by have := a.isLt; omega)⟩).2 i (Nat.zero_le _)

theorem sweep_correct (first : B.first.val=A.firstFinal) (fit : n<2^w)
    (oldEnd : B.nodes.val+8*n ≤ B.roots.val) (space : B.roots.val+n ≤ 2^w)
    (parents : ∀ a : Fin n, m (B.nodes.val+8*a.val+1)=(A.parent a).val) (i : Fin n) :
    sweep B n m (B.roots.val+i.val) = A.root i :=
  sweep_correct_of_inner A B m first fit oldEnd space (fun a _=>parents a) i

end ThreeFlat.RAM.HistoryNodeDirectory.Reverse

end OAI
