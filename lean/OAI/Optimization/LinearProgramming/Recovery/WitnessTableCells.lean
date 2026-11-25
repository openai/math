import OAI.Optimization.LinearProgramming.Elimination.Augmented
import OAI.Optimization.LinearProgramming.Recovery.Presentation
import OAI.Optimization.LinearProgramming.Geometry.UniformCopy
import OAI.Optimization.LinearProgramming.Geometry.UniformTable

/-! Write the augmented transpose of the witness equations, with coordinate zero
normalized to one. Source matrix entries are read unchanged from their original area. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessTable

open RAM Geometry

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The first equation fixes the anchor. The remaining equations are the rows of C.
This is definitionally the augmented row table for normalizedSystem. -/
def matrix {k n : ℕ} (C : Matrix (Fin k) (Fin n) K) (hn : 0 < n) :
    Matrix (Fin (n+1)) (Fin (k+1)) K :=
  Elimination.augmentedRows (Fin.cons (fun j : Fin n => if j=⟨0,hn⟩ then (1:K) else 0) C)
    (Presentation.anchorRhs k)

def cell : Block := .branch (.addrLT 32 15)
  (.branch (.addrLT 30 16) (.op (.const 6 1)) (.op (.const 6 0)))
  (.branch (.addrLT 30 15) (.op (.const 6 0)) (GramCopy.cell true))

def Keep (p : ℕ) := ¬TableScratch p ∧ p≠38 ∧ p≠39 ∧ p≠42
instance (p : ℕ) : Decidable (Keep p) := by unfold Keep; infer_instance

private def value (m : Memory K) : K :=
  if m.index 32 < m.index 15 then (if m.index 30 < m.index 16 then 1 else 0)
  else if m.index 30 < m.index 15 then 0 else m.data (GramCopy.sourceAddress true m)

private theorem eval_cell (P : K→Prop) (s : Memory K) (hs : s.AllData P) (h0 : P 0) (h1 : P 1) :
    ∃ t c, c ≤ GramCopy.readCost true s+4 ∧ Block.Eval (Memory.AllData P) cell s c t ∧
      t.data=Function.update s.data 6 (value s) ∧ GramCopy.KeepsAddresses s t := by
  have zero : Block.Eval (Memory.AllData P) (.op (.const 6 0)) s 1 (s.putData 6 0) := by
    simpa only [Rat.cast_zero] using Block.Eval.op_const s 6 0 hs (by simpa only [Rat.cast_zero] using hs.putData 6 h0)
  have one : Block.Eval (Memory.AllData P) (.op (.const 6 1)) s 1 (s.putData 6 1) := by
    simpa only [Rat.cast_one] using Block.Eval.op_const s 6 1 hs (by simpa only [Rat.cast_one] using hs.putData 6 h1)
  by_cases col : s.index 32 < s.index 15
  · have ct : (Cond.addrLT 32 15).test s=true := by simp [Cond.test,col]
    by_cases row : s.index 30 < s.index 16
    · have rt : (Cond.addrLT 30 16).test s=true := by simp [Cond.test,row]
      exact ⟨s.putData 6 1,5,by unfold GramCopy.readCost; omega,
        .branchTrue ct (.branchTrue rt one),
        by simp [value,col,row,Memory.putData],fun _ _ _ _ => rfl⟩
    · have rt : (Cond.addrLT 30 16).test s=false := by simp [Cond.test,row]
      exact ⟨s.putData 6 0,4,by omega,.branchTrue ct (.branchFalse rt zero),
        by simp [value,col,row,Memory.putData],fun _ _ _ _ => rfl⟩
  · have ct : (Cond.addrLT 32 15).test s=false := by simp [Cond.test,col]
    by_cases row : s.index 30 < s.index 15
    · have rt : (Cond.addrLT 30 15).test s=true := by simp [Cond.test,row]
      exact ⟨s.putData 6 0,4,by omega,.branchFalse ct (.branchTrue rt zero),
        by simp [value,col,row,Memory.putData],fun _ _ _ _ => rfl⟩
    · have rt : (Cond.addrLT 30 15).test s=false := by simp [Cond.test,row]
      obtain ⟨t,rd,dat,addr⟩ := GramCopy.cell_spec true P s hs
      exact ⟨t,1+(1+GramCopy.readCost true s),by omega,
        .branchFalse ct (.branchFalse rt rd),by simpa [value,col,row] using dat,addr⟩

private theorem callback {k n base out : ℕ} (C : Matrix (Fin k) (Fin n) K) (hn : 0 < n)
    (P : K→Prop) (m : Memory K) (h0 : P 0) (h1 : P 1)
    (a15 : m.index 15=1) (a16 : m.index 16=2) (a40 : m.index 40=base-(n+1))
    (a41 : m.index 41=n) (lo : 8 ≤ base) (room : n+1 ≤ base) (sep : base+k*n ≤ out)
    (input : uniformRect k n base m=C) :
    TableCallbackSpec cell P (fun a => 8 ≤ a) Keep m (n+1) (k+1) out (matrix C hn)
      (k*(4*n+5)+4*n+15) := by
  intro i j s hs i30 j32 inds words
  have p15 := (inds 15 (Or.inr (by decide))).trans a15
  have p16 := (inds 16 (Or.inr (by decide))).trans a16
  have p40 := (inds 40 (Or.inr (by decide))).trans a40
  have p41 := (inds 41 (Or.inr (by decide))).trans a41
  obtain ⟨t,c,hc,e,dat,idx⟩ := eval_cell P s hs h0 h1
  have cost : GramCopy.readCost true s ≤ k*(4*n+5)+4*n+6 := by
    change s.index 32*(4*s.index 41+5)+4*s.index 30+6 ≤ _
    rw [j32,p41,i30]
    have row : i.val ≤ n := by have := i.isLt; omega
    have col : j.val ≤ k := by have := j.isLt; omega
    have mul := Nat.mul_le_mul_right (4*n+5) col
    omega
  have matchValue : value s=matrix C hn i j := by
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        change value s=(1:K)
        simp [value,i30,j32,p15,p16]
      | succ b =>
        change value s=(0:K)
        simp [value,i30,j32,p15]
    | succ a =>
      cases j using Fin.cases with
      | zero =>
        change value s=(if a=⟨0,hn⟩ then 1 else 0)
        have iff : a.val+1 < 2 ↔ a=⟨0,hn⟩ := by
          constructor
          · intro lt
            apply Fin.ext
            change a.val=0
            omega
          · rintro rfl
            exact (by decide : (0 : ℕ)+1 < 2)
        simp only [value,i30,j32,p15,p16,Fin.val_zero,Fin.val_succ,Nat.zero_lt_one,
          ite_true,iff]
      | succ b =>
        change value s=C b a
        have atAddr : GramCopy.sourceAddress true s=base+b.val*n+a.val := by
          change s.index 40+s.index 32*s.index 41+s.index 30=_
          rw [p40,j32,p41,i30,Fin.val_succ,Fin.val_succ,Nat.succ_mul]
          omega
        have span := rectOffset_lt b a
        have src := words (base+b.val*n+a.val) (by omega) (Or.inl (by omega))
        have saved := congrFun (congrFun input b) a
        have fetched : s.data (GramCopy.sourceAddress true s)=C b a := by
          rw [atAddr]
          exact src.trans saved
        simp [value,i30,j32,p15,fetched]
  refine ⟨t,c,by omega,e,?_,?_,?_⟩
  · rw [dat,Function.update_self,matchValue]
  · intro a ha
    rw [dat,Function.update_of_ne (show a≠6 by omega)]
  · intro p hp
    rcases hp with control|kept
    · unfold TableControl at control
      exact idx p (by omega) (by omega) (by omega)
    · exact idx p kept.2.1 kept.2.2.1 kept.2.2.2

/-- The real rectangular writer produces every augmented witness coefficient and
preserves the source. Its address frame covers all caller registers at and above 43. -/
theorem table_spec {k n base out : ℕ} (C : Matrix (Fin k) (Fin n) K) (hn : 0 < n)
    (P : K→Prop) (m : Memory K) (hs : m.AllData P) (h0 : P 0) (h1 : P 1)
    (a15 : m.index 15=1) (a16 : m.index 16=2) (a31 : m.index 31=n+1)
    (a33 : m.index 33=k+1) (a35 : m.index 35=out) (a40 : m.index 40=base-(n+1))
    (a41 : m.index 41=n) (lo : 8 ≤ base) (room : n+1 ≤ base) (sep : base+k*n ≤ out)
    (input : uniformRect k n base m=C) :
    ∃ t c, c ≤ uniformTableTime (n+1) (k+1) (k*(4*n+5)+4*n+15) ∧
      Block.Eval (Memory.AllData P) (uniformTableBlock cell) m c t ∧
      uniformRect (n+1) (k+1) out t=matrix C hn ∧
      (∀ a, 8 ≤ a → (a < out ∨ out+(n+1)*(k+1) ≤ a) → t.data a=m.data a) ∧
      (∀ p, TableParameter p ∨ Keep p → t.index p=m.index p) ∧
      ∀ p, 43 ≤ p → t.index p=m.index p := by
  obtain ⟨t,c,clock,run,values,fr,ix⟩ := uniformTableBlock_spec cell P (fun a => 8 ≤ a)
    Keep m (n+1) (k+1) out (matrix C hn) _ (callback C hn P m h0 h1 a15 a16 a40 a41 lo room sep input)
    (fun _ h => h.1) (fun _ _ => by omega) a31 a33 a35 hs
  refine ⟨t,c,clock,run,values,fr,ix,?_⟩
  intro p hp
  exact ix p (.inr (by unfold Keep TableScratch; omega))

end WitnessTable
end Recovery
end LinearProgramming
end Optimization
end OAI
