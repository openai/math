import OAI.Optimization.LinearProgramming.BitRAM.IndexScript
import OAI.Optimization.LinearProgramming.RAM.StrideCopy
import OAI.Optimization.LinearProgramming.Specification

/-! Last-stage publication from the native solver's stride-two scalar bank into the sealed
RAM output convention. The zero-th returned component is written last, after register zero
has served as the streaming scratch for the remaining components. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace Publish

open RAM RAM.Block BitRAM.IndexScript Matrix
open scoped Matrix

/-- Read pointer in 14 and length in 15. All dimensions presented to the principal
comparator are positive, hence every selected branch has at least one output component. -/
private def prepareOp : List Instr := [.addrCopy 10 14,.incr 10 10,.incr 10 10,.addrConst 11 1,.decr 13 15]

def block : Block := .seq (.straight prepareOp)
  (.seq (StrideCopy.block false 10 11 12 13 0 2 1) (.op (.load 0 14)))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Works for either the final feasible point or the Farkas multiplier, preserving all
scalar height bounds at every instruction. The orientation flag is left in address 16. -/
theorem block_spec (n src : ℕ) (s : Memory K) (v : Fin n→K) (P : K→Prop) (hs : s.AllData P)
    (hn : 0 < n) (sep : n ≤ src) (s14 : s.index 14=src) (s15 : s.index 15=n)
    (input : ∀ i : Fin n,s.data (src+2*i.val)=v i) :
    ∃ t, Eval (Memory.AllData P) block s (8*(n-1)+8) t ∧ (∀ i : Fin n,t.data i.val=v i) ∧ t.index 16=s.index 16 := by
  let a : Memory K := ⟨s.data,run prepareOp s.index⟩
  have prep : Eval (Memory.AllData P) (.straight prepareOp) s 5 a := correct prepareOp
    (by intro op hop; simp [prepareOp] at hop; rcases hop with h|h|h|h <;> subst op <;> rfl) s hs
  have a10 : a.index 10=src+2 := by simp [a,prepareOp,run,update,s14,Nat.add_assoc]
  have a11 : a.index 11=1 := by simp [a,prepareOp,run,update]
  have a13 : a.index 13=n-1 := by simp [a,prepareOp,run,update,s15]
  have a14 : a.index 14=src := by simp [a,prepareOp,run,update,s14]
  have a16 : a.index 16=s.index 16 := by simp [a,prepareOp,run,update]
  obtain ⟨b,copy,vals,dataFrame,_,_,_,addrFrame⟩ := StrideCopy.block_correct P a false 10 11 12 13 0 2 1 (n-1)
    prep.safe_end a13 (by decide) (by decide) (by simp)
    (fun j _ => by simp [StrideCopy.address,StrideCopy.move,a10])
    (fun j _ => by simp [StrideCopy.address,StrideCopy.move,a11])
    (fun x y hxy hy => by simp [StrideCopy.address,StrideCopy.move,a10,a11]; omega)
  have b14 : b.index 14=src := (addrFrame 14 (by decide) (by decide) (by decide)).trans a14
  have base : b.data src=s.data src := dataFrame src (by omega)
    (fun j hj => by simp [StrideCopy.address,StrideCopy.move,a11]; omega)
  let t := b.putData 0 (b.data (b.index 14))
  have st : t.AllData P := (show b.AllData P from copy.safe_end).putData 0 (copy.safe_end _)
  have out := prep.seq (copy.seq (Eval.op_load b 0 14 copy.safe_end st))
  refine ⟨t,?_,?_,(addrFrame 16 (by decide) (by decide) (by decide)).trans a16⟩
  · have ticks : 5+((n-1)*8+2+1) = 8*(n-1)+8 := by omega
    rw [← ticks]
    exact out
  · intro i
    by_cases hi : i.val=0
    · simp [t,hi,b14,base,←input i]
    · obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hi
      have jlt : j < n-1 := by have := i.isLt; omega
      have dst : StrideCopy.address false (a.index 11) 1 j = i.val := by
        change a.index 11 + 1*j = i.val
        rw [a11,Nat.one_mul]
        omega
      have srcAt : StrideCopy.address false (a.index 10) 2 j = src+2*i.val := by
        change a.index 10 + 2*j = src+2*i.val
        rw [a10,hj,Nat.mul_succ]
        omega
      have h := vals j jlt
      rw [dst,srcAt] at h
      exact (show t.data i.val = b.data i.val from Memory.putData_ne _ hi _).trans (h.trans (input i))

omit [IsStrictOrderedRing K] in
/-- A normalized sparse certificate on the exposed prefix meets both public solution layouts. -/
theorem feasibleResult {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (x : Fin d→K)
    (s : State K) (tag : s.output=some 0) (read : ∀ i,s.data i.val=x i) (h : A*ᵥx ≤ b) :
    FeasibilityOutput A b s ∧ NormalizedFeasibilityOutput A b s := by
  have out : readVector s 0 d = x := by funext i; simpa [readVector] using read i
  exact ⟨Or.inl ⟨tag,out.symm ▸ h⟩,Or.inl ⟨tag,out.symm ▸ h⟩⟩

theorem certificateResult {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b y : Fin m→K)
    (s : State K) (tag : s.output=some 1) (read : ∀ i,s.data i.val=y i) (hzero : 0 ≤ y)
    (ann : A.transpose*ᵥy=0) (norm : b ⬝ᵥ y = -1) (sparse : (Finset.univ.filter (fun i => y i≠0)).card ≤ A.rank+1) :
    FeasibilityOutput A b s ∧ NormalizedFeasibilityOutput A b s := by
  have out : readVector s 0 m = y := by funext i; simpa [readVector] using read i
  have c : Certificate A b y := ⟨hzero,ann,norm.trans_lt neg_one_lt_zero,sparse⟩
  exact ⟨Or.inr ⟨tag,out.symm ▸ c⟩,Or.inr ⟨tag,out.symm ▸ c,out.symm ▸ norm⟩⟩

end Publish
end Recovery
end LinearProgramming
end Optimization
end OAI
