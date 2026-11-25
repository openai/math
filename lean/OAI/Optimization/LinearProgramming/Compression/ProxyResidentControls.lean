import Mathlib.Tactic.IntervalCases
import OAI.Optimization.LinearProgramming.Compression.ProxyResidentCode
import OAI.Optimization.LinearProgramming.Compression.ProxyEvenDoubles

/-! ## Control registers for scattering the resident numerical minor cache -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ResidentInstall

open RAM GeneratorTable

structure Started {K : Type*} [Zero K] (cap : ℕ) (original t : Memory K) : Prop where
  source : t.index 0=cap
  outer : t.index 1=4*cap+2
  inner : t.index 2=4*cap
  zeroIndex : t.index 3=0
  stop : t.index 8=15
  cutoff : t.index 14=60
  zeroScalar : t.data 1=0
  metadata : ∀ i<4, t.index (10+i)=original.index (102+i)
  highIndex : ∀ i, 16 ≤ i → t.index i=original.index i
  scalar : ∀ i, i≠1 → t.data i=original.data i

structure Finished {K : Type*} (s t : Memory K) : Prop where
  metadata : ∀ i<4, t.index (57+2*i)=s.index (10+i)
  frame : ∀ i, i∉[57,59,61,63] → t.index i=s.index i
  data : t.data=s.data

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The prologue takes exactly `12*cap+16` instructions, including the zero write. -/
theorem startBlock_eval (P : K → Prop) (s : Memory K) (cap : ℕ) (hcap : s.index 0=cap)
    (hs : s.AllData P) (hzero : P 0) : ∃ t,
    Block.Eval (Memory.AllData P) startBlock s (12*cap+16) t ∧ Started cap s t := by
  let a := applyPlan capture s
  let b := ServiceFill.doubleWord a 1 0
  let c := ServiceFill.doubleWord b 2 1
  let d := applyPlan setup c
  let t := d.putData 1 0
  have ea : Block.Eval (Memory.AllData P) (addressPlan capture) s 4 a := addressPlan_spec (fun f => ∀ i,P (f i)) _ _ hs
  have a0 : a.index 0=cap := by simp [a,capture,applyPlan,AddressSet.apply,hcap]
  have eb := ServiceFill.doubleWord_eval P a 1 0 ea.safe_end (by decide) (by decide) (by decide)
  have b1 : b.index 1=2*cap := by simp [b,ServiceFill.doubleWord,a0]
  have ec := ServiceFill.doubleWord_eval P b 2 1 eb.safe_end (by decide) (by decide) (by decide)
  have ed : Block.Eval (Memory.AllData P) (addressPlan setup) c 5 d := addressPlan_spec (fun f => ∀ i,P (f i)) _ _ ec.safe_end
  have ht : t.AllData P := ed.safe_end.putData 1 hzero
  have et : Block.Eval (Memory.AllData P) (.op (.const 1 0)) d 1 t := by
    simpa [t] using Block.Eval.op_const (safe := Memory.AllData P) d 1 0 ed.safe_end (by simpa [t] using ht)
  have c2 : c.index 2=4*cap := by
    calc
      c.index 2 = 2*(2*cap) := by simp [c,ServiceFill.doubleWord,b1]
      _ = 4*cap := by omega
  refine ⟨t,?_,?_,?_,?_,?_,?_,?_,by simp [t],?_,?_,?_⟩
  · have run := ea.seq (eb.seq (ec.seq (ed.seq et)))
    rw [a0,b1] at run
    have clock : 4+((4*cap+3)+((4*(2*cap)+3)+(5+1)))=12*cap+16 := by omega
    rw [clock] at run
    exact run
  · simp [t,d,setup,applyPlan,AddressSet.apply,c,b,ServiceFill.doubleWord,a0]
  · simp [t,d,setup,applyPlan,AddressSet.apply,c2]
  · simp [t,d,setup,applyPlan,AddressSet.apply,c2]
  · simp [t,d,setup,applyPlan,AddressSet.apply]
  · simp [t,d,setup,applyPlan,AddressSet.apply]
  · simp [t,d,setup,applyPlan,AddressSet.apply]
  · intro i hi
    interval_cases i <;> simp [t,d,setup,c,b,ServiceFill.doubleWord,a,capture,applyPlan,AddressSet.apply]
  · intro i hi
    simp [t,d,setup,c,b,ServiceFill.doubleWord,a,capture,applyPlan,AddressSet.apply,
      show i≠1 by omega,show i≠2 by omega,show i≠3 by omega,show i≠5 by omega,
      show i≠8 by omega,show i≠10 by omega,show i≠11 by omega,show i≠12 by omega,
      show i≠13 by omega,show i≠14 by omega]
  · intro i hi
    rw [show t.data i=d.data i from Memory.putData_ne _ hi _,show d.data=c.data from applyPlan_data _ _]
    exact congrFun (applyPlan_data capture s) i

/-- Copy the saved words into their four designated odd physical registers. All scalar
data and every other address are preserved. -/
theorem finishBlock_eval (P : K → Prop) (s : Memory K) (hs : s.AllData P) : ∃ t,
    Block.Eval (Memory.AllData P) finishBlock s 4 t ∧ Finished s t := by
  let t := applyPlan publish s
  refine ⟨t,addressPlan_spec (fun f => ∀ i,P (f i)) _ _ hs,?_,?_,applyPlan_data _ _⟩
  · intro i hi
    interval_cases i <;> simp [t,publish,applyPlan,AddressSet.apply]
  · intro i hi
    simp at hi
    simp [t,publish,applyPlan,AddressSet.apply,hi]

end ResidentInstall
end Compression
end LinearProgramming
end Optimization
end OAI
