import OAI.Optimization.LinearProgramming.RAM.CallableOddBlock
import OAI.Optimization.LinearProgramming.RAM.Array

/-! Borrow a third scalar for bounded counting while retaining every caller register.
The consumed request tag can store the old scalar because its original value is known on the branch. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace MinorInstall

open RAM RAM.Block RAM.Callable

def readTag : Block := .op (.load 2 80)
def parkCode : Block := .straight [.const 2 0,.store 80 3,.const 3 1]
def restoreCode (tag : ℕ) : Block := .straight [.load 3 80,.const 2 tag,.store 80 2,.const 2 0]

def parked (m : Memory ℚ) : Memory ℚ := (m.putData (m.index 80) (m.data 3)).putData 3 1

private theorem eq_mem {m t : Memory ℚ} (hd : ∀i,m.data i=t.data i) (hi : m.index=t.index) : m=t := by
  exact congrArg₂ Memory.mk (funext hd) hi

theorem readTag_eval (m : Memory ℚ) (P : ℚ → Prop) (tag : ℕ) (tagged : m.data (m.index 80)=(tag:ℚ))
    (safe : m.AllData P) : Eval (Memory.AllData P) readTag m 1 (m.putData 2 (tag:ℚ)) := by
  simpa [readTag,tagged] using Eval.op_load m 2 80 safe (safe.putData _ (safe _))

theorem park_eval (m : Memory ℚ) (P : ℚ → Prop) (tag : ℕ) (safe : m.AllData P) (allowed : P (tag:ℚ))
    (first : m.data 2=0) (one : P 1) :
    Eval (Memory.AllData P) parkCode (m.putData 2 (tag:ℚ)) 3 (parked m) := by
  let a := m.putData 2 (tag:ℚ)
  have sa := safe.putData 2 allowed
  have zero : P 0 := first ▸ safe 2
  have reset : a.putData 2 0=m := by
    refine eq_mem (m := a.putData 2 0) (t := m) ?_ rfl
    intro i
    by_cases hit : i=2 <;> simp_all [a,Memory.putData]
  have e1 : Eval (Memory.AllData P) (.op (.const 2 0)) a 1 m := by
    have h := Eval.op_const a 2 0 sa (sa.putData _ (by simpa only [Rat.cast_zero] using zero))
    simpa only [Rat.cast_zero,reset] using h
  let b := m.putData (m.index 80) (m.data 3)
  have e2 : Eval (Memory.AllData P) (.op (.store 80 3)) m 1 b := Eval.op_store m 80 3 safe (safe.putData _ (safe _))
  have e3 : Eval (Memory.AllData P) (.op (.const 3 1)) b 1 (parked m) := by
    simpa [parked,b] using Eval.op_const b 3 1 e2.safe_end (e2.safe_end.putData _ (by simpa only [Rat.cast_one] using one))
  exact e1.seq (e2.seq (e3.seq (.skip e3.safe_end)))

theorem parked_safe (m : Memory ℚ) (P : ℚ → Prop) (hm : m.AllData P) (one : P 1) : (parked m).AllData P :=
  (hm.putData _ (hm _)).putData _ one

@[simp] theorem parked_index (m : Memory ℚ) : (parked m).index=m.index := rfl

theorem parked_zero_two (m : Memory ℚ) (high : 35 ≤ m.index 80) (h : m.data 2=0) : (parked m).data 2=0 := by
  simpa [parked,show 2 ≠ m.index 80 by omega] using h

theorem parked_zero_29 (m : Memory ℚ) (high : 35 ≤ m.index 80) (h : m.data 29=0) : (parked m).data 29=0 := by
  simpa [parked,show 29 ≠ m.index 80 by omega] using h

@[simp] theorem parked_one (m : Memory ℚ) : (parked m).data 3=1 := by simp [parked]

theorem parked_source (m : Memory ℚ) (high : 35 ≤ m.index 80) (i : ℕ) (positive : 0 < i) :
    (parked m).data (m.index 80+i)=m.data (m.index 80+i) := by
  change Function.update (Function.update m.data (m.index 80) (m.data 3)) 3 1 (m.index 80+i)=_
  rw [Function.update_of_ne (by omega : m.index 80+i ≠ 3),Function.update_of_ne (by omega : m.index 80+i ≠ m.index 80)]

theorem restore_eval (m : Memory ℚ) (P : ℚ → Prop) (tag : ℕ) (hm : m.AllData P) (one : P 1)
    (high : 35 ≤ m.index 80) (first : m.data 2=0) (tagged : m.data (m.index 80)=(tag:ℚ)) :
    Eval (Memory.AllData P) (restoreCode tag) (parked m) 4 m := by
  let a := (parked m).putData 3 (m.data 3)
  let b := a.putData 2 (tag:ℚ)
  let c := b.putData (m.index 80) (tag:ℚ)
  let d := c.putData 2 0
  have saved : (parked m).data ((parked m).index 80)=m.data 3 := by
    simp [parked,show m.index 80 ≠ 3 by omega]
  have safe := parked_safe m P hm one
  have e1 : Eval (Memory.AllData P) (.op (.load 3 80)) (parked m) 1 a := by
    simpa only [a,saved] using Eval.op_load (parked m) 3 80 safe (safe.putData _ (safe _))
  have ht : P (tag:ℚ) := tagged ▸ hm _
  have e2 : Eval (Memory.AllData P) (.op (.const 2 tag)) a 1 b := by
    simpa [b] using Eval.op_const a 2 tag e1.safe_end (e1.safe_end.putData _ (by simpa using ht))
  have e3 : Eval (Memory.AllData P) (.op (.store 80 2)) b 1 c := by
    simpa [c,b,a] using Eval.op_store b 80 2 e2.safe_end (e2.safe_end.putData _ (e2.safe_end _))
  have zero : P 0 := first ▸ hm 2
  have e4 : Eval (Memory.AllData P) (.op (.const 2 0)) c 1 d := by
    simpa [d] using Eval.op_const c 2 0 e3.safe_end (e3.safe_end.putData _ (by simpa only [Rat.cast_zero] using zero))
  have final : d=m := by
    refine eq_mem (m := d) (t := m) ?_ rfl
    intro i
    simp only [d,c,b,a,parked,Memory.putData,Function.update_apply]
    split_ifs
    all_goals simp_all
  exact final ▸ e1.seq (e2.seq (e3.seq (e4.seq (.skip e4.safe_end))))

end MinorInstall
end Geometry
end LinearProgramming
end Optimization
end OAI
