import OAI.Optimization.LinearProgramming.RAM.CallableBootOps
import OAI.Optimization.LinearProgramming.RAM.StrideCopy

/-! Stage the ordinary scalar input above the cap before scattering it. Saving
scalar zero first makes that register available to the fixed gather/scatter kernel. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Boot

open Block

def copyData (size ss ds : ℕ) : Block := StrideCopy.block false 3 4 5 size 0 ss ds

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem copyData_spec (P : K→Prop) (s : Memory K) (size ss ds n A D : ℕ)
    (hs : s.AllData P) (reg : size=2 ∨ size=6) (hn : s.index size=n)
    (ha : s.index 3=A) (hd : s.index 4=D) (src : 0 < A) (dst : 0 < D) (step : 0 < ds)
    (sep : A+ss*n+1 ≤ D ∨ D+ds*n ≤ A) :
    ∃ t, Eval (Memory.AllData P) (copyData size ss ds) s (n*(ss+ds+5)+2) t ∧
      (∀ i < n, t.data (D+ds*i)=s.data (A+ss*i)) ∧
      (∀ r, r≠0 → (∀ i < n, r≠D+ds*i) → t.data r=s.data r) ∧
      ∀ r, r≠3 → r≠4 → r≠5 → t.index r=s.index r := by
  obtain ⟨t,e,w,f,_,_,_,ix⟩ := StrideCopy.block_correct P s false 3 4 5 size 0 ss ds n
    hs hn (by rcases reg with rfl|rfl <;> decide) step (by simp)
    (fun i hi => by simp [ha]; omega) (fun i hi => by simp [hd]; omega)
    (by
      intro l j hlj hj
      have d := Nat.mul_lt_mul_of_pos_left (hlj.trans hj) step
      have a := Nat.mul_le_mul_left ss hj.le
      simp only [StrideCopy.address_forward,ha,hd]
      omega)
  exact ⟨t,e,by simpa [ha,hd] using w,by simpa [hd] using f,ix⟩

private def stageOps : List AddressOp := [.incr 7 0,.set 3 1,.incr 4 7,.decr 6 2]
def scalarStage : Block := .seq (program stageOps) (.seq (.op (.store 7 0)) (copyData 6 1 1))

theorem scalarStage_spec (P : K→Prop) (s : Memory K) (cap n : ℕ)
    (hs : s.AllData P) (h0 : s.index 0=cap) (h2 : s.index 2=n) (room : 2*n+4 ≤ cap)
    (zero : ∀r, n ≤ r → s.data r=0) :
    ∃ t, Eval (Memory.AllData P) scalarStage s (4+(1+((n-1)*7+2))) t ∧
      t.index 7=cap+1 ∧ (∀ i < n, t.data (cap+1+i)=s.data i) ∧
      (∀ r, r≠0 → n ≤ r → (r < cap+1 ∨ cap+1+n ≤ r) → t.data r=0) ∧
      ∀ r, r < 3 ∨ 7 < r → t.index r=s.index r := by
  let a := applyOps stageOps s
  have init := ops_spec P stageOps s hs
  have da : a.data=s.data := ops_data ..
  have p7 : a.index 7=cap+1 := by simp [a,stageOps,applyOps,AddressOp.apply,h0]
  let u := a.putData (cap+1) (s.data 0)
  have e : Eval (Memory.AllData P) (.op (.store 7 0)) a 1 u := by
    simpa only [u,p7,da] using Eval.op_store a 7 0 init.safe_end
      (init.safe_end.putData _ (init.safe_end 0))
  obtain ⟨t,copy,wr,df,af⟩ := copyData_spec P u 6 1 1 (n-1) 1 (cap+1+1) e.safe_end
    (.inr rfl) (by simp [u,a,stageOps,applyOps,AddressOp.apply,h2])
    (by simp [u,a,stageOps,applyOps,AddressOp.apply])
    (by simp [u,a,stageOps,applyOps,AddressOp.apply,h0]) (by decide) (by omega) (by decide)
    (.inl (by omega))
  refine ⟨t,init.seq (e.seq copy),(af _ (by decide) (by decide) (by decide)).trans p7,?_,?_,?_⟩
  · rintro (_|i) hi
    · have h := df (cap+1) (by omega) (by intro j hj; omega)
      simpa [u] using h
    · have h := wr i (by omega)
      have input : u.data (1+1*i)=s.data (i+1) := by
        calc
          u.data (1+1*i) = a.data (1+1*i) := Memory.putData_ne a (by omega) _
          _ = s.data (i+1) := by rw [da,one_mul,Nat.add_comm 1 i]
      rw [show cap+1+(i+1)=cap+1+1+1*i by omega]
      exact h.trans input
  · intro r hr hnr whereAt
    have fr := df r hr (by intro i hi; omega)
    by_cases h : r=cap+1
    · subst r
      have hn : n=0 := by omega
      have z := zero 0 (by omega)
      simpa [u,z] using fr
    · exact fr.trans ((Memory.putData_ne a h _).trans (by rw [da]; exact zero r hnr))
  · intro r hr
    have f := af r (by omega) (by omega) (by omega)
    simpa (disch := omega) [u,a,stageOps,applyOps,AddressOp.apply] using f

end Boot
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
