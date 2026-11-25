import OAI.Optimization.LinearProgramming.Recovery.WitnessProgramCode
import OAI.Optimization.LinearProgramming.Recovery.BankRead
import OAI.Optimization.LinearProgramming.RAM.FrameHeaders
import OAI.Optimization.LinearProgramming.RAM.CallableReentrant
import OAI.Optimization.LinearProgramming.RAM.CallableOddCalls

/-! The finite witness subroutine and the return of its scalar coordinates to the LP caller. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace WitnessCall

open RAM RAM.Callable RAM.Call RAM.Tape

noncomputable def invoke : Fragment := .stage (.invoke WitnessProgram.program 1 (Odd.sink (.index 1)))
noncomputable def numericalFootprint (h n : ℕ) := max (addressBudget WitnessProgram.program) (max (h*n+n) (max 2 (h+n)))+WitnessProgram.clockPolynomial.eval (h+n)
noncomputable def numericalTime (h n cap : ℕ) := 19*cap+225+(2*WitnessProgram.clockPolynomial.eval (h+n)+2)

private def headers : HeaderPlan 220 := [(180,.val 0),(212,(.reg 151)+(.reg 150)),(181,.reg 212),(182,.reg 150)]

def receive : Fragment := .seq (Odd.leaf (HeaderPlan.code 230 headers)) (.ofBlock BankRead.copyWindow)
noncomputable def receivePolynomial : Polynomial ℕ := headers.budget
noncomputable def receiveTime (limit n : ℕ):=4*(receivePolynomial.eval limit)+(21*n+5)

/-- Header 212 retains the actual high vector address; the original data and all
metadata below 180 survive at the stated locations. -/
theorem receive_run {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K→Prop) (native caller : Memory K) (base n limit : ℕ) (w : Fin n→K)
    (sn : native.AllData P) (sc : caller.AllData P) (i150 : caller.index 150=n) (i151 : caller.index 151=base)
    (high : 5 ≤ base+n) (bounded : ∀j,caller.index j ≤ limit) (values : ∀j : Fin n,native.data j.val=w j) :
    ∃ t,receive.Run P (Odd.memory native caller) (receiveTime limit n) (Odd.memory native t) ∧ t.index 212=base+n ∧
      (∀j : Fin n,t.data (base+n+j.val)=w j) ∧ (∀a,a≠4 → (a<base+n ∨ base+n+n ≤ a) → t.data a=caller.data a) ∧
      t.index 24=caller.index 24 ∧ t.index 28=caller.index 28 ∧ t.index 29=caller.index 29 ∧
      t.index 60=caller.index 60 ∧ t.index 156=caller.index 156 := by
  let env:=fun j : Fin 220=>caller.index j.val
  obtain ⟨a,c,prep,clk,data,idx⟩:=headers.correct 230 (by decide) caller env (fun _=>rfl) sc
  have p151 : env 151=base:=i151
  have p150 : env 150=n:=i150
  have combined : env 151 + env 150 = base+n := congrArg₂ Nat.add p151 p150
  have dst : a.index 181 = base+n := (idx 181).trans combined
  have dest : a.index 212 = base+n := (idx 212).trans combined
  obtain ⟨t,k,hk,copy,word,rest,_,_,_,fr⟩:=BankRead.copyWindow_eval P native a sn prep.safe_end 0 (base+n) n
    (idx 180) dst ((idx 182).trans p150) high
  have pre:=Odd.leaf_run P native sn prep
  have hcost:=clk.trans (headers.cost_le _ _ (fun j=>bounded j.val))
  have timeBound : 4*c+k ≤ receiveTime limit n :=
    Nat.add_le_add (Nat.mul_le_mul_left 4 hcost) hk
  refine ⟨t,(pre.seq (Fragment.Run.ofBlock copy)).mono timeBound,
    (fr 212 (by decide) (by decide) (by decide)).trans dest,?_,?_,
    (fr 24 (by decide) (by decide) (by decide)).trans (idx 24),
    (fr 28 (by decide) (by decide) (by decide)).trans (idx 28),
    (fr 29 (by decide) (by decide) (by decide)).trans (idx 29),
    (fr 60 (by decide) (by decide) (by decide)).trans (idx 60),
    (fr 156 (by decide) (by decide) (by decide)).trans (idx 156)⟩
  · intro j;simpa using (word j.val j.isLt).trans (by simpa using values j)
  · intro j h4 h;exact (rest j h4 h).trans (congrFun data j)

end WitnessCall
end Recovery
end LinearProgramming
end Optimization
end OAI
