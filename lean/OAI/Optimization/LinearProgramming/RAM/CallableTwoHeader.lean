import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.RAM.FrameStatic
import Mathlib.Tactic.FinCases

/-! A two-dimensional ordinary input header for the finite caller bootstrap. Both the
length of the scalar tape and its required memory bound are evaluated by native code. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Boot

open Block Tape Call

/-- The values of a portable two-dimensional address expression. -/
def dimensions (m d : ℕ) (i : Fin 2) : ℕ := if i=0 then m else d

private def saved : AddressTerm 2 → AddressTerm 5
  | .val v => .val v
  | .reg i => if i=0 then .reg 3 else .reg 4
  | .binary o a b => .binary o (saved a) (saved b)

private theorem saved_value (e : AddressTerm 2) (env : Fin 5 → ℕ) :
    (saved e).value env=e.value (dimensions (env 3) (env 4)) := by
  induction e with
  | val _ => rfl
  | reg i => by_cases h : i=0 <;> simp [saved,AddressTerm.value,dimensions,h]
  | binary _ _ _ ha hb => simp [saved,AddressTerm.value,ha,hb]

/-- Compute the size and requested cap after saving both original dimension registers. -/
def twoDimPlan (len floor : AddressTerm 2) : HeaderPlan 5 :=
  [(3,.reg 0),(4,.reg 1),(2,saved len),(0,saved floor+2*.reg 2+72),(1,2)]

def twoDimStatic (len floor : AddressTerm 2) : ℕ :=
  max 64 (indexLimitBlock (HeaderPlan.code 5 (twoDimPlan len floor)))

def twoDimRawCap (len floor : AddressTerm 2) (m d : ℕ) : ℕ :=
  floor.value (dimensions m d)+2*len.value (dimensions m d)+72

def twoDimCap (len floor : AddressTerm 2) (m d : ℕ) : ℕ :=
  max (twoDimRawCap len floor m d) (twoDimStatic len floor)

private def raiseHeader (limit : ℕ) : Block := .seq (.op (.addrConst 5 limit))
  (.branch (.addrLT 0 5) (.op (.addrCopy 0 5)) .skip)

def twoDimHeader (len floor : AddressTerm 2) : Block :=
  .seq (HeaderPlan.code 5 (twoDimPlan len floor)) (raiseHeader (twoDimStatic len floor))

/-- The public LP coefficient and right-hand-side tape has `m*d+m` scalars. -/
def lpLength : AddressTerm 2 := .reg 0 * .reg 1 + .reg 0

@[simp] theorem lpLength_value (m d : ℕ) : lpLength.value (dimensions m d)=m*d+m := by
  simp [lpLength,AddressTerm.value,AddressOp.value,dimensions]

theorem twoDimCap_bounds (len floor : AddressTerm 2) (m d : ℕ) :
    floor.value (dimensions m d)≤twoDimCap len floor m d ∧
      2*len.value (dimensions m d)+4≤twoDimCap len floor m d ∧ 64≤twoDimCap len floor m d := by
  have h : twoDimRawCap len floor m d≤twoDimCap len floor m d := le_max_left ..
  unfold twoDimRawCap at h
  omega

/-- The exact prefix required by the finite bootstrap. Its scratch cells below the
computed cap will be overwritten. Addresses beyond the cap retain the ordinary zero tail. -/
structure TwoDimHeaderOut {K : Type*} (cap length m d : ℕ) (startMem out : Memory K) : Prop where
  capAt : out.index 0=cap
  countAt : out.index 1=2
  lengthAt : out.index 2=length
  rowAt : out.index 3=m
  columnAt : out.index 4=d
  scalar : out.data=startMem.data
  tail : ∀i,cap< i → out.index i=0

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

private theorem raiseHeader_correct (limit : ℕ) (s : Memory K) (hs : Good P s) :
    ∃ t k, Eval (Good P) (raiseHeader limit) s k t ∧ k≤4 ∧ t.data=s.data ∧
      t.index 0=max (s.index 0) limit ∧ ∀ j,j≠0 → j≠5 → t.index j=s.index j := by
  let a := s.putIndex 5 limit
  have first : Eval (Good P) (.op (.addrConst 5 limit)) s 1 a := eval_constI s hs _ _
  by_cases h : s.index 0 < limit
  · let t := a.putIndex 0 (a.index 5)
    have put : Eval (Good P) (.op (.addrCopy 0 5)) a 1 t := eval_copyI a first.safe_end _ _
    have guard : (Cond.addrLT 0 5).test a=true := by simp [Cond.test,a,h]
    exact ⟨t,4,first.seq (.branchTrue guard put),by decide,rfl,by simp [t,a,max_eq_right h.le],
      fun i h0 h5 => by simp [t,a,h0,h5]⟩
  · have guard : (Cond.addrLT 0 5).test a=false := by simp [Cond.test,a,h]
    exact ⟨a,2,first.seq (.branchFalse guard (.skip first.safe_end)),by decide,rfl,
      by simp [a,max_eq_left (Nat.le_of_not_gt h)],fun i _ h5 => by simp [a,h5]⟩

/-- From the public `[m,d]` header the fixed code preserves the whole scalar tape and
constructs `[cap,2,len(m,d),m,d]` in its first five native address cells. -/
theorem twoDimHeader_correct (len floor : AddressTerm 2) (m d : ℕ) (xs : List K)
    (hs : ((start [m,d] xs).memory).AllData P) :
    ∃ t k, Eval (Memory.AllData P) (twoDimHeader len floor) (start [m,d] xs).memory k t ∧
      k≤(HeaderPlan.budget (twoDimPlan len floor)).eval (m+d)+4 ∧
      TwoDimHeaderOut (twoDimCap len floor m d) (len.value (dimensions m d)) m d
        (start [m,d] xs).memory t := by
  let s := (start [m,d] xs).memory
  let env := fun i : Fin 5 => s.index i
  have henv (i : Fin 5) : env i≤ m+d := by
    fin_cases i <;> first
      | exact Nat.le_add_right m d
      | exact Nat.le_add_left d m
      | exact Nat.zero_le _
  obtain ⟨u,k,code,hk,ud,low⟩ := HeaderPlan.correct (P := P) (twoDimPlan len floor) 5 (by decide) s env (fun _ => rfl) hs
  obtain ⟨t,l,raise,hl,td,cap,other⟩ := raiseHeader_correct (twoDimStatic len floor) u code.safe_end
  have raw : u.index 0=twoDimRawCap len floor m d := by
    simpa [twoDimRawCap,twoDimPlan,HeaderPlan.output,saved_value,AddressTerm.value,AddressOp.value,env,s,State.memory,start] using low (0 : Fin 5)
  have frame (i : ℕ) (hi : twoDimCap len floor m d< i) : t.index i=0 := by
    have hh : twoDimStatic len floor ≤ twoDimCap len floor m d := le_max_right ..
    have big : 64≤twoDimStatic len floor := le_max_left ..
    have limit : indexLimitBlock (HeaderPlan.code 5 (twoDimPlan len floor)) ≤ twoDimStatic len floor := le_max_right ..
    rw [other i (by omega) (by omega),code.index_frame (indexWritesBelow_of_direct _ _ (header_direct _ _) limit) (by omega)]
    change ([m,d][i]?).getD 0=0
    have beyond : ([m,d] : List ℕ).length ≤ i := by
      change 2 ≤ i
      omega
    exact congrArg (fun cell : Option ℕ => cell.getD 0) (List.getElem?_eq_none beyond)
  have headerRun := code.seq raise
  have scalarInvariant : Tape.Good P = Memory.AllData P := by
    funext state
    rfl
  rw [scalarInvariant] at headerRun
  refine ⟨t,k+l,headerRun,Nat.add_le_add (hk.trans (HeaderPlan.cost_le _ _ _ henv)) hl,?_,?_,?_,?_,?_,td.trans ud,frame⟩
  · simpa only [twoDimCap,raw] using cap
  all_goals rw [other _ (by decide) (by decide)]
  all_goals first | exact (low (1 : Fin 5)).trans rfl |
    (first | apply (low (1 : Fin 5)).trans | apply (low (2 : Fin 5)).trans |
      apply (low (3 : Fin 5)).trans | apply (low (4 : Fin 5)).trans)
  all_goals simp [twoDimPlan,HeaderPlan.output,saved_value,AddressTerm.value,env,s,State.memory,start]

end Boot
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
