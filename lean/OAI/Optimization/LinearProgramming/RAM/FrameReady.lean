import OAI.Optimization.LinearProgramming.RAM.FramePack
import OAI.Optimization.LinearProgramming.RAM.CallHeader
import OAI.Optimization.LinearProgramming.RAM.CallPrepared

/-! A single fixed RAM prelude for repeated calls on flat scalar inputs. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Call

open Block Tape

/-- Set up both banks, then enter a caller-provided isolated program. Permanent odd
address registers 9, 11 and 21 retain the dimensions and the memory bound. -/
def prepareCallInputs : Block := .seq prepareScalars (.seq (.op (.addrCopy 5 21))
  (.seq (.op (.addrConst 7 0)) callHeader))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

theorem prepareCallInputs_correct (s : Memory K) (m d vs fs fn B : Nat) (input : List K)
    (hs : Good P s) (hzero : P 0) (hm : s.index 9=m) (hd : s.index 11=d)
    (hv : s.index 13=vs) (hn : s.index 15=input.length)
    (hf : s.index 17=fs) (hfn : s.index 19=fn) (hB : s.index 21=B)
    (hvs : 3+2*(input.length+fn) ≤ vs) (hfs : 3+2*(input.length+fn) ≤ fs)
    (dataTail : ∀ i, B ≤ i → s.data (2*i)=0) (idxTail : ∀ i, B ≤ i → s.index (2*i)=0)
    (stored : ∀ i < input.length, s.data (vs+i)=(start [m,d] input).data i) :
    ∃ t, Eval (Good P) prepareCallInputs s (8*(input.length+fn)+12*B+4*m+4*d+21) t ∧
      (∀ i, t.data (2*i)=(start [m,d] input).data i) ∧
      (∀ i, t.index (2*i)=2*(start [m,d] input).index i) ∧
      (∀ i < fn, t.data (3+2*i)=s.data (fs+i)) ∧
      (∀ q, q % 2 = 1 → q≠1 → 3+2*fn ≤ q → t.data q=s.data q) ∧
      ∀ r, r % 2 = 1 → r≠3 → r≠5 → r≠7 → r≠31 → r≠35 → t.index r = s.index r := by
  obtain ⟨u,ru,ud,us,ui,u3,_,utail⟩ := prepareScalars_correct_framed s vs input.length fs fn B
    hs hzero hv hn hf hfn hB hvs hfs dataTail
  let a := u.putIndex 5 (u.index 21)
  let b := a.putIndex 7 0
  have ra : Eval (Good P) (.op (.addrCopy 5 21)) u 1 a := eval_copyI u ru.safe_end _ _
  have rb : Eval (Good P) (.op (.addrConst 7 0)) a 1 b := eval_constI a ra.safe_end _ _
  have u21 : u.index 21 = B := (ui 21 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hB
  have u9 : u.index 9 = m := (ui 9 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hm
  have u11 : u.index 11 = d := (ui 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hd
  have tail (i : Nat) (hi : B ≤ i) : b.index (2*i) = 0 := by
    have hu := ui (2*i) (by omega) (by omega) (by omega) (by omega) (by omega)
    simpa [b,a,show 2*i ≠ 5 by omega,show 2*i ≠ 7 by omega,hu] using idxTail i hi
  obtain ⟨t,rt,td,ti,todd,_,_⟩ := callHeader_correct b B m d input rb.safe_end
    (by simp [b,a,u3]) (by simp [b,a,u21]) (by simp [b]) (by simp [b,a,u9])
    (by simp [b,a,u11]) tail
  refine ⟨t, ?_, ?_, ti, ?_, ?_, ?_⟩
  · rw [show 8*(input.length+fn)+12*B+4*m+4*d+21 =
        (8*(input.length+fn)+6*B+12)+(1+(1+(6*B+4*m+4*d+7))) by omega]
    exact ru.seq (ra.seq (rb.seq rt))
  · intro i
    rw [td]; change u.data (2*i) = _
    rw [ud]
    by_cases hi : i < input.length
    · simpa [hi] using stored i hi
    · simp [hi,start]
  · intro i hi; rw [td]; exact us i hi
  · intro q hodd h1 hbound; rw [td]; exact utail q hodd h1 hbound
  · intro r hodd h3 h5 h7 h31 h35
    rw [todd r hodd h5 h7]
    simpa [b,a,h5,h7] using ui r h3 h5 h7 h31 h35

end Call
end RAM
end LinearProgramming
end Optimization
end OAI
