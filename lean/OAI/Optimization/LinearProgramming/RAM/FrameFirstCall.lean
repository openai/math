import OAI.Optimization.LinearProgramming.RAM.FrameFirst

/-! The first feasibility call of Corollary 1.2, from the ordinary optimization input. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Call

variable {K : Type*}

open Block Tape

/-- Register layout after returning from the first feasibility call. The decoded
result and the original optimization input are simultaneously accessible. -/
structure AfterFirst [Zero K] (p : Program) (C E m d : Nat) (input obj : List K)
    (last : State K) (s : Memory K) : Prop where
  result : ∀ j, s.data (2*j) = last.data j
  addresses : ∀ j, s.index (2*j) = 2*(last.index j)
  original : ∀ j < (input++obj).length, s.data (3+2*j) = (start [m,d] (input++obj)).data j
  rows : s.index 9 = m
  cols : s.index 11 = d
  limit : s.index 21 = firstLimit p C E m d
  vacant : ∀ q, 2*(firstLimit p C E m d)+2 ≤ q → s.data q = 0 ∧ s.index q = 0

def firstReturnBase (p : Program) (C E : Nat) : Nat :=
  (firstPrelude p C E).size + (p.map width).sum

/-- Lay out the optimizer as the first prelude, protected first feasibility call,
and a single relocatable continuation implementing the two exits of that call. -/
def withFirstCall (p : Program) (C E : Nat) (next : Nat → Nat → Nat)
    (ending : Nat → Program) : Program :=
  let pre := firstPrelude p C E
  let off := firstReturnBase p C E
  pre.compile 0 ++ subroutine p pre.size (next off) ++ ending off

theorem withFirstCall_locations (p : Program) (C E : Nat) (next : Nat → Nat → Nat)
    (ending : Nat → Program) :
    let pre := firstPrelude p C E
    let off := firstReturnBase p C E
    let prog := withFirstCall p C E next ending
    CodeAt prog 0 (pre.compile 0) ∧ CodeAt prog pre.size (subroutine p pre.size (next off)) ∧
      CodeAt prog off (ending off) := by
  dsimp only
  let a := (firstPrelude p C E).compile 0
  let b := subroutine p (firstPrelude p C E).size (next (firstReturnBase p C E))
  have ha : a.length = (firstPrelude p C E).size := Block.length_compile _ _
  have hb : b.length = (p.map width).sum := Layout.assemble_length p width _ _ (emit_length _)
  refine ⟨⟨[],b++ending (firstReturnBase p C E),rfl,by simp [withFirstCall,b,List.append_assoc]⟩,
    ⟨a,ending (firstReturnBase p C E),ha,rfl⟩,⟨a++b,[],?_,by simp [a,b,withFirstCall]⟩⟩
  rw [List.length_append,ha,hb]; rfl

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

/-- The first normal-entry optimization call pays for all setup, every simulated
instruction, and every input word. Neither the callee nor its output is preloaded. -/
theorem normal_first_call (p : Program) (C E m d : Nat) (xs obj : List K)
    (hx : xs.length = primalLength m d) (hy : obj.length = d) (hz : P 0)
    (hs : Good P (start [m,d] (xs++obj)).memory)
    {target : Program} {ret : Nat → Nat}
    (pre : CodeAt target 0 ((firstPrelude p C E).compile 0))
    (code : CodeAt target (firstPrelude p C E).size (subroutine p (firstPrelude p C E).size ret))
    {k tag : Nat} (trace : Fin (k+1) → State K) (hrun : Trace p (start [m,d] xs) k trace)
    (hcost : k ≤ polyBound C E (m+d)) (hsafe : ∀ i j, P ((trace i).data j))
    (done : (trace (Fin.last k)).output = some tag) :
    ∃ n ≤ firstCost p C E m d + 2*k, ∃ out : Memory K,
      Execution target (fun st => ∀ j, P (st.data j)) (start [m,d] (xs++obj)) n (out.atPC (ret tag)) ∧
      AfterFirst p C E m d xs obj (trace (Fin.last k)) out := by
  obtain ⟨ready,r,prep,hr,h⟩ := firstPrelude_correct p C E m d xs obj hx hy hz hs
  obtain ⟨n,hn,out,callrun,res,addr,odd,oddi⟩ := invoke_prepared_trace ready [m,d] xs P code
    h.data h.index prep.safe_end trace hrun hsafe done
  have initialRun : Execution target (fun st => ∀ j, P (st.data j)) (start [m,d] (xs++obj)) r
      (ready.atPC (firstPrelude p C E).size) := by
    simpa only [Good,State.memory,Memory.atPC,start,Nat.zero_add] using prep.compile_correct pre
  refine ⟨r+n,Nat.add_le_add hr hn,out,initialRun.append callrun,
    res,addr,?_,(oddi 4).trans h.savedRows,(oddi 5).trans h.savedCols,(oddi 10).trans h.savedLimit,?_⟩
  · intro j hj
    rw [show 3+2*j = 2*(j+1)+1 by omega,odd]
    simpa only [show 2*(j+1)+1 = 3+2*j by omega] using h.saved j hj
  · let D := addressBudget p + xs.length + m + d + 2
    have fp : Footprint D (start [m,d] xs) := by
      apply Footprint.initial
      · dsimp [D]; omega
      · change 2 ≤ D; dsimp [D]; omega
      · intro a ha
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl | rfl <;> dsimp [D] <;> omega
    have lastfp := trace_footprint (show addressBudget p ≤ D by dsimp [D]; omega) fp hrun (Fin.last k)
    have hb : D+k ≤ firstLimit p C E m d := by
      apply le_trans _ (le_max_left _ _)
      have hm : m ≤ xs.length := by simp [hx,primalLength]
      dsimp only [D,rawLimit,firstSource,optimizationLength]
      rw [←hx]; omega
    intro q hq
    by_cases he : q%2=0
    · have hj : D+(Fin.last k).val < q/2 := by simp only [Fin.val_last]; omega
      have eq : q=2*(q/2) := by omega
      refine ⟨?_,?_⟩
      · calc out.data q = out.data (2*(q/2)) := congrArg out.data eq
             _ = _ := (res _).trans (lastfp.data_zero _ hj)
      · calc out.index q = out.index (2*(q/2)) := congrArg out.index eq
             _ = 0 := by rw [addr,lastfp.index_zero _ hj,Nat.mul_zero]
    · have hj : firstLimit p C E m d < q/2 := by omega
      have eq : q=2*(q/2)+1 := by omega
      exact ⟨(congrArg out.data eq).trans ((odd _).trans (h.oddDataTail _ hj)),
        (congrArg out.index eq).trans ((oddi _).trans (h.oddIndexTail _ hj))⟩

end Call
end RAM
end LinearProgramming
end Optimization
end OAI
