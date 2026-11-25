import OAI.Optimization.LinearProgramming.Compression.ProxyRange
import OAI.Optimization.LinearProgramming.FieldTransfer.Execution
import OAI.Optimization.LinearProgramming.FieldTransfer.ProxyRange

/-! An instruction-level implementation of the power search and exponent recovery. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

/-- Scalar 0 is normalized in place. The upward scan writes successive powers to the stack
starting at register 8. On the downward scan scalar 3 holds the product of the accepted powers,
and scalar 4 holds the integer exponent recovered so far. Address 0 initially holds the fuel. -/
def logRangeProgram : Program := [
  .const 1 1, .branchLT 0 1 2 3, .div 0 1 0, .const 2 2,
  .copy 3 1, .const 4 0, .addrConst 1 0, .addrConst 2 8, .addrCopy 3 2,
  .branchLT 0 2 17 10, .branchAddrLT 1 0 12 11, .halt 1,
  .store 3 2, .incr 3 3, .decr 0 0, .mul 2 2 2, .jump 9,
  .branchAddrLT 2 3 19 18, .halt 0, .decr 3 3, .load 2 3,
  .mul 5 3 2, .add 4 4 4, .branchLT 0 5 17 24, .copy 3 5, .add 4 4 1, .jump 17]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Generic partial evaluation of the upward search and downward exponent recovery. -/
def rangeAnswer : ℕ → K → K → Option (ℕ × K)
  | 0, z, p => if z < p then some (0,1) else none
  | n+1, z, p =>
    if z < p then some (0,1) else
      match rangeAnswer n z (p*p) with
      | none => none
      | some (e,q) => if z < q*p then some (2*e,q) else some (2*e+1,q*p)

def normalizedRangeInput (a : K) : K := if a < 1 then a⁻¹ else a

namespace RangeKernel

def Scan (s : State K) (z p : K) (n ptr : ℕ) : Prop :=
  s.pc = 9 ∧ s.output = none ∧ s.data 0 = z ∧ s.data 1 = 1 ∧ s.data 2 = p ∧
  s.data 3 = 1 ∧ s.data 4 = 0 ∧ s.index 0 = n ∧ s.index 1 = 0 ∧
  s.index 2 = 8 ∧ s.index 3 = ptr

def Unwind (s : State K) (z : K) (ptr e : ℕ) (q : K) : Prop :=
  s.pc = 17 ∧ s.output = none ∧ s.data 0 = z ∧ s.data 1 = 1 ∧
  s.data 3 = q ∧ s.data 4 = (e : K) ∧ s.index 2 = 8 ∧ s.index 3 = ptr

def StackPrefix (s t : State K) (ptr : ℕ) : Prop :=
  ∀ j, 8 ≤ j → j < ptr → t.data j = s.data j

theorem range_run_add (s : State K) (i j : ℕ) :
    runExactly logRangeProgram s (i+j) =
      (runExactly logRangeProgram s i).bind (fun t => runExactly logRangeProgram t j) := by
  induction j with
  | zero => simp [runExactly]
  | succ j ih => simp [runExactly, ih, Option.bind_assoc]

theorem scan_init (mag : K) (hm : 0 < mag) (fuel : ℕ) (a : State K)
    (hpc : a.pc = 0) (ho : a.output = none) (hm0 : a.data 0 = mag) (hn0 : a.index 0 = fuel) :
    ∃ n ≤ 9, ∃ s, runExactly logRangeProgram a n = some s ∧
      Scan s (normalizedRangeInput mag) 2 fuel 8 := by
  by_cases h : mag < 1
  · refine ⟨9, le_rfl, ?_⟩
    simp [runExactly, step, logRangeProgram, execInstr, State.putData, State.putIndex,
      Function.update, hpc, ho, hm0, hn0, h, hm.ne', Scan, normalizedRangeInput]
  · refine ⟨8, by decide, ?_⟩
    simp [runExactly, step, logRangeProgram, execInstr, State.putData, State.putIndex,
      Function.update, hpc, ho, hm0, hn0, h, Scan, normalizedRangeInput]

theorem scan_push {s : State K} {z p : K} {n ptr : ℕ} (hptr : 8 ≤ ptr)
    (hh : Scan s z p (n+1) ptr) (hpz : p ≤ z) :
    ∃ t, runExactly logRangeProgram s 7 = some t ∧
      Scan t z (p*p) n (ptr+1) ∧ t.data ptr = p ∧ StackPrefix s t ptr := by
  obtain ⟨hpc, ho, h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈⟩ := hh
  have a0 : (0 : ℕ) ≠ ptr := by omega
  have a1 : (1 : ℕ) ≠ ptr := by omega
  have a2 : (2 : ℕ) ≠ ptr := by omega
  have a3 : (3 : ℕ) ≠ ptr := by omega
  have a4 : (4 : ℕ) ≠ ptr := by omega
  simp (config := {maxSteps := 100000}) [runExactly, step, logRangeProgram, execInstr, State.putData, State.putIndex,
    Function.update, hpc, ho, h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈, hpz.not_gt, Scan, StackPrefix,
    a0,a1,a2,a3,a4,a2.symm]
  intro j hj hlt
  split_ifs <;> first | rfl | omega

theorem scan_base {s : State K} {z p : K} {n ptr : ℕ}
    (hh : Scan s z p n ptr) (hpz : z < p) :
    ∃ t, runExactly logRangeProgram s 1 = some t ∧
      Unwind t z ptr 0 1 ∧ StackPrefix s t ptr := by
  obtain ⟨hpc, ho,h₀,h₁,h₂,h₃,h₄,_,_,h₇,h₈⟩ := hh
  simp [runExactly, step, logRangeProgram, execInstr, hpc, ho,h₀,h₁,h₂,h₃,h₄,h₇,h₈,
    hpz, Unwind, StackPrefix]

theorem scan_saturate {s : State K} {z p : K} {ptr : ℕ}
    (hh : Scan s z p 0 ptr) (hpz : p ≤ z) :
    ∃ t, runExactly logRangeProgram s 3 = some t ∧ t.output = some 1 := by
  obtain ⟨hpc, ho, h₀,_,h₂,_,_,h₅,h₆,_,_⟩ := hh
  simp [runExactly, step, logRangeProgram, execInstr, hpc, ho, h₀,h₂,h₅,h₆,hpz.not_gt]

theorem unwind_bit_exact {s : State K} {z p q : K} {ptr e : ℕ} (hptr : 8 ≤ ptr)
    (hh : Unwind s z (ptr+1) e q) (hp : s.data ptr = p) :
    ∃ t, runExactly logRangeProgram s (if z < q*p then 6 else 9) = some t ∧
      (if z < q*p then Unwind t z ptr (2*e) q else Unwind t z ptr (2*e+1) (q*p)) ∧
      StackPrefix s t ptr := by
  obtain ⟨hpc,ho,h₀,h₁,h₃,h₄,h₇,h₈⟩ := hh
  have hlt : 8 < ptr+1 := by omega
  have he : (e : K) + e = 2 * e := by ring
  by_cases h : z < q*p
  · simp (config := {maxSteps := 100000}) [runExactly, step, logRangeProgram, execInstr, State.putData, State.putIndex,
      Function.update, hpc, ho, h₀,h₁,h₃,h₄,h₇,h₈,hp,h,hlt,Unwind,StackPrefix,he]
    intro j hj _
    split_ifs <;> first | rfl | omega
  · simp (config := {maxSteps := 100000}) [runExactly, step, logRangeProgram, execInstr, State.putData, State.putIndex,
      Function.update, hpc, ho, h₀,h₁,h₃,h₄,h₇,h₈,hp,h,hlt,Unwind,StackPrefix,he]
    intro j hj _
    split_ifs <;> first | rfl | omega

theorem unwind_bit {s : State K} {z p q : K} {ptr e : ℕ} (hptr : 8 ≤ ptr)
    (hh : Unwind s z (ptr+1) e q) (hp : s.data ptr = p) :
    ∃ n ≤ 9, ∃ t, runExactly logRangeProgram s n = some t ∧
      (if z < q*p then Unwind t z ptr (2*e) q else Unwind t z ptr (2*e+1) (q*p)) ∧
      StackPrefix s t ptr := by
  obtain ⟨t, ht, hpost, hframe⟩ := unwind_bit_exact hptr hh hp
  exact ⟨_, by split <;> decide, t, ht, hpost, hframe⟩

theorem unwind_halt {s : State K} {z q : K} {e : ℕ} (hh : Unwind s z 8 e q) :
    ∃ t, runExactly logRangeProgram s 2 = some t ∧
      t.output = some 0 ∧ t.data 0 = z ∧ t.data 3 = q ∧ t.data 4 = (e : K) := by
  obtain ⟨hpc,ho,h₀,_,h₃,h₄,h₇,h₈⟩ := hh
  simp [runExactly, step, logRangeProgram, execInstr, hpc, ho, h₀,h₃,h₄,h₇,h₈]

theorem scan_correct (n : ℕ) {s : State K} {z p : K} {ptr : ℕ}
    (hptr : 8 ≤ ptr) (hh : Scan s z p n ptr) :
    ∃ ell ≤ 16*n+3, ∃ t, runExactly logRangeProgram s ell = some t ∧
      (match rangeAnswer n z p with
       | none => t.output = some 1
       | some (e,q) => Unwind t z ptr e q ∧ StackPrefix s t ptr) := by
  induction n generalizing s p ptr with
  | zero =>
    by_cases h : z < p
    · obtain ⟨t,ht,ho,hm⟩ := scan_base hh h
      exact ⟨1, by decide, t, ht, by simpa only [rangeAnswer, ite_eq_left h] using And.intro ho hm⟩
    · obtain ⟨t,ht,ho⟩ := scan_saturate hh (le_of_not_gt h)
      exact ⟨3, by decide, t, ht, by simpa only [rangeAnswer, ite_eq_right h] using ho⟩
  | succ n ih =>
    by_cases h : z < p
    · obtain ⟨t,ht,ho,hm⟩ := scan_base hh h
      exact ⟨1, by omega, t, ht, by simpa only [rangeAnswer, ite_eq_left h] using And.intro ho hm⟩
    · obtain ⟨u,hsu,huhead,huval,humem⟩ := scan_push hptr hh (le_of_not_gt h)
      obtain ⟨ell,hell,v,huv,hret⟩ := ih (by omega) huhead
      have hv : runExactly logRangeProgram s (7+ell) = some v := by
        rw [range_run_add, hsu, Option.bind_some]
        exact huv
      cases hs : rangeAnswer n z (p*p) with
      | none =>
        rw [hs] at hret
        exact ⟨7+ell, by omega, v, hv,
          by simpa only [rangeAnswer, ite_eq_right h, hs] using hret⟩
      | some pair =>
        rcases pair with ⟨e,q⟩
        rw [hs] at hret
        obtain ⟨hvhead,hvmem⟩ := hret
        have hval : v.data ptr = p := (hvmem ptr hptr (by omega)).trans huval
        obtain ⟨j, hj, t, ht, hout, htmem⟩ := unwind_bit hptr hvhead hval
        have hr : runExactly logRangeProgram s ((7+ell)+j) = some t := by
          rw [range_run_add, hv, Option.bind_some]
          exact ht
        have hmem : StackPrefix s t ptr := fun i hi hic =>
          (htmem i hi hic).trans ((hvmem i hi (by omega)).trans (humem i hi hic))
        refine ⟨(7+ell)+j, by omega, t, hr, ?_⟩
        by_cases hb : z < q*p
        · rw [ite_eq_left hb] at hout
          simpa only [rangeAnswer, ite_eq_right h, hs, ite_eq_left hb] using And.intro hout hmem
        · rw [ite_eq_right hb] at hout
          simpa only [rangeAnswer, ite_eq_right h, hs, ite_eq_right hb] using And.intro hout hmem

end RangeKernel

open RangeKernel

/-- The fixed RAM code refines the adaptive range search, including the exact `q=2^e`
register and the integer exponent on its small branch. Register traffic and stack
accesses are included in the uniform linear bound. -/
theorem logRangeProgram_trace_from (fuel : ℕ) {mag : K} (hm : 0 < mag) (a : State K)
    (hpc : a.pc = 0) (ho : a.output = none) (hm0 : a.data 0 = mag) (hn0 : a.index 0 = fuel) :
    ∃ ell ≤ 16*fuel+14, ∃ t : Fin (ell+1) → State K,
      Trace logRangeProgram a ell t ∧
      (match rangeAnswer fuel (normalizedRangeInput mag) 2 with
       | none => (t (Fin.last _)).output = some 1
       | some (e,q) => (t (Fin.last _)).output = some 0 ∧
          (t (Fin.last _)).data 0 = normalizedRangeInput mag ∧
          (t (Fin.last _)).data 3 = q ∧ (t (Fin.last _)).data 4 = (e : K)) := by
  obtain ⟨i,hi,s,hs,hh⟩ := scan_init mag hm fuel a hpc ho hm0 hn0
  obtain ⟨j,hj,u,hu,hret⟩ := scan_correct fuel (by decide) hh
  have hrun : runExactly logRangeProgram a (i+j) = some u := by
    rw [range_run_add, hs, Option.bind_some]
    exact hu
  cases haa : rangeAnswer fuel (normalizedRangeInput mag) 2 with
  | none =>
    rw [haa] at hret
    obtain ⟨t, htrace, hlast⟩ := (runExactly_iff_trace _).mp hrun
    exact ⟨i+j, by omega, t, htrace, hlast ▸ hret⟩
  | some pair =>
    rcases pair with ⟨e,q⟩
    rw [haa] at hret
    obtain ⟨v,hv,ho,h₀,hq,he⟩ := unwind_halt hret.1
    have hr : runExactly logRangeProgram a ((i+j)+2) = some v := by
      rw [range_run_add, hrun, Option.bind_some]
      exact hv
    obtain ⟨t,htrace,hlast⟩ := (runExactly_iff_trace _).mp hr
    exact ⟨(i+j)+2, by omega, t, htrace, hlast ▸ ⟨ho,h₀,hq,he⟩⟩

/-- Standalone specialization of the range machine to the canonical input registers. -/
theorem logRangeProgram_trace (fuel : ℕ) {mag : K} (hm : 0 < mag) :
    ∃ ell ≤ 16*fuel+14, ∃ t : Fin (ell+1) → State K,
      Trace logRangeProgram (start [fuel] [mag]) ell t ∧
      (match rangeAnswer fuel (normalizedRangeInput mag) 2 with
       | none => (t (Fin.last _)).output = some 1
       | some (e,q) => (t (Fin.last _)).output = some 0 ∧
          (t (Fin.last _)).data 0 = normalizedRangeInput mag ∧
          (t (Fin.last _)).data 3 = q ∧ (t (Fin.last _)).data 4 = (e : K)) :=
  logRangeProgram_trace_from fuel hm (start [fuel] [mag]) rfl rfl (by simp [start]) (by simp [start])

/-- The generic field algorithm gives the same answer as the counted rational evaluator. -/
theorem rangeAnswer_rat_eq (n : ℕ) (z p : ℚ) :
    rangeAnswer n z p = (powerSearch n z p).answer := by
  induction n generalizing p with
  | zero => by_cases h : z < p <;> simp [rangeAnswer, powerSearch, h]
  | succ n ih =>
    by_cases h : z < p
    · simp [rangeAnswer, powerSearch, h]
    · simp only [rangeAnswer, powerSearch, ite_eq_right h, ih]
      cases hs : (powerSearch n z (p*p)).answer with
      | none => rfl
      | some rem =>
        rcases rem with ⟨e,q⟩
        by_cases ht : z < q*p <;> simp [ht]

/-- The program produces the exact rational exponent and power certified by
the binary-log mantissa specification. -/
theorem logRangeProgram_exec (fuel : ℕ) {mag : ℚ} (hm : 0 < mag) :
    ∃ ell ≤ 16*fuel+14, ∃ t : Fin (ell+1) → State ℚ,
      Trace logRangeProgram (start [fuel] [mag]) ell t ∧
      (match (powerSearch fuel (normalizedMagnitude mag) 2).answer with
       | none => (t (Fin.last _)).output = some 1
       | some (e,q) => (t (Fin.last _)).output = some 0 ∧
          (t (Fin.last _)).data 0 = normalizedMagnitude mag ∧
          (t (Fin.last _)).data 3 = q ∧ (t (Fin.last _)).data 4 = (e : ℚ)) := by
  have hn : normalizedRangeInput mag = normalizedMagnitude mag := by
    by_cases h : mag < 1 <;> simp [normalizedRangeInput, normalizedMagnitude, h]
  obtain ⟨ell,hell,t,ht,hout⟩ := logRangeProgram_trace fuel hm
  refine ⟨ell,hell,t,ht,?_⟩
  rw [hn, rangeAnswer_rat_eq] at hout
  cases hh : (powerSearch fuel (normalizedMagnitude mag) 2).answer with
  | none => simpa only [hh] using hout
  | some pair => rcases pair with ⟨e,q⟩; simpa only [hh] using hout

omit [IsStrictOrderedRing K] in
theorem rangeAnswer_field_eq (n : ℕ) (z p : K) :
    rangeAnswer n z p = (RealProxy.powerSearch n z p).answer := by
  induction n generalizing p with
  | zero => by_cases h : z < p <;> simp [rangeAnswer, RealProxy.powerSearch, h]
  | succ n ih =>
    by_cases h : z < p
    · simp [rangeAnswer, RealProxy.powerSearch, h]
    · simp only [rangeAnswer, RealProxy.powerSearch, ite_eq_right h, ih]
      cases hs : (RealProxy.powerSearch n z (p*p)).answer with
      | none => rfl
      | some rem =>
        rcases rem with ⟨e,q⟩
        by_cases ht : z < q*p <;> simp [ht]

/-- In particular this identical RAM code computes the range and exponent of arbitrary
positive real coefficients. All branches are decided by field arithmetic and comparisons. -/
theorem realProxy_range_correct
    (fuel : ℕ) {mag : K} (hm : 0 < mag) :
    ∃ ell ≤ 16*fuel+14, ∃ t : Fin (ell+1) → State K,
      Trace logRangeProgram (start [fuel] [mag]) ell t ∧
      (match (RealProxy.powerSearch fuel (RealProxy.normalizedMagnitude mag) 2).answer with
       | none => (t (Fin.last _)).output = some 1
       | some (e,q) => (t (Fin.last _)).output = some 0 ∧
          (t (Fin.last _)).data 0 = RealProxy.normalizedMagnitude mag ∧
          (t (Fin.last _)).data 3 = q ∧ (t (Fin.last _)).data 4 = (e : K)) := by
  simpa only [← rangeAnswer_field_eq, normalizedRangeInput, RealProxy.normalizedMagnitude] using
    logRangeProgram_trace fuel hm

end Compression
end LinearProgramming
end Optimization
end OAI
