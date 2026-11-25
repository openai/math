import OAI.Optimization.LinearProgramming.RAM.Call
import Mathlib.Tactic.IntervalCases

/-! A fixed caller for two three-outcome comparison programs. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Caller-owned scalar registers are zero. The low caller index records the selected branch. -/
private def dispatchFrame (K : Type*) [Zero K] (right : Bool) : Memory K where
  data := fun _ => 0
  index := fun j => if j=0 then right.toNat else 0

private def dispatchIndexWord (right : Bool) (dims : List ℕ) (j : ℕ) : ℕ :=
  if j%2=0 then 2*(dims[j/2]?.getD 0) else if j/2=0 then right.toNat else 0

/-- Even index slots hold doubled source addresses. Odd index slot 1 selects the callee;
its extra slot is present even when the source dimension list is empty. -/
def dispatchDims (right : Bool) (dims : List ℕ) : List ℕ :=
  List.ofFn fun j : Fin (2*(dims.length+1)) => dispatchIndexWord right dims j

private def dispatchScalarWord {K : Type*} [Zero K] (xs : List K) (j : ℕ) : K :=
  if j%2=0 then xs[j/2]?.getD 0 else 0

/-- The selected callee's input scalars occupy all even slots in their original order. -/
def dispatchScalars {K : Type*} [Zero K] (xs : List K) : List K :=
  List.ofFn fun j : Fin (2*xs.length) => dispatchScalarWord xs j

@[simp] theorem length_dispatchDims (right : Bool) (dims : List ℕ) :
    (dispatchDims right dims).length = 2*(dims.length+1) := by simp only [dispatchDims, List.length_ofFn]

@[simp] theorem length_dispatchScalars {K : Type*} [Zero K] (xs : List K) :
    (dispatchScalars xs).length = 2*xs.length := by simp [dispatchScalars]

private theorem get_dispatchDims (right : Bool) (dims : List ℕ) (j : ℕ) :
    (dispatchDims right dims)[j]?.getD 0 = dispatchIndexWord right dims j := by
  simp only [dispatchDims, List.getElem?_ofFn]
  split
  · rfl
  · rename_i h
    have ho : dims.length ≤ j/2 := by omega
    have hne : j/2 ≠ 0 := by omega
    simp [dispatchIndexWord,List.getElem?_eq_none ho,hne]

private theorem get_dispatchScalars {K : Type*} [Zero K] (xs : List K) (j : ℕ) :
    (dispatchScalars xs)[j]?.getD 0 = dispatchScalarWord xs j := by
  simp only [dispatchScalars, List.getElem?_ofFn]
  split
  · rfl
  · rename_i h
    have ho : xs.length ≤ j/2 := by omega
    simp [dispatchScalarWord,List.getElem?_eq_none ho]

private theorem dispatch_start {K : Type*} [Zero K] (right : Bool) (dims : List ℕ) (xs : List K) :
    start (dispatchDims right dims) (dispatchScalars xs) =
      (Call.pack (start dims xs).memory (dispatchFrame K right)).atPC 0 := by
  change ((start (dispatchDims right dims) (dispatchScalars xs)).memory).atPC 0 = _
  apply congrArg (fun m : Memory K => m.atPC 0)
  apply congrArg₂ Memory.mk
  · exact funext fun j => get_dispatchScalars xs j
  · exact funext fun j => get_dispatchDims right dims j

private def retAddr (tag : ℕ) := 1+tag

private def dispatchLeft (p : Program) : Program := Call.subroutine p 4 retAddr

private def dispatchRightPC (p : Program) : ℕ := 4+(dispatchLeft p).length

private def dispatchBase (right : Bool) (p : Program) : ℕ := if right then dispatchRightPC p else 4

private def dispatchHeader (p : Program) : Program :=
  [.branchAddrLT 3 1 (dispatchRightPC p) 4, .halt 0, .halt 1, .halt 2]

/-- A fixed branch, three fixed return addresses, and the two statically relocated callees.
Selecting the branch uses one address comparison. -/
def comparisonDispatchProgram (p₀ p₁ : Program) : Program :=
  dispatchHeader p₀ ++ (dispatchLeft p₀ ++ Call.subroutine p₁ (dispatchRightPC p₀) retAddr)

private theorem installed (p₀ p₁ : Program) (right : Bool) :
    CodeAt (comparisonDispatchProgram p₀ p₁) (dispatchBase right p₀)
      (Call.subroutine (if right then p₁ else p₀) (dispatchBase right p₀) retAddr) := by
  have whole : CodeAt (comparisonDispatchProgram p₀ p₁) 0
      (dispatchHeader p₀ ++ (dispatchLeft p₀ ++ Call.subroutine p₁ (dispatchRightPC p₀) retAddr)) :=
    CodeAt.whole _
  cases right
  · exact whole.right.left
  · exact whole.right.right

private theorem halt_instruction (p₀ p₁ : Program) (tag : ℕ) (htag : tag < 3) :
    (comparisonDispatchProgram p₀ p₁)[retAddr tag]? = some (.halt tag) := by
  interval_cases tag <;> rfl

private theorem branch_instruction {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p₀ p₁ : Program) (right : Bool) (v : Memory K) :
    let m := Call.pack v (dispatchFrame K right)
    step (comparisonDispatchProgram p₀ p₁) (m.atPC 0) = some (m.atPC (dispatchBase right p₀)) := by
  cases right <;> rfl

/-- One RAM selects the prepared source tape and returns its three-way tag. All original scalar
and address registers remain available at even addresses. Relocation costs at most twice the
original step count and the two surrounding instructions are the dispatch and final halt. -/
theorem comparisonDispatch_safe {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p₀ p₁ : Program) (right : Bool) (dims : List ℕ) (xs : List K)
    {k tag : ℕ} (source : Fin (k+1) → State K) (htag : tag < 3)
    (h : Trace (if right then p₁ else p₀) (start dims xs) k source)
    (hout : (source (Fin.last k)).output=some tag) (P : K → Prop) (hzero : P 0)
    (hs : ∀ i j, P ((source i).data j)) :
    ∃ l ≤ 2*k+2, ∃ tr : Fin (l+1) → State K,
      Trace (comparisonDispatchProgram p₀ p₁) (start (dispatchDims right dims) (dispatchScalars xs)) l tr ∧
      (tr (Fin.last l)).output=some tag ∧
      (∀ j, (tr (Fin.last l)).data (2*j)=(source (Fin.last k)).data j) ∧
      (∀ j, (tr (Fin.last l)).index (2*j)=2*(source (Fin.last k)).index j) ∧
      ∀ i j, P ((tr i).data j) := by
  let old := if right then p₁ else p₀
  let prog := comparisonDispatchProgram p₀ p₁
  let base := dispatchBase right p₀
  let f := dispatchFrame K right
  let good := fun d : ℕ → K => ∀ j, P (d j)
  let z := source (Fin.last k)
  let m := Call.pack (start dims xs).memory f
  let endmem := Call.pack z.memory f
  have hpacked (i : Fin (k+1)) : good (Call.pack (source i).memory f).data := by
    intro j
    by_cases hj : j%2=0
    · simpa [Call.pack,hj,State.memory] using hs i (j/2)
    · simpa [Call.pack,hj,f,dispatchFrame] using hzero
  obtain ⟨l,hl,run⟩ := Call.simulate_execution (installed p₀ p₁ right) (Execution.of_trace h hpacked)
  have hsrc : Call.image f retAddr (Layout.addr old Call.width base) (start dims xs) = m.atPC base := by
    simp [Call.image,Call.position,Layout.addr,start,m]
  have hfin : Call.image f retAddr (Layout.addr old Call.width base) z=endmem.atPC (retAddr tag) := by
    change z.output = some tag at hout
    simp [Call.image,Call.position,hout,endmem]
  change Execution prog (fun s => good s.data)
    (Call.image f retAddr (Layout.addr old Call.width base) (start dims xs)) l
    (Call.image f retAddr (Layout.addr old Call.width base) z) at run
  rw [hsrc,hfin] at run
  have first : Execution prog (fun s => good s.data) (m.atPC 0) 1 (m.atPC base) :=
    .one run.safe_start (branch_instruction p₀ p₁ right _) run.safe_start
  let doneState : State K := {endmem.atPC (retAddr tag) with output := some tag}
  have last : Execution prog (fun s => good s.data) (endmem.atPC (retAddr tag)) 1 doneState := by
    apply Execution.one run.safe_end _ run.safe_end
    simp [prog,step,Memory.atPC,halt_instruction p₀ p₁ tag htag,execInstr,doneState]
  obtain ⟨tr,ht,hend,hgood⟩ := ((first.append run).append last).to_trace
  refine ⟨_,by omega,tr,?_,?_,?_,?_,hgood⟩
  · simpa only [dispatch_start] using ht
  · rw [hend]
  · intro j; rw [hend]; exact Call.data_even z.memory f j
  · intro j; rw [hend]; exact Call.index_even z.memory f j

/-- For rational callees the exact original register bound suffices. The zero required to pad
the saved file already occurs past the end of every native input tape. -/
theorem comparisonDispatch_trace (p₀ p₁ : Program) (right : Bool) (dims : List ℕ) (xs : List ℚ)
    {k tag B : ℕ} (source : Fin (k+1) → State ℚ) (htag : tag < 3)
    (h : Trace (if right then p₁ else p₀) (start dims xs) k source)
    (hout : (source (Fin.last k)).output=some tag) (hs : ∀ i, scalarBound B (source i)) :
    ∃ l ≤ 2*k+2, ∃ tr : Fin (l+1) → State ℚ,
      Trace (comparisonDispatchProgram p₀ p₁) (start (dispatchDims right dims) (dispatchScalars xs)) l tr ∧
      (tr (Fin.last l)).output=some tag ∧
      (∀ j, (tr (Fin.last l)).data (2*j)=(source (Fin.last k)).data j) ∧
      (∀ j, (tr (Fin.last l)).index (2*j)=2*(source (Fin.last k)).index j) ∧
      ∀ i, scalarBound B (tr i) := by
  have h0 := hs 0 xs.length
  rw [h.1] at h0
  have hz : ratBits 0 ≤ B := by simpa [start] using h0
  exact comparisonDispatch_safe p₀ p₁ right dims xs source htag h hout (fun q => ratBits q ≤ B) hz hs

end Compression
end LinearProgramming
end Optimization
end OAI
