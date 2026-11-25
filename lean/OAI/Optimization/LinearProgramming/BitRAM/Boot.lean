import OAI.Optimization.LinearProgramming.BitRAM.Heap
import OAI.Optimization.LinearProgramming.BitRAM.IndexScript

/-! Initialize all physical heads of the fixed finite controller and the linked heap. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM

open RAM RAM.Block RAM.Tape OracleSpec

def headKeys (p : BitProgram) : List Nat := (List.finRange p.stackCount).map fun s => headReg (some s)

def headerSteps (p : BitProgram) : List Instr :=
  [.addrConst nilReg 0,.addrConst freeReg (heapStart p),.addrConst bufferReg 0,
   .addrConst bufferLenReg 0,.addrConst stateReg p.start.val,.addrConst askReg 0]

def clearHeads (keys : List Nat) := keys.map (fun j => Instr.addrConst j 0)

def reset (p : BitProgram) : Block := .seq (.straight (headerSteps p)) (.straight (clearHeads (headKeys p)))

private theorem clear_index (keys : List Nat) (a : Nat→Nat) (i : Nat) :
    IndexScript.run (clearHeads keys) a i = if i ∈ keys then 0 else a i := by
  induction keys generalizing a with
  | nil => simp [clearHeads,IndexScript.run]
  | cons j js ih =>
    change IndexScript.run (clearHeads js) (Function.update a j 0) i = _
    rw [ih]
    by_cases h : i ∈ js <;> by_cases h' : i=j <;> simp [h,h']

private theorem low_not_head (p : BitProgram) {i : Nat} (hi : i<65) : i ∉ headKeys p := by
  intro h
  obtain ⟨s,_,rfl⟩ := List.mem_map.mp h
  change 65+2*s.val < 65 at hi
  omega

/-- Reset is independent of input, takes six control stores plus one per stack, and
preserves arbitrary scalar data and all of the caller’s preconfigured packet windows. -/
theorem reset_correct {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : BitProgram) (m : Memory K) {P : K → Prop} (hm : Good P m) :
    ∃ (t : Memory K), Eval (Good P) (reset p) m (6+p.stackCount) t ∧ Rep p (p.initial []) t ∧
      t.data=m.data ∧ ∀ i, i ∉ [nilReg,freeReg,bufferReg,bufferLenReg,stateReg,askReg] →
        i ∉ headKeys p → t.index i=m.index i := by
  let u : Memory K := ⟨m.data,IndexScript.run (headerSteps p) m.index⟩
  let t : Memory K := ⟨u.data,IndexScript.run (clearHeads (headKeys p)) u.index⟩
  have header := IndexScript.correct (headerSteps p) (by
    intro i hi; simp [headerSteps] at hi; rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl) m hm
  have clear := IndexScript.correct (clearHeads (headKeys p)) (by
    intro i hi; obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi; rfl) u header.safe_end
  have low (i : Nat) (hi : i<65) : t.index i = u.index i := by
    change IndexScript.run _ _ i = _
    rw [clear_index,ite_eq_right_iff.mpr (fun h => (low_not_head p hi h).elim)]
  have head0 (s : Slot p) : t.index (headReg s) = 0 := by
    cases s with
    | none =>
      rw [low _ (by show 35<65; decide)]
      simp [u,headerSteps,IndexScript.run,IndexScript.update,headReg,nilReg,freeReg,bufferReg,
        bufferLenReg,stateReg,askReg]
    | some s =>
      change IndexScript.run _ _ _ = 0
      rw [clear_index]
      simp [headKeys]
  have h31 : t.index nilReg=0 := by
    rw [low _ (by decide)]; simp [u,headerSteps,IndexScript.run,IndexScript.update,nilReg,freeReg,
      bufferReg,bufferLenReg,stateReg,askReg]
  have h33 : t.index freeReg=heapStart p := by
    rw [low _ (by decide)]; simp [u,headerSteps,IndexScript.run,IndexScript.update,nilReg,freeReg,
      bufferReg,bufferLenReg,stateReg,askReg]
  refine ⟨t,?_,?_,rfl,?_⟩
  · simpa [reset,t,headerSteps,clearHeads,headKeys] using header.seq clear
  · refine ⟨⟨h31,h33.ge,by rw [h33]; unfold heapStart; omega,?_⟩,?_,?_,?_⟩
    · intro s
      have ew : contents (p.initial []) s = [] := by cases s <;> simp [contents,BitProgram.initial]
      rw [head0,ew]
      exact .nil
    · rw [low _ (by decide)]; simp [u,headerSteps,IndexScript.run,IndexScript.update,nilReg,freeReg,
        bufferReg,bufferLenReg,stateReg,askReg,BitProgram.initial]
    · rw [low _ (by decide)]; simp [u,headerSteps,IndexScript.run,IndexScript.update,nilReg,freeReg,
        bufferReg,bufferLenReg,stateReg,askReg,BitProgram.initial,pcCode]
    · rw [low _ (by decide)]; simp [u,headerSteps,IndexScript.run,IndexScript.update,nilReg,freeReg,
        bufferReg,bufferLenReg,stateReg,askReg]
  · intro i hi hj
    simp only [List.mem_cons,not_or] at hi
    change IndexScript.run _ _ i = _
    simp [clear_index,hj,u,headerSteps,IndexScript.run,IndexScript.update,hi]

end BitRAM
end LinearProgramming
end Optimization
end OAI
