import OAI.Optimization.LinearProgramming.BitRAM.Heap
import OAI.Optimization.LinearProgramming.BitRAM.IndexScript

/-! Constant-cost immutable list allocation on the physical RAM. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM

variable {K : Type*}

open RAM RAM.Block RAM.Tape OracleSpec

def pushSteps (head valReg : Nat) : List Instr :=
  [.addrStore freeReg head,.addrCopy head freeReg,.incr freeReg freeReg,.incr freeReg freeReg,
   .addrStore freeReg valReg,.incr freeReg freeReg,.incr freeReg freeReg]

def pushFrom (head valReg : Nat) : Block := .straight (pushSteps head valReg)

def push (head : Nat) (b : Bool) : Block := .seq (.op (.addrConst 0 (bitNat b))) (pushFrom head 0)

/-- Exactly the fresh node, its bit field, the moved head and the allocator change. -/
structure PushEffect (m t : Memory K) (head : Nat) (b : Bool) : Prop where
  data : t.data=m.data
  frontier : t.index freeReg = m.index freeReg+4
  headValue : t.index head=m.index freeReg
  link : t.index (m.index freeReg)=m.index head
  bit : t.index (m.index freeReg+2)=bitNat b
  frame : ∀ i, i ≠ freeReg → i ≠ head → i ≠ m.index freeReg → i ≠ m.index freeReg+2 →
    t.index i=m.index i

private theorem pushPre (a : Nat→Nat) (h v : Nat) (lower : 35≤h) (limit : h<a freeReg) (vs : v<31) :
    IndexScript.run (pushSteps h v) a =
      Function.update (Function.update (Function.update (Function.update a (a freeReg) (a h)) h (a freeReg))
        (a freeReg+2) (a v)) freeReg (a freeReg+4) := by
  have f : 33 < a freeReg := by omega
  have hF : freeReg ≠ h := by unfold freeReg; omega
  have fF : freeReg ≠ a freeReg := by change 33 ≠ a freeReg; omega
  have vF : v ≠ a freeReg := by omega
  have vh : v ≠ h := by omega
  have vr : v ≠ freeReg := by unfold freeReg; omega
  have hf : h ≠ a freeReg := by omega
  have ff : freeReg ≠ a freeReg+2 := by change 33 ≠ a freeReg+2; omega
  simp only [pushSteps,IndexScript.run,IndexScript.update,Function.update_of_ne fF,
    Function.update_of_ne hF,Function.update_self, Function.update_of_ne vF,
    Function.update_of_ne vh,Function.update_of_ne vr,Function.update_of_ne ff]
  funext i
  by_cases hx : i=freeReg
  · subst i; simp
  · by_cases hi : i=a freeReg+2
    · subst i; simp [ff.symm]
    · simp [Function.update_apply,hx,hi]

variable {K : Type*}

private theorem push_effect {p : BitProgram} {w : Slot p → Word} {m : Memory K}
    (h : HeapRep p w m) (s : Slot p) (v : Nat) (vs : v<31) (b : Bool) (hv : m.index v = bitNat b) :
    PushEffect m ⟨m.data,IndexScript.run (pushSteps (headReg s) v) m.index⟩ (headReg s) b := by
  obtain ⟨hlo,hhi,_⟩ := headReg_range p s
  have hl : headReg s < m.index freeReg := hhi.trans_le h.freeLower
  have hf : 33 < m.index freeReg := by omega
  rw [pushPre m.index _ v hlo hl vs]
  refine ⟨rfl,?_,?_,?_,?_,?_⟩
  · simp
  · simp [show headReg s ≠ freeReg by unfold freeReg; omega,
      show headReg s ≠ m.index freeReg+2 by omega]
  · simp [show m.index freeReg ≠ freeReg by change _ ≠ 33; omega,
      show m.index freeReg ≠ headReg s by omega]
  · simp [show m.index freeReg+2 ≠ freeReg by change _ ≠ 33; omega,hv]
  · intro i h1 h2 h3 h4
    simp [h1,h2,h3,h4]

/-- Update the logical word store after creating the actual node fields. -/
theorem HeapRep.pushed {p : BitProgram} {w : Slot p → Word} {m t : Memory K} (h : HeapRep p w m)
    (s : Slot p) (b : Bool) (he : PushEffect m t (headReg s) b) :
    HeapRep p (Function.update w s (b::w s)) t := by
  have hl := h.freeLower
  have base : 65 ≤ heapStart p := by unfold heapStart; omega
  have hs := headReg_range p s
  have old (j : Nat) (hj : heapStart p ≤ j) (hj' : j<m.index freeReg) (_ : j%2=1) : t.index j=m.index j :=
    he.frame j (by unfold freeReg; omega) (by omega) (by omega) (by omega)
  refine ⟨(he.frame nilReg (by decide) (by unfold nilReg; omega) (by unfold nilReg; omega)
      (by unfold nilReg; omega)).trans h.nilValue,he.frontier ▸ (by omega),?_,?_⟩
  · rw [he.frontier]; have := h.freeOdd; omega
  · intro j
    rw [he.frontier]
    by_cases hjs : j=s
    · subst j
      rw [Function.update_self,he.headValue]
      apply Chain.cons hl (by omega) h.freeOdd he.bit
      rw [he.link]
      exact (h.chain s).transport (by omega) old
    · have hj := headReg_range p j
      rw [Function.update_of_ne hjs,he.frame _ (by unfold freeReg; omega)
        (fun h => hjs (headReg_injective h)) (by omega) (by omega)]
      exact (h.chain j).transport (by omega) old

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Native push from a constructed address bit. No scalar cell changes. -/
theorem pushFrom_correct {p : BitProgram} {w : Slot p → Word} {m : Memory K} {P : K → Prop}
    (h : HeapRep p w m) (safe : Good P m) (s : Slot p) (b : Bool)
    (v : Nat) (vs : v<31) (hv : m.index v=bitNat b) :
    ∃ t, Eval (Good P) (pushFrom (headReg s) v) m 7 t ∧
      PushEffect m t (headReg s) b ∧ HeapRep p (Function.update w s (b::w s)) t := by
  let t := ({data := m.data, index := IndexScript.run (pushSteps (headReg s) v) m.index} : Memory K)
  have run := IndexScript.correct (pushSteps (headReg s) v) (by
    intro i hi; simp only [pushSteps,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl) m safe
  have he := push_effect h s v vs b hv
  exact ⟨t,run,he,h.pushed s b he⟩

/-- Pushing a literal uses one extra construction step in scratch index zero. -/
theorem push_correct {p : BitProgram} {w : Slot p → Word} {m : Memory K} {P : K → Prop}
    (h : HeapRep p w m) (safe : Good P m) (s : Slot p) (b : Bool) :
    ∃ t, Eval (Good P) (push (headReg s) b) m 8 t ∧
      PushEffect (m.putIndex 0 (bitNat b)) t (headReg s) b ∧
      HeapRep p (Function.update w s (b::w s)) t := by
  let start := m.putIndex 0 (bitNat b)
  have he := eval_constI m safe 0 (bitNat b)
  obtain ⟨t,hr,hf,hw⟩ := pushFrom_correct (h.putScratch (i:=0) (by decide) _) he.safe_end s b 0
    (by decide) (Memory.putIndex_same m 0 (bitNat b))
  exact ⟨t,.seq he hr,hf,hw⟩

end BitRAM
end LinearProgramming
end Optimization
end OAI
