import OAI.Optimization.LinearProgramming.BitRAM.Heap
import OAI.Optimization.LinearProgramming.BitRAM.IndexScript

/-! Clearing, reading and popping an actual linked bit stack. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM

variable {K : Type*}

open RAM RAM.Block RAM.Tape OracleSpec

namespace HeapRep

/-- Install a pointer to a word already represented by the immutable heap. This can also
clear a slot irrespective of its previous length by installing the empty pointer. -/
theorem replace_slot {p : BitProgram} {w : Slot p → Word} {m : Memory K} (h : HeapRep p w m)
    (slot : Slot p) {ptr : Nat} {word : Word} (ch : Chain m.index (heapStart p) (m.index freeReg) ptr word) :
    HeapRep p (Function.update w slot word) (m.putIndex (headReg slot) ptr) := by
  have hs := headReg_range p slot
  have hf : freeReg ≠ headReg slot := by unfold freeReg; omega
  have hn : nilReg ≠ headReg slot := by unfold nilReg; omega
  have eqv (i : Nat) (hl : heapStart p ≤ i) (_ : i < m.index freeReg) (_ : i%2=1) :
      (m.putIndex (headReg slot) ptr).index i = m.index i := Function.update_of_ne (by omega) _ _
  have fr : (m.putIndex (headReg slot) ptr).index freeReg = m.index freeReg := Function.update_of_ne hf _ _
  refine ⟨(Function.update_of_ne hn _ _).trans h.nilValue, fr ▸ h.freeLower, fr ▸ h.freeOdd, ?_⟩
  intro s
  rw [fr]
  by_cases he : s=slot
  · subst s
    rw [Memory.putIndex_same, Function.update_self]
    exact ch.transport le_rfl eqv
  · rw [Memory.putIndex_ne _ (fun hh => he (headReg_injective hh)),Function.update_of_ne he]
    exact (h.chain s).transport le_rfl eqv

theorem clear_slot {p : BitProgram} {w : Slot p → Word} {m : Memory K} (h : HeapRep p w m)
    (s : Slot p) : HeapRep p (Function.update w s []) (m.putIndex (headReg s) 0) :=
  h.replace_slot s .nil

/-- The reserved control band 37..64 is below every node and excludes every stack head. -/
theorem putHeader {p : BitProgram} {w : Slot p → Word} {m : Memory K} (h : HeapRep p w m)
    {i : Nat} (lo : 37 ≤ i) (hi : i < 65) (v : Nat) : HeapRep p w (m.putIndex i v) := by
  apply h.putOther i v (by unfold heapStart; omega) (by unfold nilReg; omega) (by unfold freeReg; omega)
  intro s
  cases s with
  | none => change i ≠ 35; omega
  | some s => change i ≠ 65+2*s.val; omega

end HeapRep

def pop (head : Nat) : Block := .branch (.addrLT nilReg head) (.op (.addrLoad head head)) .skip

def peekSteps (head : Nat) : List Instr :=
  [.addrCopy 0 head,.incr 0 0,.incr 0 0,.addrLoad 0 0,.incr 0 0]

def peek (head : Nat) : Block :=
  .branch (.addrLT nilReg head) (.straight (peekSteps head)) (.op (.addrConst 0 0))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Empty stacks remain empty; a nonempty pop loads the old head's actual link. -/
theorem pop_correct {p : BitProgram} {w : Slot p → Word} {m : Memory K} {P : K → Prop}
    (h : HeapRep p w m) (safe : Good P m) (s : Slot p) :
    ∃ (t : Memory K) (k : Nat), Eval (Good P) (pop (headReg s)) m k t ∧ k ≤ 3 ∧
      HeapRep p (Function.update w s (w s).tail) t ∧ t.data=m.data ∧
      ∀ j, j ≠ headReg s → t.index j=m.index j := by
  have tail := (h.chain s).tail
  by_cases hp : m.index (headReg s) = 0
  · have eqv : m.putIndex (headReg s) 0 = m := by
      rw [← hp]
      cases m; simp [Memory.putIndex]
    refine ⟨m,_,.branchFalse (by simp [Cond.test,h.nilValue,hp]) (.skip safe), by decide,?_,rfl,fun _ _ => rfl⟩
    have rp := h.replace_slot s tail
    simpa [hp,eqv] using rp
  · have rp := h.replace_slot s tail
    let t := m.putIndex (headReg s) (m.index (m.index (headReg s)))
    have he : Eval (Good P) (.op (.addrLoad (headReg s) (headReg s))) m 1 t := .op safe safe (fun _ => rfl)
    exact ⟨t,_,.branchTrue (by simp [Cond.test,h.nilValue,Nat.pos_of_ne_zero hp]) he,
      le_rfl,by simpa [hp] using rp,rfl,fun _ hj => Function.update_of_ne hj _ _⟩

/-- Read a finite stack's three-way top symbol into address register zero. -/
theorem peek_correct {p : BitProgram} {w : Slot p → Word} {m : Memory K} {P : K → Prop}
    (h : HeapRep p w m) (safe : Good P m) (s : Slot p) :
    ∃ (t : Memory K) (k : Nat), Eval (Good P) (peek (headReg s)) m k t ∧ k ≤ 7 ∧
      t.data=m.data ∧ (∀ j, j ≠ 0 → t.index j=m.index j) ∧ t.index 0=topTag (w s).head? := by
  have law := (h.chain s).top
  by_cases hp : m.index (headReg s) = 0
  · refine ⟨_,_,.branchFalse (by simp [Cond.test,h.nilValue,hp]) (eval_constI m safe 0 0), by decide,
      rfl,fun _ hj => Function.update_of_ne hj _ _,?_⟩
    simpa [hp] using law.symm
  · let is := peekSteps (headReg s)
    let t : Memory K := ⟨m.data,IndexScript.run is m.index⟩
    have he := IndexScript.correct is (by
      intro i hi; simp only [is,peekSteps,List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl <;> rfl) m safe
    have hptr : m.index (headReg s)+2 ≠ 0 := by omega
    refine ⟨t,_,.branchTrue (by simp [Cond.test,h.nilValue,Nat.pos_of_ne_zero hp]) he, by show 1+5+1 ≤ 7; decide,
      rfl,?_,?_⟩
    · intro j hj
      simp [t,is,peekSteps,IndexScript.run,IndexScript.update,Function.update_of_ne hj]
    · simpa [t,is,peekSteps,IndexScript.run,IndexScript.update,Function.update_apply,hptr,hp] using law.symm

/-- Reading the top symbol also retains the full bit-program boundary invariant. -/
theorem peek_rep {p : BitProgram} {c : p.Config} {m : Memory K} {P : K → Prop}
    (h : Rep p c m) (safe : Good P m) (s : Slot p) :
    ∃ (t : Memory K) (k : Nat), Eval (Good P) (peek (headReg s)) m k t ∧ k ≤ 7 ∧
      Rep p c t ∧ t.index 0=topTag ((contents c) s).head? ∧ t.data=m.data ∧
      ∀ j, j ≠ 0 → t.index j=m.index j := by
  obtain ⟨t,k,e,b,d,f,top⟩ := peek_correct h.heap safe s
  exact ⟨t,k,e,b,h.of_odd_eq (fun i hi _ => f i (by omega)),top,d,f⟩

end BitRAM
end LinearProgramming
end Optimization
end OAI
