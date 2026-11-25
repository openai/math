import OAI.Optimization.LinearProgramming.BitRAM.HeapPush
import OAI.Optimization.LinearProgramming.BitRAM.HeapAccess

/-! Concrete scalar-RAM implementation of the ordinary instructions of the frozen bit program. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM

variable {K : Type*}

open RAM RAM.Block RAM.Tape OracleSpec

abbrev Op (p : BitProgram) := BitInstruction (Fin p.states) (Fin p.stackCount)

def ordinaryTarget {p : BitProgram} (c : p.Config) : Op p → Option p.Config
  | .jump q => some {c with pc := some q}
  | .push s b q => some {c with pc := some q,store := Function.update c.store s (b::c.store s)}
  | .pop s q => some {c with pc := some q,store := Function.update c.store s (c.store s).tail}
  | .emit b q => some {c with pc := some q,bufferRev := b::c.bufferRev}
  | .ask _ => none
  | .halt => some {c with pc := none}

def actionBlock (p : BitProgram) : Op p → Block
  | .jump q => .op (.addrConst stateReg q.val)
  | .push s b q => .seq (push (headReg (some s)) b) (.op (.addrConst stateReg q.val))
  | .pop s q => .seq (pop (headReg (some s))) (.op (.addrConst stateReg q.val))
  | .emit b q => .seq (push bufferReg b) (.seq (.op (.incr bufferLenReg bufferLenReg)) (.op (.addrConst stateReg q.val)))
  | .ask q => .seq (.op (.addrConst stateReg q.val)) (.op (.addrConst askReg 1))
  | .halt => .op (.addrConst stateReg p.states)

/-- On a non-oracle line the logical target is exactly one actual frozen bit instruction. -/
theorem ordinary_tick {p : BitProgram} (o : WordOracle) {c t : p.Config} {q : Fin p.states}
    (hpc : c.pc = some q) (h : ordinaryTarget c (p.instruction q (c.store (p.scan q)).head?) = some t) :
    p.tick o c = some (1,t) := by
  generalize hop : p.instruction q (c.store (p.scan q)).head? = op at h
  cases op <;> simp_all [ordinaryTarget,BitProgram.tick]

private theorem store_contents {p : BitProgram} (c : p.Config) (q : Option (Fin p.states))
    (s : Fin p.stackCount) (w : Word) :
    contents {c with pc := q,store := Function.update c.store s w} = Function.update (contents c) (some s) w := by
  funext j
  cases j with
  | none => simp [contents]
  | some j => by_cases h : j=s <;> simp [contents,h]

private theorem buffer_contents {p : BitProgram} (c : p.Config) (q : Option (Fin p.states)) (w : Word) :
    contents {c with pc := q,bufferRev := w} = Function.update (contents c) none w := by
  funext j; cases j <;> simp [contents]

private theorem header_ne_head {p : BitProgram} {i : Nat} (lo : 37 ≤ i) (hi : i < 65) (s : Slot p) :
    i≠headReg s := by cases s <;> simp [headReg,bufferReg] <;> omega

private theorem push_header {p : BitProgram} {w : Slot p → Word} {m t : Memory K} (h : HeapRep p w m)
    (s : Slot p) (b : Bool) (e : PushEffect (m.putIndex 0 (bitNat b)) t (headReg s) b)
    (i : Nat) (lo : 37 ≤ i) (hi : i < 65) : t.index i=m.index i := by
  have hf : (m.putIndex 0 (bitNat b)).index freeReg=m.index freeReg := Memory.putIndex_ne m (by decide : freeReg ≠ 0) _
  have hl := h.freeLower
  unfold heapStart at hl
  exact (e.frame i (by unfold freeReg; omega) (header_ne_head lo hi s) (by rw [hf]; omega)
    (by rw [hf]; omega)).trans (Function.update_of_ne (by omega) _ _)

private theorem push_even {p : BitProgram} {w : Slot p → Word} {m t : Memory K} (h : HeapRep p w m)
    (s : Slot p) (b : Bool) (e : PushEffect (m.putIndex 0 (bitNat b)) t (headReg s) b)
    (i : Nat) (hi : 64 ≤ i) (ev : i%2=0) : t.index i=m.index i := by
  have hf : (m.putIndex 0 (bitNat b)).index freeReg=m.index freeReg := Memory.putIndex_ne m (by decide : freeReg ≠ 0) _
  have hr := h.freeOdd
  have hd := (headReg_range p s).2.2
  exact (e.frame i (by unfold freeReg; omega) (by omega) (by rw [hf]; omega) (by rw [hf]; omega)).trans
    (Memory.putIndex_ne _ (by omega) _)

private theorem installPC {p : BitProgram} {c : p.Config} {m : Memory K}
    (h : HeapRep p (contents c) m) (hlen : m.index bufferLenReg = c.bufferRev.length)
    (hflag : m.index askReg=0) : Rep p c (m.putIndex stateReg (pcCode c.pc)) :=
  ⟨h.putHeader (by decide) (by decide) _,(Memory.putIndex_ne _ (by decide : bufferLenReg ≠ stateReg) _).trans hlen,
    Memory.putIndex_same _ _ _,(Memory.putIndex_ne _ (by decide : askReg ≠ stateReg) _).trans hflag⟩

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- All persistent caller headers for packet windows and application state. -/
def StableHeaders (m t : Memory K) : Prop := ∀ i, 43 ≤ i → i < 65 → t.index i=m.index i

/-- High even application cache cells are disjoint from all linked stack fields. -/
def StableEven (m t : Memory K) : Prop := ∀ i, 64 ≤ i → i%2=0 → t.index i=m.index i

/-- Ordinary source instructions each consume at most ten actual scalar-RAM instructions
and leave the scalar bank untouched. -/
theorem action_complete_frame {p : BitProgram} {c c' : p.Config} (op : Op p)
    (hstep : ordinaryTarget c op=some c') {m : Memory K} {P : K → Prop}
    (h : Rep p c m) (safe : Good P m) :
    ∃ (t : Memory K) (k : Nat), Eval (Good P) (actionBlock p op) m k t ∧ k≤10 ∧ Rep p c' t ∧ t.data=m.data ∧ StableHeaders m t ∧ StableEven m t := by
  cases op with
  | ask _ => contradiction
  | jump q =>
    simp only [ordinaryTarget,Option.some.injEq] at hstep; subst c'
    exact ⟨_,_,eval_constI m safe stateReg q.val,by decide,installPC h.heap h.bufferLength h.askReady,rfl,fun i hi _ => Function.update_of_ne (by unfold stateReg; omega) _ _,fun i hi _ => Function.update_of_ne (by unfold stateReg; omega) _ _⟩
  | halt =>
    simp only [ordinaryTarget,Option.some.injEq] at hstep; subst c'
    exact ⟨_,_,eval_constI m safe stateReg p.states,by decide,installPC h.heap h.bufferLength h.askReady,rfl,fun i hi _ => Function.update_of_ne (by unfold stateReg; omega) _ _,fun i hi _ => Function.update_of_ne (by unfold stateReg; omega) _ _⟩
  | push s b q =>
    simp only [ordinaryTarget,Option.some.injEq] at hstep; subst c'
    obtain ⟨t,he,hf,hh⟩ := push_correct h.heap safe (some s) b
    have hlen := (push_header h.heap (some s) b hf bufferLenReg (by decide) (by decide)).trans h.bufferLength
    have hflag := (push_header h.heap (some s) b hf askReg (by decide) (by decide)).trans h.askReady
    refine ⟨_,_,.seq he (eval_constI t he.safe_end _ _),by decide,installPC ?_ hlen hflag,hf.data,?_,?_⟩
    · rwa [store_contents]
    · intro i hi hj
      exact (Memory.putIndex_ne _ (by unfold stateReg; omega : i ≠ stateReg) _).trans
        (push_header h.heap (some s) b hf i (by omega) hj)
    · intro i hi ev
      exact (Memory.putIndex_ne _ (by unfold stateReg; omega : i ≠ stateReg) _).trans
        (push_even h.heap (some s) b hf i hi ev)
  | pop s q =>
    simp only [ordinaryTarget,Option.some.injEq] at hstep; subst c'
    obtain ⟨t,k,he,hk,hh,hd,hf⟩ := pop_correct h.heap safe (some s)
    have hlen := (hf bufferLenReg (header_ne_head (by decide) (by decide) (some s))).trans h.bufferLength
    have hflag := (hf askReg (header_ne_head (by decide) (by decide) (some s))).trans h.askReady
    refine ⟨_,_,.seq he (eval_constI t he.safe_end _ _),by omega,installPC ?_ hlen hflag,hd,?_,?_⟩
    · rwa [store_contents]
    · intro i hi hj
      exact (Memory.putIndex_ne _ (by unfold stateReg; omega : i ≠ stateReg) _).trans
        (hf i (header_ne_head (by omega) hj (some s)))
    · intro i hi ev
      have hodd := (headReg_range p (some s)).2.2
      exact (Memory.putIndex_ne _ (by unfold stateReg; omega : i ≠ stateReg) _).trans (hf i (by omega))
  | emit b q =>
    simp only [ordinaryTarget,Option.some.injEq] at hstep; subst c'
    obtain ⟨t,he,hf,hh⟩ := push_correct h.heap safe none b
    have hlen := (push_header h.heap none b hf bufferLenReg (by decide) (by decide)).trans h.bufferLength
    have hflag := (push_header h.heap none b hf askReg (by decide) (by decide)).trans h.askReady
    let u := t.putIndex bufferLenReg (t.index bufferLenReg+1)
    have hu := eval_incr t he.safe_end bufferLenReg bufferLenReg
    refine ⟨_,_,.seq he (.seq hu (eval_constI u hu.safe_end _ _)),by decide,installPC ?_ ?_ ?_,hf.data,?_,?_⟩
    · rw [buffer_contents]
      exact hh.putHeader (by decide) (by decide) _
    · simp [u,hlen]
    · exact (Memory.putIndex_ne _ (by decide : askReg ≠ bufferLenReg) _).trans hflag

    · intro i hi hj
      exact (Memory.putIndex_ne _ (by unfold stateReg; omega : i ≠ stateReg) _).trans
        ((Memory.putIndex_ne _ (by unfold bufferLenReg; omega : i ≠ bufferLenReg) _).trans
          (push_header h.heap none b hf i (by omega) hj))

    · intro i hi ev
      exact (Memory.putIndex_ne _ (by unfold stateReg; omega : i ≠ stateReg) _).trans
        ((Memory.putIndex_ne _ (by unfold bufferLenReg; omega : i ≠ bufferLenReg) _).trans
          (push_even h.heap none b hf i hi ev))

theorem action_framed {p : BitProgram} {c c' : p.Config} (op : Op p)
    (hstep : ordinaryTarget c op=some c') {m : Memory K} {P : K → Prop}
    (h : Rep p c m) (safe : Good P m) :
    ∃ (t : Memory K) (k : Nat), Eval (Good P) (actionBlock p op) m k t ∧ k≤10 ∧ Rep p c' t ∧ t.data=m.data ∧ StableHeaders m t := by
  obtain ⟨t,k,e,b,r,d,f,_⟩ := action_complete_frame op hstep h safe
  exact ⟨t,k,e,b,r,d,f⟩

theorem action_correct {p : BitProgram} {c c' : p.Config} (op : Op p)
    (hstep : ordinaryTarget c op=some c') {m : Memory K} {P : K → Prop}
    (h : Rep p c m) (safe : Good P m) :
    ∃ (t : Memory K) (k : Nat), Eval (Good P) (actionBlock p op) m k t ∧ k≤10 ∧ Rep p c' t ∧ t.data=m.data := by
  obtain ⟨t,k,e,b,r,d,_⟩ := action_framed op hstep h safe
  exact ⟨t,k,e,b,r,d⟩

/-- Immediately after dispatching `ask`, the request and heap survive verbatim; the next
state and the request flag are installed in ordinary address registers. -/
structure Awaiting (p : BitProgram) (c : p.Config) (next : Fin p.states) (m : Memory K) : Prop where
  heap : HeapRep p (contents c) m
  bufferLength : m.index bufferLenReg=c.bufferRev.length
  stateCode : m.index stateReg=next.val
  askFlag : m.index askReg=1

theorem ask_complete_frame {p : BitProgram} {c : p.Config} (q : Fin p.states) {m : Memory K} {P : K → Prop}
    (h : Rep p c m) (safe : Good P m) :
    ∃ (t : Memory K), Eval (Good P) (actionBlock p (.ask q)) m 2 t ∧ Awaiting p c q t ∧ t.data=m.data ∧ StableHeaders m t ∧ StableEven m t := by
  let u := m.putIndex stateReg q.val
  let t := u.putIndex askReg 1
  have a := eval_constI m safe stateReg q.val
  have b := eval_constI u (show Good P u from a.safe_end) askReg 1
  refine ⟨t,.seq a b,?_,rfl,fun i hi _ => (Memory.putIndex_ne _ (by unfold askReg; omega : i ≠ askReg) _).trans (Memory.putIndex_ne _ (by unfold stateReg; omega : i ≠ stateReg) _),fun i hi _ => (Memory.putIndex_ne _ (by unfold askReg; omega : i ≠ askReg) _).trans (Memory.putIndex_ne _ (by unfold stateReg; omega : i ≠ stateReg) _)⟩
  exact ⟨(h.heap.putHeader (i:=stateReg) (by decide) (by decide) _).putHeader (by decide) (by decide) _,
    by simpa [t,u,stateReg,askReg,bufferLenReg] using h.bufferLength,
    by simp [t,u,stateReg,askReg],by simp [t]⟩

theorem ask_framed {p : BitProgram} {c : p.Config} (q : Fin p.states) {m : Memory K} {P : K → Prop}
    (h : Rep p c m) (safe : Good P m) :
    ∃ (t : Memory K), Eval (Good P) (actionBlock p (.ask q)) m 2 t ∧ Awaiting p c q t ∧ t.data=m.data ∧ StableHeaders m t := by
  obtain ⟨t,e,r,d,f,_⟩ := ask_complete_frame q h safe
  exact ⟨t,e,r,d,f⟩

theorem ask_correct {p : BitProgram} {c : p.Config} (q : Fin p.states) {m : Memory K} {P : K → Prop}
    (h : Rep p c m) (safe : Good P m) :
    ∃ (t : Memory K), Eval (Good P) (actionBlock p (.ask q)) m 2 t ∧ Awaiting p c q t ∧ t.data=m.data := by
  obtain ⟨t,e,r,d,_⟩ := ask_framed q h safe
  exact ⟨t,e,r,d⟩

end BitRAM
end LinearProgramming
end Optimization
end OAI
