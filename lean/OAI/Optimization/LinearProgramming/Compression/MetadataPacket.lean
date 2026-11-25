import OAI.Optimization.LinearProgramming.BitRAM.PacketLayout
import OAI.Optimization.LinearProgramming.RAM.Array

/-! The concrete scalar packet writer used to initialize the binary compression service. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
namespace Metadata

variable {K : Type*}

open RAM OracleSpec BitRAM

/-- Both a physical cursor and an independently readable output length are advanced
by every bit. All other writes lie inside the actual output interval. -/
structure Effect [Zero K] [One K] (s t : Memory K) (bits : Word) : Prop where
  cursor : t.index 65 = s.index 65 + bits.length
  length : t.index 49 = s.index 49 + bits.length
  packet : ScalarPacket t (s.index 65) bits
  outside : ∀ i, i < s.index 65 ∨ s.index 65 + bits.length ≤ i → t.data i = s.data i
  frame : ∀ i, i ≠ 49 → i ≠ 65 → i ≠ 69 → i ≠ 71 → t.index i = s.index i

namespace Effect
variable {K : Type*} [Zero K] [One K]

theorem empty {s t : Memory K} (hd : t.data=s.data) (hc : t.index 65=s.index 65)
    (hl : t.index 49=s.index 49)
    (hf : ∀ i, i≠49 → i≠65 → i≠69 → i≠71 → t.index i=s.index i) : Effect s t [] :=
  ⟨by simpa using hc,by simpa using hl,ScalarPacket.nil _ _, fun i _ => congrFun hd i,hf⟩

theorem refl (s : Memory K) : Effect s s [] := empty rfl rfl rfl (fun _ _ _ _ _ => rfl)

theorem append {s m t : Memory K} {a b : Word} (f : Effect s m a) (g : Effect m t b) :
    Effect s t (a ++ b) := by
  refine ⟨by rw [g.cursor,f.cursor,List.length_append,Nat.add_assoc],
    by rw [g.length,f.length,List.length_append,Nat.add_assoc],?_,?_,
    fun i h49 h65 h69 h71 => (g.frame i h49 h65 h69 h71).trans (f.frame i h49 h65 h69 h71)⟩
  · intro i hi
    by_cases left : i < a.length
    · rw [List.getElem_append_left left]
      exact (g.outside _ (Or.inl (by rw [f.cursor]; omega))).trans (f.packet i left)
    · have hle : a.length ≤ i := Nat.le_of_not_gt left
      have rem : i-a.length < b.length := by simp only [List.length_append] at hi; omega
      rw [List.getElem_append_right hle]
      simpa only [f.cursor,show s.index 65 + a.length + (i-a.length) = s.index 65+i by omega] using g.packet _ rem
  · intro i hi
    rw [List.length_append] at hi
    rw [g.outside i (by rw [f.cursor]; omega), f.outside i (by omega)]

end Effect

/-- The fixed constants and bit cells required by the writer. -/
structure Ready [Zero K] [One K] (s : Memory K) : Prop where
  zero : s.data 0 = 0
  one : s.data 2 = 1
  indexZero : s.index 67 = 0
  indexOne : s.index 75 = 1
  base : 3 ≤ s.index 65

theorem Ready.after [Zero K] [One K] {s t : Memory K} {bits : Word} (h : Ready s) (f : Effect s t bits) : Ready t := by
  have hc := h.base
  exact ⟨(f.outside 0 (Or.inl (by omega))).trans h.zero, (f.outside 2 (Or.inl (by omega))).trans h.one,
    (f.frame 67 (by decide) (by decide) (by decide) (by decide)).trans h.indexZero,
    (f.frame 75 (by decide) (by decide) (by decide) (by decide)).trans h.indexOne,
    by rw [f.cursor]; omega⟩

/-- One ordinary store, one cursor increment and one length increment. -/
def emit (bit : Bool) : Block := .seq (.op (.store 65 (if bit then 2 else 0)))
  (.seq (.op (.incr 65 65)) (.op (.incr 49 49)))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

theorem emit_correct (s : Memory K) (b : Bool) (hs : s.AllData P) (h : Ready s) :
    ∃ t, Block.Eval (Memory.AllData P) (emit b) s 3 t ∧ Effect s t [b] ∧
      ∀ i, i≠65 → i≠49 → t.index i=s.index i := by
  let src := if b then 2 else 0
  let a := s.putData (s.index 65) (s.data src)
  let v := a.putIndex 65 (a.index 65+1)
  let t := v.putIndex 49 (v.index 49+1)
  have store : Block.Eval (Memory.AllData P) (.op (.store 65 src)) s 1 a :=
    Block.Eval.op_store _ _ _ hs (hs.putData _ (hs _))
  have inc : Block.Eval (Memory.AllData P) (.op (.incr 65 65)) a 1 v :=
    Block.Eval.op_incr _ _ _ store.safe_end store.safe_end
  have len : Block.Eval (Memory.AllData P) (.op (.incr 49 49)) v 1 t :=
    Block.Eval.op_incr _ _ _ inc.safe_end inc.safe_end
  have frame (i : Nat) (h65 : i≠65) (h49 : i≠49) : t.index i=s.index i := by simp [t,v,a,h65,h49]
  have val : s.data src = bitScalar b := by cases b <;> simp [src,bitScalar,h.zero,h.one]
  refine ⟨t,store.seq (inc.seq len),?_,frame⟩
  constructor
  · simp [t,v,a]
  · simp [t,v,a]
  · intro i hi
    have e : i=0 := by simp only [List.length_singleton] at hi; omega
    subst i
    simpa [t,v,a] using val
  · intro i hi
    have he : i ≠ s.index 65 := by simp only [List.length_singleton] at hi; omega
    simp [t,v,a,he]
  · intro i h49 h65 _ _; exact frame i h65 h49

end Metadata
end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
