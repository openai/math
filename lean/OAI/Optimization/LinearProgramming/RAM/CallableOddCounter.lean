import OAI.Optimization.LinearProgramming.RAM.CallableOddBase

/-! Odd address words encode a virtual address `v` as `2*v+1`. Increment needs
two native increments. Three saturating decrements followed by an increment
reduce a positive virtual address and leave virtual zero encoded as one. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable
namespace Odd

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem overwrite (m : Memory K) (d u v : ℕ) :
    (m.putIndex d u).putIndex d v = m.putIndex d v := by
  simp [Memory.putIndex, Function.update_idem]

private theorem incr_again (P : K → Prop) (m : Memory K) (hm : m.AllData P) (d x : ℕ) :
    Block.Eval (Memory.AllData P) (.op (.incr d d)) (m.putIndex d x) 1
      (m.putIndex d (x+1)) := by
  simpa only [Memory.putIndex_same, overwrite] using
    Block.Eval.op_incr (safe := Memory.AllData P) (m.putIndex d x) d d hm hm

private theorem decr_again (P : K → Prop) (m : Memory K) (hm : m.AllData P) (d x : ℕ) :
    Block.Eval (Memory.AllData P) (.op (.decr d d)) (m.putIndex d x) 1
      (m.putIndex d (x-1)) := by
  simpa only [Memory.putIndex_same, overwrite] using
    Block.Eval.op_decr (safe := Memory.AllData P) (m.putIndex d x) d d hm hm

private theorem incr_pair (P : K → Prop) (m : Memory K) (hm : m.AllData P) (d a : ℕ) :
    Block.Eval (Memory.AllData P) (Block.straight [.incr d a, .incr d d]) m 2
      (m.putIndex d (m.index a+1+1)) :=
  (Block.Eval.op_incr (safe := Memory.AllData P) m d a hm hm).seq
    ((incr_again P m hm d _).seq (.skip hm))

private theorem decr_triple_incr (P : K → Prop) (m : Memory K) (hm : m.AllData P) (d a : ℕ) :
    Block.Eval (Memory.AllData P) (Block.straight [.decr d a, .decr d d, .decr d d, .incr d d])
      m 4 (m.putIndex d (m.index a-1-1-1+1)) :=
  (Block.Eval.op_decr (safe := Memory.AllData P) m d a hm hm).seq
    ((decr_again P m hm d _).seq ((decr_again P m hm d _).seq
      ((incr_again P m hm d _).seq (.skip hm))))

theorem incr_eval (P : K → Prop) (callee m : Memory K) (hc : callee.AllData P) (hm : m.AllData P)
    (d a : ℕ) :
    Block.Eval (Memory.AllData P) (instr (.incr d a)) (memory callee m) 2
      (memory callee (m.putIndex d (m.index a+1))) := by
  have run := incr_pair P _ (allData callee m hc hm) (slot d) (slot a)
  rw [index_slot, show slot (m.index a)+1+1 = slot (m.index a+1) by unfold slot; omega,
    putIndex] at run
  exact run

theorem decr_eval (P : K → Prop) (callee m : Memory K) (hc : callee.AllData P) (hm : m.AllData P)
    (d a : ℕ) :
    Block.Eval (Memory.AllData P) (instr (.decr d a)) (memory callee m) 4
      (memory callee (m.putIndex d (m.index a-1))) := by
  have run := decr_triple_incr P _ (allData callee m hc hm) (slot d) (slot a)
  rw [index_slot, show slot (m.index a)-1-1-1+1 = slot (m.index a-1) by unfold slot; omega,
    putIndex] at run
  exact run

end Odd
end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
