import OAI.Optimization.LinearProgramming.RAM.Code

/-! Fixed tag-to-continuation tables for composing RAM procedures. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Callable

/-- A caller can retain the tag as an address or interpret it as a rational scalar
constant, such as the sign represented by a comparison result. -/
inductive TagSink where
  | index (dst : ℕ)
  | indexMapped (dst : ℕ) (value : ℕ → ℕ)
  | scalar (dst : ℕ) (value : ℕ → ℚ)

namespace TagSink

def instr : TagSink → ℕ → Instr
  | .index d, tag => .addrConst d tag
  | .indexMapped d value, tag => .addrConst d (value tag)
  | .scalar d value, tag => .const d (value tag)

def store {K : Type*} [RatCast K] : TagSink → ℕ → Memory K → Memory K
  | .index d, tag, m => m.putIndex d tag
  | .indexMapped d value, tag, m => m.putIndex d (value tag)
  | .scalar d value, tag, m => m.putData d (value tag : K)

def dst : TagSink → ℕ
  | .index d | .indexMapped d _ | .scalar d _ => d

variable {K : Type*} [RatCast K]

@[simp] theorem store_index_data (d tag : ℕ) (m : Memory K) :
    ((TagSink.index d).store tag m).data = m.data := rfl

@[simp] theorem store_index_self (d tag : ℕ) (m : Memory K) :
    ((TagSink.index d).store tag m).index d = tag := Function.update_self ..

@[simp] theorem store_indexMapped_data (d tag : ℕ) (value : ℕ → ℕ) (m : Memory K) :
    ((TagSink.indexMapped d value).store tag m).data = m.data := rfl

@[simp] theorem store_indexMapped_self (d tag : ℕ) (value : ℕ → ℕ) (m : Memory K) :
    ((TagSink.indexMapped d value).store tag m).index d = value tag := Function.update_self ..

@[simp] theorem store_scalar_index (d tag : ℕ) (value : ℕ → ℚ) (m : Memory K) :
    ((TagSink.scalar d value).store tag m).index = m.index := rfl

@[simp] theorem store_scalar_self (d tag : ℕ) (value : ℕ → ℚ) (m : Memory K) :
    ((TagSink.scalar d value).store tag m).data d = (value tag : K) := Function.update_self ..

theorem store_data_ne (sink : TagSink) (tag : ℕ) (m : Memory K) {j : ℕ} (hj : j ≠ sink.dst) :
    (sink.store tag m).data j = m.data j := by
  cases sink with
  | index | indexMapped => rfl
  | scalar => exact Function.update_of_ne hj ..

theorem store_index_ne (sink : TagSink) (tag : ℕ) (m : Memory K) {j : ℕ} (hj : j ≠ sink.dst) :
    (sink.store tag m).index j = m.index j := by
  cases sink with
  | index | indexMapped => exact Function.update_of_ne hj ..
  | scalar => rfl

end TagSink

/-- Each row contains exactly the tag store and a jump to the shared caller continuation. -/
def tagTable (sink : TagSink) (count endPC : ℕ) : Program :=
  (List.range count).flatMap fun tag => [sink.instr tag, .jump endPC]

theorem tagTable_succ (sink : TagSink) (count endPC : ℕ) :
    tagTable sink (count+1) endPC = tagTable sink count endPC ++ [sink.instr count,.jump endPC] := by
  simp [tagTable,List.range_succ]

@[simp] theorem length_tagTable (sink : TagSink) (count endPC : ℕ) :
    (tagTable sink count endPC).length = 2*count := by
  induction count with
  | zero => simp [tagTable]
  | succ n ih => simp only [tagTable_succ,List.length_append,ih,List.length_cons,List.length_nil]; omega

/-- The offset obtained by doubling a valid tag addresses precisely its two instructions. -/
theorem tagTable_codeAt (sink : TagSink) (count endPC base tag : ℕ) {target : Program}
    (code : CodeAt target base (tagTable sink count endPC)) (htag : tag<count) :
    CodeAt target (base+2*tag) [sink.instr tag,.jump endPC] := by
  induction count with
  | zero => omega
  | succ n ih =>
    rw [tagTable_succ] at code
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ htag) with lt | eq
    · exact ih code.left lt
    · subst tag; simpa only [length_tagTable] using code.right

/-- A callee can return directly to the corresponding table row. The store and jump cost
two actual primitive steps, including every intermediate state in the safety invariant. -/
theorem tagTable_exec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (sink : TagSink) (count endPC base tag : ℕ) (m : Memory K)
    {target : Program} {safe : Memory K → Prop} (code : CodeAt target base (tagTable sink count endPC))
    (htag : tag<count) (before : safe m) (after : safe (sink.store tag m)) :
    Execution target (fun s => safe s.memory) (m.atPC (base+2*tag)) 2 ((sink.store tag m).atPC endPC) := by
  have cell := tagTable_codeAt sink count endPC base tag code htag
  have here := cell.head
  have jump : target[base+2*tag+1]? = some (.jump endPC) :=
    (CodeAt.right (a := [sink.instr tag]) cell).head
  have storeStep : step target (m.atPC (base+2*tag)) =
      some ((sink.store tag m).atPC (base+2*tag+1)) := by
    change (match (none : Option ℕ), target[base+2*tag]? with
      | none,some i => execInstr i (m.atPC (base+2*tag))
      | _,_ => none) = _
    rw [here]
    cases sink <;> rfl
  have jumpStep : step target ((sink.store tag m).atPC (base+2*tag+1)) =
      some ((sink.store tag m).atPC endPC) := by
    simp [step,Memory.atPC,jump,execInstr]
  exact .next before storeStep (.one after jumpStep after)

end Callable
end RAM
end LinearProgramming
end Optimization
end OAI
