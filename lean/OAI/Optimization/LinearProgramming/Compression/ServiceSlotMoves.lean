import OAI.Optimization.LinearProgramming.RAM.Loops

/-! Fixed sequences of address instructions used by the generator-slot comparator. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable
open RAM

inductive SlotMove where
  | copy (dst src : ℕ)
  | incr (dst src : ℕ)
  | decr (dst src : ℕ)
  | constant (dst value : ℕ)

def SlotMove.instruction : SlotMove → Instr
  | .copy a b => .addrCopy a b
  | .incr a b => .incr a b
  | .decr a b => .decr a b
  | .constant a n => .addrConst a n

def SlotMove.act (m : Memory ℚ) : SlotMove → Memory ℚ
  | .copy a b => m.putIndex a (m.index b)
  | .incr a b => m.putIndex a (m.index b+1)
  | .decr a b => m.putIndex a (m.index b-1)
  | .constant a n => m.putIndex a n

def slotMoves : List SlotMove → Block
  | [] => .skip
  | a::xs => .seq (.op a.instruction) (slotMoves xs)

def afterMoves (m : Memory ℚ) : List SlotMove → Memory ℚ
  | [] => m
  | a::xs => afterMoves (a.act m) xs

@[simp] theorem SlotMove.act_data (m : Memory ℚ) (a : SlotMove) : (a.act m).data=m.data := by
  cases a <;> rfl

@[simp] theorem afterMoves_data (m : Memory ℚ) (xs : List SlotMove) : (afterMoves m xs).data=m.data := by
  induction xs generalizing m with
  | nil => rfl
  | cons a xs ih => simp [afterMoves,ih]

theorem slotMoves_eval (P : ℚ → Prop) (s : Memory ℚ) (xs : List SlotMove) (hs : ∀ j,P (s.data j)) :
    Block.Eval (fun m => ∀ j,P (m.data j)) (slotMoves xs) s xs.length (afterMoves s xs) := by
  induction xs generalizing s with
  | nil => exact .skip hs
  | cons a xs ih =>
    have h : ∀ i, P ((a.act s).data i) := by simpa using hs
    have e : Block.Eval (fun m => ∀ j,P (m.data j)) (.op a.instruction) s 1 (a.act s) := by
      cases a with
      | copy x y => exact Block.Eval.op_addrCopy _ _ _ hs h
      | incr x y => exact Block.Eval.op_incr _ _ _ hs h
      | decr x y => exact Block.Eval.op_decr _ _ _ hs h
      | constant x y => exact Block.Eval.op_addrConst _ _ _ hs h
    simpa [slotMoves,afterMoves,Nat.add_comm] using e.seq (ih (a.act s) h)

/-- Both initial row pointers begin at the first member of each index list, with one
comparison result of equality. The warmup advances the column pointers an extra n. -/
def setupMoves : List SlotMove := [.incr 24 20,.incr 24 24,.copy 25 24,
  .incr 26 21,.incr 26 26,.copy 27 26,.constant 23 1]

def warmMoves : List SlotMove := [.incr 24 24,.incr 25 25,.incr 25 25,
  .incr 26 26,.incr 27 27,.incr 27 27]

def backMoves : List SlotMove := [.decr 24 24,.decr 25 25,.decr 26 26,.decr 27 27]

def headMoves : List SlotMove := [.decr 24 24,.decr 26 26]

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
