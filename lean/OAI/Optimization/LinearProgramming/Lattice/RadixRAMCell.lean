import OAI.Optimization.LinearProgramming.Lattice.Radix
import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.RAM.ArrayFill

/-! The fixed scalar-RAM instruction sequence for one signed Horner update. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace RadixRAM

open OAI.Optimization.LinearProgramming.RAM

/-- The eight header addresses store p, the number of digits, input base, output base,
row counter, column counter, input cursor, output cursor. Scalar zero holds the radix;
only scalar scratch registers one and two are needed beyond the output buffer. -/
def cell : Block := .straight [.load 1 7, .load 2 6, .mul 1 0 1, .add 1 1 2,
    .store 7 1, .incr 6 6, .incr 7 7]

/-- Seven actual instructions load the prior accumulator and the next signed digit,
write `B * accumulator + digit`, and advance the two independent pointers. -/
theorem cell_correct (P : ℚ → Prop) (m : Memory ℚ) (hs : m.AllData P)
    (hread : 2 < m.index 6) (hprod : P (m.data 0 * m.data (m.index 7)))
    (hval : P (m.data 0 * m.data (m.index 7) + m.data (m.index 6))) :
    ∃ t, Block.Eval (Memory.AllData P) cell m 7 t ∧
      t.data (m.index 7) = m.data 0 * m.data (m.index 7) + m.data (m.index 6) ∧
      (∀ k, k≠1 → k≠2 → k≠m.index 7 → t.data k=m.data k) ∧
      t.index 6=m.index 6+1 ∧ t.index 7=m.index 7+1 ∧
      ∀ k, k≠6 → k≠7 → t.index k=m.index k := by
  let p := m.data 0 * m.data (m.index 7)
  let v := p + m.data (m.index 6)
  let m1 := m.putData 1 (m.data (m.index 7))
  let m2 := m1.putData 2 (m.data (m.index 6))
  let m3 := m2.putData 1 p
  let m4 := m3.putData 1 v
  let m5 := m4.putData (m.index 7) v
  let m6 := m5.putIndex 6 (m.index 6+1)
  let t := m6.putIndex 7 (m.index 7+1)
  have h1 : m1.AllData P := hs.putData _ (hs _)
  have h2 : m2.AllData P := h1.putData _ (hs _)
  have h3 : m3.AllData P := h2.putData _ hprod
  have h4 : m4.AllData P := h3.putData _ hval
  have h5 : m5.AllData P := h4.putData _ hval
  have h6 : m6.AllData P := h5
  have ht : t.AllData P := h5
  have e1 : Block.Eval (Memory.AllData P) (.op (.load 1 7)) m 1 m1 := Block.Eval.op_load _ _ _ hs h1
  have e2 : Block.Eval (Memory.AllData P) (.op (.load 2 6)) m1 1 m2 := by
    have e : m1.data (m1.index 6) = m.data (m.index 6) := by simp [m1, show m.index 6 ≠ 1 by omega]
    simpa only [e] using Block.Eval.op_load m1 2 6 h1 (by simpa only [e] using h2)
  have e3 : Block.Eval (Memory.AllData P) (.op (.mul 1 0 1)) m2 1 m3 := by
    have e : m2.data 0 * m2.data 1 = p := by simp [m2,m1,p]
    simpa only [e] using Block.Eval.op_mul m2 1 0 1 h2 (by simpa only [e] using h3)
  have e4 : Block.Eval (Memory.AllData P) (.op (.add 1 1 2)) m3 1 m4 := by
    have e : m3.data 1 + m3.data 2 = v := by simp [m3,m2,v]
    simpa only [e] using Block.Eval.op_add m3 1 1 2 h3 (by simpa only [e] using h4)
  have e5 : Block.Eval (Memory.AllData P) (.op (.store 7 1)) m4 1 m5 := by
    have e : m4.data 1 = v := by simp [m4]
    have ea : m4.index 7 = m.index 7 := rfl
    simpa only [e,ea] using Block.Eval.op_store m4 7 1 h4 (by simpa only [e,ea] using h5)
  have e6 : Block.Eval (Memory.AllData P) (.op (.incr 6 6)) m5 1 m6 := Block.Eval.op_incr _ _ _ h5 h6
  have e7 : Block.Eval (Memory.AllData P) (.op (.incr 7 7)) m6 1 t := by
    have e : m6.index 7 = m.index 7 := by simp [m6,m5,m4,m3,m2,m1]
    simpa only [e] using Block.Eval.op_incr m6 7 7 h6 (by simpa only [e] using ht)
  refine ⟨t,e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq (e7.seq (.skip ht))))))),?_,?_,?_,?_,?_⟩
  · simp [t,m6,m5,v,p]
  · intro k h1 h2 h7; simp [t,m6,m5,m4,m3,m2,m1,h1,h2,h7]
  · simp [t,m6]
  · simp [t]
  · intro k h6 h7; simp [t,m6,m5,m4,m3,m2,m1,h6,h7]

/-- Appending a signed digit is a single Horner update of the paper's radix expansion. -/
theorem radixVector_append_digit {ι : Type*} (B : ℤ) (zs : List (ι → ℤ)) (z : ι → ℤ) (i : ι) :
    radixVector B (zs ++ [z]) i = B * radixVector B zs i + z i := by
  have h (ds : List ℤ) : radixDigits B (ds ++ [z i]) = B * radixDigits B ds + z i := by
    induction ds with
    | nil => simp [radixDigits]
    | cons a ds ih => simp [radixDigits, ih, pow_succ]; ring
  simpa only [radixVector_apply, List.map_append, List.map_cons, List.map_nil] using h (zs.map (fun v ↦ v i))

end RadixRAM
end Lattice
end LinearProgramming
end Optimization
end OAI
