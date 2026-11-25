import OAI.Optimization.LinearProgramming.Compression.BinarySerialization
import OAI.Optimization.LinearProgramming.Compression.PowerTapeEncoder
import Mathlib.Data.Nat.Bitwise

/-! Compute the canonical binary length of an already constructed integer scalar.
The RAM uses repeated doubling, starting at one, and a scalar comparison. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
open RAM

/-- Data register 0 holds a nonnegative integer. The length of its canonical
binary representation is returned in address register 0. Data registers 40
and 41 hold respectively the running power of two and the strict threshold. -/
def scalarWidthBlock : Block :=
  .seq (.straight [.const 40 1, .add 41 0 40, .addrConst 0 0])
    (.loop (.scalarLT 40 41) (.straight [.add 40 40 40, .incr 0 0]))

private structure WidthState (m : Memory ℚ) (P : ℚ → Prop) (a j : ℕ)
    (s : Memory ℚ) : Prop where
  safe : s.AllData P
  power : s.data 40 = 2^j
  threshold : s.data 41 = (a : ℚ)+1
  count : s.index 0 = j
  dataFrame : ∀ i, i ≠ 40 → i ≠ 41 → s.data i = m.data i
  indexFrame : ∀ i, i ≠ 0 → s.index i = m.index i

theorem scalarWidthBlock_spec (m : Memory ℚ) (a w : ℕ) {P : ℚ → Prop}
    (hm : m.AllData P) (ha : m.data 0 = (a : ℚ)) (hw : a < 2^w)
    (hP : ∀ v : ℕ, v ≤ 2^w → P (v : ℚ)) :
    ∃ s, Block.Eval (Memory.AllData P) scalarWidthBlock m (4*a.size+4) s ∧
      s.index 0 = a.size ∧ (∀ i, i ≠ 40 → i ≠ 41 → s.data i=m.data i) ∧
      (∀ i, i ≠ 0 → s.index i=m.index i) := by
  let m₁ := m.putData 40 1
  let m₂ := m₁.putData 41 (m₁.data 0 + m₁.data 40)
  let m₃ := m₂.putIndex 0 0
  have h₁ : m₁.AllData P := hm.putData _ (by simpa using hP 1 (Nat.one_le_pow _ _ (by decide)))
  have hth : m₁.data 0 + m₁.data 40 = (a:ℚ)+1 := by simp [m₁,ha]
  have h₂ : m₂.AllData P := h₁.putData _ (by rw [hth]; exact_mod_cast hP (a+1) (by omega))
  have h₃ : m₃.AllData P := h₂
  have init := (Block.Eval.op_const m 40 1 hm h₁).seq
    ((Block.Eval.op_add m₁ 41 0 40 h₁ h₂).seq
      ((Block.Eval.op_addrConst m₂ 0 0 h₂ h₃).seq (.skip h₃)))
  have start : WidthState m P a 0 m₃ := by
    refine ⟨h₃,by simp [m₃,m₂,m₁],by simpa [m₃,m₂] using hth,by simp [m₃],?_,?_⟩
    · intro i h40 h41; simp [m₃,m₂,m₁,h40,h41]
    · intro i hi; simp [m₃,m₂,m₁,hi]
  have loop := Block.Eval.loop_invariant_exact (safe:=Memory.AllData P)
    (c:=Cond.scalarLT 40 41) (body:=Block.straight [.add 40 40 40, .incr 0 0])
    (WidthState m P a) m₃ a.size 2 start (by
      intro j hj s hs
      have hd : (2:ℚ)^j ≤ a := by exact_mod_cast Nat.lt_size.mp hj
      have hpj : j+1 ≤ w := (Nat.succ_le_of_lt hj).trans (Nat.size_le.mpr hw)
      have hd' : s.data 40 + s.data 40 = ((2:ℕ)^(j+1) : ℚ) := by
        rw [hs.power,pow_succ]; norm_num; ring
      let s₁ := s.putData 40 (s.data 40+s.data 40)
      let s₂ := s₁.putIndex 0 (s₁.index 0+1)
      have hS : s₁.AllData P := hs.safe.putData _ (by
        rw [hd']; exact_mod_cast hP (2^(j+1)) (Nat.pow_le_pow_right (by decide) hpj))
      have hT : s₂.AllData P := hS
      refine ⟨by simp [Cond.test,hs.power,hs.threshold]; linarith, s₂,
        (Block.Eval.op_add s 40 40 40 hs.safe hS).seq
          ((Block.Eval.op_incr s₁ 0 0 hS hT).seq (.skip hT)), ?_⟩
      refine ⟨hT,by simpa [s₂,s₁] using hd',by simpa [s₂,s₁] using hs.threshold,
        by simp [s₂,s₁,hs.count],?_,?_⟩
      · intro i h40 h41; simpa [s₂,s₁,h40] using hs.dataFrame i h40 h41
      · intro i hi; simpa [s₂,s₁,hi] using hs.indexFrame i hi) (by
      intro s hs
      have hp : ((a:ℚ)+1) ≤ 2^a.size := by exact_mod_cast Nat.lt_size_self a
      exact ⟨by simp [Cond.test,hs.power,hs.threshold,not_lt.mpr hp], hs.safe⟩)
  obtain ⟨s,he,hs⟩ := loop
  refine ⟨s,?_,hs.count,hs.dataFrame,hs.indexFrame⟩
  rw [show 4*a.size+4 = (1+(1+(1+0))) + (a.size*(2+2)+1) by omega]
  exact init.seq he

/-- The canonical length is right also at zero. Within that length, a digit
read by its little-endian index is exactly the corresponding canonical token. -/
theorem reverse_bits_eq_testBit (a : ℕ) :
    a.bits.reverse = List.ofFn (fun j : Fin a.size => a.testBit (a.size-1-j.val)) := by
  have hl : a.bits.length = a.size := Nat.size_eq_bits_len a
  apply List.ext_getElem (by simp [hl])
  intro i h₁ h₂
  have hi : i < a.size := by simpa [hl] using h₁
  have hj : a.size-1-i < a.bits.length := by omega
  simp only [List.getElem_reverse,List.getElem_ofFn,Nat.testBit_eq_inth,List.getI_eq_getElem a.bits hj]
  congr 1
  omega

end Compression
end LinearProgramming
end Optimization
end OAI
