import OAI.Optimization.LinearProgramming.RAM.Loops

/-! A fixed register-level decision for each entry of the masked Gram matrix. The arithmetic
uses only copies and the constants zero and one; the other cases do not multiply large entries. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM

private def diagonalEntry : Block :=
  .branch (.addrLT 4 5) (.op (.const 3 0))
    (.branch (.addrLT 5 4) (.op (.const 3 0)) (.op (.const 3 1)))

private theorem choiceWrite {K : Type*} {P : K → Prop} {m : Memory K}
    (h : ∀ i, P (m.data i)) {x : K} (hx : P x) : ∀ i, P ((m.putData 3 x).data i) := by
  intro i; by_cases hi : i=3 <;> simp [Memory.putData,hi,h,hx]

private theorem diagonalEntry_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (hm : ∀ i, P (m.data i)) (h0 : P 0) (h1 : P 1) :
    ∃ k, k ≤ 4 ∧ Block.Eval (fun w => ∀ i, P (w.data i)) diagonalEntry m k
      (m.putData 3 (if m.index 4 = m.index 5 then 1 else 0)) := by
  let safe := fun w : Memory K => ∀ i, P (w.data i)
  have z : Block.Eval safe (.op (.const 3 0)) m 1 (m.putData 3 0) := by
    simpa using Block.Eval.op_const (safe := safe) m 3 0 hm (by simpa [safe] using choiceWrite hm h0)
  have o : Block.Eval safe (.op (.const 3 1)) m 1 (m.putData 3 1) := by
    simpa using Block.Eval.op_const (safe := safe) m 3 1 hm (by simpa [safe] using choiceWrite hm h1)
  rcases lt_trichotomy (m.index 4) (m.index 5) with h | h | h
  · rw [ite_eq_right h.ne]
    exact ⟨3,by decide,.branchTrue (by simp [Cond.test,h]) z⟩
  · rw [ite_eq_left h]
    exact ⟨3,by decide,.branchFalse (by simp [Cond.test,h]) (.branchFalse (by simp [Cond.test,h]) o)⟩
  · rw [ite_eq_right h.ne']
    exact ⟨4,by decide,.branchFalse (by simp [Cond.test,h.not_gt]) (.branchTrue (by simp [Cond.test,h]) z)⟩

/-- Scalar registers zero and one contain the two active flags, register two the Gram entry,
register four the scalar zero; the two address counters are four and five. -/
def chooseMaskEntry : Block :=
  .branch (.scalarLT 4 0) (.branch (.scalarLT 4 1) (.op (.copy 3 2)) (.op (.const 3 0))) diagonalEntry

theorem chooseMaskEntry_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (onRow onCol : Prop) [Decidable onRow] [Decidable onCol]
    (hm : ∀ i, P (m.data i)) (h0 : P 0) (h1 : P 1) (hz : m.data 4 = 0)
    (hr : m.data 0 = if onRow then 1 else 0) (hc : m.data 1 = if onCol then 1 else 0) :
    let value := if onRow then (if onCol then m.data 2 else 0) else
      (if m.index 4 = m.index 5 then 1 else 0)
    ∃ k, k ≤ 6 ∧ Block.Eval (fun w => ∀ i, P (w.data i)) chooseMaskEntry m k (m.putData 3 value) := by
  let safe := fun w : Memory K => ∀ i, P (w.data i)
  have z : Block.Eval safe (.op (.const 3 0)) m 1 (m.putData 3 0) := by
    simpa using Block.Eval.op_const (safe := safe) m 3 0 hm (by simpa [safe] using choiceWrite hm h0)
  have cp : Block.Eval safe (.op (.copy 3 2)) m 1 (m.putData 3 (m.data 2)) :=
    Block.Eval.op_copy m 3 2 hm (choiceWrite hm (hm 2))
  dsimp only
  by_cases r : onRow
  · rw [ite_eq_left r]
    have htest : (Cond.scalarLT 4 0).test m = true := by simp [Cond.test,hz,hr,r]
    by_cases c : onCol
    · rw [ite_eq_left c]
      exact ⟨5,by decide,.branchTrue htest (.branchTrue (by simp [Cond.test,hz,hc,c]) cp)⟩
    · rw [ite_eq_right c]
      exact ⟨4,by decide,.branchTrue htest (.branchFalse (by simp [Cond.test,hz,hc,c]) z)⟩
  · rw [ite_eq_right r]
    obtain ⟨k,hk,he⟩ := diagonalEntry_spec P m hm h0 h1
    exact ⟨1+k,by omega,.branchFalse (by simp [Cond.test,hz,hr,r]) he⟩

end Elimination
end LinearProgramming
end Optimization
end OAI
