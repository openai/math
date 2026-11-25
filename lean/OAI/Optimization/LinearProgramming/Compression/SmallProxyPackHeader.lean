import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.RAM.ArrayFill
import Mathlib.Tactic

/-! Write the three scratch zeros, grid denominator, and affine constant of the
small-logarithm dot-product input into a caller-selected buffer. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Address 3 points to the buffer. Address 4 already points to the affine
constant after scanning the coefficient row. Scalar 8 is the common positive
denominator of the grid proxies. -/
def patchSmallProxyHeader : Block :=
  .seq (.op (.const 0 0)) <| .seq (.op (.addrConst 5 3)) <| .seq (fillBlock 0 3 6 8 5) <|
    .seq (.op (.store 6 8)) <| .seq (.op (.incr 6 6)) <| .seq (.op (.load 0 4)) (.op (.store 6 0))

theorem patchSmallProxyHeader_spec {P : ℚ → Prop} (m : Memory ℚ) (hm : m.AllData P) (h0 : P 0)
    (hO : 8 < m.index 3) (hC : 0 < m.index 4)
    (hsep : m.index 4 < m.index 3 ∨ m.index 3+5 ≤ m.index 4) :
    ∃ z, Block.Eval (Memory.AllData P) patchSmallProxyHeader m 24 z ∧
      (∀ j < 3, z.data (m.index 3+j) = 0) ∧ z.data (m.index 3+3)=m.data 8 ∧
      z.data (m.index 3+4)=m.data (m.index 4) ∧
      (∀ j, j ≠ 0 → (j < m.index 3 ∨ m.index 3+5 ≤ j) → z.data j=m.data j) ∧
      (∀ j, j ≠ 5 → j ≠ 6 → j ≠ 8 → z.index j=m.index j) := by
  let u := m.putData 0 0
  let v := u.putIndex 5 3
  have ez : Block.Eval (Memory.AllData P) (.op (.const 0 0)) m 1 u :=
    Block.Eval.op_const m 0 0 hm (hm.putData 0 h0)
  have es : Block.Eval (Memory.AllData P) (.op (.addrConst 5 3)) u 1 v :=
    Block.Eval.op_addrConst u 5 3 ez.safe_end ez.safe_end
  obtain ⟨t, fill, cells, framed, _, ptr, indices⟩ :=
    fillBlock_correct P v 0 3 6 8 5 3 (by decide) (by decide) (by decide) (by simp [v])
      (by simpa [v,u] using (show 0 < m.index 3 by omega)) es.safe_end
  have t6 : t.index 6=m.index 3+3 := by simpa [v,u] using ptr
  have t4 : t.index 4=m.index 4 := by simpa [v,u] using indices 4 (by decide) (by decide)
  have zeroes (j : ℕ) (hj : j<3) : t.data (m.index 3+j) = 0 := by
    simpa [v,u] using cells j hj
  have old (j : ℕ) (hn : j ≠ 0) (hw : j < m.index 3 ∨ m.index 3+3 ≤ j) :
      t.data j=m.data j := by
    simpa [v,u,hn] using framed j (by simpa [v,u] using hw)
  let tD := t.putData (t.index 6) (t.data 8)
  let tP := tD.putIndex 6 (tD.index 6+1)
  let tC := tP.putData 0 (tP.data (tP.index 4))
  let z := tC.putData (tC.index 6) (tC.data 0)
  have tsafe : t.AllData P := fill.safe_end
  have eD : Block.Eval (Memory.AllData P) (.op (.store 6 8)) t 1 tD :=
    Block.Eval.op_store _ _ _ tsafe (tsafe.putData _ (tsafe 8))
  have eP : Block.Eval (Memory.AllData P) (.op (.incr 6 6)) tD 1 tP :=
    Block.Eval.op_incr _ _ _ eD.safe_end eD.safe_end
  have eC : Block.Eval (Memory.AllData P) (.op (.load 0 4)) tP 1 tC :=
    Block.Eval.op_load _ _ _ eP.safe_end (eP.safe_end.putData _ (eP.safe_end _))
  have eZ : Block.Eval (Memory.AllData P) (.op (.store 6 0)) tC 1 z :=
    Block.Eval.op_store _ _ _ eC.safe_end (eC.safe_end.putData _ (eC.safe_end _))
  have c6 : tC.index 6=m.index 3+4 := by simp [tC,tP,tD,t6,Nat.add_assoc]
  have p4 : tP.index 4=m.index 4 := by simp [tP,tD,t4]
  have unchanged (j : ℕ) (hj : j ≠ 0) (h3 : j ≠ m.index 3+3) (h4 : j ≠ m.index 3+4) :
      z.data j = t.data j :=
    (Memory.putData_ne tC (c6 ▸ h4) _).trans <| (Memory.putData_ne tP hj _).trans
      (Memory.putData_ne t (t6 ▸ h3) _)
  refine ⟨z, ez.seq (es.seq (fill.seq (eD.seq (eP.seq (eC.seq eZ))))), ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact (unchanged _ (by omega) (by omega) (by omega)).trans (zeroes j hj)
  · calc
      z.data (m.index 3+3) = tC.data (m.index 3+3) := Memory.putData_ne _ (by omega) _
      _ = tP.data (m.index 3+3) := Memory.putData_ne _ (by omega) _
      _ = tD.data (t.index 6) := by rw [t6]; rfl
      _ = t.data 8 := Memory.putData_same ..
      _ = m.data 8 := old 8 (by decide) (Or.inl hO)
  · rw [← c6]
    calc
      z.data (tC.index 6) = tC.data 0 := Memory.putData_same ..
      _ = tP.data (tP.index 4) := Memory.putData_same ..
      _ = tD.data (m.index 4) := by rw [p4]; rfl
      _ = t.data (m.index 4) := Memory.putData_ne _ (by omega) _
      _ = m.data (m.index 4) := old _ (by omega) (by omega)
  · intro j hj hw
    exact (unchanged _ hj (by omega) (by omega)).trans (old _ hj (by omega))
  · intro j h5 h6 h8
    exact (Memory.putIndex_ne tD h6 _).trans <| (indices j h8 h6).trans
      (Memory.putIndex_ne u h5 _)

end Compression
end LinearProgramming
end Optimization
end OAI
