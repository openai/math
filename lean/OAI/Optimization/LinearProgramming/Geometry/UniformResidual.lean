import OAI.Optimization.LinearProgramming.Geometry.UniformCopy
import OAI.Optimization.LinearProgramming.Geometry.UniformTable
import Mathlib.Data.Matrix.Mul

/-! Compute the rational residual projector I−P by a uniform table pass. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace GramCopy

open RAM Matrix
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The row and column addresses of the callback determine the diagonal
indicator. The Gram matrix is read from register 40 and its stride from 41. -/
def residualCell : Block :=
  .seq (cell false) (.seq (ifAddressEq 30 32 (.op (.const 7 1)) (.op (.const 7 0)))
    (.op (.sub 6 7 6)))

theorem residualCell_spec (P : K → Prop) (m : Memory K)
    (hm : m.AllData P) (h0 : P 0) (h1 : P 1)
    (hval : P ((if m.index 30 = m.index 32 then 1 else 0) - m.data (sourceAddress false m))) :
    ∃ k ≤ readCost false m + 5, ∃ t, Block.Eval (Memory.AllData P) residualCell m k t ∧
      t.data 6 = (if m.index 30 = m.index 32 then 1 else 0) - m.data (sourceAddress false m) ∧
      (∀ p, p ≠ 6 → p ≠ 7 → t.data p = m.data p) ∧ KeepsAddresses m t := by
  obtain ⟨s, hs, hd, hf⟩ := cell_spec false P m hm
  have h30 := hf 30 (by decide) (by decide) (by decide)
  have h32 := hf 32 (by decide) (by decide) (by decide)
  have h6 : s.data 6 = m.data (sourceAddress false m) := by simp [hd]
  let bit : K := if m.index 30 = m.index 32 then 1 else 0
  let u := s.putData 7 bit
  have pre : Block.Eval (Memory.AllData P)
      (if s.index 30 = s.index 32 then .op (.const 7 1) else .op (.const 7 0)) s 1 u := by
    rw [h30, h32]
    by_cases hij : m.index 30 = m.index 32
    · simp only [hij, ite_true, u, bit]
      simpa using Block.Eval.op_const s 7 1 hs.safe_end (by simpa using (show s.AllData P from hs.safe_end).putData 7 h1)
    · simp only [hij, ite_false, u, bit]
      simpa using Block.Eval.op_const s 7 0 hs.safe_end (by simpa using (show s.AllData P from hs.safe_end).putData 7 h0)
  obtain ⟨b, hb, hbRun⟩ := eval_ifAddressEq 30 32 _ _ s u 1 pre
  have hu6 : u.data 6 = m.data (sourceAddress false m) := by simpa [u, Memory.putData] using h6
  have hu7 : u.data 7 = bit := by simp [u, Memory.putData]
  let t := u.putData 6 (u.data 7 - u.data 6)
  have hfinal : Block.Eval (Memory.AllData P) (.op (.sub 6 7 6)) u 1 t := by
    apply Block.Eval.op_sub _ _ _ _ hbRun.safe_end
    apply hbRun.safe_end.putData
    rwa [hu7, hu6]
  refine ⟨_, by omega, t, hs.seq (hbRun.seq hfinal), ?_, ?_, hf⟩
  · simp [t, Memory.putData, hu7, hu6, bit]
  · intro p h6' h7'
    simp [t, u, Memory.putData, h6', h7', hd]

/-- Every completed output cell equals the appropriate entry of I−P. The copy is
disjoint from the source, so all matrix reads and protected scalar arrays survive. -/
theorem residual_callback (P : K → Prop) (care keep : ℕ → Prop) (start : Memory K)
    (n out : ℕ) (A : Matrix (Fin n) (Fin n) K) (stride : start.index 41 = n)
    (hA : ∀ i j : Fin n, start.data (start.index 40+i.val*n+j.val) = A i j)
    (hs : ∀ i j : Fin n, let a := start.index 40+i.val*n+j.val
      care a ∧ (a < out ∨ out+n*n ≤ a))
    (h0 : P 0) (h1 : P 1) (hval : ∀ i j : Fin n, P ((1-A) i j))
    (h6 : ¬care 6) (h7 : ¬care 7) (keepScratch : ∀ p, keep p → p ≠ 38 ∧ p ≠ 39 ∧ p ≠ 42)
    (h40 : keep 40) (h41 : keep 41) :
    TableCallbackSpec residualCell P care keep start n n out (1-A) (n*(4*n+5) + 4*n + 11) := by
  intro i j m hm hi hj hp hd
  have hbase := hp _ (Or.inr h40)
  have hwidth := (hp _ (Or.inr h41)).trans stride
  have hsource : sourceAddress false m = start.index 40+i.val*n+j.val := by
    simp [sourceAddress, rowRegister, colRegister, hbase, hwidth, hi, hj]
  have hv : (if m.index 30 = m.index 32 then (1:K) else 0) - m.data (sourceAddress false m) =
      (1-A) i j := by
    rw [hi,hj,hsource,hd _ (hs i j).1 (hs i j).2,hA]
    simp [Matrix.sub_apply, Matrix.one_apply, Fin.ext_iff]
  obtain ⟨k,hk,t,hr,he,hdata,haddr⟩ := residualCell_spec P m hm h0 h1 (hv ▸ hval i j)
  refine ⟨t,k,?_,hr,he.trans hv,?_,?_⟩
  · have h := readCost_le false m n (hi ▸ i.isLt.le) (hj ▸ j.isLt.le) hwidth.le
    omega
  · intro p h; exact hdata p (fun hn => h6 (hn ▸ h)) (fun hn => h7 (hn ▸ h))
  · intro p h
    rcases h with h | h
    · unfold TableControl at h; rcases h with rfl | rfl | rfl | rfl | rfl <;> exact haddr _ (by decide) (by decide) (by decide)
    · obtain ⟨h38,h39,h42⟩ := keepScratch p h
      exact haddr _ h38 h39 h42

end GramCopy
end Geometry
end LinearProgramming
end Optimization
end OAI
