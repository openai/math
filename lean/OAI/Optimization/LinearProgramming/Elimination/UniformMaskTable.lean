import OAI.Optimization.LinearProgramming.Elimination.UniformTabulate
import OAI.Optimization.LinearProgramming.Elimination.UniformMaskCell

/-! One fixed nested loop materializes the entire padded Gram matrix. The matrix and flags
are disjoint from the output, and only the low scratch cells and the output interval change. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM Compression Matrix

private def maskScratch : Finset ℕ := {8,9,10}

def uniformMaskTable : Block := .forRowsCols 4 0 5 0 uniformMaskCell

def maskTableCost (n : ℕ) : ℕ := n*(n*(90*(n+1)^2+3)+5)+2

private theorem cell_offset_lt {n : ℕ} (i j : Fin n) : i.val*n+j.val < n*n := by
  simpa [finProdFinEquiv,Nat.add_comm,Nat.mul_comm] using (finProdFinEquiv (i,j)).isLt

theorem uniformMaskTable_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (n : ℕ) (S : Finset (Fin n)) (hN : m.index 0=n)
    (hzero : m.index 14=0) (hG : 7 ≤ m.index 17) (hf : 7 ≤ m.index 18) (ho : 7 ≤ m.index 1)
    (hgo : m.index 17+n*n ≤ m.index 1) (hfo : m.index 18+n ≤ m.index 1)
    (hm : ∀ p, P (m.data p)) (h0 : P 0) (h1 : P 1)
    (hflag : ∀ k : Fin n, m.data (m.index 18+k.val) = flag S k) :
    ∃ t k, k ≤ maskTableCost n ∧ Block.Eval (fun s => ∀p,P (s.data p)) uniformMaskTable m k t ∧
      uniformMatrix n (m.index 1) t = maskGram (uniformMatrix n (m.index 17) m) (flag S) ∧
      (∀ a, 7 ≤ a → (a < m.index 1 ∨ m.index 1+n*n ≤ a) → t.data a = m.data a) ∧
      (∀ p, p ∉ ({4,5,8,9,10} : Finset ℕ) → t.index p = m.index p) := by
  let T := maskGram (uniformMatrix n (m.index 17) m) (flag S)
  let out := m.index 1
  have callback (i j : Fin n) (s : Memory K) (h : FillState P maskScratch out (i.val*n+j.val) T m s)
      (hi : s.index 4=i.val) (hj : s.index 5=j.val) :
      ∃ k t, k ≤ 90*(n+1)^2 ∧ Block.Eval (fun w => ∀p,P (w.data p)) uniformMaskCell s k t ∧
      t.data (out+i.val*n+j.val)=T i j ∧
      (∀ p,7≤p → p≠out+i.val*n+j.val → t.data p=s.data p) ∧
      (∀ p ∉ maskScratch, t.index p = s.index p) := by
    have f0 := h.index 0 (by decide)
    have f1 := h.index 1 (by decide)
    have f14 := h.index 14 (by decide)
    have f17 := h.index 17 (by decide)
    have f18 := h.index 18 (by decide)
    have hstored (k : Fin n) : s.data (s.index 18+k.val) = flag S k := by
      rw [f18,h.other _ (by omega) (Or.inl (by dsimp [out]; omega)),hflag]
    have gmat : uniformMatrix n (s.index 17) s = uniformMatrix n (m.index 17) m := by
      rw [f17]
      ext i j
      have hlt := cell_offset_lt i j
      exact h.other _ (by omega) (Or.inl (by dsimp [out]; omega))
    obtain ⟨k,t,hk,he,write,other,idx⟩ := uniformMaskCell_spec P s n S i j (f0.trans hN) hi hj
      (f14.trans hzero) (f17 ▸ hG) (f18 ▸ hf) h.valid h0 h1 hstored
    rw [f1,gmat] at write
    rw [f1] at other
    refine ⟨k,t,hk,he,write,other,?_⟩
    intro p hp
    have hnot : p ≠ 8 ∧ p ≠ 9 ∧ p ≠ 10 := by simpa [maskScratch] using hp
    exact idx p hnot.1 hnot.2.1 hnot.2.2
  obtain ⟨t,k,hk,he,h⟩ := uniform_tabulate P uniformMaskCell maskScratch 0 0 out (90*(n+1)^2) T m
    hm ho hN hN (by decide) (by decide) (by decide) (by decide) callback
  refine ⟨t,k,hk,he,?_,h.other,h.index⟩
  ext i j
  exact h.done_ i j (cell_offset_lt i j)

end Elimination
end LinearProgramming
end Optimization
end OAI
