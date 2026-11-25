import OAI.Optimization.LinearProgramming.Compression.UniformBirdFinish
import OAI.Optimization.LinearProgramming.Compression.UniformBirdScan

/-! A dimension-independent RAM program for one cell of the Bird determinant iteration. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM
open scoped BigOperators

/-- A complete cell program. Its constants and instructions do not depend on `n`. -/
def uniformBirdCell : Block :=
  .seq (.op (.const 1 0)) (.seq (.op (.const 2 0)) (.seq (.forRange 6 0 birdScanBranch) uniformBirdFinish))

theorem uniformBirdCell_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (n : ℕ) (i j : Fin n) (hn : m.index 0 = n)
    (hi : m.index 4 = i.val) (hj : m.index 5 = j.val)
    (hA : 7 ≤ m.index 1) (hF : 7 ≤ m.index 2) (_hW : 7 ≤ m.index 3)
    (hm : ∀ p, P (m.data p))
    (hreg : ∀ r : BirdRegister n, P (r.read (uniformMatrix n (m.index 1) m) (uniformMatrix n (m.index 2) m))) :
    ∃ cost t, cost ≤ 1000*(n+1)^4 ∧ Block.Eval (fun z => ∀ a, P (z.data a)) uniformBirdCell m cost t ∧
      t.data (m.index 3+i.val*n+j.val) = BirdDet.Spec.stepEntry
        (uniformMatrix n (m.index 1) m) (uniformMatrix n (m.index 2) m) i j ∧
      (∀ p, 7 ≤ p → p ≠ m.index 3+i.val*n+j.val → t.data p = m.data p) ∧
      birdCellIndexFrame t m := by
  let A := uniformMatrix n (m.index 1) m
  let F := uniformMatrix n (m.index 2) m
  have hz : P (0:K) := by simpa [BirdRegister.read] using hreg (.diagonal ∅)
  let a := m.putData 1 (0:K)
  let b := a.putData 2 (0:K)
  have ha : ∀ p, P (a.data p) := birdScalarPut hm _ _ hz
  have hb : ∀ p, P (b.data p) := birdScalarPut ha _ _ hz
  have h1 : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.const 1 0)) m 1 a := by
    simpa [a] using Block.Eval.op_const m 1 0 hm (show ∀p, P ((m.putData 1 ((0:ℚ):K)).data p) by simpa using ha)
  have h2 : Block.Eval (fun z => ∀ p, P (z.data p)) (.op (.const 2 0)) a 1 b := by
    simpa [b] using Block.Eval.op_const a 2 0 ha (show ∀p, P ((a.putData 2 ((0:ℚ):K)).data p) by simpa using hb)
  have hinit : BirdScanInv P m n i j 0 (b.putIndex 6 0) := by
    refine ⟨hb, by simp [Memory.putIndex], ?_, ?_, ?_, ?_⟩
    · intro p hp
      simp [b,a,Memory.putData,Memory.putIndex,Function.update_of_ne (by omega : p ≠ 2),
        Function.update_of_ne (by omega : p ≠ 1)]
    · intro p hp _ _ _; simp [b,a,Memory.putData,Memory.putIndex,Function.update_of_ne hp]
    · simp [b,a,Memory.putData,Memory.putIndex]
    · simp [b,a,Memory.putData,Memory.putIndex]
  obtain ⟨s, ks, hks, hs, hstate⟩ := Block.Eval.forRange_invariant (body := birdScanBranch)
    6 0 n (100*(n+1)^2+2) (BirdScanInv P m n i j) b hb hinit
    (fun _ s h => ⟨h.valid, h.counter, (birdCell_frame_small h.frame 0 (by decide)).trans hn⟩)
    (birdScanCallback P m n i j hn hi hj hA hF hreg)
  have dsum : s.data 1 = ∑ k ∈ Finset.Ioi i, F k k := by simpa [F] using hstate.diag
  have psum : s.data 2 = ∑ k ∈ Finset.Ioi i, F i k * A k j := by simpa [F,A] using hstate.dot
  have sb := birdCell_frame_small hstate.frame 1 (by decide)
  have sw := birdCell_frame_small hstate.frame 3 (by decide)
  have sij : s.data (s.index 1+i.val*n+j.val) = A i j := by
    rw [sb]; exact hstate.memory _ (by omega)
  obtain ⟨kf,t,hkf,hf,hres,hmf,hif⟩ := uniformBirdFinish_spec P s n i j
    ((birdCell_frame_small hstate.frame 0 (by decide)).trans hn)
    ((birdCell_frame_small hstate.frame 4 (by decide)).trans hi)
    ((birdCell_frame_small hstate.frame 5 (by decide)).trans hj) hstate.valid hz
    (by rw [dsum]; exact hreg (.negDiagonal (Finset.Ioi i)))
    (by rw [dsum,sij]; exact hreg (.diagonalProduct (Finset.Ioi i) i j))
    (by rw [dsum,sij,psum]; exact hreg (.output (Finset.Ioi i) (Finset.Ioi i) i j))
  refine ⟨1+(1+(ks+kf)), t, ?_, h1.seq (h2.seq (hs.seq hf)), ?_, ?_, ?_⟩
  · nlinarith [Nat.zero_le (n^4), Nat.zero_le (n^3), Nat.zero_le (n^2)]
  · rw [← sw]; exact hres.trans (by rw [dsum,sij,psum]; rfl)
  · intro p hp hend
    exact (hmf p hp (sw ▸ hend)).trans (hstate.memory p hp)
  · intro p h6 h8 h9 h10; exact (hif p h6 h8 h9 h10).trans (hstate.frame p h6 h8 h9 h10)

end Compression
end LinearProgramming
end Optimization
end OAI
