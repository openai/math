import OAI.Optimization.LinearProgramming.Compression.UniformBirdCellData
import OAI.Optimization.LinearProgramming.Compression.UniformBirdTerm

/-! A dimension-independent RAM program for one cell of the Bird determinant iteration. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM
open scoped BigOperators

structure BirdScanInv {K : Type} [CommRing K] (P : K → Prop)
    (m : Memory K) (n : ℕ) (i j : Fin n) (c : ℕ) (s : Memory K) : Prop where
  valid : ∀ a, P (s.data a)
  counter : s.index 6 = c
  memory : ∀ a, 7 ≤ a → s.data a = m.data a
  frame : birdCellIndexFrame s m
  diag : s.data 1 = ∑ k ∈ birdCut i c, uniformMatrix n (m.index 2) m k k
  dot : s.data 2 = ∑ k ∈ birdCut i c,
    uniformMatrix n (m.index 2) m i k * uniformMatrix n (m.index 1) m k j

theorem birdCell_frame_small {K : Type*} {s m : Memory K} (h : birdCellIndexFrame s m)
    (p : ℕ) (hp : p < 6) : s.index p = m.index p := h p (by omega) (by omega) (by omega) (by omega)

private theorem scanAdvance {K : Type} [CommRing K] {P : K → Prop}
    {m : Memory K} {n : ℕ} {i j : Fin n} {c : ℕ} (s : Memory K)
    (hgood : ∀ a, P (s.data a)) (hcounter : s.index 6 = c)
    (hmem : ∀ a, 7 ≤ a → s.data a = m.data a) (hframe : birdCellIndexFrame s m)
    (hd : s.data 1 = ∑ k ∈ birdCut i (c+1), uniformMatrix n (m.index 2) m k k)
    (hp : s.data 2 = ∑ k ∈ birdCut i (c+1),
      uniformMatrix n (m.index 2) m i k * uniformMatrix n (m.index 1) m k j) :
    BirdScanInv P m n i j (c+1) (s.putIndex 6 (s.index 6+1)) := by
  refine ⟨hgood, by simp [Memory.putIndex, hcounter], hmem, ?_, hd, hp⟩
  intro p h6 h8 h9 h10
  simp only [Memory.putIndex, Function.update_of_ne h6]
  exact hframe p h6 h8 h9 h10

def birdScanBranch : Block := .branch (.addrLT 4 6) uniformBirdTerm .skip

theorem birdScanCallback {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (P : K → Prop) (m : Memory K) (n : ℕ) (i j : Fin n) (hn : m.index 0 = n)
    (hi : m.index 4 = i.val) (hj : m.index 5 = j.val)
    (hA : 7 ≤ m.index 1) (hF : 7 ≤ m.index 2)
    (hreg : ∀ r : BirdRegister n, P (r.read (uniformMatrix n (m.index 1) m) (uniformMatrix n (m.index 2) m)))
    (c : ℕ) (hc : c < n) (s : Memory K) (ih : BirdScanInv P m n i j c s) :
    ∃ t cost, cost ≤ 100*(n+1)^2 + 2 ∧
      Block.Eval (fun z => ∀ a, P (z.data a)) birdScanBranch s cost t ∧
      BirdScanInv P m n i j (c+1) (t.putIndex 6 (t.index 6+1)) := by
  let A := uniformMatrix n (m.index 1) m
  let F := uniformMatrix n (m.index 2) m
  let k : Fin n := ⟨c,hc⟩
  have sn := (birdCell_frame_small ih.frame 0 (by decide)).trans hn
  have si := (birdCell_frame_small ih.frame 4 (by decide)).trans hi
  have sj := (birdCell_frame_small ih.frame 5 (by decide)).trans hj
  have sa := birdCell_frame_small ih.frame 1 (by decide)
  have sf := birdCell_frame_small ih.frame 2 (by decide)
  by_cases he : i.val < c
  · have fkk : s.data (s.index 2+s.index 6*s.index 0+s.index 6) = F k k := by
      rw [sf, ih.counter, sn]; exact ih.memory _ (by omega)
    have fik : s.data (s.index 2+s.index 4*s.index 0+s.index 6) = F i k := by
      rw [sf, si, sn, ih.counter]; exact ih.memory _ (by omega)
    have akj : s.data (s.index 1+s.index 6*s.index 0+s.index 5) = A k j := by
      rw [sa, ih.counter, sn, sj]; exact ih.memory _ (by omega)
    have hd : s.data 1 + F k k = ∑ a ∈ birdCut i (c+1), F a a := by
      rw [ih.diag, birdCut_succ_yes i hc he, Finset.sum_insert (notMem_birdCut i hc), add_comm]
    have hp : s.data 2 + F i k * A k j = ∑ a ∈ birdCut i (c+1), F i a * A a j := by
      rw [ih.dot, birdCut_succ_yes i hc he, Finset.sum_insert (notMem_birdCut i hc), add_comm]
    obtain ⟨cost, t, hcost, hrun, hd', hp', hdata, hidx⟩ := uniformBirdTerm_spec s P ih.valid
      (si ▸ sn ▸ i.isLt) (sj ▸ sn ▸ j.isLt) (ih.counter ▸ sn ▸ hc) (sa ▸ hA) (sf ▸ hF)
      (by rw [fkk, hd]; exact hreg (.diagonal _)) (by rw [fik, akj]; exact hreg (.product i k j))
      (by rw [fik, akj, hp]; exact hreg (.dotPartial _ i j))
    rw [sn] at hcost
    refine ⟨t, 1+cost+1, by omega, .branchTrue (by simpa [Cond.test, si, ih.counter]) hrun, ?_⟩
    apply scanAdvance t hrun.safe_end
    · exact (hidx 6 (by decide) (by decide) (by decide)).trans ih.counter
    · intro a ha; exact (hdata a ha).trans (ih.memory a ha)
    · intro p h6 h8 h9 h10; exact (hidx p h8 h9 h10).trans (ih.frame p h6 h8 h9 h10)
    · simpa only [hd', fkk] using hd
    · simpa only [hp', fik, akj] using hp
  · refine ⟨s, 1, by omega, .branchFalse (by simp [Cond.test, si, ih.counter, he]) (.skip ih.valid), ?_⟩
    exact scanAdvance s ih.valid ih.counter ih.memory ih.frame
      (by rw [birdCut_succ_no i he]; exact ih.diag) (by rw [birdCut_succ_no i he]; exact ih.dot)

end Compression
end LinearProgramming
end Optimization
end OAI
