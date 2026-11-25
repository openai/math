import OAI.Optimization.LinearProgramming.RAM.StrideCopy
import Mathlib.Tactic

/-! Transfer a contiguous proxy column into one parity of a staged output buffer. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

private def pointerAtOffset (dst src : ℕ) : ℕ → Block
  | 0 => .op (.addrCopy dst src)
  | k+1 => .seq (pointerAtOffset dst src k) (.op (.incr dst dst))

private theorem pointerAtOffset_spec (dst src k : ℕ) (m : Memory ℚ) {P : ℚ → Prop}
    (hm : m.AllData P) : ∃ z, Block.Eval (Memory.AllData P) (pointerAtOffset dst src k) m (k+1) z ∧
      z.data = m.data ∧ z.index dst = m.index src + k ∧ ∀ i, i ≠ dst → z.index i = m.index i := by
  induction k with
  | zero =>
    refine ⟨m.putIndex dst (m.index src), Block.Eval.op_addrCopy _ _ _ hm hm, rfl, by simp, ?_⟩
    exact fun i hi => Memory.putIndex_ne _ hi _
  | succ k ih =>
    obtain ⟨z, he, hd, hv, hf⟩ := ih
    refine ⟨z.putIndex dst (z.index dst+1), he.seq (Block.Eval.op_incr _ _ _ he.safe_end he.safe_end),
      hd, by simp [hv, Nat.add_assoc], ?_⟩
    exact fun i hi => (Memory.putIndex_ne _ hi _).trans (hf i hi)

/-- Gather consecutive source scalars into alternating output cells. Address
register 3 gives the common output base and address 0 the number of entries. -/
def scatterProxyLane (src sp dp offset : ℕ) : Block :=
  .seq (.op (.addrCopy sp src)) (.seq (pointerAtOffset dp 3 offset)
    (StrideCopy.block false sp dp 8 0 0 1 2))

theorem scatterProxyLane_spec {P : ℚ → Prop} (m : Memory ℚ) (src sp dp offset n : ℕ)
    (hm : m.AllData P) (hn : m.index 0 = n) (hsp : sp ≠ 3) (hregs : [sp,dp,8,0].Nodup)
    (hsrc : 0 < m.index src) (hout : 0 < m.index 3)
    (hsep : ∀ i < n, ∀ j < n, m.index 3+offset+2*i ≠ m.index src+j) :
    ∃ z, Block.Eval (Memory.AllData P) (scatterProxyLane src sp dp offset) m (8*n+offset+4) z ∧
      (∀ i < n, z.data (m.index 3+offset+2*i) = m.data (m.index src+i)) ∧
      (∀ j, j ≠ 0 → (∀ i < n, j ≠ m.index 3+offset+2*i) → z.data j = m.data j) ∧
      z.index sp = m.index src+n ∧
      ∀ j, j ≠ sp → j ≠ dp → j ≠ 8 → z.index j = m.index j := by
  have hsd : sp ≠ dp := by rintro rfl; simp at hregs
  have h0s : 0 ≠ sp := by rintro rfl; simp at hregs
  have h0d : 0 ≠ dp := by rintro rfl; simp at hregs
  let v := m.putIndex sp (m.index src)
  have cp : Block.Eval (Memory.AllData P) (.op (.addrCopy sp src)) m 1 v :=
    Block.Eval.op_addrCopy _ _ _ hm hm
  obtain ⟨u, off, data, dst, frame⟩ := pointerAtOffset_spec dp 3 offset v cp.safe_end
  have xs : u.index sp = m.index src := by simpa [v] using frame sp hsd
  have ds : u.index dp = m.index 3 + offset := by simpa [v,hsp.symm] using dst
  have un : u.index 0 = n := by simpa [v,h0s,hn] using frame 0 h0d
  have clean : u.data=m.data := data
  obtain ⟨z, he, written, held, endSrc, _, _, index⟩ :=
    StrideCopy.block_correct P u false sp dp 8 0 0 1 2 n off.safe_end un hregs
      (by decide) (by simp)
      (fun j hj => by simp only [StrideCopy.address_forward,xs,Nat.one_mul]; omega)
      (fun j hj => by simp only [StrideCopy.address_forward,ds]; omega)
      (fun i j hij hj => by
        simpa only [StrideCopy.address_forward,ds,xs,Nat.one_mul] using hsep i (hij.trans hj) j hj)
  refine ⟨z, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show 8*n+offset+4 = 1+((offset+1)+(n*(1+2+5)+2)) by omega]
    exact cp.seq (off.seq he)
  · simpa only [StrideCopy.address_forward,ds,xs,Nat.one_mul,clean] using written
  · simpa only [StrideCopy.address_forward,ds,clean] using held
  · simpa only [StrideCopy.address_forward,xs,Nat.one_mul] using endSrc
  · intro j hs hd h8
    exact (index j hs hd h8).trans ((frame j hd).trans (Memory.putIndex_ne _ hs _))

end Compression
end LinearProgramming
end Optimization
end OAI
