import OAI.Optimization.LinearProgramming.Compression.SmallProxyPackLane
import OAI.Optimization.LinearProgramming.Compression.SmallProxyPackHeader
import OAI.Optimization.LinearProgramming.Compression.SmallProxyTapeLayout

/-! # Staging a materialized affine query for the small-logarithm branch

Row inputs are consecutive integer coefficients followed by their constant.
The grid array contains stored integer proxy numerators, with zero for a
symbolic proxy when this computation supplies the small part of a mixed query. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Address registers 0–3 supply dimension, row base, grid base, and output base.
Scalar 8 supplies D. The remaining work uses scalar 0 and address registers 4–8. -/
def smallProxyPackBlock : Block :=
  .seq (scatterProxyLane 1 4 6 5)
    (.seq (scatterProxyLane 2 5 7 6) patchSmallProxyHeader)

/-- A fixed program stages all required cells of the native dot-product argument,
with separate input/output regions in either order. Its clock includes both
strided scans, every array access, pointer motion and the final header writes.
All original scalar-size invariants containing zero survive unchanged. -/
theorem smallProxyPackBlock_spec {P : ℚ → Prop} (m : Memory ℚ) (n D : ℕ) (c : ℤ)
    (a grid : Fin n → ℤ) (hm : m.AllData P) (h0 : P 0)
    (hn : m.index 0=n) (hD : m.data 8=(D:ℚ))
    (hR : 0 < m.index 1) (hG : 0 < m.index 2) (hO : 8 < m.index 3)
    (hRsep : m.index 1+n < m.index 3 ∨ m.index 3+2*n+5 ≤ m.index 1)
    (hGsep : m.index 2+n ≤ m.index 3 ∨ m.index 3+2*n+5 ≤ m.index 2)
    (ha : ∀ i : Fin n, m.data (m.index 1+i) = (a i : ℚ))
    (hc : m.data (m.index 1+n)=(c:ℚ)) (hg : ∀ i : Fin n, m.data (m.index 2+i)=(grid i:ℚ)) :
    ∃ z, Block.Eval (Memory.AllData P) smallProxyPackBlock m (16*n+43) z ∧
      (∀ j<(smallProxyScalarTape D c a grid).length,
        z.data (m.index 3+j)=(smallProxyScalarTape D c a grid)[j]?.getD 0) ∧
      (∀ j, j ≠ 0 → (j < m.index 3 ∨ m.index 3+2*n+5 ≤ j) → z.data j=m.data j) ∧
      (∀ j, j<4 ∨ 8<j → z.index j=m.index j) := by
  obtain ⟨u, eu, wa, fa, rowEnd, iu⟩ := scatterProxyLane_spec m 1 4 6 5 n hm hn
    (by decide) (by decide) hR (by omega) (by intro i hi j hj; omega)
  have u0 := iu 0 (by decide) (by decide) (by decide)
  have u2 := iu 2 (by decide) (by decide) (by decide)
  have u3 := iu 3 (by decide) (by decide) (by decide)
  obtain ⟨v, ev, wg, fg, _, iv⟩ := scatterProxyLane_spec u 2 5 7 6 n eu.safe_end (u0.trans hn)
    (by decide) (by decide) (u2 ▸ hG) (by omega) (by intro i hi j hj; rw [u2,u3]; omega)
  have v3 := (iv 3 (by decide) (by decide) (by decide)).trans u3
  have v4 := (iv 4 (by decide) (by decide) (by decide)).trans rowEnd
  have before (j : ℕ) (hne : j ≠ 0) (hw : j<m.index 3 ∨ m.index 3+2*n+5≤j) :
      v.data j = m.data j := by
    refine (fg j hne (fun i hi => ?_)).trans (fa j hne (fun i hi => ?_)) <;> omega
  have coeff (i : Fin n) : v.data (m.index 3+5+2*(i:ℕ)) = (a i : ℚ) := by
    refine (fg _ (by omega) (fun j _ => ?_)).trans ((wa i i.isLt).trans (ha i))
    omega
  have proxies (i : Fin n) : v.data (m.index 3+6+2*(i:ℕ)) = (grid i : ℚ) := by
    have h := wg i i.isLt
    rw [u2,u3] at h
    refine h.trans ((fa _ (by omega) (fun j hj => ?_)).trans (hg i))
    have hi := i.isLt
    omega
  obtain ⟨z, ez, zeros, denom, constant, fh, ih⟩ := patchSmallProxyHeader_spec v ev.safe_end h0
    (by omega) (by omega) (by omega)
  rw [v3] at zeros denom constant
  rw [v4] at constant
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · rw [show 16*n+43 = (8*n+5+4)+((8*n+6+4)+24) by omega]
    exact eu.seq (ev.seq ez)
  · apply smallProxyScalarTape_of_cells D c a grid z.data (m.index 3) zeros
    · exact denom.trans ((before 8 (by decide) (Or.inl hO)).trans hD)
    · exact constant.trans ((before _ (by omega) (by omega)).trans hc)
    · intro i
      exact (fh _ (by omega) (by omega)).trans (coeff i)
    · intro i
      exact (fh _ (by omega) (by omega)).trans (proxies i)
  · intro j hne hw
    exact (fh _ hne (by omega)).trans (before j hne hw)
  · intro j hj
    exact (ih j (by omega) (by omega) (by omega)).trans <|
      (iv j (by omega) (by omega) (by omega)).trans (iu j (by omega) (by omega) (by omega))

end Compression
end LinearProgramming
end Optimization
end OAI
