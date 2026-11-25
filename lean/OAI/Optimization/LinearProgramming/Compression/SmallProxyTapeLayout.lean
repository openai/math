import OAI.Optimization.LinearProgramming.Compression.SmallProxy
import OAI.Optimization.LinearProgramming.Compression.AffineRAMInput

/-! Cell-by-cell description of the numerical input to the proxy sign program. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

/-- The three scratch cells and the interleaved augmented coefficient/grid row. -/
def smallProxyScalarTape {n : ℕ} (D : ℕ) (c : ℤ) (a grid : Fin n → ℤ) : List ℚ :=
  0 :: 0 :: 0 :: affineInputPairs (smallProxyLeft D a) (smallProxyRight c grid)

@[simp] theorem smallProxyScalarTape_length {n : ℕ} (D : ℕ) (c : ℤ) (a grid : Fin n → ℤ) :
    (smallProxyScalarTape D c a grid).length = 2*n+5 := by
  simp only [smallProxyScalarTape, List.length_cons, affineInputPairs_length]
  omega

private theorem tapeScratch {n : ℕ} (D : ℕ) (c : ℤ) (a grid : Fin n → ℤ) (j : ℕ) (hj : j<3) :
    (smallProxyScalarTape D c a grid)[j]?.getD 0=0 := by interval_cases j <;> rfl

private theorem tapeDen {n : ℕ} (D : ℕ) (c : ℤ) (a grid : Fin n → ℤ) :
    (smallProxyScalarTape D c a grid)[3]?.getD 0=(D:ℚ) := by
  change (affineInputPairs (smallProxyLeft D a) (smallProxyRight c grid))[2*0]?.getD 0 = _
  rw [affineInputPairs_even]
  change affineInputEntry (smallProxyLeft D a) ((0 : Fin (n+1)) : ℕ) = _
  rw [affineInputEntry_fin]
  rfl

private theorem tapeConst {n : ℕ} (D : ℕ) (c : ℤ) (a grid : Fin n → ℤ) :
    (smallProxyScalarTape D c a grid)[4]?.getD 0=(c:ℚ) := by
  change (affineInputPairs (smallProxyLeft D a) (smallProxyRight c grid))[2*0+1]?.getD 0 = _
  rw [affineInputPairs_odd]
  change affineInputEntry (smallProxyRight c grid) ((0 : Fin (n+1)) : ℕ) = _
  rw [affineInputEntry_fin]
  rfl

private theorem tapeCoeff {n : ℕ} (D : ℕ) (c : ℤ) (a grid : Fin n → ℤ) (i : Fin n) :
    (smallProxyScalarTape D c a grid)[5+2*(i:ℕ)]?.getD 0=(a i:ℚ) := by
  rw [show 5+2*(i:ℕ) = 2*((i:ℕ)+1)+3 by omega]
  change (affineInputPairs (smallProxyLeft D a) (smallProxyRight c grid))[2*((i:ℕ)+1)]?.getD 0 = _
  rw [affineInputPairs_even]
  change affineInputEntry (smallProxyLeft D a) (i.succ : ℕ) = _
  rw [affineInputEntry_fin]
  rfl

private theorem tapeGrid {n : ℕ} (D : ℕ) (c : ℤ) (a grid : Fin n → ℤ) (i : Fin n) :
    (smallProxyScalarTape D c a grid)[6+2*(i:ℕ)]?.getD 0=(grid i:ℚ) := by
  rw [show 6+2*(i:ℕ) = (2*((i:ℕ)+1)+1)+3 by omega]
  change (affineInputPairs (smallProxyLeft D a) (smallProxyRight c grid))[2*((i:ℕ)+1)+1]?.getD 0 = _
  rw [affineInputPairs_odd]
  change affineInputEntry (smallProxyRight c grid) (i.succ : ℕ) = _
  rw [affineInputEntry_fin]
  rfl

/-- Exact agreement of the materialized cells with the evaluator's native list
encoding, including both augmented constant cells and the empty-vector case. -/
theorem smallProxyScalarTape_of_cells {n : ℕ} (D : ℕ) (c : ℤ) (a grid : Fin n → ℤ)
    (data : ℕ → ℚ) (o : ℕ) (hzero : ∀ j<3, data (o+j)=0)
    (hD : data (o+3)=(D:ℚ)) (hc : data (o+4)=(c:ℚ))
    (ha : ∀ i : Fin n, data (o+5+2*(i:ℕ))=(a i:ℚ))
    (hg : ∀ i : Fin n, data (o+6+2*(i:ℕ))=(grid i:ℚ)) :
    ∀ j<(smallProxyScalarTape D c a grid).length,
      data (o+j)=(smallProxyScalarTape D c a grid)[j]?.getD 0 := by
  intro j hj
  by_cases hz : j<3
  · exact (hzero j hz).trans (tapeScratch D c a grid j hz).symm
  by_cases h3 : j=3
  · subst j; exact hD.trans (tapeDen D c a grid).symm
  by_cases h4 : j=4
  · subst j; exact hc.trans (tapeConst D c a grid).symm
  rw [smallProxyScalarTape_length] at hj
  let i : Fin n := ⟨(j-5)/2, by omega⟩
  have hi : (i : ℕ)=(j-5)/2 := rfl
  rcases (show j=5+2*(i:ℕ) ∨ j=6+2*(i:ℕ) by omega) with h | h
  · rw [h, tapeCoeff, ← Nat.add_assoc]
    exact ha i
  · rw [h, tapeGrid, ← Nat.add_assoc]
    exact hg i

end Compression
end LinearProgramming
end Optimization
end OAI
