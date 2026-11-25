import OAI.Optimization.LinearProgramming.Compression.SmallProxyCachePack
import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheLayout

/-! A query repeatedly reads the same cache. The staging arrays must avoid the
row, cached magnitudes, scale, grid, and the address array of symbolic flags. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM RAM.Callable MinorProxyCache

structure SmallCacheWorkspace (m : Memory ℚ) (L : Buffers) (n : ℕ) : Prop where
  rowHigh : 128 ≤ m.index 67
  scalarHigh : 128 ≤ m.index 87
  addressHigh : 128 ≤ m.index 88
  row : m.index 67+n < m.index 87 ∨ m.index 87+2*n+5 ≤ m.index 67
  grid : L.gridBase+n ≤ m.index 87 ∨ m.index 87+2*n+5 ≤ L.gridBase
  magnitude : L.magBase+n ≤ m.index 87 ∨ m.index 87+2*n+5 ≤ L.magBase
  scale : L.scalePtr < m.index 87 ∨ m.index 87+2*n+5 ≤ L.scalePtr
  flag : m.index 88 < L.flagBase ∨ L.flagBase+n ≤ m.index 88

theorem SmallCachePackFrame.stableCache {m t : Memory ℚ} {L : Buffers} {n fuel prec : ℕ} {mag : ℕ → ℚ}
    (fr : SmallCachePackFrame n m t) (cache : StableCache m L n fuel prec mag)
    (w : SmallCacheWorkspace m L n) : StableCache t L n fuel prec mag := by
  have idx (i : ℕ) (lo : 60 ≤ i) (hi : i < 128) : t.index i=m.index i :=
    fr.addresses i (by omega) (by omega) (by omega) (by omega) (by omega) (by have := w.addressHigh; omega)
  have mh : 128 ≤ L.magBase := (Nat.le_max_left ..).trans cache.separated.magHigh
  have gh : 128 ≤ L.gridBase := (Nat.le_max_left ..).trans cache.separated.gridHigh
  have sh : 128 ≤ L.scalePtr := (Nat.le_max_left ..).trans cache.separated.scaleHigh
  refine ⟨cache.header.transfer (fun i lo hi => idx i (by omega) (by omega)),cache.separated,?_,
    cache.positive,?_,?_,(idx 61 (by decide) (by decide)).trans cache.any,
    (idx 62 (by decide) (by decide)).trans cache.zero,?_⟩
  · intro i hi
    have sep := w.magnitude
    exact (fr.scalars _ (by omega) (by omega) (by omega)).trans (cache.magnitude i hi)
  · intro i hi
    have sep := w.grid
    exact (fr.scalars _ (by omega) (by omega) (by omega)).trans (cache.numerator i hi)
  · intro i hi
    have fh := cache.separated.flagHigh
    have sep := w.flag
    exact (fr.addresses _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (cache.symbolic i hi)
  · exact (fr.scalars _ (by omega) (by omega) w.scale).trans cache.scale

/-- The native capacity and caller-owned query arena stay in place between calls. -/
theorem SmallCachePackFrame.workspace {m t : Memory ℚ} {L : Buffers} {n : ℕ}
    (fr : SmallCachePackFrame n m t) (w : SmallCacheWorkspace m L n) : SmallCacheWorkspace t L n := by
  have idx (i : ℕ) (lo : 60 ≤ i) (hi : i < 128) : t.index i=m.index i :=
    fr.addresses i (by omega) (by omega) (by omega) (by omega) (by omega) (by have := w.addressHigh; omega)
  have h67 := idx 67 (by decide) (by decide)
  have h87 := idx 87 (by decide) (by decide)
  have h88 := idx 88 (by decide) (by decide)
  exact ⟨h67 ▸ w.rowHigh,h87 ▸ w.scalarHigh,h88 ▸ w.addressHigh,h67 ▸ h87 ▸ w.row,
    h87 ▸ w.grid,h87 ▸ w.magnitude,h87 ▸ w.scale,h88 ▸ w.flag⟩

/-- The same integer pair tape supplies both the small sign comparator and the
constant-offset evaluator in a query with symbolic magnitudes. -/
theorem smallCacheRawTapes_fromStable {P : ℚ → Prop} {L : Buffers} {n fuel prec C : ℕ}
    (m : Memory ℚ) (mag : ℕ → ℚ) (c : ℤ) (a : Fin n → ℤ)
    (cache : StableCache m L n fuel prec mag) (w : SmallCacheWorkspace m L n)
    (hm : m.AllData P) (hz : P 0) (capacity : m.index 60=C+1)
    (coeff : ∀ i : Fin n, m.data (m.index 67+i)=(a i:ℚ)) (rhs : m.data (m.index 67+n)=(c:ℚ)) :
    let grid : Fin n → ℤ := fun i => (logProxyNumerator fuel prec (mag i)).getD 0
    ∃ t, Block.Eval (Memory.AllData P) smallCacheRawBlock m (21*n+57) t ∧
      RawTapes t (m.index 87) (m.index 88) (C+1) (smallProxyScalarTape (2^(prec+2)) c a grid) [n+1] ∧
      SmallCachePackFrame n m t ∧ StableCache t L n fuel prec mag ∧ SmallCacheWorkspace t L n := by
  let g : Fin n → ℤ := fun i => (logProxyNumerator fuel prec (mag i)).getD 0
  have gh : 128 ≤ L.gridBase := (Nat.le_max_left ..).trans cache.separated.gridHigh
  have scale : m.data (m.index 86)=((2:ℕ)^(prec+2):ℕ) := by
    simp only [cache.header.scalePtr,cache.scale,Nat.cast_pow,Nat.cast_ofNat]
  have num (i : Fin n) : m.data (m.index 81+i)=(g i:ℚ) := by
    rw [cache.header.numerators]
    simpa only [g,numeratorWord,fieldProxyNumerator_rat] using cache.numerator i i.isLt
  obtain ⟨t,ev,raw,fr⟩ := smallCacheRawTapes_spec m n (2^(prec+2)) C c a g hm hz cache.header.size
    scale capacity w.rowHigh (cache.header.numerators ▸ gh) w.scalarHigh w.addressHigh
    w.row (cache.header.numerators ▸ w.grid) coeff rhs num
  exact ⟨t,ev,raw,fr,fr.stableCache cache w,fr.workspace w⟩

end Compression
end LinearProgramming
end Optimization
end OAI
