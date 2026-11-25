import OAI.Optimization.LinearProgramming.Compression.SymbolicResidentLayout
import OAI.Optimization.LinearProgramming.Compression.SmallProxyCachePack

/-! The cached numerical input determines the symbolic flags and affine operands. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM RAM.Callable FieldTransfer

theorem symbolicCache_positive {n fuel prec : ℕ} {m : Memory ℚ} {L : MinorProxyCache.Buffers}
    {mag : ℕ → ℚ} (cache : MinorProxyCache.StableCache m L n fuel prec mag) (i : Fin n) : 0 < mag i :=
  cache.positive i i.isLt

theorem symbolicCache_scale {n fuel prec : ℕ} {m : Memory ℚ} {L : MinorProxyCache.Buffers}
    {mag : ℕ → ℚ} (cache : MinorProxyCache.StableCache m L n fuel prec mag) :
    m.data (m.index 86) = ((2^(prec+2) : ℕ):ℚ) := by
  rw [cache.header.scalePtr,cache.scale]
  norm_cast

theorem symbolicCache_grid {n fuel prec : ℕ} {m : Memory ℚ} {L : MinorProxyCache.Buffers}
    {mag : ℕ → ℚ} (cache : MinorProxyCache.StableCache m L n fuel prec mag) (i : Fin n) :
    m.data (m.index 81+i)=((logProxyNumerator fuel prec (mag i)).getD 0 : ℤ) := by
  rw [cache.header.numerators,cache.numerator i i.isLt,MinorProxyCache.numeratorWord,fieldProxyNumerator_rat]

theorem symbolicCache_nonempty {n fuel prec : ℕ} {m : Memory ℚ} {L : MinorProxyCache.Buffers}
    {mag : ℕ → ℚ} (cache : MinorProxyCache.StableCache m L n fuel prec mag) (flag : m.index 61=1) :
    proxyLargeIndices fuel prec (fun i : Fin n => mag i) ≠ [] := by
  intro hn
  have no := (proxyLargeIndices_empty_iff fuel prec (fun i : Fin n => mag i)).mp hn
  have all (i : ℕ) (hi : i < n) : (fieldProxyNumerator fuel prec (mag i)).isSome=true := by
    rw [fieldProxyNumerator_rat]
    have ne := no ⟨i,hi⟩
    cases eq : logProxyNumerator fuel prec (mag i) with
    | none => exact False.elim (ne eq)
    | some => rfl
  have noneLeft := (MinorProxyCache.anySymbolic_zero_iff (fun i => fieldProxyNumerator fuel prec (mag i)) n).mpr all
  have anyFlag := cache.any
  omega

theorem symbolicScan_after_offset {m s : Memory ℚ} {L : MinorProxyCache.Buffers}
    (n fuel prec : ℕ) (mag : ℕ → ℚ) (a : ℕ → ℤ) (offset : ℤ)
    (cache : MinorProxyCache.StableCache m L n fuel prec mag) (space : SymbolicQueryLayout m n fuel)
    (row : ∀ j < n, m.data (m.index 67+j)=(a j:ℚ)) (fr : SmallCachePackFrame n m s) :
    ProxyPacking.Inputs (symbolicScanLayout m n) (s.putData 45 (offset:ℚ))
      (fun j => (logProxyNumerator fuel prec (mag j)).isNone) mag a offset (2^(prec+2)) := by
  have dim := space.dimHigh
  have ah (i : ℕ) (lo : 60 ≤ i) (hi : i < 128) : s.index i=m.index i :=
    fr.addresses i (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have magHigh : 128 ≤ m.index 80 := space.scan.magHigh
  have rowHigh : 128 ≤ m.index 67 := space.scan.rowHigh
  have flagsHigh : 128 ≤ m.index 82 := space.scan.flagsHigh
  have scaleHigh : 128 ≤ m.index 86 := by
    rw [cache.header.scalePtr]
    exact (le_max_left ..).trans cache.separated.scaleHigh
  have keepData (i : ℕ) (high : 128 ≤ i) (out : i < m.index 87 ∨ m.index 87+2*n+5 ≤ i) :
      (s.putData 45 (offset:ℚ)).data i=m.data i :=
    (Memory.putData_ne _ (by omega) _).trans (fr.scalars i (by omega) (by omega) out)
  refine ⟨(ah 62 (by decide) (by decide)).trans cache.zero,ah 67 (by decide) (by decide),
    ah 68 (by decide) (by decide),ah 69 (by decide) (by decide),ah 80 (by decide) (by decide),
    ah 82 (by decide) (by decide),(ah 83 (by decide) (by decide)).trans cache.header.size,?_,
    Memory.putData_same ..,?_,?_,?_⟩
  · rw [Memory.putData_index,ah 86 (by decide) (by decide),
      keepData _ scaleHigh space.scaleTape,symbolicCache_scale cache]
  · intro j hj
    change (s.putData 45 (offset:ℚ)).data (m.index 80+j)=mag j
    have sep := space.magTape
    rw [keepData _ (by omega) (by change j < n at hj; omega),cache.header.magnitudes]
    exact cache.magnitude j hj
  · intro j hj
    change (s.putData 45 (offset:ℚ)).data (m.index 67+j)=(a j:ℚ)
    have sep := space.rowTape
    exact (keepData _ (by omega) (by change j < n at hj; omega)).trans (row j hj)
  · intro j hj
    change s.index (m.index 82+j)=(logProxyNumerator fuel prec (mag j)).isNone.toNat
    have sep := space.flagDim
    rw [fr.addresses _ (by omega) (by omega) (by omega) (by omega) (by omega)
      (by change j < n at hj; omega),cache.header.flags,cache.symbolic j hj,fieldProxyNumerator_rat]
    cases logProxyNumerator fuel prec (mag j) <;> rfl

end Compression
end LinearProgramming
end Optimization
end OAI
