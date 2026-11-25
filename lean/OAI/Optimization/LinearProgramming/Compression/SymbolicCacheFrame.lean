import OAI.Optimization.LinearProgramming.Compression.SymbolicQueryLayout
import OAI.Optimization.LinearProgramming.Compression.SmallProxyCacheFrame

/-! Stability of a previously computed log cache through a mixed query. The
allocator reserves disjoint caller pages for the cache, row and temporary power tapes. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM RAM.Callable MinorProxyCache

theorem SymbolicQueryLayout.ofSmall {m : Memory ℚ} {L : Buffers} {n fuel prec : ℕ} {mag : ℕ → ℚ}
    (cache : StableCache m L n fuel prec mag) (w : SmallCacheWorkspace m L n)
    (hs : (symbolicScanLayout m n).Valid)
    (he : (symbolicPairAreas m).Valid (n+1) (symbolicDigitWidth fuel)) : SymbolicQueryLayout m n fuel := by
  refine ⟨hs,he,w.addressHigh,w.row,?_,?_,?_,?_⟩
  · simpa only [cache.header.numerators] using w.grid
  · simpa only [cache.header.magnitudes] using w.magnitude
  · simpa only [cache.header.scalePtr] using w.scale
  · simpa only [cache.header.flags] using w.flag.symm

theorem SymbolicQueryFrame.stableCache {m t : Memory ℚ} {L : Buffers} {n fuel prec : ℕ} {mag : ℕ → ℚ}
    (fr : SymbolicQueryFrame n fuel m t) (cache : StableCache m L n fuel prec mag)
    (space : SymbolicQueryLayout m n fuel) (res : SymbolicCacheReservation m L n fuel) :
    StableCache t L n fuel prec mag := by
  have hh (i) (low : 60 ≤ i) (hi : i < 128) (aux : i < 70 ∨ 75 < i) := fr.header space i low hi aux
  have hmag : 128 ≤ L.magBase := (le_max_left ..).trans cache.separated.magHigh
  have hgrid : 128 ≤ L.gridBase := (le_max_left ..).trans cache.separated.gridHigh
  have hscale : 128 ≤ L.scalePtr := (le_max_left ..).trans cache.separated.scaleHigh
  have hf := space.flagDim
  rw [cache.header.flags] at hf
  refine ⟨cache.header.transfer (fun i a b => hh i (by omega) (by omega) (by omega)),
    cache.separated,?_,cache.positive,?_,?_,(hh 61 (by decide) (by decide) (by decide)).trans cache.any,
    (hh 62 (by decide) (by decide) (by decide)).trans cache.zero,
    (fr.high_data _ hscale res.scale).trans cache.scale⟩
  · intro j hj
    exact (fr.high_data _ (by omega) (res.magnitudes j hj)).trans (cache.magnitude j hj)
  · intro j hj
    exact (fr.high_data _ (by omega) (res.numerators j hj)).trans (cache.numerator j hj)
  · intro j hj
    have high := cache.separated.flagHigh
    exact (fr.index _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (res.flags j hj)).trans (cache.symbolic j hj)

theorem SymbolicQueryFrame.row_data {m t : Memory ℚ} {L : Buffers} {n fuel : ℕ}
    (fr : SymbolicQueryFrame n fuel m t) (space : SymbolicQueryLayout m n fuel)
    (res : SymbolicCacheReservation m L n fuel) (j : ℕ) (hj : j ≤ n) :
    t.data (t.index 67+j)=m.data (m.index 67+j) := by
  rw [fr.header space 67 (by decide) (by decide) (by decide)]
  have hi : 128 ≤ m.index 67 := space.scan.rowHigh
  exact fr.high_data _ (by omega) (res.row j hj)

theorem SymbolicQueryFrame.workspace {m t : Memory ℚ} {n fuel : ℕ}
    (fr : SymbolicQueryFrame n fuel m t) (space : SymbolicQueryLayout m n fuel) :
    SymbolicQueryLayout t n fuel :=
  space.transfer_headers (fun i lo hi aux => fr.header space i lo (by omega) aux)

theorem SymbolicQueryFrame.reservation {m t : Memory ℚ} {L : Buffers} {n fuel : ℕ}
    (fr : SymbolicQueryFrame n fuel m t) (space : SymbolicQueryLayout m n fuel)
    (res : SymbolicCacheReservation m L n fuel) : SymbolicCacheReservation t L n fuel :=
  res.transfer_headers (fun i lo hi aux => fr.header space i lo (by omega) aux)

end Compression
end LinearProgramming
end Optimization
end OAI
