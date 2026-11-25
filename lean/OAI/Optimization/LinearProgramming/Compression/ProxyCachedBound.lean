import OAI.Optimization.LinearProgramming.Compression.ProxyMemory
import OAI.Optimization.LinearProgramming.Compression.ProxyReadFootprint
import OAI.Optimization.LinearProgramming.Compression.ProxyProgramSpec

/-! Batch-stable bounds for repeated native proxy computations with large caller data. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

/-- Size of the low scalar bank that may supply operands to a raw logarithm call. -/
def proxyReadBank (fuel k : ℕ) := max (9+fuel) (k+14)

private theorem raw_direct_reads : logProxyProgram.all (ProxyMemory.directReadsBelow 10) = true := by
  decide

/-- Each call only requires the low bank to be small. Previously cached high
registers keep their previous size bound, so the caller can reuse the same polynomial
encoding bound across arbitrarily many calls. -/
theorem logProxyProgram_cached_scalarBound (fuel k B H : ℕ) {mag : ℚ} (hm : 0 < mag)
    (s : State ℚ) (hp : s.pc = 0) (ho : s.output = none) (hd : s.data 0 = mag)
    (hf : s.index 0 = fuel) (hk : s.index 1 = k)
    (hlo : ∀ i < proxyReadBank fuel k, ratBits (s.data i) ≤ B) (hglobal : scalarBound H s)
    {n : ℕ} {t : State ℚ} (ht : runExactly logProxyProgram s n = some t) :
    scalarBound (max H (proxyRegisterBound B fuel k)) t := by
  let D := proxyReadBank fuel k
  have hd14 : k+14 ≤ D := le_max_right _ _
  have hD : 0 < D := by omega
  have h3 : 3 ≤ B :=
    (show 3 ≤ ratBits (s.data 0) by unfold ratBits; omega).trans (hlo 0 hD)
  have hmasked : (ProxyMemory.mask D s).data 0 = mag := by simpa [ProxyMemory.mask,hD] using hd
  refine ProxyMemory.transfer_bound (D := D) s h3 hlo hglobal ?_ ?_ ht
  · intro i u hu op hread
    apply ProxyMemory.readsBelow_of_direct (cap := 10) (by omega) op u.index
    · exact List.all_eq_true.mp raw_direct_reads op (List.mem_of_getElem? hread)
    · intro dst addr hload
      subst op
      exact logProxyProgram_indirectReadBound fuel k s hp hf hk hu hread
  · intro hsmall j u hu
    exact logProxyProgram_scalarBound fuel k B hm (ProxyMemory.mask D s) hp ho hmasked hf hk hsmall hu

/-- If the cache-wide bound dominates the single-call cubic bound, every prefix
retains that same bound. The estimate applies uniformly over all calls in the batch. -/
theorem logProxyProgram_cached_stable (fuel k B H : ℕ) {mag : ℚ} (hm : 0 < mag)
    (s : State ℚ) (hp : s.pc = 0) (ho : s.output = none) (hd : s.data 0 = mag)
    (hf : s.index 0 = fuel) (hk : s.index 1 = k)
    (hlo : ∀ i < proxyReadBank fuel k, ratBits (s.data i) ≤ B) (hglobal : scalarBound H s)
    (hcap : polyBound proxySizeCoefficient 3 (B+fuel+k) ≤ H)
    {n : ℕ} {t : State ℚ} (ht : runExactly logProxyProgram s n = some t) : scalarBound H t := by
  intro j
  exact (logProxyProgram_cached_scalarBound fuel k B H hm s hp ho hd hf hk hlo hglobal ht j).trans
    (max_le le_rfl ((proxyRegisterBound_le_polyBound B fuel k).trans hcap))

end Compression
end LinearProgramming
end Optimization
end OAI
