import OAI.Optimization.LinearProgramming.RAM.SafeRun
import OAI.Optimization.LinearProgramming.Compression.ProxyDriverMetadata
import OAI.Optimization.LinearProgramming.Compression.ProxyNormalHeader
import OAI.Optimization.LinearProgramming.Compression.ProxyFuelCoefficients
import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheStart

/-! A single native cache call from the normal numerical request tape. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM RAM.Callable MinorProxyCache

/-- One fixed executable fragment for the whole initialization and logarithm batch.
The coefficient list is computed from the manuscript's fixed polynomial. -/
def numericProxyCache : Fragment :=
  Fragment.seq (.ofBlock (normalProxyHeader manuscriptProxyFuelCoefficients)) MinorProxyCache.fromPositive

def numericCachePrecision (N : ℕ) := 100*(N+1)^3+7

def numericCacheAddressEnd (N : ℕ) :=
  (8+numericCachePrecision N+1)+manuscriptProxyFuel N+1

noncomputable def numericProxyCacheSteps (N g : ℕ) : ℕ :=
  normalProxyHeaderSteps manuscriptProxyFuelCoefficients N g +
    fromPositiveCost (g+1) (manuscriptProxyFuel N) (numericCachePrecision N) (g+8) (numericCacheAddressEnd N)

noncomputable def numericProxyCacheBits (N B : ℕ) : ℕ :=
  cacheBits (max B (parameterBits manuscriptProxyFuelPolynomial N)) B (manuscriptProxyFuel N)
    (numericCachePrecision N)

def numericProxyCacheBuffers (N g : ℕ) : Buffers :=
  buffers (g+1) (manuscriptProxyFuel N) (numericCachePrecision N) (g+8) (numericCacheAddressEnd N)

/-- Normal request ABI for the numerical service. The actual cached proxies represent
the vector in its supplied order. Address registers 90, 91, 92 and 93 return the
dimension, preceding generator count, membership bit and insertion rank. -/
theorem numericProxyCache_framed (N g rank B : ℕ) (member : Bool) (mag : Fin (g+1) → ℚ)
    (positive : ∀ i, 0 < mag i) (words : ∀ i, ratBits (mag i) ≤ B) :
    let s := (start [N,g,member.toNat,rank] (List.ofFn mag)).memory
    ∃ t, numericProxyCache.Run (fun q => ratBits q ≤ numericProxyCacheBits N B) s
        (numericProxyCacheSteps N g) t ∧
      StableCache t (numericProxyCacheBuffers N g) (g+1) (manuscriptProxyFuel N)
        (numericCachePrecision N) (tapeMagnitude mag) ∧
      t.index 60 = 0 ∧ t.index 90 = N ∧ t.index 91 = g ∧
      t.index 92 = member.toNat ∧ t.index 93 = rank ∧ ProxyDriverMetadata N g member.toNat rank t := by
  intro s
  let H := max B (parameterBits manuscriptProxyFuelPolynomial N)
  let fuel := manuscriptProxyFuel N
  let prec := numericCachePrecision N
  have coeff (j : ℕ) : parameterCoefficientValue manuscriptProxyFuelCoefficients j =
      manuscriptProxyFuelPolynomial.eval j :=
    (manuscriptProxyFuelCoefficients_value j).trans (manuscriptProxyFuelPolynomial_eval j).symm
  obtain ⟨u,hhead,out,values⟩ := normalProxyHeader_on_input manuscriptProxyFuelCoefficients
    manuscriptProxyFuelPolynomial coeff N g rank B H member mag words (le_max_left _ _) (le_max_right _ _)
  have hf : u.index 1 = fuel := out.cutoff.trans (manuscriptProxyFuelPolynomial_eval N)
  have he : u.index 4 = numericCacheAddressEnd N := by
    simpa [numericCacheAddressEnd,numericCachePrecision,manuscriptProxyFuelPolynomial_eval] using out.protectedEnd
  obtain ⟨t,run,cache,h60,frame⟩ := fromPositive_rational_framed H B (g+1) fuel prec
    (g+8) (numericCacheAddressEnd N) (tapeMagnitude mag) u hhead.safe_end out.count hf
    out.precision out.base he
    (fun i hi => (values ⟨i,hi⟩).trans (tapeMagnitude_fin mag ⟨i,hi⟩).symm)
    (fun i hi => by simpa only [tapeMagnitude_fin mag ⟨i,hi⟩] using positive ⟨i,hi⟩)
    (fun i hi => by simpa only [tapeMagnitude_fin mag ⟨i,hi⟩] using words ⟨i,hi⟩)
  have hcap : H ≤ numericProxyCacheBits N B := by
    change H ≤ cacheBits H B fuel prec
    unfold cacheBits
    omega
  have pre := Fragment.Run.weakenData (P := fun q : ℚ => ratBits q ≤ H)
    (Q := fun q : ℚ => ratBits q ≤ numericProxyCacheBits N B)
    (Fragment.Run.ofBlock (P := fun q : ℚ => ratBits q ≤ H) hhead)
    (fun _ bound => Nat.le_trans bound hcap)
  exact ⟨t,pre.seq run,cache,h60.trans out.cacheCounter,
    (frame.driver 90 (by decide) (by decide)).trans out.dimension,
    (frame.driver 91 (by decide) (by decide)).trans out.generators,
    (frame.driver 92 (by decide) (by decide)).trans out.membership,
    (frame.driver 93 (by decide) (by decide)).trans out.position,
    ⟨(frame.driver 102 (by decide) (by decide)).trans out.stableDimension,
     (frame.driver 103 (by decide) (by decide)).trans out.stableGenerators,
     (frame.driver 104 (by decide) (by decide)).trans out.stableMembership,
     (frame.driver 105 (by decide) (by decide)).trans out.stablePosition⟩⟩

/-- The initial cache-return interface, before a sign call borrows address 90. -/
theorem numericProxyCache_run (N g rank B : ℕ) (member : Bool) (mag : Fin (g+1) → ℚ)
    (positive : ∀ i, 0 < mag i) (words : ∀ i, ratBits (mag i) ≤ B) :
    let s := (start [N,g,member.toNat,rank] (List.ofFn mag)).memory
    ∃ t, numericProxyCache.Run (fun q => ratBits q ≤ numericProxyCacheBits N B) s
        (numericProxyCacheSteps N g) t ∧
      StableCache t (numericProxyCacheBuffers N g) (g+1) (manuscriptProxyFuel N)
        (numericCachePrecision N) (tapeMagnitude mag) ∧
      t.index 60 = 0 ∧ t.index 90 = N ∧ t.index 91 = g ∧
      t.index 92 = member.toNat ∧ t.index 93 = rank := by
  obtain ⟨t,run,cache,h60,h90,h91,h92,h93,_⟩ := numericProxyCache_framed N g rank B member mag positive words
  exact ⟨t,run,cache,h60,h90,h91,h92,h93⟩

/-- The same native fragment as a standalone halted trace, with every intermediate
physical rational register bounded. -/
theorem numericProxyCache_trace (N g rank B : ℕ) (member : Bool) (mag : Fin (g+1) → ℚ)
    (positive : ∀ i, 0 < mag i) (words : ∀ i, ratBits (mag i) ≤ B) :
    ∃ k ≤ numericProxyCacheSteps N g+1, ∃ tr : Fin (k+1) → State ℚ,
      Trace (numericProxyCache.program 0) (start [N,g,member.toNat,rank] (List.ofFn mag)) k tr ∧
      (tr (Fin.last k)).output = some 0 ∧
      StableCache (tr (Fin.last k)).memory (numericProxyCacheBuffers N g) (g+1) (manuscriptProxyFuel N)
        (numericCachePrecision N) (tapeMagnitude mag) ∧
      (tr (Fin.last k)).index 90 = N ∧ (tr (Fin.last k)).index 91 = g ∧
      (tr (Fin.last k)).index 92 = member.toNat ∧ (tr (Fin.last k)).index 93 = rank ∧
      ProxyDriverMetadata N g member.toNat rank (tr (Fin.last k)).memory ∧
      ∀ i, scalarBound (numericProxyCacheBits N B) (tr i) := by
  obtain ⟨z,hz,hcache,_,h90,h91,h92,h93,stable⟩ := numericProxyCache_framed N g rank B member mag positive words
  obtain ⟨k,hk,tr,ht,htag,hmem,hsize⟩ := Fragment.run_halt hz 0
  refine ⟨k,hk,tr,ht,htag,hmem ▸ hcache,?_,?_,?_,?_,hmem ▸ stable,hsize⟩
  · change (tr (Fin.last k)).memory.index 90 = N
    rw [hmem]; exact h90
  · change (tr (Fin.last k)).memory.index 91 = g
    rw [hmem]; exact h91
  · change (tr (Fin.last k)).memory.index 92 = member.toNat
    rw [hmem]; exact h92
  · change (tr (Fin.last k)).memory.index 93 = rank
    rw [hmem]; exact h93

end Compression
end LinearProgramming
end Optimization
end OAI
