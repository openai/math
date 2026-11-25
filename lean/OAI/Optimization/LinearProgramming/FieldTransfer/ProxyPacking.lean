import OAI.Optimization.LinearProgramming.FieldTransfer.ProxyPackingRun
import OAI.Optimization.LinearProgramming.Compression.ProxyPrepared
import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheLayout

/-! Interpret the signed operand stream in the stable minor cache and the rational proxy comparator. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace FieldTransfer
namespace ProxyPacking

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The source addresses retained by the minor-proxy cache, together with the current
affine row and the two separate outgoing scalar arrays. -/
def queryLayout (cache : Compression.MinorProxyCache.Buffers) (n row bases exponents : Nat) : Layout :=
  ⟨n,cache.magBase,cache.flagBase,row,bases,exponents⟩

/-- The checked cache supplies the magnitude, symbolic flag, and common denominator
cells used by the physical scan. Only the new query row and its output pointers enter
through the per-query calling convention. -/
theorem inputs_of_stable_cache {cache : Compression.MinorProxyCache.Buffers} {m : Memory K}
    {n fuel prec row bases exponents : Nat} {mag : Nat → K} {a : Nat → ℤ} {offset : ℤ}
    (old : Compression.MinorProxyCache.StableCache m cache n fuel prec mag)
    (hrow : m.index 67=row) (hb : m.index 68=bases) (he : m.index 69=exponents)
    (constant : m.data 45=(offset:K)) (coeff : ∀ j < n, m.data (row+j)=(a j:K)) :
    Inputs (queryLayout cache n row bases exponents) m
      (fun j => (Compression.fieldProxyNumerator fuel prec (mag j)).isNone) mag a offset (2^(prec+2)) := by
  refine ⟨old.zero,hrow,hb,he,old.header.magnitudes,old.header.flags,old.header.size,?_,
    constant,old.magnitude,coeff,?_⟩
  · rw [old.header.scalePtr,old.scale]
    simp
  · intro j hj
    change m.index (cache.flagBase+j)=_
    rw [old.symbolic j hj]
    cases Compression.fieldProxyNumerator fuel prec (mag j) <;> rfl

/-- Subsequent affine queries can reuse the same cached field data when the two output
pages also avoid the grid and scale cells. -/
theorem Packed.stableCache {cache : Compression.MinorProxyCache.Buffers} {m t : Memory K}
    {n fuel prec row bases exponents : Nat} {mag : Nat → K} {ps : List (K × ℤ)}
    (post : Packed (queryLayout cache n row bases exponents) m t ps)
    (old : Compression.MinorProxyCache.StableCache m cache n fuel prec mag)
    (valid : (queryLayout cache n row bases exponents).Valid) (len : ps.length ≤ n+1)
    (gridB : Apart cache.gridBase n bases (n+1)) (gridE : Apart cache.gridBase n exponents (n+1))
    (scaleB : Apart cache.scalePtr 1 bases (n+1)) (scaleE : Apart cache.scalePtr 1 exponents (n+1)) :
    Compression.MinorProxyCache.StableCache t cache n fuel prec mag := by
  have hmag : Apart cache.magBase n bases (n+1) := valid.magBase
  have hexp : Apart cache.magBase n exponents (n+1) := valid.magExp
  have magHigh : 128 ≤ cache.magBase := valid.magHigh
  have flagHigh := old.separated.flagHigh
  have gridHigh : 128 ≤ cache.gridBase := (Nat.le_max_left ..).trans old.separated.gridHigh
  have scaleHigh : 128 ≤ cache.scalePtr := (Nat.le_max_left ..).trans old.separated.scaleHigh
  refine ⟨old.header.transfer (fun j hj _ => post.indexFrame j (by omega) (by omega)),
    old.separated,?_,old.positive,?_,?_,?_,?_,?_⟩
  · intro j hj
    exact (post.dataFrame _ (by omega) (fun k hk => hmag.ne hj (by omega))
      (fun k hk => hexp.ne hj (by omega))).trans (old.magnitude j hj)
  · intro j hj
    exact (post.dataFrame _ (by omega) (fun k hk => gridB.ne hj (by omega))
      (fun k hk => gridE.ne hj (by omega))).trans (old.numerator j hj)
  · intro j hj
    exact (post.indexFrame _ (by omega) (by omega)).trans (old.symbolic j hj)
  · exact (post.indexFrame _ (by omega) (by omega)).trans old.any
  · exact (post.indexFrame _ (by omega) (by omega)).trans old.zero
  · exact (post.dataFrame _ (by omega)
      (fun k hk => by
        change cache.scalePtr ≠ bases+k
        simpa only [Nat.add_zero] using scaleB.ne (i:=0) (j:=k) (by decide) (by omega))
      (fun k hk => by
        change cache.scalePtr ≠ exponents+k
        simpa only [Nat.add_zero] using scaleE.ne (i:=0) (j:=k) (by decide) (by omega))).trans old.scale

/-- In the rational implementation these are exactly the operands consumed by the
formal proxy-product comparison routine. -/
theorem rational_operandPrefix (pick : Nat → Bool) (mag : Nat → ℚ) (a : Nat → ℤ)
    (offset : ℤ) (D n : Nat) :
    operandPrefix pick mag a offset D n =
      Compression.proxyPowerOperands ((List.range n).filter pick) offset D a mag := rfl

/-- When the stored flags are the actual proxy-cache flags, the compacted scalar
buffers are exactly the canonical finite-index operands of the rational comparator. -/
theorem cached_operandPrefix (n fuel prec : Nat) (pick : Nat → Bool) (mag : Nat → ℚ)
    (a : Nat → ℤ) (offset : ℤ) (D : Nat)
    (flag : ∀ i : Fin n, pick i.val = (Compression.logProxyNumerator fuel prec (mag i.val)).isNone) :
    operandPrefix pick mag a offset D n =
      Compression.proxyPowerOperands
        (Compression.proxyLargeIndices fuel prec (fun i : Fin n => mag i.val))
        offset D (fun i => a i.val) (fun i => mag i.val) := by
  rw [finite_operandPrefix]
  have hp := funext flag
  rw [hp]
  rfl

theorem scaled_rational_bits (D : Nat) (a : ℤ) :
    ratBits ((((D:ℤ)*a):ℤ):ℚ) ≤ ratBits (D:ℚ)+ratBits (a:ℚ) := by
  simpa using Compression.ratBits_mul_le_add (D:ℚ) (a:ℚ)

end ProxyPacking
end FieldTransfer
end LinearProgramming
end Optimization
end OAI
