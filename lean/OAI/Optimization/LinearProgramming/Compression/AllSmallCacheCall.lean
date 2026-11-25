import OAI.Optimization.LinearProgramming.Compression.SmallProxyCacheFrame
import OAI.Optimization.LinearProgramming.Compression.CallableReentrantProxy
import OAI.Optimization.LinearProgramming.RAM.CallableOddBlock

/-! Invoke the numerical branch directly from the permanent logarithm cache
and the current query row. The dirty native bank obeys one common footprint
at entry and exit. The caller chooses how and where the three-way tag is stored. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM RAM.Callable MinorProxyCache
open scoped BigOperators

def allSmallCacheCall (dest : TagSink) : Fragment :=
  .seq (.ofBlock (Odd.block smallCacheRawBlock)) (reentrantProxySignFragment dest)

def allSmallCacheCallSteps (n fuel C : ℕ) : ℕ :=
  4*(21*n+57)+(19*(C+1)+225+(2*proxyQuerySteps n fuel+4))

theorem allSmallCacheCall_spec {n fuel prec B C : ℕ} {A : ℤ} (c : ℤ) (a : Fin n → ℤ)
    (mag : ℕ → ℚ) (old m : Memory ℚ) (P : ℚ → Prop) (dest : TagSink) {L : Buffers}
    (cache : StableCache m L n fuel prec mag) (w : SmallCacheWorkspace m L n) (flag : m.index 61=0)
    (capacity : m.index 60=C+1) (coeff : ∀ i : Fin n, m.data (m.index 67+i)=(a i:ℚ))
    (rhs : m.data (m.index 67+n)=(c:ℚ)) (hm : m.AllData P) (hold : old.AllData P) (hz : P 0)
    (foot : Footprint C (old.atPC 0)) (hr : ∀ tag < 3, (dest.store tag m).AllData P)
    (hbits : ∀ i : Fin n, ratBits (mag i) ≤ B) (hform : |c| + ∑ i, |a i| ≤ A)
    (hcut : (2 : ℤ)^prec * A ≤ 2^fuel) (hq : ∀ q, ratBits q ≤ proxyQueryBits n fuel prec B → P q)
    (hwindow : directProxyWindow (preparedProxyQuery fuel prec c a (fun i => mag i)) + proxyQuerySteps n fuel ≤ C) :
    let form := (c : ℝ) + ∑ i : Fin n, (a i : ℝ) * logProxyValue prec (mag i) (logProxyNumerator fuel prec (mag i))
    let tag : ℕ := if form < 0 then 0 else if 0 < form then 2 else 1
    ∃ last staged : Memory ℚ, (allSmallCacheCall dest).Run P (Odd.memory old m)
      (allSmallCacheCallSteps n fuel C) (Odd.memory last (dest.store tag staged)) ∧
      Footprint C (last.atPC 0) ∧ SmallCachePackFrame n m staged ∧
      StableCache staged L n fuel prec mag ∧ SmallCacheWorkspace staged L n := by
  let ms : Fin n → ℚ := fun i => mag i
  have small : proxyLargeIndices fuel prec ms=[] := by
    apply (proxyLargeIndices_empty_iff fuel prec ms).2
    intro i e
    have h := cache.allSmall_of_noSymbolic flag i i.isLt
    rw [fieldProxyNumerator_rat] at h
    change logProxyNumerator fuel prec (mag i)=none at e
    simp [e] at h
  have tt := preparedProxyQuery_small_input fuel prec c a ms small
  obtain ⟨t,pack,raw,fr,tc,tw⟩ := smallCacheRawTapes_fromStable m mag c a cache w hm hz capacity coeff rhs
  have adapted : let p := preparedProxyQuery fuel prec c a ms
      RawTapes t (m.index 87) (m.index 88) (C+1) p.scalar p.address := by
    rw [tt]
    exact raw
  have branch : t.index 61=(preparedProxyQuery fuel prec c a ms).symbolic.toNat := by
    rw [tt]
    exact (fr.addresses 61 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by have := w.addressHigh; omega)).trans flag
  obtain ⟨last,call,foot'⟩ := reentrantProxySignFragment_raw fuel prec B C c a ms old t P dest
    (m.index 87) (m.index 88) (fun i => cache.positive i i.isLt) hbits hform hcut hq
    pack.safe_end hold hz foot (fun tag ht => smallProxySink_store_safe dest tag m t (hr tag ht) pack.safe_end)
    branch tc.zero adapted hwindow
  obtain ⟨k,hk,leaf⟩ := Odd.block_eval P old hold pack
  exact ⟨last,t,(Fragment.Run.ofBlock leaf |>.mono hk).seq call,foot',fr,tc,tw⟩

/-- Ordinary branch sinks lie below the permanent headers. They leave the full
cache usable at the next query, including a scalar-valued sign sink. -/
theorem smallCache_tag_lt_header {L : Buffers} {n fuel prec tag : ℕ} {mag : ℕ → ℚ}
    {m : Memory ℚ} (cache : StableCache m L n fuel prec mag) (dest : TagSink) (low : dest.dst < 55) :
    StableCache (dest.store tag m) L n fuel prec mag := by
  have mh : 128 ≤ L.magBase := (Nat.le_max_left ..).trans cache.separated.magHigh
  have gh : 128 ≤ L.gridBase := (Nat.le_max_left ..).trans cache.separated.gridHigh
  have sh : 128 ≤ L.scalePtr := (Nat.le_max_left ..).trans cache.separated.scaleHigh
  have fh := cache.separated.flagHigh
  have idx (i : ℕ) (hi : 55 ≤ i) : (dest.store tag m).index i=m.index i :=
    dest.store_index_ne tag m (by omega)
  have scalar (i : ℕ) (hi : 55 ≤ i) : (dest.store tag m).data i=m.data i :=
    dest.store_data_ne tag m (by omega)
  refine ⟨cache.header.transfer (fun i lo _ => idx i (by omega)),cache.separated,?_,cache.positive,?_,
    ?_,(idx 61 (by decide)).trans cache.any,(idx 62 (by decide)).trans cache.zero,?_⟩
  · intro i hi
    exact (scalar _ (by omega)).trans (cache.magnitude i hi)
  · intro i hi
    exact (scalar _ (by omega)).trans (cache.numerator i hi)
  · intro i hi
    exact (idx _ (by omega)).trans (cache.symbolic i hi)
  · exact (scalar _ (by omega)).trans cache.scale

theorem SmallCacheWorkspace.tag_lt_header {L : Buffers} {n tag : ℕ} {m : Memory ℚ}
    (w : SmallCacheWorkspace m L n) (dest : TagSink) (low : dest.dst < 55) :
    SmallCacheWorkspace (dest.store tag m) L n := by
  have h67 := dest.store_index_ne tag m (j := 67) (by omega)
  have h87 := dest.store_index_ne tag m (j := 87) (by omega)
  have h88 := dest.store_index_ne tag m (j := 88) (by omega)
  exact ⟨h67 ▸ w.rowHigh,h87 ▸ w.scalarHigh,h88 ▸ w.addressHigh,h67 ▸ h87 ▸ w.row,
    h87 ▸ w.grid,h87 ▸ w.magnitude,h87 ▸ w.scale,h88 ▸ w.flag⟩

end Compression
end LinearProgramming
end Optimization
end OAI
