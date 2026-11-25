import OAI.Optimization.LinearProgramming.Compression.SymbolicQueryLayout
import OAI.Optimization.LinearProgramming.Compression.SymbolicQueryTime
import OAI.Optimization.LinearProgramming.Compression.SymbolicSerialize
import OAI.Optimization.LinearProgramming.Compression.SymbolicPackingBounds
import OAI.Optimization.LinearProgramming.Compression.CallableReentrantOffset
import OAI.Optimization.LinearProgramming.Compression.CallableReentrantProxy
import OAI.Optimization.LinearProgramming.Compression.PowerPairCaller
import OAI.Optimization.LinearProgramming.RAM.CallableOddLeaf
import OAI.Optimization.LinearProgramming.FieldTransfer.ProxyPacking

/-! Fixed native call for a materialized affine query with at least one symbolic
logarithm. The numerator cache, offset evaluation, operand compaction, scalar
serialization, comparison and return each use the executable RAM semantics. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM RAM.Callable FieldTransfer
open scoped BigOperators

def symbolicProxyQueryFragment (dest : TagSink) : Fragment :=
  .seq (Odd.leaf smallCacheRawBlock) <|
  .seq (Fragment.stage proxyOffsetFragment) <|
  .seq (Odd.leaf ProxyPacking.compactOperands) <|
  .seq (Odd.leaf symbolicSerialize) (reentrantProxySignFragment dest)

private theorem symbolicFrame_compose {m s v t : Memory ℚ} {n fuel : ℕ} {x : ℚ} {ps : List (ℚ×ℤ)}
    (first : SmallCachePackFrame n m s) (mid : ProxyPacking.Packed (symbolicScanLayout m n)
      (s.putData 45 x) v ps) (last : SymbolicSerializeFrame (symbolicPairAreas m) (n+1)
      (symbolicDigitWidth fuel) v t) (hlen : ps.length ≤ n+1) :
    SymbolicQueryFrame n fuel m t := by
  constructor
  · intro i hi h8 low h40 h41 h45 h87 h68 h69 h89
    have hdst : i < m.index 87 ∨ m.index 87+((n+1)+4) ≤ i := by omega
    have a := last.data i hi h40 h41 h89 hdst
    have b := mid.dataFrame i low
      (fun k hk => by change i ≠ m.index 68+k; omega) (fun k hk => by change i ≠ m.index 69+k; omega)
    exact a.trans (b.trans ((Memory.putData_ne _ h45 _).trans (first.scalars i (by omega) h8 h87)))
  · intro i hi low h54 h55 h56 h57 h58 h59 aux dim tokens
    have a := last.index i hi (by omega) h54 h55 h56 h57 h58 h59 tokens
    exact a.trans ((mid.indexFrame i low aux).trans (first.addresses i (by omega) h55 h56 h57 h58 dim))

/-- The public mixed-branch contract. The returned `staged` memory describes
all off-workspace cells before the destination tag is written. `C` bounds the
even registers both on entry and on return. -/
theorem symbolicProxyQueryFragment_run {n : ℕ} (fuel prec B C : ℕ) {A : ℤ}
    (c : ℤ) (a : ℕ → ℤ) (mag : ℕ → ℚ) (old m : Memory ℚ) (P : ℚ → Prop)
    (dest : TagSink) (L : MinorProxyCache.Buffers)
    (cache : MinorProxyCache.StableCache m L n fuel prec mag) (space : SymbolicQueryLayout m n fuel)
    (hbits : ∀ i : Fin n, ratBits (mag i) ≤ B)
    (hform : |c|+∑ i : Fin n, |a i|≤A) (hcut : (2:ℤ)^prec*A ≤ 2^fuel)
    (row : ∀ i < n, m.data (m.index 67+i)=(a i:ℚ)) (rhs : m.data (m.index 67+n)=(c:ℚ))
    (hm : m.AllData P) (hold : old.AllData P) (foot : Footprint C (old.atPC 0))
    (capacity : m.index 60=C+1) (flag : m.index 61=1)
    (hcap : symbolicQueryCap n fuel ≤ C)
    (hq : ∀ q, ratBits q ≤ symbolicQueryBits n fuel prec B → P q)
    (hr : ∀ tag < 3, (dest.store tag m).AllData P) :
    let form := (c:ℝ) + ∑ i : Fin n, (a i:ℝ) * logProxyValue prec (mag i) (logProxyNumerator fuel prec (mag i))
    let tag : ℕ := if form < 0 then 0 else if 0 < form then 2 else 1
    ∃ last staged : Memory ℚ, (symbolicProxyQueryFragment dest).Run P (Odd.memory old m)
      (symbolicQuerySteps n fuel C) (Odd.memory last (dest.store tag staged)) ∧
      Footprint C (last.atPC 0) ∧ SymbolicQueryFrame n fuel m staged := by
  classical
  let af (i : Fin n) := a i
  let mf (i : Fin n) := mag i
  let D := (2:ℕ)^(prec+2)
  let grid (i : Fin n) := (logProxyNumerator fuel prec (mf i)).getD 0
  let ix := proxyLargeIndices fuel prec mf
  let offset := clearedProxyOffset ix.toFinset D c af grid
  let ps := proxyPowerOperands ix offset D af mf
  let pick (j : ℕ) := (logProxyNumerator fuel prec (mag j)).isNone
  let w := symbolicDigitWidth fuel
  have hmag (i : Fin n) : 0 < mf i := symbolicCache_positive cache i
  have smallBits : proxyQueryBits n fuel prec B ≤ symbolicQueryBits n fuel prec B := le_max_left ..
  have wordBits : 2*w+5 ≤ symbolicQueryBits n fuel prec B := le_max_right ..
  have hzero : P 0 := hq 0 ((by rfl : ratBits 0=3).le.trans (by omega))
  have htwo : P 2 := hq 2 ((by rfl : ratBits 2=4).le.trans (by omega))
  have hgridHigh : 128 ≤ m.index 81 := by
    rw [cache.header.numerators]
    exact (le_max_left ..).trans cache.separated.gridHigh
  obtain ⟨s,prep,raw,first⟩ := smallCacheRawTapes_spec m n D C c af grid hm hzero cache.header.size
    (symbolicCache_scale cache) capacity space.scan.rowHigh hgridHigh space.encode.scalarHigh space.dimHigh
    space.rowTape space.gridTape (fun i => row i i.isLt) rhs (symbolicCache_grid cache)
  have prepRun := Odd.leaf_run P old hold prep
  obtain ⟨middle,offsetRun,footMid⟩ := reentrantProxyOffsetFragment_raw fuel prec C c af mf old s P
    (m.index 87) (m.index 88) hmag hform hcut
    (fun q h => hq q (h.trans ((le_max_left ..).trans smallBits))) prep.safe_end hold hzero foot raw
    ((le_max_right ..).trans hcap)
  let u := s.putData 45 (offset:ℚ)
  have off : (Fragment.stage proxyOffsetFragment).Run P (Odd.memory old s)
      (19*(C+1)+225+(2*(9*(n+1)+3)+3)) (Odd.memory middle u) := by
    simpa only [u,offset,ix,proxyLargeIndices_toFinset,D,grid] using offsetRun
  have hu : u.AllData P := fun i => by simpa only [Odd.data_slot] using off.safe_end (Odd.slot i)
  have hmid : middle.AllData P := fun i => by simpa only [Odd.data_even] using off.safe_end (2*i)
  obtain ⟨width,scaleBits,_⟩ := canonicalProxyPowerOperands_width fuel prec c af mf hmag hform hcut
  have inp := symbolicScan_after_offset n fuel prec mag a offset cache space row first
  obtain ⟨v,k,hk,comp,packed⟩ := ProxyPacking.compactOperands_correct space.scan inp hu htwo
    (fun j hj _ => hq _ ((scaleBits ⟨j,hj⟩).trans (by dsimp [w,symbolicDigitWidth] at wordBits; omega)))
  have psEq : ProxyPacking.operandPrefix pick mag a offset D n=ps := by
    rw [ProxyPacking.rational_operandPrefix,canonicalProxyPowerOperands_range]
  have packed' : ProxyPacking.Packed (symbolicScanLayout m n) u v ps := psEq ▸ packed
  have hlen : ps.length ≤ n+1 := psEq ▸ ProxyPacking.operandPrefix_length pick mag a offset D n
  have compRun := (Odd.leaf_run P middle hmid comp).mono (Nat.mul_le_mul_left 4 hk)
  have dim := space.dimHigh
  have vi (i : ℕ) (hi : 60 ≤ i) (hj : i < 128) (haux : i < 70 ∨ 75 < i) : v.index i=m.index i :=
    (packed'.indexFrame i (by omega) haux).trans (first.addresses i (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega))
  have closed (z : ℕ) (hz : z ≤ 2^(2*w+2)) : P (z:ℚ) :=
    hq _ ((natCast_ratBits_le hz).trans (by omega))
  obtain ⟨t,l,hl,encode,encoded,encFrame⟩ := symbolicSerialize_eval (symbolicPairAreas m) (n+1) w ps v
    comp.safe_end space.encode hlen packed'.count packed'.bases packed'.exponents
    (vi 87 (by decide) (by decide) (by decide)) (vi 89 (by decide) (by decide) (by decide))
    (vi 90 (by decide) (by decide) (by decide)) packed'.contents width closed
  have encRun := (Odd.leaf_run P middle hmid encode).mono (Nat.mul_le_mul_left 4 hl)
  have frame := symbolicFrame_compose first packed' encFrame hlen
  have sym := symbolicCache_nonempty cache flag
  let tapeBase := m.index 90-(2*(signedBitTape (ps.map Prod.snd)).length+8)
  let native := preparedProxyQuery fuel prec c af mf
  have ready : RawTapes t (m.index 87) tapeBase (C+1) native.scalar native.address := by
    have h := symbolicProxyPairTapes fuel prec c af mf sym encoded
    have hv : v.index 60=C+1 := (vi 60 (by decide) (by decide) (by decide)).trans capacity
    simpa only [symbolicPairAreas, tapeBase, native, hv] using h
  have hflag : t.index 61=native.symbolic.toNat := by
    rw [frame.header space 61 (by decide) (by decide) (by decide),flag]
    simp [native,preparedProxyQuery,show proxyLargeIndices fuel prec mf ≠ [] from sym]
  have hz : t.index 62=0 := (frame.header space 62 (by decide) (by decide) (by decide)).trans cache.zero
  obtain ⟨last,sign,lastFoot⟩ := reentrantProxySignFragment_raw fuel prec B C c af mf middle t P dest
    (m.index 87) tapeBase hmag hbits hform hcut (fun q h => hq q (h.trans smallBits))
    encode.safe_end hmid hzero footMid (fun tag ht => smallProxySink_store_safe dest tag m t (hr tag ht)
      encode.safe_end) hflag hz ready
    ((directProxyWindow_le_reentrantQueryCap fuel prec B c af mf hmag hbits hform hcut).trans
      ((le_max_left ..).trans hcap))
  exact ⟨last,t,prepRun.seq (off.seq (compRun.seq (encRun.seq sign))),lastFoot,frame⟩

end Compression
end LinearProgramming
end Optimization
end OAI
