import OAI.Optimization.LinearProgramming.Compression.SignWireCost
import OAI.Optimization.LinearProgramming.Compression.AllSmallCacheCall
import OAI.Optimization.LinearProgramming.Compression.SymbolicQueryCall

/-! A single runtime sign comparator for both kinds of cached logarithm
proxies. Each branch starts with the same live coefficient row and a dirty
bounded native working bank. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
open RAM RAM.Callable MinorProxyCache
open scoped BigOperators

/-- The cached symbolic flag selects the implementation at runtime. -/
def cachedProxySignFragment (dest : TagSink) : Fragment :=
  .branch (Odd.cond (.addrLT 62 61)) (symbolicProxyQueryFragment dest) (allSmallCacheCall dest)

private theorem anySymbolic_le_one (a : ℕ → Option ℤ) (n : ℕ) : anySymbolic a n ≤ 1 := by
  induction n with
  | zero => simp [anySymbolic]
  | succ n ih => rw [anySymbolic];split <;> omega

theorem SymbolicQueryLayout.smallWorkspace {n fuel prec : ℕ} {m : Memory ℚ}
    {L : Buffers} {mag : ℕ → ℚ} (space : SymbolicQueryLayout m n fuel)
    (cache : StableCache m L n fuel prec mag) : SmallCacheWorkspace m L n := by
  refine ⟨space.scan.rowHigh,space.encode.scalarHigh,space.dimHigh,space.rowTape,?_,?_,?_,?_⟩
  · simpa only [cache.header.numerators] using space.gridTape
  · simpa only [cache.header.magnitudes] using space.magTape
  · simpa only [cache.header.scalePtr] using space.scaleTape
  · simpa only [cache.header.flags,or_comm] using space.flagDim

theorem SmallCachePackFrame.toSymbolic {n : ℕ} (fuel : ℕ) {m t : Memory ℚ}
    (h : SmallCachePackFrame n m t) : SymbolicQueryFrame n fuel m t := by
  constructor
  · intro i hi h8 _ _ _ _ tape _ _ _; exact h.scalars i (by omega) h8 tape
  · intro i hi _ _ h55 h56 h57 h58 _ _ hd _; exact h.addresses i (by omega) h55 h56 h57 h58 hd

/-- One relocatable machine sequence, including both physical input packing
paths, the original native comparison and the prescribed three-way tag. -/
theorem cachedProxySignFragment_run {n : ℕ} (fuel prec B C : ℕ) {A : ℤ}
    (c : ℤ) (a : ℕ → ℤ) (mag : ℕ → ℚ) (old m : Memory ℚ) (P : ℚ → Prop)
    (dest : TagSink) (L : Buffers) (cache : StableCache m L n fuel prec mag)
    (space : SymbolicQueryLayout m n fuel) (bits : ∀ i : Fin n, ratBits (mag i) ≤ B)
    (form : |c|+∑ i : Fin n, |a i| ≤ A) (cut : (2:ℤ)^prec*A ≤ 2^fuel)
    (row : ∀ i < n, m.data (m.index 67+i)=(a i:ℚ)) (rhs : m.data (m.index 67+n)=(c:ℚ))
    (hm : m.AllData P) (hold : old.AllData P) (foot : Footprint C (old.atPC 0))
    (capacity : m.index 60=C+1) (hcap : symbolicQueryCap n fuel ≤ C)
    (hq : ∀ q, ratBits q ≤ symbolicQueryBits n fuel prec B → P q)
    (hr : ∀ tag < 3, (dest.store tag m).AllData P) :
    let f := (c:ℝ) + ∑ i : Fin n, (a i:ℝ) * logProxyValue prec (mag i) (logProxyNumerator fuel prec (mag i))
    let tag : ℕ := if f<0 then 0 else if 0<f then 2 else 1
    ∃ last staged : Memory ℚ, (cachedProxySignFragment dest).Run P (Odd.memory old m)
      (cachedProxySignSteps n fuel C) (Odd.memory last (dest.store tag staged)) ∧
      Footprint C (last.atPC 0) ∧ SymbolicQueryFrame n fuel m staged := by
  have hflag : m.index 61 ≤ 1 := by rw [cache.any];exact anySymbolic_le_one _ _
  by_cases zero : m.index 61=0
  · have cond : (Odd.cond (.addrLT 62 61)).test (Odd.memory old m)=false := by
      rw [Odd.cond_test]
      simp [Cond.test,zero,cache.zero]
    have cap := (directProxyWindow_le_reentrantQueryCap fuel prec B c
      (fun i : Fin n => a i) (fun i => mag i) (fun i => cache.positive i i.isLt)
      bits form cut).trans ((le_max_left ..).trans hcap)
    have pzero : P 0 := hq _ ((by rfl : ratBits 0=3).le.trans
      (by change 3 ≤ max _ _; exact (show 3 ≤ 2*symbolicDigitWidth fuel+5 by omega).trans (le_max_right ..)))
    obtain ⟨last,staged,run,finite,fr,_,_⟩ := allSmallCacheCall_spec c (fun i : Fin n => a i) mag
      old m P dest cache (space.smallWorkspace cache) zero capacity (fun i => row i i.isLt) rhs
      hm hold pzero foot hr bits form cut (fun q h => hq q (h.trans (le_max_left ..))) cap
    exact ⟨last,staged,(Fragment.Run.branchFalse cond (symbolicProxyQueryFragment dest) run).mono
      (le_max_right ..),finite,fr.toSymbolic fuel⟩
  · have one : m.index 61=1 := by omega
    have cond : (Odd.cond (.addrLT 62 61)).test (Odd.memory old m)=true := by
      rw [Odd.cond_test]
      simp [Cond.test,one,cache.zero]
    obtain ⟨last,staged,run,finite,fr⟩ := symbolicProxyQueryFragment_run fuel prec B C c a mag
      old m P dest L cache space bits form cut row rhs hm hold foot capacity one hcap hq hr
    exact ⟨last,staged,(Fragment.Run.branchTrue cond run (allSmallCacheCall dest)).mono
      (le_max_left ..),finite,fr⟩

end Compression
end LinearProgramming
end Optimization
end OAI
