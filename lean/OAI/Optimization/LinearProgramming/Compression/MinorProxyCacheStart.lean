import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheFromPositive
import OAI.Optimization.LinearProgramming.Compression.MinorProxyCacheBits

/-! A normal-entry polynomial-step, polynomial-bit batch of actual logarithm computations. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorProxyCache
open RAM RAM.Callable

theorem scale_bits (j : ℕ) : ratBits ((2:ℚ)^(j+2))≤j+5 := by
  have h := natCast_ratBits_le (n:=2^(j+2)) (e:=j+2) le_rfl
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using h

theorem fromPositive_rational_framed (H B n fuel prec src addressEnd : ℕ) (mag : ℕ→ℚ)
    (m : Memory ℚ) (initial : ∀j,ratBits (m.data j)≤H) (h0 : m.index 0=n) (h1 : m.index 1=fuel)
    (h2 : m.index 2=prec) (h3 : m.index 3=src) (h4 : m.index 4=addressEnd)
    (input : ∀i<n,m.data (src+i)=mag i) (positive : ∀i<n,0<mag i) (words : ∀i<n,ratBits (mag i)≤B) :
    let L := buffers n fuel prec src addressEnd
    ∃ t, fromPositive.Run (fun x : ℚ => ratBits x≤cacheBits H B fuel prec) m
      (fromPositiveCost n fuel prec src addressEnd) t ∧ StableCache t L n fuel prec mag ∧ t.index 60=m.index 60 ∧ Retained m t L n (cap fuel prec) := by
  have hH : H≤cacheBits H B fuel prec := by unfold cacheBits; omega
  have h0' : ratBits 0≤cacheBits H B fuel prec := by change 3≤_; unfold cacheBits; omega
  exact fromPositive_framed (fun x : ℚ => ratBits x≤cacheBits H B fuel prec) (fun x => ratBits x≤B)
    n fuel prec src addressEnd mag m (fun j => (initial j).trans hH) h0' h0 h1 h2 h3 h4 input positive words
    (fun j hj => (scale_bits j).trans (by unfold cacheBits; omega)) (rational_nativeSafe H B fuel prec)
    (fun i hi => (numeratorWord_bits fuel prec (positive i hi)).trans (by unfold cacheBits; omega))

theorem fromPositive_rational_run (H B n fuel prec src addressEnd : ℕ) (mag : ℕ→ℚ)
    (m : Memory ℚ) (initial : ∀j,ratBits (m.data j)≤H) (h0 : m.index 0=n) (h1 : m.index 1=fuel)
    (h2 : m.index 2=prec) (h3 : m.index 3=src) (h4 : m.index 4=addressEnd)
    (input : ∀i<n,m.data (src+i)=mag i) (positive : ∀i<n,0<mag i) (words : ∀i<n,ratBits (mag i)≤B) :
    let L := buffers n fuel prec src addressEnd
    ∃ t, fromPositive.Run (fun x : ℚ => ratBits x≤cacheBits H B fuel prec) m
      (fromPositiveCost n fuel prec src addressEnd) t ∧ StableCache t L n fuel prec mag ∧ t.index 60=m.index 60 := by
  obtain ⟨t,r,out,h60,_⟩ := fromPositive_rational_framed H B n fuel prec src addressEnd mag m initial
    h0 h1 h2 h3 h4 input positive words
  exact ⟨t,r,out,h60⟩

/-- The address list contains only the count and precision parameters, and the
scalar list contains only the positive magnitudes. The RAM computes its own denominator,
output pointers, return flags, and every cached integer numerator. -/
theorem fromPositive_rational {n : ℕ} (B fuel prec : ℕ) (mag : Fin n→ℚ) (positive : ∀i,0<mag i)
    (words : ∀i,ratBits (mag i)≤B) :
    let m := start [n,fuel,prec,0,0] (List.ofFn mag)
    ∃ k≤fromPositiveCost n fuel prec 0 0+1, ∃ tr : Fin (k+1)→State ℚ,
      Trace (fromPositive.program 0) m k tr ∧ (tr (Fin.last k)).output=some 0 ∧
      StableCache (tr (Fin.last k)).memory (buffers n fuel prec 0 0) n fuel prec (tapeMagnitude mag) ∧
      ∀j,scalarBound (cacheBits (B+3) B fuel prec) (tr j) := by
  let m := start [n,fuel,prec,0,0] (List.ofFn mag)
  have initial (i : ℕ) : ratBits (m.data i)≤B+3 := by
    change ratBits (tapeMagnitude mag i)≤B+3
    by_cases h : i<n
    · rw [tapeMagnitude_fin mag ⟨i,h⟩]
      exact (words ⟨i,h⟩).trans (Nat.le_add_right _ _)
    · have zero : tapeMagnitude mag i=0 := by simp [tapeMagnitude,List.getElem?_eq_none (show (List.ofFn mag).length ≤ i by simpa using Nat.le_of_not_gt h)]
      rw [zero]; change 3≤B+3; omega
  obtain ⟨t,run,out,_⟩ := fromPositive_rational_run (B+3) B n fuel prec 0 0 (tapeMagnitude mag) m.memory
    initial rfl rfl rfl rfl rfl (fun i _ => by change tapeMagnitude mag (0+i)=tapeMagnitude mag i; rw [Nat.zero_add])
    (fun i hi => (tapeMagnitude_fin mag ⟨i,hi⟩) ▸ positive ⟨i,hi⟩)
    (fun i hi => (tapeMagnitude_fin mag ⟨i,hi⟩) ▸ words ⟨i,hi⟩)
  obtain ⟨k,hk,tr,trace,tag,mem,safe⟩ := Fragment.run_halt run 0
  exact ⟨k,hk,tr,trace,tag,mem ▸ out,safe⟩

end MinorProxyCache
end Compression
end LinearProgramming
end Optimization
end OAI
