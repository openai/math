import OAI.Optimization.LinearProgramming.Compression.MinorProxyCache
import OAI.Optimization.LinearProgramming.Compression.ProxyCachedBound

/-! A stable rational bit budget for the whole batched cache, independent of the number of calls. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace MinorProxyCache
open RAM RAM.Callable FieldTransfer

/-- An initial bound survives unchanged through untouched cells. All other terms
come from one logarithm call or one explicitly scaled signed integer. -/
def cacheBits (initial magnitude fuel prec : ℕ) := initial+fuel+prec+6+
  polyBound proxySizeCoefficient 3 (magnitude+3+fuel+prec)

theorem numeratorWord_bits (fuel prec : ℕ) {mag : ℚ} (hpos : 0<mag) :
    ratBits (numeratorWord (fieldProxyNumerator fuel prec mag) : ℚ) ≤ fuel+prec+5 := by
  cases h : fieldProxyNumerator fuel prec mag with
  | none => change 3≤fuel+prec+5; omega
  | some v =>
    have absV := fieldProxy_word_length fuel prec hpos h
    have bits : v.natAbs.log2 ≤ fuel+prec+2 := by
      by_cases z : v.natAbs=0
      · simp [z]
      · exact Nat.le_of_lt ((Nat.log2_lt z).mpr absV)
    simp only [numeratorWord,Option.getD_some,ratBits,Rat.num_intCast,Rat.den_intCast,
      show (1:ℕ).log2=0 by decide,Nat.add_zero]
    omega

theorem rational_nativeSafe (H B fuel prec : ℕ) :
    NativeSafe (fun x : ℚ => ratBits x≤cacheBits H B fuel prec) (fun x => ratBits x≤B) fuel prec := by
  intro s safe allowed positive hf hp clear l v run
  apply logProxyProgram_cached_stable fuel prec (B+3) (cacheBits H B fuel prec) positive
    (s.atPC 0) rfl rfl rfl hf hp _ safe _ run
  · intro i hi
    by_cases eq : i=0
    · subst i; change ratBits (s.data 0)≤B+3; omega
    · have ca : proxyReadBank fuel prec≤cap fuel prec := by unfold proxyReadBank cap; omega
      change ratBits (s.data i)≤B+3
      rw [clear i (by omega) (hi.trans_le ca)]
      change 3≤B+3; omega
  · unfold cacheBits; omega

/-- Starting with a dense positive magnitude tape, the fixed compiled cache
produces every gridded numerator, every symbolic bit, and the correct global tag.
Each rational register in each individual step obeys one polynomial envelope. -/
theorem materialize_rational (H B fuel prec n : ℕ) (L : Buffers) (mag : ℕ→ℚ) (m : Memory ℚ)
    (head : Header m L n fuel prec) (sep : Separated L n (cap fuel prec)) (limit : m.index 79=cap fuel prec)
    (scale : m.data L.scalePtr=(2:ℚ)^(prec+2)) (input : ∀i<n,m.data (L.magBase+i)=mag i)
    (positive : ∀i<n,0<mag i) (initial : ∀j,ratBits (m.data j)≤H) (bits : ∀i<n,ratBits (mag i)≤B) :
    ∃ k≤cacheCost n fuel prec+1, ∃ tr : Fin (k+1)→State ℚ,
      Trace (materialize.program 0) (m.atPC 0) k tr ∧ (tr (Fin.last k)).output=some 0 ∧
      StableCache (tr (Fin.last k)).memory L n fuel prec mag ∧ (tr (Fin.last k)).index 60=m.index 60 ∧
      ∀ i,scalarBound (cacheBits H B fuel prec) (tr i) := by
  have hH : H≤cacheBits H B fuel prec := by unfold cacheBits; omega
  have h0 : ratBits 0≤cacheBits H B fuel prec := by change 3≤_; unfold cacheBits; omega
  obtain ⟨t,run,out,capacity,_⟩ := materialize_run (fun x : ℚ => ratBits x≤cacheBits H B fuel prec)
    (fun x => ratBits x≤B) fuel prec n L mag m (fun j => (initial j).trans hH) h0 head sep limit scale
    input positive bits (rational_nativeSafe H B fuel prec) (fun i hi =>
      (numeratorWord_bits fuel prec (positive i hi)).trans (by unfold cacheBits; omega))
  obtain ⟨k,hk,tr,trace,tag,mem,safe⟩ := Fragment.run_halt run 0
  have actual : (tr (Fin.last k)).memory.index 60=m.index 60 := by rw [mem]; exact capacity
  exact ⟨k,hk,tr,trace,tag,mem ▸ out,actual,safe⟩

end MinorProxyCache
end Compression
end LinearProgramming
end Optimization
end OAI
