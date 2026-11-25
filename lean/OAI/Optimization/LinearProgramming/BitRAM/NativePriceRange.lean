import OAI.Optimization.LinearProgramming.Compression.MetadataRepeat
import OAI.Optimization.LinearProgramming.Contraction.DyadicRange

/-! Emit the price-game's potentially exponential natural range using only its
polynomially bounded binary exponent. Each loop iteration emits a pair of scalar bits. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace PriceEpoch
open RAM OracleSpec Compression.Inner.Metadata

/-- A fixed finite literal compiles to real scalar-bit stores. -/
def literal : Word → Block
  | [] => .skip
  | b::bs => .seq (emit b) (literal bs)

/-- Address 8 holds the length parameter `b`. -/
def rangeField : Block := .seq (literal [true,false])
  (.seq (repeatPairFrom 8 false) (literal [true,true,false]))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K→Prop}

theorem literal_correct (word : Word) (s : Memory K) (safe : s.AllData P) (ready : Ready s) :
    ∃ t, Block.Eval (Memory.AllData P) (literal word) s (3*word.length) t ∧ Effect s t word := by
  induction word generalizing s with
  | nil => exact ⟨s,.skip safe,Effect.refl _⟩
  | cons bit tail ih =>
    obtain ⟨a,first,e,_⟩ := emit_correct s bit safe ready
    obtain ⟨t,rest,f⟩ := ih a first.safe_end (ready.after e)
    refine ⟨t,?_,e.append f⟩
    rw [List.length_cons,show 3*(tail.length+1)=3+3*tail.length by omega]
    exact first.seq rest

theorem rangeField_correct (b : Nat) (s : Memory K) (safe : s.AllData P) (ready : Ready s)
    (width : s.index 8=b) :
    ∃ t k, Block.Eval (Memory.AllData P) rangeField s k t ∧ k≤10*b+18 ∧
      Effect s t (encodeNat (2^(b+1))) := by
  obtain ⟨a,first,e⟩ := literal_correct [true,false] s safe ready
  have h8 : a.index 8=b := (e.frame _ (by decide) (by decide) (by decide) (by decide)).trans width
  obtain ⟨d,k,mid,hm,f⟩ := repeatPairFrom_correct 8 false b a first.safe_end (ready.after e) h8
  obtain ⟨t,last,g⟩ := literal_correct [true,true,false] d mid.safe_end ((ready.after e).after f)
  refine ⟨t,_,first.seq (mid.seq last),?_,?_⟩
  · change 6+(k+9)≤10*b+18
    omega
  · rw [Contraction.nativeRange_encode,List.replicate_succ,List.flatten_cons]
    exact e.append (f.append g)

end PriceEpoch
end BitRAM
end LinearProgramming
end Optimization
end OAI
