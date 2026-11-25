import OAI.Optimization.LinearProgramming.BitRAM.NativePriceRange
import OAI.Optimization.LinearProgramming.Compression.MetadataNat
import OAI.Optimization.LinearProgramming.OracleSpec.PriceGame

/-! Native emission of the exact three public fields of one price-game epoch. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace PriceEpoch
open RAM OracleSpec Compression.Inner.Metadata

/-- Physical index 72 is the dimension, index 74 the zero-based anchor, and index 8
the range exponent computed by the preceding numerical bounds block. -/
def fields : Block := .seq (writeNatFrom 72) (.seq rangeField (writeNatFrom 74))

def fieldsTime (n b : Nat) := 2*((n+1)*(5*n+25)+5)+10*b+18

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K→Prop}

theorem fields_correct {n : Nat} (anchor : Fin n) (b : Nat) (s : Memory K) (safe : s.AllData P) (ready : Ready s)
    (dim : s.index 72=n) (mark : s.index 74=anchor.val) (width : s.index 8=b) :
    ∃ t k, Block.Eval (Memory.AllData P) fields s k t ∧ k≤fieldsTime n b ∧
      Effect s t (priceInput (2^(1+b)) anchor) := by
  obtain ⟨a,j,num,jb,hN⟩ := writeNatFrom_correct s 72 n safe ready dim
  have av : a.index 8=b := (hN.frame 8 (by decide) (by decide) (by decide) (by decide)).trans width
  obtain ⟨u,l,bound,lb,hr⟩ := rangeField_correct b a num.safe_end (ready.after hN) av
  have uv : u.index 74=anchor.val := (hr.frame 74 (by decide) (by decide) (by decide) (by decide)).trans
    ((hN.frame 74 (by decide) (by decide) (by decide) (by decide)).trans mark)
  obtain ⟨t,h,last,hb,hm⟩ := writeNatFrom_correct u 74 anchor.val bound.safe_end ((ready.after hN).after hr) uv
  have aN := anchor.isLt
  have grow := Nat.mul_le_mul (show anchor.val+1 ≤ n+1 by omega) (show 5*anchor.val+25 ≤ 5*n+25 by omega)
  refine ⟨t,_,num.seq (bound.seq last),?_,?_⟩
  · unfold fieldsTime
    omega
  · simpa only [priceInput,Nat.add_comm 1 b,List.append_assoc] using hN.append (hr.append hm)

theorem word_length {n : Nat} (anchor : Fin n) (b : Nat) :
    (priceInput (2^(1+b)) anchor).length ≤ 4*n+2*b+7 := by
  have nBits : n.size≤n := Nat.size_le.mpr (Nat.lt_two_pow_self (n := n))
  have aBits : anchor.val.size≤anchor.val := Nat.size_le.mpr (Nat.lt_two_pow_self (n := anchor.val))
  have less := anchor.isLt
  simp only [priceInput,List.length_append,Nat.add_comm 1 b]
  rw [Contraction.nativeRange_encode_length]
  simp only [OracleSpec.encodeNat_length]
  omega

end PriceEpoch
end BitRAM
end LinearProgramming
end Optimization
end OAI
