import OAI.Hierarchy.ProtocolRAMBinarySpan

namespace OAI
/-! # A single sign-table exponent for every payload below the instance size -/

namespace Hierarchy.ProtocolRAMPurchaseSampler

theorem threshold_index {z cap payload n : Nat} (bounded : n≤ cap*payload) (width : payload≤2^z) :
    n<2^(z+bits cap) := by
  calc n≤ cap*payload := bounded
       _≤ cap*2^z := Nat.mul_le_mul_left cap width
       _<(span cap)*2^z := Nat.mul_lt_mul_of_pos_right (lt_span cap) (Nat.two_pow_pos _)
       _=2^(z+bits cap) := (Nat.mul_comm _ _).trans (Nat.pow_add 2 z (bits cap)).symm

theorem threshold_clip (z cap payload raw : Nat) (width : payload≤2^z) :
    min raw (cap*payload)<2^(z+bits cap) :=
  threshold_index (Nat.min_le_right ..) width

end Hierarchy.ProtocolRAMPurchaseSampler

end OAI
