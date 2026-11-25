import OAI.Optimization.LinearProgramming.Compression.BinaryPublicEmit
import OAI.Optimization.LinearProgramming.NativePrice.PacketBits

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM OracleSpec OracleSpec.MinorLog

theorem components_fit_wire (q : ℚ) (k : ℕ) (len : (encodeRat q).length ≤ k) :
    q.num.natAbs < 2^k ∧ q.den < 2^k := by
  have w := (NativePrice.field_width q).trans len
  have fit (n : ℕ) (h : n.bits.length ≤ k) : n < 2^k :=
    (by simpa only [NativePrice.value_bits] using NativePrice.value_lt n.bits : n < 2^n.bits.length).trans_le
      (Nat.pow_le_pow_right (by decide) h)
  exact ⟨fit _ ((Nat.le_max_left _ _).trans w),fit _ ((Nat.le_max_right _ _).trans w)⟩

/-- Publish canonical integer components from a finite binary packet without recomputing
the affine expression that supplied them. Their public bit budget is the wire length. -/
def publishWireComponents : Block :=
  .seq (.op (.addrCopy 0 37)) (.seq canonicalRationalBitsBlock publicReplyBlock)

theorem publishWireComponents_spec (m : Memory ℚ) (q : ℚ) (k limit : ℕ)
    (hm : m.AllData (fun z=>ratBits z ≤ limit)) (len : m.index 37=k) (hl : 2*k+7 ≤ limit)
    (bound : (encodeRat q).length ≤ k) (num : m.data 0=(q.num:ℚ)) (den : m.data 1=(q.den:ℚ)) :
    ∃ s t, Block.Eval (Memory.AllData (fun z=>ratBits z ≤ limit)) publishWireComponents m s t ∧
      s ≤ 2*k*(16*k+17)+2*k*(16*k+18)+48*k+111 ∧ explicitValue (t.atPC 0) q := by
  let P := fun z : ℚ=>ratBits z ≤ limit
  let a := m.putIndex 0 (m.index 37)
  have prep := Block.Eval.op_addrCopy m 0 37 hm (hm.putIndex _ _)
  have fit := components_fit_wire q k bound
  have qp : (q.num:ℚ)/(q.den:ℚ)=q := Rat.num_div_den q
  have hp (v : ℤ) (hv : v.natAbs ≤ 2^(2*k+2)) : P (v:ℚ) :=
    (ratBits_signed_integer_of_le_pow v (2*k+2) hv).trans (by omega)
  have hq : P ((q.num:ℚ)/(q.den:ℚ)) := by
    rw [qp]; exact (NativePrice.ratBits_field q).trans (by omega)
  obtain ⟨s,u,run,cost,uk,v,sg,nb,db⟩ := canonicalRationalBitsBlock_spec a q.num q.den k prep.safe_end
    num den (by simpa [a] using len) q.pos fit.1 fit.2 hp hq
  rw [qp] at v sg nb db
  obtain ⟨l,t,pub,pc,out⟩ := publicReplyBlock_spec u q k run.safe_end uk fit ⟨v,sg,nb,db⟩
    (fun z h => (smallPublicationBits k z h).trans hl)
  exact ⟨_,t,prep.seq (run.seq pub),by omega,out⟩

end Compression
end LinearProgramming
end Optimization
end OAI
