import OAI.Computability.BorderVNP.StackFrameCodec
import OAI.Computability.BorderVNP.CoverMotionProgram

/-! # Public integer divisions for shortening pools

The divisors in a direction pool and a matched block are fixed constants. Compile the actual
stack division procedure into a shared Boolean circuit on the same most-significant-bit-first
words as the public sort, including zero input and words of length zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

open StackFrame ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork
open RationalHitting RationalHitting.StackLanguage

/-- A polynomial-size Boolean DAG computing Euclidean division by a fixed positive constant. -/
theorem fixed_division_frames (d : ℕ) (hd : 0 < d) :
    ∃ C e : ℕ, ∀ w, ∃ f : Frame (Fin w) (Fin w),
      f.size ≤ C*(w+1)^e ∧ ∀ x, value (f.eval x) = value x / d := by
  let m : {a : ℕ // 0 < a} := ⟨d,hd⟩
  have hpair : Poly (fun x : ℕ => (x,m)) := StackLanguage.Poly.id.pair (StackLanguage.Poly.const m)
  have h : Poly (fun x : ℕ => x / d) := Cover.Frame.quotient_poly.comp hpair
  obtain ⟨p⟩ := h
  obtain ⟨c,hc⟩ := programFrame_size p.program p.input p.output
  let budget : TimeBound := 12*TimeBound.variable^2 +
    .const c * (TimeBound.variable + p.bound + 3)^2
  obtain ⟨C,e,_,_,hg⟩ := budget.growth
  refine ⟨C,e,fun w => ?_⟩
  let run := programFrame p.program p.input p.output w (p.bound.eval (w+1))
  let result := (natDecodeFrame w).subst (run.subst (natEncodeFrame w))
  refine ⟨result,?_,fun x => ?_⟩
  · have hcodec : (natEncodeFrame w).size ≤ 12*(w+1)^2 := (natEncodeFrame_size w).trans (by nlinarith)
    have hcost := hc w (p.bound.eval (w+1))
    simp only [result,Frame.subst_size,natDecodeFrame_size,add_zero]
    apply (Nat.add_le_add hcodec hcost).trans
    calc
      _ ≤ 12*(w+1)^2 + c*((w+1) + p.bound.eval (w+1) + 3)^2 := by gcongr; omega
      _ ≤ _ := by simpa [budget] using hg (w+1) (by omega)
  · have hl : (value x).bits.length ≤ w := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr (value_lt x)
    obtain ⟨t,ht,he⟩ := p.correct (value x)
    have hlen : (code (value x)).length + 1 ≤ w+1 := Nat.add_le_add_right hl 1
    have hrun := programFrame_correct p.program p.input p.output he (W := w) hl
      (ht.trans (p.bound.monotone hlen))
    have hr : (run.subst (natEncodeFrame w)).eval x = padded w (value x / d).bits := by
      funext j
      rw [Frame.subst_eval, natEncodeFrame_correct]
      exact congrFun hrun j
    let q : Fin (2^w) := ⟨value x / d, (Nat.div_le_self _ _).trans_lt (value_lt x)⟩
    have heq : result.eval x = (numberWords w).symm q := by
      funext j
      rw [show result.eval x j = (natDecodeFrame w).eval ((run.subst (natEncodeFrame w)).eval x) j
        by simp only [result, Frame.subst_eval], hr]
      exact congrFun (natDecodeFrame_correct q) j
    rw [heq,value_encode]

end Packing

end BorderVNP
end Computability
end OAI
