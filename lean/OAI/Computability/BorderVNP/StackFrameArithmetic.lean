import OAI.Computability.BorderVNP.CrossingParallelFrame
import OAI.Computability.BorderVNP.StackFrameCodec
import OAI.Computability.BorderVNP.StackFramePairCode
import OAI.Computability.RationalHitting.Feasibility

/-!
# Compiling binary arithmetic on fixed-width numerical words

Both operand words are serialized and joined by the stack language's escaped
pair encoding. The result of the fixed stack program is read in big-endian
order. This construction preserves the full product, including carries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackFrame

open RationalHitting RationalHitting.StackLanguage
open VPVNP.VerifierNetwork (Frame)
open ParseBatchSort ParseBatchCounts

/-- Wire both operands from numerical inputs into one escaped binary pair. -/
noncomputable def numericPairFrame (w W : ℕ) : Frame (Fin w ⊕ Fin w) (Slots W) :=
  (pairCodeFrame w w W).subst (Crossing.parallelFrame
    ((natEncodeFrame w).subst (Frame.initial Sum.inl))
    ((natEncodeFrame w).subst (Frame.initial Sum.inr)))

/-- Numeric pairing produces exactly the pair accepted by the arithmetic programs. -/
theorem numericPairFrame_correct {w : ℕ} (W : ℕ) (x y : Fin w → Bool) :
    (numericPairFrame w W).eval (Sum.elim x y) =
      padded W (pairCode Nat.bits Nat.bits (value x,value y)) := by
  let a := (value x).bits
  let b := (value y).bits
  have hx : (Frame.initial Sum.inl).eval (Sum.elim x y) = x := funext fun _ => by simp
  have hy : (Frame.initial Sum.inr).eval (Sum.elim x y) = y := funext fun _ => by simp
  have hp : (Crossing.parallelFrame ((natEncodeFrame w).subst (Frame.initial Sum.inl))
      ((natEncodeFrame w).subst (Frame.initial Sum.inr))).eval (Sum.elim x y) =
      Sum.elim (padded w a) (padded w b) := by
    funext i
    cases i <;> simp only [Crossing.parallelFrame_eval_inl, Crossing.parallelFrame_eval_inr,
      Frame.subst_eval, hx, hy, natEncodeFrame_correct, Sum.elim_inl, Sum.elim_inr, a, b]
  funext i
  rw [numericPairFrame, Frame.subst_eval, hp]
  exact congrFun (pairCodeFrame_correct (Wout := W) a b
    ((Nat.size_eq_bits_len _).symm ▸ Nat.size_le.mpr (value_lt x))
    ((Nat.size_eq_bits_len _).symm ▸ Nat.size_le.mpr (value_lt y))) i

/-- Serialization and pairing together cost at most quadratically many gates. -/
theorem numericPairFrame_size (w W : ℕ) :
    (numericPairFrame w W).size ≤ 24*w*(w+1) + 30*W*(w+1) := by
  simp only [numericPairFrame, Frame.subst_size, Crossing.parallelFrame_size,
    Frame.initial_size, zero_add]
  have h := natEncodeFrame_size w
  have hp := pairCodeFrame_size w w W
  nlinarith only [h,hp]

/-- A fixed two-input binary stack procedure becomes a polynomial-size
numerical Boolean frame when its answer fits the output word. -/
theorem binaryProcedureFrames {op : ℕ × ℕ → ℕ}
    (p : Procedure (pairCode Nat.bits Nat.bits) Nat.bits op)
    (fits : ∀ (w : ℕ) (x y : Fin w → Bool), op (value x,value y) < 2^(2*w)) :
    ∃ C e : ℕ, ∀ w : ℕ, ∃ f : Frame (Fin w ⊕ Fin w) (Fin (2*w)),
      f.size ≤ C*(w+1)^e ∧ ∀ x y : Fin w → Bool,
        value (f.eval (Sum.elim x y)) = op (value x,value y) := by
  obtain ⟨c,hc⟩ := programFrame_size p.program p.input p.output
  let wb : TimeBound := 3*TimeBound.variable
  let budget : TimeBound := 114*TimeBound.variable^2 +
    .const c * (wb + p.bound.comp wb + 3)^2
  obtain ⟨C,e,_,_,hg⟩ := budget.growth
  refine ⟨C,e,?_⟩
  intro w
  let W := 3*(w+1)
  let f := programFrame p.program p.input p.output W (p.bound.eval W)
  let out : Slots (2*w) → Slots W := fun i => (i.1.castLE (by dsimp [W]; omega), i.2)
  refine ⟨(natDecodeFrame (2*w)).subst ((f.select out).subst (numericPairFrame w W)), ?_, ?_⟩
  · simp only [Frame.subst_size, Frame.select_size, natDecodeFrame_size, Nat.add_zero]
    have hp := numericPairFrame_size w W
    have hsum : (numericPairFrame w W).size ≤ 114*(w+1)^2 := by dsimp [W] at hp; nlinarith
    apply (Nat.add_le_add hsum (hc W (p.bound.eval W))).trans
    simpa only [budget,wb,W,TimeBound.eval_add,TimeBound.eval_mul,TimeBound.eval_pow,
      TimeBound.eval_variable,TimeBound.eval_numeral,TimeBound.eval_const,TimeBound.eval_comp]
      using hg (w+1) (by omega)
  · intro x y
    let pair := (value x,value y)
    have hx : (value x).bits.length ≤ w := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr (value_lt x)
    have hy : (value y).bits.length ≤ w := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr (value_lt y)
    have hpair : (pairCode Nat.bits Nat.bits pair).length+1 ≤ W := by
      simp only [pair,pairCode_length,W]; omega
    obtain ⟨t,ht,he⟩ := p.correct pair
    have sim := programFrame_correct p.program p.input p.output he (W := W)
      (by omega) (ht.trans (p.bound.monotone hpair))
    have hout : ((f.select out).subst (numericPairFrame w W)).eval (Sum.elim x y) =
        padded (2*w) (op pair).bits := by
      funext i
      rw [Frame.subst_eval, Frame.select_eval, numericPairFrame_correct]
      exact congrFun sim (out i)
    let result : Fin (2^(2*w)) := ⟨op pair,fits w x y⟩
    have hd := natDecodeFrame_correct result
    have hn : ((natDecodeFrame (2*w)).subst ((f.select out).subst (numericPairFrame w W))).eval
        (Sum.elim x y) = (numberWords (2*w)).symm result := by
      funext j
      rw [Frame.subst_eval,hout]
      exact congrFun hd j
    rw [hn, value_encode]

/-- An exact full-width product of two numerical words computed by a shared
Boolean frame of polynomial size, uniformly in the input word width. -/
theorem multiplicationFrames :
    ∃ C e : ℕ, ∀ w : ℕ, ∃ f : Frame (Fin w ⊕ Fin w) (Fin (2*w)),
      f.size ≤ C*(w+1)^e ∧ ∀ x y : Fin w → Bool,
        value (f.eval (Sum.elim x y)) = value x * value y := by
  apply binaryProcedureFrames Procedure.binaryMul
  intro w x y
  rw [two_mul,pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (value_lt x) (value_lt y)

end StackFrame

end BorderVNP
end Computability
end OAI
