import OAI.Computability.NearSquareRoot.InterchangeRadixSpace
import OAI.Computability.NearSquareRoot.BoundedProgramForget

/-! # The physical recursive interchange of two radix fields -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAddress.Request

open Filter IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic IntegerMultiplication.Loom NearSquareRoot.InterchangeFrame
  NearSquareRoot.Interchange NearSquareRoot.Interchange.StageKernel

/-- At the selected fixed radix and ground field, one recursive tape command
interchanges every pair of equal-width fields with bounded spectator radices,
including all inputs above the common payload-padding threshold. The selector
for the digit symbols is an arbitrary fixed injective representation. -/
theorem exists_radix_interchange {α : ℝ} (hα : 1/2 < α) (threshold : ℕ) :
    ∃ p b : ℕ, p.Prime ∧ 2 < p ∧ b.Prime ∧ threshold < b ∧
      ∀ digit : ZMod p → Tree, Function.Injective digit → ∃ k : ℕ,
        Sized (fun x : ThickRequest (b:=b) (Packed digit) k =>
            (x.val.recordVolume : ℝ) * (x.val.width : ℝ)^α)
          (fun x => (job b).issue x.val) (fun x => (job b).reply x.val) := by
  obtain ⟨p,b,hp,odd,hb,big,run⟩ := exists_bounded_radix_interchange hα threshold
  refine ⟨p,b,hp,odd,hb,big,fun digit inj => ?_⟩
  obtain ⟨k,tape⟩ := run digit inj
  have one (x : ThickRequest (b:=b) (Packed digit) k) :
      1 ≤ (x.val.recordVolume : ℝ) * (x.val.width : ℝ)^α := by
    have vol := (Nat.pow_pos (by decide : 0 < 2)).trans_le
      ((pow_digits_le x.val hb.two_le x.property.1.1).trans (rows_le_recordVolume _))
    exact one_le_mul_of_one_le_of_one_le (by exact_mod_cast vol)
      (Real.one_le_rpow (by exact_mod_cast x.property.1.2.1) (by linarith))
  refine ⟨k,one,_,tape.forget,3,fun x => ?_⟩
  have ceil := Nat.ceil_lt_add_one (a := (x.val.recordVolume : ℝ) * (x.val.width : ℝ)^α)
    (zero_le_one.trans (one x))
  simp only [Nat.cast_ofNat]
  linarith [one x]

end InterchangeAddress.Request

end NearSquareRoot
end Computability
end OAI
