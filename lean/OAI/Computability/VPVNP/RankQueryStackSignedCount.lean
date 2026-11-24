import OAI.Computability.VPVNP.RankQueryStackSignedScalar
import OAI.Computability.VPVNP.RankQueryStackNativeFrames
import OAI.Computability.VPVNP.SliceArithmeticSignedCount
import OAI.Computability.VPVNP.UniversalCountStackBounds

/-!
# Feeding an integer equation coefficient to the native rank-query stack

The two counted Boolean circuits return the positive and negative parts of
the coefficient. Their little-endian counter words supply a fixed stack
routine that returns the actual integer cast in the advised scalar ring.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Scalar

open SliceArithmetic RAMTape SliceArithmeticSignedCount

theorem signedCount_runs {p e w : ℕ} [Fact p.Prime] [NeZero e]
    (hw : Word.workingWidth p ≤ w) (c : Vector p e) (z : ℤ) (positive negative suffix : List Bool)
    (hsigned : (TapeWord.value positive : ℤ) - (TapeWord.value negative : ℤ) = z) :
    ∃ t ≤ callCap positive.length negative.length e w, machine.Runs t
      (clean (external p e w positive negative suffix))
      (clean (external p e w positive negative (Engine.scalar w (z : Scalar c) ++ suffix))) := by
  let a : Fin p := difference p positive negative
  have hcast : pack c (scale a (one p e)) = (z : Scalar c) := by
    simpa only [a, difference, hsigned] using pack_signed_counts c (TapeWord.value positive) (TapeWord.value negative)
  have hbits : Engine.scalar w (z : Scalar c) =
      BurstRAM.wordBits (Word.limb w a) ++ List.replicate ((e-1)*w) false := by
    rw [← hcast, Engine.scalar, digits_pack]
    exact packed_scale_one (NeZero.pos e) w a
  rw [hbits]
  exact machine_runs (NeZero.pos e) hw positive negative suffix

/-- Every intermediate stack fits within the input lengths plus the
polynomial time bound of this coefficient conversion. -/
theorem signedCount_spaceRun {p e w : ℕ} [Fact p.Prime] [NeZero e]
    (hw : Word.workingWidth p ≤ w) (c : Vector p e) (z : ℤ) (positive negative suffix : List Bool)
    (hsigned : (TapeWord.value positive : ℤ) - (TapeWord.value negative : ℤ) = z) :
    let cap := callCap positive.length negative.length e w
    let space := positive.length + negative.length + suffix.length + e + w + cap
    ∃ t ≤ cap, UniversalCountStack.SpaceRun machine.body.standalone space t (some machine.body.entry)
      (clean (external p e w positive negative suffix)) none
      (clean (external p e w positive negative (Engine.scalar w (z : Scalar c) ++ suffix))) := by
  intro cap space
  obtain ⟨t, ht, run⟩ := signedCount_runs hw c z positive negative suffix hsigned
  refine ⟨t, ht, UniversalCountStack.spaceRun_of_steps run ?_⟩
  rintro (i|i)
  · cases i with
    | divide j => cases j <;> simp [clean, frame, space, cap] <;> omega
    | _ => simp [clean, frame, space, cap]; omega
  · cases i <;> simp [clean, frame, external, space, cap] <;> omega

end RankQuery.Stack.Scalar

end VPVNP
end Computability
end OAI
