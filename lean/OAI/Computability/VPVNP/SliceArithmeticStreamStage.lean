import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-!
# Staging the persistent streams of a Horner round

A fixed control copies the advised modulus, the multiplier and the row count
into the three consumable input stacks of the coefficient scan. All three
source stacks remain available for the next Horner digit.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace SliceArithmetic.StreamStage

open RAMTape RAMTape.SuccessorFields

/-- Ports for saved and consumable copies of the reduction coefficients, multiplier, and row
count, plus copy scratch space. -/
inductive Port where
  | coefficient | factor | count
  | coefficientInput | factorInput | countInput | scratch
  deriving DecidableEq

/-- Three order-preserving copies into empty stacks. -/
def stage : FiniteRoutine Port :=
  ((prependCopy .coefficient .coefficientInput .scratch).followedBy
    (prependCopy .factor .factorInput .scratch)).followedBy
    (prependCopy .count .countInput .scratch)

/-- State of the three saved streams and their three consumable input stacks for one Horner
round. -/
def frame (c b n ci bi ni : List Bool) : Stacks Port
  | .coefficient => c
  | .factor => b
  | .count => n
  | .coefficientInput => ci
  | .factorInput => bi
  | .countInput => ni
  | .scratch => []

theorem stage_runs (c b n : List Bool) :
    stage.Runs (5 * (c.length + b.length + n.length) + 6)
      (frame c b n [] [] []) (frame c b n c b n) := by
  let s := frame c b n [] [] []
  have hc := prependCopy_runs .coefficient .coefficientInput .scratch
    (by decide) (by decide) (by decide) s rfl
  have hb := prependCopy_runs .factor .factorInput .scratch
    (by decide) (by decide) (by decide) (frame c b n c [] []) rfl
  have hn := prependCopy_runs .count .countInput .scratch
    (by decide) (by decide) (by decide) (frame c b n c b []) rfl
  have h₁ : Function.update s .coefficientInput (s .coefficient ++ s .coefficientInput) =
      frame c b n c [] [] := by funext i; cases i <;> simp [s, frame, Function.update]
  have h₂ : Function.update (frame c b n c [] []) .factorInput (b ++ []) =
      frame c b n c b [] := by funext i; cases i <;> simp [frame, Function.update]
  have h₃ : Function.update (frame c b n c b []) .countInput (n ++ []) =
      frame c b n c b n := by funext i; cases i <;> simp [frame, Function.update]
  rw [h₁] at hc
  change (prependCopy ..).Runs (5 * b.length + 2) _ (Function.update _ _ (b ++ [])) at hb
  change (prependCopy ..).Runs (5 * n.length + 2) _ (Function.update _ _ (n ++ [])) at hn
  rw [h₂] at hb
  rw [h₃] at hn
  rw [show 5 * (c.length + b.length + n.length) + 6 =
    (5 * c.length + 2 + (5 * b.length + 2)) + (5 * n.length + 2) by omega]
  exact (hc.followedBy hb).followedBy hn

end SliceArithmetic.StreamStage

end VPVNP
end Computability
end OAI
