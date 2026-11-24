import OAI.Computability.VPVNP.CompressionProcedure
import OAI.Computability.VPVNP.CompressionTemplates
import OAI.Computability.VPVNP.ShrinkStatePass

/-!
# Running a shrinking template at one scheduled degree

The template and scheduled degrees are fixed before the coefficient ring,
its parameter assignment, the network and the number of remaining lanes.
The exact shrinking pass has the position divisor and energy multiplier
required to compose one block of Theorem 7.1.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

theorem packingLaneBits_add (a g : ℕ) : packingLaneBits a 0 + g = packingLaneBits a g := by
  simp [packingLaneBits, Nat.add_assoc]

namespace BlockSchedule.Templates

open MotifConversion PackingData ShrinkEnergy ShrinkMotif

variable {k : Type*} [Field k] {S : BlockSchedule k}
variable (B : S.Templates) {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
variable (i : Fin S.steps)

/-- The additive coefficient for this degree transition, before choosing
any solution of the fixed scalar equations. -/
noncomputable def shrinkRoundingError : ℝ :=
  let d := 2 ^ S.degreeExponent i.castSucc
  let d' := 2 ^ S.degreeExponent i.succ
  let c := 2 * d + 1
  max 0 (roundingConstant d d' (pieceCount d c) shrinkComparison B.shrink.energyConstant
    (1 - shrinkLoss) (subdivisions d c d'))

/-- The actual pass at any input lane length equal to the scheduled one. -/
noncomputable def shrinkPassAt {g n : ℕ} (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n) : StatePass R X (S.degreeExponent i.succ) g := by
  subst n
  exact X.shrinkStatePass B.shrink (f ∘ Sum.inl) ((B.solution_iff f).mp hf).1 (S.shrink i)

theorem shrinkPassAt_positions {g n : ℕ} (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n) (z : (B.shrinkPassAt f hf i h X).step.Choice) :
    X.positions = packingFactor (S.degreeExponent i.castSucc) *
      ((B.shrinkPassAt f hf i h X).next z).positions := by
  subst n
  exact X.shrinkStatePass_positions B.shrink (S.shrink i) (f ∘ Sum.inl)
    ((B.solution_iff f).mp hf).1 z

theorem shrinkPassAt_energy {g n : ℕ} (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n) (z : (B.shrinkPassAt f hf i h X).step.Choice) :
    ((B.shrinkPassAt f hf i h X).next z).energy ≤
      shrinkMultiplier * X.energy + B.shrinkRoundingError i * (X.positions : ℝ) ^ 2 := by
  subst n
  have hz := X.shrinkStatePass_energy B.shrink (S.shrink i) (f ∘ Sum.inl)
    ((B.solution_iff f).mp hf).1 shrink_constants.2.2.1 (by norm_num [shrinkComparison]) z
  exact hz.trans (add_le_add_right (mul_le_mul_of_nonneg_right (le_max_right 0 _)
    (sq_nonneg (X.positions : ℝ))) _)

/-- An elementary scheduled shrinking procedure with the exact six-party
expansion in every term and the bounds of (7.2). -/
noncomputable def shrinkProcedure :
    Procedure R (S.degreeExponent i.castSucc) (S.degreeExponent i.succ)
      (packingLaneBits (S.degreeExponent i.castSucc) 0)
      (packingFactor (S.degreeExponent i.castSucc))
      shrinkMultiplier :=
  Procedure.ofPass (by unfold packingFactor; positivity) shrink_constants.2.2.2.2.2.1.le
    (le_max_left 0 _) (fun g X ↦ B.shrinkPassAt f hf i (packingLaneBits_add _ g) X)
    (fun g X ↦ B.shrinkPassAt_positions f hf i (packingLaneBits_add _ g) X)
    (fun g X ↦ B.shrinkPassAt_energy f hf i (packingLaneBits_add _ g) X)

/-- The same additive error works over every ring and for every solution. -/
@[simp] theorem shrinkProcedure_error : (B.shrinkProcedure f hf i).error =
    B.shrinkRoundingError i := rfl

end BlockSchedule.Templates
end Compression

end VPVNP
end Computability
end OAI
