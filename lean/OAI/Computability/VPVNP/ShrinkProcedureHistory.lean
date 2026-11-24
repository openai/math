import OAI.Computability.VPVNP.ShrinkProcedure
import OAI.Computability.VPVNP.ShrinkStateHistory
import OAI.Computability.VPVNP.CompressionProcedureHistory

/-!
# Local record bounds for a scheduled shrinking procedure

A scheduled shrinking step has the same fixed six-party template at every
remaining lane count. Transporting the lane length to the format of the
dyadic state pass preserves its chosen records and their bounds. Thus the
one-step history factor can be fixed before selecting the coefficient ring
or any solution of the template equations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.BlockSchedule.Templates

variable {k : Type*} [Field k] {S : BlockSchedule k}
variable (B : S.Templates) {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
variable (i : Fin S.steps)

/-- At the scheduled lane length, use all actual slot and resident motif
records of the selected dyadic state pass. -/
private noncomputable def recordsAt {g n : ℕ}
    (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n) : (B.shrinkPassAt f hf i h X).Records := by
  subst n
  let hshrink := ((B.solution_iff f).mp hf).1
  exact (X.shrinkStatePass B.shrink (f ∘ Sum.inl) hshrink (S.shrink i)).slotRecords
    (X.shrinkExtraRecords B.shrink (f ∘ Sum.inl) hshrink (S.shrink i))

private theorem boundedAt {g n : ℕ} (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n) :
    (B.shrinkPassAt f hf i h X).Bounded (B.recordsAt f hf i h X)
      (State.shrinkHistoryFactor B.shrink (S.degreeExponent i.castSucc)
        (S.degreeExponent i.succ)) := by
  subst n
  exact X.shrinkStatePass_bounded B.shrink (f ∘ Sum.inl) ((B.solution_iff f).mp hf).1 (S.shrink i)

/-- Every branch of the scheduled shrinking procedure has one substep and
satisfies the fixed history factor for its two degree exponents. -/
noncomputable def shrinkProcedureRecords :
    (B.shrinkProcedure f hf i).RecordBounds
      (State.shrinkHistoryFactor B.shrink (S.degreeExponent i.castSucc)
        (S.degreeExponent i.succ)) 1 :=
  Procedure.RecordBounds.ofPass _ _ _ _ _ _
    (fun g X ↦ B.recordsAt f hf i (packingLaneBits_add _ g) X)
    (fun g X ↦ B.boundedAt f hf i (packingLaneBits_add _ g) X)

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
