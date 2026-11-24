import OAI.Computability.VPVNP.CompressorInitialBoundary
import OAI.Computability.VPVNP.CompressorInitialTraceEquiv
import OAI.Computability.VPVNP.CompressorNativePassRates

/-! # A single communication rate for the selected chronological descriptor run -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ScheduledTrace

open BurstRAM Compression PairSimulation.LocalHistory

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- The initial four rows, one native pass rate for each of the fixed substeps,
and the final calendar call. This coefficient is fixed before the input length. -/
noncomputable def chronologicalRate (raw : ℕ) : ℕ :=
  2 * initialRate B + (S.steps+1) * nativePassRate (BlockProgram.script B) raw + 4

theorem chronological_charge (raw positions T n : ℕ) (positive : 0 < positions)
    (blocks : T ≤ n.log2+1) :
    initialRate B*(positions+1) + (T*(S.steps+1))*(nativePassRate (BlockProgram.script B) raw*positions)+4 ≤
      chronologicalRate B raw * positions * (n.log2+1) := by
  let L := n.log2+1
  have hL : 0 < L := Nat.succ_pos _
  have init : initialRate B*(positions+1) ≤ (2*initialRate B*positions)*L := calc
    _ ≤ initialRate B*(2*positions) := Nat.mul_le_mul_left _ (by omega)
    _ = 2*initialRate B*positions := by ring
    _ ≤ _ := Nat.le_mul_of_pos_right _ hL
  have repeatCharge := Nat.mul_le_mul_right ((S.steps+1)*(nativePassRate (BlockProgram.script B) raw*positions)) blocks
  have last : 4 ≤ 4*positions*L :=
    (Nat.le_mul_of_pos_right 4 positive).trans (Nat.le_mul_of_pos_right _ hL)
  unfold chronologicalRate
  change _ ≤ (2*initialRate B+(S.steps+1)*nativePassRate (BlockProgram.script B) raw+4)*positions*L
  change T*_ ≤ L*_ at repeatCharge
  calc
    _ = initialRate B*(positions+1) + T*((S.steps+1)*(nativePassRate (BlockProgram.script B) raw*positions)) + 4 := by ring
    _ ≤ 2*initialRate B*positions*L + L*((S.steps+1)*(nativePassRate (BlockProgram.script B) raw*positions)) + 4*positions*L :=
      Nat.add_le_add (Nat.add_le_add init repeatCharge) last
    _ = _ := by ring

variable {B} {R : Type*} [CommRing R] {f : B.Entry → R} {hf : B.IsSolution f}
variable {w base T cap small b l width n : ℕ} {pub : Fin 11 → Word w} {m : Memory w}
variable {X : State (S.degreeExponent 0) l} {a g : ℕ} {E : StateExecution R a g X}
variable {origin : PassOrigins B f hf E} {W : E.MapWitnesses f} {readers : ExecutionReaders E W}
variable {resident : Resident B f hf w} {pitch : Word w} {total : ℕ} {past : List (SelectedLevel B f hf)}

/-- Charge the reports of the initial native interval and the recursive
scheduled result on this same branch. Repeated passes appear with their
multiplicity in the budget carried by the result. -/
theorem InitialInterval.chronologicalRate_le (raw : ℕ)
    (init : InitialInterval B base X.positions T cap small b l width pub m)
    (cursor : BlockStartupPrefix.Resident (BlockProgram.layout B base X.positions T) (S.degreeExponent 0)
      b l width n (pub 2) m X)
    (result : Result resident pub pitch total cap small
      (T*(S.steps+1)*(nativePassRate (BlockProgram.script B) raw*X.positions)+4)
      E origin W readers past init.interval.segment.state init.interval.segment.memory)
    (blocks : T ≤ n.log2+1) (z : E.Choices) :
    RAMBuckets.cost Report.probes (init.interval.combinedCore result.trace result.source z).logs ≤
      chronologicalRate B raw * X.positions * (n.log2+1) := by
  rw [init.interval.combinedCost]
  exact (Nat.add_le_add (init.rate cursor) (result.cost z)).trans (by
    simpa only [Nat.add_assoc] using chronological_charge B raw X.positions T n X.positions_pos blocks)

end CompressorRecords.ScheduledTrace

end VPVNP
end Computability
end OAI
