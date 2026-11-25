import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Optimization.LinearProgramming.PriceGame.LearningConstraints

/-! Prefix-free binary records for one compact-skeleton comparison. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram

private abbrev CutTuple := ℕ × (ℕ × (ℚ × (Bool × Bool)))
private abbrev sideCode := prodCode Procedure.boolCode Procedure.boolCode
private abbrev tailCode := prodCode ratCode sideCode
private abbrev restCode := prodCode Nat.bits tailCode
private abbrev tupleCode := prodCode Nat.bits restCode

/-- Two side bits indicate respectively "less" and "greater"; equality clears both. -/
private def cutTuple {n : ℕ} (o : Observation n) : CutTuple :=
  (o.i.val, o.j.val, o.threshold, decide (o.side = .lt), decide (o.side = .gt))

def cutObservationCode (n : ℕ) (o : Observation n) : List Bool := tupleCode (cutTuple o)

theorem cutThreshold_length {n : ℕ} (o : Observation n) :
    (ratCode o.threshold).length ≤ (cutObservationCode n o).length := by
  simp only [cutObservationCode, tupleCode, restCode, tailCode, sideCode, prodCode,
    cutTuple, pairBits_length]
  omega

noncomputable def cutIndexIP (n : ℕ) : Procedure (cutObservationCode n) Nat.bits (fun o => o.i.val) :=
  (Procedure.first Nat.bits restCode).precompose cutTuple

private noncomputable def restP (n : ℕ) :
    Procedure (cutObservationCode n) restCode (fun o => (cutTuple o).2) :=
  (Procedure.second Nat.bits restCode).precompose cutTuple

noncomputable def cutIndexJP (n : ℕ) : Procedure (cutObservationCode n) Nat.bits (fun o => o.j.val) :=
  (Procedure.first Nat.bits tailCode).comp (restP n)

private noncomputable def tailP (n : ℕ) :
    Procedure (cutObservationCode n) tailCode (fun o => (cutTuple o).2.2) :=
  (Procedure.second Nat.bits tailCode).comp (restP n)

noncomputable def cutThresholdP (n : ℕ) :
    Procedure (cutObservationCode n) ratCode (fun o => o.threshold) :=
  (Procedure.first ratCode sideCode).comp (tailP n)

private noncomputable def sideP (n : ℕ) :
    Procedure (cutObservationCode n) sideCode (fun o => (cutTuple o).2.2.2) :=
  (Procedure.second ratCode sideCode).comp (tailP n)

noncomputable def cutLessP (n : ℕ) :
    Procedure (cutObservationCode n) Procedure.boolCode (fun o => decide (o.side = .lt)) :=
  (Procedure.first Procedure.boolCode Procedure.boolCode).comp (sideP n)

noncomputable def cutGreaterP (n : ℕ) :
    Procedure (cutObservationCode n) Procedure.boolCode (fun o => decide (o.side = .gt)) :=
  (Procedure.second Procedure.boolCode Procedure.boolCode).comp (sideP n)

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
