import OAI.Optimization.LinearProgramming.RAM.Basic

/-! The arithmetic oracle model for §9. The ordinary instructions are precisely the finite
RAM instructions. An additional instruction sends a block of scalar registers, copies the
answer to another block and stores its length in an address register. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Contract

open RAM

abbrev History (K : Type*) := List (List K × List K)
abbrev ScalarOracle (K : Type*) := History K → List K → List K

inductive OracleInstr where
  | core (instr : Instr)
  | query (sendBase sendLength receiveBase receiveLength : ℕ)

abbrev OracleProgram := List OracleInstr

structure Config (K : Type*) where
  state : State K
  history : History K

/-- The history is accessible to the oracle alone. A call costs one plus the number of
scalar words transferred in each direction, including words the calling program discards. -/
def oracleStep {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : OracleProgram) (o : ScalarOracle K) (c : Config K) : Option (ℕ × Config K) := do
  let s := c.state
  guard s.output.isNone
  let instr : OracleInstr ← (p : List OracleInstr)[s.pc]?
  match instr with
  | .core i =>
    let t ← execInstr i s
    return (1, ⟨t, c.history⟩)
  | .query src len dst size =>
    let q := List.ofFn fun j : Fin (s.index len) => s.data (s.index src + j.val)
    let a := o c.history q
    let base := s.index dst
    let next : State K :=
      { s with
        pc := s.pc + 1
        index := Function.update s.index size a.length
        data := fun j => if base ≤ j then a[j-base]?.getD (s.data j) else s.data j }
    return (1 + q.length + a.length, ⟨next, (q, a) :: c.history⟩)

inductive OracleRun {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : OracleProgram) (o : ScalarOracle K) : Config K → ℕ → Config K → Prop where
  | refl (s) : OracleRun p o s 0 s
  | next {s t u cost more} : oracleStep p o s = some (cost,t) → OracleRun p o t more u →
      OracleRun p o s (cost + more) u

def OracleProgram.ComputesWithin {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : OracleProgram) (o : ScalarOracle K) (dimensions : List ℕ) (input : List K)
    (budget : ℕ) (post : History K → State K → Prop) : Prop :=
  ∃ elapsed final, OracleRun p o ⟨start dimensions input, []⟩ elapsed final ∧
    elapsed ≤ budget ∧ final.state.output.isSome ∧ post final.history final.state

end Contract
end LinearProgramming
end Optimization
end OAI
