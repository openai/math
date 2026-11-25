import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Optimization.LinearProgramming.OracleSpec.BitStackDeployment

/-! Literal, polynomial-time bit-stack programs for a Bellman candidate and the
lexicographic selection used in the residual-network longest-path table. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace GridMachine
open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

/-- The first coordinate is the integer-scaled score. The second counts the used arcs. -/
abbrev Key := ℤ × ℤ
def keyCode : Key → List Bool := prodCode intCode intCode

def nextKey (input : Key × ℤ) : Key := (input.1.1+input.2, input.1.2+1)

def improves (p : Key × Key) : Bool :=
  decide (p.1.1 < p.2.1 ∨ p.1.1 = p.2.1 ∧ p.2.2 < p.1.2)

/-- Add the current arc weight and increment the path length by one using certified integer
procedures. Both operations run as instructions of the finite bit-stack program. -/
noncomputable def nextKeyProgram : Procedure (prodCode keyCode intCode) keyCode nextKey := by
  let p := first keyCode intCode
  let edge := second keyCode intCode
  let score := (first intCode intCode).comp p
  let len := (second intCode intCode).comp p
  let one := constant (prodCode keyCode intCode) intCode (1 : ℤ)
  exact ((intAdd.comp (score.pair edge)).pair (intAdd.comp (len.pair one))).congrFun (fun _ => rfl)

/-- Compare the scaled scores and then the lengths in reverse order. -/
noncomputable def improvesProgram : Procedure (prodCode keyCode keyCode) boolCode improves := by
  let p := first keyCode keyCode
  let q := second keyCode keyCode
  let score := first intCode intCode
  let length := second intCode intCode
  let better := OracleSpec.Arithmetic.intLt.comp ((score.comp p).pair (score.comp q))
  let worse := OracleSpec.Arithmetic.intLt.comp ((score.comp q).pair (score.comp p))
  let shorter := OracleSpec.Arithmetic.intLt.comp ((length.comp q).pair (length.comp p))
  let tie := boolAnd.comp ((boolNot.comp worse).pair shorter)
  apply (boolOr.comp (better.pair tie)).congrFun
  intro z
  change (decide (z.1.1 < z.2.1) || (!decide (z.2.1 < z.1.1) && decide (z.2.2 < z.1.2))) = _
  by_cases h : z.1.1 < z.2.1
  · simp [improves, h]
  · by_cases eq : z.1.1 = z.2.1
    · simp [improves, eq]
    · have rev : z.2.1 < z.1.1 := by omega
      simp [improves, h, eq, rev]

/-- Copy the winning entire item so its route or backpointer is preserved. -/
def winner {α : Type} (z : (Key × α) × (Key × α)) : Key × α :=
  if improves (z.1.1,z.2.1) then z.2 else z.1

noncomputable def winnerProgram {α : Type} (payload : α → List Bool) :
    Procedure (prodCode (prodCode keyCode payload) (prodCode keyCode payload))
      (prodCode keyCode payload) winner := by
  let item := prodCode keyCode payload
  let p := first item item
  let q := second item item
  let readKey := first keyCode payload
  let test := improvesProgram.comp ((readKey.comp p).pair (readKey.comp q))
  exact (conditional test q p).congrFun (fun _ => rfl)

theorem nextKey_deploy (o : OracleSpec.WordOracle) (x : Key × ℤ) :
    (OracleSpec.BitCode.deploy nextKeyProgram).ComputesWithin o (prodCode keyCode intCode x)
      (3*nextKeyProgram.bound.eval (prodCode keyCode intCode x).length +
        2*(prodCode keyCode intCode x).length+2)
      (fun history bits => history = [] ∧ bits = keyCode (nextKey x)) :=
  OracleSpec.BitCode.deploy_correct nextKeyProgram o x

theorem winner_deploy {α : Type} (payload : α → List Bool) (o : OracleSpec.WordOracle)
    (x : (Key × α) × (Key × α)) :
    let input := prodCode (prodCode keyCode payload) (prodCode keyCode payload) x
    let p := winnerProgram payload
    (OracleSpec.BitCode.deploy p).ComputesWithin o input
      (3*p.bound.eval input.length+2*input.length+2)
      (fun history bits => history = [] ∧ bits = prodCode keyCode payload (winner x)) :=
  OracleSpec.BitCode.deploy_correct (winnerProgram payload) o x


private theorem foldWinner_mem {α : Type} (xs : List (Key × α)) (init : Key × α) :
    xs.foldl (fun b a => winner (b,a)) init = init ∨
      xs.foldl (fun b a => winner (b,a)) init ∈ xs := by
  induction xs generalizing init with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    change xs.foldl _ (winner (init,x)) = init ∨ xs.foldl _ (winner (init,x)) ∈ x :: xs
    rcases ih (winner (init,x)) with h | h
    · rw [h]
      unfold winner
      split <;> simp
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- Select from an entire serialized row. The current best is always an input item, so the
fold carries an item whose encoded length is bounded by the incoming row and initial value. -/
noncomputable def foldWinnerProgram {α : Type} (payload : α → List Bool) (d : α) :
    Procedure (prodCode (listCode (prodCode keyCode payload)) (prodCode keyCode payload))
      (prodCode keyCode payload) (fun z => z.1.foldl (fun b a => winner (b,a)) z.2) := by
  let item := prodCode keyCode payload
  let step := (winnerProgram payload).comp (swap item item)
  refine (foldList (ea := item) (eb := item) (((0,0),d) : Key × α) step Polynomial.X ?_).congrFun
    (fun _ => rfl)
  intro xs z i
  change (item ((xs.take i).foldl (fun b a => winner (b,a)) z)).length ≤
    Polynomial.X.eval ((listCode item xs).length + (item z).length)
  simp only [Polynomial.eval_X]
  rcases foldWinner_mem (xs.take i) z with h | h
  · rw [h]; omega
  · exact (code_le_of_mem item (List.mem_of_mem_take h)).trans (by omega)

def candidate {α : Type} (p : (Key × ℤ) × α) : Key × α := (nextKey p.1, p.2)

noncomputable def candidateProgram {α : Type} (payload : α → List Bool) :
    Procedure (prodCode (prodCode keyCode intCode) payload) (prodCode keyCode payload) candidate :=
  ((nextKeyProgram.comp (first (prodCode keyCode intCode) payload)).pair
    (second (prodCode keyCode intCode) payload)).congrFun (fun _ => rfl)

/-- One complete row of numeric relaxations, preserving each candidate's backpointer.
Inputs are the previous key, arc cost, and backpointer for each outgoing arc. -/
def relaxRow {α : Type} (z : List ((Key × ℤ) × α) × (Key × α)) : Key × α :=
  (z.1.map candidate).foldl (fun best next => winner (best,next)) z.2

noncomputable def relaxRowProgram {α : Type} (payload : α → List Bool) (d : α) :
    Procedure (prodCode (listCode (prodCode (prodCode keyCode intCode) payload)) (prodCode keyCode payload))
      (prodCode keyCode payload) relaxRow := by
  let source := prodCode (prodCode keyCode intCode) payload
  let item := prodCode keyCode payload
  let edges := first (listCode source) item
  let start := second (listCode source) item
  let extended := (listMap (((0,0),0),d) ((0,0),d) (candidateProgram payload)).comp edges
  exact ((foldWinnerProgram payload d).comp (extended.pair start)).congrFun (fun _ => rfl)

theorem relaxRow_deploy {α : Type} (payload : α → List Bool) (d : α) (o : OracleSpec.WordOracle)
    (x : List ((Key × ℤ) × α) × (Key × α)) :
    let input := prodCode (listCode (prodCode (prodCode keyCode intCode) payload)) (prodCode keyCode payload) x
    let p := relaxRowProgram payload d
    (OracleSpec.BitCode.deploy p).ComputesWithin o input
      (3*p.bound.eval input.length+2*input.length+2)
      (fun history bits => history = [] ∧ bits = prodCode keyCode payload (relaxRow x)) :=
  OracleSpec.BitCode.deploy_correct (relaxRowProgram payload d) o x

end GridMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
