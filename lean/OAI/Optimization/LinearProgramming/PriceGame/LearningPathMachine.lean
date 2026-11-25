import OAI.Computability.QuantumFactoring.BitStackRationalDivision
import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Optimization.LinearProgramming.PriceGame.LearningVecMachine
import OAI.Optimization.LinearProgramming.PriceGame.LearningRepresentatives

/-! # A binary-stack procedure for Floyd–Warshall and the centered representative

There are at most 66 coordinates in a compact skeleton. With the arity fixed, the loops
over pivots and cells compile to finite compositions of genuine bit-stack procedures.
All input-dependent integer and rational operations, copying, and addressing have the
bit-step polynomial supplied by `Procedure.runs`.
-/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Learning
namespace BitMachine

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure (boolCode)

/-- Wire form of an optional result, with a one-bit tag. -/
def optionCode {α : Type} (ea : α → List Bool) : Option α → List Bool
  | none => [false]
  | some a => true :: ea a

noncomputable def someP {α : Type} (ea : α → List Bool) : Procedure ea (optionCode ea) some :=
  (Procedure.prepend ea [true]).result (fun _ => rfl)

noncomputable def minP : Procedure (prodCode intCode intCode) intCode
    (fun x : ℤ × ℤ => min x.1 x.2) := by
  apply (Procedure.conditional OracleSpec.Arithmetic.intLe (Procedure.first intCode intCode)
    (Procedure.second intCode intCode)).congrFun
  intro x; simp [min_def]

/-- Include empty walks when initializing the diagonals. -/
noncomputable def initialP (n : ℕ) : Procedure (matrixCode intCode n) (matrixCode intCode n)
    (@Paths.initial (Fin n) inferInstance) := by
  apply assembleMatrix
  intro i j
  let cell := readMatrix intCode 0 i j
  if h : i = j then
    exact (minP.comp ((Procedure.constant (matrixCode intCode n) intCode 0).pair cell)).congrFun
      (by intro c; simp [Paths.initial,h])
  else exact cell.congrFun (by intro c; simp [Paths.initial,h])

/-- One *actual* min-plus relaxation of the encoded table. -/
noncomputable def relaxP {n : ℕ} (k : Fin n) :
    Procedure (matrixCode intCode n) (matrixCode intCode n) (Paths.relax k) := by
  apply assembleMatrix
  intro i j
  let old := readMatrix intCode 0 i j
  let via := Procedure.intAdd.comp ((readMatrix intCode 0 i k).pair (readMatrix intCode 0 k j))
  exact minP.comp (old.pair via)

noncomputable def sweepP {n : ℕ} (ks : List (Fin n)) :
    Procedure (matrixCode intCode n) (matrixCode intCode n) (Paths.sweep ks) :=
  match ks with
  | [] => Procedure.identity _
  | k :: rest => (sweepP rest).comp (relaxP k)

/-- A finite bit machine whose decoded output is the exact integer distance matrix. -/
noncomputable def distanceP (n : ℕ) : Procedure (matrixCode intCode n) (matrixCode intCode n)
    (@Paths.distance n) := (sweepP (List.finRange n)).comp (initialP n)

private noncomputable def andListP {α ι : Type} (ea : α → List Bool) (f : α → ι → Bool)
    (p : ∀ i, Procedure ea boolCode (fun a => f a i)) :
    (is : List ι) → Procedure ea boolCode (fun a => is.all (f a))
  | [] => Procedure.constant ea boolCode true
  | i::is => (Procedure.boolAnd.comp ((p i).pair (andListP ea f p is))).congrFun (by simp)

noncomputable def diagonalP (n : ℕ) : Procedure (matrixCode intCode n) boolCode
    (fun d => decide (∀ i, 0 ≤ d i i)) := by
  let e := matrixCode intCode n
  let p (i : Fin n) := OracleSpec.Arithmetic.intLe.comp ((Procedure.constant e intCode 0).pair (readMatrix intCode 0 i i))
  apply (andListP e (fun d i => decide (0 ≤ d i i)) p (List.finRange n)).congrFun
  intro d
  apply Bool.eq_iff_iff.mpr
  simp

private noncomputable def sumIntP {α : Type} (ea : α → List Bool) :
    (n : ℕ) → (f : α → Fin n → ℤ) → (∀ i, Procedure ea intCode (fun a => f a i)) →
      Procedure ea intCode (fun a => ∑ i, f a i)
  | 0, _, _ => (Procedure.constant ea intCode 0).congrFun (by simp)
  | n+1, f, p =>
    (Procedure.intAdd.comp ((p 0).pair (sumIntP ea n (fun x i => f x i.succ) (fun i => p i.succ)))).congrFun
      (by intro a; change f a 0 + ∑ i : Fin n, f a i.succ = _; rw [Fin.sum_univ_succ])

/-- The actual source average is obtained with integer accumulation and one rational division. -/
noncomputable def representativeP {p : ℕ} (a : Fin (p+1)) :
    Procedure (matrixCode intCode (p+1)) (vecCode ratCode (p+1)) (fun d => representative d a) := by
  let e := matrixCode intCode (p+1)
  apply assemble
  intro i
  let sum := sumIntP e (p+1) (fun d s => potential d a s i) (fun s =>
    Procedure.intSub.comp ((readMatrix intCode 0 s i).pair (readMatrix intCode 0 s a)))
  let denom := Procedure.constant e ratCode ((p+1 : ℕ) : ℚ)
  apply (Procedure.ratDiv.comp ((Procedure.intToRat.comp sum).pair denom)).congrFun
  intro d
  change ((∑ s, potential d a s i : ℤ) : ℚ) / ((p+1 : ℕ) : ℚ) = _
  simp [representative]

/-- The checked cell routine starting from compiled integer arc bounds. -/
def feasibleRepresentative {p : ℕ} (a : Fin (p+1)) (c : Bounds (p+1)) :
    Option (Fin (p+1) → ℚ) :=
  let d := Paths.distance c
  if ∀ i, 0 ≤ d i i then some (representative d a) else none

noncomputable def feasibleRepresentativeP {p : ℕ} (a : Fin (p+1)) :
    Procedure (matrixCode intCode (p+1)) (optionCode (vecCode ratCode (p+1)))
      (feasibleRepresentative a) := by
  let e := matrixCode intCode (p+1)
  let out := optionCode (vecCode ratCode (p+1))
  let success := (someP (vecCode ratCode (p+1))).comp (representativeP a)
  let test := Procedure.conditional (diagonalP (p+1)) success (Procedure.constant e out none)
  apply (test.comp (distanceP (p+1))).congrFun
  intro c
  simp [feasibleRepresentative]

/-- The decoded stack routine agrees with `cellRepresentative` for the *same* compiled
observation list, including its negative-diagonal rejection. -/
theorem feasibleRepresentative_eq {p R} (a : Fin (p+1)) (os : List (Observation (p+1)))
    (c : Bounds (p+1)) (hc : addObservations os (boxBounds R a) = some c) :
    feasibleRepresentative a c = cellRepresentative R a os := by
  simp only [feasibleRepresentative, cellRepresentative,cellTable,hc,bind,Option.bind_some,
    Paths.compute_correct]
  split <;> simp [Paths.compute_correct]

end BitMachine
end Learning
end PriceGame
end LinearProgramming
end Optimization
end OAI
