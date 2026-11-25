import OAI.Optimization.LinearProgramming.PriceGame.MarketContextMap
import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCost
import OAI.Optimization.LinearProgramming.OracleSpec.BitStackDeployment

/-! # Binary-stack materialization of the market flow table

Each route entry is a binary arc identifier. The even identifier `2k` adds a unit to
cell `k`, and `2k+1` removes one. Bounds come from the serialized table and route,
so a large binary identifier never drives a loop over its numerical value. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace FlowMachine

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure

abbrev Flow := List ℕ
abbrev Route := List ℕ
abbrev flowCode : Flow → List Bool := listCode Nat.bits
abbrev routeCode : Route → List Bool := listCode Nat.bits
abbrev inputCode := prodCode flowCode routeCode

private noncomputable def sameNatP : Procedure (prodCode Nat.bits Nat.bits) boolCode
    (fun p => decide (p.1 = p.2)) := by
  let rev := binaryLe.comp (swap Nat.bits Nat.bits)
  apply (boolAnd.comp (binaryLe.pair rev)).congrFun
  rintro ⟨a,b⟩
  change (decide (a ≤ b) && decide (b ≤ a)) = decide (a = b)
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h.le, not_le.mpr h, h.ne]
  · simp
  · simp [h.le, not_le.mpr h, h.ne']

private def tally (p : Bool × ℕ) : ℕ := if p.1 then p.2+1 else p.2

private theorem fold_tally (xs : List Bool) (n : ℕ) :
    xs.foldl (fun n b => tally (b,n)) n = n + xs.count true := by
  induction xs generalizing n with
  | nil => simp
  | cons b xs ih =>
    rw [List.foldl_cons, ih]
    cases b
    · simp [tally]
    · simp only [tally, ite_true, List.count_cons_self]
      omega

private noncomputable def countTrueP : Procedure (listCode boolCode) Nat.bits
    (fun xs => xs.count true) := by
  let step : Procedure (prodCode boolCode unaryCode) unaryCode tally :=
    (choose (identity unaryCode) unarySuccessor).congrFun (fun _ => rfl)
  let run := foldList false step Polynomial.X (by
    intro xs n j
    change (unaryCode ((xs.take j).foldl (fun n b => tally (b,n)) n)).length ≤ _
    rw [fold_tally]
    have ht := List.count_le_length (a := true) (l := xs.take j)
    have hs := list_length_le_code boolCode xs
    simp only [List.length_take] at ht
    simp only [unaryCode, List.length_replicate, Polynomial.eval_X]
    omega)
  let init := (identity (listCode boolCode)).pair (constant (listCode boolCode) unaryCode 0)
  exact (unaryToBits.comp (run.comp init)).congrFun (by
    intro xs
    change xs.foldl (fun n b => tally (b,n)) 0 = _
    simp [fold_tally])

private theorem count_mark (xs : List ℕ) (k : ℕ) :
    (xs.map (fun v => decide (k = v))).count true = xs.count k := by
  induction xs with
  | nil => simp
  | cons j js ih =>
    by_cases hk : k = j
    · subst j
      simp [ih]
    · simp [hk, Ne.symm hk, ih]

/-- Scanning the complete route counts occurrences of a binary identifier. -/
noncomputable def occurrencesP : Procedure (prodCode routeCode Nat.bits) Nat.bits
    (fun z => z.1.count z.2) := by
  let marked := GridMachine.mapWithContext 0 false sameNatP
  exact (countTrueP.comp marked).congrFun (fun x => count_mark x.1 x.2)

def updatedCell (x : Flow × Route) (k : ℕ) : ℕ :=
  (x.1.drop k).headD 0 + x.2.count (2*k) - x.2.count (2*k+1)

/-- Materialize exactly the original number of table cells, in their original order. -/
def update (x : Flow × Route) : Flow := (List.range x.1.length).map (updatedCell x)

noncomputable def cellP : Procedure (prodCode unaryCode inputCode) Nat.bits
    (fun z => updatedCell z.2 z.1) := by
  let k := unaryToBits.comp (first unaryCode inputCode)
  let input := second unaryCode inputCode
  let mass := (first flowCode routeCode).comp input
  let route := (second flowCode routeCode).comp input
  let old := (listGet Nat.bits 0).comp (k.pair mass)
  let added := occurrencesP.comp (route.pair (double.comp k))
  let removed := occurrencesP.comp (route.pair (doubleOne.comp k))
  exact (binarySub.comp ((binaryAdd.comp (old.pair added)).pair removed)).congrFun (fun _ => rfl)

/-- A fixed finite-stack program, including list indexing, bit comparisons, all route scans
and final table serialization. Its runtime polynomial is in the input encoding length. -/
noncomputable def updateP : Procedure inputCode flowCode update := by
  let count := (Learning.GenerationCost.lengthUnaryP Nat.bits 0).comp (first flowCode routeCode)
  exact ((tabulate 0 cellP).comp (count.pair (identity inputCode))).congrFun (fun _ => rfl)

/-- Doubling all integral flows at a digit boundary uses the binary doubling program. -/
noncomputable def doubleP : Procedure flowCode flowCode (List.map (2 * ·)) :=
  listMap 0 0 double

theorem update_length (xs : Flow) (route : Route) : (update (xs,route)).length = xs.length := by
  simp [update]

theorem update_deploy (o : OracleSpec.WordOracle) (x : Flow × Route) :
    (OracleSpec.BitCode.deploy updateP).ComputesWithin o (inputCode x)
      (3*updateP.bound.eval (inputCode x).length + 2*(inputCode x).length + 2)
      (fun history bits => history = [] ∧ bits = flowCode (update x)) :=
  OracleSpec.BitCode.deploy_correct updateP o x

end FlowMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
