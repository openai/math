import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignData
import OAI.Optimization.LinearProgramming.PriceGame.ControlCampaignPower
import OAI.Optimization.LinearProgramming.PriceGame.ControlRatListSum
import OAI.Optimization.LinearProgramming.PriceGame.LearningGenerationCost

/-! # Physical weight-array updates for the outer campaign

The only padded quantity is the cap on the returned integer score. Every loop is
a concrete finite-bit-stack procedure with a polynomial bound on its input words.
-/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open Learning.GenerationCost

abbrev scaleCode : (ℕ × List ℚ × List ℕ) → List Bool :=
  prodCode unaryCode (prodCode (listCode ratCode) (listCode Nat.bits))

def clippedScale (x : ℕ × List ℚ × List ℕ) (i : ℕ) : ℚ :=
  (2 : ℚ)^(min x.1 ((x.2.2.drop i).headD 0)) * (x.2.1.drop i).headD 0

def clippedWeights (x : ℕ × List ℚ × List ℕ) : List ℚ :=
  (List.range x.2.1.length).map (clippedScale x)

private noncomputable def scaleAtP : Procedure (prodCode unaryCode scaleCode) ratCode
    (fun indexed => clippedScale indexed.2 indexed.1) := by
  let index := unaryToBits.comp (first unaryCode scaleCode)
  let env := second unaryCode scaleCode
  let cap := (first unaryCode (prodCode (listCode ratCode) (listCode Nat.bits))).comp env
  let fields := (second unaryCode (prodCode (listCode ratCode) (listCode Nat.bits))).comp env
  let weights := (first (listCode ratCode) (listCode Nat.bits)).comp fields
  let scores := (second (listCode ratCode) (listCode Nat.bits)).comp fields
  let score := (listGet Nat.bits 0).comp (index.pair scores)
  let weight := (listGet ratCode 0).comp (index.pair weights)
  exact ratMul.comp ((boundedPowerRatP.comp (cap.pair score)).pair weight)

/-- Actual physical scale update, preserving all previous roster positions. -/
noncomputable def clippedWeightsP : Procedure scaleCode (listCode ratCode) clippedWeights := by
  let fields := second unaryCode (prodCode (listCode ratCode) (listCode Nat.bits))
  let weights := (first (listCode ratCode) (listCode Nat.bits)).comp fields
  let length := (lengthUnaryP ratCode 0).comp weights
  exact (tabulate (f:=clippedScale) (0 : ℚ) scaleAtP).comp (length.pair (identity scaleCode))

theorem clippedWeights_eq (cap : ℕ) (w : List ℚ) (scores : List ℕ)
    (safe : ∀ i < w.length, scores[i]?.getD 0 ≤ cap) :
    clippedWeights (cap,w,scores) = scaledWeights w scores := by
  apply List.ext_getElem
  · simp [clippedWeights,scaledWeights]
  · intro i hi hj
    have hw : i < w.length := by simpa [clippedWeights] using hi
    simp [clippedWeights,clippedScale,scaledWeights,List.head?_drop,min_eq_right (safe i hw),
      List.getElem?_eq_getElem hw]

abbrev updateCode : (ℕ × List ℚ) → List Bool := prodCode unaryCode (listCode ratCode)

def paddedRows (x : ℕ × List ℚ) : List ℚ :=
  (List.range x.1).map fun i => (x.2.drop i).headD 0

private noncomputable def paddedRowsP : Procedure updateCode (listCode ratCode) paddedRows := by
  let i := unaryToBits.comp (first unaryCode (listCode ratCode))
  let input := second unaryCode (listCode ratCode)
  let each := (listGet ratCode 0).comp (i.pair input)
  exact tabulate (f := fun (xs : List ℚ) j => (xs.drop j).headD 0) 0 each

private theorem sum_padded (v : List ℚ) (n : ℕ) :
    (paddedRows (n,v)).sum = ∑ i ∈ Finset.range n, v[i]?.getD 0 := by
  induction n with
  | zero => simp [paddedRows]
  | succ n ih =>
    simpa [paddedRows,List.range_succ,Finset.sum_range_succ,List.head?_drop] using
      congrArg (· + v[n]?.getD 0) ih

/-- Physical materialization of the fixed-share vector. Its zero-padded old entries
and reweighted total agree also when supplied a size shorter than the old vector. -/
noncomputable def nextWeightsP : Procedure updateCode (listCode ratCode)
    (fun x => nextWeights x.2 x.1) := by
  let size := first unaryCode (listCode ratCode)
  let total := ratListSumP.comp paddedRowsP
  let qsize := natToRat.comp (unaryToBits.comp size)
  let share := ratMul.comp ((ratDiv.comp ((constant updateCode ratCode (1/64)).pair qsize)).pair total)
  let term := ratAdd.comp ((ratMul.comp ((constant (prodCode ratCode ratCode) ratCode (1-1/64)).pair
    (first ratCode ratCode))).pair (second ratCode ratCode))
  let out := (mapContextP (0 : ℚ) (0 : ℚ) term).comp (paddedRowsP.pair share)
  apply out.congrFun
  rintro ⟨n,v⟩
  change (paddedRows (n,v)).map (fun a : ℚ => (1-1/64)*a + ((1/64 : ℚ)/n)*(paddedRows (n,v)).sum) = _
  rw [sum_padded]
  apply List.ext_getElem
  · simp [paddedRows,nextWeights]
  · intro i hi hj
    simp [paddedRows,nextWeights,List.head?_drop]

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
