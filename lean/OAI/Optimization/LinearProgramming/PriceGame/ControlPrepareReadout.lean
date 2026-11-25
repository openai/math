import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblyLoops
import OAI.Optimization.LinearProgramming.PriceGame.ControlListMedian
import OAI.Optimization.LinearProgramming.PriceGame.MarketContextMap
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine

/-! Input-independent bit-stack programs for the two possible outputs of a trial
preparation: coordinate medians and the dense allocation row readout. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
open ExactQuantumFactoring.BitStackProgram Procedure
open Trial Wire TrialExecution Market.GridMachine

private abbrev ns := listCode Nat.bits
private abbrev qs := listCode ratCode

def prefixMedians (x : List ℕ × ℕ × List Completed) : List ℚ :=
  x.1.map fun i => medianValue ((x.2.2.take x.2.1).map fun c => atD c.baseline i)

noncomputable def prefixMediansP : Procedure (prodCode ns (prodCode Nat.bits assemblyCallsCode)) qs
    prefixMedians := by
  let goods := first ns (prodCode Nat.bits assemblyCallsCode)
  let data := second ns (prodCode Nat.bits assemblyCallsCode)
  let rows := (takeListP completedCode default).comp data
  let val := medianValueP.comp (columnP ratCode completedBaselineP)
  exact (mapWithContext 0 (0:ℚ) val).comp (goods.pair rows)

private theorem median_same_width {n m : ℕ} (h : n=m) (f : Fin n → ℚ) (g : Fin m → ℚ)
    (hf : ∀ i, f i = g (i.cast h)) : median f = median g := by
  subst m
  exact congrArg median (funext hf)

private theorem median_list_ofFn {n : ℕ} (f : Fin n → ℚ) :
    medianValue (List.ofFn f) = median f := by
  unfold medianValue
  apply median_same_width (List.length_ofFn (f:=f))
  intro i
  change (List.ofFn f)[i.val] = f (i.cast _)
  rw [List.getElem_ofFn]
  rfl

theorem prefixMedians_eq (g r : ℕ) (xs : List Completed) (hr : r ≤ xs.length) :
    prefixMedians (List.range g,r,xs) = medianRows r g (xs.map Completed.baseline) := by
  apply List.ext_getElem
  · simp [prefixMedians,medianRows]
  · intro i _ _
    simp only [prefixMedians,List.getElem_map,List.getElem_range,medianRows,List.getElem_ofFn]
    have col : ((xs.take r).map fun c => atD c.baseline i) =
        List.ofFn (fun k : Fin r => atD (atD (xs.map Completed.baseline) k.val) i) := by
      apply List.ext_getElem
      · simp [Nat.min_eq_left hr]
      · intro k h _
        have hkr : k < r := by simpa [Nat.min_eq_left hr] using h
        have hk := hkr.trans_le hr
        simp [atD, hk]
    rw [col,median_list_ofFn]

abbrev DenseAlloc := ℕ × List ℕ × List ℚ
abbrev denseAllocCode : DenseAlloc → List Bool := prodCode unaryCode (prodCode ns qs)

def recoverCell (x : ℕ × ℕ × List ℚ) (j : ℕ) : ℚ :=
  atD x.2.2 (x.1 * (x.2.1+1) + (j+1))

def recoverRows (x : DenseAlloc) : List (List ℚ) :=
  (List.range x.1).map (fun e => x.2.1.map (recoverCell (e,x.2.1.length,x.2.2)))

/-- Recover only real-good columns, skipping each expert's preceding dummy entry. -/
noncomputable def recoverRowsP : Procedure denseAllocCode (listCode qs) recoverRows := by
  let rest := prodCode ns qs
  let data := second unaryCode rest
  let n := first unaryCode rest
  let frame := prodCode Nat.bits (prodCode Nat.bits qs)
  let f := first frame Nat.bits
  let j := second frame Nat.bits
  let e := (first Nat.bits (prodCode Nat.bits qs)).comp f
  let rem := (second Nat.bits (prodCode Nat.bits qs)).comp f
  let one := constant (prodCode frame Nat.bits) Nat.bits 1
  let width := binaryAdd.comp (((first Nat.bits qs).comp rem).pair one)
  let bids := (second Nat.bits qs).comp rem
  let ix := binaryAdd.comp ((binaryMul.comp (e.pair width)).pair (binaryAdd.comp (j.pair one)))
  let cell := (atDP ratCode).comp (ix.pair bids)
  let env := first rest Nat.bits
  let current := second rest Nat.bits
  let goods := (first ns qs).comp env
  let alloc := (second ns qs).comp env
  let num := (listLength Nat.bits 0).comp goods
  let row := (mapWithContext 0 (0:ℚ) cell).comp (goods.pair (current.pair (num.pair alloc)))
  exact (mapWithContext 0 [] row).comp ((addressRangeP.comp n).pair data)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
