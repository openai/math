import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachine
import OAI.Optimization.LinearProgramming.PriceGame.MarketBitStackBridge
import OAI.Optimization.LinearProgramming.PriceGame.ControlScalarMachine

/-! Computing the terminal integer banks and endpoint address for a serialized unit augmentation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace Augment
namespace Machine

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open OAI.Optimization.LinearProgramming.PriceGame.Market.GridMachine

abbrev Bank := List ℤ
abbrev Banks := Bank × Bank
abbrev bankCode : Bank → List Bool := listCode intCode
abbrev banksCode : Banks → List Bool := prodCode bankCode bankCode

/-- Expert index, expert signs, common integer grid denominator, and old dual banks. -/
abbrev Seed := ℕ × (List Bool × (ℤ × Banks))
abbrev seedCode : Seed → List Bool := prodCode Nat.bits (prodCode (listCode boolCode) (prodCode intCode banksCode))

abbrev Replace := (ℕ × ℤ) × Bank
abbrev replaceCode : Replace → List Bool := prodCode (prodCode Nat.bits intCode) bankCode

def replacedCell (x : Replace) (k : ℕ) : ℤ :=
  if k = x.1.1 then x.1.2 else (x.2.drop k).headD 0

def replaceCell (x : Replace) : Bank := (List.range x.2.length).map (replacedCell x)

private noncomputable def replacedCellP : Procedure (prodCode unaryCode replaceCode) intCode
    (fun a => replacedCell a.2 a.1) := by
  let env := prodCode unaryCode replaceCode
  let idx := unaryToBits.comp (first unaryCode replaceCode)
  let x := second unaryCode replaceCode
  let iv := (first (prodCode Nat.bits intCode) bankCode).comp x
  let xs := (second (prodCode Nat.bits intCode) bankCode).comp x
  let old := (listGet intCode 0).comp (idx.pair xs)
  let target := (first Nat.bits intCode).comp iv
  let value := (second Nat.bits intCode).comp iv
  let eq := Control.Native.natEqP.comp (idx.pair target)
  exact ((choose old value).comp (eq.pair (identity env))).congrFun fun _ => by simp [replacedCell]

noncomputable def replaceCellP : Procedure replaceCode bankCode replaceCell := by
  let len := (Learning.GenerationCost.lengthUnaryP intCode 0).comp (second (prodCode Nat.bits intCode) bankCode)
  exact (tabulate (f := replacedCell) 0 replacedCellP).comp (len.pair (identity replaceCode))

@[simp] theorem length_replace (x : Replace) : (replaceCell x).length = x.2.length := by simp [replaceCell]

def isSupply (x : Seed) : Bool := (x.2.1.drop x.1).headD false

def sourceIndex (x : Seed) : ℕ := if isSupply x then x.1 else x.2.1.length

def newTerminal (x : Seed) : ℤ :=
  (if isSupply x then (x.2.2.2.1.drop x.1).headD 0 else x.2.2.2.2.headD 0) + x.2.2.1

def terminalBanks (x : Seed) : Banks :=
  if isSupply x then (x.2.2.2.1, replaceCell ((0,newTerminal x),x.2.2.2.2))
  else (replaceCell ((x.1,newTerminal x),x.2.2.2.1),x.2.2.2.2)

private noncomputable abbrev numberP := first Nat.bits (prodCode (listCode boolCode) (prodCode intCode banksCode))
private noncomputable abbrev fieldsP := second Nat.bits (prodCode (listCode boolCode) (prodCode intCode banksCode))
private noncomputable abbrev signsP := (first (listCode boolCode) (prodCode intCode banksCode)).comp fieldsP
private noncomputable abbrev remainingP := (second (listCode boolCode) (prodCode intCode banksCode)).comp fieldsP
private noncomputable abbrev denP := (first intCode banksCode).comp remainingP
private noncomputable abbrev banksP := (second intCode banksCode).comp remainingP
private noncomputable abbrev peP := (first bankCode bankCode).comp banksP
private noncomputable abbrev poP := (second bankCode bankCode).comp banksP

noncomputable def isSupplyP : Procedure seedCode boolCode isSupply :=
  (listGet boolCode false).comp (numberP.pair signsP)

noncomputable def sourceIndexP : Procedure seedCode Nat.bits sourceIndex :=
  (choose ((listLength boolCode false).comp signsP) numberP).comp (isSupplyP.pair (identity seedCode))

noncomputable def newTerminalP : Procedure seedCode intCode newTerminal := by
  let getE := (listGet intCode 0).comp (numberP.pair peP)
  let getO := (listGet intCode 0).comp ((constant seedCode Nat.bits 0).pair poP)
  let src := (choose getO getE).comp (isSupplyP.pair (identity seedCode))
  exact (intAdd.comp (src.pair denP)).congrFun fun _ => rfl

noncomputable def terminalBanksP : Procedure seedCode banksCode terminalBanks := by
  let keyE := numberP.pair newTerminalP
  let keyO := (constant seedCode Nat.bits 0).pair newTerminalP
  let e' := replaceCellP.comp (keyE.pair peP)
  let o' := replaceCellP.comp (keyO.pair poP)
  exact (choose (e'.pair poP) (peP.pair o')).comp (isSupplyP.pair (identity seedCode))

/-- Terminal rewriting leaves the two physical banks at their original lengths. -/
theorem terminal_lengths (x : Seed) :
    (terminalBanks x).1.length = x.2.2.2.1.length ∧ (terminalBanks x).2.length = x.2.2.2.2.length := by
  cases h : isSupply x <;> simp [terminalBanks, h]

end Machine
end Augment
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
