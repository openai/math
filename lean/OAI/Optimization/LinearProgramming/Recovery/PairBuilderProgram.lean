import OAI.Optimization.LinearProgramming.Recovery.PairBuilderLayout
import OAI.Optimization.LinearProgramming.Recovery.PairBuilderHeaders
import OAI.Optimization.LinearProgramming.Recovery.PairBuilderBounds
import OAI.Optimization.LinearProgramming.Recovery.BankRead

/-! Register layout and fixed instruction sequence for both orderings of a complementary basis pair. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PairBuilder

open RAM RAM.Call RAM.Callable RAM.Tape Matrix
open _root_.OAI.Optimization.LinearProgramming.Geometry

def limit {h n : ℕ} (l : Layout h n) := h+n+l.scratch+capacity h n l.previous+3

def firstDst (kernelFirst : Bool) (out n k : ℕ) := if kernelFirst then out+(n-k)*n else out

def secondDst (kernelFirst : Bool) (out n k : ℕ) := if kernelFirst then out else out+k*n

inductive Phase where
  | init | firstLoad | place (kernelFirst : Bool) | residualLoad | copyResidual | lastLoad | copyLast | finish (kernelFirst : Bool)
  deriving DecidableEq

open Phase in
def plan : Phase→Plan
  | init => [(210,capacityExpr (.reg 200) (.reg 201) (.reg 205)),(206,0),(207,0),(211,0),(212,0)]
  | firstLoad => [(55,.reg 202),(56,.reg 200 * .reg 201),(57,208),(58,2),(60,.reg 210),(208,.reg 200),(209,.reg 201)]
  | place rev =>
    let lhs : AddressTerm 220 := if rev then .reg 203 + (.reg 201 - .reg 206) * .reg 201 else .reg 203
    let rhs : AddressTerm 220 := if rev then .reg 203 else .reg 203 + .reg 206 * .reg 201
    [(211,lhs),(212,rhs),(181,.reg 211),(182,.reg 206 * .reg 201)]
  | residualLoad => [(55,.reg 211),(56,.reg 206 * .reg 201),(57,208),(58,2),(60,.reg 210),(208,.reg 206),(209,.reg 201)]
  | copyResidual => [(181,.reg 204),(182,.reg 201 * .reg 201)]
  | lastLoad => [(55,.reg 204),(56,.reg 201 * .reg 201),(57,208),(58,2),(60,.reg 210),(208,.reg 201),(209,.reg 201)]
  | copyLast => [(181,.reg 212),(182,.reg 207 * .reg 201)]
  | finish rev => [(55,.reg 203),(56,.reg 201 * .reg 201),(57,208),(58,2),(60,.reg 210),
    (208,.reg (if rev then 207 else 206)),(209,.reg (if rev then 206 else 207))]

def «meta» (p : Phase) := header (plan p)
def receive (native dst : ℕ) := Fragment.ofBlock (BankRead.receiveIndex native dst)
def copyRows := Fragment.ofBlock BankRead.copyWindow

def firstCall := («meta» .firstLoad).seq (normalCall RowPack.program)
def firstExport (rev : Bool) := (receive 165 206).seq ((receive 57 180).seq ((«meta» (.place rev)).seq copyRows))
def residualCall := («meta» .residualLoad).seq (normalCall ResidualROM.block)
def residualExport := (receive 58 180).seq ((«meta» .copyResidual).seq copyRows)
def lastCall := («meta» .lastLoad).seq (normalCall RowPack.program)
def lastExport := (receive 165 207).seq ((receive 57 180).seq ((«meta» .copyLast).seq copyRows))

/-- `false` emits (packed C, packed ker C). `true` emits (packed ker C, packed C). -/
def program (kernelFirst : Bool) : Fragment := («meta» .init).seq (firstCall.seq ((firstExport kernelFirst).seq
  (residualCall.seq (residualExport.seq (lastCall.seq (lastExport.seq («meta» (.finish kernelFirst))))))))

noncomputable def metaBudget : Polynomial ℕ := 4*((plan .init).budget + (plan .firstLoad).budget + (plan (.place false)).budget + (plan (.place true)).budget + (plan .residualLoad).budget + (plan .copyResidual).budget + (plan .lastLoad).budget + (plan .copyLast).budget + (plan (.finish false)).budget + (plan (.finish true)).budget)

theorem meta_budget (p : Phase) (B : ℕ) : 4*(plan p).budget.eval B ≤ metaBudget.eval B := by
  simp only [metaBudget, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_ofNat]
  cases p with
  | place r | finish r => cases r <;> omega
  | _ => omega

def usable : Finset (Fin 220) := {200,201,202,203,204,205,206,207,210,211,212}

theorem needed_usable (p : Phase) : needed (plan p) ⊆ usable := by
  cases p with | place r | finish r => cases r <;> decide | _ => decide

theorem meta_static (p : Phase) : ((plan p).code 220).indexWritesBelow 512=true := by
  cases p with | place r | finish r => cases r <;> decide | _ => decide

def Held (p : ℕ) : Prop := p=24 ∨ p=28 ∨ p=29 ∨ 512 ≤ p

theorem keeps_held (u : Phase) (i : Fin 220) (h : Held i) : i∉written (plan u) := by
  rcases h with h|h|h|h <;> have hi:=i.isLt
  · have eq : i=(24 : Fin 220) := Fin.ext h; subst i; cases u with | place r | finish r => cases r <;> decide | _ => decide
  · have eq : i=(28 : Fin 220) := Fin.ext h; subst i; cases u with | place r | finish r => cases r <;> decide | _ => decide
  · have eq : i=(29 : Fin 220) := Fin.ext h; subst i; cases u with | place r | finish r => cases r <;> decide | _ => decide
  · omega

noncomputable def time {h n : ℕ} (l : Layout h n) :=
  8*metaBudget.eval (limit l) + 3*(19*capacity h n l.previous+225+(2*workerTime h n+2)) + 3*(21*n*n+7)

def SourceFrame {K : Type*} {h n : ℕ} (l : Layout h n) (m t : Memory K) : Prop :=
  (∀ p,Held p → t.index p=m.index p) ∧
  ∀p,p≠4 → (p<l.out ∨ l.out+n*n ≤ p) → (p<l.scratch ∨ l.scratch+n*n ≤ p) → t.data p=m.data p

end PairBuilder
end Recovery
end LinearProgramming
end Optimization
end OAI
