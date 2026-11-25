import OAI.Optimization.LinearProgramming.PriceGame.ControlCollapseMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlScanMachine
import OAI.Optimization.LinearProgramming.PriceGame.ControlWire
import OAI.Optimization.LinearProgramming.OracleSpec.ArithmeticEncoding

/-! A polynomial-time finite-stack implementation of the complete feedback scan:
form numerical median prices, build the actual root requests on ties, and consume
the prefix of answers. No oracle call is executed by this pure dispatch program. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure

abbrev ItemContext := List Row × (Row × Row)
def itemContextCode : ItemContext → List Bool := prodCode (listCode rowCode) (prodCode rowCode rowCode)

private def get (xs : Row) (j : ℕ) : ℚ := (xs.drop j).headD 0

/-- Prepare a single sequential interaction. `emit` selects the internal or the public
wire representation of the suspended root query. -/
def rawItem (emit : RowState → List Bool) (z : ItemContext) (i : ℕ) : RequestItem :=
  let y := get z.2.1 i
  let d := get z.2.2 i
  if y < d then .inl true else if d < y then .inl false
  else .inr (emit (collapse (z.1, i,z.2.2)))

noncomputable def rawItemP (emit : RowState → List Bool) (write : Procedure rowStateCode id emit) :
    Procedure (prodCode unaryCode itemContextCode) itemCode (fun z => rawItem emit z.2 z.1) := by
  let domain := prodCode unaryCode itemContextCode
  let i := unaryToBits.comp (first unaryCode itemContextCode)
  let ctx := second unaryCode itemContextCode
  let h := (first (listCode rowCode) (prodCode rowCode rowCode)).comp ctx
  let yd := (second (listCode rowCode) (prodCode rowCode rowCode)).comp ctx
  let y := (first rowCode rowCode).comp yd
  let d := (second rowCode rowCode).comp yd
  let yi := (listGet ratCode 0).comp (i.pair y)
  let di := (listGet ratCode 0).comp (i.pair d)
  let ascend := collapseP.comp (h.pair (i.pair d))
  let word := write.comp ascend
  let request : Procedure domain itemCode (fun z => Sum.inr (emit (collapse (z.2.1,z.1,z.2.2.2)))) :=
    ((prepend id [true]).comp word).result (by intro t; rfl)
  let lower := conditional (OracleSpec.Arithmetic.ratLt.comp (di.pair yi)) (constant domain itemCode (.inl false)) request
  exact (conditional (OracleSpec.Arithmetic.ratLt.comp (yi.pair di)) (constant domain itemCode (.inl true)) lower).congrFun
    (by intro z; simp only [rawItem, Function.comp_apply, id_eq, decide_eq_true_eq]; rfl)

abbrev FeedbackInput := List Row × (Row × (Row × List Bool))
def feedbackCode : FeedbackInput → List Bool :=
  prodCode (listCode rowCode) (prodCode rowCode (prodCode rowCode answerListCode))

def medianRow (y x : Row) : Row := liftRow (2*y.length, y, x)

noncomputable def medianRowP : Procedure (prodCode rowCode rowCode) rowCode (fun z => medianRow z.1 z.2) := by
  let y := first rowCode rowCode
  let n := (listLength ratCode 0).comp y
  let q := double.comp n
  exact (liftRowP.comp (q.pair (identity (prodCode rowCode rowCode)))).congrFun (by intro z; rfl)

def preparedItems (emit : RowState → List Bool) (s : FeedbackInput) : List RequestItem :=
  let y := s.2.1
  let d := medianRow y s.2.2.1
  (List.range y.length).map (rawItem emit (s.1,y,d))

noncomputable def preparedItemsP (emit : RowState → List Bool) (write : Procedure rowStateCode id emit) :
    Procedure feedbackCode (listCode itemCode) (preparedItems emit) := by
  let tailCode := prodCode rowCode (prodCode rowCode answerListCode)
  let hist := first (listCode rowCode) tailCode
  let rest := second (listCode rowCode) tailCode
  let base := (first rowCode (prodCode rowCode answerListCode)).comp rest
  let childAndBits := (second rowCode (prodCode rowCode answerListCode)).comp rest
  let child := (first rowCode answerListCode).comp childAndBits
  let d := medianRowP.comp (base.pair child)
  let n := (rowSizeP ratCode 0).comp base
  let ctx := hist.pair (base.pair d)
  exact ((tabulate (f:=rawItem emit) (.inl false) (rawItemP emit write)).comp
    (n.pair ctx)).congrFun (by intro s; rfl)

def finishState : ScanState → (List Bool ⊕ List Bool)
  | .inl packet => .inr packet
  | .inr (_, backwards) => .inl backwards.reverse

noncomputable def finishStateP : Procedure scanCode (sumCode answerListCode id) finishState := by
  let rc := prodCode answerListCode answerListCode
  let done := (listReverse boolCode false).comp (second answerListCode answerListCode)
  let ret : Procedure rc (sumCode answerListCode id) (fun z => .inl z.2.reverse) :=
    ((prepend answerListCode [false]).comp done).result (by intro x; rfl)
  let wait : Procedure id (sumCode answerListCode id) (Sum.inr : List Bool → List Bool ⊕ List Bool) :=
    (prepend id [true]).result (by intro w; rfl)
  exact (casesSum wait ret).congrFun (by intro s; cases s <;> rfl)

def rawFeedback (emit : RowState → List Bool) (s : FeedbackInput) : List Bool ⊕ List Bool :=
  finishState (scanFeedback (preparedItems emit s,s.2.2.2))

noncomputable def rawFeedbackP (emit : RowState → List Bool) (write : Procedure rowStateCode id emit) :
    Procedure feedbackCode (sumCode answerListCode id) (rawFeedback emit) := by
  let tailCode := prodCode rowCode (prodCode rowCode answerListCode)
  let rest := second (listCode rowCode) tailCode
  let xb := (second rowCode (prodCode rowCode answerListCode)).comp rest
  let bits := (second rowCode answerListCode).comp xb
  exact (finishStateP.comp (scanFeedbackP.comp ((preparedItemsP emit write).pair bits))).congrFun (by
    intro s; rfl)

def internalRowWord (q : RowState) : List Bool := Wire.packedQueryCode ⟨q.2,q.1⟩
def externalRowWord (q : RowState) : List Bool := OracleSpec.encodeNat q.1 ++ q.2.flatMap OracleSpec.encodeRat

noncomputable def internalRowWordP : Procedure rowStateCode id internalRowWord :=
  (swap Nat.bits rowCode).result (by intro q; rfl)

noncomputable def feedbackPackedP :
    Procedure feedbackCode (sumCode answerListCode id) (rawFeedback internalRowWord) :=
  rawFeedbackP _ internalRowWordP

noncomputable def feedbackWireP :
    Procedure feedbackCode (sumCode answerListCode id) (rawFeedback externalRowWord) :=
  rawFeedbackP _ OracleSpec.Wire.writeQuery

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
