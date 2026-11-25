import OAI.Optimization.LinearProgramming.Lattice.BitDriverRows

/-! A finite-control, explicitly stored continuation for the adaptive maximum-coordinate
search and the dyadic queries of a single residual probe. Rows are processed in precisely
the order in which the mathematical sign-query tree requests them. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
namespace Probe

def ask (a : Row) (c : Carry) : Action := .inr (a,c)
def done (b : Bool) (y : List ℚ) : Action := .inl (b,y)

/-- The maximum tree recurses through the tail first. `pending` therefore stores
the still-unprocessed suffix of the reversed matrix. -/
def nextMax (z : Params) (pending : IntMatrix) (best : Row) : Action :=
  match pending with
  | [] => ask (best.map Neg.neg) (.inr (.inl (z,best)))
  | a :: tail => ask a (.inl (.inl ((z,tail),(a,best))))

def start (z : Params) : Action :=
  nextMax z z.2.reverse (List.replicate z.1.1 0)

def orient (nonnegative : Bool) (s : MaxState) : Action :=
  let a := if nonnegative then s.2.1 else s.2.1.map Neg.neg
  ask (rowDifference (a,s.2.2)) (.inl (.inr (s.1,(a,s.2.2))))

def compare (larger : Bool) (s : MaxState) : Action :=
  nextMax s.1.1 s.1.2 (if larger then s.2.1 else s.2.2)

def emitRatio (s : Ratio) : Action :=
  let a := s.1.2.1
  let d := s.1.1.2
  let n := s.2.1.1
  let denominator := s.2.1.2
  ask (combineRows (((denominator : ℤ),n),(a,d))) (.inr (.inr s))

/-- `values` stores the already completed rational coordinates in reverse order. -/
def nextRow (pivot : Pivot) (rows : IntMatrix) (values : List ℚ) : Action :=
  match rows with
  | [] => done true values.reverse
  | a :: tail => emitRatio ((pivot,(a,tail)),((0,1),(pivot.1.1.2-1,values)))

def zeroReply (isZero : Bool) (pivot : Pivot) : Action :=
  if isZero then done false []
  else if pivot.1.1.2 = 0 then done true (List.replicate pivot.1.2.length 0)
  else nextRow pivot pivot.1.2 []

def ratioReply (nonnegative : Bool) (s : Ratio) : Action :=
  let n' := 2*s.2.1.1 + if nonnegative then 1 else -1
  let d' := 2*s.2.1.2
  let left := s.2.2.1
  let values := s.2.2.2
  if left = 0 then
    nextRow s.1.1 s.1.2.2 (((n' : ℚ) / (d' : ℚ)) :: values)
  else emitRatio (s.1,((n',d'),(left-1,values)))

def advance (answer : Bool) : Carry → Action
  | .inl (.inl s) => orient answer s
  | .inl (.inr s) => compare answer s
  | .inr (.inl s) => zeroReply answer s
  | .inr (.inr s) => ratioReply answer s

/-- Input and output follow the machine chronologically. Each listed row causes one
three-valued sign call, whose nonnegative bit determines the next continuation. -/
inductive Runs (oracle : Row → Bool) : Action → List Row → Result → Prop
  | done (r : Result) : Runs oracle (.inl r) [] r
  | ask {a c qs r} (tail : Runs oracle (advance (oracle a) c) qs r) :
      Runs oracle (.inr (a,c)) (a::qs) r

/-- Any stored continuation reached by either answer to an actual pending query. -/
inductive Reaches (start : Action) : Action → Prop
  | refl : Reaches start start
  | step {a c} (reachable : Reaches start (.inr (a,c))) (answer : Bool) :
      Reaches start (advance answer c)

end Probe
end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
