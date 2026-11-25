import OAI.Computability.NearSquareRoot.InterchangeROMProgram
import OAI.Computability.NearSquareRoot.InterchangeStageRoute

/-! # Numbered register banks of a shared rectangle stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage

abbrev Role := ℕ × ℕ × ℕ × ℕ

def label (v : ℕ) : Role := (0,0,v,0)
def endpoint (v b : ℕ) : Role := (1,0,v,b)
def queryEndpoint (j v b : ℕ) : Role := (2,j,v,b)
def rectangle (j b : ℕ) : Role := (3,j,0,b)
def rankTerm (j i k : ℕ) : Role := (4,j,i,k)
def rankRow (j i : ℕ) : Role := (5,j,i,0)
def queryLabel (j v : ℕ) : Role := (6,j,v,0)

/-- A flat geometric frame. Fields are query count, label count, rectangle count,
the side-major incidence mask, and the selected row and column labels. -/
abbrev Frame := ℕ × ℕ × ℕ × List Bool × List ℕ × List ℕ

namespace Frame

def queries (g : Frame) := g.1
def labels (g : Frame) := g.2.1
def boxes (g : Frame) := g.2.2.1
def mask (g : Frame) := g.2.2.2.1
def minor (g : Frame) (side : Bool) := if side then g.2.2.2.2.1 else g.2.2.2.2.2

def incident (g : Frame) (side : Bool) (v b : ℕ) : Bool :=
  (mask g)[(side.toNat*boxes g+b)*labels g+v]?.getD false

def localBoxes (g : Frame) (side : Bool) (v : ℕ) : List ℕ :=
  (List.range (boxes g)).filter (incident g side v)

def labelsBank (g : Frame) : List Role := (List.range (labels g)).map label

def endpoints (g : Frame) (side : Bool) : List Role :=
  (List.range (labels g)).flatMap fun v => (localBoxes g side v).map (endpoint v)

def queryEndpoints (g : Frame) (side : Bool) : List Role :=
  (List.range (queries g)).flatMap fun j =>
    (endpoints g side).map fun (_,_,v,b) => queryEndpoint j v b

def product (n m : ℕ) (f : ℕ → ℕ → Role) : List Role :=
  (List.range n).flatMap fun j => (List.range m).map (f j)

def boxesBank (g : Frame) := product (queries g) (boxes g) rectangle
def rankBank (g : Frame) := product (queries g) (minor g true).length rankRow
def queryBank (g : Frame) := product (queries g) (labels g) queryLabel

def terms (g : Frame) (side : Bool) : List Role :=
  (List.range (queries g)).flatMap fun j =>
    (List.range (minor g side).length).flatMap fun i =>
      let v := (minor g side)[i]?.getD 0
      rankTerm j i 0 :: (localBoxes g side v).map (fun b => rankTerm j i (b+1))

/-- Banks indexed by their position in the stage, including entry and exit. -/
def bank (g : Frame) : ℕ → List Role
  | 0 => labelsBank g
  | 1 => labelsBank g ++ endpoints g false
  | 2 => labelsBank g ++ queryEndpoints g false
  | 3 => labelsBank g ++ boxesBank g
  | 4 => labelsBank g ++ boxesBank g ++ terms g true
  | 5 => labelsBank g ++ boxesBank g ++ rankBank g
  | 6 => labelsBank g ++ boxesBank g ++ terms g false
  | 7 => labelsBank g ++ queryBank g ++ boxesBank g
  | 8 => labelsBank g ++ queryBank g ++ queryEndpoints g true
  | 9 | 10 => labelsBank g ++ endpoints g true
  | _ => labelsBank g

/-- An oriented chart slot. An empty slot denotes the identity move. -/
abbrev Move := Option (Bool × ℕ)

def labelChart (g : Frame) (side : Bool) (j v : ℕ) :=
  (side.toNat*queries g + j)*labels g+v

def commonChart (g : Frame) (j b : ℕ) :=
  2*queries g*labels g + j*boxes g+b

def reserveChart (g : Frame) (side : Bool) (v b : ℕ) :=
  2*queries g*labels g + queries g*boxes g + (side.toNat*labels g+v)*boxes g+b

def localChart (g : Frame) (side : Bool) (j v b : ℕ) :=
  2*queries g*labels g + queries g*boxes g + 2*labels g*boxes g +
    ((side.toNat*queries g+j)*labels g+v)*boxes g+b

/-- The movement of a single output register, indexed by its input boundary.
The Boolean in an occupied slot requests the inverse chart when true. -/
def leg (g : Frame) (stage : ℕ) (out : Role) : Role × Move :=
  let (tag,j,v,b) := out
  match stage,tag with
  | 0,1 => (label v, some (false,reserveChart g false v b))
  | 1,2 => (endpoint v b, some (false,localChart g false j v b))
  | 3,4 =>
    match b with
    | 0 =>
      let w := (minor g true)[v]?.getD 0
      (label w, some (false,labelChart g false j w))
    | b+1 => (rectangle j b, some (false,commonChart g j b))
  | 5,4 =>
    match b with
    | 0 =>
      let w := (minor g false)[v]?.getD 0
      (rankRow j v, some (true,labelChart g true j w))
    | b+1 => (rankRow j v, some (true,commonChart g j b))
  | 7,2 => (rectangle j b,some (true,localChart g true j v b))
  | 9,1 => (endpoint v b,some (true,reserveChart g true v b))
  | _,_ => (out,none)

/-- Expand an abstract matrix register into its ground-ring component rows.
Lane ranks are inner, so all components of one register are contiguous. -/
def route (g : Frame) (lanes n : ℕ) : List (ℕ × Move) :=
  (bank g (n+1)).flatMap fun dest =>
    let (src,move) := leg g n dest
    (List.range lanes).map fun d => ((bank g n).idxOf src * lanes + d,move)

abbrev Table := ℕ × List Role × List Role

def gate (g : Frame) (tag n : ℕ) : Table := (tag,bank g n,bank g (n+1))

/-- The six movement banks and five local tables in their execution order. -/
def script (g : Frame) (lanes : ℕ) : List (InterchangeROM.Instruction Table Move) :=
  [.inr (route g lanes 0),.inr (route g lanes 1),.inl (gate g 0 2),
   .inr (route g lanes 3),.inl (gate g 1 4),.inr (route g lanes 5),
   .inl (gate g 2 6),.inr (route g lanes 7),.inl (gate g 3 8),
   .inr (route g lanes 9),.inl (gate g 4 10)]

/-- Literal programs contain no geometrically impossible incidence leg. -/
theorem endpoint_mem (g : Frame) (side : Bool) (v b : ℕ) :
    endpoint v b ∈ endpoints g side ↔ v < labels g ∧ b < boxes g ∧ incident g side v b := by
  simp [endpoints,localBoxes,endpoint]

theorem queryEndpoint_mem (g : Frame) (side : Bool) (j v b : ℕ) :
    queryEndpoint j v b ∈ queryEndpoints g side ↔
      j < queries g ∧ v < labels g ∧ b < boxes g ∧ incident g side v b := by
  simp [queryEndpoints,endpoints,localBoxes,queryEndpoint,endpoint]

end Frame
end InterchangeROMStage

end NearSquareRoot
end Computability
end OAI
