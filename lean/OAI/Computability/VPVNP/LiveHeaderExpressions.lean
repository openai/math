import OAI.Computability.VPVNP.LivePublicExpr
import OAI.Computability.VPVNP.LiveHeaderProgram

/-!
# Arithmetic expressions for the complete live header operand bank

Only the four inputs of the physical site reader and fixed constants appear
in these expressions. Their values include the nested stage tag address,
all source and destination buffer addresses, and the public scan limits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram
open LiveHeaderSchedule LiveHeaderWidths LiveHeaderDescriptors

instance : Add PublicExpr := ⟨PublicExpr.add⟩
instance : Mul PublicExpr := ⟨PublicExpr.mul⟩
instance (n : ℕ) : OfNat PublicExpr n := ⟨PublicExpr.lit n⟩

@[simp] theorem eval_add (g : Geometry) (a b : PublicExpr) : (a+b).eval g = a.eval g + b.eval g := rfl
@[simp] theorem eval_mul (g : Geometry) (a b : PublicExpr) : (a*b).eval g = a.eval g * b.eval g := rfl
@[simp] theorem eval_numeral (g : Geometry) (n : ℕ) : (OfNat.ofNat n : PublicExpr).eval g = n := rfl

/-- The five public size expressions used to allocate and parameterize live-header storage for
any processor geometry. -/
structure Lengths where
  /-- The public expression for the chain-height parameter used in group and cut numbering. -/
  h : PublicExpr
  /-- The public expression for the basic cut width used in the exterior and padding
  capacities. -/
  delta : PublicExpr
  /-- The public expression for the number of distributed advice bits. -/
  advice : PublicExpr
  /-- The public expression for the serialized exponent field length. -/
  e : PublicExpr
  /-- The public expression for the serialized evaluator configuration length. -/
  config : PublicExpr

/-- Evaluate the five public header dimensions at the supplied geometry. -/
def Lengths.eval (s : Lengths) (g : Geometry) : Sizes :=
  ⟨s.h.eval g, s.delta.eval g, s.advice.eval g, s.e.eval g, s.config.eval g⟩

namespace HeaderLayout

/-- The maximum scan length allocated to the requested incident field. -/
def capacity (s : Lengths) : Field → PublicExpr
  | .exterior | .padding => (s.h+1)*s.delta
  | .exponents => s.e
  | .config => s.config

/-- The workspace address holding the computed cut width for one of the five live or primed
slots. -/
def width (b : PublicExpr) : Slot → PublicExpr
  | .liveLeft => b+1 | .liveRight => b+2 | .primedLeft => b+3 | .primedMiddle => b+4 | .primedRight => b+5

/-- The workspace address holding the selected group-phase flag. -/
def flag (b : PublicExpr) : Flag → PublicExpr
  | .first => b+6 | .middle => b+7 | .firstHalf => b+8 | .last => b+9

/-- The workspace cell marking the first evaluator group. -/
def firstTail (b : PublicExpr) := b+10
/-- The workspace cell holding the selected unit, pair, or tail mode. -/
def mode (b : PublicExpr) := b+11
/-- The shared descriptor cell holding the next incident field's source offset. -/
def offset (b : PublicExpr) := b+12
/-- The shared descriptor cell holding the next incident field's live length. -/
def count (b : PublicExpr) := b+13
/-- The workspace cell carrying the borrow while constructing primed group indices. -/
def borrow (b : PublicExpr) := b+14
/-- The base address of the unpacked one-based group index. -/
def index (b : PublicExpr) := b+15
/-- The cell after the group-index array storing the position of its highest set bit. -/
def high (s : Lengths) (b : PublicExpr) := index b+(s.h+2)
/-- The cell storing the number of set bits in the group index. -/
def population (s : Lengths) (b : PublicExpr) := high s b+1
/-- The base of the unpacked left primed group index. -/
def leftIndex (s : Lengths) (b : PublicExpr) := population s b+1
/-- The base of the unpacked right primed group index, following the left index array. -/
def rightIndex (s : Lengths) (b : PublicExpr) := leftIndex s b+(s.h+2)
/-- The distributed advice array's base following both primed index arrays. -/
def advice (s : Lengths) (b : PublicExpr) := rightIndex s b+(s.h+2)

/-- The base of the selected side's exterior payload, with a full reserved interval per side. -/
def exterior (s : Lengths) (b : PublicExpr) : Side → PublicExpr
  | .left => advice s b+s.advice
  | .right => advice s b+s.advice+capacity s .exterior

/-- The base of the selected side's exponent buffer following both exterior reservations. -/
def exponent (s : Lengths) (b : PublicExpr) : Side → PublicExpr
  | .left => exterior s b .right+capacity s .exterior
  | .right => exterior s b .right+capacity s .exterior+s.e

/-- The base of the selected side's evaluator configuration buffer following the exponent
buffers. -/
def config (s : Lengths) (b : PublicExpr) : Side → PublicExpr
  | .left => exponent s b .right+s.e
  | .right => exponent s b .right+s.e+s.config

/-- The exclusive end of the live-header workspace, immediately after the right configuration
buffer. -/
def limit (s : Lengths) (b : PublicExpr) := config s b .right + s.config

/-- The destination base for a side's payload field, using zero as the unused operand of a
padding check. -/
def dest (s : Lengths) (b : PublicExpr) (side : Side) : Field → PublicExpr
  | .exterior => exterior s b side
  | .exponents => exponent s b side
  | .config => config s b side
  | .padding => 0

/-- Assemble the selected header stage's public operand expressions from the size parameters
and workspace layout. -/
def row (s : Lengths) (b : PublicExpr) (st : LiveHeaderSchedule.Stage) : List PublicExpr :=
  let widthInputs (out : PublicExpr) := [s.h+1,s.delta,high s b,population s b,out,index b]
  let groupInputs := [index b,leftIndex s b,rightIndex s b,borrow b]
  match st with
    | .index => [index b,high s b,population s b,s.h+2]
    | .advice => [0,advice s b,s.advice]
    | .width slot => widthInputs (width b slot)
    | .flag f => widthInputs (flag b f)
    | .firstTail => widthInputs (firstTail b)
    | .mode => [width b .liveLeft,width b .liveRight,flag b .firstHalf,mode b]
    | .primedInit => groupInputs
    | .primedDigits => groupInputs ++ [s.h+1]
    | .descriptor side _ => [width b (if side = .left then .liveLeft else .liveRight),mode b,flag b .firstHalf,
        firstTail b,s.delta,s.e,s.config,offset b,count b]
    | .scan side f => [0,offset b,dest s b side f,count b] ++ List.replicate 12 0 ++ [capacity s f]

private theorem row_value (s : Lengths) (b : PublicExpr) (g : Geometry) (st : LiveHeaderSchedule.Stage)
    (j : Fin 17) : (((row s b st)[j.val]?).getD 0).eval g =
      LiveHeaderProgram.publicRow (s.eval g) (b.eval g) st j := by
  have lookup (l : List PublicExpr) (i : ℕ) : ((l[i]?).getD 0).eval g =
      ((l.map (PublicExpr.eval g))[i]?).getD 0 := by
    rw [List.getElem?_map]; cases l[i]? <;> rfl
  rw [lookup]
  cases st <;> first | (rename_i a; cases a <;> rfl) | (rename_i a f; cases a <;> cases f <;> rfl) | rfl

/-- Flatten the fixed 31 rows, appending the address of the header-stage tag. -/
def operands (s : Lengths) (b : PublicExpr) : Fin (LiveHeaderSchedule.stages.length*17+1) → PublicExpr :=
  Fin.snoc (fun j : LiveHeaderProgram.PublicIndex =>
    let p := finProdFinEquiv.symm j
    ((row s b (LiveHeaderProgram.stage p.1))[p.2.val]?).getD 0) b

/-- The expression bank instantiates precisely the native header's ABI. -/
theorem operands_eq (g : Geometry) (s : Lengths) (b : PublicExpr) (i : Fin (LiveHeaderSchedule.stages.length*17+1)) :
    Fin.ofNat (2^g.w) ((operands s b i).eval g) = LiveHeaderProgram.publicData g.w (s.eval g) (b.eval g) i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [operands,LiveHeaderProgram.publicData,LiveStageLink.publicData]
  · simp only [operands,LiveHeaderProgram.publicData,LiveStageLink.publicData,Fin.snoc_castSucc,row_value]

end HeaderLayout
end LiveProgram

end VPVNP
end Computability
end OAI
