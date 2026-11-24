import OAI.Computability.VPVNP.AffinePinTable
import OAI.Computability.VPVNP.AffinePinBlocks
import OAI.Computability.VPVNP.SliceArithmeticCallClear

/-! # Reading the pinned coordinate and classifying its exponent -/

namespace OAI
namespace Computability
namespace VPVNP

namespace AffinePin.Stage

open RAMTape

/-- Stacks for decoding the row index, computing offsets, reading the pin mask and scalar
table, and classifying the packed exponent. -/
inductive Port where
  | binary | high | index | wordStride | scalarStride | one | offset | outer | tmp | width
  | mask | values | saved | reversed | active | value | exponents | constant | unit
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Immutable lookup data for the affine pin stage, including the two record widths, membership
mask, and packed field values. -/
structure Advice where
  /-- Number of bits in each coordinate’s exponent word in the packed monomial. -/
  w : ℕ
  /-- Number of bits per field element in the packed table of coordinate values. -/
  scalarWidth : ℕ
  /-- One Boolean flag per coordinate, set precisely for the pinned coordinates in the query
  advice. -/
  mask : List Bool
  /-- Consecutive fixed-width blocks holding the coordinate values in field representation. -/
  values : List Bool

/-- Mutable state of a pin-row query, including the coordinate index, offset, exponent stream,
extracted value, and classification flags. -/
structure Work where
  /-- Binary input word identifying the coordinate whose pin row is being queried. -/
  binary : List Bool := []
  /-- Decoded coordinate index, stored as a unary counter and reused for both pin-table reads. -/
  index : ℕ := 0
  /-- Bit offset to the selected exponent's low bit, represented by one unary mark per bit to
  skip. -/
  offset : ℕ := 0
  /-- Packed exponent words of the queried monomial, consumed while testing for the constant
  and selected-variable monomials. -/
  exponents : List Bool := []
  /-- Output stack for the packed scalar at the selected coordinate in the pin-value table. -/
  value : List Bool := []
  /-- Output stack for the mask bit indicating whether the selected coordinate is pinned. -/
  active : List Bool := []
  /-- Output flag for the constant monomial, set when all bits in the exponent vector are zero. -/
  constant : List Bool := []
  /-- Output flag for the selected variable's monomial, set when its low exponent bit is the
  only bit equal to one. -/
  unit : List Bool := []

/-- Place the pin mask, scalar values and stride markers on their advice stacks and encode the
mutable work fields on the stage's remaining ports. -/
def frame (A : Advice) (s : Work) : Stacks Port
  | .binary => s.binary | .index => List.replicate s.index true | .offset => List.replicate s.offset true
  | .wordStride => List.replicate A.w true | .scalarStride => List.replicate A.scalarWidth true
  | .one => [true] | .mask => A.mask | .values => A.values | .value => s.value | .active => s.active
  | .exponents => s.exponents | .constant => s.constant | .unit => s.unit | _ => []

private def decodePorts : Index.Port → Port
  | .bits => .binary | .high => .high | .index => .index | .tmp => .tmp

private def offsetPorts : Index.OffsetPort → Port
  | .index => .index | .stride => .wordStride | .offset => .offset | .outer => .outer | .tmp => .tmp

private def exponentPorts : Exponents.Port → Port
  | .exponents => .exponents | .offset => .offset | .constant => .constant | .unit => .unit

private def readPorts (scalar : Bool) : Reader.Port → Port
  | .index => .index | .stride => if scalar then .scalarStride else .one
  | .offset => .offset | .outer => .outer | .tmp => .tmp | .width => .width
  | .src => if scalar then .values else .mask | .saved => .saved | .reversed => .reversed
  | .out => if scalar then .value else .active

/-- Decode the coordinate, classify its queried monomial, read its mask bit and packed pin
value, and clear the unary index. -/
def machine : FiniteRoutine Port :=
  (((((Index.decode.onPorts decodePorts).followedBy (Index.scale.onPorts offsetPorts)).followedBy
    (Exponents.machine.onPorts exponentPorts)).followedBy (Reader.machine.onPorts (readPorts false))).followedBy
    (Reader.machine.onPorts (readPorts true))).followedBy (SliceArithmetic.CallClear.clear .index)

/-- Step bound for a stage call at row `i`, covering its binary decoding, exponent-offset
calculation, scan of `n` exponent bits, two table reads and index cleanup. -/
def cost (rowWidth i w scalarWidth n : ℕ) : ℕ :=
  7*i+6*rowWidth+2 + (i*(5*w+6)+2) + (2*n+5) + Reader.cost i 1 + Reader.cost i scalarWidth + (i+1)

/-- The tables and width markers are retained. The row word, exponent vector,
unary row index and all other scratch are consumed or reclaimed. -/
theorem machine_runs (A : Advice) (xs pre : List Bool) (b : Bool) (post : List Bool) (i : ℕ)
    (hi : TapeWord.value xs = i) (hpre : pre.length = i*A.w)
    (hm : i+1 ≤ A.mask.length) (hv : i*A.scalarWidth+A.scalarWidth ≤ A.values.length) :
    let input := pre ++ b::post
    let k := Exponents.classify pre b post
    let ready : Work := {binary := xs, exponents := input}
    let final : Work := {
      active := (A.mask.drop i).take 1
      value := (A.values.drop (i*A.scalarWidth)).take A.scalarWidth
      constant := [decide (k = .constant)]
      unit := [decide (k = .unit)] }
    ∃ steps ≤ cost xs.length i A.w A.scalarWidth input.length, machine.Runs steps (frame A ready) (frame A final) := by
  dsimp only
  let input := pre ++ b::post
  let k := Exponents.classify pre b post
  let s₀ : Work := {binary := xs, exponents := input}
  let s₁ : Work := {index := i, exponents := input}
  let s₂ : Work := {s₁ with offset := i*A.w}
  let s₃ : Work := {index := i, constant := [decide (k = .constant)], unit := [decide (k = .unit)]}
  let s₄ := {s₃ with active := (A.mask.drop i).take 1}
  let s₅ := {s₄ with value := (A.values.drop (i*A.scalarWidth)).take A.scalarWidth}
  obtain ⟨u,hu,ud⟩ := Index.decode_runs xs
  rw [hi] at hu ud
  have decode : (Index.decode.onPorts decodePorts).Runs u (frame A s₀) (frame A s₁) := by
    apply FiniteRoutine.runs_onPorts_framed _ (by decide) ud
    · intro p; cases p <;> rfl
    · intro p; cases p <;> rfl
    · intro p hp; cases p <;> first | rfl | exact (hp .bits rfl).elim | exact (hp .index rfl).elim
  have offset : (Index.scale.onPorts offsetPorts).Runs (i*(5*A.w+6)+2) (frame A s₁) (frame A s₂) := by
    apply FiniteRoutine.runs_onPorts_framed _ (by decide) (Index.scale_runs i A.w)
    · intro p; cases p <;> rfl
    · intro p; cases p <;> rfl
    · intro p hp; cases p <;> first | rfl | exact (hp .offset rfl).elim
  have classify : (Exponents.machine.onPorts exponentPorts).Runs (2*pre.length+post.length+5)
      (frame A s₂) (frame A s₃) := by
    have ex := Exponents.machine_runs pre b post [] []
    rw [hpre] at ex
    rw [hpre]
    apply FiniteRoutine.runs_onPorts_framed _ (by decide) ex
    · intro p; cases p <;> rfl
    · intro p; cases p <;> rfl
    · intro p hp; cases p <;> first | rfl | exact (hp .offset rfl).elim | exact (hp .exponents rfl).elim | exact (hp .constant rfl).elim | exact (hp .unit rfl).elim
  have mask : (Reader.machine.onPorts (readPorts false)).Runs (Reader.cost i 1) (frame A s₃) (frame A s₄) := by
    have r := Reader.machine_runs A.mask [] i 1 (by simpa using hm)
    simp only [Nat.mul_one, List.append_nil] at r
    apply FiniteRoutine.runs_onPorts_framed _ (by decide) r
    · intro p; cases p <;> rfl
    · intro p; cases p <;> rfl
    · intro p hp; cases p <;> first | rfl | exact (hp .out rfl).elim
  have value : (Reader.machine.onPorts (readPorts true)).Runs (Reader.cost i A.scalarWidth)
      (frame A s₄) (frame A s₅) := by
    have r := Reader.machine_runs A.values [] i A.scalarWidth hv
    rw [List.append_nil] at r
    apply FiniteRoutine.runs_onPorts_framed _ (by decide) r
    · intro p; cases p <;> rfl
    · intro p; cases p <;> rfl
    · intro p hp; cases p <;> first | rfl | exact (hp .out rfl).elim
  have clear := SliceArithmetic.CallClear.clear_runs Port.index (frame A s₅)
  have len : ((frame A s₅) .index).length = i := List.length_replicate
  have upd : Function.update (frame A s₅) .index [] = frame A {s₅ with index := 0} := by
    funext p; cases p <;> rfl
  rw [len, upd] at clear
  refine ⟨_, ?_, ((((decode.followedBy offset).followedBy classify).followedBy mask).followedBy value).followedBy clear⟩
  simp only [cost, List.length_append, List.length_cons]
  omega

end AffinePin.Stage

end VPVNP
end Computability
end OAI
