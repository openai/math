import OAI.Computability.BorderVNP.DiagonalTallyPacketLookupLoop
import OAI.Computability.BorderVNP.RoutingISATableState

/-!
# Emitting physical packet lookup operands from the owned triples

The ownership scan emits triples (packet base, selector number, vertex number). The first
native loop writes a begin/end pair for each row. The second resolves each digit's
fixed recipe into a literal word address or a relative packet address.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyPacketEmit

open VPVNP.BurstRAM RoutingISA

/-- The frame fields for the generated operand vectors. -/
structure Frame where
  /-- The number of owned packet vertices. -/
  count : ℕ
  /-- First input triple. -/
  triples : ℕ
  /-- Start of fixed relative recipes indexed by selector, vertex and digit. -/
  recipes : ℕ
  /-- First generated absolute bit reference. -/
  refs : ℕ
  /-- First generated row descriptor. -/
  descriptors : ℕ
  /-- Word holding literal zero. -/
  zeroAddr : ℕ
  /-- Word holding literal one. -/
  oneAddr : ℕ
  /-- Digits in every fixed lookup argument. -/
  width : ℕ
  /-- Cardinality of the cube vertex alphabet. -/
  vertices : ℕ

/-- Initial values of the native frame fields. -/
def Frame.resident (f : Frame) (pub : Arg → ℕ) (m : ℕ → ℕ) : Prop :=
  let a := pub 0
  m (a+46) = f.count ∧ m (a+78) = f.triples ∧ m (a+79) = f.recipes ∧
    m (a+80) = f.refs ∧ m (a+45) = f.descriptors ∧ m (a+81) = f.zeroAddr ∧
    m (a+82) = f.oneAddr ∧ m (a+83) = f.width ∧ m (a+84) = f.vertices

/-- Shared row-major recipe location for the selected cube vertex and digit. -/
def Frame.recipeAddr (f : Frame) (m : ℕ → ℕ) (i j : ℕ) : ℕ :=
  f.recipes+(m (f.triples+3*i+1)*f.vertices+m (f.triples+3*i+2))*f.width+j

/-- Address represented by one code from the fixed finite recipe table. -/
def Frame.resolve (f : Frame) (base code : ℕ) : ℕ :=
  if code=0 then f.zeroAddr else if code=1 then f.oneAddr else base+(code-2)

/-- Result of the absolute-address computation for one flattened reference. -/
def Frame.refValue (f : Frame) (m : ℕ → ℕ) (k : ℕ) : ℕ :=
  f.resolve (m (f.triples+3*(k/f.width))) (m (f.recipeAddr m (k/f.width) (k%f.width)))

/-- Word of the flattened begin/end descriptor array. -/
def Frame.descValue (f : Frame) (k : ℕ) : ℕ := f.refs+(k/2+k%2)*f.width

/-- A prefix of an output array as an actual memory update. -/
def written (dst : ℕ) (output : ℕ → ℕ) (m : ℕ → ℕ) (n a : ℕ) : ℕ :=
  if dst ≤ a ∧ a-dst<n then output (a-dst) else m a

theorem written_at (dst : ℕ) (output m : ℕ → ℕ) {n i : ℕ} (hi : i<n) :
    written dst output m n (dst+i) = output i := by simp [written,hi]

theorem written_before (dst : ℕ) (output m : ℕ → ℕ) {n i : ℕ} (hi : i<dst) :
    written dst output m n i = m i := by simp [written,Nat.not_le_of_lt hi]

/-- The next word write extends the physical prefix by one. -/
theorem written_step (dst : ℕ) (out m : ℕ → ℕ) (i : ℕ) :
    Function.update (written dst out m i) (dst+i) (out i) = written dst out m (i+1) := by
  funext a
  by_cases he : a=dst+i
  · subst a; simp [written]
  · rw [Function.update_of_ne he]
    unfold written; split_ifs <;> first | rfl | omega

/-- Read the native directory and prepare both flattened loop bounds. -/
def setup : Code := .block [
  .constant 0 0,.constant 1 1,.constant 2 2,.constant 3 3,
  readFrame 4 62 63 46,readFrame 5 62 63 78,readFrame 6 62 63 79,readFrame 7 62 63 80,
  readFrame 8 62 63 45,readFrame 9 62 63 81,readFrame 10 62 63 82,readFrame 11 62 63 83,
  readFrame 12 62 63 84,.binary .add 13 4 4,.binary .mul 14 4 11,.copy 15 0]

/-- One half of a row descriptor: use the row number and side to compute its begin or end. -/
def descStep : Code := .block [
  .binary .div 16 15 2,.binary .mod 17 15 2,.binary .add 16 16 17,.binary .mul 16 16 11,
  .binary .add 16 7 16,.binary .add 17 8 15,.store 17 16,.binary .add 15 15 1]

/-- Use the flattened reference index to locate its triple and selected recipe slot. -/
def selectRef : Code := .block [
  .binary .div 16 15 11,.binary .mod 17 15 11,.binary .mul 16 3 16,.binary .add 16 5 16,
  .load 18 16,.binary .add 16 16 1,.load 19 16,.binary .add 16 16 1,.load 20 16,
  .binary .mul 19 19 12,.binary .add 19 19 20,.binary .mul 19 19 11,
  .binary .add 19 6 19,.binary .add 19 19 17,.load 21 19]

/-- Relocate a literal or relative packet address according to the static recipe. -/
def resolveRef : Code := .ifEq 21 0 (.copy 22 9) (.ifEq 21 1 (.copy 22 10)
  (.seq (.binary .sub 22 21 2) (.binary .add 22 18 22)))

/-- Store the computed absolute address and advance the flattened reference cursor. -/
def storeRef : Code := .block [.binary .add 23 7 15,.store 23 22,.binary .add 15 15 1]

/-- Compute and write the next actual packet argument source. -/
def refStep : Code := .seq selectRef (.seq resolveRef storeRef)

/-- Produce all reference operands from the triples, before reading the selected IDs. -/
def emitReferences : Code := .block [setup,.whileLt 15 13 descStep,.copy 15 0,.whileLt 15 14 refStep]

/-- The immutable source tables precede both outputs, and all reached addresses fit
the actual word space. The directory's fixed recipe contents can be shared among all teams. -/
structure Frame.Fits (f : Frame) (m : ℕ → ℕ) (w frame : ℕ) : Prop where
  /-- Full runtime frame is below the fresh arrays. -/
  frameBefore : frame+85 ≤ f.descriptors
  /-- The triple stream is below the generated descriptors. -/
  triplesBefore : f.triples+3*f.count ≤ f.descriptors
  /-- Every needed fixed recipe entry is below the generated descriptors. -/
  recipesBefore : ∀ i < f.count, ∀ j < f.width, f.recipeAddr m i j < f.descriptors
  /-- The two distinct output arrays are in increasing order. -/
  outputs : f.descriptors+2*f.count ≤ f.refs
  /-- The final output sentinel fits. -/
  room : f.refs+f.count*f.width < 2^w
  /-- Packet-relative physical bit addresses fit, including those from delivered triples. -/
  digit : ∀ k < f.count*f.width, f.refValue m k < 2^w
  /-- Every selected slice number fits, including when the cube table has no lookup digits. -/
  slice : ∀ i < f.count, m (f.triples+3*i+1)*f.vertices+m (f.triples+3*i+2) < 2^w

/-- Loop registers shared by the two consecutive table writers. -/
structure State (f : Frame) (i : ℕ) (z : NatState) : Prop where
  zeroEq : z.reg 0 = 0
  oneEq : z.reg 1 = 1
  twoEq : z.reg 2 = 2
  threeEq : z.reg 3 = 3
  count : z.reg 4 = f.count
  triples : z.reg 5 = f.triples
  recipes : z.reg 6 = f.recipes
  refs : z.reg 7 = f.refs
  descriptors : z.reg 8 = f.descriptors
  zeroAddr : z.reg 9 = f.zeroAddr
  oneAddr : z.reg 10 = f.oneAddr
  width : z.reg 11 = f.width
  vertices : z.reg 12 = f.vertices
  numDesc : z.reg 13 = 2*f.count
  numRefs : z.reg 14 = f.count*f.width
  cursor : z.reg 15 = i

/-- Equality of the protected frame registers suffices to retain the whole loop state. -/
theorem State.preserve {f : Frame} {i j : ℕ} {z z' : NatState} (hs : State f i z)
    (h : ∀ r : Reg, r.val < 15 → z'.reg r = z.reg r) (hj : z'.reg 15 = j) : State f j z' := by
  constructor
  all_goals first | exact hj | rw [h _ (by decide)]; first
    | exact hs.zeroEq | exact hs.oneEq | exact hs.twoEq | exact hs.threeEq | exact hs.count
    | exact hs.triples | exact hs.recipes | exact hs.refs | exact hs.descriptors
    | exact hs.zeroAddr | exact hs.oneAddr | exact hs.width | exact hs.vertices
    | exact hs.numDesc | exact hs.numRefs

/-- One descriptor step reaches the exact new prefix. -/
theorem descStep_runs {w : ℕ} (f : Frame) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (orig : ℕ → ℕ) (i : ℕ) (hi : i<2*f.count)
    (fit : f.Fits orig w (pub 0).val) (state : State f i (.ofWords s m))
    (mem : readings m = written f.descriptors f.descValue orig i) :
    BoundedRun pub mac descStep s m descStep.slots (fun z => State f (i+1) z ∧
      z.mem = written f.descriptors f.descValue orig (i+1)) := by
  let z := NatState.ofWords s m
  change State f i z at state
  have initial := state
  obtain ⟨_,h1,h2,_,_,_,_,h7,h8,_,_,h11,_,_,_,h15⟩ := state
  have divBound : i/2+i%2 ≤ f.count := by omega
  have hd := Nat.mul_le_mul_right f.width divBound
  have hw := fit.room
  have hout := fit.outputs
  have safe : descStep.fixedSafe w (readings pub) z := by
    simp [descStep,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,
      Function.update,addressOpFits,addressOp,h1,h2,h7,h8,h11,h15]; omega
  apply (descStep.runFixed pub mac s m safe).mono le_rfl
  intro z' eq
  rw [eq]
  change State f (i+1) (descStep.fixedEval (readings pub) z) ∧
    (descStep.fixedEval (readings pub) z).mem = _
  constructor
  · apply State.preserve (i := i) (z := z) (by assumption)
    · exact Code.fixedEval_protected _ _ _ (show descStep.protects 15 = true by decide)
    · simp [descStep,Code.block,Code.fixedEval,Code.evalNat,Function.update,addressOp,h15,h1]
  · change z.mem = written f.descriptors f.descValue orig i at mem
    simp [descStep,Code.block,Code.fixedEval,Code.evalNat,Function.update,addressOp,h2,h7,h8,h11,h15]
    rw [mem]
    exact written_step _ _ _ _

end DiagonalTallyPacketEmit

end BorderVNP
end Computability
end OAI
