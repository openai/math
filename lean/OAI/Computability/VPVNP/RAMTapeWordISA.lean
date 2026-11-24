import OAI.Computability.VPVNP.RAMTapeWordSimple
import OAI.Computability.VPVNP.RAMTapeWordMul
import OAI.Computability.VPVNP.RAMTapeDivision
import OAI.Computability.VPVNP.RAMTapeWordShift
import OAI.Computability.VPVNP.RAMTapeStackLift

/-!
# Finite stack routines for every binary word instruction

Every routine uses two distinct operand ports and an explicit result port.
Other local stacks start empty. At a successful return every local stack
contains at most one word's worth of bits, so the caller can reclaim all
scratch space in linear time. The port embeddings leave four of sixteen
workspace slots available for operand staging.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace TapeWord

open RAMTape BurstRAM BurstRAM.PrivateRAM

/-- Place the two operand bit strings on their ports and initialize scratch
ports to empty stacks. -/
def operandStacks {K : Type*} [DecidableEq K] (lhs rhs : K) (x y : List Bool) : Stacks K :=
  fun i => if i = lhs then x else if i = rhs then y else []

/-- The finite control table of a binary word routine and its call contract. -/
structure Kernel (op : BinaryOp) where
  /-- Finite type of local bit stacks used by the selected binary word kernel. -/
  K : Type
  /-- Finite control states of the binary word kernel, fixed independently of the operand
  width. -/
  Q : Type
  [decK : DecidableEq K]
  [finK : Fintype K]
  [decQ : DecidableEq Q]
  [finQ : Fintype Q]
  /-- Inject each kernel stack into one of the twelve reserved arithmetic stack positions. -/
  index : K → Fin 12
  index_injective : Function.Injective index
  /-- Local stack initially holding the first operand's little-endian bits. -/
  lhs : K
  /-- Distinct local stack initially holding the second operand's little-endian bits. -/
  rhs : K
  /-- Stack containing the fixed-width opcode result at an accepting return. -/
  out : K
  lhs_ne_rhs : lhs ≠ rhs
  /-- Initial control state for invoking the kernel on its two operand stacks. -/
  entry : Q
  /-- Bit-stack instructions implementing the selected binary operation at every word width. -/
  code : StackCode K Q
  run : ∀ {w : ℕ} (x y : Word w), ∃ (steps : ℕ) (exit : Q) (final : Stacks K),
    steps ≤ 40 * (w + 1)^2 ∧
    StackRuns code steps entry (operandStacks lhs rhs (wordBits x) (wordBits y)) exit final ∧
    code exit = .halt true ∧ final out = wordBits (op.eval x y) ∧ ∀ i, (final i).length ≤ w

attribute [instance] Kernel.decK Kernel.finK Kernel.decQ Kernel.finQ

/-- A successful subroutine halt serves as the caller's return boundary. -/
def Kernel.accepts {op : BinaryOp} (k : Kernel op) (q : k.Q) : Bool :=
  match k.code q with
  | .halt true => true
  | _ => false

theorem Kernel.accepts_iff {op : BinaryOp} (k : Kernel op) (q : k.Q) :
    k.accepts q = true ↔ k.code q = .halt true := by
  cases h : k.code q with
  | halt b => cases b <;> simp [Kernel.accepts, h]
  | push | pop | goto | choose => simp [Kernel.accepts, h]

private def scanIndex : ScanPort → Fin 12
  | .left => 0
  | .right => 1
  | .tmp => 2
  | .out => 3

private def scanKernel (op : ScanOp) : Kernel op.opcode where
  K := ScanPort
  Q := ScanState
  index := scanIndex
  index_injective := by intro i j h; cases i <;> cases j <;> simp_all [scanIndex]
  lhs := .left
  rhs := .right
  out := .out
  lhs_ne_rhs := by decide
  entry := .left false
  code := scanCode op.step
  run := by
    intro w x y
    refine ⟨5 * w + 2, .done (scan op.step false (wordBits x) (wordBits y)).2,
      scanStacks [] [] [] (wordBits (op.opcode.eval x y)), ?_, ?_, rfl, rfl, ?_⟩
    · ring_nf; omega
    · convert op.word_run x y using 1
      funext i; cases i <;> rfl
    · intro i; cases i <;> simp [scanStacks]

private def mulIndex : Mul.Reg → Fin 12
  | .multiplicand => 0
  | .multiplier => 1
  | .accumulator => 2
  | .shifted => 3
  | .sum => 4

private def mulKernel : Kernel .mul where
  K := Mul.Reg
  Q := Mul.State
  index := mulIndex
  index_injective := by intro i j h; cases i <;> cases j <;> simp_all [mulIndex]
  lhs := .multiplicand
  rhs := .multiplier
  out := .accumulator
  lhs_ne_rhs := by decide
  entry := .init
  code := Mul.code
  run := by
    intro w x y
    refine ⟨8 * w ^ 2 + 9 * w + 4, .done,
      Mul.store [] [] (wordBits (BinaryOp.mul.eval x y)) [] [], ?_, ?_, rfl, rfl, ?_⟩
    · ring_nf; omega
    · convert Mul.multiply_word_run x y using 1
      funext i; cases i <;> rfl
    · intro i; cases i <;> simp [Mul.store]

private def divisionIndex : DivisionStack.Port → Fin 12
  | .input => 0
  | .feed => 1
  | .divisor => 2
  | .remainder => 3
  | .quotient => 4
  | .saved => 5
  | .original => 6
  | .difference => 7

private def divisionKernel (quot : Bool) : Kernel (if quot then .div else .mod) where
  K := DivisionStack.Port
  Q := DivisionStack.State
  index := divisionIndex
  index_injective := by intro i j h; cases i <;> cases j <;> simp_all [divisionIndex]
  lhs := .input
  rhs := .divisor
  out := if quot then .quotient else .remainder
  lhs_ne_rhs := by decide
  entry := .reverseInput
  code := DivisionStack.code
  run := by
    intro w x y
    let final : DivisionStack.Data := ⟨[], [], wordBits y, wordBits (BinaryOp.mod.eval x y),
      wordBits (BinaryOp.div.eval x y), [], [], []⟩
    refine ⟨DivisionStack.ticks (wordBits x) (wordBits y), .done, final.stacks,
      ?_, ?_, rfl, ?_, ?_⟩
    · have h := DivisionStack.ticks_le (x := wordBits x) (d := wordBits y) (by simp)
      rw [length_wordBits] at h
      omega
    · convert DivisionStack.divideWordRun x y using 1
      funext i; cases i <;> rfl
    · cases quot <;> rfl
    · intro i; cases i <;> simp [final, DivisionStack.Data.stacks]

private def shiftIndex : Shift.Reg → Fin 12
  | .amount => 0
  | .data => 1
  | .temp => 2
  | .output => 3
  | .scratch => 4

private def shiftKernel (left : Bool) : Kernel (if left then .shiftLeft else .shiftRight) where
  K := Shift.Reg
  Q := Shift.State
  index := shiftIndex
  index_injective := by intro i j h; cases i <;> cases j <;> simp_all [shiftIndex]
  lhs := if left then .temp else .data
  rhs := .amount
  out := if left then .temp else .output
  lhs_ne_rhs := by cases left <;> decide
  entry := .start
  code := Shift.code left
  run := by
    intro w x y
    obtain ⟨steps, bound, run⟩ := Shift.shift_run left x y
    refine ⟨steps, .done, Shift.output left (wordBits ((if left then BinaryOp.shiftLeft else
      BinaryOp.shiftRight).eval x y)), bound, ?_, rfl, ?_, ?_⟩
    · convert run using 1
      funext i
      cases left <;> cases i <;> rfl
    · cases left <;> rfl
    · intro i
      cases left <;> cases i <;> simp [Shift.output, Shift.store]

/-- Select the fixed finite bit-stack implementation of a word RAM opcode. -/
def wordKernel : (op : BinaryOp) → Kernel op
  | .add => scanKernel .add
  | .sub => scanKernel .sub
  | .bitAnd => scanKernel .bitAnd
  | .bitOr => scanKernel .bitOr
  | .bitXor => scanKernel .bitXor
  | .mul => mulKernel
  | .div => divisionKernel true
  | .mod => divisionKernel false
  | .shiftLeft => shiftKernel true
  | .shiftRight => shiftKernel false

theorem wordKernel_entry (op : BinaryOp) :
    (wordKernel op).accepts (wordKernel op).entry = false := by cases op <;> rfl

theorem wordKernel_entry_continues (op : BinaryOp) :
    ((wordKernel op).code (wordKernel op).entry).returns = false := by cases op <;> rfl

end TapeWord

end VPVNP
end Computability
end OAI
