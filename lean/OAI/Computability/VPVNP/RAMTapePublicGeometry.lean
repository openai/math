import OAI.Computability.VPVNP.RAMTapePublicExprArithmetic
import OAI.Computability.VPVNP.RAMTapeUnaryWord
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-!
# Converting the physical geometry tallies into public RAM words

The processor supplies four unary stacks and a persistent width-sized zero
template. For each field, copy the zero template into the destination, save
the field's unary marks, and increment the destination word once per mark.
All four source tallies and the template remain available to the processor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.PublicGeometry

open BurstRAM LiveProgram PublicExprMachine

/-- Stack labels for four unary geometry tallies, their corresponding word outputs, a zero
template, and conversion scratch. -/
inductive Port where
  | unary (i : Fin 4) | word (i : Fin 4) | zeros | pending | tmp
  deriving DecidableEq, Fintype

private def counterPorts (i : Fin 4) : UnaryWord.Port → Port
  | .src => .unary i
  | .pending => .pending
  | .number => .word i
  | .unit => .zeros
  | .tmp => .tmp

private theorem counterPorts_inj (i : Fin 4) : Function.Injective (counterPorts i) := by
  intro a b h
  cases a <;> cases b <;> simp_all [counterPorts]

private def count (i : Fin 4) : FiniteRoutine Port :=
  FiniteRoutine.ofStackCode (UnaryWord.code 0) (counterPorts i) .count (· == .done)

private def field (i : Fin 4) : FiniteRoutine Port :=
  ((SuccessorFields.prependCopy .zeros (.word i) .tmp).followedBy
    (SuccessorFields.prependCopy (.unary i) .pending .tmp)).followedBy (count i)

private def bank (g : Geometry) (done : ℕ) : Stacks Port
  | .unary j => List.replicate (geometryNat g j) true
  | .word j => if j.val < done then wordBits (geometryWords g j) else []
  | .zeros => List.replicate g.w false
  | .pending | .tmp => []

/-- Geometry-conversion bank before any of the four unary fields has been converted to a word. -/
def initial (g : Geometry) : Stacks Port := bank g 0

/-- Bank containing all four packed geometry words and the original tallies and zero template. -/
def result (g : Geometry) : Stacks Port
  | .word j => wordBits (geometryWords g j)
  | j => initial g j

private def work (w v : ℕ) := (5*w+2) + (5*v+2) + (v*(4*w+3)+1)

private theorem field_runs (g : Geometry) (i : Fin 4) (hfit : geometryNat g i < 2^g.w) :
    (field i).Runs (work g.w (geometryNat g i)) (bank g i.val) (bank g (i.val+1)) := by
  let v := geometryNat g i
  let z := List.replicate g.w false
  let marks := List.replicate v true
  let s := bank g i.val
  let allocated := Function.update s (.word i) z
  let ready := Function.update allocated Port.pending marks
  have hz := SuccessorFields.prependCopy_runs Port.zeros (.word i) .tmp (by simp) (by decide) (by simp) s rfl
  have halloc : (SuccessorFields.prependCopy .zeros (.word i) .tmp).Runs (5*g.w+2) s allocated := by
    simpa [s, allocated, bank, z] using hz
  have hs := SuccessorFields.prependCopy_runs (Port.unary i) .pending .tmp (by simp) (by simp) (by decide)
    allocated (by simp [allocated,s,bank])
  have hsave : (SuccessorFields.prependCopy (.unary i) .pending .tmp).Runs (5*v+2) allocated ready := by
    simpa [ready, allocated, s, bank, v, marks] using hs
  have hc : (count i).Runs (v*(4*g.w+3)+1) ready (bank g (i.val+1)) := by
    apply FiniteRoutine.runs_ofStackCode_framed (counterPorts_inj i) (normal := (· == .done))
      rfl rfl (fun q h => by cases q <;> first | rfl | contradiction)
      (UnaryWord.count_fixed 0 g.w v marks z hfit)
    · intro j; cases j <;> simp [counterPorts, ready, allocated, s, bank, marks, v, z, UnaryWord.store]
    · intro j; cases j <;> simp [counterPorts, bank, marks, v, z, UnaryWord.store, geometryWords, packed]
    · intro p hp
      cases p with
      | word j =>
        have hn : j ≠ i := by rintro rfl; exact hp .number rfl
        have hv : j.val ≠ i.val := fun h => hn (Fin.ext h)
        have hlt : j.val < i.val + 1 ↔ j.val < i.val := by omega
        simp [ready, allocated, s, bank, hn, hlt]
      | unary j | zeros => simp [ready, allocated, s, bank]
      | pending => exact (hp .pending rfl).elim
      | tmp => exact (hp .tmp rfl).elim
  exact (halloc.followedBy hsave).followedBy hc

/-- The four source fields are prepared in the public operand order. -/
def prepare : FiniteRoutine Port :=
  (((field 0).followedBy (field 1)).followedBy (field 2)).followedBy (field 3)

/-- Total conversion steps for input length, address width, bucket capacity, and word width. -/
def steps (g : Geometry) := work g.w g.n + work g.w g.d + work g.w g.H + work g.w g.w

theorem steps_le (g : Geometry) :
    steps g ≤ 25 * (g.n+g.d+g.H+g.w+1)*(g.w+1) := by
  unfold steps work
  nlinarith only [Nat.zero_le g.n, Nat.zero_le g.d, Nat.zero_le g.H, Nat.zero_le g.w,
    Nat.zero_le (g.n*g.w), Nat.zero_le (g.d*g.w), Nat.zero_le (g.H*g.w), Nat.zero_le (g.w*g.w)]

theorem runs (g : Geometry) (hfit : ∀ i, geometryNat g i < 2^g.w) :
    prepare.Runs (steps g) (initial g) (result g) := by
  have finish : bank g 4 = result g := by
    funext p
    cases p with
    | word j => simp [result, bank, j.isLt]
    | unary | zeros | pending | tmp => rfl
  rw [← finish]
  exact (((field_runs g 0 (hfit 0)).followedBy (field_runs g 1 (hfit 1))).followedBy
    (field_runs g 2 (hfit 2))).followedBy (field_runs g 3 (hfit 3))

end RAMTape.PublicGeometry

end VPVNP
end Computability
end OAI
