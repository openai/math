import OAI.Computability.VPVNP.PairSimulationLeafPortWalk
import OAI.Computability.VPVNP.LivePublicCounterOperands
import OAI.Computability.VPVNP.LivePublicVirtualSites

/-!
# Loading the fixed public register vector of an auxiliary leaf

The live program supplies the virtual address width and bucket, its own word
width, the auxiliary clock, and all 34 auxiliary operands. Two of the latter
are taken from the live program's literal prefix. The current leaf address
and its full header word are dynamic and enter through separate registers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSourceLoad

open BurstRAM PrivateRAM RAMTape LiveProgram LeafRegisterBank PrimedCounter.GuessWord
open scoped Fin.CommRing

/-- Fields fixed for all auxiliary leaf visits in one pair invocation. -/
inductive Static (k : ℕ) where
  | d | width | bucket | fuel | operand (i : Fin k)
  deriving DecidableEq, Fintype

variable {k r p pubs w : ℕ}

/-- The register-bank field receiving a fixed scalar or public operand. -/
def Static.dest : Static k → Source k
  | .d => .d | .width => .width | .bucket => .bucket | .fuel => .fuel | .operand i => .operand i

theorem Static.dest_injective : Function.Injective (@Static.dest k) := by
  intro i j h
  cases i <;> cases j <;> simp_all [Static.dest]

/-- Cache order for the four geometry scalars followed by the public operands. -/
def slots (k : ℕ) : List (Static k) := [.d,.width,.bucket,.fuel] ++ (List.finRange k).map .operand

theorem mem_slots (i : Static k) : i ∈ slots k := by cases i <;> simp [slots]

@[simp] theorem length_slots : (slots k).length = 4+k := by simp [slots]; omega

/-- The expression that computes a fixed leaf scalar from the live pair operands. -/
def expr (c : Constants) : Static 34 → InputOperand
  | .d => .geometry (.clog2 virtualSites)
  | .width => .geometry .w
  | .bucket => .geometry (.pow2 (.divConst (.add (.clog2 .n) (.lit 3)) 4))
  | .fuel => .geometry PrimedCounter.virtualFuel
  | .operand i => CounterPublic.operands c i

/-- Update the scalar's destination register while preserving the other registers. -/
def setStatic (ports : Source k ↪ Fin r) (vals : Static k → Word w)
    (bank : Fin r → Word w) (i : Static k) := Function.update bank (ports i.dest) (vals i)

theorem fold_at (ports : Source k ↪ Fin r) (vals : Static k → Word w) (ls : List (Static k))
    (bank : Fin r → Word w) (j : Static k) :
    ls.foldl (setStatic ports vals) bank (ports j.dest) = if j ∈ ls then vals j else bank (ports j.dest) := by
  induction ls generalizing bank with
  | nil => simp
  | cons i ls ih =>
    rw [List.foldl_cons,ih]
    by_cases hi : j = i
    · subst i; simp [setStatic]
    · simp [hi,setStatic,ports.injective.ne (Static.dest_injective.ne hi)]

theorem fold_outside (ports : Source k ↪ Fin r) (vals : Static k → Word w) (ls : List (Static k))
    (bank : Fin r → Word w) (j : Fin r) (h : ∀ i : Static k, j ≠ ports i.dest) :
    ls.foldl (setStatic ports vals) bank j = bank j := by
  induction ls generalizing bank with
  | nil => rfl
  | cons i ls ih => simp only [List.foldl_cons, ih, setStatic, Function.update_of_ne (h i)]

/-- The field's offset in the private scalar cache. -/
def Static.offset : Static k → ℕ
  | .d => 0 | .width => 1 | .bucket => 2 | .fuel => 3 | .operand i => 4+i.val

theorem slots_offsets : (slots k).map Static.offset = List.range (4+k) := by
  rw [List.range_add]
  simp only [slots, List.map_append, List.map_cons, List.map_nil, Static.offset, List.map_map]
  rw [← List.map_coe_finRange_eq_range (n := k), List.map_map]
  rfl

end PairSimulation.LeafSourceLoad

end VPVNP
end Computability
end OAI
