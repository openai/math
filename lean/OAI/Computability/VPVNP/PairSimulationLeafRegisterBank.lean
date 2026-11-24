import OAI.Computability.VPVNP.PairSimulationLeafFill
import OAI.Computability.VPVNP.PairSimulationLeafFieldCode

/-! # Register wiring between the virtual validator's operand staging and scalar fill loop -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafRegisterBank

open RAMTape BurstRAM PrivateRAM LeafStartup StackMachine
open scoped Fin.CommRing

variable {K : Type} {k r : ℕ}

/-- Input register names for the site dimensions, bucket, fuel, address and words, and the
virtual machine's public operands. -/
inductive Source (k : ℕ) where
  | d | width | bucket | fuel | address | initial | header | operand (i : Fin k)
  deriving DecidableEq, Fintype

/-- The combined scalar-loader register bank, with fill-loop registers and a separate bank of
source words. -/
abbrev Reg (K : Type) (k : ℕ) := LeafFill.Reg K ⊕ Source k

/-- Physical embedding of the fill-loop registers in the combined scalar-loader bank. -/
def load (reg : Reg K k ↪ Fin r) : LeafFill.Reg K ↪ Fin r :=
  ⟨fun j => reg (.inl j),fun _ _ h => Sum.inl.inj (reg.injective h)⟩

/-- Wire each staging register to its scalar source, fill destination, or shared stack constant
and temporary. -/
def stagingName : Staging.Reg k → Reg K k
  | .out .len => .inl .length
  | .out .value => .inl .value
  | .out .tmp => .inl (.pointers (.stack .tmp))
  | .zero => .inl (.pointers (.stack .zero))
  | .one => .inl (.pointers (.stack .one))
  | .d => .inr .d
  | .width => .inr .width
  | .bucket => .inr .bucket
  | .fuel => .inr .fuel
  | .address => .inr .address
  | .initial => .inr .initial
  | .header => .inr .header
  | .operand i => .inr (.operand i)

private theorem stagingName_injective : Function.Injective (stagingName (K := K) (k := k)) := by
  intro a b h
  cases a <;> cases b <;> (try casesm* Staging.Out) <;> simp_all [stagingName]

/-- The injective host placement of staging registers induced by their wiring into the
scalar-loader bank. -/
def stage (reg : Reg K k ↪ Fin r) : Staging.Reg k ↪ Fin r :=
  ⟨fun j => reg (stagingName j),reg.injective.comp stagingName_injective⟩

@[simp] theorem load_at (reg : Reg K k ↪ Fin r) (j : LeafFill.Reg K) : load reg j = reg (.inl j) := rfl

@[simp] theorem stage_at (reg : Reg K k ↪ Fin r) (j : Staging.Reg k) : stage reg j = reg (stagingName j) := rfl

/-- Physical placement of the validator's stack registers in the scalar-loader bank. -/
abbrev stack (reg : Reg K k ↪ Fin r) := LeafFill.stack (load reg)

theorem preserved (reg : Reg K k ↪ Fin r) (j : Register K) (hj : j ≠ .tmp) (o : Staging.Out) :
    stack reg j ≠ stage reg (.out o) := by cases o <;> simp [stack,stagingName,hj]

variable {w p : ℕ}

/-- Staging writes only three scratch registers. The entire logical stack
bank therefore retains its private cells and pointers. -/
theorem staged_represents (reg : Reg K k ↪ Fin r) (L : Layout K w) (s : Stacks K)
    (ls : List (Staging.Line k)) (pc : Fin p) (c : Config w p r) (rep : Represents L (stack reg) c s) :
    Represents L (stack reg) {c with pc := pc,reg := ls.foldl (Staging.applyPhysical (stage reg)) c.reg} s := by
  have keep (j : Register K) (hj : j ≠ .tmp) := Staging.physical_outside (stage reg) ls c.reg _
    (preserved reg j hj)
  exact ⟨(keep .one nofun).trans rep.unit,(keep .zero nofun).trans rep.zero,
    fun a => (keep (.base a) nofun).trans (rep.bases a), fun a => (keep (.top a) nofun).trans (rep.tops a),rep.cells⟩

end PairSimulation.LeafRegisterBank

end VPVNP
end Computability
end OAI
