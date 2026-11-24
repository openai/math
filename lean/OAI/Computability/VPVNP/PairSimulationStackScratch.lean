import OAI.Computability.VPVNP.PairSimulationStackFootprint
import OAI.Computability.VPVNP.PairSimulationDFSDecode

/-!
# A stack leaf inside the private DFS workspace

The live pending descriptor addresses lie below the private stack intervals.
A source rejection precludes a successful native call at every instruction
budget. On acceptance the ordered writes define an update of the caller's
scratch, including stale cells above the current stack tops.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.StackMachine

open RAMTape BurstRAM BurstRAM.PrivateRAM
open StackCompiler (Reach)
open scoped Fin.CommRing
open private guessed_addFuel from OAI.Computability.VPVNP.PairSimulationDFSDecode

variable {w p r k : ℕ} {K Q : Type} {L : Layout K w}
  {reg : Register K ↪ Fin r} {c out : Config w p r}

/-- Update the scratch cells using the complete ordered sequence of pushes.
The value supplied for addresses below the scratch is immaterial. -/
def Footprint.applyScratch (f : Footprint w) (endAddr : ℕ) (s : DFS.Scratch w endAddr) :
    DFS.Scratch w endAddr :=
  fun a => f.applyWrites (fun b => if h : endAddr ≤ b.val then s ⟨b, h⟩ else 0) a.val

theorem Footprint.scratch_applyWrites (f : Footprint w) (endAddr : ℕ) (m : Word w → Word w) :
    DFS.scratch endAddr (f.applyWrites m) = f.applyScratch endAddr (DFS.scratch endAddr m) := by
  funext a
  apply f.applyWrites_congr
  simp [DFS.scratch, a.property]

/-- Every descriptor below the workspace boundary survives the virtual
stack execution at its exact pending address. -/
theorem Frame.keepsPending (frame : Frame L reg c out) {endAddr top : ℕ} {pending : List (Word w)}
    (above : ∀ j, endAddr ≤ L.base j) (htop : top + pending.length = endAddr)
    (pendingRep : DFS.Represents c.privateMem top pending) :
    DFS.Represents out.privateMem top pending := by
  refine ⟨pendingRep.1, fun i => ?_⟩
  refine (frame.memory _ fun j => Or.inl ?_).trans (pendingRep.2 i)
  change ((top + i.val : ℕ) : Word w).val < L.base j
  have h := pendingRep.1
  rw [Fin.val_natCast, Nat.mod_eq_of_lt (by have := i.isLt; omega)]
  have := above j
  have := i.isLt
  omega

/-- Preserve each dispatcher register under the two disjoint assignments
of physical registers. -/
theorem Frame.dfsReg (frame : Frame L reg c out) (dfs : Fin 9 ↪ Fin r)
    (apart : ∀ i j, dfs i ≠ reg j) (i : Fin 9) : out.reg (dfs i) = c.reg (dfs i) :=
  frame.regs _ (fun ⟨j, h⟩ => apart i j h.symm)

variable [DecidableEq K] {M : Machine w p r k} {code : StackCode K Q} {pc : Q → Fin 7 → Fin p}
  {done : Fin p} {q : Q} {s : Stacks K} {fuel : ℕ}

/-- Missing source choices and rejecting source halts both rule out any
successful native execution, including one with a smaller budget than
the stack simulation's advertised clock. -/
theorem rejects_returns (linked : Linked M code pc reg done) (hw : 0 < w)
    (space : ∀ ⦃v u⦄, Reach code q s v u → ∀ j, (u j).length ≤ L.capacity)
    (stops : StopsWithin code fuel q s) (c : Config w p r) (atPC : c.pc = pc q 0)
    (rep : Represents L reg c s) (m : Memory w) (bits : List Bool)
    (bad : acceptPrefix code fuel q s bits = none) : ¬DFS.Returns M c m bits := by
  rintro ⟨f, report, ran⟩
  obtain ⟨trace, correct, consumed⟩ := execute_iff.mp ran
  have large := execute_iff.mpr ⟨guessed_addFuel trace (4 * fuel), correct, consumed⟩
  rw [Nat.add_comm (4 * fuel) f] at large
  have call := parse_native linked hw space fuel f (.inr stops) c atPC rep m bits
  cases h : parse code fuel q s bits with
  | none => simp [NativeCall, h, large] at call
  | some x => cases ok : x.accept with
    | true => simp [acceptPrefix, haltPrefix, h, ok] at bad
    | false => simp [NativeCall, h, ok, large] at call

end PairSimulation.StackMachine

end VPVNP
end Computability
end OAI
