import OAI.Computability.VPVNP.PairNodeChildSlots
import OAI.Computability.VPVNP.PairPendingArguments

/-!
# Native loop control for a placement-fiber argument scan

A three-instruction test exits on an empty row. On a nonempty row it removes
one unit from the child counter and enters the descriptor-address block.
The scan consumes only the supplied argument bits and returns with the
unconsumed suffix and the remaining private memory available.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NodeArguments.ChildScan

open BurstRAM BurstRAM.PrivateRAM Compression LocalHistory CompressorRecords
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.tick ReadPrefix.nil ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices
open private returns_prefix from OAI.Computability.VPVNP.PairSimulationDFSDecode

variable {w p r k a g : ℕ} {M : Machine w p r k} {m : Memory w}

/-- A linked prefix that consumes exactly its own list of choices. -/
def Prefix (M : Machine w p r k) (m : Memory w) (c d : Config w p r)
    (bits : List Bool) (es : List (Event w)) : Prop := ∀ fuel tail,
  execute M.program (fuel + es.length) c m (bits ++ tail) =
    (execute M.program fuel d m tail).map (fun q => ⟨es ++ q.events, q.result⟩)

theorem Prefix.trans {c d z : Config w p r} {xs ys : List Bool} {es fs : List (Event w)}
    (first : Prefix M m c d xs es) (next : Prefix M m d z ys fs) :
    Prefix M m c z (xs ++ ys) (es ++ fs) := by
  intro fuel tail
  rw [List.append_assoc, List.length_append, show fuel + (es.length + fs.length) =
    (fuel + fs.length) + es.length by omega, first _ _, next fuel tail]
  simp [Option.map_map, Function.comp_def, List.append_assoc]

theorem Prefix.returns {c d : Config w p r} {xs : List Bool} {es : List (Event w)}
    (h : Prefix M m c d xs es) (tail : List Bool) :
    DFS.Returns M c m (xs ++ tail) ↔ DFS.Returns M d m tail := returns_prefix (fun f => h f tail)

/-- Slot routines use the first nine registers of the enclosing loop. -/
def slotRegs (reg : Fin 16 ↪ Fin r) : Fin 9 ↪ Fin r := (Fin.castAddEmb 7).trans reg

/-- The loop branches to the address calculation or to its continuation. -/
def guard (pc : Fin 3 → Fin p) (reg : Fin 16 ↪ Fin r) (body ret : Fin p) :
    Fin 3 → Instr w p r k :=
  ![.constant (reg 0) 0 (pc 1), .jumpEq (reg 10) (reg 0) ret (pc 2),
    .binary .sub (reg 10) (reg 10) (reg 3) body]

theorem resize_guard (pc : Fin 3 → Fin p) (reg : Fin 16 ↪ Fin r) (body ret : Fin p) (j : Fin 3) :
    (guard (w := 1) (k := k) pc reg body ret j).resize w = guard pc reg body ret j := by
  fin_cases j <;> rfl

/-- The machine contains the three child-loop guard instructions at the specified counters.
With its unit register set, the guard returns on a zero count or decrements the count and
enters the child body. -/
def GuardLinked (M : Machine w p r k) (pc : Fin 3 → Fin p) (reg : Fin 16 ↪ Fin r)
    (body ret : Fin p) : Prop := ∀ j, M.code (pc j) = guard pc reg body ret j

variable {pc : Fin 3 → Fin p} {reg : Fin 16 ↪ Fin r} {body ret : Fin p}

private theorem step_at (hl : GuardLinked M pc reg body ret) (c : Config w p r) (j : Fin 3)
    (hc : c.pc = pc j) : M.program.step c = (guard pc reg body ret j).run M.publicData c := by
  simp [Machine.program, hc, hl j]

/-- The empty loop exits without consuming a choice or changing the argument buffers. -/
theorem guard_empty (hl : GuardLinked M pc reg body ret) (c : Config w p r) (hc : c.pc = pc 0)
    (hzero : c.reg (reg 10) = 0) (m : Memory w) :
    ∃ d, d.pc = ret ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      (∀ i, i ≠ reg 0 → d.reg i = c.reg i) ∧ Prefix M m c d [] [.tick, .tick] := by
  let c₁ := c.put (pc 1) (reg 0) 0
  let d := {c₁ with pc := ret}
  have h₀ : M.program.step c = .localStep c₁ := step_at hl c 0 hc
  have h₁ : M.program.step c₁ = .localStep d := by
    rw [step_at hl c₁ 1 rfl]
    change CallAction.localStep {c₁ with
      pc := (if c₁.reg (reg 10) = c₁.reg (reg 0) then ret else pc 2)} = _
    simp [c₁, Config.put, hzero, d]
  refine ⟨d, rfl, rfl, rfl, fun i hi => by simp [d, c₁, Config.put, Function.update_of_ne hi], ?_⟩
  exact fun fuel tail => ReadPrefix.execute
    (ReadPrefix.tick h₀ (ReadPrefix.tick h₁ (ReadPrefix.nil _))) fuel tail

/-- For a nonempty child row the guard subtracts one in the word register,
retains the source pointer and enters the single common child body. -/
theorem guard_cons (hl : GuardLinked M pc reg body ret) (c : Config w p r) (hc : c.pc = pc 0)
    (n : ℕ) (hn : n + 1 < 2 ^ w) (hcount : c.reg (reg 10) = ((n + 1 : ℕ) : Word w))
    (hone : c.reg (reg 3) = 1) (m : Memory w) :
    ∃ d, d.pc = body ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      d.reg (reg 10) = (n : Word w) ∧ (∀ i, i ≠ reg 0 → i ≠ reg 10 → d.reg i = c.reg i) ∧
      Prefix M m c d [] [.tick, .tick, .tick] := by
  let c₁ := c.put (pc 1) (reg 0) 0
  let c₂ := {c₁ with pc := pc 2}
  let d := c₂.put body (reg 10) (n : Word w)
  have nz : ((n + 1 : ℕ) : Word w) ≠ 0 := by
    intro eqn
    have h := congrArg Fin.val eqn
    change (n + 1) % (2 ^ w) = 0 at h
    rw [Nat.mod_eq_of_lt hn] at h
    omega
  have h₀ : M.program.step c = .localStep c₁ := step_at hl c 0 hc
  have h₁ : M.program.step c₁ = .localStep c₂ := by
    rw [step_at hl c₁ 1 rfl]
    change CallAction.localStep {c₁ with
      pc := (if c₁.reg (reg 10) = c₁.reg (reg 0) then ret else pc 2)} = _
    have nz' : (n : Word w) + 1 ≠ 0 := by simpa using nz
    simp [c₁, c₂, Config.put, hcount, nz']
  have h₂ : M.program.step c₂ = .localStep d := by
    rw [step_at hl c₂ 2 rfl]
    change CallAction.localStep (c₂.put body (reg 10) (c₂.reg (reg 10) - c₂.reg (reg 3))) = _
    simp [c₂, c₁, Config.put, hcount, hone, d]
  refine ⟨d, rfl, rfl, rfl, Config.put_same .., fun i h₀ h₁ => by
    simp [d, c₂, c₁, Config.put, Function.update_of_ne h₀, Function.update_of_ne h₁], ?_⟩
  exact fun fuel tail => ReadPrefix.execute
    (ReadPrefix.tick h₀ (ReadPrefix.tick h₁ (ReadPrefix.tick h₂ (ReadPrefix.nil _)))) fuel tail

end PairSimulation.NodeArguments.ChildScan

end VPVNP
end Computability
end OAI
