import OAI.ThreeFlat.RAM.DeterministicBlock
import OAI.ThreeFlat.RAM.WordSegment
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
/-! # Emitting consecutive words from a native descriptor subroutine

Each descriptor call may take a different number of deterministic steps.
The driver charges that call, one comparison, one external write, and one
pointer increment. It checks the empty suffix once.
-/

namespace ThreeFlat.RAM.DescriptorScan

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM

variable {w p r k : ℕ}

structure Labels (p : ℕ) where
  guard : Fin p
  describe : Fin p
  store : Fin p
  bump : Fin p
  exit : Fin p

/-- Registers 0 through 3 hold the current address, exclusive end, result,
and unit increment, respectively. -/
structure Installed (M : Machine w p r k) (reg : Fin 4 ↪ Fin r) (L : Labels p) : Prop where
  test : M.code L.guard = .jumpLt (reg 0) (reg 1) L.describe L.exit
  store : M.code L.store = .writeExternal (reg 0) (reg 2) L.bump
  bump : M.code L.bump = .binary .add (reg 0) (reg 0) (reg 3) L.guard

def next (reg : Fin 4 ↪ Fin r) (L : Labels p) (c : Config w p r) : Config w p r :=
  c.put L.guard (reg 0) (c.reg (reg 0) + c.reg (reg 3))

variable (M : Machine w p r k) (reg : Fin 4 ↪ Fin r) (L : Labels p)

/-- A word descriptor is verified on the actual native instructions at the
descriptor entry counter. Its invariant can describe read-only source tables,
public parameters, and scratch registers used between calls. -/
def Describes (cost : ℕ) (word : ℕ → Word w) (valid : Config w p r → Memory w → Prop) : Prop :=
  ∀ (c : Config w p r) (m : Memory w), c.pc = L.guard → valid c m →
    c.reg (reg 0) < c.reg (reg 1) →
    ∃ t ≤ cost, ∃ out : Config w p r,
      advance M.program t {c with pc := L.describe} m = some (out,m) ∧
      out.pc = L.store ∧ out.reg (reg 0) = c.reg (reg 0) ∧
      out.reg (reg 1) = c.reg (reg 1) ∧ out.reg (reg 3) = 1 ∧
      out.reg (reg 2) = word (c.reg (reg 0)).val ∧
      valid (next reg L out) (writeMemory m (c.reg (reg 0)) (word (c.reg (reg 0)).val))

theorem generate (rom : Installed M reg L) (cost : ℕ) (word : ℕ → Word w)
    (valid : Config w p r → Memory w → Prop) (desc : Describes M reg L cost word valid)
    (n : ℕ) (c : Config w p r) (m : Memory w) (entry : c.pc = L.guard) (ok : valid c m)
    (length : (c.reg (reg 0)).val+n = (c.reg (reg 1)).val) :
    ∃ steps ≤ 1+n*(cost+3), ∃ out : Config w p r, out.pc = L.exit ∧
      advance M.program steps c m = some (out,fillSegment (c.reg (reg 0)).val n word m) := by
  induction n generalizing c m with
  | zero =>
    have eq : c.reg (reg 0) = c.reg (reg 1) := Fin.ext (by simpa using length)
    refine ⟨1, by simp, {c with pc := L.exit}, rfl, ?_⟩
    simp [advance, Machine.program, entry, rom.test, Instr.run, eq]
  | succ n ih =>
    have lt : c.reg (reg 0) < c.reg (reg 1) := by change _ < (c.reg (reg 1)).val; omega
    obtain ⟨t, ht, d, run, pc, addr, stop, unit, result, inv⟩ := desc c m entry ok lt
    let val := word (c.reg (reg 0)).val
    let m' := writeMemory m (c.reg (reg 0)) val
    have head : advance M.program 1 c m = some ({c with pc := L.describe},m) := by
      simp [advance, Machine.program, entry, rom.test, Instr.run, lt]
    have store : advance M.program 2 d m = some (next reg L d,m') := by
      simp [advance, Machine.program, pc, rom.store, rom.bump, Instr.run, BinaryOp.eval,
        next, addr, result, m', val, Config.put]
    have ptr : ((next reg L d).reg (reg 0)).val = (c.reg (reg 0)).val + 1 := by
      simp only [next, Config.put_same, addr, unit]
      apply Fin.val_add_one_of_lt'
      have := (c.reg (reg 1)).isLt
      omega
    have endReg : (next reg L d).reg (reg 1) = c.reg (reg 1) := by
      simpa [next, Config.put, Function.update_of_ne (reg.injective.ne (by decide : (1:Fin 4) ≠ 0))]
        using stop
    obtain ⟨s, hs, z, exitPc, finish⟩ := ih (next reg L d) m' rfl inv
      (by rw [ptr,endReg]; omega)
    refine ⟨1+t+2+s, ?_, z, exitPc, ?_⟩
    · rw [Nat.succ_mul]
      omega
    · have combined := advance_trans (advance_trans (advance_trans head run) store) finish
      rw [fillSegment_succ, ← ptr]
      exact combined

end ThreeFlat.RAM.DescriptorScan

end OAI
