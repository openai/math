import OAI.ThreeFlat.RAM.DeterministicBlock

namespace OAI
/-! # Native zero initialization of a register frame

One constant instruction per register clears the interpreter's scratch frame
before control passes to its entry. The location after the last instruction
belongs to the continuation. No memory access or extra exit jump is needed.
-/

namespace ThreeFlat.RAM.TickClearFrame

open Computability.VPVNP.BurstRAM PrivateRAM

variable {w p r k n : ℕ}

/-- Row `i` zeros its assigned register and falls through to the next location. -/
def row (loc : Fin (n+1) → Fin p) (reg : Fin n → Fin r) (i : Fin n) : Instr w p r k :=
  .constant (reg i) 0 (loc i.succ)

/-- The caller configuration at the end of the prologue. -/
def cleared (reg : Fin n → Fin r) (exit : Fin p) (c : Config w p r) : Config w p r :=
  {c with pc := exit, reg := fun j => if ∃ i, reg i = j then 0 else c.reg j}

@[simp] theorem cleared_pc (reg : Fin n → Fin r) (exit : Fin p) (c : Config w p r) :
    (cleared reg exit c).pc = exit := rfl

@[simp] theorem cleared_persistent (reg : Fin n → Fin r) (exit : Fin p) (c : Config w p r) :
    (cleared reg exit c).persistent = c.persistent := rfl

@[simp] theorem cleared_privateMem (reg : Fin n → Fin r) (exit : Fin p) (c : Config w p r) :
    (cleared reg exit c).privateMem = c.privateMem := rfl

@[simp] theorem cleared_target (reg : Fin n → Fin r) (exit : Fin p) (c : Config w p r)
    (i : Fin n) : (cleared reg exit c).reg (reg i) = 0 := by
  simp [cleared, show ∃ a, reg a = reg i from ⟨i,rfl⟩]

theorem cleared_other (reg : Fin n → Fin r) (exit : Fin p) (c : Config w p r)
    {j : Fin r} (outside : ∀ i, reg i ≠ j) : (cleared reg exit c).reg j = c.reg j := by
  simp [cleared, not_exists.mpr outside]

private def prefixState (loc : Fin (n+1) → Fin p) (reg : Fin n → Fin r)
    (c : Config w p r) (j : Fin (n+1)) : Config w p r :=
  {c with pc := loc j, reg := fun a =>
    if ∃ i, i.val < j.val ∧ reg i = a then 0 else c.reg a}

private theorem prefix_put (loc : Fin (n+1) → Fin p) (reg : Fin n → Fin r)
    (c : Config w p r) (i : Fin n) :
    (prefixState loc reg c i.castSucc).put (loc i.succ) (reg i) 0 =
      prefixState loc reg c i.succ := by
  unfold prefixState Config.put
  congr 1
  funext a
  by_cases h : a = reg i
  · subst a
    rw [Function.update_self, ite_eq_left (show ∃ j : Fin n, j.val < i.succ.val ∧ reg j = reg i from
      ⟨i, Nat.lt_succ_self _, rfl⟩)]
  · have past : (∃ j : Fin n, j.val < i.succ.val ∧ reg j = a) ↔
        ∃ j : Fin n, j.val < i.castSucc.val ∧ reg j = a := by
      simp only [Fin.val_succ, Fin.val_castSucc]
      constructor
      · rintro ⟨j,hj,ha⟩
        have ne : j.val ≠ i.val := fun eqn => h (ha.symm.trans (congrArg reg (Fin.ext eqn)))
        exact ⟨j,by omega,ha⟩
      · rintro ⟨j,hj,ha⟩
        exact ⟨j,by omega,ha⟩
    simp only [Function.update_of_ne h, past]

/-- The block takes exactly `n` native steps, preserving both memories,
the persistent word and every register outside the designated frame. -/
theorem advance_clear (M : Machine w p r k) (loc : Fin (n+1) → Fin p)
    (reg : Fin n → Fin r) (rom : ∀ i, M.code (loc i.castSucc) = row loc reg i)
    (c : Config w p r) (mem : Memory w) (start : c.pc = loc 0) :
    advance M.program n c mem = some (cleared reg (loc (Fin.last n)) c, mem) := by
  have run (j : Fin (n+1)) :
      advance M.program j.val c mem = some (prefixState loc reg c j, mem) := by
    induction j using Fin.induction with
    | zero =>
      simp [advance, prefixState, ← start]
    | succ i ih =>
      change advance M.program (i.castSucc.val+1) c mem = _
      rw [advance_add, ih]
      simp only [Option.bind_some]
      simp only [advance, Machine.program, prefixState, rom, row, Instr.run]
      exact congrArg (fun d => some (d,mem)) (prefix_put loc reg c i)
  simpa [prefixState, cleared, Fin.is_lt] using run (Fin.last n)

/-- Weighted evaluation can prepend this native block at the exact fuel cost. -/
theorem mass_clear {F : Type*} [Semiring F] (code : FieldCode F w) (M : Machine w p r k)
    (loc : Fin (n+1) → Fin p) (reg : Fin n → Fin r)
    (rom : ∀ i, M.code (loc i.castSucc) = row loc reg i)
    (c : Config w p r) (mem : Memory w) (start : c.pc = loc 0) (fuel : ℕ) :
    mass code M.program (fuel+n) c mem =
      mass code M.program fuel (cleared reg (loc (Fin.last n)) c) mem :=
  mass_of_advance code M.program (advance_clear M loc reg rom c mem start) fuel

end ThreeFlat.RAM.TickClearFrame

end OAI
