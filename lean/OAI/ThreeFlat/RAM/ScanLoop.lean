import OAI.ThreeFlat.RAM.Weighted

namespace OAI
/-! # Comparing two contiguous external memory regions

The native loop reads one word from each region, rejects a mismatch, and
increments the two addresses. A successful scan reaches the continuation
after six instructions per word and a final end check.
-/

namespace ThreeFlat.RAM.ScanLoop

open Computability.VPVNP.BurstRAM PrivateRAM

variable {F : Type*} [Semiring F] {w p r k : ℕ}

/-- Registers hold the left cursor, left limit, right cursor, two word
buffers and the unit increment. -/
def block (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (exit : Fin p) :
    Fin 7 → Instr w p r k
  | 0 => .jumpLt (reg 0) (reg 1) (pc 1) exit
  | 1 => .readExternal (reg 3) (reg 0) (pc 2)
  | 2 => .readExternal (reg 4) (reg 2) (pc 3)
  | 3 => .jumpEq (reg 3) (reg 4) (pc 4) (pc 6)
  | 4 => .binary .add (reg 0) (reg 0) (reg 5) (pc 5)
  | 5 => .binary .add (reg 2) (reg 2) (reg 5) (pc 0)
  | 6 => .reject

def next (reg : Fin 6 ↪ Fin r) (pc : Fin 7 → Fin p) (c : Config w p r)
    (v v' : Word w) : Config w p r :=
  (((c.put (pc 2) (reg 3) v).put (pc 3) (reg 4) v').put
    (pc 5) (reg 0) (c.reg (reg 0) + 1)).put (pc 0) (reg 2) (c.reg (reg 2) + 1)

def endConfig (reg : Fin 6 ↪ Fin r) (pc : Fin 7 → Fin p) (exit : Fin p) (mem : Memory w) :
    ℕ → Config w p r → Config w p r
  | 0, c => { c with pc := exit }
  | n+1, c => endConfig reg pc exit mem n (next reg pc c
      (mem (c.reg (reg 0)).val) (mem (c.reg (reg 2)).val))

@[simp] theorem endConfig_pc (reg : Fin 6 ↪ Fin r) (pc : Fin 7 → Fin p) (exit : Fin p)
    (mem : Memory w) (n : ℕ) (c : Config w p r) :
    (endConfig reg pc exit mem n c).pc = exit := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => exact ih _

/-- The loop preserves every register outside the two address cursors and read buffers. -/
theorem endConfig_reg (reg : Fin 6 ↪ Fin r) (pc : Fin 7 → Fin p) (exit : Fin p)
    (mem : Memory w) (n : ℕ) (c : Config w p r) (i : Fin r)
    (h₀ : i ≠ reg 0) (h₂ : i ≠ reg 2) (h₃ : i ≠ reg 3) (h₄ : i ≠ reg 4) :
    (endConfig reg pc exit mem n c).reg i = c.reg i := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp [endConfig, ih, next, Config.put, Function.update, h₀, h₂, h₃, h₄]

/-- The two regions agree word for word. -/
def agree (mem : Memory w) (left right count : ℕ) : Prop :=
  ∀ j : Fin count, mem (left + j.val) = mem (right + j.val)

instance (mem : Memory w) (left right count : ℕ) : Decidable (agree mem left right count) :=
  inferInstanceAs (Decidable (∀ j : Fin count, mem (left + j.val) = mem (right + j.val)))

private theorem agree_succ (mem : Memory w) (left right n : ℕ) :
    agree mem left right (n+1) ↔ mem left = mem right ∧ agree mem (left+1) (right+1) n := by
  constructor
  · intro h
    refine ⟨by simpa using h 0, fun j => ?_⟩
    simpa [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h j.succ
  · rintro ⟨h₀, h⟩ j
    refine Fin.cases (by simpa using h₀) (fun i => ?_) j
    simpa [Fin.val_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h i

private theorem mass_one (code : FieldCode F w) (M : Machine w p r k)
    (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (exit : Fin p)
    (hm : ∀ i, M.code (pc i) = block pc reg exit i)
    (c : Config w p r) (mem : Memory w) (fuel : ℕ)
    (hc : c.pc = pc 0) (hl : c.reg (reg 0) < c.reg (reg 1)) (hi : c.reg (reg 5) = 1) :
    mass code M.program (fuel + 6) c mem =
      if mem (c.reg (reg 0)).val = mem (c.reg (reg 2)).val then
        mass code M.program fuel (next reg pc c (mem (c.reg (reg 0)).val)
          (mem (c.reg (reg 2)).val)) mem
      else 0 := by
  by_cases he : mem (c.reg (reg 0)).val = mem (c.reg (reg 2)).val <;>
    simp (config := { decide := true }) [mass, Machine.program, hc, hm, block, Instr.run, hl,
      hi, he, next, Config.put, Function.update, BinaryOp.eval]

/-- Rejection on the first unequal word and continuation on equal regions.
The right limit is representable, which rules out cursor wraparound. -/
theorem mass_block (code : FieldCode F w) (M : Machine w p r k)
    (pc : Fin 7 → Fin p) (reg : Fin 6 ↪ Fin r) (exit : Fin p)
    (hm : ∀ i, M.code (pc i) = block pc reg exit i)
    (n fuel : ℕ) (c : Config w p r) (mem : Memory w) (hc : c.pc = pc 0)
    (hn : (c.reg (reg 0)).val + n = (c.reg (reg 1)).val)
    (hr : (c.reg (reg 2)).val + n < 2 ^ w) (hi : c.reg (reg 5) = 1) :
    mass code M.program (fuel+1+6*n) c mem =
      if agree mem (c.reg (reg 0)).val (c.reg (reg 2)).val n then
        mass code M.program fuel (endConfig reg pc exit mem n c) mem
      else 0 := by
  classical
  induction n generalizing c with
  | zero =>
    have he : c.reg (reg 0) = c.reg (reg 1) := Fin.ext (by simpa using hn)
    simp [agree, mass, Machine.program, hc, hm, block, Instr.run, he, endConfig]
  | succ n ih =>
    have hl : c.reg (reg 0) < c.reg (reg 1) := by change _ < (c.reg (reg 1)).val; omega
    have ha : (c.reg (reg 0) + 1).val = (c.reg (reg 0)).val + 1 := by
      rw [Fin.val_add_one_of_lt']
      change (c.reg (reg 0)).val+1 < 2 ^ w
      have := (c.reg (reg 1)).isLt
      omega
    have hb : (c.reg (reg 2) + 1).val = (c.reg (reg 2)).val + 1 := by
      rw [Fin.val_add_one_of_lt']
      change (c.reg (reg 2)).val+1 < 2 ^ w
      omega
    let c' := next reg pc c (mem (c.reg (reg 0)).val) (mem (c.reg (reg 2)).val)
    have cl : (c'.reg (reg 0)).val = (c.reg (reg 0)).val + 1 := by
      simpa (config := { decide := true }) [c', next, Config.put, Function.update] using ha
    have cr : (c'.reg (reg 2)).val = (c.reg (reg 2)).val + 1 := by
      simpa (config := { decide := true }) [c', next, Config.put, Function.update] using hb
    have ce : c'.reg (reg 1) = c.reg (reg 1) := by
      simp (config := { decide := true }) [c', next, Config.put, Function.update]
    have ci : c'.reg (reg 5) = 1 := by
      simpa (config := { decide := true }) [c', next, Config.put, Function.update] using hi
    rw [show fuel+1+6*(n+1) = (fuel+1+6*n)+6 by omega,
      mass_one code M pc reg exit hm c mem _ hc hl hi]
    have htail := ih c' rfl (by rw [cl, ce]; omega) (by rw [cr]; omega) ci
    rw [cl, cr] at htail
    change (if _ then mass code M.program _ c' mem else _) = _
    rw [htail]
    by_cases h : mem (c.reg (reg 0)).val = mem (c.reg (reg 2)).val <;>
      simp [agree_succ, h, endConfig, c']

end ThreeFlat.RAM.ScanLoop

end OAI
