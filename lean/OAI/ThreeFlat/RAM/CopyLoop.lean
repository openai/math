import OAI.ThreeFlat.RAM.DeterministicBlock

namespace OAI
/-! # Forward copy between two external memory regions

A native block copies one external word using a read and a write and advances the
two cursors. Regions may overlap if the destination begins at or before the source.
-/

namespace ThreeFlat.RAM.CopyLoop

open Computability.VPVNP.BurstRAM PrivateRAM

variable {F : Type*} [Semiring F] {w p r k : ℕ}

/-- Registers hold the source cursor, its end, the destination cursor, a temporary
word and the unit increment. -/
def block (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p) :
    Fin 5 → Instr w p r k
  | 0 => .jumpLt (reg 0) (reg 1) (pc 1) exit
  | 1 => .readExternal (reg 3) (reg 0) (pc 2)
  | 2 => .writeExternal (reg 2) (reg 3) (pc 3)
  | 3 => .binary .add (reg 0) (reg 0) (reg 4) (pc 4)
  | 4 => .binary .add (reg 2) (reg 2) (reg 4) (pc 0)

def next (reg : Fin 5 ↪ Fin r) (pc : Fin 5 → Fin p) (c : Config w p r)
    (v : Word w) : Config w p r :=
  ((c.put (pc 2) (reg 3) v).put (pc 4) (reg 0) (c.reg (reg 0) + 1)).put
    (pc 0) (reg 2) (c.reg (reg 2) + 1)

def endConfig (reg : Fin 5 ↪ Fin r) (pc : Fin 5 → Fin p) (exit : Fin p) :
    ℕ → (ℕ → Word w) → Config w p r → Config w p r
  | 0, _, c => { c with pc := exit }
  | n+1, v, c => endConfig reg pc exit n (fun j => v (j+1)) (next reg pc c (v 0))

@[simp] theorem endConfig_pc (reg : Fin 5 ↪ Fin r) (pc : Fin 5 → Fin p) (exit : Fin p)
    (n : ℕ) (v : ℕ → Word w) (c : Config w p r) :
    (endConfig reg pc exit n v c).pc = exit := by
  induction n generalizing c v with
  | zero => rfl
  | succ n ih => exact ih _ _

/-- The two address cursors and the transfer register are the only registers written. -/
theorem endConfig_reg (reg : Fin 5 ↪ Fin r) (pc : Fin 5 → Fin p) (exit : Fin p)
    (n : ℕ) (v : ℕ → Word w) (c : Config w p r) (i : Fin r)
    (h₀ : i ≠ reg 0) (h₂ : i ≠ reg 2) (h₃ : i ≠ reg 3) :
    (endConfig reg pc exit n v c).reg i = c.reg i := by
  induction n generalizing c v with
  | zero => rfl
  | succ n ih => simp [endConfig, ih, next, Config.put, Function.update, h₀, h₂, h₃]

/-- Replace the half-open destination interval, retaining every exterior word. -/
def install (dst count : ℕ) (v : ℕ → Word w) (mem : Memory w) : Memory w :=
  fun a => if dst ≤ a ∧ a < dst + count then v (a-dst) else mem a

@[simp] theorem install_zero (dst : ℕ) (v : ℕ → Word w) (mem : Memory w) : install dst 0 v mem = mem := by
  funext a
  simp [install]

private theorem install_cons (dst : Word w) (n : ℕ) (v : ℕ → Word w) (mem : Memory w) :
    install dst.val (n+1) v mem =
      install (dst.val+1) n (fun j => v (j+1)) (writeMemory mem dst (v 0)) := by
  funext a
  by_cases h : a = dst.val
  · subst a
    simp [install, writeMemory]
  · by_cases ha : dst.val ≤ a ∧ a < dst.val + (n+1)
    · have hb : dst.val+1 ≤ a ∧ a < dst.val+1+n := by omega
      simp only [install, ite_eq_left ha, ite_eq_left hb]
      congr 1
      omega
    · have hb : ¬(dst.val+1 ≤ a ∧ a < dst.val+1+n) := by omega
      simp [install, ha, hb, writeMemory, h]

private theorem advance_one (M : Machine w p r k)
    (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p)
    (hm : ∀ i, M.code (pc i) = block pc reg exit i)
    (c : Config w p r) (mem : Memory w)
    (hc : c.pc = pc 0) (hl : c.reg (reg 0) < c.reg (reg 1)) (hi : c.reg (reg 4) = 1) :
    advance M.program 5 c mem = some (next reg pc c (mem (c.reg (reg 0)).val),
        writeMemory mem (c.reg (reg 2)) (mem (c.reg (reg 0)).val)) := by
  simp (config := { decide := true }) [advance, Machine.program, hc, hm, block, Instr.run, hl,
    hi, next, Config.put, Function.update, BinaryOp.eval]

private theorem advance_of_words (M : Machine w p r k)
    (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p)
    (hm : ∀ i, M.code (pc i) = block pc reg exit i)
    (n : ℕ) (c : Config w p r) (mem : Memory w) (hc : c.pc = pc 0)
    (hn : (c.reg (reg 0)).val + n = (c.reg (reg 1)).val)
    (hr : (c.reg (reg 2)).val + n < 2^w)
    (hsafe : (c.reg (reg 2)).val ≤ (c.reg (reg 0)).val ∨
       (c.reg (reg 0)).val + n ≤ (c.reg (reg 2)).val)
    (hi : c.reg (reg 4) = 1) (v : ℕ → Word w)
    (hv : ∀ j < n, mem ((c.reg (reg 0)).val+j) = v j) :
    advance M.program (1+5*n) c mem =
      some (endConfig reg pc exit n v c, install (c.reg (reg 2)).val n v mem) := by
  induction n generalizing c mem v with
  | zero =>
    have he : c.reg (reg 0) = c.reg (reg 1) := Fin.ext (by simpa using hn)
    simp [advance, Machine.program, hc, hm, block, Instr.run, he, endConfig]
  | succ n ih =>
    have hl : c.reg (reg 0) < c.reg (reg 1) := by change _ < (c.reg (reg 1)).val; omega
    have ha : (c.reg (reg 0) + 1).val = (c.reg (reg 0)).val + 1 := by
      rw [Fin.val_add_one_of_lt']
      change (c.reg (reg 0)).val+1 < 2^w
      have := (c.reg (reg 1)).isLt
      omega
    have hb : (c.reg (reg 2) + 1).val = (c.reg (reg 2)).val + 1 := by
      rw [Fin.val_add_one_of_lt']
      change (c.reg (reg 2)).val+1 < 2^w
      omega
    let c' := next reg pc c (v 0)
    have cl : (c'.reg (reg 0)).val = (c.reg (reg 0)).val+1 := by
      simpa (config := { decide := true }) [c', next, Config.put, Function.update] using ha
    have cr : (c'.reg (reg 2)).val = (c.reg (reg 2)).val+1 := by
      simpa (config := { decide := true }) [c', next, Config.put, Function.update] using hb
    have ce : c'.reg (reg 1) = c.reg (reg 1) := by
      simp (config := { decide := true }) [c', next, Config.put, Function.update]
    have ci : c'.reg (reg 4) = 1 := by
      simpa (config := { decide := true }) [c', next, Config.put, Function.update] using hi
    have hcur : mem (c.reg (reg 0)).val = v 0 := by simpa using hv 0 (by omega)
    let mem' := writeMemory mem (c.reg (reg 2)) (v 0)
    have hv' (j : ℕ) (hj : j < n) : mem' ((c'.reg (reg 0)).val+j) = v (j+1) := by
      rw [cl]
      have hne : (c.reg (reg 0)).val+1+j ≠ (c.reg (reg 2)).val := by omega
      have hx : (c.reg (reg 0)).val+1+j = (c.reg (reg 0)).val+(j+1) := by omega
      change (if _ then _ else _) = _
      rw [ite_eq_right hne, hx]
      exact hv (j+1) (by omega)
    rw [show 1+5*(n+1) = 5+(1+5*n) by omega, advance_add, advance_one M pc reg exit hm _ _ hc hl hi,
      hcur, endConfig, install_cons]
    simp only [Option.bind_some]
    have htail := ih c' mem' rfl (by rw [cl, ce]; omega) (by rw [cr]; omega)
      (by rw [cl, cr]; omega) ci (fun j => v (j+1)) hv'
    rw [cr] at htail
    exact htail

/-- Deterministically copy the source interval before entering the continuation.
Every word outside the destination interval retains its initial value. -/
theorem advance_block (M : Machine w p r k)
    (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p)
    (hm : ∀ i, M.code (pc i) = block pc reg exit i)
    (n : ℕ) (c : Config w p r) (mem : Memory w) (hc : c.pc = pc 0)
    (hn : (c.reg (reg 0)).val+n = (c.reg (reg 1)).val)
    (hr : (c.reg (reg 2)).val+n < 2^w)
    (hsafe : (c.reg (reg 2)).val ≤ (c.reg (reg 0)).val ∨
       (c.reg (reg 0)).val+n ≤ (c.reg (reg 2)).val)
    (hi : c.reg (reg 4) = 1) :
    let v := fun j => mem ((c.reg (reg 0)).val+j)
    advance M.program (1+5*n) c mem =
      some (endConfig reg pc exit n v c, install (c.reg (reg 2)).val n v mem) :=
  advance_of_words M pc reg exit hm n c mem hc hn hr hsafe hi _ (fun _ _ => rfl)

/-- A native forward copy with its exact fuel cost and complete memory semantics. -/
theorem mass_block (code : FieldCode F w) (M : Machine w p r k)
    (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p)
    (hm : ∀ i, M.code (pc i) = block pc reg exit i)
    (n fuel : ℕ) (c : Config w p r) (mem : Memory w) (hc : c.pc = pc 0)
    (hn : (c.reg (reg 0)).val+n = (c.reg (reg 1)).val)
    (hr : (c.reg (reg 2)).val+n < 2^w)
    (hsafe : (c.reg (reg 2)).val ≤ (c.reg (reg 0)).val ∨
       (c.reg (reg 0)).val+n ≤ (c.reg (reg 2)).val)
    (hi : c.reg (reg 4) = 1) :
    let v := fun j => mem ((c.reg (reg 0)).val+j)
    mass code M.program (fuel+1+5*n) c mem =
      mass code M.program fuel (endConfig reg pc exit n v c) (install (c.reg (reg 2)).val n v mem) :=
  by simpa only [Nat.add_assoc] using mass_of_advance code M.program
       (advance_block M pc reg exit hm n c mem hc hn hr hsafe hi) fuel

end ThreeFlat.RAM.CopyLoop

end OAI
