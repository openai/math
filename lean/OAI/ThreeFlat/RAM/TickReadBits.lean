import OAI.ThreeFlat.RAM.DeterministicBlock
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

namespace OAI
/-! # Reading a little-endian field from the external bit tape -/

namespace ThreeFlat.RAM.TickReadBits

open Computability.VPVNP.BurstRAM PrivateRAM Fin.CommRing

variable {w p r k : ℕ}

/-- Registers contain the cursor, end, accumulated word, place value, temporary and unit. -/
def loop (pc : Fin 6 → Fin p) (reg : Fin 6 ↪ Fin r) (exit : Fin p) : Fin 6 → Instr w p r k
  | 0 => .jumpLt (reg 0) (reg 1) (pc 1) exit
  | 1 => .readExternal (reg 4) (reg 0) (pc 2)
  | 2 => .binary .mul (reg 4) (reg 3) (reg 4) (pc 3)
  | 3 => .binary .add (reg 2) (reg 2) (reg 4) (pc 4)
  | 4 => .binary .add (reg 3) (reg 3) (reg 3) (pc 5)
  | 5 => .binary .add (reg 0) (reg 0) (reg 5) (pc 0)

/-- The public constants are the base address of the field and its bit count. -/
def header (pc : Fin 6 → Fin p) (reg : Fin 6 ↪ Fin r) (entry : Fin p)
    (base width : Fin k) : Fin 6 → Instr w p r k
  | 0 => .publicWord (reg 0) base (pc 1)
  | 1 => .publicWord (reg 1) width (pc 2)
  | 2 => .binary .add (reg 1) (reg 0) (reg 1) (pc 3)
  | 3 => .constant (reg 2) 0 (pc 4)
  | 4 => .constant (reg 3) 1 (pc 5)
  | 5 => .constant (reg 5) 1 entry

/-- Each run preserves the caller's state and private memory and every register
outside the declared scratch bank. -/
structure Preserves (reg : Fin 6 ↪ Fin r) (c d : Config w p r) : Prop where
  persistent : d.persistent = c.persistent
  privateMem : d.privateMem = c.privateMem
  registers : ∀ i, (∀ j, i ≠ reg j) → d.reg i = c.reg i

theorem Preserves.trans {reg : Fin 6 ↪ Fin r} {c d e : Config w p r}
    (h : Preserves reg c d) (h' : Preserves reg d e) : Preserves reg c e :=
  ⟨h'.persistent.trans h.persistent, h'.privateMem.trans h.privateMem,
    fun i hi => (h'.registers i hi).trans (h.registers i hi)⟩

private def next (reg : Fin 6 ↪ Fin r) (pc : Fin 6 → Fin p) (c : Config w p r) (bit : Word w) :
    Config w p r :=
  let term := c.reg (reg 3) * bit
  let read := c.put (pc 2) (reg 4) bit
  (((read.put (pc 3) (reg 4) term).put (pc 4) (reg 2) (c.reg (reg 2)+term)).put
    (pc 5) (reg 3) (c.reg (reg 3)+c.reg (reg 3))).put (pc 0) (reg 0) (c.reg (reg 0)+1)

private theorem one_iter (M : Machine w p r k) (pc : Fin 6 → Fin p) (reg : Fin 6 ↪ Fin r)
    (exit : Fin p) (rom : ∀ i, M.code (pc i) = loop pc reg exit i)
    (c : Config w p r) (m : Memory w) (hc : c.pc = pc 0)
    (hl : c.reg (reg 0) < c.reg (reg 1)) (hi : c.reg (reg 5) = 1) :
    advance M.program 6 c m = some (next reg pc c (m (c.reg (reg 0)).val), m) := by
  simp (config := { decide := true }) [advance, Machine.program, hc, rom, loop, Instr.run, hl,
    hi, next, Config.put, Function.update, BinaryOp.eval]

/-- Run the loop with an arbitrary initial accumulator and coefficient. Its
arithmetic is in the word ring even if a temporary place value wraps around. -/
theorem advance_loop (M : Machine w p r k) (pc : Fin 6 → Fin p) (reg : Fin 6 ↪ Fin r)
    (exit : Fin p) (rom : ∀ i, M.code (pc i) = loop pc reg exit i)
    (m : Memory w) (n : ℕ) (c : Config w p r) (a scale value : ℕ)
    (hc : c.pc = pc 0) (hend : (c.reg (reg 0)).val+n = (c.reg (reg 1)).val)
    (hacc : c.reg (reg 2) = Fin.ofNat _ a) (hscale : c.reg (reg 3) = Fin.ofNat _ scale)
    (hone : c.reg (reg 5) = 1) (fit : value < 2^n)
    (bits : ∀ i < n, m ((c.reg (reg 0)).val+i) = Fin.ofNat _ (value.testBit i).toNat) :
    ∃ d, advance M.program (1+6*n) c m = some (d,m) ∧ d.pc = exit ∧
      d.reg (reg 2) = Fin.ofNat _ (a+scale*value) ∧ Preserves reg c d := by
  induction n generalizing c a scale value with
  | zero =>
    have eq : c.reg (reg 0) = c.reg (reg 1) := Fin.ext (by simpa using hend)
    have hv : value = 0 := by simpa using fit
    refine ⟨{c with pc := exit}, ?_, rfl, by simpa [hv] using hacc, ⟨rfl,rfl,fun _ _ => rfl⟩⟩
    simp [advance, Machine.program, hc, rom, loop, Instr.run, eq]
  | succ n ih =>
    have hl : c.reg (reg 0) < c.reg (reg 1) := by change _ < (c.reg (reg 1)).val; omega
    have haddr : (c.reg (reg 0)+1).val = (c.reg (reg 0)).val+1 := by
      apply Fin.val_add_one_of_lt'
      change (c.reg (reg 0)).val+1 < 2^w
      have := (c.reg (reg 1)).isLt
      omega
    have hb : m (c.reg (reg 0)).val = Fin.ofNat _ (value%2) := by
      simpa only [Nat.toNat_testBit, Nat.pow_zero, Nat.div_one, Nat.add_zero] using bits 0 (by omega)
    let c' := next reg pc c (Fin.ofNat _ (value%2))
    have step : advance M.program 6 c m = some (c',m) := by
      simpa only [hb, c'] using one_iter M pc reg exit rom c m hc hl hone
    have cursor : (c'.reg (reg 0)).val = (c.reg (reg 0)).val+1 := by
      simpa (config := { decide := true }) [c',next,Config.put,Function.update] using haddr
    have last : c'.reg (reg 1) = c.reg (reg 1) := by
      simp (config := { decide := true }) [c',next,Config.put,Function.update]
    have acc : c'.reg (reg 2) = Fin.ofNat _ (a+scale*(value%2)) := by
      simp (config := { decide := true }) [c',next,Config.put,Function.update,hacc,hscale,
        Fin.ofNat_eq_cast, Nat.cast_add, Nat.cast_mul]
    have place : c'.reg (reg 3) = Fin.ofNat _ (scale+scale) := by
      simp (config := { decide := true }) [c',next,Config.put,Function.update,hscale,
        Fin.ofNat_eq_cast, Nat.cast_add]
    have unit : c'.reg (reg 5) = 1 := by
      simpa (config := { decide := true }) [c',next,Config.put,Function.update] using hone
    have tail (i : ℕ) (hi : i < n) :
        m ((c'.reg (reg 0)).val+i) = Fin.ofNat _ ((value/2).testBit i).toNat := by
      rw [cursor, Nat.testBit_div_two, show (c.reg (reg 0)).val+1+i =
        (c.reg (reg 0)).val+(i+1) by omega]
      exact bits (i+1) (by omega)
    have fits : value / 2 < 2^n := by rw [pow_succ] at fit; omega
    obtain ⟨d, done, atExit, result, frame⟩ := ih c' _ _ _ rfl
      (by rw [cursor,last]; omega) acc place unit fits tail
    refine ⟨d, ?_, atExit, ?_, ?_⟩
    · rw [show 1+6*(n+1) = 6+(1+6*n) by omega]
      exact advance_trans step done
    · rw [result]
      congr 1
      calc
        _ = a+scale*(value%2+2*(value/2)) := by ring
        _ = _ := by rw [Nat.mod_add_div]
    · apply Preserves.trans (d := c') _ frame
      refine ⟨rfl,rfl,?_⟩
      intro i hi
      simp [c',next,Config.put,Function.update,hi]

private def start (reg : Fin 6 ↪ Fin r) (entry : Fin p) (c : Config w p r) (base width : Word w) :
    Config w p r :=
  let loaded := (c.put entry (reg 0) base).put entry (reg 1) width
  (((loaded.put entry (reg 1) (base+width)).put entry (reg 2) 0).put entry (reg 3) 1).put
    entry (reg 5) 1

/-- Decode a public-addressed little-endian segment in six steps per bit and
seven more steps for setup and the terminating branch. -/
theorem advance_public (M : Machine w p r k) (setup pc : Fin 6 → Fin p) (reg : Fin 6 ↪ Fin r)
    (exit : Fin p) (base width : Fin k)
    (hs : ∀ i, M.code (setup i) = header setup reg (pc 0) base width i)
    (hl : ∀ i, M.code (pc i) = loop pc reg exit i)
    (c : Config w p r) (m : Memory w) (value : ℕ) (hc : c.pc = setup 0)
    (addr : (M.publicData base).val + (M.publicData width).val < 2^w)
    (fit : value < 2^(M.publicData width).val) (fitsWord : value < 2^w)
    (bits : ∀ i < (M.publicData width).val,
      m ((M.publicData base).val+i) = Fin.ofNat _ (value.testBit i).toNat) :
    ∃ d, advance M.program (7+6*(M.publicData width).val) c m = some (d,m) ∧
      d.pc = exit ∧ (d.reg (reg 2)).val = value ∧ Preserves reg c d := by
  let c' := start reg (pc 0) c (M.publicData base) (M.publicData width)
  have step : advance M.program 6 c m = some (c',m) := by
    simp (config := { decide := true }) [advance,Machine.program,hc,hs,header,Instr.run,
      BinaryOp.eval,c',start,Config.put,Function.update]
  have cur : c'.reg (reg 0) = M.publicData base := by
    simp (config := { decide := true }) [c',start,Config.put,Function.update]
  have endv : (c'.reg (reg 1)).val = (M.publicData base).val + (M.publicData width).val := by
    simp (config := { decide := true }) [c',start,Config.put,Function.update,Fin.val_add,
      Nat.mod_eq_of_lt addr]
  obtain ⟨d,done,hexit,read,frame⟩ := advance_loop M pc reg exit hl m (M.publicData width).val c'
    0 1 value rfl (by rw [cur,endv])
    (by simp (config := { decide := true }) [c',start,Config.put,Function.update])
    (by simp (config := { decide := true }) [c',start,Config.put,Function.update])
    (by simp (config := { decide := true }) [c',start,Config.put,Function.update])
    fit (by simpa only [cur] using bits)
  refine ⟨d,?_,hexit,?_,?_⟩
  · rw [show 7+6*(M.publicData width).val = 6+(1+6*(M.publicData width).val) by omega]
    exact advance_trans step done
  · simp [read,Fin.ofNat,Nat.mod_eq_of_lt fitsWord]
  · apply Preserves.trans (d := c') _ frame
    refine ⟨rfl,rfl,?_⟩
    intro i hi
    simp [c',start,Config.put,Function.update,hi]

end ThreeFlat.RAM.TickReadBits

end OAI
