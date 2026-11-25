import OAI.ThreeFlat.RAM.DeterministicBlock
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # A fixed native loop reading word-sized public data stored one bit per address -/

namespace ThreeFlat.RAM.ReadPackedWord

open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {w p r k : ℕ}

/-- Registers hold cursor, end, unit increment, accumulator, and input bit. -/
def instruction (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p) :
    Fin 5 → Instr w p r k :=
  ![.jumpLt (reg 0) (reg 1) (pc 1) exit,
    .readExternal (reg 4) (reg 0) (pc 2),
    .binary .add (reg 3) (reg 3) (reg 3) (pc 3),
    .binary .add (reg 3) (reg 3) (reg 4) (pc 4),
    .binary .add (reg 0) (reg 0) (reg 2) (pc 0)]

def accumulate (m : Memory w) : ℕ → ℕ → Word w → Word w
  | 0,_,x => x
  | n+1,a,x => accumulate m n (a+1) (x+x+m a)

private def update (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r)
    (c : Config w p r) (m : Memory w) :=
  let x := c.reg (reg 3)
  let b := m (c.reg (reg 0)).val
  ((c.put (pc 2) (reg 4) b).put (pc 4) (reg 3) (x+x+b)).put
    (pc 0) (reg 0) (c.reg (reg 0)+c.reg (reg 2))

def Frame (reg : Fin 5 ↪ Fin r) (c d : Config w p r) : Prop :=
  d.persistent = c.persistent ∧ d.privateMem = c.privateMem ∧
    ∀ i, i≠reg 0 → i≠reg 3 → i≠reg 4 → d.reg i = c.reg i

theorem run (M : Machine w p r k) (pc : Fin 5 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p)
    (rom : ∀ i, M.code (pc i) = instruction pc reg exit i)
    (m : Memory w) (n : ℕ) (c : Config w p r) (entry : c.pc = pc 0)
    (unit : c.reg (reg 2) = 1) (len : (c.reg (reg 0)).val+n = (c.reg (reg 1)).val) :
    ∃ d, advance M.program (5*n+1) c m = some (d,m) ∧ d.pc = exit ∧
      d.reg (reg 3) = accumulate m n (c.reg (reg 0)).val (c.reg (reg 3)) ∧
      d.reg (reg 0) = c.reg (reg 1) ∧ Frame reg c d := by
  induction n generalizing c with
  | zero =>
    have eq : c.reg (reg 0) = c.reg (reg 1) := Fin.ext (by simpa using len)
    refine ⟨{c with pc := exit},?_,rfl,rfl,eq,rfl,rfl,fun _ _ _ _ => rfl⟩
    simp [advance,Machine.program,entry,rom,instruction,Instr.run,eq]
  | succ n ih =>
    have before : c.reg (reg 0) < c.reg (reg 1) := by change _ < (c.reg (reg 1)).val; omega
    let d := update pc reg c m
    have run5 : advance M.program 5 c m = some (d,m) := by
      simp (config := {decide := true}) [advance,Machine.program,entry,rom,instruction,
        Instr.run,BinaryOp.eval,Config.put,before,d,update,Function.update_idem]
    have cursor : (d.reg (reg 0)).val = (c.reg (reg 0)).val+1 := by
      simp only [d,update,Config.put_same,unit]
      apply Fin.val_add_one_of_lt'
      have := (c.reg (reg 1)).isLt
      omega
    have keep (i : Fin r) (h0 : i≠reg 0) (h3 : i≠reg 3) (h4 : i≠reg 4) :
        d.reg i = c.reg i := by simp [d,update,Config.put,Function.update_of_ne,h0,h3,h4]
    have up (i : Fin 5) (h0 : i≠0) (h3 : i≠3) (h4 : i≠4) : d.reg (reg i) = c.reg (reg i) :=
      keep _ (reg.injective.ne h0) (reg.injective.ne h3) (reg.injective.ne h4)
    have acc : d.reg (reg 3) = c.reg (reg 3)+c.reg (reg 3)+m (c.reg (reg 0)).val := by
      simp (config := {decide := true}) [d,update,Config.put]
    obtain ⟨z,hz,ep,out,atEnd,hp,hm,hr⟩ := ih d rfl
      ((up 2 (by decide) (by decide) (by decide)).trans unit)
      (by rw [cursor,up 1 (by decide) (by decide) (by decide)]; omega)
    refine ⟨z,?_,ep,?_,atEnd.trans (up 1 (by decide) (by decide) (by decide)),
      hp,hm,fun i h0 h3 h4 => (hr i h0 h3 h4).trans (keep i h0 h3 h4)⟩
    · rw [show 5*(n+1)+1 = 5+(5*n+1) by omega]
      exact advance_trans run5 hz
    · simpa [cursor,acc,accumulate] using out

private theorem next_digit (x n : ℕ) :
    x/2^(n+1) + x/2^(n+1) + (x.testBit n).toNat = x/2^n := by
  rw [Nat.toNat_testBit,pow_succ,← Nat.div_div_eq_div_mul]
  have eq := Nat.div_add_mod (x/2^n) 2
  omega

/-- A big-endian bit segment spells precisely the specified word. -/
theorem accumulate_word (m : Memory w) (n a : ℕ) (x acc : Word w)
    (startValue : acc = ((x.val/2^n : ℕ) : Word w))
    (bits : ∀ i<n, m (a+i) = ((x.val.testBit (n-1-i)).toNat : Word w)) :
    accumulate m n a acc = x := by
  induction n generalizing a acc with
  | zero => simpa [accumulate] using startValue
  | succ n ih =>
    rw [accumulate]
    apply ih
    · have first := bits 0 (by omega)
      simp only [Nat.add_zero,Nat.succ_sub_one,Nat.sub_zero] at first
      rw [startValue, first, ← Nat.cast_add, ← Nat.cast_add, next_digit]
    · intro i hi
      simpa [show a+1+i=a+(i+1) by omega, show n-1-i=n-(i+1) by omega] using
        bits (i+1) (by omega)

theorem accumulate_full (m : Memory w) (a : ℕ) (x : Word w)
    (bits : ∀ i<w, m (a+i) = ((x.val.testBit (w-1-i)).toNat : Word w)) :
    accumulate m w a 0 = x :=
  accumulate_word m w a x 0 (by simp [Nat.div_eq_of_lt x.isLt]) bits

end ThreeFlat.RAM.ReadPackedWord

end OAI
