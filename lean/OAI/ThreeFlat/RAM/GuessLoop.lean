import OAI.ThreeFlat.RAM.ContractionMemory
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
/-! # Native loop for guessing a contiguous binary string

The four registers contain the next address, end address, scratch bit and
unit increment. At termination the caller receives the actual updated
configuration and memory and continues with its residual fuel.
-/

namespace ThreeFlat.RAM.GuessLoop

open Computability.VPVNP.BurstRAM PrivateRAM

variable {F : Type*} [Semiring F] {w p r k : ℕ}

def block (pc : Fin 6 → Fin p) (reg : Fin 4 ↪ Fin r) (exit : Fin p) :
    Fin 6 → Instr w p r k
  | 0 => .jumpLt (reg 0) (reg 1) (pc 1) exit
  | 1 => .choose (pc 3) (pc 2)
  | 2 => .constant (reg 2) 0 (pc 4)
  | 3 => .constant (reg 2) 1 (pc 4)
  | 4 => .writeExternal (reg 0) (reg 2) (pc 5)
  | 5 => .binary .add (reg 0) (reg 0) (reg 3) (pc 0)

def next (reg : Fin 4 ↪ Fin r) (pc : Fin 6 → Fin p) (c : Config w p r) (b : Bool) :
    Config w p r :=
  (c.put (pc 4) (reg 2) (BitLayout.bitWord w b)).put (pc 0) (reg 0) (c.reg (reg 0) + 1)

def endConfig (reg : Fin 4 ↪ Fin r) (pc : Fin 6 → Fin p) (exit : Fin p) :
    (n : ℕ) → (Fin n → Bool) → Config w p r → Config w p r
  | 0, _, c => {c with pc := exit}
  | n+1, f, c => endConfig reg pc exit n (fun j => f j.succ) (next reg pc c (f 0))

/-- Install the guessed words at consecutive natural addresses, preserving every other word. -/
def install (start : ℕ) {n : ℕ} (f : Fin n → Bool) (m : Memory w) : Memory w :=
  fun a => if h : start ≤ a ∧ a < start + n then
    BitLayout.bitWord w (f ⟨a-start, by omega⟩) else m a

@[simp] theorem install_get (start : ℕ) {n : ℕ} (f : Fin n → Bool)
    (m : Memory w) (i : Fin n) : install start f m (start+i.val) = BitLayout.bitWord w (f i) := by
  simp [install, i.isLt]

@[simp] theorem install_zero (start : ℕ) (f : Fin 0 → Bool) (m : Memory w) :
    install start f m = m := by
  funext a
  simp [install]

private theorem install_cons (addr : Word w) {n : ℕ} (f : Fin (n+1) → Bool) (m : Memory w) :
    install addr.val f m = install (addr.val+1) (fun j : Fin n => f j.succ)
      (writeMemory m addr (BitLayout.bitWord w (f 0))) := by
  funext a
  by_cases ha : a = addr.val
  · subst a
    simp [install, writeMemory]
  · by_cases hr : addr.val ≤ a ∧ a < addr.val + (n+1)
    · have hs : addr.val + 1 ≤ a ∧ a < addr.val + 1 + n := by omega
      simp only [install, dite_eq_left hr, dite_eq_left hs]
      congr 2
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    · have hs : ¬(addr.val + 1 ≤ a ∧ a < addr.val + 1 + n) := by omega
      simp [install, hr, hs, writeMemory, ha]

private theorem mass_one (code : FieldCode F w) (M : Machine w p r k)
    (pc : Fin 6 → Fin p) (reg : Fin 4 ↪ Fin r) (exit : Fin p)
    (hm : ∀ i, M.code (pc i) = block pc reg exit i)
    (c : Config w p r) (m : Memory w) (fuel : ℕ)
    (hc : c.pc = pc 0) (hl : c.reg (reg 0) < c.reg (reg 1)) (hi : c.reg (reg 3) = 1) :
    mass code M.program (fuel+5) c m =
      mass code M.program fuel (next reg pc c false)
        (writeMemory m (c.reg (reg 0)) (BitLayout.bitWord w false)) +
      mass code M.program fuel (next reg pc c true)
        (writeMemory m (c.reg (reg 0)) (BitLayout.bitWord w true)) := by
  have h02 : reg 0 ≠ reg 2 := reg.injective.ne (by decide)
  have h32 : reg 3 ≠ reg 2 := reg.injective.ne (by decide)
  simp [mass, Machine.program, hm, hc, hl, block, Instr.run, Config.put, Function.update_of_ne,
    hi, h02, h32, next, BitLayout.bitWord, BinaryOp.eval]
  rfl

/-- Installing this six-instruction loop into any machine runs five steps per guessed
bit and a final bounds check, then enters its continuation with the chosen writes. -/
theorem mass_block (code : FieldCode F w) (M : Machine w p r k)
    (pc : Fin 6 → Fin p) (reg : Fin 4 ↪ Fin r) (exit : Fin p)
    (hm : ∀ i, M.code (pc i) = block pc reg exit i)
    (n fuel : ℕ) (c : Config w p r) (m : Memory w) (hc : c.pc = pc 0)
    (hn : (c.reg (reg 0)).val + n = (c.reg (reg 1)).val) (hi : c.reg (reg 3) = 1) :
    mass code M.program (fuel+1+5*n) c m =
      ∑ f : Fin n → Bool, mass code M.program fuel (endConfig reg pc exit n f c)
        (install (c.reg (reg 0)).val f m) := by
  classical
  induction n generalizing c m with
  | zero =>
    have he : c.reg (reg 0) = c.reg (reg 1) := Fin.ext (by simpa using hn)
    simp [mass, Machine.program, hc, hm, block, Instr.run, he, endConfig]
  | succ n ih =>
    have hl : c.reg (reg 0) < c.reg (reg 1) := by change _ < (c.reg (reg 1)).val; omega
    have h12 : reg 1 ≠ reg 2 := reg.injective.ne (by decide)
    have h10 : reg 1 ≠ reg 0 := reg.injective.ne (by decide)
    have h32 : reg 3 ≠ reg 2 := reg.injective.ne (by decide)
    have h30 : reg 3 ≠ reg 0 := reg.injective.ne (by decide)
    have ha : (c.reg (reg 0) + 1).val = (c.reg (reg 0)).val+1 := by
      rw [Fin.val_add_one_of_lt']
      change (c.reg (reg 0)).val+1 < 2^w
      have he := (c.reg (reg 1)).isLt
      omega
    have hnext (b : Bool) : ((next reg pc c b).reg (reg 0)).val + n =
        ((next reg pc c b).reg (reg 1)).val := by
      simp [next, Config.put, Function.update_of_ne, h10, h12, ha]
      omega
    have hunit (b : Bool) : (next reg pc c b).reg (reg 3) = 1 := by
      simp [next, Config.put, Function.update_of_ne, h30, h32, hi]
    rw [show fuel+1+5*(n+1) = (fuel+1+5*n)+5 by omega,
      mass_one code M pc reg exit hm _ _ _ hc hl hi, ih _ _ rfl (hnext false) (hunit false),
      ih _ _ rfl (hnext true) (hunit true)]
    let along (f : Fin (n+1) → Bool) := mass code M.program fuel (endConfig reg pc exit (n+1) f c)
      (install (c.reg (reg 0)).val f m)
    change _ = ∑ f, along f
    rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp along, Fintype.sum_prod_type,
      Fintype.sum_bool, add_comm]
    congr 1 <;> refine Finset.sum_congr rfl fun f _ => ?_ <;>
      simp [along, endConfig, Fin.consEquiv, install_cons (c.reg (reg 0)), next, Config.put, ha]

end ThreeFlat.RAM.GuessLoop

end OAI
