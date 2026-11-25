import OAI.ThreeFlat.RAM.CopyLoop
import OAI.ThreeFlat.RAM.ContinuationLink

namespace OAI
/-! # Native preloading of public input words

Five setup instructions read the source, count and destination from the public
table, compute the exclusive source limit, and set the unit increment. The
remaining five instruction rows implement the forward copy loop. Both the
initial registers and the words outside the input interval may be arbitrary.
-/

namespace ThreeFlat.RAM.PhysicalInputCopy

open Computability.VPVNP.BurstRAM PrivateRAM

variable {w p r k : ℕ}

/-- Public slots 0, 1 and 2 give the source address, word count and destination. -/
def parameters (src count dst : ℕ) : Fin 3 → Word w
  | 0 => Fin.ofNat _ src
  | 1 => Fin.ofNat _ count
  | 2 => Fin.ofNat _ dst

def loopPC (pc : Fin 10 → Fin p) (i : Fin 5) : Fin p := pc (Fin.natAdd 5 i)

private def setup (pc : Fin 10 → Fin p) (reg : Fin 5 ↪ Fin r) (pub : Fin 3 → Fin k) :
    Fin 5 → Instr w p r k
  | 0 => .publicWord (reg 0) (pub 0) (pc 1)
  | 1 => .publicWord (reg 1) (pub 1) (pc 2)
  | 2 => .binary .add (reg 1) (reg 0) (reg 1) (pc 3)
  | 3 => .publicWord (reg 2) (pub 2) (pc 4)
  | 4 => .constant (reg 4) 1 (loopPC pc 0)

/-- Install these ten rows in the caller's ROM. The branch after the last
word jumps to the caller's continuation. -/
def row (pc : Fin 10 → Fin p) (reg : Fin 5 ↪ Fin r) (pub : Fin 3 → Fin k) (exit : Fin p) :
    Fin 10 → Instr w p r k :=
  Fin.addCases (motive := fun _ => Instr w p r k) (setup pc reg pub)
    (CopyLoop.block (loopPC pc) reg exit)

/-- Ten instruction rows, five scratch registers and three public words. -/
def block (w : ℕ) : ContinuationLink.Block w 10 5 3 where
  first := 0
  emit pc reg pub exit := row pc reg pub exit

private def ready (pc : Fin 10 → Fin p) (reg : Fin 5 ↪ Fin r)
    (src count dst : ℕ) (c : Config w p r) : Config w p r :=
  let a : Word w := Fin.ofNat _ src
  let n : Word w := Fin.ofNat _ count
  let cursors := (((c.put (pc 1) (reg 0) a).put (pc 2) (reg 1) n).put
    (pc 3) (reg 1) (a+n)).put (pc 4) (reg 2) (Fin.ofNat _ dst)
  cursors.put (loopPC pc 0) (reg 4) 1

/-- This is the whole external memory at the continuation, including the tail. -/
def copied (src count dst : ℕ) (m : Memory w) : Memory w :=
  CopyLoop.install dst count (fun j => m (src+j)) m

theorem copied_at (src count dst : ℕ) (m : Memory w) (j : ℕ) (h : j < count) :
    copied src count dst m (dst+j) = m (src+j) := by
  simp [copied,CopyLoop.install,h]

theorem copied_outside (src count dst : ℕ) (m : Memory w) (a : ℕ)
    (h : a < dst ∨ dst+count ≤ a) : copied src count dst m a = m a := by
  have h' : ¬ (dst ≤ a ∧ a < dst+count) := by omega
  simp [copied,CopyLoop.install,h']

/-- The complete register state after the deterministic setup and loop. -/
def finalConfig (pc : Fin 10 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p)
    (src count dst : ℕ) (c : Config w p r) (m : Memory w) : Config w p r :=
  CopyLoop.endConfig reg (loopPC pc) exit count (fun j => m (src+j)) (ready pc reg src count dst c)

@[simp] theorem finalConfig_pc (pc : Fin 10 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p)
    (src count dst : ℕ) (c : Config w p r) (m : Memory w) :
    (finalConfig pc reg exit src count dst c m).pc = exit := CopyLoop.endConfig_pc ..

theorem finalConfig_preserves (pc : Fin 10 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p)
    (src count dst : ℕ) (c : Config w p r) (m : Memory w) :
    let out := finalConfig pc reg exit src count dst c m
    out.persistent = c.persistent ∧ out.privateMem = c.privateMem := by
  have keep (n : ℕ) (v : ℕ → Word w) (b : Config w p r) :
      let out := CopyLoop.endConfig reg (loopPC pc) exit n v b
      out.persistent = b.persistent ∧ out.privateMem = b.privateMem := by
    induction n generalizing v b with
    | zero => exact ⟨rfl,rfl⟩
    | succ n ih => exact ih _ _
  exact keep count (fun j => m (src+j)) (ready pc reg src count dst c)

theorem finalConfig_other_reg (pc : Fin 10 → Fin p) (reg : Fin 5 ↪ Fin r) (exit : Fin p)
    (src count dst : ℕ) (c : Config w p r) (m : Memory w) (a : Fin r)
    (outside : ∀ i, a ≠ reg i) : (finalConfig pc reg exit src count dst c m).reg a = c.reg a := by
  unfold finalConfig
  rw [CopyLoop.endConfig_reg _ _ _ _ _ _ _ (outside 0) (outside 2) (outside 3)]
  simp [ready,Config.put,Function.update,outside]

private theorem advance_setup (M : Machine w p r k) (pc : Fin 10 → Fin p)
    (reg : Fin 5 ↪ Fin r) (pub : Fin 3 → Fin k) (exit : Fin p) (src count dst : ℕ)
    (rom : ∀ i, M.code (pc i) = row pc reg pub exit i)
    (par : ∀ i, M.publicData (pub i) = parameters src count dst i)
    (c : Config w p r) (m : Memory w) (start : c.pc = pc 0) :
    advance M.program 5 c m = some (ready pc reg src count dst c, m) := by
  have pre (i : Fin 5) : M.code (pc (Fin.castAdd 5 i)) = setup pc reg pub i := by
    simpa only [row, Fin.addCases_left] using rom (Fin.castAdd 5 i)
  have h0 : M.code (pc 0) = _ := pre 0
  have h1 : M.code (pc 1) = _ := pre 1
  have h2 : M.code (pc 2) = _ := pre 2
  have h3 : M.code (pc 3) = _ := pre 3
  have h4 : M.code (pc 4) = _ := pre 4
  simp (config := { decide := true }) [advance,Machine.program,start,h0,h1,h2,h3,h4,
    setup,Instr.run,par,parameters,BinaryOp.eval,ready,Config.put,Function.update]

/-- From an arbitrary entry configuration, copy exactly `count` scalar words
in `6 + 5*count` instructions. Copying upwards requires disjoint intervals. -/
theorem advance_copy (M : Machine w p r k) (pc : Fin 10 → Fin p)
    (reg : Fin 5 ↪ Fin r) (pub : Fin 3 → Fin k) (exit : Fin p) (src count dst : ℕ)
    (rom : ∀ i, M.code (pc i) = row pc reg pub exit i)
    (par : ∀ i, M.publicData (pub i) = parameters src count dst i)
    (srcFit : src+count < 2^w) (dstFit : dst+count < 2^w)
    (safe : dst ≤ src ∨ src+count ≤ dst)
    (c : Config w p r) (m : Memory w) (start : c.pc = pc 0) :
    advance M.program (6+5*count) c m =
      some (finalConfig pc reg exit src count dst c m, copied src count dst m) := by
  let cfg := ready pc reg src count dst c
  have hv (n : ℕ) (h : n < 2^w) : (Fin.ofNat (2^w) n).val = n := Nat.mod_eq_of_lt h
  have hs := hv src (by omega)
  have hn := hv count (by omega)
  have hd := hv dst (by omega)
  have hsum : ((Fin.ofNat (2^w) src + Fin.ofNat (2^w) count) : Word w).val = src+count := by
    rw [Fin.val_add,hs,hn,Nat.mod_eq_of_lt srcFit]
  have input : (cfg.reg (reg 0)).val = src := by
    simpa (config := {decide := true}) [cfg,ready,Config.put,Function.update] using hs
  have stop : (cfg.reg (reg 1)).val = src+count := by
    simpa (config := {decide := true}) [cfg,ready,Config.put,Function.update] using hsum
  have output : (cfg.reg (reg 2)).val = dst := by
    simpa (config := {decide := true}) [cfg,ready,Config.put,Function.update] using hd
  have unit : cfg.reg (reg 4) = 1 := by simp [cfg,ready]
  have loop (i : Fin 5) : M.code (loopPC pc i) = CopyLoop.block (loopPC pc) reg exit i := by
    simpa only [loopPC,row,Fin.addCases_right] using rom (Fin.natAdd 5 i)
  have run := CopyLoop.advance_block M (loopPC pc) reg exit loop count cfg m rfl
    (by rw [input,stop]) (by rwa [output]) (by rwa [input,output]) unit
  dsimp only at run
  rw [input,output] at run
  rw [show 6+5*count = 5+(1+5*count) by omega]
  exact advance_trans (advance_setup M pc reg pub exit src count dst rom par c m start) run

/-- Preloading the low-address binary input is the copy with source zero.
Every entry below `scratch` survives until the later initialization phase. -/
theorem advance_preload (M : Machine w p r k) (pc : Fin 10 → Fin p)
    (reg : Fin 5 ↪ Fin r) (pub : Fin 3 → Fin k) (exit : Fin p) (count scratch : ℕ)
    (rom : ∀ i, M.code (pc i) = row pc reg pub exit i)
    (par : ∀ i, M.publicData (pub i) = parameters 0 count scratch i)
    (apart : count ≤ scratch) (fits : scratch+count < 2^w)
    (c : Config w p r) (m : Memory w) (start : c.pc = pc 0) :
    advance M.program (6+5*count) c m =
      some (finalConfig pc reg exit 0 count scratch c m, copied 0 count scratch m) :=
  advance_copy M pc reg pub exit 0 count scratch rom par (by omega) fits
    (Or.inr (by omega)) c m start

/-- Three public loads, one add, a constant, and the terminating loop guard
cost 26 word operations. Each word adds a comparison, two probes and two adds. -/
theorem wordWork (pc : Fin 10 → Fin p) (reg : Fin 5 ↪ Fin r) (pub : Fin 3 → Fin k)
    (exit : Fin p) (count : ℕ) :
    let work := fun i => (row (w := w) pc reg pub exit i).wordWork
    work 0 + work 1 + work 2 + work 3 + work 4 + work 5 +
      (work 5 + work 6 + work 7 + work 8 + work 9)*count = 26 + 25*count := by
  rfl

end ThreeFlat.RAM.PhysicalInputCopy

end OAI
