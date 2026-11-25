import OAI.ThreeFlat.RAM.ContinuationLink
import OAI.ThreeFlat.RAM.DeterministicBlock
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.FinCases

namespace OAI
/-! # Repeated execution of a fixed compiled compressor block -/

namespace ThreeFlat.RAM.CompressorIteration

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
open scoped Fin.CommRing
variable {W n k P R K : ℕ}

/-- The loop lives outside the temporary register frame used by the body. Its one persistent
word contains the remaining block count and is decremented before each entry. -/
def control (cell : Word W) (pc : Fin 6 → Fin P) (reg : Fin 3 ↪ Fin R) (body exit : Fin P) :
    Fin 6 → Instr W P R K :=
  ![.constant (reg 0) cell (pc 1), .readExternal (reg 1) (reg 0) (pc 2),
    .constant (reg 2) 0 (pc 3), .jumpEq (reg 1) (reg 2) exit (pc 4),
    .constant (reg 2) 1 (pc 5), .binary .sub (reg 1) (reg 1) (reg 2) body]

/-- One write persists the new count, followed by the body. A direct return to the first
control counter permits unrestricted register use inside the fixed sequence of stages. -/
def block {r : ℕ} (cell : Word W) (controlReg : Fin 3 ↪ Fin r) (b : Block W n r k) : Block W (7+n) r k where
  first := 0
  emit pc reg pub exit :=
    let left := (Fin.castAddEmb n : Fin 7 ↪ Fin (7+n)).trans pc
    let inner := (Fin.natAddEmb 7 : Fin n ↪ Fin (7+n)).trans pc
    let frame := controlReg.trans reg
    let row : Fin 7 → Instr W _ _ _ := Fin.lastCases
      (.writeExternal (frame 0) (frame 1) (inner b.first))
      (control cell (fun i => left i.castSucc) frame (left 6) exit)
    Fin.addCases row (b.emit inner reg pub (left 0))

private def decState (_M : Machine W P R K) (pc : Fin 7 → Fin P) (reg : Fin 3 ↪ Fin R)
    (body : Fin P) (c : Config W P R) (cell : Word W) (m : Memory W) :=
  let r0 := c.put (pc 1) (reg 0) cell
  let r1 := r0.put (pc 2) (reg 1) (m cell.val)
  let r2 := r1.put (pc 3) (reg 2) 0
  let r3 := r2.put (pc 5) (reg 2) 1
  { r3 with pc := body, reg := Function.update r3.reg (reg 1) ((m cell.val)-1) }

/-- Exact effect of the control words on an arbitrary register frame. -/
theorem visit {r : ℕ} (cell : Word W) (b : Block W n r k) (frame : Fin 3 ↪ Fin r)
    (M : Machine W P R K) (pc : Fin (7+n) ↪ Fin P) (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K)
    (exit : Fin P) (installed : (block cell frame b).Installed M pc reg pub exit)
    (c : Config W P R) (mem : Memory W) (entry : c.pc = pc 0) :
    (mem cell.val = 0 → ∃ d, advance M.program 4 c mem = some (d,mem) ∧ d.pc=exit) ∧
    (mem cell.val ≠ 0 → ∃ d, advance M.program 7 c mem = some (d,writeMemory mem cell (mem cell.val-1)) ∧
      d.pc=pc (Fin.natAdd 7 b.first)) := by
  let lp (i : Fin 7) := pc (i.castAdd n)
  let fr := frame.trans reg
  let body := pc (Fin.natAdd 7 b.first)
  have rom (i : Fin 7) : M.code (lp i) = Fin.lastCases
      (.writeExternal (fr 0) (fr 1) body) (control cell (fun j => lp j.castSucc) fr (lp 6) exit) i := by
    simpa [block,lp,fr,body] using installed (i.castAdd n)
  have ctrl (i : Fin 6) : M.code (lp i.castSucc) =
      control cell (fun j => lp j.castSucc) fr (lp 6) exit i := by
    rw [rom, Fin.lastCases_castSucc]
  have op0 : M.code (lp 0) = .constant (fr 0) cell (lp 1) := ctrl 0
  have op1 : M.code (lp 1) = .readExternal (fr 1) (fr 0) (lp 2) := ctrl 1
  have op2 : M.code (lp 2) = .constant (fr 2) 0 (lp 3) := ctrl 2
  have op3 : M.code (lp 3) = .jumpEq (fr 1) (fr 2) exit (lp 4) := ctrl 3
  have op4 : M.code (lp 4) = .constant (fr 2) 1 (lp 5) := ctrl 4
  have op5 : M.code (lp 5) = .binary .sub (fr 1) (fr 1) (fr 2) (lp 6) := ctrl 5
  have op6 : M.code (lp 6) = .writeExternal (fr 0) (fr 1) body := by
    rw [show (6 : Fin 7) = Fin.last 6 by decide, rom, Fin.lastCases_last]
  have start : c.pc=lp 0 := entry
  constructor
  · intro stop
    let z := ((c.put (lp 1) (fr 0) cell).put (lp 2) (fr 1) (mem cell.val)).put exit (fr 2) 0
    refine ⟨z,?_,rfl⟩
    simp (config := {decide:=true}) [advance,Machine.program,start,op0,op1,op2,op3,Instr.run,Config.put,
      fr.injective.eq_iff,z,stop]
  · intro next
    let z := decState M lp fr body c cell mem
    refine ⟨z,?_,rfl⟩
    simp (config := {decide:=true}) [advance,Machine.program,start,op0,op1,op2,op3,op4,op5,op6,Instr.run,
      BinaryOp.eval,Config.put,fr.injective.eq_iff,z,decState,next]

/-- Simulate every iteration, allowing the application-specific memory invariant and body time
to vary with the remaining count. Invalid histories can branch to the machine's reject row. -/
theorem run {r : ℕ} (cell : Word W) (b : Block W n r k) (frame : Fin 3 ↪ Fin r)
    (M : Machine W P R K) (pc : Fin (7+n) ↪ Fin P) (reg : Fin r ↪ Fin R) (pub : Fin k → Fin K)
    (exit : Fin P) (installed : (block cell frame b).Installed M pc reg pub exit)
    (inv : ℕ → Memory W → Prop) (cost : ℕ)
    (body : ∀ z (m : Memory W) (c : Config W P R), inv (z+1) m → (m cell.val).val=z+1 →
      c.pc=pc (Fin.natAdd 7 b.first) → ∃ t ≤ cost, ∃ d m',
        advance M.program t c (writeMemory m cell (m cell.val-1))=some (d,m') ∧
        d.pc=pc 0 ∧ (m' cell.val).val=z ∧ inv z m') :
    ∀ z (c : Config W P R) (m : Memory W), inv z m → (m cell.val).val=z → c.pc=pc 0 →
      ∃ t ≤ z*(7+cost)+4, ∃ d m', advance M.program t c m=some (d,m') ∧ d.pc=exit ∧ inv 0 m' := by
  intro z
  induction z with
  | zero =>
    intro c m hi hv hp
    obtain ⟨d,st,done⟩ := (visit cell b frame M pc reg pub exit installed c m hp).1 (Fin.ext hv)
    exact ⟨4,by simp,d,m,st,done,hi⟩
  | succ z ih =>
    intro c m hi hv hp
    have nz : m cell.val ≠ 0 := by intro h; simp [h] at hv
    obtain ⟨d,pre,next⟩ := (visit cell b frame M pc reg pub exit installed c m hp).2 nz
    obtain ⟨t,ht,c',m',bodyRun,back,rem,inv'⟩ := body z m d hi hv next
    obtain ⟨s,hs,out,last,rest,finish,inv0⟩ := ih c' m' inv' rem back
    refine ⟨7+t+s,?_,out,last,advance_trans (advance_trans pre bodyRun) rest,finish,inv0⟩
    rw [Nat.succ_mul]
    omega

end ThreeFlat.RAM.CompressorIteration

end OAI
