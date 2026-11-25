import OAI.ThreeFlat.RAM.TickCheckSetup
import OAI.ThreeFlat.RAM.TickGenerateTable
import OAI.ThreeFlat.RAM.ChunkRequestLink

namespace OAI
/-! # A finite native ROM for a continuing generated comparison -/

namespace ThreeFlat.RAM.TickCheckedBank

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr ChunkRequests
open scoped Fin.CommRing

variable {w p r k : ℕ}

/-- A generator, seven constant setup instructions, and the actual reader with
an embedded zero-weight rejection counter. All valid paths leave via one exit. -/
def count (e : Term w k 1) := (e.labels+6)+(7+93)

def generatePC (e : Term w k 1) (pc : Fin (count e) ↪ Fin p) :=
  (Fin.castAddEmb (7+93)).trans pc

def setupPC (e : Term w k 1) (pc : Fin (count e) ↪ Fin p) :=
  (Fin.castAddEmb 93).trans ((Fin.natAddEmb (e.labels+6)).trans pc)

def scanPC (e : Term w k 1) (pc : Fin (count e) ↪ Fin p) :=
  (Fin.natAddEmb 7).trans ((Fin.natAddEmb (e.labels+6)).trans pc)

def emit (e : Term w k 1) (start stop old new : Word w) (pc : Fin (count e) ↪ Fin p)
    (genReg : Fin (4+e.binds) ↪ Fin r) (chkReg : Fin 37 ↪ Fin r) (exit : Fin p) :
    Fin (count e) → Instr w p r k :=
  let a := generatePC e pc
  let b := setupPC e pc
  let d := scanPC e pc
  let rr := linkedRegisters w k chkReg
  Fin.append (TickGenerateTable.emit e start stop a genReg (b 0))
    (Fin.append (TickCheckSetup.emit b rr.slot (TickCheckSetup.values start old new stop) (linkedLabels w k d).guard)
      ((linkedBlock w).emit d chkReg Fin.elim0 exit))

structure Installed (M : Machine w p r k) (e : Term w k 1) (start stop old new : Word w)
    (pc : Fin (count e) ↪ Fin p) (genReg : Fin (4+e.binds) ↪ Fin r)
    (chkReg : Fin 37 ↪ Fin r) (exit : Fin p) : Prop where
  get : ∀ i, M.code (pc i) = emit e start stop old new pc genReg chkReg exit i

variable {M : Machine w p r k} {e : Term w k 1} {start stop old new : Word w}
    {pc : Fin (count e) ↪ Fin p} {reg : Fin (4+e.binds) ↪ Fin r} {ck : Fin 37 ↪ Fin r} {exit : Fin p}

theorem Installed.gen (h : Installed M e start stop old new pc reg ck exit) (i : Fin (e.labels+6)) :
    M.code (generatePC e pc i) = TickGenerateTable.emit e start stop (generatePC e pc)
      reg (setupPC e pc 0) i := by
  change M.code (pc (i.castAdd (7+93))) = _
  simpa only [emit,Fin.append_left] using h.get (i.castAdd (7+93))

theorem Installed.setup (h : Installed M e start stop old new pc reg ck exit) (i : Fin 7) :
    M.code (setupPC e pc i) = TickCheckSetup.emit (setupPC e pc) (linkedRegisters w k ck).slot
      (TickCheckSetup.values start old new stop) (linkedLabels w k (scanPC e pc)).guard i := by
  change M.code (pc (Fin.natAdd (e.labels+6) (i.castAdd 93))) = _
  simpa only [emit,Fin.append_right,Fin.append_left] using h.get (Fin.natAdd (e.labels+6) (i.castAdd 93))

theorem Installed.check (h : Installed M e start stop old new pc reg ck exit) :
    ContinueInstalled M (linkedRegisters w k ck) (linkedLabels w k (scanPC e pc)) (ck 36)
      (linkedControl (scanPC e pc) 3) (linkedControl (scanPC e pc) 4) exit := by
  apply linkedBlock_installed M (scanPC e pc) ck Fin.elim0 exit
  intro i
  change M.code (pc (Fin.natAdd (e.labels+6) (Fin.natAdd 7 i))) = _
  simpa only [emit,Fin.append_right] using h.get (Fin.natAdd (e.labels+6) (Fin.natAdd 7 i))

/-- A bank may be put directly in front of an arbitrary continuation ROM. -/
def machine {t : ℕ} (e : Term w k 1) (start stop old new : Word w) (next : Fin t)
    (tail : (Fin t ↪ Fin (count e+t)) → Fin t → Instr w (count e+t) (max (4+e.binds) 37) k)
    (params : Fin k → Word w) :
    Machine w (count e+t) (max (4+e.binds) 37) k :=
  let outer := Fin.castAddEmb t
  let genReg := Fin.castLEEmb (Nat.le_max_left (4+e.binds) 37)
  let chkReg := Fin.castLEEmb (Nat.le_max_right (4+e.binds) 37)
  let cont := Fin.natAddEmb (count e)
  ⟨TickGenerateTable.driver e (generatePC e outer) 0,
    Fin.append (emit e start stop old new outer genReg chkReg (cont next)) (tail cont),params⟩

theorem machine_installed {t : ℕ} (e : Term w k 1) (start stop old new : Word w) (next : Fin t)
    (tail : (Fin t ↪ Fin (count e+t)) → Fin t → Instr w (count e+t) (max (4+e.binds) 37) k)
    (params : Fin k → Word w) :
    Installed (machine e start stop old new next tail params) e start stop old new (Fin.castAddEmb t)
      (Fin.castLEEmb (Nat.le_max_left _ _)) (Fin.castLEEmb (Nat.le_max_right _ _)) (Fin.natAdd (count e) next) := by
  constructor
  intro i
  simp [machine]

end ThreeFlat.RAM.TickCheckedBank

end OAI
