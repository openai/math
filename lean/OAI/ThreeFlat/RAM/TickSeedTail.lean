import OAI.ThreeFlat.RAM.TickGenerateTable
import OAI.ThreeFlat.RAM.TickClearLink

namespace OAI
/-! # Emitting the field table, register prologue and terminal weighted evaluator -/

namespace ThreeFlat.RAM.TickSeedTail
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr NativeRelocate

open scoped Fin.CommRing

variable {w k p r : ℕ}

def count (e : Term w k 1) := (e.labels+6)+(36+108)

def genPC (e : Term w k 1) (P : Fin (count e) ↪ Fin p) := (Fin.castAddEmb (36+108)).trans P
def clearRows (e : Term w k 1) (P : Fin (count e) ↪ Fin p) :=
  (Fin.castAddEmb 108).trans ((Fin.natAddEmb (e.labels+6)).trans P)
def runPC (e : Term w k 1) (P : Fin (count e) ↪ Fin p) :=
  (Fin.natAddEmb 36).trans ((Fin.natAddEmb (e.labels+6)).trans P)

def clearPC (e : Term w k 1) (P : Fin (count e) ↪ Fin p) (first : Fin 108) :=
  TickClearFrame.locations (clearRows e P) (runPC e P first)

def emit (e : Term w k 1) (first last : Word w) (native : Machine w 108 36 7)
    (P : Fin (count e) ↪ Fin p) (genR : Fin (4+e.binds) ↪ Fin r)
    (R : Fin 36 ↪ Fin r) (K : Fin 7 → Fin k) : Fin (count e) → Instr w p r k :=
  Fin.append (TickGenerateTable.emit e first last (genPC e P) genR (clearPC e P native.entry 0))
    (Fin.append (TickClearFrame.row (clearPC e P native.entry) R)
      (fun i => relocate (runPC e P) R K (native.code i)))

variable (e : Term w k 1) (first last : Word w) (native : Machine w 108 36 7)
    (M : Machine w p r k) (P : Fin (count e) ↪ Fin p) (genR : Fin (4+e.binds) ↪ Fin r)
    (R : Fin 36 ↪ Fin r) (K : Fin 7 → Fin k)
    (rom : ∀ i, M.code (P i) = emit e first last native P genR R K i)

include rom in
theorem gen_installed (i : Fin (e.labels+6)) :
    M.code (genPC e P i) = TickGenerateTable.emit e first last (genPC e P) genR
      (clearPC e P native.entry 0) i := by
  change M.code (P (i.castAdd (36+108))) = _
  simpa only [emit,Fin.append_left] using rom (i.castAdd (36+108))

include rom in
theorem clear_installed (i : Fin 36) :
    M.code (clearPC e P native.entry i.castSucc) = TickClearFrame.row (clearPC e P native.entry) R i := by
  conv_lhs => rw [clearPC,TickClearFrame.locations_castSucc]
  change M.code (P (Fin.natAdd (e.labels+6) (i.castAdd 108))) = _
  simpa only [emit,Fin.append_right,Fin.append_left] using
    rom (Fin.natAdd (e.labels+6) (i.castAdd 108))

include rom in
theorem interpreter_installed (i : Fin 108) : M.code (runPC e P i) = relocate (runPC e P) R K (native.code i) := by
  change M.code (P (Fin.natAdd (e.labels+6) (Fin.natAdd 36 i))) = _
  simpa only [emit,Fin.append_right] using rom (Fin.natAdd (e.labels+6) (Fin.natAdd 36 i))

@[simp] theorem clear_to_eval : clearPC e P native.entry (Fin.last 36) = runPC e P native.entry :=
  TickClearFrame.locations_last _ _

end ThreeFlat.RAM.TickSeedTail

end OAI
