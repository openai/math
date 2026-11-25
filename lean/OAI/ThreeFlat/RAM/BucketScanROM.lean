import OAI.ThreeFlat.RAM.HistoryRowLoop
import Mathlib.Data.Fin.Tuple.Basic
import OAI.ThreeFlat.RAM.NativeOpRows

namespace OAI
/-! # Native table for scanning compact bucket rows -/

namespace ThreeFlat.RAM.BucketScanROM

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM HistoryRowLoop

variable {w p r k n : ℕ}

export NativeRows (opRows contains_opRows)

/-- The 22 original bucket operations precede the guard in the physical table.
The final operation jumps to the guard, which either enters the body or returns. -/
def emit (R : Fin 12 ↪ Fin r) (loc : Fin 23 → Fin p) (exit bad : Fin p) :
    Fin 23 → Instr w p r k :=
  Fin.lastCases (n:=22) (motive:=fun _ => Instr w p r k) (.jumpLt (R 0) (R 5) (loc 0) exit)
    (opRows w (HistoryBucketEmitter.ops R) loc bad)

theorem installed (M : Machine w p r k) (R : Fin 12 ↪ Fin r)
    (loc : Fin 23 → Fin p) (exit bad : Fin p)
    (rows : ∀ i, M.code (loc i) = emit R loc exit bad i) :
    M.code (loc (Fin.last 22)) = .jumpLt (R 0) (R 5) (loc 0) exit ∧
      Contains M bad (loc 0) (HistoryBucketEmitter.ops R) (loc (Fin.last 22)) := by
  constructor
  · exact (rows (Fin.last 22)).trans (Fin.lastCases_last (n:=22))
  · apply contains_opRows M bad (HistoryBucketEmitter.ops (k:=k) R) loc
    intro i
    change Fin 22 at i
    exact (rows i.castSucc).trans (Fin.lastCases_castSucc (n:=22) i)

theorem advance_scan (M : Machine w p r k) (R : Fin 12 ↪ Fin r)
    (loc : Fin 23 → Fin p) (exit bad : Fin p)
    (rows : ∀ i, M.code (loc i) = emit R loc exit bad i)
    (count : ℕ) (state : Word w) (rs : Regs w r) (priv : Word w → Word w) (m : Memory w)
    (size : (rs (R 0)).val + count*3 = (rs (R 5)).val) :
    ∃ out, advance M.program (1+count*23) ⟨loc (Fin.last 22),state,rs,priv⟩ m =
      some (⟨exit,state,out,priv⟩,
        walk BucketRegisters.next BucketRegisters.update count (BucketRegisters.view R rs) m) := by
  obtain ⟨guard,linked⟩ := installed M R loc exit bad rows
  exact BucketRegisters.advance_all M R _ _ exit bad guard linked count state rs priv m size

/-- A complete scan in front of any supplied continuation. Both the scan exit
and the failure target can be selected from the continuation rows. -/
def machine (R : Fin 12 ↪ Fin r) (exit bad : Fin n)
    (tail : Fin n → Instr w (23+n) r k) (data : Fin k → Word w) : Machine w (23+n) r k where
  entry := (Fin.last 22).castAdd n
  code := Fin.addCases (emit R (fun i => i.castAdd n) (Fin.natAdd 23 exit) (Fin.natAdd 23 bad)) tail
  publicData := data

theorem machine_rows (R : Fin 12 ↪ Fin r) (exit bad : Fin n)
    (tail : Fin n → Instr w (23+n) r k) (data : Fin k → Word w) (i : Fin 23) :
    (machine R exit bad tail data).code (i.castAdd n) =
      emit R (fun j => j.castAdd n) (Fin.natAdd 23 exit) (Fin.natAdd 23 bad) i := by
  simp [machine]

theorem machine_tail (R : Fin 12 ↪ Fin r) (exit bad : Fin n)
    (tail : Fin n → Instr w (23+n) r k) (data : Fin k → Word w) (i : Fin n) :
    (machine R exit bad tail data).code (Fin.natAdd 23 i) = tail i := by simp [machine]

end ThreeFlat.RAM.BucketScanROM

end OAI
