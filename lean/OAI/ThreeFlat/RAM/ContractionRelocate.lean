import OAI.ThreeFlat.RAM.NativeRelocate
import OAI.ThreeFlat.RAM.ContractionMachine

namespace OAI
/-! # Relocating contraction code inside a larger RAM -/

namespace ThreeFlat.RAM.ContractionTail

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM

variable {w P R K : ℕ}

/-- Install one of the 35 contraction rows in the caller's register and control layout. -/
abbrev relocate (pc : Fin 35 ↪ Fin P) (reg : Fin 10 ↪ Fin R) (pub : Fin 5 → Fin K) :
    Instr w 35 10 5 → Instr w P R K := NativeRelocate.relocate pc reg pub

theorem instruction_externalOnly (i : Fin 35) :
    NativeRelocate.ExternalOnly (Contraction.instruction (w := w) i) := by
  unfold Contraction.instruction
  split <;> trivial

variable (pc : Fin 35 ↪ Fin P) (reg : Fin 10 ↪ Fin R) {F : Type*} [Semiring F]

/-- Fuel-by-fuel execution of the relocated table agrees on every external memory. -/
theorem mass_eq_eval (pub : Fin 5 → Fin K) (M : Machine w P R K)
    (param : Fin 5 → Word w)
    (hcode : ∀ i, M.code (pc i) = relocate pc reg pub (Contraction.instruction i))
    (hpub : ∀ i, M.publicData (pub i) = param i) (code : FieldCode F w)
    (fuel : ℕ) (c : Config w P R) (m : Memory w) (i : Fin 35) (hc : c.pc = pc i) :
    mass code M.program fuel c m =
      Contraction.eval code param fuel i (fun j => c.reg (reg j)) m :=
  NativeRelocate.mass_eq pc reg pub (Contraction.machine param) M instruction_externalOnly
    hcode hpub code fuel c (Contraction.config i (fun j => c.reg (reg j))) m hc (fun _ => rfl)

end ThreeFlat.RAM.ContractionTail

end OAI
