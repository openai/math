import OAI.ThreeFlat.RAM.TickPaddedBankRun
import OAI.ThreeFlat.RAM.HistoryCompiledRows

namespace OAI
/-! # One terminal initializer for every forest of a fixed-capacity tick -/

noncomputable section
namespace ThreeFlat.RAM.TickPaddedROM
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink BitLayout HistoryFactors Diagonal.TraceCircuit
open scoped Fin.CommRing

variable {F : Type*} [Field F] [Fintype F] {w p pc r k : ℕ}

def catalog (F : Type*) [Fintype F] [Zero F] [One F] :
    Fin (Fintype.card ((Fin 3 → Bool) → F)+2) → (Fin 3 → Bool) → F :=
  Fin.addCases (Fintype.equivFin _).symm ![fun z => if z 0 then 0 else 1,fun _ => 1]

def fixed (code : FieldCode F w) («meta» lut J : ℕ) :=
  block code (catalog F) lut («meta»+4*J)

theorem advance_fixed (code : FieldCode F w) (N : BitNetwork F p) (b u J «meta» lut : ℕ)
    (rowsCount : N.cells+b+u=J) (M : Machine w pc r k) (base : Fin k)
    (P : Fin (labels (Fintype.card ((Fin 3 → Bool) → F)+2)+96) ↪ Fin pc)
    (R : Fin (max (4+binds (Fintype.card ((Fin 3 → Bool) → F)+2)) 33) ↪ Fin r) (exit : Fin pc)
    (rom : (fixed code «meta» lut J).Installed M P R (fun _ => base) exit)
    (c : Config w pc r) (m : Memory w) (entry : c.pc=P (fixed code «meta» lut J).first)
    (safe : «meta»+4*J ≤ lut) (fit : lut+8*(Fintype.card ((Fin 3 → Bool) → F)+2) < 2^w)
    (control : ∀ j : Fin 4, HistoryPadDriver.header (M.publicData base) m j =
      ![(«meta»+4*N.cells : ℕ),(b : Word w),(hiddenBase p+N.internal : ℕ),
        (Fintype.card ((Fin 3 → Bool) → F) : Word w)] j)
    (away : ∀ j : Fin 4, (M.publicData base+(j.val : Word w)).val < «meta»+4*N.cells ∨
      lut+8*(Fintype.card ((Fin 3 → Bool) → F)+2) ≤ (M.publicData base+(j.val : Word w)).val)
    (rows : ∀ i : Fin N.cells, ∀ j : Fin 4, m («meta»+4*i.val+j.val) =
      metadataWord (HistoryCompiledRows.library N) i j) :
    let t := Fintype.card ((Fin 3 → Bool) → F)+2
    ∃ time ≤ (4+8*t*(6*(8*t)+10))+(5+62*(4*(b+u))),
      ∃ d : Config w pc r, ∃ out : Memory w, d.pc=exit ∧
        advance M.program time c m = some (d,out) ∧
        Stores (addPadding N b u) ((HistoryCompiledRows.library N).padded b u) code «meta» lut out ∧
        ∀ i < «meta», out i=m i := by
  let L := HistoryCompiledRows.library N
  have last : «meta»+4*N.cells+4*(b+u)=«meta»+4*J := by omega
  have installed : (block code (L.padded b u).table lut («meta»+4*N.cells+4*(b+u))).Installed
      M P R (fun _ => base) exit := by rw [last]; exact rom
  have pc0 : c.pc=P (block code (L.padded b u).table lut («meta»+4*N.cells+4*(b+u))).first := by
    rw [last]; exact entry
  exact advance_bank code N L b u «meta» lut M base P R exit installed c m pc0 (by omega)
    fit control away rows

end ThreeFlat.RAM.TickPaddedROM

end
end OAI
