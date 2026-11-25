import OAI.ThreeFlat.RAM.TickPaddedTail
import OAI.ThreeFlat.RAM.ContinuationLink

namespace OAI
/-! # Fixed coefficient and padding ROM for all selected forests -/

namespace ThreeFlat.RAM.TickPaddedROM
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr ContinuationLink
open scoped Fin.CommRing

variable {F : Type*} {t w : ℕ}
def binds (t : ℕ) := 3*(8*t)+3
def labels (t : ℕ) := 3*(binds t)+7

theorem tableLabels {k : ℕ} (code : FieldCode F w) (table : Fin t → (Fin 3 → Bool) → F)
    (lut : ℕ) : (TickLUTSeed.expr (k:=k) code table lut).labels+6 = labels t := by
  rw [Term.labels_eq,TickLUTSeed.expr_binds]
  rfl

theorem tableRegs {k : ℕ} (code : FieldCode F w) (table : Fin t → (Fin 3 → Bool) → F)
    (lut : ℕ) : 4+(TickLUTSeed.expr (k:=k) code table lut).binds = 4+binds t := by
  rw [TickLUTSeed.expr_binds]
  rfl

def tableBlock (code : FieldCode F w) (table : Fin t → (Fin 3 → Bool) → F) (lut : ℕ) :
    Block w (labels t) (4+binds t) 0 where
  first := ⟨3*(binds t)+1,by unfold labels; omega⟩
  emit {P R K} pc reg _ exit i := by
    let e := TickLUTSeed.expr (k:=K) code table lut
    let h := tableLabels (k:=K) code table lut
    let hR := tableRegs (k:=K) code table lut
    exact TickGenerateTable.emit e (lut : Word w) (lut+8*t : ℕ) (fun j => pc (Fin.cast h j))
      ((finCongr hR).toEmbedding.trans reg) exit (Fin.cast h.symm i)

theorem padLabels {k : ℕ} (base : Fin k) : HistoryPadROM.count (w:=w) base = 96 := by
  rw [HistoryPadROM.count,Term.labels_eq,HistoryPadDriver.term_binds]

theorem padRegs {k : ℕ} (base : Fin k) : 4+(HistoryPadDriver.term (w:=w) base).binds = 33 := by
  rw [HistoryPadDriver.term_binds]

def padBlock (w last : ℕ) : Block w 96 33 1 where
  first := 94
  emit {P R K} pc reg par exit i := by
    let base := par 0
    let h := padLabels (w:=w) base
    exact HistoryPadROM.emit base (last : Word w) (fun j => pc (Fin.cast h j))
      ((finCongr (padRegs (w:=w) base)).toEmbedding.trans reg) exit (Fin.cast h.symm i)

/-- Only the fixed coefficient table, the final fixed-shape metadata limit and
its public scratch base enter the two linked instruction banks. -/
def block (code : FieldCode F w) (table : Fin t → (Fin 3 → Bool) → F) (lut last : ℕ) :
    Block w (labels t+96) (max (4+binds t) 33) 1 :=
  let seed := (tableBlock code table lut).reindex (Fin.castLEEmb (le_max_left _ _)) Fin.elim0
  let pad := (padBlock w last).reindex (Fin.castLEEmb (le_max_right _ _)) id
  seed.seq pad

end ThreeFlat.RAM.TickPaddedROM

end OAI
