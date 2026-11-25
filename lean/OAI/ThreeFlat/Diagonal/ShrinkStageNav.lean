import OAI.ThreeFlat.Diagonal.ShrinkIntegerLayout
import OAI.ThreeFlat.Diagonal.RefreshWidthWriter
import OAI.ThreeFlat.RAM.MotifRows
import OAI.ThreeFlat.RAM.HeaderScanProcedure

namespace OAI
/-! # Native row choice, admitted widths and common survivor layout of a shrink stage -/

namespace ThreeFlat.Diagonal.ShrinkStageNav

open Computability.VPVNP.BurstRAM RAM RAM.PhysicalPinsExpr RAM.MotifRows RAM.PhysicalProcedure ShrinkMotif
open scoped Classical BigOperators

noncomputable section
variable {W n : ℕ}

def ptr (current : Word W) (offset : ℕ) : Formula 1 := field (.load (.lit current.val)) offset

def rel (current : Word W) (start : ℕ) : Formula 1 := .cut (.reg 0) (ptr current start)

def atRow (base row : Formula 1) (stride : ℕ) : Formula 1 := plus base (.op .mul row (.lit stride))

/-- Row zero and its ordered tail are stored in the native instruction text. -/
def choiceWords {last : ℕ} (current : Word W) (base : Fin (last+1) → Fin 2 → ℕ)
    (size : Fin (last+1) → ℕ) : Formula 1 :=
  let pos := rel current 2
  let row := Formula.op .div pos (.lit 3)
  let col := Formula.op .mod pos (.lit 3)
  let z := RefreshDemandRows.chooseFields (fun e : Fin 2 => field (atRow (ptr current 8) row 2) e.val) base
  .select .eq col (.lit 0) z.1 (.select .eq col (.lit 1) z.2 (RefreshDemandRows.rowAt _ (fun i => .lit (size i)) z.2))

/-- Zero padding of every K-word count row is checked before this instruction sweep is called. -/
def widthWords {last : ℕ} (current : Word W) (K : ℕ) (size bits : Fin (last+1) → ℕ)
    (pool : ∀ i, Fin (size i) → Fin 8 → ℕ) : Formula 1 :=
  let pos := rel current 3
  let row := Formula.op .div pos (.lit 8)
  let edge := Formula.op .mod pos (.lit 8)
  let desc := atRow (ptr current 2) row 3
  let counts := atRow (ptr current 1) row K
  RefreshDemandRows.rowAt _ (fun j => RefreshDemandRows.rowAt 8 (fun e => outputWidth (fun a => pool j a e) counts
    (field desc 0) (bits j)) edge) (field desc 1)

def localCost (width : Formula 1) (b : Bool) : Formula 1 :=
  totals ((List.finRange 4).map fun j =>
    let e := survivor b j
    let x := field width e.val
    Formula.op .mul (.lit (multiplier e)) (.op .mul x x))

/-- Interleaving false and true prefix sums ensures each transition reads a completed lower
address. The first two words are zero even when the motif array is empty. -/
def prefixWords (current : Word W) : Formula 1 :=
  let pos := rel current 30
  let row := Formula.cut (.op .div pos (.lit 2)) (.lit 1)
  let width := atRow (ptr current 3) row 8
  let here := Formula.select .eq (.op .mod pos (.lit 2)) (.lit 0) (localCost width false) (localCost width true)
  .select .lt pos (.lit 2) (.lit 0) (plus (.load (.cut (.reg 0) (.lit 2))) here)

/-- Select true only upon strict improvement, as in `ShrinkMotif.chooseWidths`. -/
def layoutWord (current : Word W) : Formula 1 :=
  let tail := atRow (ptr current 30) (ptr current 0) 2
  .select .lt (field tail 1) (field tail 0) (.lit 1) (.lit 0)

def prepare {last : ℕ} (current : Word W) (base : Fin (last+1) → Fin 2 → ℕ)
    (size : Fin (last+1) → ℕ) : Procedure W :=
  HeaderScan.procedure current 2 28 (HeaderScan.closed (choiceWords current base size))

def commit {last : ℕ} (current : Word W) (K : ℕ) (size bits : Fin (last+1) → ℕ)
    (pool : ∀ i, Fin (size i) → Fin 8 → ℕ) : Procedure W :=
  (HeaderScan.procedure current 3 29 (HeaderScan.closed (widthWords current K size bits pool))).seq
    ((HeaderScan.procedure current 30 31 (HeaderScan.closed (prefixWords current))).seq
      (HeaderScan.procedure current 32 33 (HeaderScan.closed (layoutWord current))))

end
end ThreeFlat.Diagonal.ShrinkStageNav

end OAI
