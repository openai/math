import OAI.ThreeFlat.Diagonal.RefreshWidthWriter
import OAI.ThreeFlat.Diagonal.CompressorStageMachine
import OAI.ThreeFlat.RAM.HeaderScanProcedure

namespace OAI
/-! # Linked native pre-admission and admitted-output refresh stages -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.PhysicalPinsExpr RAM.PhysicalProcedure
open RAM.MotifRows RefreshDemandRows CompressorPacking.Native

variable {W a h k : ℕ}

/-- The first seven fields belong to the common history coordinator. -/
def field (current : Word W) (offset : ℕ) : Formula 1 :=
  .load (plus (.load (.lit current.val)) (.lit offset))

def index (current : Word W) (start : ℕ) : Formula 1 := .cut (.reg 0) (field current start)

def oldColumn (current : Word W) (which : ℕ) : Formula 1 :=
  plus (field current 10) (.op .mul (field current 11) (.lit which))

def splitColumn (current : Word W) (which : ℕ) : Formula 1 :=
  plus (field current 12) (.op .mul (field current 11) (.lit which))

def input (current : Word W) : Columns (Formula 1) :=
  ⟨field current 9,oldColumn current 3,oldColumn current 4,splitColumn current 2,splitColumn current 1⟩

/-- Column order is outgoing residual, incoming residual, incoming consumed.
The old six-column table retains its packed full-lane binary displacements. -/
def splitShifts (m : ℕ) (current : Word W) : Formula 1 :=
  let idx := index current 12
  let row := Formula.op .mod idx (field current 11)
  let col := Formula.op .div idx (field current 11)
  let out := readColumn (oldColumn current 2) row
  let rev := readColumn (oldColumn current 5) row
  .select .eq col (.lit 0) (.op .div out (.lit m))
    (.select .eq col (.lit 1) (.op .div rev (.lit m)) (.op .mod rev (.lit m)))

/-- Consecutive triples are shared with the count parser and the physical
local-coefficient builder. They depend only on the input graph and widths. -/
noncomputable def choiceWords (current : Word W) (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size : Fin (k+1) → ℕ) : Formula 1 :=
  let idx := index current 2
  let member := Formula.op .mod idx (.lit 3)
  let row := Formula.op .div idx (.lit 3)
  let z := refreshChoice (input current) (field current 8) row base
  .select .eq member (.lit 0) z.1
    (.select .eq member (.lit 1) z.2 (rowAt (k+1) (fun j => .lit (size j)) z.2))

/-- Materialize the next six adjacency columns with the schedule compiler's
fixed expander transition ROM. -/
def graphWords (current : Word W) (E : SlotGraph (Fin (mPort a)) h) (pad : ℕ) : DescriptorExpr.Term W 0 1 :=
  let old := fun reverse : Bool => Refresh.OldColumns.mk
    (HeaderScan.closed (oldColumn current (if reverse then 3 else 0)))
    (HeaderScan.closed (oldColumn current (if reverse then 4 else 1)))
    (HeaderScan.closed (splitColumn current (if reverse then 1 else 0)))
  refreshColumns E pad old (HeaderScan.closed (field current 14)) (HeaderScan.closed (field current 15))

/-- Source-coordinate sparse-width table used by later local maps. The same
field is already stored among the physical successor's six numbered columns
and is copied into block-major, port-major, expander-slot order here. -/
def sparseCopy (m h pad : ℕ) (current : Word W) : Formula 1 :=
  let idx := index current 3
  let slot := Formula.op .mod idx (.lit h)
  let atPort := Formula.op .div idx (.lit h)
  let port := Formula.op .mod atPort (.lit m)
  let block := Formula.op .div atPort (.lit m)
  let lanes := field current 8
  let lane := Formula.op .mod block lanes
  let base := Formula.op .div block lanes
  let site := plus (.op .mul base (.lit m)) port
  let row := plus (.op .mul site (.lit (1+h+pad))) (plus (.lit 1) slot)
  readColumn (field current 19) (plus (.op .mul row lanes) lane)

noncomputable def prepare (current : Word W) (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size : Fin (k+1) → ℕ) : Procedure W :=
  (HeaderScan.procedure current 12 13 (HeaderScan.closed (splitShifts (mPort a) current))).seq
    (HeaderScan.procedure current 2 18 (HeaderScan.closed (choiceWords current base size)))

/-- The accepted branch performs its graph update, then the physical width
scan, and finally the sparse width scan used by the later kernel compiler.
All arrays and the current header directory are read from memory. -/
noncomputable def commit (current : Word W) (E : SlotGraph (Fin (mPort a)) h) (pad stride : ℕ)
    (base : Fin (k+1) → (Bool × Fin (mPort a) × Fin (mPort a)) → ℕ)
    (size bits : Fin (k+1) → ℕ) (pool : ∀ j, Fin (size j) → Fin (mPort a) → Fin h → ℕ) : Procedure W :=
  let widths := generateWidth (input current) (field current 8) (index current 19) (field current 1)
    pad stride base size bits pool
  (HeaderScan.procedure current 14 16 (graphWords current E pad)).seq
    ((HeaderScan.procedure current 19 17 (HeaderScan.closed widths)).seq
      (HeaderScan.procedure current 3 20 (HeaderScan.closed (sparseCopy (mPort a) h pad current))))

end ThreeFlat.Diagonal.RefreshStageNav

end OAI
