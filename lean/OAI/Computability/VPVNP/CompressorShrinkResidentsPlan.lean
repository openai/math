import OAI.Computability.VPVNP.CompressorShrinkResidentLayout
import OAI.Computability.VPVNP.CompressorShrinkResidentOwners

/-!
# Native planner rows for the six-party resident directories

Build hidden and map owner columns, clear their counters, append the dense
ordinals, and publish the six absolute heads in level header cells 30–35.
The chosen layout is read from the score comparison's actual output cell.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkResidentsPlan

open BurstRAM BlockPlanner PhaseRecipe PrimedStackRAM ShrinkResidentLayout
open scoped Fin.CommRing

variable (I : SelectedPlan.Inputs) (first : Expr)

/-- Number of dense resident IDs for the chosen kind, four per motif for hidden residents and
six per motif for maps. -/
def size (maps : Bool) := I.motifs.mul (.lit (radix maps))

/-- Planner expression for the start of the owner column. Hidden owners start at `first`, and
map owners start just after the hidden ID rows. -/
def owner (maps : Bool) :=
  if maps then ((first.add (size I false)).add I.newSites).add (size I false) else first

/-- Planner address of the per-site counters, immediately after the owner column for this
resident kind. -/
def counts (maps : Bool) := (owner I first maps).add (size I maps)

/-- Planner address of the resident ID rows, immediately after the count word for the last
packed site. -/
def rows (maps : Bool) := (counts I first maps).add I.newSites

/-- First address after the map ID rows, which end the workspace for the two resident
directories. -/
def endAddr := (rows I first true).add (size I true)

/-- The six operand expressions for resident collection, giving the resident count, owner base,
site count, counter base, IDs per row, and ID row base. -/
def bank (a : ℕ) (maps : Bool) : Fin 6 → Expr :=
  ![size I maps,owner I first maps,I.newSites,counts I first maps,.lit (rowCapacity a maps),rows I first maps]

/-- The three visits for one resident kind write each ID’s packed owner using the chosen
layout, clear one counter per site, then append the IDs to their owners’ rows. -/
def phases (absoluteCD : Expr) (a : ℕ) (maps : Bool) : List Visit :=
  [ResidentOwners.visit maps (size I maps) absoluteCD (SelectedPlan.roleBase I) (SelectedPlan.layout I) (owner I first maps),
   ops SliceRAM.clearOps 0 (.lit 0) I.newSites (fun _ => counts I first maps),
   ops collectPreimage 3 (.lit 0) (size I maps) (bank I first a maps)]

/-- The six directory bases in publication order, with owner, count, and ID row bases for
hidden residents followed by the same three bases for maps. -/
def heads : Fin 6 → Expr :=
  ![owner I first false,counts I first false,rows I first false,owner I first true,counts I first true,rows I first true]

/-- Six visits that write the resident directory bases to offsets 30 through 35 of the old
level header. -/
def publications (oldLevel : Expr) :=
  List.ofFn fun i : Fin 6 => publish (oldLevel.add (.lit (30+i.val))) (heads I first i)

/-- The complete resident schedule builds the hidden directory, builds the map directory, then
publishes their six bases in the old level header. -/
def visits (oldLevel absoluteCD : Expr) (a : ℕ) :=
  phases I first absoluteCD a false ++ phases I first absoluteCD a true ++ publications I first oldLevel

theorem visits_length (oldLevel absoluteCD : Expr) (a : ℕ) :
    (visits I first oldLevel absoluteCD a).length = 12 := by simp [visits,phases,publications]

section Words

variable {w : ℕ} (pub : Fin 5 → Word w) (st : Word w) (mem : Memory w) (L : Layout)
local notation "ev" => Expr.eval pub st mem

/-- Only the site count, motif count and start of the allocated arena vary
across the linked levels. -/
structure Ready : Prop where
  sites : ev I.newSites = (L.sites : Word w)
  motifs : ev I.motifs = (L.motifs : Word w)
  arena : ev first = (L.first : Word w)

variable (h : Ready I first pub st mem L)

private theorem eval_add (a b : Expr) : ev (a.add b) = ev a + ev b := rfl
private theorem eval_mul (a b : Expr) : ev (a.mul b) = ev a * ev b := rfl
private theorem eval_lit (n : ℕ) : ev (.lit n) = (n : Word w) := rfl

include h in
theorem size_val (maps : Bool) : ev (size I maps) = (L.size maps : Word w) := by
  simp only [size,Layout.size,eval_mul,eval_lit,h.motifs,Nat.cast_mul]

include h in
theorem owner_val (maps : Bool) : ev (owner I first maps) = (L.owner maps : Word w) := by
  cases maps <;> simp [owner,Layout.owner,eval_add,h.arena,size_val I first pub st mem L h,h.sites,Nat.cast_add]

include h in
theorem counts_val (maps : Bool) : ev (counts I first maps) = (L.counts maps : Word w) := by
  simp only [counts,Layout.counts,eval_add,owner_val I first pub st mem L h,size_val I first pub st mem L h,Nat.cast_add]

include h in
theorem rows_val (maps : Bool) : ev (rows I first maps) = (L.rows maps : Word w) := by
  simp only [rows,Layout.rows,eval_add,counts_val I first pub st mem L h,h.sites,Nat.cast_add]

include h in
theorem end_val : ev (endAddr I first) = (L.endAddr : Word w) := by
  simp only [endAddr,Layout.endAddr,eval_add,rows_val I first pub st mem L h,size_val I first pub st mem L h,Nat.cast_add]

include h in
theorem bank_val (a : ℕ) (maps : Bool) :
    (fun i => ev (bank I first a maps i)) = L.params a maps w := by
  funext i
  fin_cases i <;> first | exact size_val I first pub st mem L h maps | exact owner_val I first pub st mem L h maps
                         | exact h.sites | exact counts_val I first pub st mem L h maps | rfl | exact rows_val I first pub st mem L h maps

end Words
end CompressorRecords.ShrinkResidentsPlan

end VPVNP
end Computability
end OAI
