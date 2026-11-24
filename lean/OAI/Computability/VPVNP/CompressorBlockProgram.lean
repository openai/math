import OAI.Computability.VPVNP.CompressorBlockDataHeads
import OAI.Computability.VPVNP.CompressorRefreshBlockPlan
import OAI.Computability.VPVNP.CompressorRefreshPlacementRows
import OAI.Computability.VPVNP.CompressorShrinkResidentsPlan
import OAI.Computability.VPVNP.CompressorBlockMetadata
import OAI.Computability.VPVNP.CompressorShrinkLevelSpace
import OAI.Computability.VPVNP.CompressorDescriptorTableFits

/-!
# The online descriptor program for a fixed compression template

The initial four visits publish the cursor counts, construct its incidence
table and mark its role. One block contains the prescribed shrinking
substeps in increasing order and one degree refresh. Every phase computes
its operands from the live RAM. The script depends on the fixed compressor
template. The input size, iteration count and choices enter through RAM
and the branch tapes.

Table zero holds the greedy, rank, term and selected placement data of a
shrink, or the packed allocation of a refresh. Tables one through five
hold the AB intersections, surviving width and interval rows, sorted-slot
workspace, refresh preimages, and shrink resident tables, respectively.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.BlockProgram

open BurstRAM PhaseRecipe BlockPlanner Compression DescriptorSpace
open scoped Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Per-site scratch allowance for refresh segment columns, demands, term records, supply,
expander tables and output incidence. -/
def refreshRate :=
  let s := RefreshBlockPlan.shape B
  7*s.ports+s.ties+s.stride+3*s.dH+6*s.degree

/-- The resident arrays contain twice the combined number of hidden and
map occurrences, plus one count for each new site in each directory. -/
def residentRate (S : BlockSchedule k) := 20*slotDegree S+2

/-- Reserved field count per table slot, covering the largest shrinking, refresh or resident
workspace with three extra fields. -/
def fieldCount := max (ShrinkLevelSpace.tableFactor S) (max (refreshRate B) (residentRate S))+3

/-- Only the scalar, table, slot and field dimensions are compiled into the
phase programs. The physical directory below uses the resulting catalog
arity and chronological row counts. -/
def geometry : Shape :=
  ⟨0,0,0,0,54,6,slotDegree S,fieldCount B⟩

/-- Expression reading the base address of one of the six tables at the given level. -/
def arena (step : ℕ) (index : Fin 6) : Expr := LevelFields.table (geometry B) step index

/-- Four visits publishing the term base, term stride, layout and absolute operand at header
offsets 36 through 39. -/
def termPointers (step : ℕ) (termHead termStride layout absolute : Expr) : List Visit :=
  let operands : Fin 4 → Expr := ![termHead,termStride,layout,absolute]
  List.ofFn fun j : Fin 4 ↦ BlockPlanner.publish (LevelFields.address step (36+j.val)) (operands j)

theorem termPointers_length (step : ℕ) (h s l a : Expr) : (termPointers step h s l a).length =
    4 := by
  simp [termPointers]

/-- Every selected graph level uses the old graph's published columns and
writes the next graph's canonical incidence columns. -/
def shrink (i : Fin S.steps) : List Visit :=
  let F := geometry B
  let step := i.val
  let a := ShrinkBlockInputs.a i
  let origin := arena B step 0
  let chosen := ShrinkBlockInputs.selectedInputs B F i origin
  let absolute := ShrinkBundlePlan.absoluteCD step a origin
  ShrinkBlockInputs.beforeSlices B F i origin ++
    ShrinkResidentsPlan.visits chosen (arena B step 5) (LevelFields.atLevel step) absolute a ++
    BlockSlices.visits B F i origin (arena B step 1) (arena B step 2) ++
    ShrinkBlockInputs.slots B F i origin (arena B step 3) (arena B step 2) ++
    BlockMetadata.visits F step B.recordLimit (slotDegree S) .shrink (.shrink a chosen) ++
    termPointers step chosen.termBase (.lit chosen.termStride) (SelectedPlan.layout chosen)
      absolute ++
    BlockDataHeads.visits B F i origin (arena B step 1) (arena B step 2) (arena B step 3)

/-- The singleton-child placement scan, using consecutive owner, count and child columns of one
word per site. -/
def refreshPlacement (step : ℕ) (table4 : Expr) : Visit :=
  let n := LevelFields.sites step
  ⟨RefreshPlacement.worker,.lit 0,n,![table4,table4.add n,table4.add ((Expr.lit 2).mul n)]⟩

/-- The complete refresh visit sequence, including successor incidence copies, singleton
placement and the traversal metadata. -/
def refresh : List Visit :=
  let F := geometry B
  let step := S.steps
  let s := RefreshBlockPlan.shape B
  let p := RefreshBlockPlan.input F step (0 : Fin 6)
  let fields := BlockMetadata.Fields.refresh step (arena B step 4)
  BlockHeaderPlan.substep F step (.refresh S.portExponent (S.degreeExponent 0) S.expanderExponent)
    ++
    RefreshBlockPlan.visits B F step (0 : Fin 6) ++ [refreshPlacement step (arena B step 4)] ++
    BlockMetadata.visits F step B.recordLimit (slotDegree S) .refresh fields ++
    termPointers step (PortRefresh.LevelRecipe.termStart s p) (.lit s.stride) (.lit 0) (.lit 0) ++
    [BlockPlanner.publish (LevelFields.address step 40) (LevelFields.atLevel (step+1))]

/-- The initial header and cursor visits followed by publication of the cursor role at level
zero. -/
def initial : List Visit :=
  BlockHeaderPlan.initial (geometry B) (S.degreeExponent 0) ++
    [BlockPlanner.publish (LevelFields.address 0 27) (.lit 0)]

/-- One compression block, consisting of the shrinking steps in schedule order followed by the
refresh. -/
def block : List Visit := (List.finRange S.steps).flatMap (shrink B) ++ refresh B

/-- The fixed script with its initial visits and its repeatable block of shrinking and refresh
visits. -/
def script : BlockPlanner.Script := ⟨S.steps+1,initial B,block B⟩

/-- Finite instruction table for all inputs and all branch selections. -/
def template := Schedule.Online.template (script B).plan

/-- Instantiate the block script as a RAM program at the supplied scheduler ports. -/
def native {w : ℕ} (ports : Schedule.Ports w) := (script B).program ports

theorem initial_length : (script B).initial.length = 4 := rfl

theorem shrink_length (i : Fin S.steps) :
    let a := ShrinkBlockInputs.a i
    let m := ShrinkBundlePlan.thickCount a
    let n := ShrinkBundlePlan.cap a
    (shrink B i).length = 95+m+n+2*(m*n) := by
  simp only [shrink, List.length_append, ShrinkBlockInputs.beforeSlices_length,
    ShrinkResidentsPlan.visits_length,
    BlockSlices.visits_length, ShrinkBlockInputs.slots_length, termPointers_length,
      BlockDataHeads.visits_length]
  change 36+12+(_+_+_+4)+22+3+4+14 = _
  omega

/-- The directory uses the program's actual arity. The capacity calculation
can reserve one complete block per state, and the physical run then takes
exactly the shorter chronological directory. -/
def allocationShape : Shape :=
  { (geometry B) with
    arity := Schedule.arity (script B).catalog
    initialRows := (initial B).length
    levelPasses := (block B).length }

/-- The physical descriptor layout for the given base, position capacity and block count, with
the directory sized to the actual visit count. -/
def layout (base positions blocks : ℕ) : Layout :=
  let L : Layout := ⟨allocationShape B,base,positions,1+(S.steps+1)*blocks⟩
  LevelFields.tightDirectory L ((initial B).length+blocks*(block B).length)

theorem directory_rows (base positions blocks : ℕ) :
    directoryRows (layout B base positions blocks) = (Schedule.Online.calendar
      (script B).plan).total blocks :=
  (LevelFields.tight_rows ..).trans ((script B).calendar_total blocks).symm

theorem allocation_end (base positions blocks : ℕ) :
    endAddress (layout B base positions blocks) ≤
      endAddress ⟨allocationShape B,base,positions,1+(S.steps+1)*blocks⟩ := by
  apply LevelFields.tight_end
  apply LevelFields.calendar_capacity
  · exact le_rfl
  · change blocks ≤ 1+(S.steps+1)*blocks
    exact (Nat.le_mul_of_pos_left blocks (show 0 < S.steps+1 by omega)).trans (Nat.le_add_left ..)
  · simp [passesPerLevel,allocationShape,geometry]

theorem layout_arity (base positions blocks : ℕ) :
    (layout B base positions blocks).shape.arity = Schedule.arity (script B).catalog := rfl

theorem actual_level_count (base positions blocks : ℕ) :
    (layout B base positions blocks).levels = 1+(S.steps+1)*blocks := rfl

theorem table_fields : 54 ≤ (geometry B).scalarFields ∧ 6 = (geometry B).tables := ⟨le_rfl,rfl⟩

end CompressorRecords.BlockProgram

end

end VPVNP
end Computability
end OAI
