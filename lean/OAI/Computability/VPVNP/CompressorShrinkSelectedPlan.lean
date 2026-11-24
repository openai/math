import OAI.Computability.VPVNP.CompressorRecordsBlockPlanner
import OAI.Computability.VPVNP.CompressorRecordsSelectedScoreRun
import OAI.Computability.VPVNP.CompressorRecordsSelectedArenaDemand
import OAI.Computability.VPVNP.CompressorRecordsShrinkPreimages

/-!
# Selected layout, placement, role and child-directory visits

The two scores and chosen layout bit follow the strided term array.
Four placement columns and the absolute arc role rows follow. The
preimage collector appends old sites in their numeric order after clearing
a counter for each new site. The one-shot score stages return cursor one
after writing their result to its designated cell.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SelectedPlan

open BurstRAM BurstRAM.PrivateRAM Compression BlockPlanner PhaseRecipe PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Counts, term-table dimensions and placement operands used to score both shrinking layouts
and build the chosen layout’s placement, arc-role and child tables. -/
structure Inputs where
  /-- Expression for the number of old sites. It sets the length of each placement column and
  the number of calls to the preimage collector. -/
  oldSites : Expr
  /-- Expression for the number of packed sites after shrinking. Each packed site receives a
  child count and one row of old-site indices. -/
  newSites : Expr
  /-- Expression for the number of old arc slots. The role pass visits each slot and reserves
  four words per absolute arc. -/
  oldSlots : Expr
  /-- Expression for the number of motif term records scanned on each of the eight score
  coordinates. -/
  motifs : Expr
  /-- Address expression for the first motif’s selected term record. The score passes read the
  repetition and supply fields relative to this base. -/
  termBase : Expr
  /-- Distance in words between successive motif term records, used to locate each record and
  the score cells following the last one. -/
  termStride : ℕ
  /-- Number of selector bits per repetition. Each score pass adds the repetition count times
  this width to its coordinate’s payload width. -/
  selectorBits : ℕ
  /-- The fourteen operand expressions for the preliminary placement pass. The selected pass
  reuses its dimensions and input columns, supplying the chosen layout bit and fresh output
  addresses. -/
  preliminary : Fin 14 → Expr
  /-- Address expression for the old incidence directory’s actual-out column, used by the role
  pass to find the target of each old arc. -/
  oldActualOut : Expr

variable (I : Inputs)

/-- Start of the two layout-score accumulators, immediately after the strided array of motif
term records. -/
def scoreBase := I.termBase.add (I.motifs.mul (.lit I.termStride))
/-- Address of the chosen-layout bit, two words past the start of the score accumulators. -/
def layoutCell := (scoreBase I).add (.lit 2)
/-- Load the chosen-layout bit from the cell written by the score comparison. -/
def layout := Expr.load (layoutCell I)
/-- Start of the selected placement columns, immediately after the two scores and their
comparison bit. -/
def placementBase := (scoreBase I).add (.lit 3)
/-- Base address of column `c` in the selected placement table. In order, the columns store the
owner, thick-site bit, assigned bundle and bundle target, with one word per old site. -/
def placementColumn (c : Fin 4) := (placementBase I).add ((Expr.lit c.val).mul I.oldSites)
/-- Start of the four-word demand-role records indexed by absolute old arc, following the four
placement columns. -/
def roleBase := (placementBase I).add ((Expr.lit 4).mul I.oldSites)
/-- First address after the old-arc role records and base of the child-count array indexed by
packed site. -/
def roleEnd := (roleBase I).add ((Expr.lit 4).mul I.oldSlots)
/-- Base of the rectangular child table, just past the count word for the last packed site. -/
def childRows := (roleEnd I).add I.newSites
/-- First address after the child table, which reserves one word for every old site across all
packed-site rows. -/
def preimageEnd := (childRows I).add I.oldSites

/-- One-shot visit that zeros both layout-score accumulators before the coordinate scans and
returns cursor one. -/
def clear : Visit := ops TermScores.clearCode 2 (.lit 0) (.lit 1) (fun _ ↦ scoreBase I)

theorem clear_native (L : TermScores.Tables w) (m : Memory w) :
    let P := ((clear I).worker.table.instantiate w (fun _ ↦ L.scoreBase)).program
    execute P 7 (P.start 0) m [] = some ⟨(TermScores.clearReport L).events,some 1⟩ := rfl

/-- Seven operands for score coordinate `j` comprise the term base and stride, score base,
selector width, coordinate index, layout side and relative-mass weight. -/
noncomputable def axisBank (j : Fin 8) : Fin 7 → Expr :=
  let e := SelectedScore.supplyOrder.entries j
  ![I.termBase,.lit I.termStride,scoreBase I,.lit I.selectorBits,.lit j.val,.lit e.1.toNat,
    .lit (MotifAdmission.weight ShrinkMotif.relativeMass e.2)]

/-- Scan all motif term records for coordinate `j`, adding the weighted square of each supply
width to that coordinate’s layout score. -/
noncomputable def axis (j : Fin 8) : Visit :=
  ops TermScores.worker 0 (.lit 0) I.motifs (axisBank I j)

/-- The source comparison leaves one in register two on both outcomes. Its
published bit is still taken from register four. -/
def compareTable : Template 11 5 2 :=
  { TermScores.compareTemplate with code := fun pc ↦ if pc.val = 10 then .returnState 2
      else TermScores.compareTemplate.code pc }

/-- Compare the two scores once and store one in the layout cell exactly when the second score
is smaller. The visit returns cursor one on either outcome. -/
def compare : Visit :=
  ⟨⟨_,_,_,compareTable⟩,.lit 0,.lit 1,![scoreBase I,layoutCell I]⟩

theorem compare_native (L : TermScores.Tables w) (m : Memory w) :
    let M := compareTable.instantiate w ![L.scoreBase,L.levelCell]
    execute M.program 10 (M.program.start 0) m [] = some ⟨(TermScores.compareReport L
      m).events,some 1⟩ := by
  let M := compareTable.instantiate w ![L.scoreBase,L.levelCell]
  let c := (((M.program.start 0).put 1 0 L.scoreBase).put 2 1 (m L.scoreBase.val)).put 3 2 1
  let d := (c.put 4 0 (L.scoreBase+1)).put 5 3 (m (L.scoreBase+1).val)
  let pc := if m (L.scoreBase+1).val < m L.scoreBase.val then (6 : Fin 11) else 7
  change (execute M.program 4 {d with pc := pc} m [] |>.map (Report.prepend .tick)
    |>.map (Report.prepend (.read (L.scoreBase+1) (m (L.scoreBase+1).val)))
    |>.map (Report.prepend .tick) |>.map (Report.prepend .tick)
    |>.map (Report.prepend (.read L.scoreBase (m L.scoreBase.val))) |>.map (Report.prepend .tick))
      = _
  by_cases h : m (L.scoreBase+1).val < m L.scoreBase.val <;>
    simp only [pc,h,↓reduceIte,TermScores.compareReport,TermScores.bit] <;> rfl

/-- Operands for recomputing placement. Slot 5 reads the winning layout bit, slots 10 through
13 point to the selected output columns, and the other slots come from preliminary
placement. -/
def placementBank : Fin 14 → Expr :=
  ![I.preliminary 0,I.preliminary 1,I.preliminary 2,I.preliminary 3,I.preliminary 4,layout I,
    I.preliminary 6,I.preliminary 7,I.preliminary 8,I.preliminary 9,
    placementColumn I 0,placementColumn I 1,placementColumn I 2,placementColumn I 3]

/-- Scan the old sites with the chosen layout and write the owner, thick-site bit, assigned
bundle and bundle target for each site. -/
def placement : Visit := ops ShrinkRAM.visit 0 (.lit 0) I.oldSites (placementBank I)

/-- Operands for the absolute arc-role pass, combining the preliminary dimensions, old
actual-out column, selected placement columns and role-table destination. -/
def rolesBank : Fin 11 → Expr :=
  ![I.preliminary 2,I.preliminary 0,I.preliminary 1,I.preliminary 3,.lit 0,I.oldActualOut,
    placementColumn I 1,placementColumn I 0,placementColumn I 2,placementColumn I 3,roleBase I]

/-- Visit every old arc slot and write its four-word demand-role record at the absolute arc
index using the selected placement. -/
def roles : Visit := ops DemandRAM.visit 0 (.lit 0) I.oldSlots (rolesBank I)

/-- Zero the child counter for each packed site before the preimage collector begins appending
old sites. -/
def clearChildren : Visit := ops SliceRAM.clearOps 0 (.lit 0) I.newSites (fun _ ↦ roleEnd I)

/-- Six operands for collecting preimages comprise the old-site count, selected owner column,
packed-site count, child-count base, row capacity at exponent `a`, and child-row base. -/
def childBank (a : ℕ) : Fin 6 → Expr :=
  ![I.oldSites,placementColumn I 0,I.newSites,roleEnd I,.lit
    (ShrinkPreimages.capacity a),childRows I]

/-- Visit old sites in increasing index order, appending each index to its selected owner’s
child row and incrementing that owner’s count. -/
def children (a : ℕ) : Visit := ops collectPreimage 3 (.lit 0) I.oldSites (childBank I a)

/-- The fourteen visits that clear the scores, scan eight supply coordinates, choose the
layout, write placement and arc roles, then clear the child counts and collect preimages. -/
noncomputable def visits (a : ℕ) : List Visit :=
  [clear I] ++ List.ofFn (axis I) ++ [compare I,placement I,roles I,clearChildren I,children I a]

theorem visits_length (a : ℕ) : (visits I a).length = 14 := by simp [visits]

section Values

variable {a g : ℕ} (X : State a (packingLaneBits a g)) (p₀ : Fin 14 → Word w)
  (T : IncidenceDirectory w) (term : Word w) (pub : Fin 5 → Word w) (state : Word w) (m : Memory w)

local notation "ev" => Expr.eval pub state m

/-- Relates the evaluated input expressions to a shrinking state’s site, arc and motif counts,
term base, actual-out column and preliminary operands, and requires the term stride to fit
in a word. -/
structure Reads : Prop where
  sites : ev I.oldSites = ((ShrinkPreimages.oldCount X : ℕ) : Word w)
  nextSites : ev I.newSites = ((ShrinkPreimages.newCount X : ℕ) : Word w)
  slots : ev I.oldSlots = ((DemandRAM.oldCount X : ℕ) : Word w)
  motifs : ev I.motifs = ((SelectedArena.motifs X : ℕ) : Word w)
  term : ev I.termBase = term
  strideFit : I.termStride < 2^w
  oldOut : ev I.oldActualOut = T.actualOut
  prior : ∀ i, ev (I.preliminary i) = p₀ i

variable (read : Reads I X p₀ T term pub state m)

local notation "L" => SelectedArena.scoreTables X term (I.termStride : Word w)
    (I.selectorBits : Word w)

private theorem ev_add (u v : Expr) : ev (u.add v) = ev u + ev v := rfl
private theorem ev_mul (u v : Expr) : ev (u.mul v) = ev u * ev v := rfl
private theorem ev_lit (u : ℕ) : ev (.lit u) = (u : Word w) := rfl

include read in
theorem score_head : ev (scoreBase I) = (SelectedArena.origin X term (I.termStride : Word w)
    : Word w) := by
  have ht : (term.val : Word w) = term := Fin.ext (Nat.mod_eq_of_lt term.isLt)
  simp [scoreBase, ev_add, ev_mul, ev_lit, read.term, read.motifs, SelectedArena.origin, ht,
    Nat.mod_eq_of_lt read.strideFit]

include read in
theorem axis_bank (j : Fin 8) :
    (fun i ↦ ev (axisBank I j i)) = TermScores.params L (SelectedScore.axes j) := by
  funext i
  fin_cases i <;> first | exact read.term | exact score_head I X p₀ T term pub state m read | rfl

include read in
theorem placement_column (c : Fin 4) :
    ev (placementColumn I c) = SelectedArena.placementWord X term (I.termStride : Word w) c := by
  simp only [placementColumn,placementBase,ev_add,ev_mul,ev_lit,score_head I X p₀ T term pub state
    m read,read.sites]
  change _ = ((SelectedArena.origin X term
    (I.termStride : Word w)+3+c.val*ShrinkPreimages.oldCount X : ℕ) : Word w)
  push_cast
  rfl

include read in
theorem roles_head : ev (roleBase I) = (SelectedArena.roleBase X term (I.termStride : Word w)
    : Word w) := by
  simp only [roleBase,placementBase,ev_add,ev_mul,ev_lit,score_head I X p₀ T term pub state m
    read,read.sites]
  simp [SelectedArena.roleBase, SelectedArena.placementBase, SelectedArena.positions,
    ShrinkPreimages.oldCount]

include read in
theorem placement_bank (fit : SelectedArena.Fits X term (I.termStride : Word w)) :
    (fun i ↦ ev (placementBank I i)) = SelectedArena.selectedWords X term (I.termStride : Word w)
      p₀ m := by
  have head := score_head I X p₀ T term pub state m read
  have col := placement_column I X p₀ T term pub state m read
  have loc : SelectedArena.origin X term (I.termStride : Word w)+2 < 2^w := by
    change _ + 3 + 4 * _ + 4 * _ < 2^w at fit; omega
  have bit : ev (layout I) = m (SelectedArena.origin X term (I.termStride : Word w)+2) := by
    change m (ev (scoreBase I)+2).val = _
    rw [head,← (Nat.cast_ofNat (R := Word w) (n :=
      2)),← Nat.cast_add,Fin.val_natCast,Nat.mod_eq_of_lt loc]
  funext i
  fin_cases i <;> first | exact read.prior _ | exact bit | exact col _

include read in
theorem roles_bank :
    (fun i ↦ ev (rolesBank I i)) = SelectedArena.demandWords X term (I.termStride : Word w)
      p₀ T := by
  have col := placement_column I X p₀ T term pub state m read
  funext i
  fin_cases i <;> first | exact read.prior _ | exact read.oldOut | exact col _ |
    exact roles_head I X p₀ T term pub state m read | rfl

include read in
theorem child_bank (selected : Fin 14 → Word w)
    (owner : selected 10 = SelectedArena.placementWord X term (I.termStride : Word w) 0) :
    (fun i ↦ ev (childBank I a i)) = ShrinkPreimages.params X selected (ev (roleEnd I)) (ev
      (childRows I)) := by
  funext i
  fin_cases i <;> first | exact read.sites | exact read.nextSites |
    exact (placement_column I X p₀ T term pub state m read 0).trans owner.symm | rfl

end Values
end CompressorRecords.SelectedPlan

end VPVNP
end Computability
end OAI
