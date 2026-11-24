import OAI.Computability.VPVNP.CompressorSlotLevel
import OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
import Mathlib.Data.List.OfFn

/-!
# Native row planners for the five shrinking slot passes

The template fixes the degree, consumed colors, tag count and subdivisions
for this substep. The planner reads the current base and residual lane counts,
the heads of the selected input tables, and the start of scratch space. It
computes each pass's exclusive stop and every address in its public bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotLevel.Recipe

open BurstRAM BurstRAM.PrivateRAM PhaseRecipe
open scoped Fin.CommRing
open Compression Compression.PackingData Compression.SurvivingSlots Slots SlotOwners

/-- Constants in a shrinking substep's fixed finite instruction template. -/
structure Template where
  /-- Fixed number of tags per base vertex used by this shrinking substep's planner. -/
  tags : ℕ
  /-- Input slot degree compiled into the planner's old arc counts. -/
  oldDegree : ℕ
  /-- Fixed number of old color-mask bits used to size the genuine candidate range. -/
  colors : ℕ
  /-- Fixed subdivision count for each role edge type, used to size the candidate range and
  determine padding. -/
  subdivisions : Fin 4 → ℕ
  /-- Padded output degree compiled into the slot rows and base-matching phase. -/
  newDegree : ℕ

/-- Combine the template constants with the current base and lane counts to obtain the slot
level shape. -/
def Template.shape (T : Template) (bases lanes : ℕ) : Shape :=
  ⟨bases, T.tags, lanes, T.oldDegree, T.colors, T.subdivisions, T.newDegree⟩

/-- Current level counts and physical heads. The role table contains the
eight entries materialized for the chosen layout. -/
structure Inputs where
  /-- Planner expression yielding the current number of base vertices. -/
  bases : Expr
  /-- Planner expression yielding the number of residual lanes per packed base. -/
  lanes : Expr
  /-- Planner expression locating the selected old arc records with their role sites and CD
  flags. -/
  oldArc : Expr
  /-- Planner expression locating the chosen layout's eight endpoint role selectors. -/
  role : Expr
  /-- Planner expression locating the published subdivision counts for the four edge types. -/
  subdivisions : Expr
  /-- Planner expression locating the cyclic site successor table used by dummy slots. -/
  nextSite : Expr
  /-- Planner expression yielding the first fresh address for the slot directory. -/
  scratch : Expr

variable {w : ℕ}

/-- The current expressions read the two shape scalars and the five array heads. -/
structure Reads (I : Inputs) (pub : Fin 5 → Word w) (state : Word w) (m : Memory w)
    (bases lanes : ℕ) (h : Heads) : Prop where
  bases_eq : I.bases.eval pub state m = (bases : Word w)
  lanes_eq : I.lanes.eval pub state m = (lanes : Word w)
  oldArc_eq : I.oldArc.eval pub state m = (h.oldArc : Word w)
  role_eq : I.role.eval pub state m = (h.role : Word w)
  subdivisions_eq : I.subdivisions.eval pub state m = (h.subdivisions : Word w)
  nextSite_eq : I.nextSite.eval pub state m = (h.nextSite : Word w)
  scratch_eq : I.scratch.eval pub state m = (h.scratch : Word w)

/-- Derived counts and array addresses used by the native passes. -/
structure Counts (α : Type) where
  /-- Total number of packed sites including all residual lanes. -/
  sites : α
  /-- Number of dummy outgoing slots needed at each packed site to reach the target degree. -/
  pad : α
  /-- Number of old arc identifiers before adding the residual lane digit. -/
  oldBaseArcs : α
  /-- Size of the genuine candidate arc range across edge types, subdivisions, and residual
  lanes, including holes. -/
  genuineArcs : α
  /-- Number of source and target fields in the genuine candidate range. -/
  genuine : α
  /-- Number of source and target fields in the dummy arc range. -/
  dummy : α
  /-- Total number of field addresses covered by the owner and append scans. -/
  fields : α
  /-- Count of real site-and-side owners before allocating private rows for holes. -/
  owners : α
  /-- Number of packed base ports for which the matching scan computes a target and
  displacement. -/
  baseArcs : α
  /-- Starting address of the rectangular field rows following the append counters. -/
  rows : α
  /-- Starting address of the inverse table that maps each real endpoint field to its
  rectangular slot. -/
  inverse : α
  /-- Starting address of the matching target column indexed by packed base port. -/
  targets : α
  /-- Starting address of the lane displacement column indexed by packed base port. -/
  shifts : α
  /-- First address after the slot directory's base displacement column. -/
  stopAddress : α

/-- Compile only the level-dependent arithmetic. Subtraction, division and
exponentiation inside template constants take place when building the fixed program. -/
def counts (T : Template) (I : Inputs) : Counts Expr :=
  let sites := I.bases.mul ((.lit T.tags : Expr).mul I.lanes)
  let oldBaseArcs := I.bases.mul (.lit (T.tags * (T.oldDegree * (2 ^ T.colors * T.oldDegree))))
  let pad := Expr.lit (T.newDegree - survivingDegree T.oldDegree T.colors T.subdivisions)
  let keys := (.lit 4 : Expr).mul (oldBaseArcs.mul (.lit (∑ t, T.subdivisions t)))
  let genuineArcs := keys.mul I.lanes
  let dummyArcs := sites.mul pad
  let fields := (genuineArcs.add dummyArcs).mul (.lit 2)
  let owners := sites.mul (.lit 2)
  let baseArcs := (I.bases.mul (.lit T.tags)).mul (.lit T.newDegree)
  let rows := (I.scratch.add fields).add (owners.add fields)
  let inverse := rows.add ((owners.add fields).mul (.lit T.newDegree))
  let targets := inverse.add fields
  let shifts := targets.add baseArcs
  ⟨sites,pad,oldBaseArcs,genuineArcs,genuineArcs.mul (.lit 2),dummyArcs.mul (.lit 2),
    fields,owners,baseArcs,rows,inverse,targets,shifts,shifts.add baseArcs⟩

/-- Apply the same conversion to every derived count and address, as when evaluating planner
expressions or encoding natural values as words. -/
def Counts.map {α β : Type} (f : α → β) (c : Counts α) : Counts β :=
  ⟨f c.sites, f c.pad, f c.oldBaseArcs, f c.genuineArcs, f c.genuine, f c.dummy, f c.fields,
    f c.owners, f c.baseArcs, f c.rows, f c.inverse, f c.targets, f c.shifts, f c.stopAddress⟩

/-- Calculate the natural-number slot counts and physical table addresses from the level shape
and input heads. -/
def countValues (s : Shape) (h : Heads) : Counts ℕ :=
  ⟨sites s, pad s, oldBaseArcCount s.bases s.tags s.oldDegree s.colors,
    keyCount s.bases s.tags s.oldDegree s.colors s.subdivisions * s.lanes,
    genuineCount s, dummyCount s, fields s, owners s, baseArcs s, rowsHead s h,
    inverseHead s h, targetsHead s h, shiftsHead s h, stopAddress s h⟩

theorem eval_counts (T : Template) (I : Inputs) {pub : Fin 5 → Word w} {state : Word w} {m : Memory w}
    {bases lanes : ℕ} {h : Heads} (read : Reads I pub state m bases lanes h) :
    (counts T I).map (fun e ↦ e.eval pub state m) =
      (countValues (T.shape bases lanes) h).map (fun n : ℕ ↦ (n : Word w)) := by
  simp only [counts, Counts.map, countValues, Expr.mul, Expr.add, Expr.eval, BinaryOp.eval,
    read.bases_eq, read.lanes_eq, read.scratch_eq, ← Nat.cast_mul, ← Nat.cast_add]
  rfl

/-- Planner expression for the selected slot worker's exclusive cursor bound. -/
def stop (T : Template) (I : Inputs) : SlotLevel.Phase → Expr
  | .genuineOwners => (counts T I).genuine
  | .dummyOwners => (counts T I).dummy
  | .appendFields => (counts T I).fields
  | .invertFields => (counts T I).owners.mul (.lit T.newDegree)
  | .baseMatching => (counts T I).baseArcs

/-- Public parameter expressions for the selected worker, in the order of its native parameter
bank. -/
def params (T : Template) (I : Inputs) : (p : SlotLevel.Phase) → Fin (arity p) → Expr
  | .genuineOwners => ![I.lanes, .lit (∑ t, T.subdivisions t), (counts T I).oldBaseArcs,
      I.oldArc, I.role, I.subdivisions, (counts T I).owners, I.scratch]
  | .dummyOwners => ![(counts T I).pad, I.nextSite, I.scratch.add (counts T I).genuine]
  | .appendFields =>
    let c := counts T I
    ![c.fields, I.scratch, c.owners.add c.fields, I.scratch.add c.fields, .lit T.newDegree, c.rows]
  | .invertFields => ![(counts T I).rows, (counts T I).inverse]
  | .baseMatching =>
    let c := counts T I
    ![.lit T.newDegree, I.lanes, c.rows, c.inverse, c.targets, c.shifts]

/-- Form the selected worker's descriptor recipe from its tag, zero starting cursor, stop
expression, and public parameters. -/
def phase (tag : SlotLevel.Phase → ℕ) (T : Template) (I : Inputs) (p : SlotLevel.Phase) :
    PhaseRecipe.Phase (arity p) := ⟨tag p, .lit 0, stop T I p, params T I p⟩

variable (tag : SlotLevel.Phase → ℕ) (T : Template) (I : Inputs) (p : SlotLevel.Phase)
variable {pub : Fin 5 → Word w} {state : Word w} {m : Memory w} {bases lanes : ℕ} {h : Heads}
variable (read : Reads I pub state m bases lanes h)

include read

theorem eval_stop :
    (stop T I p).eval pub state m = Fin.ofNat (2^w) (limit (T.shape bases lanes) p) := by
  have hc := eval_counts T I read
  cases p
  case genuineOwners => exact congrArg Counts.genuine hc
  case dummyOwners => exact congrArg Counts.dummy hc
  case appendFields => exact congrArg Counts.fields hc
  case invertFields =>
    change ((counts T I).owners.eval pub state m) * (T.newDegree : Word w) = _
    rw [show (counts T I).owners.eval pub state m = (owners (T.shape bases lanes) : Word w) from
      congrArg Counts.owners hc, ← Nat.cast_mul]
    rfl
  case baseMatching => exact congrArg Counts.baseArcs hc

theorem eval_params (i : Fin (arity p)) :
    (params T I p i).eval pub state m = bank (T.shape bases lanes) h w p i := by
  let s := T.shape bases lanes
  have hc := eval_counts T I read
  have c (f : Counts (Word w) → Word w) := congrArg f hc
  have old : (counts T I).oldBaseArcs.eval pub state m = (oldBaseArcCount s.bases s.tags s.oldDegree s.colors : Word w) := c Counts.oldBaseArcs
  have own : (counts T I).owners.eval pub state m = (owners s : Word w) := c Counts.owners
  have pad' : (counts T I).pad.eval pub state m = (pad s : Word w) := c Counts.pad
  have genuine : (counts T I).genuine.eval pub state m = (genuineCount s : Word w) := c Counts.genuine
  have fields' : (counts T I).fields.eval pub state m = (fields s : Word w) := c Counts.fields
  have rows : (counts T I).rows.eval pub state m = (rowsHead s h : Word w) := c Counts.rows
  have inv : (counts T I).inverse.eval pub state m = (inverseHead s h : Word w) := c Counts.inverse
  have targets : (counts T I).targets.eval pub state m = (targetsHead s h : Word w) := c Counts.targets
  have shifts : (counts T I).shifts.eval pub state m = (shiftsHead s h : Word w) := c Counts.shifts
  have plus {a b : Expr} {x y : ℕ} (hx : a.eval pub state m = (x : Word w))
      (hy : b.eval pub state m = (y : Word w)) : (a.add b).eval pub state m = ((x+y : ℕ) : Word w) := by
    change a.eval pub state m + b.eval pub state m = _
    rw [hx, hy, Nat.cast_add]
  cases p with
  | genuineOwners =>
    fin_cases i
    exacts [read.lanes_eq, rfl, old, read.oldArc_eq, read.role_eq, read.subdivisions_eq, own, read.scratch_eq]
  | dummyOwners =>
    fin_cases i
    exacts [pad', read.nextSite_eq, plus read.scratch_eq genuine]
  | appendFields =>
    fin_cases i
    exacts [fields', read.scratch_eq, plus own fields', plus read.scratch_eq fields', rfl, rows]
  | invertFields =>
    fin_cases i
    exacts [rows, inv]
  | baseMatching =>
    fin_cases i
    exacts [rfl, read.lanes_eq, rows, inv, targets, shifts]

/-- Exact words of the compiled planner at the worker's own arity. -/
theorem recipe_words :
    (phase tag T I p).recipe.words pub state m =
      frame (T.shape bases lanes) h (fun q ↦ (tag q : Word w)) p := by
  rw [PhaseRecipe.recipe_words]
  change _ :: _ :: (stop T I p).eval pub state m :: List.ofFn (fun i ↦ (params T I p i).eval pub state m) =
    _ :: _ :: _ :: List.ofFn _
  rw [eval_stop T I p read, show (fun i ↦ (params T I p i).eval pub state m) =
    bank (T.shape bases lanes) h w p from funext (eval_params T I p read)]
  rfl

/-- The cursor stop also equals the natural count when that count fits in one word. -/
theorem stop_val (fit : limit (T.shape bases lanes) p < 2^w) :
    ((phase tag T I p).stop.eval pub state m).val = limit (T.shape bases lanes) p := by
  change ((stop T I p).eval pub state m).val = _
  rw [eval_stop T I p read]
  exact Nat.mod_eq_of_lt fit

/-- Extend a slot phase recipe to the scheduler's common arity by appending zero parameter
words. -/
def padded (g : ℕ) (room : arity p ≤ g) : PhaseRecipe.Phase g :=
  PhaseRecipe.Phase.ofParams room (tag p) (.lit 0) (stop T I p) (params T I p)

omit read in
private theorem ofFn_padded {α : Type} {k g : ℕ} (f : Fin k → α) (z : α) (room : k ≤ g) :
    List.ofFn (fun i : Fin g ↦ if h : i.val < k then f ⟨i.val,h⟩ else z) =
      List.ofFn f ++ List.replicate (g-k) z := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le room
  rw [Nat.add_sub_cancel_left, ← List.ofFn_const l z, ← List.ofFn_fin_append]
  congr 1
  funext i
  cases i using Fin.addCases with
  | left j => simp [j.isLt]
  | right j => simp

omit read in
/-- Padding a native phase only appends zero words to its parameter row. -/
theorem pad_phase_words {k g : ℕ} (room : k ≤ g) (P : PhaseRecipe.Phase k)
    (pub : Fin 5 → Word w) (state : Word w) (m : Memory w) :
    (PhaseRecipe.Phase.ofParams room P.tag P.initial P.stop P.params).recipe.words pub state m =
      P.recipe.words pub state m ++ List.replicate (g-k) 0 := by
  simp only [PhaseRecipe.recipe_words, PhaseRecipe.Phase.ofParams, PhaseRecipe.Phase.words, List.cons_append]
  congr 3
  rw [← ofFn_padded (fun i ↦ (P.params i).eval pub state m) (0 : Word w) room]
  congr 1
  funext i
  by_cases hi : i.val < k <;> simp [hi, Expr.eval]

/-- The enclosing catalog can use any larger row width. Extra words after the
worker's public bank are zero and have no effect on its operands. -/
theorem padded_words (g : ℕ) (room : arity p ≤ g) :
    (padded tag T I p g room).recipe.words pub state m =
      frame (T.shape bases lanes) h (fun q ↦ (tag q : Word w)) p ++
      List.replicate (g-arity p) 0 := by
  rw [← recipe_words tag T I p read]
  exact pad_phase_words room (phase tag T I p) pub state m

/-- Launch the finite planner and install the computed row in the live
directory. Its reads, writes and private execution use the native compiler. -/
theorem execute_padded (g : ℕ) (room : arity p ≤ g) (cap : ℕ)
    (budget : (padded tag T I p g room).recipe.code.length < cap)
    (fit : (Controller.rowBase g pub m).val + (g+3) ≤ 2^w) :
    let R := (padded tag T I p g room).recipe
    let M := R.acceptTable.instantiate w pub
    let es := (R.report pub state m).events
    execute M.program cap (M.program.start state) m [] = some ⟨es,none⟩ ∧
      Greedy.Stores (after m es) (Controller.rowBase g pub m)
        (frame (T.shape bases lanes) h (fun q ↦ (tag q : Word w)) p ++ List.replicate (g-arity p) 0) ∧
      (∀ a, a < (Controller.rowBase g pub m).val ∨ (Controller.rowBase g pub m).val + (g+3) ≤ a →
        after m es a = m a) ∧ countProbes es = R.reads+(g+3) ∧ choiceBits es = [] := by
  have he := execute_phase (padded tag T I p g room) pub state m cap budget fit
  rw [← PhaseRecipe.recipe_words, padded_words tag T I p read g room] at he
  exact he

end CompressorRecords.SlotLevel.Recipe

end VPVNP
end Computability
end OAI
