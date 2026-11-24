import OAI.Computability.VPVNP.CompressorSlotLevelRecipe
import OAI.Computability.VPVNP.CompressorSlotOutputLayout

/-!
# Planning the shrinking output columns

The base inverse, two actual incidence permutations, and width column are
allocated immediately after the sorted slot directory. Their native planner
rows are computed from the selected level's counts and heads. Only the width
worker also reads the head of the already materialized split-width input.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlots.Recipe

open SlotLevel.Recipe PhaseRecipe BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

/-- The four output passes following base matching, inverting base mates, expanding actual
mates in each direction, and collecting outgoing widths. -/
inductive Phase where
  | baseInverse | actualOut | actualIn | widths
  deriving DecidableEq

/-- Number of public words required by each output worker, two for base inversion, five for
actual incidence, and eight for widths. -/
abbrev arity : Phase → ℕ
  | .baseInverse => 2
  | .actualOut | .actualIn => 5
  | .widths => 8

/-- Exclusive output scan bound, counting base ports for the inverse scan and actual ports for
the other three passes. -/
def limit (s : SlotLevel.Shape) : Phase → ℕ
  | .baseInverse => SlotLevel.baseArcs s
  | .actualOut | .actualIn | .widths => actualCount s

/-- Select the native parameter bank for the requested output phase, including the split-width
input head for the width scan. -/
def bank (s : SlotLevel.Shape) (h : SlotLevel.Heads) (split w : ℕ) : (p : Phase) → Fin (arity p) → Word w
  | .baseInverse => inverseBank s h w
  | .actualOut => actualBank s h false w
  | .actualIn => actualBank s h true w
  | .widths => widthBank s h split w

/-- Controller row containing the output worker tag, zero starting cursor, exclusive stop, and
public parameters. -/
def frame {w : ℕ} (s : SlotLevel.Shape) (h : SlotLevel.Heads) (split : ℕ)
    (tag : Phase → Word w) (p : Phase) : List (Word w) :=
  tag p :: 0 :: Fin.ofNat _ (limit s p) :: List.ofFn (bank s h split w p)

/-- Native expressions for the additional addresses and the shared lane-slot count. -/
structure Columns where
  /-- Planner expression for the number of actual outgoing ports, the common length of the two
  mate columns and the width column. -/
  count : Expr
  /-- Planner expression for the start of the inverse base-matching column following the base
  displacement column. -/
  baseInverse : Expr
  /-- Planner expression for the start of the actual forward mate column. -/
  actualOut : Expr
  /-- Planner expression for the start of the actual inverse mate column. -/
  actualIn : Expr
  /-- Planner expression for the start of the actual outgoing-width column. -/
  width : Expr
  /-- Planner expression for the first free address after the last output column. -/
  finish : Expr

/-- Derive the output count and column boundaries from the current slot level's computed
dimensions and stop address. -/
def columns (T : SlotLevel.Recipe.Template) (I : Inputs) : Columns :=
  let c := counts T I
  let count := c.sites.mul (.lit T.newDegree)
  let out := c.stopAddress.add c.baseArcs
  let incoming := out.add count
  let width := incoming.add count
  ⟨count,c.stopAddress,out,incoming,width,width.add count⟩

variable {w : ℕ} (T : SlotLevel.Recipe.Template) (I : Inputs) (split : Expr)
variable {pub : Fin 5 → Word w} {state : Word w} {m : Memory w} {bases lanes : ℕ} {h : SlotLevel.Heads}
variable (read : Reads I pub state m bases lanes h)

/-- Evaluating the planner expressions yields the word encodings of the actual port count, the
four output heads, and the final address. -/
structure ColumnValues (c : Columns) (pub : Fin 5 → Word w) (state : Word w) (m : Memory w)
    (s : SlotLevel.Shape) (h : SlotLevel.Heads) : Prop where
  count : c.count.eval pub state m = (actualCount s : Word w)
  baseInverse : c.baseInverse.eval pub state m = (inverseBaseHead s h : Word w)
  actualOut : c.actualOut.eval pub state m = (outHead s h : Word w)
  actualIn : c.actualIn.eval pub state m = (inHead s h : Word w)
  width : c.width.eval pub state m = (widthHead s h : Word w)
  finish : c.finish.eval pub state m = (ShrinkSlots.finish s h : Word w)

include read in
theorem eval_columns : ColumnValues (columns T I) pub state m (T.shape bases lanes) h := by
  let s := T.shape bases lanes
  let c := counts T I
  have hc := eval_counts T I read
  have sites : c.sites.eval pub state m = (SlotLevel.sites s : Word w) := congrArg Counts.sites hc
  have stop : c.stopAddress.eval pub state m = (inverseBaseHead s h : Word w) := congrArg Counts.stopAddress hc
  have arcs : c.baseArcs.eval pub state m = (SlotLevel.baseArcs s : Word w) := congrArg Counts.baseArcs hc
  have size : (columns T I).count.eval pub state m = (actualCount s : Word w) := by
    change c.sites.eval pub state m * (T.newDegree : Word w) = _
    rw [sites, ← Nat.cast_mul]
    rfl
  have plus {a b : Expr} {x y : ℕ} (hx : a.eval pub state m = (x : Word w))
      (hy : b.eval pub state m = (y : Word w)) : (a.add b).eval pub state m = ((x+y : ℕ) : Word w) := by
    change a.eval pub state m + b.eval pub state m = _
    rw [hx,hy,Nat.cast_add]
  have out : (columns T I).actualOut.eval pub state m = (outHead s h : Word w) := plus stop arcs
  have incoming : (columns T I).actualIn.eval pub state m = (inHead s h : Word w) := plus out size
  have width : (columns T I).width.eval pub state m = (widthHead s h : Word w) := plus incoming size
  exact ⟨size,stop,out,incoming,width,plus width size⟩

/-- All six heads in the order used by the next level's incidence header. -/
def columnHeads : Fin 6 → Expr :=
  let c := counts T I
  let col := columns T I
  ![c.targets, col.baseInverse, c.shifts, col.actualOut, col.actualIn, col.width]

include read in
theorem eval_columnHeads (j : Fin 6) :
    (columnHeads T I j).eval pub state m = (directory (T.shape bases lanes) h w).column j := by
  have hc := eval_counts T I read
  have hs := eval_columns T I read
  fin_cases j
  exacts [congrArg Counts.targets hc, hs.baseInverse, congrArg Counts.shifts hc, hs.actualOut, hs.actualIn, hs.width]

/-- Construct the cursor-stop expression for a base inverse, actual mate, or width scan. -/
def stop : Phase → Expr
  | .baseInverse => (counts T I).baseArcs
  | .actualOut | .actualIn | .widths => (columns T I).count

private def actualParams (reverse : Bool) : Fin 5 → Expr :=
  let c := counts T I
  let col := columns T I
  ![.lit T.newDegree, I.lanes, if reverse then col.baseInverse else c.targets, c.shifts,
    if reverse then col.actualIn else col.actualOut]

/-- Construct the ordered parameter expressions for one output worker from the level inputs
and, for widths, the split table head. -/
def params : (p : Phase) → Fin (arity p) → Expr
  | .baseInverse => ![(counts T I).targets, (columns T I).baseInverse]
  | .actualOut => actualParams T I false
  | .actualIn => actualParams T I true
  | .widths =>
    let c := counts T I
    ![.lit T.newDegree, I.lanes, .lit (∑ t, T.subdivisions t), c.oldBaseArcs, c.genuineArcs,
      c.rows, split, (columns T I).width]

/-- Assemble one output worker recipe from its dispatch tag, zero starting cursor, computed
stop, and parameter expressions. -/
def phase (tag : Phase → ℕ) (p : Phase) : PhaseRecipe.Phase (arity p) :=
  ⟨tag p, .lit 0, stop T I p, params T I split p⟩

variable (tag : Phase → ℕ) (p : Phase)
variable {splitHead : ℕ} (hsplit : split.eval pub state m = (splitHead : Word w))

include read in
theorem eval_stop :
    (stop T I p).eval pub state m = Fin.ofNat (2^w) (limit (T.shape bases lanes) p) := by
  cases p
  case baseInverse => exact congrArg Counts.baseArcs (eval_counts T I read)
  all_goals exact (eval_columns T I read).count

include read hsplit in
theorem eval_params (i : Fin (arity p)) :
    (params T I split p i).eval pub state m = bank (T.shape bases lanes) h splitHead w p i := by
  have hc := eval_counts T I read
  have hs := eval_columns T I read
  cases p with
  | baseInverse =>
    fin_cases i
    exacts [congrArg Counts.targets hc, hs.baseInverse]
  | actualOut =>
    fin_cases i
    exacts [rfl,read.lanes_eq,congrArg Counts.targets hc,congrArg Counts.shifts hc,hs.actualOut]
  | actualIn =>
    fin_cases i
    exacts [rfl,read.lanes_eq,hs.baseInverse,congrArg Counts.shifts hc,hs.actualIn]
  | widths =>
    fin_cases i
    exacts [rfl,read.lanes_eq,rfl,congrArg Counts.oldBaseArcs hc,congrArg Counts.genuineArcs hc,
      congrArg Counts.rows hc,hsplit,hs.width]

include read hsplit in
theorem recipe_words :
    (phase T I split tag p).recipe.words pub state m =
      frame (T.shape bases lanes) h splitHead (fun q ↦ (tag q : Word w)) p := by
  rw [PhaseRecipe.recipe_words]
  change _ :: _ :: (stop T I p).eval pub state m :: List.ofFn (fun i ↦ (params T I split p i).eval pub state m) =
    _ :: _ :: _ :: List.ofFn _
  rw [eval_stop T I read p, show (fun i ↦ (params T I split p i).eval pub state m) =
    bank (T.shape bases lanes) h splitHead w p from funext (eval_params T I split read p hsplit)]
  rfl

/-- Extend the output worker's recipe to the scheduler's common parameter count with trailing
zero operands. -/
def padded (g : ℕ) (room : arity p ≤ g) : PhaseRecipe.Phase g :=
  PhaseRecipe.Phase.ofParams room (tag p) (.lit 0) (stop T I p) (params T I split p)

include read hsplit in
theorem padded_words (g : ℕ) (room : arity p ≤ g) :
    (padded T I split tag p g room).recipe.words pub state m =
      frame (T.shape bases lanes) h splitHead (fun q ↦ (tag q : Word w)) p ++ List.replicate (g-arity p) 0 := by
  rw [← recipe_words T I split read tag p hsplit]
  exact pad_phase_words room (phase T I split tag p) pub state m

include read hsplit in
theorem execute_padded (g : ℕ) (room : arity p ≤ g) (cap : ℕ)
    (budget : (padded T I split tag p g room).recipe.code.length < cap)
    (fit : (Controller.rowBase g pub m).val + (g+3) ≤ 2^w) :
    let R := (padded T I split tag p g room).recipe
    let M := R.acceptTable.instantiate w pub
    let es := (R.report pub state m).events
    execute M.program cap (M.program.start state) m [] = some ⟨es,none⟩ ∧
      Greedy.Stores (after m es) (Controller.rowBase g pub m)
        (frame (T.shape bases lanes) h splitHead (fun q ↦ (tag q : Word w)) p ++ List.replicate (g-arity p) 0) ∧
      (∀ a, a < (Controller.rowBase g pub m).val ∨ (Controller.rowBase g pub m).val + (g+3) ≤ a →
        after m es a = m a) ∧ countProbes es = R.reads+(g+3) ∧ choiceBits es = [] := by
  have he := execute_phase (padded T I split tag p g room) pub state m cap budget fit
  rw [← PhaseRecipe.recipe_words, padded_words T I split read tag p hsplit g room] at he
  exact he

end CompressorRecords.ShrinkSlots.Recipe

end VPVNP
end Computability
end OAI
