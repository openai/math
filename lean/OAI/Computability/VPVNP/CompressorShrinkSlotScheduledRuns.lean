import OAI.Computability.VPVNP.CompressorSlotBuild
import OAI.Computability.VPVNP.CompressorShrinkSlotPlan
import OAI.Computability.VPVNP.CompressorSourceWalk
import OAI.Computability.VPVNP.CompressorRecordsCopyIncidence

/-!
# Source runs of the shrinking slot program

The slot builder's reports follow the same sequence of workers as the
descriptor planner. The first sixteen phases prepare and fill the physical
directory. The last six copy it into the next level's canonical arrays.
Each worker starts at zero in the actual memory left by the preceding phase.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlotPlan.Scheduled

open BurstRAM PhaseRecipe BlockPlanner ShrinkSlots SlotLevel
open scoped Fin.CommRing

/-- The operands compiled into this occurrence of the slot plan. -/
structure Plan where
  /-- Fixed slot geometry and role subdivision counts for this scheduled shrinking step. -/
  template : ShrinkSlotPlan.Template
  /-- Expressions locating the dynamic dimensions and working tables of the slot builder. -/
  input : Inputs
  /-- Expression reading the layout side selected by the shrink score. -/
  layout : Expr
  /-- Expression locating the surviving-width table used to fill the output slot widths. -/
  split : Expr
  /-- Descriptor shape used to locate the next level's canonical incidence pointers. -/
  space : DescriptorSpace.Shape
  /-- Substep number used to locate the level receiving the six completed columns. -/
  step : ℕ

/-- A scheduled slot-builder stage for publishing subdivision data, preparing lookups, building
the directory or copying one incidence column. -/
inductive Stage where
  | subdivision (i : Fin 4)
  | roles | cyclic | clear
  | core (p : SlotLevel.Phase)
  | output (p : ShrinkSlots.Recipe.Phase)
  | copy (c : Fin 6)
  deriving DecidableEq

/-- Compile a slot-builder stage into the corresponding planned worker visit and operands. -/
def Stage.visit (P : Plan) : Stage → Visit
  | .subdivision i => ShrinkSlotPlan.subdivision P.template P.input i
  | .roles => ShrinkSlotPlan.roles P.input P.layout
  | .cyclic => ShrinkSlotPlan.cyclic P.template P.input
  | .clear => ShrinkSlotPlan.clear P.template P.input
  | .core p => ShrinkSlotPlan.core P.template P.input p
  | .output p => ShrinkSlotPlan.output P.template P.input P.split p
  | .copy c => ShrinkSlotPlan.copyColumn P.template P.input P.space P.step c

/-- Publish four subdivision counts, prepare the role and cyclic-site lookups, then clear the
append counters. -/
def preparationOrder : List Stage := List.ofFn Stage.subdivision ++ [.roles,.cyclic,.clear]

/-- The five sorted-slot core phases followed by base inverse, actual outgoing, actual incoming
and width publication. -/
def directoryOrder : List Stage := [.core .genuineOwners,.core .dummyOwners,.core .appendFields,
  .core .invertFields,.core .baseMatching,.output .baseInverse,.output .actualOut,.output .actualIn,.output .widths]

/-- The preparation and directory phases in the order that builds all six output columns. -/
def constructionOrder := preparationOrder ++ directoryOrder

/-- The complete shrinking slot schedule, ending with the six copies into the next level's
canonical arrays. -/
def order := constructionOrder ++ CopyIncidence.allColumns.map Stage.copy

/-- The stage enumeration uses exactly the same chronological visits as the
native block planner, including its six per-column destinations. -/
theorem order_visits (P : Plan) :
    order.map (Stage.visit P) = visits P.template P.input P.layout P.split P.space P.step := rfl

/-- Exclusive worker cursor for each stage, using its actual site, owner, field or
incidence-column count. -/
def Stage.limit (s : Shape) : Stage → ℕ
  | .subdivision _ => 1
  | .roles => 8
  | .cyclic => sites s
  | .clear => owners s+fields s
  | .core p => SlotLevel.limit s p
  | .output p => ShrinkSlots.Recipe.limit s p
  | .copy c => if c.val < 3 then baseArcs s else actualCount s

/-- Number of public operand words expected by the worker for this scheduled stage. -/
abbrev Stage.arity : Stage → ℕ
  | .subdivision _ | .roles => 2
  | .cyclic | .copy _ => 3
  | .clear => 1
  | .core p => SlotLevel.arity p
  | .output p => ShrinkSlots.Recipe.arity p

theorem Stage.params (P : Plan) (j : Stage) : (j.visit P).worker.params = j.arity := by
  cases j with
  | core p => cases p <;> rfl
  | output p => cases p <;> rfl
  | _ => rfl

variable {w : ℕ}

/-- Instantiate the stage's physical operands from the slot shape and table heads, chosen
layout, split widths and destination directory. -/
def Stage.bank (s : Shape) (h : Heads) (chosen : Bool) (splitHead : ℕ) (dest : IncidenceDirectory w) :
    (j : Stage) → Fin j.arity → Word w
  | .subdivision i => Preparation.publishBank h.subdivisions s.subdivisions w i
  | .roles => Preparation.roleBank h chosen w
  | .cyclic => Preparation.cyclicBank s h w
  | .clear => fun _ ↦ Fin.ofNat _ (h.scratch+fields s)
  | .core p => SlotLevel.bank s h w p
  | .output p => ShrinkSlots.Recipe.bank s h splitHead w p
  | .copy c => CopyIncidence.copyPublic ((directory s h w).column c) (dest.column c)

/-- Expression evaluation at the planner cursor supplies the exact bank and
exclusive stop used by the physical worker. -/
theorem Stage.words (P : Plan) (j : Stage) {pub : Fin 5 → Word w} {state : Word w} {m : Memory w}
    {bases lanes : ℕ} {h : Heads} {chosen : Bool} {splitHead : ℕ} {dest : IncidenceDirectory w}
    (read : SlotLevel.Recipe.Reads P.input pub state m bases lanes h)
    (layout : P.layout.eval pub state m = (chosen.toNat : Word w))
    (split : P.split.eval pub state m = (splitHead : Word w))
    (columns : ∀ c, (LevelFields.incidence P.space (P.step+1) c).eval pub state m = dest.column c)
    (tag : Word w) :
    let s := P.template.shape bases lanes
    ShrinkSlotPlan.words (j.visit P) tag pub state m =
      tag :: 0 :: (j.limit s : Word w) :: List.ofFn (j.bank s h chosen splitHead dest) := by
  intro s
  cases j with
  | subdivision i => exact subdivision_words P.template P.input read tag i
  | roles => exact role_words P.input read P.layout chosen layout tag
  | cyclic => exact cyclic_words P.template P.input read tag
  | clear => exact clear_words P.template P.input read tag
  | core p => exact core_words P.template P.input read p tag
  | output p => exact output_words P.template P.input read P.split split p tag
  | copy c =>
    have eqn := copy_words P.template P.input read tag P.space P.step c
    rw [columns] at eqn
    exact eqn

/-- The visit's straight-line program has one unreachable reject instruction.
All preceding instructions, including the return, form its checked fuel bound. -/
def Source (P : Plan) (s : Shape) (h : Heads) (chosen : Bool) (splitHead : ℕ)
    (dest : IncidenceDirectory w) (j : Stage) (m : Memory w) (rs : List (Report w)) : Prop :=
  let v := j.visit P
  let bank := (j.bank s h chosen splitHead dest) ∘ Fin.cast (j.params P)
  let M := (v.worker.table.instantiate w bank).program
  runSegment M (v.worker.pcs-1) (some 0) m (List.replicate (j.limit s) []) = some rs

variable (P : Plan) (s : Shape) (h : Heads) (chosen : Bool) (splitHead : ℕ) (dest : IncidenceDirectory w)
local notation "src" => Source P s h chosen splitHead dest

private theorem preparation_sources (r : Preparation.Reports w) (m : Memory w)
    (hr : r.Native s h chosen m) : SourceWalk src preparationOrder m r.all := by
  obtain ⟨hp,hr,hn,hc⟩ := hr
  have put (i : Fin 4) : src (.subdivision i) (after m (eventLog ((List.ofFn r.publish).take i.val))) [r.publish i] :=
    hp i
  have p₀ : SourceWalk src [.subdivision 0] m [r.publish 0] := .singleton (put 0)
  have pubs : SourceWalk src (List.ofFn Stage.subdivision) m (List.ofFn r.publish) :=
    ((p₀.append (.singleton (put 1))).append (.singleton (put 2))).append (.singleton (put 3))
  let mp := after m (eventLog (List.ofFn r.publish))
  have rest : SourceWalk src [.roles,.cyclic,.clear] mp (r.roles++(r.cyclic++r.clear)) :=
    .next hr (.next hn (.singleton hc))
  simpa only [preparationOrder,Preparation.Reports.all,List.append_assoc] using pubs.append rest

private theorem directory_sources (r : Build.Passes w) (m : Memory w) (hr : r.Native s h splitHead m) :
    SourceWalk src directoryOrder m r.all := by
  obtain ⟨⟨hg,hd,ha,hi,hb⟩,⟨hbi,ho,hinc⟩,hw⟩ := hr
  simp only [Build.Passes.all,SlotLevel.Reports.all,MateReports.all,List.append_assoc]
  exact .next hg (.next hd (.next ha (.next hi (.next hb (.next hbi (.next ho (.next hinc (.singleton hw))))))))

/-- Extraction of the original reports of all sixteen construction phases,
with the physical banks and fresh cursors of their compiled workers. -/
theorem construction_sources (r : Build.Construction w) (m : Memory w) (hr : r.Native s h splitHead chosen m) :
    SourceWalk src constructionOrder m r.all :=
  (preparation_sources P s h chosen splitHead dest r.prepare m hr.1).append
    (directory_sources P s h chosen splitHead dest r.passes (r.prepare.final m) hr.2)

variable {a l : ℕ} (Y : Compression.State a l)

/-- Copy the completed columns using their actual base or lane-slot row count. -/
theorem copy_sources {cs : List (Fin 6)} {m : Memory w} {rs : List (Report w)}
    (lengths : ∀ c, CopyIncidence.rows Y c = (Stage.copy c).limit s)
    (hr : CopyIncidence.Runs Y (directory s h w) dest cs m rs) :
    SourceWalk src (cs.map Stage.copy) m rs := by
  induction hr with
  | nil => exact .done _
  | cons c hr _ ih =>
    rw [lengths] at hr
    exact .next hr ih

/-- The twenty-two-stage source walk retains every report in construction
and copying. The destination represents the selected next state at the end. -/
theorem sources (r : Build.Construction w) (m : Memory w)
    (hr : r.Native s h splitHead chosen m)
    (lengths : ∀ c, CopyIncidence.rows Y c = (Stage.copy c).limit s)
    (reg : CopyIncidence.Regions Y (directory s h w) dest)
    (rep : (directory s h w).Represents Y (after m (eventLog r.all))) :
    let built := after m (eventLog r.all)
    let copies := CopyIncidence.reports Y (directory s h w) dest CopyIncidence.allColumns built
    SourceWalk src order m (r.all++copies) ∧ dest.Represents Y (after built (eventLog copies)) := by
  intro built copies
  obtain ⟨copied,rep',_⟩ := CopyIncidence.copy_directory Y (directory s h w) dest built reg rep
  exact ⟨(construction_sources P s h chosen splitHead dest r m hr).append
    (copy_sources P s h chosen splitHead dest Y lengths copied),rep'⟩

end CompressorRecords.ShrinkSlotPlan.Scheduled

end VPVNP
end Computability
end OAI
