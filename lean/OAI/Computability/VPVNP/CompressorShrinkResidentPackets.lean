import OAI.Computability.VPVNP.CompressorBlockIndex
import OAI.Computability.VPVNP.CompressorScriptWindow
import OAI.Computability.VPVNP.CompressorShrinkResidentHeaders
import OAI.Computability.VPVNP.CompressorShrinkResidentRun
import OAI.Computability.VPVNP.CompressorHeaderOperands

/-! # The twelve resident-directory visits in the installed compressor script

The old hidden and map directories each use an owner scan, a counter clear
and a guarded append. Six single-word publishers then install their heads
at offsets 30 through 35. The window starts after the 36 preceding visits
of the same shrinking substep.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkResidentPackets

open Compression BurstRAM BlockPlanner PhaseRecipe DescriptorSpace PrimedStackRAM SourceTransport
open ShrinkResidentRun ShrinkResidentLayout
open scoped Fin.CommRing

/-- Expressions and degree exponent used to plan the two resident directory builds and their
six header publications for a selected shrink. -/
structure Plan where
  /-- Selected-shrink input formulas supplying the site and motif counts, role-record base and
  layout choice. -/
  chosen : SelectedPlan.Inputs
  /-- Expression for the first workspace address assigned to the hidden-field and party-map
  directories. -/
  first : Expr
  /-- Expression for the old level header where the six completed directory heads are
  published. -/
  oldLevel : Expr
  /-- Expression for the dense motif-indexed array of absolute CD identifiers read by the owner
  scans. -/
  absoluteCD : Expr
  /-- Old degree exponent used to compute the preimage-row capacity for the collector's operand
  bank. -/
  exponent : ℕ

/-- A resident-directory operation, either writing owners, clearing counts, appending preimages
for one resident kind, or publishing one of the six heads. -/
inductive Stage
  | owners (maps : Bool)
  | clear (maps : Bool)
  | append (maps : Bool)
  | header (i : Fin 6)

/-- The three visits that build one resident directory, assigning owners, clearing site counts
and appending occurrence identifiers in order. -/
def scans (maps : Bool) : List Stage := [.owners maps,.clear maps,.append maps]

/-- Execution order of the twelve stages, building hidden-field rows, then party-map rows, then
publishing their six pointers. -/
def order : List Stage := scans false ++ scans true ++ (List.finRange 6).map Stage.header

/-- Translate one resident stage into its scheduled worker, cursor bounds and operand
expressions for this plan. -/
def Stage.visit (P : Plan) : Stage → BlockPlanner.Visit
  | .owners maps => ResidentOwners.visit maps (ShrinkResidentsPlan.size P.chosen maps) P.absoluteCD
      (SelectedPlan.roleBase P.chosen) (SelectedPlan.layout P.chosen) (ShrinkResidentsPlan.owner P.chosen P.first maps)
  | .clear maps => ops SliceRAM.clearOps 0 (.lit 0) P.chosen.newSites (fun _ => ShrinkResidentsPlan.counts P.chosen P.first maps)
  | .append maps => ops collectPreimage 3 (.lit 0) (ShrinkResidentsPlan.size P.chosen maps)
      (ShrinkResidentsPlan.bank P.chosen P.first P.exponent maps)
  | .header i => ShrinkResidentsPlan.headerVisit P.chosen P.first P.oldLevel i

/-- The ordered block-planner visits that execute both resident directory builds and publish
their heads using the plan's inputs. -/
def Plan.visits (P : Plan) := ShrinkResidentsPlan.visits P.chosen P.first P.oldLevel P.absoluteCD P.exponent

theorem Plan.ordered (P : Plan) : order.map (Stage.visit P) = P.visits := by
  simp only [order,List.map_append,List.map_map,Plan.visits,ShrinkResidentsPlan.visits,
    ShrinkResidentsPlan.publications,List.ofFn_eq_map]
  rfl

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)

/-- Recover the resident plan for a particular block substep from its selected inputs, old
level, directory arena, absolute CD table and old degree exponent. -/
def plan : Plan :=
  let F := BlockProgram.geometry B
  let origin := BlockProgram.arena B i.val 0
  ⟨ShrinkBlockInputs.selectedInputs B F i origin,BlockProgram.arena B i.val 5,LevelFields.atLevel i.val,
    ShrinkBundlePlan.absoluteCD i.val (ShrinkBlockInputs.a i) origin,ShrinkBlockInputs.a i⟩

/-- The portion of this shrinking substep preceding its resident-directory window, comprising
the first 36 visits. -/
def prior := ShrinkBlockInputs.beforeSlices B (BlockProgram.geometry B) i (BlockProgram.arena B i.val 0)

private theorem tail_exists : ∃ tail, BlockProgram.shrink B i = prior B i ++ (plan B i).visits ++ tail := by
  unfold BlockProgram.shrink
  simp only [List.append_assoc]
  exact ⟨_,rfl⟩

/-- Locate the twelve resident visits in the installed block script after the earlier substeps
and this substep's prefix. -/
def window : Window (BlockProgram.script B) (plan B i).visits where
  before := BlockIndex.earlier B i ++ prior B i
  after := (tail_exists B i).choose ++ BlockIndex.later B i
  block := by
    change BlockProgram.block B = _
    conv_lhs => rw [BlockIndex.split_block,(tail_exists B i).choose_spec]
    simp only [List.append_assoc]

theorem window_offset : (window B i).before.length = (BlockIndex.earlier B i).length+36 := by
  change (BlockIndex.earlier B i ++ prior B i).length = _
  rw [List.length_append,prior,ShrinkBlockInputs.beforeSlices_length]

theorem window_phase (t : ℕ) (j : Fin (plan B i).visits.length) :
    let A := BlockProgram.script B
    let ordinal := A.initial.length+t*A.block.length+(BlockIndex.earlier B i).length+36+j.val
    (Schedule.Online.calendar A.plan).phase ordinal = ((window B i).index j).val ∧
    (Schedule.Online.calendar A.plan).level ordinal = t := by
  dsimp only
  simpa only [Window.index,Window.position,window_offset,Fin.val_natAdd,Nat.add_assoc] using
    (BlockProgram.script B).block_phase t ((window B i).position j)

variable {w : ℕ}

/-- Concrete resident workspace, header address, source pointers and layout choice used to
instantiate the planned scans at a given word width. -/
structure Values (w : ℕ) where
  /-- The concrete layout of both resident directories, determining their table addresses and
  scan sizes. -/
  layout : ShrinkResidentLayout.Layout
  /-- Address of the old level header receiving the six resident directory pointers. -/
  level : ℕ
  /-- Machine-word pointer to the dense absolute CD identifiers, one per motif. -/
  absolute : Word w
  /-- Machine-word pointer to the four-word role records indexed by absolute old arc. -/
  role : Word w
  /-- The Boolean shrink layout used to select the resident's packed role when writing owners. -/
  side : Bool

/-- Exclusive cursor bound for this stage, the occurrence count for owners and appends, the
site count for clearing, or one for a head publication. -/
def Stage.limit (D : Values w) : Stage → ℕ
  | .owners maps | .append maps => D.layout.size maps
  | .clear _ => D.layout.sites
  | .header _ => 1

/-- Private fuel allowed for one worker call of this stage, determined by its native owner,
clear, append or publication code. -/
def Stage.fuel : Stage → ℕ
  | .owners maps => 1+(ResidentOwners.code maps).length
  | .clear _ => 8
  | .append _ => 23
  | .header _ => 7

theorem Stage.clock (j : Stage) : 0 < j.fuel ∧ j.fuel ≤ 40 := by
  cases j with
  | owners maps => cases maps <;> decide
  | clear | append | header => simp [Stage.fuel]

/-- Concrete public operand vector for the stage's worker, using the instantiated directory
addresses, source pointers and selected layout. -/
def Stage.bank (P : Plan) (D : Values w) : (j : Stage) → Fin (Stage.visit P j).worker.params → Word w
  | .owners maps => ![D.absolute,D.role,(D.side.toNat : Word w),(D.layout.owner maps : Word w)]
  | .clear maps => fun _ => (D.layout.counts maps : Word w)
  | .append maps => D.layout.params P.exponent maps w
  | .header j => ShrinkResidentsPlan.headerBank D.level D.layout w j

/-- The planned operands evaluate in the current public words, state and memory to the concrete
resident layout, header address, source pointers and selected side. -/
structure OperandValues (P : Plan) (D : Values w) (pub : Fin 5 → Word w) (st : Word w) (mem : Memory w) : Prop where
  ready : ShrinkResidentsPlan.Ready P.chosen P.first pub st mem D.layout
  oldLevel : P.oldLevel.eval pub st mem = (D.level : Word w)
  absolute : P.absoluteCD.eval pub st mem = D.absolute
  role : (SelectedPlan.roleBase P.chosen).eval pub st mem = D.role
  side : (SelectedPlan.layout P.chosen).eval pub st mem = (D.side.toNat : Word w)

theorem OperandValues.words {P : Plan} {D : Values w} {pub : Fin 5 → Word w} {st : Word w} {mem : Memory w}
    (h : OperandValues P D pub st mem) (j : Stage) :
    (j.visit P).initial.eval pub st mem = 0 ∧ (j.visit P).stop.eval pub st mem = (j.limit D : Word w) ∧
      (fun t => ((j.visit P).params t).eval pub st mem) = j.bank P D := by
  have size := ShrinkResidentsPlan.size_val P.chosen P.first pub st mem D.layout h.ready
  have owner := ShrinkResidentsPlan.owner_val P.chosen P.first pub st mem D.layout h.ready
  have counts := ShrinkResidentsPlan.counts_val P.chosen P.first pub st mem D.layout h.ready
  cases j with
  | owners maps =>
    refine ⟨rfl,size maps,?_⟩
    funext t
    fin_cases t <;> first | exact h.absolute | exact h.role | exact h.side | exact owner maps
  | clear maps => exact ⟨rfl,h.ready.sites,funext fun _ => counts maps⟩
  | append maps => exact ⟨rfl,size maps,ShrinkResidentsPlan.bank_val P.chosen P.first pub st mem D.layout h.ready P.exponent maps⟩
  | header t => exact ⟨rfl,rfl,ShrinkResidentsPlan.header_bank_eq P.chosen P.first P.oldLevel pub st mem D.level D.layout h.ready h.oldLevel t⟩

/-- The only loaded expressions needed for all twelve visits. -/
structure OperandReads (P : Plan) (data : ℕ → Prop) (pub : Fin 5 → Word w) (st : Word w) (mem : Memory w) : Prop where
  sites : P.chosen.newSites.ReadsFrom data pub st mem
  motifs : P.chosen.motifs.ReadsFrom data pub st mem
  first : P.first.ReadsFrom data pub st mem
  role : (SelectedPlan.roleBase P.chosen).ReadsFrom data pub st mem
  layout : (SelectedPlan.layout P.chosen).ReadsFrom data pub st mem
  absolute : P.absoluteCD.ReadsFrom data pub st mem
  level : P.oldLevel.ReadsFrom data pub st mem

theorem OperandReads.supported {P : Plan} {data : ℕ → Prop} {pub : Fin 5 → Word w} {st : Word w} {mem : Memory w}
    (h : OperandReads P data pub st mem) (j : Stage) : HeaderOperands.Supported data pub st mem (j.visit P) := by
  let rd := fun x : Expr => x.ReadsFrom data pub st mem
  have size (b) : rd (ShrinkResidentsPlan.size P.chosen b) := ⟨h.motifs,trivial⟩
  have owner (b) : rd (ShrinkResidentsPlan.owner P.chosen P.first b) := by
    cases b
    · exact h.first
    · exact ⟨⟨⟨h.first,size false⟩,h.sites⟩,size false⟩
  have counts (b) : rd (ShrinkResidentsPlan.counts P.chosen P.first b) := ⟨owner b,size b⟩
  have rows (b) : rd (ShrinkResidentsPlan.rows P.chosen P.first b) := ⟨counts b,h.sites⟩
  cases j with
  | owners b =>
    refine ⟨trivial,size b,?_⟩
    intro t; fin_cases t <;> first | exact h.absolute | exact h.role | exact h.layout | exact owner b
  | clear b => exact ⟨trivial,h.sites,fun _ => counts b⟩
  | append b =>
    refine ⟨trivial,size b,?_⟩
    intro t; fin_cases t <;> first | exact size b | exact owner b | exact h.sites | exact counts b | exact rows b | trivial
  | header i =>
    refine ⟨trivial,trivial,?_⟩
    intro t
    fin_cases t
    · exact ⟨h.level,trivial⟩
    · fin_cases i <;> first | exact owner false | exact counts false | exact rows false
                            | exact owner true | exact counts true | exact rows true

end CompressorRecords.ShrinkResidentPackets

end

end VPVNP
end Computability
end OAI
