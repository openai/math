import OAI.Computability.VPVNP.PairRefreshResidentDispatch
import OAI.Computability.VPVNP.PairSimulationMapHandlerImage
import OAI.Computability.VPVNP.PairSimulationMapInvocationClock
import OAI.Computability.VPVNP.CompressorRefreshDiagonalFrame
import OAI.Computability.VPVNP.CompressorRefreshMapWorkspace

/-!
# The diagonal, dispatch and motif rows of a refresh vertex

The two diagonal tests enter the grid/party loader on success and a local
reject instruction on failure. Every target of the ordinal chains is the
argument writer of the corresponding inlined map. All operands are evaluated
from the six registers selected by the enclosing role.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.RefreshResidentImage

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe OperandInputs PairSimulation NodeArguments MotifConversion MotifSelector
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {t hist shared : ℕ}
local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "hd" => And.right S.degree_bounds

/-- Fixed resident refresh plan giving the tie ordering, physical operand recipes, histogram
ordinals, and source register assignments. -/
structure Plan (t hist shared : ℕ) where
  /-- Enumeration of the graph's refresh ties used by the operand and handler tables. -/
  ties : Fin t ≃ Tie D
  /-- Stride supplied to the refresh term and route address recipes. -/
  stride : ℕ
  /-- Runtime address expressions for the old and new refresh argument packets and published
  level tables. -/
  input : OperandInputs.Input
  /-- Recipe expression locating the private map-call directory. -/
  directory : Expr
  /-- Recipe expression locating the persistent private histogram counters. -/
  histogram : Expr
  /-- Map each refresh parameter entry to its counter ordinal in the common histogram. -/
  ordinal : (parameterData B.refresh).Entry → Fin hist
  /-- Identify the six recipe inputs among the DFS, saved, and shared registers. -/
  source : Fin 6 → MapHandlerImage.Source shared

namespace Plan

variable {B} (A : Plan B t hist shared)

/-- Compute the planned map-call field heads from the tie geometry, argument inputs, directory,
and histogram. -/
noncomputable def heads := MapCallWords.plannedHeads D H A.stride A.input A.directory A.histogram

/-- Assemble the refresh map handler for each demand and party, with inline table layout,
operand recipes, and global histogram ordinals. -/
noncomputable def family : MapHandlerImage.Family B.refresh hist shared where
  regCount i := RegisterSetup.regCount (MapCallTable.formulas (MapEntryTable.allocation B.refresh i.1 i.2)
    (Fintype.equivFin _) (Fintype.equivFin _)) + 3
  portCount i := Nat.card (MapEntryTable.PublicPort B.refresh i.1 i.2)
  layout i := MapInline.layout B.refresh i.1 i.2
  ordinal := A.ordinal
  base _ := A.directory
  field _ := MapCallWords.fields S.graph.toSlotGraph hd A.ties A.stride A.input A.heads
  source _ := A.source

/-- Register expressions for checking the diagonal tie at the designated external refresh slot. -/
def diagonal := DiagonalFrame.fields D (refreshSlots hd (Sum.inl 0)) A.input
/-- Register expressions that select the demand profile and party of the refresh map call. -/
def route := MapRoute.fields D A.stride A.input

/-- Instruction addresses for diagonal setup, the comparisons, route setup and dispatch, the
map handler, and the rejection exit. -/
noncomputable abbrev Address := Fin (RegisterSetup.lines A.diagonal).length ⊕ (Fin 3 × Fin 7) ⊕
  Fin (RegisterSetup.lines A.route).length ⊕ ResidentDispatchImage.Address B.refresh.grid.demands (Fin D) ⊕
  A.family.Address ⊕ Unit

/-- Local register banks reserved for diagonal setup and scanning, route evaluation, and the
selected map handler. -/
noncomputable abbrev Local := (Fin (RegisterSetup.regCount A.diagonal) ⊕ Fin 4) ⊕
  Fin (RegisterSetup.regCount A.route) ⊕ A.family.PrivateReg

variable {p r w : ℕ} (pc : A.Address → Fin p) (dfs : Fin 9 ↪ Fin r)
  (saved : VertexImage.Saved ↪ Fin r) (common : Fin shared ↪ Fin r) (own : A.Local ↪ Fin r) (done : Fin p)

/-- Resolve each recipe input to its host register using its designated DFS, saved, or shared
source. -/
def inputs (i : Fin 6) := (A.source i).elim dfs (Sum.elim saved common)

/-- Register embedding for the compiled diagonal-setup expressions. -/
noncomputable def diagVM : Fin (RegisterSetup.regCount A.diagonal) ↪ Fin r :=
  (Function.Embedding.inl.trans Function.Embedding.inl).trans own

private def diagSlots : Fin 10 ↪ (Fin 6 ⊕ Fin 4) :=
  ⟨![.inl 0,.inl 1,.inl 2,.inr 0,.inr 1,.inr 2,.inr 3,.inl 3,.inl 4,.inl 5], by decide⟩

/-- Select the ten registers for the two diagonal bit scans from the setup outputs and the
additional scratch registers. -/
noncomputable def diagReg : Fin 10 ↪ Fin r :=
  (diagSlots.trans <| (Function.Embedding.sumMap
    (⟨RegisterSetup.output A.diagonal,fun _ _ eqn => Fin.ext (congrArg (Fin.val : Fin (RegisterSetup.regCount A.diagonal) → ℕ) eqn)⟩ : Fin 6 ↪ _)
    (Function.Embedding.refl _)).trans Function.Embedding.inl).trans own

theorem outputs (i : Fin 6) :
    A.diagVM own (RegisterSetup.output A.diagonal i) = A.diagReg own (DiagonalFrame.register i) := by
  fin_cases i <;> rfl

/-- Register embedding for the compiled route-setup expressions. -/
noncomputable def routeVM : Fin (RegisterSetup.regCount A.route) ↪ Fin r :=
  (Function.Embedding.inl.trans Function.Embedding.inr).trans own

/-- Place the refresh handler family's private registers in the resident plan's local bank. -/
noncomputable def handlerReg : A.family.PrivateReg ↪ Fin r :=
  (Function.Embedding.inr.trans Function.Embedding.inr).trans own

/-- Program counter of the chosen control or bit-scan instruction in the diagonal comparison
block. -/
def comparePC (scan : Fin 3) (i : Fin 7) := pc (.inr (.inl (scan,i)))
/-- Program counter of a refresh grid or party dispatch instruction. -/
def routePC (a : ResidentDispatchImage.Address B.refresh.grid.demands (Fin D)) := pc (.inr (.inr (.inr (.inl a))))
/-- Translate a local map-family instruction address into its resident program counter. -/
def handlerPC (a : A.family.Address) := pc (.inr (.inr (.inr (.inr (.inl a)))))
/-- Rejection address reached when the resident refresh selection fails. -/
def bad := pc (.inr (.inr (.inr (.inr (.inr ())))))

/-- Program counter for a diagonal setup line, with fallthrough to the first comparison once
all operands are evaluated. -/
noncomputable def diagSetup (i : ℕ) : Fin p := if hi : i < (RegisterSetup.lines A.diagonal).length then
  pc (.inl ⟨i,hi⟩) else A.comparePC pc 0 0
/-- Program counter for a route setup line, with fallthrough to the dispatch entry after its
last line. -/
noncomputable def routeSetup (i : ℕ) : Fin p := if hi : i < (RegisterSetup.lines A.route).length then
  pc (.inr (.inr (.inl ⟨i,hi⟩))) else A.routePC pc (.inl ())

/-- The installed grid-and-party dispatcher using the evaluated route registers and the
family's handler entries. -/
noncomputable def dispatcher := RefreshResidentDispatch.image B A.input A.stride (A.routeVM own)
  (A.routePC pc) (fun z j => A.family.target (A.handlerPC pc) (z,j)) (A.bad pc)

/-- The host rows. The caller supplies the already loaded common registers and
the continuation for a successful motif. The diagonal and map failures halt. -/
noncomputable def text : A.Address → Instr 5 p r 11
  | .inl i => (RegisterSetup.instruction (w := 2) (A.diagVM own) (A.inputs dfs saved common)
      (RegisterSetup.lines A.diagonal)[i.val] (A.diagSetup pc (i.val+1))).resize 5
  | .inr (.inl (s,i)) => match s.val with
    | 0 => RefreshDiagonal.control (A.comparePC pc 0) (A.comparePC pc 1) (A.comparePC pc 2)
        (A.diagReg own) (A.routeSetup pc 0) (A.bad pc) i
    | 1 => MapConsistency.instruction (A.comparePC pc 1) (RefreshDiagonal.loopRegs (A.diagReg own)) (A.comparePC pc 0 2) i
    | _ => MapConsistency.instruction (A.comparePC pc 2) (RefreshDiagonal.loopRegs (A.diagReg own)) (A.comparePC pc 0 5) i
  | .inr (.inr (.inl i)) => (RegisterSetup.instruction (w := 2) (A.routeVM own) (A.inputs dfs saved common)
      (RegisterSetup.lines A.route)[i.val] (A.routeSetup pc (i.val+1))).resize 5
  | .inr (.inr (.inr (.inl a))) => (A.dispatcher pc own).text a
  | .inr (.inr (.inr (.inr (.inl a)))) =>
      A.family.text (A.handlerPC pc) dfs saved common (A.handlerReg own) done a
  | .inr (.inr (.inr (.inr (.inr _)))) => .reject

private noncomputable def number (Z : Type*) [Finite Z] : Z ≃ Fin (Nat.card Z) := by
  letI := Fintype.ofFinite Z
  exact Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm

/-- Finite numbering of all addresses in the resident refresh instruction image. -/
noncomputable def locations : A.Address ≃ Fin (Nat.card A.Address) := number _
/-- Finite numbering of the shared and local registers used to install the resident image. -/
noncomputable def registers : (Fin shared ⊕ A.Local) ≃ Fin (Nat.card (Fin shared ⊕ A.Local)) := number _

/-- The vertex segment obtained by numbering the plan's instructions and registers, entered at
the first diagonal-setup instruction. -/
noncomputable def segment : VertexImage.Segment where
  count := Nat.card A.Address
  privateRegs := Nat.card (Fin shared ⊕ A.Local)
  entry := A.diagSetup A.locations 0
  row loc dfs saved localRegs done i := A.text (loc ∘ A.locations) dfs saved
    ((Function.Embedding.inl.trans A.registers.toEmbedding).trans localRegs)
    ((Function.Embedding.inr.trans A.registers.toEmbedding).trans localRegs) done (A.locations.symm i)

variable (M : Machine w p r 11)
/-- Each physical instruction at a plan address is the plan's instruction resized to the
machine word width. -/
def Installed : Prop := ∀ a, M.code (pc a) = (A.text pc dfs saved common own done a).resize w

private theorem resize5 (op : Instr 2 p r 11) : (op.resize 5).resize w = op.resize w := by
  cases op <;> try rfl
  case constant dst val next => simp only [Instr.resize, resize_literal (by decide : 2 ≤ 5)]

variable (installed : A.Installed pc dfs saved common own done M)

include installed in
theorem diag_link : RegisterSetup.Linked (A.diagVM own) (A.inputs dfs saved common) M (A.diagSetup pc)
    (RegisterSetup.lines A.diagonal) := by
  intro i
  rw [diagSetup,dite_eq_left i.isLt,installed]
  exact (resize5 _).trans (RegisterSetup.resize_instruction ..)

include installed in
theorem compare_link : RefreshDiagonal.Linked M (A.comparePC pc 0) (A.comparePC pc 1) (A.comparePC pc 2)
    (A.diagReg own) (A.routeSetup pc 0) (A.bad pc) := by
  constructor <;> intro i <;> apply (installed (.inr (.inl (_,i)))).trans <;> fin_cases i <;> rfl

include installed in
theorem route_link : RegisterSetup.Linked (A.routeVM own) (A.inputs dfs saved common) M (A.routeSetup pc)
    (RegisterSetup.lines A.route) := by
  intro i
  rw [routeSetup,dite_eq_left i.isLt,installed]
  exact (resize5 _).trans (RegisterSetup.resize_instruction ..)

include installed in
theorem dispatch_link : (A.dispatcher pc own).Linked M := fun a => installed (.inr (.inr (.inr (.inl a))))

include installed in
theorem handler_rows (a) : M.code (A.handlerPC pc a) =
    (A.family.text (A.handlerPC pc) dfs saved common (A.handlerReg own) done a).resize w :=
  installed (.inr (.inr (.inr (.inr (.inl a)))))

include installed in
theorem rejection : M.code (A.bad pc) = .reject := installed (.inr (.inr (.inr (.inr (.inr ())))))

theorem segment_installed (loc : Fin A.segment.count → Fin p)
    (localRegs : Fin A.segment.privateRegs ↪ Fin r)
    (installed : ∀ i, M.code (loc i) = (A.segment.row loc dfs saved localRegs done i).resize w) :
    A.Installed (loc ∘ A.locations) dfs saved
      ((Function.Embedding.inl.trans A.registers.toEmbedding).trans localRegs)
      ((Function.Embedding.inr.trans A.registers.toEmbedding).trans localRegs) done M := by
  intro a
  change M.code (loc (A.locations a)) = _
  exact (installed (A.locations a)).trans (by simp only [segment,Equiv.symm_apply_apply])

end Plan
end CompressorRecords.PortRefresh.RefreshResidentImage

end VPVNP
end Computability
end OAI
