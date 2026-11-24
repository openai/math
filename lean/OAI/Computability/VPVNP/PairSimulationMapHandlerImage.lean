import OAI.Computability.VPVNP.PairSimulationMapInlineImage
import OAI.Computability.VPVNP.PairSimulationMapArgumentWriter

/-!
# Vertex image of the grid-point and party map handlers

Every fixed handler first evaluates its argument recipes and writes the raw
call descriptor. The descriptor pointer goes directly into the lowered map's
pointer register. All successful calls enter the common continuation, while
failed calls reach a rejecting instruction local to the selected handler.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapHandlerImage

open MotifSelector MotifGrid MotifBlocks MotifConversion MapConstants
open BurstRAM.PrivateRAM CompressorRecords CompressorRecords.PhaseRecipe

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  (B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H') {t shared p r w : ℕ}

/-- The writer's six incoming values can be selected from DFS, saved bootstrap,
or the enclosing role's own shared header and cursor registers. -/
abbrev Source (shared : ℕ) := Fin 9 ⊕ VertexImage.Saved ⊕ Fin shared

/-- A demand grid point paired with the party whose local map table handles that demand. -/
abbrev Index := B.grid.demands × J

/-- Fixed code and data recipes for one whole role. -/
structure Family (t shared : ℕ) where
  /-- Number of source registers allocated to each grid-point and party map table. Lowering the
  table adds two scratch registers. -/
  regCount : Index B → ℕ
  /-- Number of public ports in each source map table, used to index the constants that will be
  inlined. -/
  portCount : Index B → ℕ
  /-- Register, port and argument allocations used to assemble the map call table for each
  demand grid point and party. -/
  layout : ∀ i : Index B, MapCallTable.Layout B i.1 i.2 (regCount i) (portCount i)
  /-- Assigns each motif parameter entry its histogram index, shared by the lookup tables of
  every handler in the family. -/
  ordinal : (parameterData B).Entry → Fin t
  /-- Expression whose value is the first private word of the call descriptor for the selected
  handler. -/
  base : Index B → Expr
  /-- Expression that computes the word to publish for each named descriptor argument of the
  selected handler. -/
  field : Index B → MapCallSetup.Arg D E → Expr
  /-- Chooses a DFS, saved bootstrap or role-shared register for each of the descriptor
  writer's five public operands and its state operand. -/
  source : Index B → Fin 6 → Source shared

private noncomputable def number (X : Type*) [Finite X] : X ≃ Fin (Nat.card X) := by
  letI := Fintype.ofFinite X
  exact Fintype.equivFinOfCardEq Nat.card_eq_fintype_card.symm

namespace Family

variable {B} (F : Family B t shared)

/-- Descriptor field expressions in physical slot order. The layout's inverse argument
numbering recovers the named argument stored at each offset. -/
noncomputable def fields (i : Index B) := F.field i ∘ (F.layout i).args.symm

/-- Vertex code segment for one lowered map call table, with the family's parameter ordinals
embedded among its lookup constants. -/
noncomputable abbrev image (i : Index B) := MapInline.imageSegment (F.layout i) F.ordinal

/-- Local instruction addresses for evaluating one handler's field and base expressions,
installing its descriptor pointer and storing the fields. -/
noncomputable abbrev WriterPC (i : Index B) :=
  MapArgumentWriter.Address (F.base i) (F.fields i)

/-- Instruction addresses of the whole family. Each selects a grid point and party, then either
a descriptor writer instruction or a row of the lowered map. -/
noncomputable abbrev Address := (i : Index B) × (F.WriterPC i ⊕ Fin (F.image i).count)

/-- Size of the register bank needed to evaluate all descriptor field expressions and the base
expression for one handler. -/
noncomputable abbrev VMCount (i : Index B) :=
  RegisterSetup.regCount (MapArgumentWriter.recipes (F.base i) (F.fields i))

/-- Registers private to one handler, grouped into the expression evaluator, two
descriptor-writing temporaries, and the map's source registers plus two lowering
temporaries. -/
noncomputable abbrev Local (i : Index B) := Fin (F.VMCount i) ⊕ Fin 2 ⊕ Fin (F.regCount i + 2)

/-- A private register identified by its grid-point and party handler and its slot in that
handler's local bank. -/
noncomputable abbrev PrivateReg := (i : Index B) × F.Local i

variable (pc : F.Address → Fin p) (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r)
  (common : Fin shared ↪ Fin r) (own : F.PrivateReg ↪ Fin r) (advance : Fin p)

/-- Resolves one of the writer's six input operands to the physical DFS, saved or shared
register chosen by the handler's source assignment. -/
def inputs (i : Index B) (a : Fin 6) : Fin r :=
  (F.source i a).elim dfs (Sum.elim saved common)

/-- Embeds the selected handler's local register slots into the host machine through the
allocation of the family's private registers. -/
noncomputable def localReg (i : Index B) : F.Local i ↪ Fin r :=
  (⟨Sigma.mk i, fun _ _ h ↦ eq_of_heq (Sigma.mk.inj h).2⟩ : F.Local i ↪ F.PrivateReg).trans own

/-- Physical registers used by the selected handler's expression evaluator to compute the
descriptor fields and pointer. -/
noncomputable def vm (i : Index B) : Fin (F.VMCount i) ↪ Fin r :=
  Function.Embedding.inl.trans (F.localReg own i)

/-- Physical register embedding for one lowered map, including its source map registers and the
two scratch registers used to materialize constants. -/
noncomputable def mapReg (i : Index B) : Fin (F.regCount i + 2) ↪ Fin r :=
  (Function.Embedding.inr.trans Function.Embedding.inr).trans (F.localReg own i)

/-- The descriptor publisher returns the pointer in exactly the source map's pointer
register. Its two other temporaries belong to the writer. -/
noncomputable def aux (i : Index B) : Fin 3 ↪ Fin r :=
  (⟨Fin.cases (.inr (.inr ((F.layout i).ptr.castAdd 2))) (fun j ↦ .inr (.inl j)), by
    intro a b h
    fin_cases a <;> fin_cases b <;> first | rfl | cases h⟩ :
      Fin 3 ↪ F.Local i).trans (F.localReg own i)

/-- Host program counter of an instruction in the selected handler's descriptor writer. -/
def writerPC (i : Index B) (a : F.WriterPC i) := pc ⟨i, .inl a⟩

/-- Host program counter of a row in the selected handler's lowered map segment. -/
def mapPC (i : Index B) (a : Fin (F.image i).count) := pc ⟨i, .inr a⟩

/-- Installs one lowered map at its assigned instruction and register locations, routing
success to the shared continuation and rejection to its local reject instruction. -/
noncomputable def placement (i : Index B) :=
  MapInline.imagePlacement (F.layout i) F.ordinal (F.mapPC pc i) (F.mapReg own i) advance

/-- The dynamically selected target starts with the actual descriptor writer. -/
noncomputable def target (i : Index B) :=
  MapArgumentWriter.setupPC (F.base i) (F.fields i) (F.writerPC pc i) 0

/-- The first part of each grid/party bank is the raw argument writer, followed
by the actual inlined eleven-port map code. -/
noncomputable def text : F.Address → Instr 5 p r 11
  | ⟨i, .inl a⟩ =>
    (MapArgumentWriter.text (F.base i) (F.fields i) (F.vm own i) (F.inputs dfs saved common i)
      (F.aux own i) (F.writerPC pc i) (F.mapPC pc i (F.image i).entry) a).resize 5
  | ⟨i, .inr a⟩ =>
    (F.image i).row (F.mapPC pc i) dfs saved (F.mapReg own i) advance a

/-- The role's shared inputs and the caller's saved registers lie outside the bank
in which the handlers publish and evaluate their descriptors. -/
structure Apart : Prop where
  dfs : ∀ a b, own a ≠ dfs b
  saved : ∀ a b, own a ≠ saved b
  shared : ∀ a b, own a ≠ common b

theorem vm_safe (h : F.Apart dfs saved common own) (i : Index B) (a b) :
    F.vm own i a ≠ F.inputs dfs saved common i b := by
  unfold inputs
  cases F.source i b with
  | inl j => exact h.dfs _ j
  | inr x =>
    cases x with
    | inl j => exact h.saved _ j
    | inr j => exact h.shared _ j

/-- All writer scratch slots are disjoint from the map pointer and writer cursors. -/
theorem vm_aux (i : Index B) (a b) : F.vm own i a ≠ F.aux own i b := by
  fin_cases b <;> exact (F.localReg own i).injective.ne Sum.inl_ne_inr

theorem pointer (i : Index B) :
    (F.placement pc own advance i).reg (F.layout i).ptr = F.aux own i 0 := rfl

private theorem resize5 (op : Instr 2 p r 11) : (op.resize 5).resize w = op.resize w := by
  cases op <;> try rfl
  case constant dst val next => simp only [Instr.resize, resize_literal (by decide : 2 ≤ 5)]

variable (M : Machine w p r 11)
  (installed : ∀ a, M.code (pc a) = (F.text pc dfs saved common own advance a).resize w)

include installed in
/-- Per-handler links extracted from the actual rows of the complete image. -/
theorem links (i : Index B) :
    let V := F.placement pc own advance i
    (∀ a, M.code (F.writerPC pc i a) = (MapArgumentWriter.text (F.base i) (F.fields i)
      (F.vm own i) (F.inputs dfs saved common i) (F.aux own i) (F.writerPC pc i)
      (V.entry (F.layout i).template.entry) a).resize w) ∧
    MapInline.Linked (F.layout i) F.ordinal V M ∧
    V.entry (MapInline.callProgram (F.layout i)).done = advance ∧
    M.code (V.entry (MapInline.callProgram (F.layout i)).bad) = .reject := by
  intro V
  let rows := fun a ↦ installed ⟨i, .inr a⟩
  refine ⟨?_, MapInline.imageLinked (F.layout i) F.ordinal _ _ advance dfs saved M rows,
    MapInline.imageDone (F.layout i) F.ordinal _ _ advance,
    MapInline.imageReject (F.layout i) F.ordinal _ _ advance dfs saved M rows⟩
  intro a
  rw [show V.entry (F.layout i).template.entry = F.mapPC pc i (F.image i).entry from
    MapInline.imageEntry ..]
  exact (installed ⟨i, .inl a⟩).trans (resize5 _)

/-- Finite numbering of all descriptor writer instructions and lowered map rows, used to
address the family as one vertex segment. -/
noncomputable def locations : F.Address ≃ Fin (Nat.card F.Address) := number _

/-- Numbers the role's shared registers together with every handler's private slots for
allocation in the vertex segment's register bank. -/
noncomputable def registers :
    (Fin shared ⊕ F.PrivateReg) ≃ Fin (Nat.card (Fin shared ⊕ F.PrivateReg)) :=
  number _

/-- A native vertex subsegment with a designated grid/party entry. In a larger
role, the caller can use the other targets of the same installed table. -/
noncomputable def segment (i : Index B) : VertexImage.Segment where
  count := Nat.card F.Address
  privateRegs := Nat.card (Fin shared ⊕ F.PrivateReg)
  entry := F.target F.locations i
  row loc dfs saved localRegs done a :=
    F.text (loc ∘ F.locations) dfs saved
      ((Function.Embedding.inl.trans F.registers.toEmbedding).trans localRegs)
      ((Function.Embedding.inr.trans F.registers.toEmbedding).trans localRegs)
      done (F.locations.symm a)

/-- The surrounding role can recover every installed handler row from the
ordinary vertex segment interface at its finite program-counter numbering. -/
theorem segment_rows (chosen : Index B) (loc : Fin (Nat.card F.Address) → Fin p)
    (localRegs : Fin (Nat.card (Fin shared ⊕ F.PrivateReg)) ↪ Fin r)
    (rows : ∀ a, M.code (loc a) =
      ((F.segment chosen).row loc dfs saved localRegs advance a).resize w)
    (a : F.Address) :
    M.code (loc (F.locations a)) = (F.text (loc ∘ F.locations) dfs saved
      ((Function.Embedding.inl.trans F.registers.toEmbedding).trans localRegs)
      ((Function.Embedding.inr.trans F.registers.toEmbedding).trans localRegs)
      advance a).resize w := by
  simpa only [segment, Equiv.symm_apply_apply] using rows (F.locations a)

/-- All registers of a different grid/party handler survive the selected handler. -/
theorem different_registers {i j : Index B} (ne : i ≠ j) (x : F.Local i) (y : F.Local j) :
    F.localReg own i x ≠ F.localReg own j y := by
  intro eq
  exact ne (congrArg Sigma.fst (own.injective eq))

end Family

end PairSimulation.MapHandlerImage

end VPVNP
end Computability
end OAI
