import OAI.Computability.VPVNP.LivePublicExpr
import OAI.Computability.VPVNP.LiveStageOperands
import OAI.Computability.VPVNP.LiveStageLinkPaths

/-!
# Linking native components with length-computable public operands

Each piece has its own register and operand count. The single finite native
table shares registers, and numbers the disjoint operand rows by a concrete
finite equivalence. Its sole additional operand is the outer tag address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram
open BurstRAM BurstRAM.PrivateRAM

/-- The processor may read its own literal prefix when constructing the primed
strings. Supplying these two parsed values avoids embedding its code in itself. -/
structure LiteralPrefix where
  /-- Length in bits of the processor's literal program prefix as read from its input. -/
  length : ℕ
  /-- Packed natural number representing the bits of that literal program prefix. -/
  value : ℕ

/-- Source of one public operand, chosen from a geometry expression, the literal prefix length,
or its packed word. -/
inductive InputOperand where
  | geometry (e : PublicExpr)
  | prefixLength
  | prefixWord

/-- Evaluate an operand using the supplied geometry and the two parsed literal-prefix values. -/
def InputOperand.eval (g : Geometry) (p : LiteralPrefix) : InputOperand → ℕ
  | .geometry e => e.eval g
  | .prefixLength => p.length
  | .prefixWord => p.value

/-- A native component with a finite instruction table, register and operand counts, and a
source for each public operand. -/
structure Piece where
  /-- Number of program-counter positions in this component's instruction table. -/
  pcs : ℕ
  /-- Number of ordinary registers addressed by this component's instructions. -/
  regs : ℕ
  /-- Number of public operand positions in the component. -/
  count : ℕ
  /-- The component's burst-RAM template at its specified instruction, register, and operand
  counts. -/
  table : Template pcs regs count
  /-- Select the source of each public word supplied to the component. -/
  operands : Fin count → InputOperand

/-- Package a native table whose public operands are all evaluated from geometry expressions. -/
def Piece.ofTable {p r k : ℕ} (T : Template p r k) (operands : Fin k → PublicExpr) : Piece :=
  ⟨p,r,k,T,InputOperand.geometry ∘ operands⟩

namespace Pieces
variable {d : ℕ} (rows : Fin d → Piece) (next : Fin d → Option (Fin d)) (tag : PublicExpr)

/-- Size of the shared ordinary register bank, given by the largest component register count. -/
def regs := Finset.univ.sup fun s => (rows s).regs
/-- Total length of the public operand bank obtained by concatenating the component operand
rows. -/
def count := ∑ s, (rows s).count

/-- Embed a component's register in the shared bank at the same numerical index. -/
def regEmbedding (s : Fin d) : Fin (rows s).regs ↪ Fin (regs rows) :=
  ⟨fun i => i.castLE (Finset.le_sup (Finset.mem_univ s)), fun _ _ h => Fin.ext (congrArg (fun x : Fin (regs rows) => x.val) h)⟩

/-- Number a component's local operand in the disjoint union of all component operand rows. -/
def operandEmbedding (s : Fin d) (i : Fin (rows s).count) : Fin (count rows) := finSigmaFinEquiv ⟨s,i⟩

/-- Relocate a component's ordinary registers and public operands into the shared banks. -/
def table (s : Fin d) : Template (rows s).pcs (regs rows) (count rows) :=
  LiveStageLink.widen (rows s).table (regEmbedding rows s) (operandEmbedding rows s)

/-- Link the relocated component tables using the prescribed successor for each accepting stage
exit. -/
def program := LiveStageLink.linked (table rows) next

/-- Look up the operand source belonging to a flattened component and operand index. -/
def bank (i : Fin (count rows)) : InputOperand :=
  let p := finSigmaFinEquiv.symm i
  (rows p.1).operands p.2

/-- Append the geometry expression for the linker's stage-tag address to the component operand
bank. -/
def operand : Fin (count rows+1) → InputOperand := Fin.snoc (bank rows) (.geometry tag)

/-- Evaluate a public operand and encode its natural value as a word at the geometry's RAM
width. -/
def word (g : Geometry) (lit : LiteralPrefix) (e : InputOperand) : Word g.w := Fin.ofNat _ (e.eval g lit)

/-- Encode every linked public operand, including the final stage-tag address, for the given
geometry and literal prefix. -/
def publicData (g : Geometry) (lit : LiteralPrefix) := word g lit ∘ operand rows tag

/-- Instantiate the linked native table at the geometry's word width with the evaluated public
bank. -/
def machine (g : Geometry) (lit : LiteralPrefix) := (program rows next).instantiate g.w (publicData rows tag g lit)

/-- Instantiate the individual component using its own public operand row at the same geometry
and literal prefix. -/
def component (s : Fin d) (g : Geometry) (lit : LiteralPrefix) := ((rows s).table.instantiate g.w (word g lit ∘ (rows s).operands)).program

@[simp] theorem bank_at (s : Fin d) (i : Fin (rows s).count) :
    bank rows (operandEmbedding rows s i) = (rows s).operands i := by
  unfold bank operandEmbedding
  rw [Equiv.symm_apply_apply]

/-- The physical processor can evaluate the flattened bank without receiving
any extra header contents or choices in its startup registers. -/
theorem data_eq (g : Geometry) (lit : LiteralPrefix) : publicData rows tag g lit =
    LiveStageLink.publicData (word g lit ∘ bank rows) (word g lit (.geometry tag)) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [publicData,operand,LiveStageLink.publicData]

/-- Operand relocation is invisible to native execution in each selected stage. -/
theorem component_eq (g : Geometry) (lit : LiteralPrefix) (s : Fin d) (fuel : ℕ) (st : Word g.w) (m : Memory g.w)
    (bits : List Bool) :
    let enlarged := ((table rows s).instantiate g.w (word g lit ∘ bank rows)).program
    execute enlarged fuel (enlarged.start st) m bits =
      execute (component rows s g lit) fuel ((component rows s g lit).start st) m bits := by
  apply (LiveStageLink.execute_widen_start (rows s).table (regEmbedding rows s) (operandEmbedding rows s)
    (word g lit ∘ bank rows) fuel st m bits).trans
  have h : (word g lit ∘ bank rows) ∘ operandEmbedding rows s = word g lit ∘ (rows s).operands := by
    funext i; simp
  rw [h]; rfl

/-- Every successful original native call appears in the linked machine on
precisely its own bit string, with the prescribed tag effect and bounded overhead. -/
theorem execute_component (g : Geometry) (lit : LiteralPrefix) (s : Fin d) (hfit : d ≤ 2^g.w) {f cap : ℕ}
    (hcap : f+2*d+5 ≤ cap) (st : Word g.w) (m : Memory g.w) (ht : m (word g lit (.geometry tag)).val = LiveStageLink.tagWord g.w s)
    (bs : List Bool) (rep : Report g.w) (h : execute (component rows s g lit) f ((component rows s g lit).start st) m bs = some rep) :
    execute (machine rows next tag g lit).program cap ((machine rows next tag g lit).program.start st) m bs =
      some (LiveStageLink.linkedReport next (word g lit (.geometry tag)) s rep) := by
  unfold machine program
  rw [data_eq]
  exact LiveStageLink.execute_linked_of_stage (table rows) next _ _ s hfit hcap st m ht bs rep
    ((component_eq rows g lit s f st m bs).trans h)

/-- Exact replay for every choice stream, including rejection and calls after
termination. The per-stage semantics in this replay are native templates. -/
theorem paths_eq (g : Geometry) (lit : LiteralPrefix) (hfit : d ≤ 2^g.w) (f : ℕ) (hf : 2*d+2 ≤ f)
    (st : Option (Word g.w)) (m : Memory g.w) (bs : List (List Bool)) :
    runSegment (machine rows next tag g lit).program f st m bs =
      LiveStageLink.stageSegment (table rows) next (word g lit ∘ bank rows) (word g lit (.geometry tag)) f st m bs := by
  unfold machine program
  rw [data_eq]
  exact LiveStageLink.runSegment_eq_stageSegment (table rows) next _ _ hfit f hf st m bs

end Pieces
end LiveProgram

end VPVNP
end Computability
end OAI
