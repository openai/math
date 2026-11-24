import OAI.Computability.VPVNP.PairRefreshGeometryReload
import OAI.Computability.VPVNP.CompressorRefreshTraversalHeaders
import OAI.Computability.VPVNP.PairRefreshResidentImage

/-!
# The refresh body in the terminal DFS register bank

The first fourteen shared words are the level locator's bank. The body reloads the
private histogram head, then uses the popped node, the site ordinal and the two genuine
level heads for its diagonal checks, dispatch and map call. The child's descriptor address
is read through the unique preimage row. The global parameter numbering sends each
refresh scalar to its right-summand histogram bin.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalPlan

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe
open PairSimulation PairSimulation.VertexImage NewSlots RefreshMapOperands NodeArguments
open PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {t hist : ℕ}
  (ties : Fin t ≃ Tie (2 ^ S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)

/-- The refresh level's static geometry, giving input and output degrees, expander size, tie
count, record stride, and selector width. -/
noncomputable def shape (t stride : ℕ) : LevelRecipe.Shape :=
  ⟨S.portExponent, S.degreeExponent 0, 2 ^ S.expanderExponent, t, stride, B.refresh.selectorBits⟩

/-- Construct the resident refresh plan from the traversal header operands, shared locator
sources, tie enumeration, and common histogram numbering. -/
noncomputable def plan : RefreshResidentImage.Plan B t hist 14 where
  ties := ties
  stride := stride
  input := TraversalHeaders.input (shape B t stride)
  directory := TraversalGeometry.directory hist
  histogram := TraversalGeometry.histogram
  ordinal e := order (.inr e)
  source := TraversalGeometry.source

local notation "T" => plan B ties stride order

/-- Embedding for the handoff from the locator and child scan into the local body. -/
noncomputable def locatorBank : Fin 14 ↪ Fin (T).segment.privateRegs :=
  Function.Embedding.inl.trans (T).registers.toEmbedding

/-- The native histogram reload and the exact refresh map image share the locator bank. -/
noncomputable def body : VertexImage.Segment :=
  TraversalGeometry.reload.thenWith (T).segment (locatorBank B ties stride order)
    (Equiv.refl _).toEmbedding

variable {pcs regs bits : ℕ} (loc : Fin (body B ties stride order).count → Fin pcs)
  (dfs : Fin 9 ↪ Fin regs) (saved : Saved ↪ Fin regs)
  (bank : Fin (body B ties stride order).privateRegs ↪ Fin regs) (done : Fin pcs)
  (M : Machine bits pcs regs 11)

local notation "left" =>
  Segment.leftPC TraversalGeometry.reload (RefreshResidentImage.Plan.segment T) loc
local notation "right" =>
  Segment.rightPC TraversalGeometry.reload (RefreshResidentImage.Plan.segment T) loc
local notation "commonBank" => Function.Embedding.trans (locatorBank B ties stride order) bank

/-- Installation of the single segment yields the precise geometry and local-body
links, including their common entry PC and shared registers. -/
theorem body_links
    (rows : ∀ j, M.code (loc j) =
      ((body B ties stride order).row loc dfs saved bank done j).resize bits) :
    (∀ j, M.code (left j) =
      (TraversalGeometry.reload.row left dfs saved commonBank
        (right (T).segment.entry) j).resize bits) ∧
    (T).Installed (right ∘ (T).locations) dfs saved commonBank
      ((Function.Embedding.inr.trans (T).registers.toEmbedding).trans bank) done M := by
  obtain ⟨a, b⟩ :=
    Segment.split_link TraversalGeometry.reload (T).segment (locatorBank B ties stride order)
      (Equiv.refl _).toEmbedding loc dfs saved bank done M rows
  exact ⟨a, (T).segment_installed dfs saved done M right bank b⟩

/-- The live expression operands are the four surviving locator values and the
histogram just reloaded. Operand three contains the private histogram-cell address. -/
theorem input_registers (common : Fin 14 ↪ Fin regs) :
    (T).inputs dfs saved common =
      ![common 7, common 0, common 4, common 9, common 10, common 11] := by
  funext i; fin_cases i <;> rfl

section Entry

variable {g : ℕ} (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2 ^ S.portExponent)) (A : Arena) (U V : IncidenceDirectory bits)
  (m : Memory bits) (start parent child listHead oldHead newHead histBase : ℕ)

local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "hd" => And.right S.degree_bounds
local notation "supply" =>
  blockSupplyWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) S.graph
    (Nat.two_pow_pos _) hc B.refresh choice
local notation "Pₗ" =>
  Allocation.plan X (S.degreeExponent 0) (2 ^ S.expanderExponent) t stride start
local notation "O" => sites (D := 2 ^ S.portExponent) X.baseIndex (bitWordFinEquiv g)

/-- Actual entry into the local computation from the preserved locator and child-scan
state. Only the header contents and the actual child row are used to recover the level
and its two argument frames. -/
theorem enter (rows : ∀ j,
    M.code (loc j) = ((body B ties stride order).row loc dfs saved bank done j).resize bits)
    (c : Config bits pcs regs)
    (entry : c.pc = left TraversalGeometry.reload.entry) {endAddr : ℕ} {G offset : W bits}
    (endWord : c.reg (dfs 6) = (endAddr : W bits))
    (resident : ResidentGeometry (DFS.scratch endAddr c.privateMem) G offset (word histBase))
    (oldWord : (c.reg (commonBank 11)).val = oldHead)
    (newWord : (c.reg (commonBank 4)).val = newHead)
    (siteWord : (c.reg (commonBank 7)).val = (O v).val)
    (parentWord : (c.reg (commonBank 0)).val = parent)
    (header : TraversalHeaders.Geometry (Fintype.card X.Base) g oldHead newHead start A U V m)
    (row : DFS.Row m parent listHead [word child]) (lanes : 2 ^ g < 2 ^ bits) :
    ∃ out, Prefix M c (List.replicate 4 .tick) out ∧ out.pc = right (T).segment.entry ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧
      (∀ j, j ≠ commonBank 9 → j ≠ commonBank 10 → out.reg j = c.reg j) ∧
      let inp := (T).inputs dfs saved commonBank
      let pub := fun i : Fin 5 => out.reg (inp i.castSucc)
      let state := out.reg (inp (Fin.last 5))
      OperandInputs.Describes (T).input pub state m X v S.graph.toSlotGraph S.port_order hd supply A
        child parent U V
        ((Pₗ).scratch bits) (word (Pₗ).demand) (word (Pₗ).term) ∧
      (T).directory.eval pub state m = word (histBase + hist + 12 + 2 * A.start) ∧
      (T).histogram.eval pub state m = word histBase := by
  have links := body_links B ties stride order loc dfs saved bank done M rows
  obtain ⟨out, pre, ep, histEq, frame, priv, pers⟩ :=
    TraversalGeometry.reload_native M left dfs saved commonBank
      (right (T).segment.entry) links.1 c entry endWord resident
  let C : LevelRecipe.Context bits :=
    ⟨fun i => out.reg ((T).inputs dfs saved commonBank i.castSucc),
      out.reg ((T).inputs dfs saved commonBank (Fin.last 5)), m⟩
  have keep (i : Fin 14) (hn₉ : i ≠ 9)
    (hn₁₀ : i ≠ 10) : out.reg (commonBank i) = c.reg (commonBank i) :=
    frame _ ((commonBank).injective.ne hn₉) ((commonBank).injective.ne hn₁₀)
  have oh : C.state.val = oldHead :=
    (congrArg Fin.val (keep 11 (by decide) (by decide))).trans oldWord
  have nh : (C.pub 2).val = newHead :=
    (congrArg Fin.val (keep 4 (by decide) (by decide))).trans newWord
  have site : (C.pub 0).val = (O v).val :=
    (congrArg Fin.val (keep 7 (by decide) (by decide))).trans siteWord
  have pw : (C.pub 1).val = parent :=
    (congrArg Fin.val (keep 0 (by decide) (by decide))).trans parentWord
  have args := TraversalHeaders.describes (shape B t stride) X v S.graph.toSlotGraph S.port_order hd
    supply A U V C
    header oh nh site pw row lanes
  have heads := TraversalGeometry.heads_eval hist A.start histBase C.pub C.state m histEq
    args.childRep.arena
  exact ⟨out, pre, ep, priv, pers, frame, args, heads.2, heads.1⟩

end Entry
end CompressorRecords.PortRefresh.TraversalPlan

end VPVNP
end Computability
end OAI
