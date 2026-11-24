import OAI.Computability.VPVNP.PairRefreshTraversalMapBody
import OAI.Computability.VPVNP.CompressorRefreshTraversalRecipeReads

/-!
# Configuration-independent operands of the refresh traversal

The parent descriptor, promoted-site ordinal and level heads survive the child scan.
Reloading the histogram fixes both remaining temporary words. Thus the complete
external event sequence of the diagonal and selected map is evaluated on the same
operand bank for every initial configuration in the packet domain.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalPlan

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe PairSimulation VertexImage NodeArguments NewSlots RefreshMapOperands NetworkKernel
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {t hist : ℕ}
  (ties : Fin t ≃ Tie (2 ^ S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)

local notation "T" => plan B ties stride order

/-- Public words for the live refresh body, including the site, parent node, new-level header,
histogram-pointer cell, and histogram base. -/
def operands {bits : ℕ} (site parent newHead histBase : ℕ) (G : W bits) : Fin 5 → W bits :=
  ![word site, word parent, word newHead, G + 11, word histBase]

variable {pcs regs bits g : ℕ} (loc : Fin (body B ties stride order).count → Fin pcs)
  (dfs : Fin 9 ↪ Fin regs) (saved : Saved ↪ Fin regs)
  (bank : Fin (body B ties stride order).privateRegs ↪ Fin regs) (done : Fin pcs)
  (M : Machine bits pcs regs 11)
local notation "left" =>
  Segment.leftPC TraversalGeometry.reload (RefreshResidentImage.Plan.segment T) loc
local notation "right" =>
  Segment.rightPC TraversalGeometry.reload (RefreshResidentImage.Plan.segment T) loc
local notation "commonBank" => Function.Embedding.trans (locatorBank B ties stride order) bank

private theorem word_val {w : ℕ} {x : W w} {n : ℕ} (h : x.val = n) : x = word n :=
  Fin.ext (h.trans (Nat.mod_eq_of_lt (h ▸ x.isLt)).symm)

/-- The four native instructions establish the canonical five public words and state. -/
theorem enter_canonical
    (rows : ∀ j, M.code (loc j) =
      ((body B ties stride order).row loc dfs saved bank done j).resize bits)
    (c : Config bits pcs regs) (entry : c.pc = left TraversalGeometry.reload.entry)
    {site parent oldHead newHead histBase endAddr : ℕ} {G offset : W bits}
    (endWord : c.reg (dfs 6) = (endAddr : W bits))
    (resident : ResidentGeometry (DFS.scratch endAddr c.privateMem) G offset (word histBase))
    (oldWord : (c.reg (commonBank 11)).val = oldHead)
    (newWord : (c.reg (commonBank 4)).val = newHead)
    (siteWord : (c.reg (commonBank 7)).val = site)
    (parentWord : (c.reg (commonBank 0)).val = parent) :
    ∃ mid, PrimedCounter.GuessWord.Prefix M c (List.replicate 4 .tick) mid ∧
      mid.pc = (T).diagSetup (right ∘ (T).locations) 0 ∧
      mid.privateMem = c.privateMem ∧ mid.persistent = c.persistent ∧
      (∀ j, j ≠ commonBank 9 → j ≠ commonBank 10 → mid.reg j = c.reg j) ∧
      (fun i : Fin 5 => mid.reg ((T).inputs dfs saved commonBank i.castSucc)) =
        operands site parent newHead histBase G ∧
      mid.reg ((T).inputs dfs saved commonBank (Fin.last 5)) = word oldHead := by
  have linked := (body_links B ties stride order loc dfs saved bank done M rows).1
  obtain ⟨mid, pre, ep, histogram, cell, frame, priv, per⟩ :=
    TraversalGeometry.reload_native_address M left dfs saved
    commonBank (right (T).segment.entry) linked c entry endWord resident
  have keep (i : Fin 14) (ha : i ≠ 9)
    (hb : i ≠ 10) : mid.reg (commonBank i) = c.reg (commonBank i) :=
    frame _ ((commonBank).injective.ne ha) ((commonBank).injective.ne hb)
  refine ⟨mid, pre, ?_, priv, per, frame, ?_, (keep 11 (by decide)
    (by decide)).trans (word_val oldWord)⟩
  · rw [ep]
    change right ((T).diagSetup (T).locations 0) = (T).diagSetup (right ∘ (T).locations) 0
    by_cases h : 0 < (RegisterSetup.lines (T).diagonal).length
    · refine (congrArg right (dite_eq_left h)).trans ?_
      rw [RefreshResidentImage.Plan.diagSetup, dite_eq_left h]; rfl
    · refine (congrArg right (dite_eq_right h)).trans ?_
      rw [RefreshResidentImage.Plan.diagSetup, dite_eq_right h]; rfl
  · funext i; fin_cases i
    · exact (keep 7 (by decide) (by decide)).trans (word_val siteWord)
    · exact (keep 0 (by decide) (by decide)).trans (word_val parentWord)
    · exact (keep 4 (by decide) (by decide)).trans (word_val newWord)
    · exact cell
    · exact histogram

variable (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2 ^ S.portExponent)) (A : Arena) (U V : IncidenceDirectory bits)
  (m : Memory bits)
  (start parent child listHead oldHead newHead histBase : ℕ) (G : W bits)
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "hd" => And.right S.degree_bounds
local notation "supply" =>
  blockSupplyWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) S.graph
    (Nat.two_pow_pos _) hc B.refresh choice
local notation "Y" =>
  dyadicRefreshNext X S.graph (Nat.two_pow_pos _) hc B.refresh S.port_order hd choice
local notation "O" => sites (D := 2 ^ S.portExponent) X.baseIndex (bitWordFinEquiv g)
local notation "Pl" =>
  Allocation.plan X (S.degreeExponent 0) (2 ^ S.expanderExponent) t stride start
local notation "pub" => operands (Fin.val (O v)) parent newHead histBase G
local notation "state" => word (bits := bits) oldHead

/-- Typed data for the selected local role on its canonical operand bank. -/
theorem canonical_data {fit :
    Fintype.card X.Base * 2 ^ S.portExponent * 2 ^ g * 2 ^ S.portExponent ≤ 2 ^ bits}
    (header : TraversalHeaders.Geometry (Fintype.card X.Base) g oldHead newHead start A U V m)
    (row : DFS.Row m parent listHead [word child]) (lanes : 2 ^ g < 2 ^ bits) :
    OperandInputs.Describes (T).input pub state m X v S.graph.toSlotGraph S.port_order hd supply A
      child parent U V
      ((Pl).scratch bits) (word (Pl).demand) (word (Pl).term) ∧
      (T).directory.eval pub state m = word (histBase + hist + 12 + 2 * A.start) ∧
      (T).histogram.eval pub state m = word histBase := by
  let C : LevelRecipe.Context bits := ⟨pub, state, m⟩
  have siteRoom := (Nat.le_mul_of_pos_right (Fintype.card X.Base * 2 ^ S.portExponent * 2 ^ g)
    (Nat.two_pow_pos S.portExponent)).trans fit
  have oldFit : C.state.val = oldHead := Nat.mod_eq_of_lt (by have := header.oldRoom; omega)
  have newFit : (C.pub 2).val = newHead := Nat.mod_eq_of_lt (by have := header.newRoom; omega)
  have siteFit : (C.pub 0).val = (O v).val := Nat.mod_eq_of_lt ((O v).isLt.trans_le siteRoom)
  have parentFit : (C.pub 1).val = parent := Nat.mod_eq_of_lt (by have := row.1; omega)
  have args := TraversalHeaders.describes (shape B t stride) X v S.graph.toSlotGraph S.port_order hd
    supply A U V C
    header oldFit newFit siteFit parentFit row lanes
  have heads := TraversalGeometry.heads_eval hist A.start histBase C.pub C.state m rfl
    args.childRep.arena
  exact ⟨args, heads.2, heads.1⟩

/-- All physical expression probes of a selected refresh stay below the terminal
header if its two level regions and its placed node row do. -/
theorem canonical_reads {fit :
    Fintype.card X.Base * 2 ^ S.portExponent * 2 ^ g * 2 ^ S.portExponent ≤ 2 ^ bits}
    (header : TraversalHeaders.Geometry (Fintype.card X.Base) g oldHead newHead start A U V m)
    (row : DFS.Row m parent listHead [word child]) (lanes : 2 ^ g < 2 ^ bits)
    (old : U.ActualColumns X m) (new : V.ActualColumns Y m) (limit : ℕ) (fits : limit ≤ 2 ^ bits)
    (oldBefore : oldHead + 60 < limit) (newBefore : newHead + 59 < limit)
    (parentBefore : parent < limit)
    (listBefore : listHead < limit) (area : (Pl).supply ≤ limit)
    (oldIn : U.actualIn.val + Fintype.card X.Base * 2 ^ (S.portExponent + g) * 2 ^ S.portExponent ≤
      limit)
    (oldWidth : U.width.val + Fintype.card X.Base * 2 ^ (S.portExponent + g) * 2 ^ S.portExponent ≤
      limit)
    (newIn : V.actualIn.val + Fintype.card (State.Base Y) * 2 ^ g * 2 ^ (S.degreeExponent 0) ≤
      limit)
    (newWidth : V.width.val + Fintype.card (State.Base Y) * 2 ^ g * 2 ^ (S.degreeExponent 0) ≤
      limit)
    (wide : 2 ^ S.portExponent < 2 ^ bits)
    (enough : 2 + 2 ^ S.portExponent * 2 ^ S.expanderExponent ≤ stride) :
    let ok := Expr.ReadsFrom (· < limit) pub state m
    (∀ i, ok ((T).diagonal i)) ∧ (∀ i, ok ((T).route i)) ∧ ok (T).directory ∧
      ∀ idx j, ok ((T).family.fields idx j) := by
  intro ok
  have oldFit : (state).val = oldHead := Nat.mod_eq_of_lt (by omega)
  have newFit : (pub 2).val = newHead := Nat.mod_eq_of_lt (by omega)
  have parentFit : (pub 1).val = parent := Nat.mod_eq_of_lt (parentBefore.trans_le fits)
  have heads := TraversalHeaders.input_reads pub state m limit (shape B t stride) oldFit newFit
    parentFit row
    oldBefore newBefore parentBefore listBefore
  have dir : ok (T).directory := ⟨⟨⟨trivial, trivial⟩, trivial⟩, trivial, heads.child.arena⟩
  have args := (canonical_data B ties stride order X choice v A U V m start parent child listHead
    oldHead newHead histBase G
    (fit := fit) header row lanes).1
  obtain ⟨dia, route, field⟩ :=
    TraversalRecipeReads.fields B X choice v A child parent U V ties start stride limit pub state
      m (T).input (fit := fit) (T).directory (T).histogram args heads old new oldIn oldWidth
      newIn newWidth area fits wide enough dir trivial
  exact ⟨dia, route, dir, fun idx j => field _⟩

end CompressorRecords.PortRefresh.TraversalPlan

end VPVNP
end Computability
end OAI
