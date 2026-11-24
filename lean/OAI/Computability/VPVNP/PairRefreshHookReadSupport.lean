import OAI.Computability.VPVNP.PairRefreshHookSite
import OAI.Computability.VPVNP.PairRefreshVertexReads
import OAI.Computability.VPVNP.PairRefreshTraversalBounds
import OAI.Computability.VPVNP.PairRefreshTraversalQuiet

/-!
# External reads of an accepted refresh hook

The locator may read the terminal scalars at offsets 1, 15, 16 and 17.
All other reads precede the terminal header. The concrete old and new
incidence regions and refresh scratch allocation supply their address bounds.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook.Site

open BurstRAM Compression CompressorRecords CompressorRecords.PortRefresh NewSlots
open NodeArguments NodeArguments.ChildScan
open TraversalControllerInputs ShrinkRole.ChildArguments DescriptorSpace
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {w n hist : ℕ}
  (R : Site B n hist w) (order : B.Entry ≃ Fin hist) (pub : Fin 11 → Word w) (m : Memory w)
  (start positions blocks : ℕ)
  (prev next : Fin (BlockProgram.layout B start positions blocks).levels)
local notation "L" => BlockProgram.layout B start positions blocks
local notation "T" => RefreshBlockPlan.order B
local notation "stride" => LevelRecipe.Shape.stride (RefreshBlockPlan.shape B)
local notation "H" => TerminalLink.header pub
local notation "cells" => TerminalLink.workerCell H

private theorem header_scalar (i : ℕ) (nonzero : 0 < i) (short : i < 31)
    (fit : (H).val + 32 ≤ 2 ^ w) :
    cells (terminalHead pub + (i : Word w)).val := by
  have hw : i < 2 ^ w := by omega
  have hi : (terminalHead pub + (i : Word w)).val = (H).val + i := by
    rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt hw,
      Nat.mod_eq_of_lt (by change (H).val + i < 2 ^ w; omega)]
    rfl
  have last : (H + 31).val = (H).val + 31 := by
    rw [show (31 : Word w) = ((31 : ℕ) : Word w) from rfl, Fin.val_add, Fin.val_natCast,
      Nat.mod_eq_of_lt (by omega : 31 < 2 ^ w), Nat.mod_eq_of_lt (by omega)]
  change _ ≠ (H).val ∧ _ ≠ (H + 31).val
  rw [hi, last]; omega

/-- A successful parse only probes the allowed words of the enclosing terminal
worker. Both packed column sizes come from the selected old position count. -/
theorem read_worker_layout (facts : R.Published T stride pub m)
    (size : R.state.positions ≤ positions)
    (below : endAddress L ≤ (H).val) (fit : (H).val + 32 ≤ 2 ^ w)
    (oldHead : (levelHead pub m R.level).val = levelStart L prev)
    (newHead : (levelHead pub m (R.level + 1)).val = levelStart L next)
    (scratch : R.start = arrayBase L prev)
    (oldCols : R.prev = packedIncidence L w prev (R.state.positions * 2 ^ S.portExponent))
    (newCols : R.next = packedIncidence L w next (R.nextState.positions * 2 ^ (S.degreeExponent 0)))
    (levelReads : ∀ i, R.level + 1 ≤ i → i ≤ R.level + 1 + R.later →
      (levelHead pub m i + 14).val < (H).val)
    (parentBefore : R.parent + 1 < (H).val) (rowBefore : R.listHead < (H).val)
    {node : Word w} {s : DFS.Scratch w n} {bs out tail}
    (atNode : node.val = R.parent)
    (hit : R.read T stride order pub m node s bs = some (out, tail)) :
    SourceTransport.Reads cells out.trace := by
  obtain ⟨_, _, es, actionEq, path⟩ := (RefreshHook.read_some_iff R.state R.olderSite R.nextState
    R.newerSite R.arena R.oldNode R.parent (R.front pub m) (R.action T stride order pub m)
    node s bs out tail).mp hit
  have limits := TraversalPlan.layout_limits (bits := w) B R.state R.choice start positions blocks
    prev next size (below.trans_lt (H).isLt) below
  obtain ⟨oldBefore, _, _, beforeCols, _, _⟩ := limits
  have col : ColumnsBelow R.prev R.state (H).val := by
    rw [oldCols]
    exact ⟨beforeCols 4, beforeCols 5⟩
  have baseBound : (levelHead pub m R.level + 14).val + 6 < (H).val := by
    rw [Fin.val_add, oldHead]
    have h14 : (14 : Word w).val = 14 := Nat.mod_eq_of_lt (by change 14 < 2 ^ w; omega)
    rw [h14, Nat.mod_eq_of_lt (by have := (H).isLt; omega)]; omega
  have child := worker_reads_of_below H fit (trace_reads_below facts.oldCols col node
    (levelHead pub m R.level + 14) R.listHead [Child.ofHalf R.state R.olderSite out.value.1]
    (atNode ▸ parentBefore) baseBound rowBefore)
  have locate : SourceTransport.Reads cells (VertexLevel.trace pub m (R.level + 1) R.later) :=
    VertexLevel.trace_reads _ _ (fun i hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl <;>
        exact header_scalar pub _ (by decide) (by decide) fit)
      (fun i lo hi => TerminalLink.workerCell_of_lt (by omega) (levelReads i lo hi))
  have bodyReads := TraversalPlan.layout_worker_reads B R.state R.choice start positions blocks
    prev next order R.port m R.parent R.oldNode R.listHead R.geometry R.degree n R.rowEnd R.room
    out.value.1 out.value.2 H (by omega) size below
    (oldHead ▸ newHead ▸ scratch ▸ oldCols ▸ newCols ▸ facts.headers) facts.children (by omega)
    rowBefore (oldCols ▸ facts.oldCols) (newCols ▸ facts.newCols)
  have eventEq := TraversalPlan.canonicalAction_events B T stride order R.state R.choice R.port
    R.degree n R.rowEnd R.oldNode R.parent R.room out.value.1 out.value.2 m
    (levelHead pub m R.level).val (levelHead pub m (R.level + 1)).val R.geometry actionEq
  rw [oldHead, newHead] at eventEq
  intro q v has
  rw [path] at has
  rcases List.mem_append.mp has with front | body
  · rcases List.mem_append.mp front with start | next
    · exact locate q v start
    · rcases List.mem_append.mp next with tick | next
      · cases List.eq_of_mem_replicate tick
      · rcases List.mem_append.mp next with tick | actual
        · cases List.eq_of_mem_replicate tick
        · exact child q v actual
  · exact bodyReads q v (eventEq ▸ body)

end PairSimulation.RefreshHook.Site

end VPVNP
end Computability
end OAI
