import OAI.Computability.VPVNP.PairVertexControl
import OAI.Computability.VPVNP.PairVertexSegmentChain
import OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
import OAI.Computability.VPVNP.PairTerminalLayout

/-!
# Refresh map workspace at the actual DFS call boundary

The role reloads the histogram base from private geometry after the child scan. Four
instructions use two dead locator temporaries and preserve the popped node, site ordinal,
current and old level heads. Its map directory is beyond the argument frames, histogram
and twelve immutable geometry cells. All staging finishes below the persistent scalar
cache for sufficiently large input size.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalGeometry

open BurstRAM BurstRAM.PrivateRAM PairSimulation VertexImage PrimedCounter.GuessWord PhaseRecipe
open scoped Fin.CommRing
open private resident_read from OAI.Computability.VPVNP.PairVertexControl

variable {w p r : ℕ}

/-- The two temporaries belong to the fourteen-word level locator. -/
def reload : VertexImage.Segment where
  count := 4
  privateRegs := 14
  entry := 0
  row loc dfs _saved common done := ![
    .loadPrivate (common 9) (dfs 6) (loc 1),
    .constant (common 10) 11 (loc 2),
    .binary .add (common 9) (common 9) (common 10) (loc 3),
    .loadPrivate (common 10) (common 9) done]

/-- Select the six locator registers that supply the refresh computation's five public operands
and its state word. -/
def source : Fin 6 → (Fin 9 ⊕ VertexImage.Saved ⊕ Fin 14) := ![
  .inr (.inr 7), .inr (.inr 0), .inr (.inr 4), .inr (.inr 9), .inr (.inr 10), .inr (.inr 11)]

/-- The freshly reloaded private histogram address, passed as public recipe operand four. -/
def histogram : Expr := .publicWord 4

/-- Compute the map directory above the histogram, its counters, twelve geometry cells, and two
live-size buffers. -/
def directory (histCount : ℕ) : Expr := ((histogram.add (.lit histCount)).add (.lit 12)).add
  ((Expr.lit 2).mul (.header 17))

/-- Actual terminal private memory supplies the histogram. No initial value of its saved
bootstrap register enters this execution. -/
theorem reload_native_address (M : Machine w p r 11) (loc : Fin 4 → Fin p) (dfs : Fin 9 ↪ Fin r)
    (saved : VertexImage.Saved ↪ Fin r) (common : Fin 14 ↪ Fin r) (done : Fin p)
    (linked : ∀ i, M.code (loc i) = (reload.row loc dfs saved common done i).resize w)
    (c : Config w p r) (entry : c.pc = loc 0) {endAddr : ℕ} {G offset hist : Word w}
    (endWord : c.reg (dfs 6) = (endAddr : Word w))
    (resident : ResidentGeometry (DFS.scratch endAddr c.privateMem) G offset hist) :
    ∃ d, Prefix M c (List.replicate 4 .tick) d ∧ d.pc = done ∧ d.reg (common 10) = hist ∧
      d.reg (common 9) = G + 11 ∧
      (∀ j, j ≠ common 9 → j ≠ common 10 → d.reg j = c.reg j) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  have rows (i : Fin 3) : M.code (loc (i.castAdd 1)) =
      geometryRows (fun j => loc (j.castAdd 1)) (dfs 6) (common 9) (common 10)
      (11 : Word w) (loc 3) i := by
    rw [linked]; fin_cases i <;> rfl
  obtain ⟨mid, pre, pc, ptr, frame, mem, pers⟩ :=
    geometry_run rows (common.injective.ne (by decide)) c entry
  obtain ⟨hg, _, hh⟩ := resident_read _ _ _ _ resident
  let d := mid.put done (common 10) (mid.privateMem (mid.reg (common 9)))
  have step : M.program.step mid = .localStep d := by
    change (M.code mid.pc).run M.publicData mid = _
    rw [pc, linked]; rfl
  have tail : Prefix M mid [.tick] d := .tick step (.nil _)
  refine ⟨d, pre.append tail, rfl, ?_, ?_, fun j h₉ h₁₀ =>
    (Function.update_of_ne h₁₀ ..).trans (frame _ h₉ h₁₀), mem, pers⟩
  · rw [show d.reg (common 10) = _ from Config.put_same .., ptr, endWord, hg, mem, hh]
  · have keep : d.reg (common 9) = mid.reg (common 9) :=
      Function.update_of_ne (common.injective.ne (by decide : (9 : Fin 14) ≠ 10)) ..
    rw [keep, ptr, endWord, hg]

theorem reload_native (M : Machine w p r 11) (loc : Fin 4 → Fin p) (dfs : Fin 9 ↪ Fin r)
    (saved : VertexImage.Saved ↪ Fin r) (common : Fin 14 ↪ Fin r) (done : Fin p)
    (linked : ∀ i, M.code (loc i) = (reload.row loc dfs saved common done i).resize w)
    (c : Config w p r) (entry : c.pc = loc 0) {endAddr : ℕ} {G offset hist : Word w}
    (endWord : c.reg (dfs 6) = (endAddr : Word w))
    (resident : ResidentGeometry (DFS.scratch endAddr c.privateMem) G offset hist) :
    ∃ d, Prefix M c (List.replicate 4 .tick) d ∧ d.pc = done ∧ d.reg (common 10) = hist ∧
      (∀ j, j ≠ common 9 → j ≠ common 10 → d.reg j = c.reg j) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  obtain ⟨out, pre, pc, histogram, _, frame, mem, per⟩ :=
    reload_native_address M loc dfs saved common done linked c entry endWord resident
  exact ⟨out, pre, pc, histogram, frame, mem, per⟩

/-- Computing the private directory and histogram requires only the freshly loaded
histogram base and the old level's published argument-arena start, which equals `n`. -/
theorem heads_eval (histCount n hist : ℕ) (pub : Fin 5 → Word w) (state : Word w) (m : Memory w)
    (hh : pub 4 = (hist : Word w)) (hn : (Expr.header 17).eval pub state m = (n : Word w)) :
    histogram.eval pub state m = (hist : Word w) ∧
      (directory histCount).eval pub state m = ((hist + histCount + 12 + 2 * n : ℕ) : Word w) := by
  refine ⟨hh, ?_⟩
  change pub 4 + (histCount : Word w) + 12 + 2 * (Expr.header 17).eval pub state m = _
  rw [hh, hn]; push_cast; rfl

/-- The node's private argument frame precedes the common histogram. -/
theorem argument_end {a g : ℕ} (degree n nodes labels : ℕ) (X : Compression.State a g)
    (v : X.network.Site) (h : X.network.Half v) (node : ℕ) (hn : node < nodes)
    (degreeBound : 2 ^ a ≤ degree) (widthBound : X.maxWireWidth ≤ n) :
    let R := TerminalLayout.privateRegions degree n nodes labels
    R.arguments.base node + (NodeArguments.packed X v h).length ≤ R.histBase := by
  let R := TerminalLayout.privateRegions degree n nodes labels
  apply (Nat.add_le_add_left _ _).trans (R.node_before hn)
  have a := NodeArguments.packed_length_le X v h
  have b := Nat.mul_le_mul (Nat.mul_le_mul_left 2 degreeBound) widthBound
  change (NodeArguments.packed X v h).length ≤ 2 * degree * n + 1
  omega

/-- The private space reserved between histogram and scalar cache covers both the
raw descriptor and all map copies. Its lower bound includes the immutable geometry. -/
theorem workspace_before_cache (degree n nodes labels headCapacity copies : ℕ)
    (large : headCapacity + 12 ≤ n) (five : 5 ≤ n) (copyBound : copies ≤ n) :
    let R := TerminalLayout.privateRegions degree n nodes labels
    let start := R.histBase + labels + 12 + 2 * n
    R.histBase + R.histWords + 12 ≤ start ∧ start + headCapacity + 2 * copies ≤ R.cacheBase := by
  have square : 5 * n ≤ n ^ 2 := (Nat.mul_le_mul_right n five).trans_eq (pow_two n).symm
  have power : n ^ 2 ≤ n ^ 5 := Nat.pow_le_pow_right (by omega) (by decide)
  dsimp only [TerminalLayout.privateRegions, LeafArena.Regions.cacheBase]
  constructor <;> omega

end CompressorRecords.PortRefresh.TraversalGeometry

end VPVNP
end Computability
end OAI
