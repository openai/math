import OAI.Computability.BorderVNP.FragmentBucketLayout
import OAI.Computability.BorderVNP.FragmentBucketOrder

/-! # Native histogram and prefix-scan instructions for sparse interval rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FragmentBucket

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- The count field in the header is one word after the start field. -/
def Layout.countAddr (l : Layout) (c : ℕ) := l.pairs + (c+c) + 1

/-- The first word of a cell header holds its exclusive prefix. -/
def Layout.startAddr (l : Layout) (c : ℕ) := l.pairs + (c+c)

/-- All caller-visible register values and all memory outside the two writable arrays survive. -/
structure Layout.Preserved (l : Layout) (before z : NatState) : Prop where
  ready : l.Ready z
  root : z.reg 0 = before.reg 0
  frame : ∀ a, (a < l.pairs ∨ l.pairs+2*l.cells ≤ a) →
    (a < l.cursors ∨ l.cursors+l.cells ≤ a) → z.mem a = before.mem a

/-- Postcondition after counting and exclusive prefixing, before stable scatter. -/
structure Layout.PrefixReady (l : Layout) (tag : Fin l.rows → Fin l.cells)
    (before z : NatState) : Prop extends l.Preserved before z where
  counts : ∀ c : Fin l.cells, z.mem (l.countAddr c.val) = count tag c
  starts : ∀ c : Fin l.cells, z.mem (l.startAddr c.val) = start tag c.val
  cursors : ∀ c : Fin l.cells, z.mem (l.cursors+c.val) = start tag c.val

/-- One cell's histogram entry is zeroed before the input scan. -/
def clearStep : Code := .block [
  .constant 11 1, .constant 12 0, .binary .add 13 10 10, .binary .add 13 5 13,
  .binary .add 13 13 11, .store 13 12, .binary .add 10 10 11]

/-- Read the cell from a four-word row and increment the selected histogram word. -/
def countStep : Code := .block [
  .constant 11 1, .constant 12 4, .binary .mul 13 12 10, .binary .add 13 2 13, .load 14 13,
  .binary .add 13 14 14, .binary .add 13 5 13, .binary .add 13 13 11, .load 14 13,
  .binary .add 14 14 11, .store 13 14, .binary .add 10 10 11]

/-- Install the exclusive prefix in the header and cursor, then add this cell's count. -/
def scanStep : Code := .block [
  .constant 11 1, .binary .add 12 10 10, .binary .add 12 5 12, .binary .add 13 12 11,
  .load 13 13, .store 12 15, .binary .add 14 7 10, .store 14 15,
  .binary .add 15 15 13, .binary .add 10 10 11]

private theorem ready_fixed (l : Layout) {z : NatState} (h : l.Ready z) (c : Code)
    (pub : Arg → ℕ) (keep : c.protects 8 = true) : l.Ready (c.fixedEval pub z) := by
  obtain ⟨h2,h3,h4,h5,h6,h7⟩ := h
  exact ⟨(c.fixedEval_protected pub z keep 2 (by decide)).trans h2,
    (c.fixedEval_protected pub z keep 3 (by decide)).trans h3,
    (c.fixedEval_protected pub z keep 4 (by decide)).trans h4,
    (c.fixedEval_protected pub z keep 5 (by decide)).trans h5,
    (c.fixedEval_protected pub z keep 6 (by decide)).trans h6,
    (c.fixedEval_protected pub z keep 7 (by decide)).trans h7⟩

/-- A protected fragment whose writes stay in the two working arrays preserves the caller. -/
theorem preserved_fixed {l : Layout} {before z : NatState} (p : l.Preserved before z)
    (c : Code) (pub : Arg → ℕ) (keep : c.protects 8 = true)
    (unchanged : ∀ a, (a < l.pairs ∨ l.pairs+2*l.cells ≤ a) →
      (a < l.cursors ∨ l.cursors+l.cells ≤ a) → (c.fixedEval pub z).mem a = z.mem a) :
    l.Preserved before (c.fixedEval pub z) := by
  exact ⟨ready_fixed _ p.ready c pub keep, (c.fixedEval_protected pub z keep 0 (by decide)).trans p.root,
    fun a hp hc => (unchanged a hp hc).trans (p.frame a hp hc)⟩

/-- Clearing a cell executes within its straight-line slot bound, with exactly one memory write. -/
theorem clearStep_run {l : Layout} {w : ℕ} (fit : l.Fits w) (c : Fin l.cells)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    {before : NatState} (p : l.Preserved before (.ofWords s m)) (idx : (s 10).val = c.val) :
    BoundedRun pub mac clearStep s m clearStep.slots (fun z =>
      l.Preserved before z ∧ z.reg 10 = c.val+1 ∧
      z.mem = Function.update (readings m) (l.countAddr c.val) 0) := by
  let z := NatState.ofWords s m
  change z.reg 10 = c.val at idx
  have pair : z.reg 5 = l.pairs := p.ready.2.2.2.1
  have bounds := fit.pairEnd
  have cap := fit.cellCount
  have hi := c.isLt
  have safe : clearStep.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [clearStep, Code.block, Code.fixedSafe, Code.fixedEval,
      Code.safeReadOnly, Code.evalNat, addressOpFits, addressOp, pair, idx]
    have nz : w ≠ 0 := fun h => by have := fit.literals; simp [h] at this
    omega
  apply (clearStep.runFixed pub mac s m safe).mono le_rfl
  rintro u rfl
  have mem : (clearStep.fixedEval (readings pub) z).mem =
      Function.update z.mem (l.countAddr c.val) 0 := by
    simp (config := {decide := true}) [clearStep, Code.block, Code.fixedEval, Code.evalNat,
      addressOp, pair, idx, Layout.countAddr]
  refine ⟨preserved_fixed p _ _ (by decide) (fun a hp _ => ?_), ?_, mem⟩
  · rw [mem, Function.update_of_ne (show a ≠ l.countAddr c.val by unfold Layout.countAddr; omega)]
  · change (clearStep.fixedEval (readings pub) z).reg 10 = _
    simp (config := {decide := true}) [clearStep, Code.block, Code.fixedEval, Code.evalNat, addressOp, idx]

/-- A prefix cursor cannot exceed the total number of input records. -/
theorem prior_le_rows {n cells : ℕ} (tag : Fin n → Fin cells) (i : ℕ) (c : Fin cells) :
    prior tag i c ≤ n := by
  simpa only [prior, Crossing.Profile.prefixCount, Fintype.card_fin] using ((Crossing.Profile.positions tag c).filter (fun j => j.val < i)).card_le_univ

/-- Each input step increments its cell in place, preserving the source quadruples. -/
theorem countStep_run {l : Layout} {w : ℕ} (fit : l.Fits w) (tag : Fin l.rows → Fin l.cells)
    (i : Fin l.rows) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    {before : NatState} (p : l.Preserved before (.ofWords s m)) (idx : (s 10).val = i.val)
    (cell : readings m (l.quads+4*i.val) = (tag i).val)
    (seen : readings m (l.countAddr (tag i).val) = prior tag i.val (tag i)) :
    BoundedRun pub mac countStep s m countStep.slots (fun z =>
      l.Preserved before z ∧ z.reg 10 = i.val+1 ∧
      z.mem = Function.update (readings m) (l.countAddr (tag i).val) (prior tag i.val (tag i)+1)) := by
  let z := NatState.ofWords s m
  change z.reg 10 = i.val at idx
  have quad : z.reg 2 = l.quads := p.ready.1
  have pair : z.reg 5 = l.pairs := p.ready.2.2.2.1
  change z.mem (l.quads+4*i.val) = (tag i).val at cell
  change z.mem (l.pairs+((tag i).val+(tag i).val)+1) = _ at seen
  have bQ := fit.quadEnd
  have bP := fit.pairEnd
  have bR := fit.rowCount
  have bL := fit.literals
  have hi := i.isLt
  have hc := (tag i).isLt
  have lim := prior_le_rows tag (i.val+1) (tag i)
  rw [prior_step, ite_eq_left rfl] at lim
  have safe : countStep.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [countStep, Code.block, Code.fixedSafe, Code.fixedEval,
      Code.safeReadOnly, Code.evalNat, addressOpFits, addressOp, quad, pair, idx, cell, seen]
    have nz : w ≠ 0 := fun h => by have := fit.literals; simp [h] at this
    omega
  apply (countStep.runFixed pub mac s m safe).mono le_rfl
  rintro u rfl
  have mem : (countStep.fixedEval (readings pub) z).mem =
      Function.update z.mem (l.countAddr (tag i).val) (prior tag i.val (tag i)+1) := by
    simp (config := {decide := true}) [countStep, Code.block, Code.fixedEval, Code.evalNat,
      addressOp, quad, pair, idx, cell, seen, Layout.countAddr]
  refine ⟨preserved_fixed p _ _ (by decide) (fun a hp _ => ?_), ?_, mem⟩
  · rw [mem, Function.update_of_ne (show a ≠ l.countAddr (tag i).val by unfold Layout.countAddr; omega)]
  · change (countStep.fixedEval (readings pub) z).reg 10 = _
    simp (config := {decide := true}) [countStep, Code.block, Code.fixedEval, Code.evalNat, addressOp, idx]

/-- Every cell prefix is bounded by the total histogram. -/
theorem start_le_rows {n cells : ℕ} (tag : Fin n → Fin cells) {k : ℕ} (hk : k ≤ cells) :
    start tag k ≤ n := by
  apply le_trans (b := start tag cells) _ (le_of_eq (start_end tag))
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hk) (fun _ _ _ => Nat.zero_le _)

/-- A prefix step publishes both starting addresses and advances the accumulator. -/
theorem scanStep_run {l : Layout} {w : ℕ} (fit : l.Fits w) (tag : Fin l.rows → Fin l.cells)
    (c : Fin l.cells) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    {before : NatState} (p : l.Preserved before (.ofWords s m)) (idx : (s 10).val = c.val)
    (acc : (s 15).val = start tag c.val) (seen : readings m (l.countAddr c.val) = count tag c) :
    BoundedRun pub mac scanStep s m scanStep.slots (fun z =>
      l.Preserved before z ∧ z.reg 10 = c.val+1 ∧ z.reg 15 = start tag (c.val+1) ∧
      z.mem = Function.update (Function.update (readings m) (l.startAddr c.val) (start tag c.val))
        (l.cursors+c.val) (start tag c.val)) := by
  let z := NatState.ofWords s m
  change z.reg 10 = c.val at idx
  change z.reg 15 = start tag c.val at acc
  have pair : z.reg 5 = l.pairs := p.ready.2.2.2.1
  have curs : z.reg 7 = l.cursors := p.ready.2.2.2.2.2
  change z.mem (l.pairs+(c.val+c.val)+1) = _ at seen
  have bP := fit.pairEnd
  have bC := fit.cursorEnd
  have bN := fit.cellCount
  have bR := fit.rowCount
  have hi := c.isLt
  have sumFits := start_le_rows tag (k := c.val+1) c.isLt
  rw [start_step tag c] at sumFits
  have safe : scanStep.fixedSafe w (readings pub) z := by
    simp (config := {decide := true}) [scanStep, Code.block, Code.fixedSafe, Code.fixedEval,
      Code.safeReadOnly, Code.evalNat, addressOpFits, addressOp, pair, curs, idx, seen, acc]
    have nz : w ≠ 0 := fun h => by have := fit.literals; simp [h] at this
    omega
  apply (scanStep.runFixed pub mac s m safe).mono le_rfl
  rintro u rfl
  have mem : (scanStep.fixedEval (readings pub) z).mem =
      Function.update (Function.update z.mem (l.startAddr c.val) (start tag c.val))
        (l.cursors+c.val) (start tag c.val) := by
    simp (config := {decide := true}) [scanStep, Code.block, Code.fixedEval, Code.evalNat,
      addressOp, pair, curs, idx, acc, Layout.startAddr]
  refine ⟨preserved_fixed p _ _ (by decide) (fun a hp hcur => ?_), ?_, ?_, mem⟩
  · rw [mem, Function.update_of_ne (show a ≠ l.cursors+c.val by omega),
      Function.update_of_ne (show a ≠ l.startAddr c.val by unfold Layout.startAddr; omega)]
  · change (scanStep.fixedEval (readings pub) z).reg 10 = _
    simp (config := {decide := true}) [scanStep, Code.block, Code.fixedEval, Code.evalNat, addressOp, idx]
  · change (scanStep.fixedEval (readings pub) z).reg 15 = _
    simp (config := {decide := true}) [scanStep, Code.block, Code.fixedEval, Code.evalNat,
      addressOp, pair, idx, seen, acc, start_step tag c]

end FragmentBucket

end BorderVNP
end Computability
end OAI
