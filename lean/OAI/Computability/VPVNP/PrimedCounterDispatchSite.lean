import OAI.Computability.VPVNP.PrimedCounterDispatchPrefix

/-!
# Dispatch within a site of the primed pair counter

Dividing the cursor offset by the span of a site gives the row and its local
cursor. The two comparisons then select a mark clear, root initialization,
or node visit. This calculation and the preparation of the parser operands
consume only ticks and preserve the two registers used to finish the call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Dispatch

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM
open scoped Fin.CommRing

variable {w A S m nodes T : ℕ} {pub : Program.Pub → Word w} {state : Word w}
  {rs : Regs w 52}

/-- Selected parser routine for each position of a site. -/
def siteBranch : Cursor.LocalItem m nodes → Program.Code
  | .inl _ => Program.clear
  | .inr (.inl _) => Program.init
  | .inr (.inr _) => Program.node

/-- Five row instructions, one or two comparisons, and any operand preparation. -/
def siteTicks : Cursor.LocalItem m nodes → ℕ
  | .inl _ | .inr (.inl _) => 7
  | .inr (.inr _) => 8

private def rowRegs (rs : Regs w 52) (u : Fin S) (i : Cursor.LocalItem m nodes) : Regs w 52 :=
  let span := Cursor.span m nodes
  let localPos := (Cursor.localIndex m nodes i).val
  let rs := Function.update rs 18 ((u.val * span + localPos : ℕ) : Word w)
  let rs := Function.update rs 19 (span : Word w)
  let rs := Function.update rs 20 (u.val : Word w)
  let rs := Function.update rs 21 (localPos : Word w)
  Function.update rs 22 (m : Word w)

/-- The branch sees the clear index in register 2 or the row offset in register 5. -/
def siteRegs (rs : Regs w 52) (u : Fin S) (i : Cursor.LocalItem m nodes) : Regs w 52 :=
  let mid := rowRegs rs u i
  match i with
  | .inl j => Function.update mid 2 (j.val : Word w)
  | .inr (.inl _) => mid
  | .inr (.inr _) => Function.update mid 5 ((u.val * m : ℕ) : Word w)

@[simp] theorem siteRegs_clear_index (rs : Regs w 52) (u : Fin S) (j : Fin m) :
    siteRegs (nodes := nodes) rs u (.inl j) (Program.parserReg 2) = (j.val : Word w) := by
  simp (config := { decide := true }) [siteRegs, Program.parserReg]

@[simp] theorem siteRegs_node_offset (rs : Regs w 52) (u : Fin S) (j : Fin nodes) :
    siteRegs (m := m) rs u (.inr (.inr j)) (Program.parserReg 5) = ((u.val * m : ℕ) : Word w) := by
  simp (config := { decide := true }) [siteRegs, Program.parserReg]

@[simp] theorem siteRegs_next (rs : Regs w 52) (u : Fin S) (i : Cursor.LocalItem m nodes) :
    siteRegs rs u i 49 = rs 49 := by
  rcases i with j | j | j <;> simp (config := { decide := true }) [siteRegs, rowRegs, Function.update]

@[simp] theorem siteRegs_total (rs : Regs w 52) (u : Fin S) (i : Cursor.LocalItem m nodes) :
    siteRegs rs u i 50 = rs 50 := by
  rcases i with j | j | j <;> simp (config := { decide := true }) [siteRegs, rowRegs, Function.update]

private theorem row_operand (u : Fin S) (i : Cursor.LocalItem m nodes) :
    rowRegs rs u i 20 = (u.val : Word w) ∧
    rowRegs rs u i 21 = ((Cursor.localIndex m nodes i).val : Word w) ∧
    rowRegs rs u i 22 = (m : Word w) := by
  simp (config := { decide := true }) [rowRegs, Function.update]

private theorem span_fit (u : Fin S) (hfit : Cursor.calls A S m nodes T < 2^w) :
    Cursor.span m nodes < 2^w := by
  have hS : 0 < S := u.pos
  have hmul := Nat.le_mul_of_pos_left (Cursor.span m nodes) hS
  unfold Cursor.calls at hfit
  omega

private theorem row_trace (u : Fin S) (i : Cursor.LocalItem m nodes)
    (hfit : Cursor.calls A S m nodes T < 2^w)
    (h48 : rs 48 = ((Cursor.index A S m nodes T (.inr (.inl (u,i)))).val : Word w))
    (h51 : rs 51 = (A : Word w)) (h31 : pub 31 = (Cursor.span m nodes : Word w))
    (hm : pub (Program.stackPub 6) = (m : Word w)) (mem : Memory w) :
    trace pub state Program.rowSetup rs mem = some (List.replicate 5 .tick, rowRegs rs u i, mem) := by
  let span := Cursor.span m nodes
  let pos := (Cursor.localIndex m nodes i).val
  have hpos : pos < span := (Cursor.localIndex m nodes i).isLt
  have hs : 0 < span := by dsimp [span, Cursor.span]; omega
  have hspan : (span : Word w).val = span := (Fin.val_natCast ..).trans (Nat.mod_eq_of_lt (span_fit u hfit))
  have hix := (Cursor.index A S m nodes T (.inr (.inl (u,i)))).isLt.trans hfit
  rw [Cursor.index_site] at hix h48
  have hoff : ((u.val * span + pos : ℕ) : Word w).val = u.val * span + pos :=
    (Fin.val_natCast ..).trans (Nat.mod_eq_of_lt (by change A + (u.val * span + pos) < 2^w at hix; omega))
  have hsub : rs 48 - rs 51 = ((u.val * span + pos : ℕ) : Word w) := by
    rw [h48, h51, Nat.cast_add, add_sub_cancel_left]
  have hdiv : (u.val * span + pos) / span = u.val := by
    rw [Nat.mul_comm, Nat.mul_add_div hs, Nat.div_eq_of_lt hpos, Nat.add_zero]
  have hmod : (u.val * span + pos) % span = pos := by simp [Nat.mod_eq_of_lt hpos]
  change pub 31 = (span : Word w) at h31
  have hd : BinaryOp.div.eval (BinaryOp.sub.eval (rs 48) (rs 51)) (pub 31) = (u.val : Word w) := by
    change Fin.ofNat _ ((rs 48 - rs 51).val / (pub 31).val) = _
    rw [hsub, h31, hoff, hspan, hdiv, Fin.ofNat_eq_cast]
  have hr : BinaryOp.mod.eval (BinaryOp.sub.eval (rs 48) (rs 51)) (pub 31) = (pos : Word w) := by
    change Fin.ofNat _ ((rs 48 - rs 51).val % (pub 31).val) = _
    rw [hsub, h31, hoff, hspan, hmod, Fin.ofNat_eq_cast]
  have hs' : BinaryOp.sub.eval (rs 48) (rs 51) = ((u.val * span + pos : ℕ) : Word w) := hsub
  simp (config := { decide := true }) [Program.rowSetup, trace, Op.effect, Function.update]
  rw [hd, hr, hs', h31, hm]
  rfl

/-- The local dispatch preserves and reflects successful traces, with the exact
tick count and the physical row and mark operands of the selected parser. -/
theorem site_pref (u : Fin S) (i : Cursor.LocalItem m nodes)
    (hfit : Cursor.calls A S m nodes T < 2^w)
    (h48 : rs 48 = ((Cursor.index A S m nodes T (.inr (.inl (u,i)))).val : Word w))
    (h51 : rs 51 = (A : Word w)) (h31 : pub 31 = (Cursor.span m nodes : Word w))
    (hm : pub (Program.stackPub 6) = (m : Word w)) :
    Pref pub state Program.site rs (siteBranch i) (siteRegs rs u i) (siteTicks i) := by
  let check : Program.Code := .ifLt 21 22 (.seq (.line (.copy 2 21)) Program.clear)
    (.ifEq 21 22 Program.init (.seq (.line (.binary .mul 5 20 22)) Program.node))
  have setup : Pref pub state Program.site rs check (rowRegs rs u i) 5 :=
    Pref.lines (by decide) (row_trace u i hfit h48 h51 h31 hm)
  obtain ⟨hu, hi, hm'⟩ := row_operand (rs := rs) u i
  have hspan := span_fit u hfit
  have hmlt : m < 2^w := by unfold Cursor.span at hspan; omega
  have hmv : (m : Word w).val = m := (Fin.val_natCast ..).trans (Nat.mod_eq_of_lt hmlt)
  have hpos := (Cursor.localIndex m nodes i).isLt.trans hspan
  have hiv : (rowRegs rs u i 21).val = (Cursor.localIndex m nodes i).val := by
    rw [hi, Fin.val_natCast, Nat.mod_eq_of_lt hpos]
  let row := rowRegs (m := m) (nodes := nodes) rs u
  rcases i with j | j | j
  · have hlt : row (.inl j) 21 < row (.inl j) 22 := by
      change (row (.inl j) 21).val < (row (.inl j) 22).val
      dsimp only [row]
      rw [hiv, hm', hmv, Cursor.local_clear]
      exact j.isLt
    apply setup.trans ((Pref.ifLtYes hlt).trans (Pref.line ?_))
    intro mem
    simp only [row, Op.effect, hi, Cursor.local_clear, siteRegs]
  · have he : row (.inr (.inl j)) 21 = row (.inr (.inl j)) 22 := by
      dsimp only [row]
      rw [hi, hm', Cursor.local_init]
    exact setup.trans ((Pref.ifLtNo (not_lt_of_ge he.ge)).trans (Pref.ifEqYes he))
  · have hlt : row (.inr (.inr j)) 22 < row (.inr (.inr j)) 21 := by
      change (row (.inr (.inr j)) 22).val < (row (.inr (.inr j)) 21).val
      dsimp only [row]
      rw [hiv, hm', hmv, Cursor.local_node]
      omega
    apply setup.trans ((Pref.ifLtNo hlt.not_gt).trans ((Pref.ifEqNo hlt.ne').trans (Pref.line ?_)))
    intro mem
    simp only [row, Op.effect, BinaryOp.eval, hu, hm', siteRegs, Nat.cast_mul]

end PrimedCounter.Dispatch

end VPVNP
end Computability
end OAI
