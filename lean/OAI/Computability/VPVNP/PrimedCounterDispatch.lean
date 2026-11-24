import OAI.Computability.VPVNP.PrimedCounterDispatchRun
import OAI.Computability.VPVNP.PrimedCounterDispatchSite

/-!
# The common dispatch on every item of a primed pair

An absolute cursor selects one assembly, clear, initialization, node, or
comparison routine. The prefix installs the required local operands and the
call successor and total. Every selected routine preserves the latter two
registers until the machine's exit instruction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Dispatch

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM Program
open scoped Fin.CommRing

variable {w A S m nodes T : ℕ} {pub : Pub → Word w} {state : Word w}
  {rs : Regs w 52}

/-- Routine selected by an absolute schedule item. -/
def branch : Cursor.Item A S m nodes T → Program.Code
  | .inl _ => Program.input
  | .inr (.inl (_,i)) => siteBranch i
  | .inr (.inr _) => Program.compare

/-- Register file at the entry of the selected routine. -/
def prepared (rs : Regs w 52) (i : Cursor.Item A S m nodes T) : Regs w 52 :=
  let v := (Cursor.index A S m nodes T i).val
  let U := Cursor.calls A S m nodes T
  let start := Cursor.compareStart A S m nodes
  match i with
  | .inl _ => controlRegs rs v A U
  | .inr (.inl (u,j)) => siteRegs (laterRegs rs v A U start) u j
  | .inr (.inr j) => compareRegs rs v A U start j.val

/-- Exact number of ticks before entry to the selected routine. -/
def overhead : Cursor.Item A S m nodes T → ℕ
  | .inl _ => 6
  | .inr (.inl (_,j)) => 8 + siteTicks j
  | .inr (.inr _) => 9

theorem overhead_le (i : Cursor.Item A S m nodes T) : overhead i ≤ 16 := by
  rcases i with j | ⟨u,j | j | j⟩ | j <;> norm_num [overhead, siteTicks]

/-- The prefix passes the decoded operands to the selected branch, with no
choice bits or external probes consumed before that branch starts. -/
theorem body_pref (hw : ScheduleWords pub A S m nodes T) (hfit : Cursor.calls A S m nodes T < 2^w)
    (i : Cursor.Item A S m nodes T) :
    Pref pub (itemState w i) body rs (branch i) (prepared rs i) (overhead i) := by
  rcases i with j | ⟨u,j⟩ | j
  · exact input_pref hw hfit j
  · apply (row_pref (rs := rs) hw hfit u j).trans
    apply site_pref u j hfit _ _ hw.span hw.marks <;>
      simp (config := { decide := true }) [laterRegs, controlRegs, Function.update]
  · exact compare_pref hw hfit j

/-- The final comparison uses the next absolute cursor and the full call count. -/
theorem prepared_controls (rs : Regs w 52) (i : Cursor.Item A S m nodes T) :
    prepared rs i 49 = (((Cursor.index A S m nodes T i).val + 1 : ℕ) : Word w) ∧
    prepared rs i 50 = (Cursor.calls A S m nodes T : Word w) := by
  rcases i with j | ⟨u,j⟩ | j <;>
    simp (config := { decide := true }) [prepared, compareRegs, laterRegs, controlRegs, Function.update]

@[simp] theorem prepared_clear_index (rs : Regs w 52) (u : Fin S) (j : Fin m) :
    prepared rs (.inr (.inl (u,.inl j)) : Cursor.Item A S m nodes T) (parserReg 2) = (j.val : Word w) :=
  siteRegs_clear_index ..

@[simp] theorem prepared_node_offset (rs : Regs w 52) (u : Fin S) (j : Fin nodes) :
    prepared rs (.inr (.inl (u,.inr (.inr j))) : Cursor.Item A S m nodes T) (parserReg 5) =
      ((u.val * m : ℕ) : Word w) :=
  siteRegs_node_offset ..

@[simp] theorem prepared_compare_index (rs : Regs w 52) (j : Fin T) :
    prepared rs (.inr (.inr j) : Cursor.Item A S m nodes T) (parserReg 7) = (j.val : Word w) := by
  simp [prepared, compareRegs, parserReg]

/-- Input dispatch leaves every assembly register at its incoming value. -/
theorem prepared_input (rs : Regs w 52) (j : Fin A) :
    prepared rs (.inl j : Cursor.Item A S m nodes T) ∘ inputRegs = rs ∘ inputRegs :=
  control_input ..

/-- Executing any selected routine leaves the two exit registers alone. -/
theorem branch_controls (i : Cursor.Item A S m nodes T) {mem mem' : Memory w}
    {es : List (Event w)} {out : Regs w 52}
    (he : Flow.Exec pub state (branch i) rs mem es out mem') : out 49 = rs 49 ∧ out 50 = rs 50 := by
  have frame {r p : ℕ} (reg : Fin r ↪ Reg) (port : Fin p → Pub) (a : Flow r p)
      (hs : Flow.Exec pub state (renameFlow reg port a) rs mem es out mem')
      (h : (49 : Reg) ∉ Set.range reg ∧ (50 : Reg) ∉ Set.range reg) : out 49 = rs 49 ∧ out 50 = rs 50 := by
    have hf := (restrictExec reg port pub a hs).2
    exact ⟨hf 49 h.1, hf 50 h.2⟩
  rcases i with j | ⟨u,j⟩ | j
  · exact frame inputRegs inputPub (Opcodes.dataCall PortCode.program) he input_outside
  · rcases j with j | j | j
    · exact frame parserRegs parserPub Admin.clear he parser_outside
    · exact frame parserRegs parserPub Admin.init he parser_outside
    · exact frame parserRegs stackPub nodeFlow he parser_outside
  · exact frame parserRegs parserPub Admin.compare he parser_outside

end PrimedCounter.Dispatch

end VPVNP
end Computability
end OAI
