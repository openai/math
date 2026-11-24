import OAI.Computability.VPVNP.PrimedInputRAMOpcodeExecutionTable
import OAI.Computability.VPVNP.PrimedInputRAMOpcodeParameters
import OAI.Computability.VPVNP.PrimedInputRAMOpcodePaths

/-!
# The physical primed input program refines the two-pass schedule

The single finite opcode table runs at the prescribed public parameters. Its data calls
add precisely three cut-length reads to the public item's probes. The four entry tests
and all dispatch arithmetic are private. The global correspondence uses only the invariant
on the three reserved length words, so it also applies to malformed primed message data.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Opcodes

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {L : Lengths} {n r H w : ℕ}

/-- The layout's sequence of first-pass bit choices and second-pass copies, using the native
encoding of a Boolean as a word. -/
abbrev nativeOps (Q : Layout L n r H w) := (Q.twoPass (encodeBit w)).ops
/-- Instantiate the fixed two-pass opcode table at the layout's word width and public parameter
words. -/
abbrev nativeMachine (Q : Layout L n r H w) := inputTable.instantiate w (pubWord Q)

/-- Per-call instruction allowance for the native input program, equal to `3*r + 165` for an
`r`-bit site index. -/
def nativeFuel (r : ℕ) := 3*r + 165

private abbrev Position (n r : ℕ) := Fin (positions n r + positions n r)

private def withinRow {N : ℕ} (i : Fin (N+N)) : Fin N :=
  ⟨i.val % N, Nat.mod_lt _ (by have := i.isLt; omega)⟩

private def address (Q : Layout L n r H w) (i : Position n r) : Word w :=
  ⟨Q.scratchBase + i.val, (Nat.add_lt_add_left i.isLt _).trans_le (Nat.add_assoc .. ▸ Q.addressesFit)⟩

private def decision (Q : Layout L n r H w) (i : Position n r) : RawCopy × Bool :=
  (PrimedInputRAM.dispatch L n r H w Q.scratchBase (UniversalMachine.programPrefix Q.program).length
    Q.prefixAt (withinRow i).val).1

private theorem scheduled_item (Q : Layout L n r H w) (i : Position n r) :
    rawItem (decide (i.val < positions n r)) (decision Q i) (address Q i) = nativeOps Q i := by
  have hr := Q.dispatch_eq (encodeBit w) (withinRow i)
  have ho := congrArg Prod.snd hr
  have hs := congrArg Prod.fst hr
  change (decision Q i).2 = Q.owns (withinRow i) at ho
  change Layout.compileCopy (encodeBit w) (decision Q i).1 = Q.source (encodeBit w) (withinRow i) at hs
  cases i using Fin.addCases with
  | left i =>
    have he : withinRow (Fin.castAdd (positions n r) i) = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    rw [he] at ho
    simp only [nativeOps, TwoPass.ops, Fin.append_left, Fin.val_castAdd, i.isLt, decide_true,
      rawItem, ↓reduceIte, ho]
    rfl
  | right i =>
    have he : withinRow (Fin.natAdd (positions n r) i) = i := by
      apply Fin.ext
      simp [withinRow, Nat.mod_eq_of_lt i.isLt]
    rw [he] at hs
    simp only [nativeOps, TwoPass.ops, Fin.append_right, Fin.val_natAdd, Nat.not_lt_of_ge (Nat.le_add_right ..),
      decide_false, rawItem, Bool.false_eq_true, ↓reduceIte, hs, Layout.twoPass]
    apply congrArg (Item.copy _)
    apply Fin.ext
    change Q.scratchBase + (positions n r + i.val) = (Q.scratchBase + positions n r) + i.val
    omega

private theorem cutMemory_step (Q : Layout L n r H w) (i : Position n r) (m : Memory w)
    (b : Bool) (hc : CutMemory L m) : CutMemory L ((nativeOps Q i).memory (encodeBit w) m b) := by
  apply hc.congr
  intro j
  have hbase := Q.headersFit
  unfold Header.count at hbase
  have haddr : j.val ≠ (address Q i).val := by change j.val ≠ Q.scratchBase + i.val; have := j.isLt; omega
  rw [← scheduled_item]
  unfold rawItem
  split <;> (try split) <;> simp [Item.memory, writeMemory, haddr]

private theorem publicTerminal (Q : Layout L n r H w) (F : ParameterFit Q) :
    ((pubWord Q 0) + (pubWord Q 0)).val = positions n r + positions n r := by
  have hn := pubWord_cells Q F
  rw [Fin.val_add_eq_of_add_lt (by rw [hn]; exact Q.cursorFits), hn]

/-- Execute the input body from arbitrary private registers. This allows the combined
counter to enter it from its own phase dispatch without changing any public item. -/
theorem native_body (Q : Layout L n r H w) (F : ParameterFit Q) (i : Position n r)
    (m : Memory w) (hc : CutMemory L m) (regs : Regs w 48) :
    let state := cursor Q.cursorFits i.val i.isLt.le
    ∃ cost ≤ 3*r+128, ∀ b, ∃ final, Flow.Exec (pubWord Q) state body regs m
      (dataEvents m cost (nativeOps Q i) b) final ((nativeOps Q i).memory (encodeBit w) m b) ∧
      final 29 = successor Q.cursorFits i := by
  let st := cursor Q.cursorFits i.val i.isLt.le
  obtain ⟨pre,hpre,hI⟩ := load_unpack_exec Q F st m regs i.isLt hc
  have hphase : pre 4 < pre 5 ↔ decide (i.val < positions n r) = true := by
    rw [Fin.lt_def, hI.stateReg, hI.cells, decide_eq_true_iff]
    rfl
  have hdest : pre 30 = address Q i := Fin.ext hI.cursor.dest
  have hnext : pre 29 = successor Q.cursorFits i := Fin.ext hI.cursor.next
  have hw : 0 < w := by
    have hh := Q.headersFit
    have ha := Q.addressesFit
    unfold Header.count at hh
    by_contra! he
    obtain rfl : w = 0 := by omega
    simp at ha
    omega
  obtain ⟨cost, hcost, runs⟩ := dataCall_exec (pubWord Q) st _ pre m _ _ _ hw hpre hI.dispatch hphase hdest hnext
  change ∀ b, ∃ final, Flow.Exec _ _ body _ m
    (dataEvents m cost (rawItem _ (decision Q i) _) b) final ((rawItem _ (decision Q i) _).memory _ m b) ∧ _ at runs
  rw [scheduled_item] at runs
  exact ⟨cost, hcost, runs⟩

/-- Each valid data call has its native event list, with one common private dispatch
cost for both possible values of the selected bit. -/
theorem native_data (Q : Layout L n r H w) (F : ParameterFit Q) (i : Position n r)
    (m : Memory w) (hc : CutMemory L m) :
    let state := cursor Q.cursorFits i.val i.isLt.le
    ∃ cost ≤ 3*r+128, ∀ b,
      execute (nativeMachine Q).program (nativeFuel r) ((nativeMachine Q).program.start state) m
          ((nativeOps Q i).bits b) =
        some ⟨prefixEvents w ++ dataEvents m cost (nativeOps Q i) b, some (successor Q.cursorFits i)⟩ := by
  let st := cursor Q.cursorFits i.val i.isLt.le
  obtain ⟨cost, hcost, runs⟩ := native_body Q F i m hc (prefixRegs st (pubWord Q 0))
  refine ⟨cost, hcost, fun b ↦ ?_⟩
  obtain ⟨final,hE,hret⟩ := runs b
  have hn : st ≠ pubWord Q 0 + pubWord Q 0 := fun h ↦ i.isLt.ne ((congrArg Fin.val h).trans (publicTerminal Q F))
  have hlen := dataEvents_length m cost (nativeOps Q i) b
  have hr := execute_data (pubWord Q) st m (nativeFuel r) hn _ final _ hE (by unfold nativeFuel; omega)
  simpa only [dataEvents_choices, hret] using hr

private def nativeReport (Q : Layout L n r H w) (i : Position n r) (m : Memory w) (b : Bool) : Report w :=
  (execute (nativeMachine Q).program (nativeFuel r)
    ((nativeMachine Q).program.start (cursor Q.cursorFits i.val i.isLt.le)) m ((nativeOps Q i).bits b)).getD
      (haltReport w)

private theorem nativeReport_spec (Q : Layout L n r H w) (F : ParameterFit Q) (i : Position n r)
    (m : Memory w) (b : Bool) (hc : CutMemory L m) :
    ∃ cost, nativeReport Q i m b =
      ⟨prefixEvents w ++ dataEvents m cost (nativeOps Q i) b, some (successor Q.cursorFits i)⟩ := by
  obtain ⟨cost, _, hr⟩ := native_data Q F i m hc
  exact ⟨cost, by simp [nativeReport, hr b]⟩

/-- Refinement by the fixed physical program of every scheduled owner and copy call. -/
def physicalSchedule (Q : Layout L n r H w) (F : ParameterFit Q) :
    PhysicalSchedule (nativeMachine Q).program (nativeFuel r) (nativeOps Q) (encodeBit w) Q.cursorFits (CutMemory L) where
  report := nativeReport Q
  last _ := ⟨prefixEvents w, none⟩
  data i m b hc := by
    obtain ⟨cost, _, hr⟩ := native_data Q F i m hc
    simp only [nativeReport, hr b, Option.getD_some]
  result i m b hc := by obtain ⟨_, he⟩ := nativeReport_spec Q F i m b hc; rw [he]
  memory i m b hc := by
    obtain ⟨cost, he⟩ := nativeReport_spec Q F i m b hc
    rw [he]
    change after m (dataEvents m cost (nativeOps Q i) b) = _
    exact dataEvents_memory ..
  probes i m b hc := by
    obtain ⟨cost, he⟩ := nativeReport_spec Q F i m b hc
    rw [he]
    change countProbes (dataEvents m cost (nativeOps Q i) b) = _
    rw [dataEvents_probes, Nat.add_comm]
  closed := cutMemory_step Q
  halt m _ := by
    change execute _ ((3*r+160)+5) _ m [] = _
    exact execute_terminal _ _ m _ (Fin.ext (publicTerminal Q F).symm)
  halt_result _ _ := rfl
  halt_memory _ _ := rfl
  halt_probes _ _ := rfl

end PrimedInputRAM.Opcodes

end VPVNP
end Computability
end OAI
