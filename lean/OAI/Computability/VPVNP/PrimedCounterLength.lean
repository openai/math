import OAI.Computability.VPVNP.PrimedCounterData
import OAI.Computability.VPVNP.PrimedCounterDispatchNative

/-!
# Number of calls in a native pair-counter history

Every successful call returns the next absolute cursor, or accepts at the final
item. This follows from the code for all five branches, even on arbitrary external
memory. Consequently a successful history halts exactly at the public call count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM PrimedSchedule
open scoped Fin.CommRing

namespace Dispatch

variable {w A S m nodes T : ℕ} {pub : Program.Pub → Word w}

/-- All five branches preserve the prepared successor and total through the final jump. -/
theorem native_result (hw : ScheduleWords pub A S m nodes T) (hfit : Cursor.calls A S m nodes T < 2^w)
    (i : Cursor.Item A S m nodes T) (regs : Regs w 52) (priv : Word w → Word w)
    (mem : Memory w) (bits : List Bool) (fuel : ℕ) (out : Report w)
    (hr : NativeAt pub regs priv mem bits fuel out i) :
    out.result = control w (Cursor.calls A S m nodes T) ((Cursor.index A S m nodes T i).val+1) := by
  have arm {r p : ℕ} (reg : Fin r ↪ Program.Reg) (port : Fin p → Program.Pub) (small : Flow r p)
      (hc : branch i = renameFlow reg port small)
      (hout : (49 : Program.Reg) ∉ Set.range reg ∧ (50 : Program.Reg) ∉ Set.range reg) :
      out.result = control w (Cursor.calls A S m nodes T) ((Cursor.index A S m nodes T i).val+1) := by
    obtain ⟨_,_,_,_,_,_,_,hc,_⟩ :=
      (placed_execute_iff hw hfit i reg port small hc hout regs priv mem bits fuel out).mp hr
    exact hc
  rcases i with j | ⟨u,j | j | j⟩ | j
  · exact arm Program.inputRegs Program.inputPub _ rfl input_outside
  · exact arm Program.parserRegs Program.parserPub _ rfl parser_outside
  · exact arm Program.parserRegs Program.parserPub _ rfl parser_outside
  · exact arm Program.parserRegs Program.stackPub _ rfl parser_outside
  · exact arm Program.parserRegs Program.parserPub _ rfl parser_outside

end Dispatch

namespace Data

variable {L : Lengths} {w n r H s : ℕ} {Q : Layout L n r H w} (D : Data Q s)

theorem total_pos : 0 < D.total := by
  have hsites : 0 < 2 * 2^r := by positivity
  have hspan : 0 < Cursor.span n (2*n-1) := by unfold Cursor.span; omega
  have := Nat.mul_pos hsites hspan
  unfold total Cursor.calls
  omega

private def nativeItem : PrimedSchedule.Item w := fun i m b =>
  execute D.machine.program D.fuel (D.machine.program.start (cursor w i)) m b

private theorem nativeSchedule (hf : D.Fits) :
    ScheduleSpec D.machine.program D.fuel D.total D.nativeItem (fun _ _ => True) := by
  refine ⟨fun _ _ _ _ _ => rfl, ?_⟩
  intro v hv mem _ bits out he
  refine ⟨?_,trivial⟩
  let idx := Cursor.index D.assembly (2*2^r) n (2*n-1) D.labels
  let i := idx.symm ⟨v,hv⟩
  have hi : (idx i).val = v := congrArg Fin.val (idx.apply_symm_apply _)
  have hcur : Dispatch.itemState w i = cursor w v := by
    change ((idx i).val : Word w) = cursor w v
    rw [hi, PrimedSchedule.cursor, Fin.ofNat_eq_cast]
  have hm : D.parserPub (Admin.stackPublic 6) = (n : Word w) := congrFun D.parserPub_stack 6
  have hwords : Dispatch.ScheduleWords D.pub D.assembly (2*2^r) n (2*n-1) D.labels :=
    Dispatch.scheduleWords (Opcodes.pubWord Q) D.parserPub hm
  have hrun : Dispatch.NativeAt D.pub (fun _ => 0) (fun _ => 0) mem bits D.fuel out i := by
    unfold Dispatch.NativeAt
    rw [hcur]
    exact he
  have hr := Dispatch.native_result hwords hf.cursor i _ _ mem bits D.fuel out hrun
  change out.result = control w D.total ((idx i).val+1) at hr
  simpa only [hi] using hr

private theorem first_control : control w D.total 0 = some 0 := by
  simp [PrimedSchedule.control, D.total_pos, PrimedSchedule.cursor, Fin.ofNat_eq_cast]

private theorem run_eq_items (hf : D.Fits) (m : Memory w) (bs : List (List Bool)) :
    runSegment D.machine.program D.fuel (some 0) m bs = runItems D.nativeItem D.total 0 m bs := by
  simpa only [D.first_control] using native_eq_runItems (D.nativeSchedule hf) 0 m trivial bs

/-- A successful partial run halts precisely when its number of supplied call tapes
equals the public call count. -/
theorem history_halts_iff (hf : D.Fits) {m : Memory w} {bs : List (List Bool)} {rs : List (Report w)}
    (hr : runSegment D.machine.program D.fuel (some 0) m bs = some rs) :
    endState (some 0) rs = none ↔ bs.length = D.total := by
  rw [D.run_eq_items hf] at hr
  obtain ⟨_,hle,he⟩ := runItems_progress (D.nativeSchedule hf) 0 m trivial (Nat.zero_le _) hr
  rw [D.first_control, Nat.zero_add] at he
  rw [Nat.zero_add] at hle
  rw [he, PrimedSchedule.control]
  split <;> rename_i h
  · simp [Nat.ne_of_lt h]
  · simp [Nat.le_antisymm hle (Nat.le_of_not_gt h)]

theorem actualPath_length (hf : D.Fits) {m : Memory w} {cap : List (Report w) → Prop}
    (p : ActualPaths D.machine.program D.fuel 0 m cap) : p.val.length = D.total := by
  obtain ⟨rs,hr,hh,_⟩ := p.property
  exact (D.history_halts_iff hf hr).mp hh

/-- Every successful fixed-size tape reaches the accepting state. -/
theorem history_end (hf : D.Fits) {m : Memory w} {raw : Fin D.total → List Bool} {rs : List (Report w)}
    (hr : runSegment D.machine.program D.fuel (some 0) m (List.ofFn raw) = some rs) :
    endState (some 0) rs = none := (D.history_halts_iff hf hr).mpr List.length_ofFn

/-- Read an accepting native history as the unique array of choices at its absolute
cursors. Reading the array back in order recovers the original history. -/
noncomputable def historyEquiv (hf : D.Fits) (S K : ℕ) :
    ActualPaths D.machine.program D.fuel 0 D.initial (withinCaps S K) ≃
      {raw : Fin D.total → List Bool //
        ∃ rs, runSegment D.machine.program D.fuel (some 0) D.initial (List.ofFn raw) = some rs ∧
          withinCaps S K rs} :=
  (nativeScheduleEquiv (D.nativeSchedule hf) D.total_pos D.initial trivial (withinCaps S K)).trans
    (Equiv.subtypeEquivRight fun _ => by
      rw [← D.run_eq_items hf])

end Data
end PrimedCounter

end VPVNP
end Computability
end OAI
