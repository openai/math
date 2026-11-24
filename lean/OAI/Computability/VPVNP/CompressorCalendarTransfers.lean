import OAI.Computability.VPVNP.CompressorOnlineCursorStartup

/-!
# Calendar control across outer pair tag transfers

The compressed pair writes its stage tag after each successful component.
When that tag precedes the descriptor workspace, these writes preserve the
controller's pointer bank, controls, stride, and all persistent level cells.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.OnlineCursorStartup

open BurstRAM BurstRAM.PrivateRAM DescriptorSpace
open scoped Fin.CommRing

variable {w : ℕ}

/-- The outer stage transfer appends a tag write to the source memory effect. -/
def transfer (m : Memory w) (rep : Report w) (tag : Word w) (index : ℕ) : Memory w :=
  writeMemory (after m rep.events) tag (index : Word w)

theorem transfer_tag (m : Memory w) (rep : Report w) (tag : Word w) (index : ℕ) :
    transfer m rep tag index tag.val = (index : Word w) := by simp [transfer,writeMemory]

theorem lower_write_frame {k : ℕ} (m : Memory w) (base tag value : Word w)
    (lower : tag.val < base.val) (fit : base.val+k ≤ 2^w) :
    (Frame.data base (writeMemory m tag value) : Fin k → Word w) = Frame.data base m := by
  funext i
  rw [Frame.data_at _ _ fit, Frame.data_at _ _ fit, writeMemory, ite_eq_right (by omega)]

theorem offset_value (base : Word w) (j : ℕ) (fit : base.val+j < 2^w) :
    (base+(j : Word w)).val = base.val+j := by
  rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (show j < 2^w by omega), Nat.mod_eq_of_lt fit]

theorem lower_write_ready (d g : ℕ) (base rows stride tag value : Word w) (m : Memory w)
    (lower : tag.val < base.val) (fit : base.val+10+g < 2^w)
    (ready : OnlineWorkspace.Ready d g base rows stride m) :
    OnlineWorkspace.Ready d g base rows stride (writeMemory m tag value) := by
  have same (j : ℕ) (hj : j ≤ 10+g) :
      writeMemory m tag value (base+(j : Word w)).val = m (base+(j : Word w)).val := by
    rw [offset_value _ _ (by omega), writeMemory, ite_eq_right (by omega)]
  constructor
  · exact (lower_write_frame m base tag value lower (by omega : base.val+6 ≤ 2^w)).trans ready.bank
  · exact (same 6 (by omega)).trans ready.tag
  · exact (same 7 (by omega)).trans ready.ordinal
  · exact (same 8 (by omega)).trans ready.count
  · rw [OnlineWorkspace.gap_eq]
    apply (same (10+g) le_rfl).trans
    simpa only [OnlineWorkspace.gap_eq, OnlineWorkspace.gap] using ready.pitch

/-- Insert the two real transfer writes between and after the workspace
initializer and calendar selector. The ready workspace and every persistent
word above its controls are available to the next stage. -/
theorem transferred_arm (d g : ℕ) (pub : Fin 11 → Word w) (m : Memory w)
    (tag rows stride : Word w) (lower : tag.val < (pub 2).val) (fit : (pub 2).val+10+g < 2^w)
    (hr : m (pub 2+8).val = rows) (hs : m (OnlineWorkspace.gap g (pub 2)).val = stride) :
    let init := Workspace.initReport g (pub 2)
    let mid := transfer m init tag 7
    let arm := Workspace.calendarReport d (pub 2)
    let out := transfer mid arm tag 8
    Call (Workspace.initTable g) pub 42 0 m init ∧ Call (Workspace.calendarStart d) pub 6 0 mid arm ∧
      OnlineWorkspace.Ready d g (pub 2) rows stride out ∧
      (∀ x, (pub 2).val+8 ≤ x → out x = m x) := by
  intro init mid arm out
  have ⟨initExec,_,ready⟩ := OnlineWorkspace.arm d g pub 0 m rows stride (by omega) hr hs
  have armtag : (Workspace.ports g (pub 2)).tag.val = (pub 2).val+6 :=
    offset_value (pub 2) 6 (by omega)
  have desc : out = writeMemory (OnlineWorkspace.armed d g (pub 2) m) tag (8 : Word w) := by
    funext x
    change writeMemory (after mid (Workspace.calendarReport d (pub 2)).events) tag _ x =
      writeMemory (after (after m init.events) (Workspace.calendarReport d (pub 2)).events) tag _ x
    rw [(Workspace.calendar_effect d g _ mid).1, (Workspace.calendar_effect d g _ (after m init.events)).1]
    by_cases ht : x = tag.val <;> simp [writeMemory, ht, mid, transfer]
  refine ⟨initExec, Workspace.execute_calendarStart d pub 0 mid [] 6 le_rfl,
    desc ▸ lower_write_ready d g _ rows stride tag 8 _ lower fit ready, ?_⟩
  intro x hx
  rw [desc, writeMemory, ite_eq_right (by omega : x ≠ tag.val), OnlineWorkspace.armed,
    (Workspace.calendar_effect d g ..).1, writeMemory,
    ite_eq_right (by omega : x ≠ (Workspace.ports g (pub 2)).tag.val)]
  apply Workspace.init_outside
  intro i
  rw [offset_value _ _ (by have := i.isLt; omega)]
  have := i.isLt
  omega

end CompressorRecords.OnlineCursorStartup

end VPVNP
end Computability
end OAI
