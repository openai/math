import OAI.Computability.VPVNP.PrimedCounterDispatchPrefix

/-!
# Cursor bounds and the outer dispatch tests

At a legal item, the first five opcodes install the absolute cursor, its
successor and the public call count. Two unsigned comparisons distinguish the
input, site and histogram regions without wraparound.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Dispatch

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM Program
open scoped Fin.CommRing

variable {w A S m nodes T : ℕ}

/-- The schedule words used by the actual jump and division opcodes. -/
structure ScheduleWords (pub : Pub → Word w) (A S m nodes T : ℕ) : Prop where
  assembly : pub 30 = (A : Word w)
  span : pub 31 = (Cursor.span m nodes : Word w)
  compareStart : pub 32 = (Cursor.compareStart A S m nodes : Word w)
  calls : pub 33 = (Cursor.calls A S m nodes T : Word w)
  marks : pub (stackPub 6) = (m : Word w)

theorem scheduleWords (inputs : Fin 16 → Word w) (parser : Fin 14 → Word w)
    (hm : parser (Admin.stackPublic 6) = (m : Word w)) :
    ScheduleWords (publicWords inputs parser A S m nodes T) A S m nodes T := by
  obtain ⟨ha, hs, hc, ht⟩ := public_schedule inputs parser A S m nodes T
  exact ⟨ha, hs, hc, ht, (public_parser inputs parser A S m nodes T _).trans hm⟩

/-- A scheduled input cell, local parser operation or histogram comparison represented before
conversion to its absolute cursor. -/
abbrev Item := Cursor.Item A S m nodes T

/-- Persistent word supplied to the common program for this item. -/
def itemState (w : ℕ) (i : Item (A := A) (S := S) (m := m) (nodes := nodes) (T := T)) : Word w :=
  ((Cursor.index A S m nodes T i).val : Word w)

/-- Registers after executing the first five literal instructions. -/
def controlRegs (rs : Regs w 52) (v A U : ℕ) : Regs w 52 :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    rs 48 (v : Word w)) 51 1) 49 ((v+1 : ℕ) : Word w)) 50 (U : Word w)) 51 (A : Word w)

/-- Site and histogram regions also retain the absolute histogram start in register 17. -/
def laterRegs (rs : Regs w 52) (v A U start : ℕ) : Regs w 52 :=
  Function.update (controlRegs rs v A U) 17 (start : Word w)

/-- Histogram comparison selects label `j` in operand register 7. -/
def compareRegs (rs : Regs w 52) (v A U start j : ℕ) : Regs w 52 :=
  Function.update (laterRegs rs v A U start) 7 (j : Word w)

variable {pub : Pub → Word w} {rs : Regs w 52}

private theorem setup_pref (hw : ScheduleWords pub A S m nodes T) (v : ℕ) :
    Pref pub (v : Word w) body rs (.ifLt 48 51 input afterInputs)
      (controlRegs rs v A (Cursor.calls A S m nodes T)) 5 := by
  apply Pref.lines
  intro mem
  simp (config := { decide := true }) [dispatchSetup, trace, Op.effect, BinaryOp.eval, controlRegs,
    Function.update, hw.calls, hw.assembly, Nat.cast_add, List.replicate_succ]

private theorem lt_word {a b : ℕ} (ha : a < 2^w) (hb : b < 2^w) :
    ((a : Word w) < (b : Word w)) ↔ a < b := by
  change (a : Word w).val < (b : Word w).val ↔ _
  rw [Fin.val_natCast, Fin.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

private theorem assembly_le_start : A ≤ Cursor.compareStart A S m nodes := by
  simp [Cursor.compareStart]

private theorem start_le_calls : Cursor.compareStart A S m nodes ≤ Cursor.calls A S m nodes T := by
  simp [Cursor.compareStart, Cursor.calls, ← Nat.add_assoc]

/-- The input branch starts on its original cursor, with the native successor
and total installed outside the 48-register assembly operand space. -/
theorem input_pref (hw : ScheduleWords pub A S m nodes T)
    (hfit : Cursor.calls A S m nodes T < 2^w) (j : Fin A) :
    Pref pub (itemState w (.inl j : Cursor.Item A S m nodes T)) body rs input
      (controlRegs rs j.val A (Cursor.calls A S m nodes T)) 6 := by
  have ha := (assembly_le_start (A := A) (S := S) (m := m) (nodes := nodes)).trans_lt (start_le_calls.trans_lt hfit)
  apply (setup_pref (rs := rs) hw j.val).trans (k := 1)
  apply Pref.ifLtYes
  simpa (config := { decide := true }) [controlRegs, Function.update] using (lt_word (j.isLt.trans ha) ha).mpr j.isLt

private theorem later_pref (hw : ScheduleWords pub A S m nodes T)
    (hfit : Cursor.calls A S m nodes T < 2^w) (v : ℕ) (hA : A ≤ v) (hv : v < 2^w) :
    Pref pub (v : Word w) body rs (.ifLt 48 17 site (.seq (.line (.binary .sub 7 48 17)) compare))
      (laterRegs rs v A (Cursor.calls A S m nodes T) (Cursor.compareStart A S m nodes)) 7 := by
  have ha := (assembly_le_start (A := A) (S := S) (m := m) (nodes := nodes)).trans_lt (start_le_calls.trans_lt hfit)
  have hge : ¬controlRegs rs v A (Cursor.calls A S m nodes T) 48 <
      controlRegs rs v A (Cursor.calls A S m nodes T) 51 := by
    simpa (config := { decide := true }) [controlRegs, Function.update, lt_word hv ha] using Nat.not_lt.mpr hA
  apply ((setup_pref (rs := rs) hw v).trans (Pref.ifLtNo hge)).trans (k := 1)
  apply Pref.line
  intro mem
  simp only [Op.effect, hw.compareStart, laterRegs]

/-- Every site cursor passes both outer phase tests, preserving the exact
absolute cursor and assembly boundary for the row division. -/
theorem row_pref (hw : ScheduleWords pub A S m nodes T)
    (hfit : Cursor.calls A S m nodes T < 2^w) (u : Fin S) (i : Cursor.LocalItem m nodes) :
    let idx := Cursor.index A S m nodes T (.inr (.inl (u,i)))
    Pref pub (itemState w (.inr (.inl (u,i)) : Cursor.Item A S m nodes T)) body rs site
      (laterRegs rs idx.val A (Cursor.calls A S m nodes T) (Cursor.compareStart A S m nodes)) 8 := by
  dsimp only
  let idx := Cursor.index A S m nodes T (.inr (.inl (u,i)))
  obtain ⟨hA, hs, _⟩ := Cursor.unpack_site (A := A) (T := T) u i
  apply (later_pref (rs := rs) hw hfit idx.val hA (idx.isLt.trans hfit)).trans (k := 1)
  apply Pref.ifLtYes
  simpa (config := { decide := true }) [laterRegs, controlRegs, Function.update] using
    (lt_word (idx.isLt.trans hfit) (start_le_calls.trans_lt hfit)).mpr hs

/-- The last region skips the site, subtracts the histogram start and passes
the resulting dense label index to the comparison code. -/
theorem compare_pref (hw : ScheduleWords pub A S m nodes T)
    (hfit : Cursor.calls A S m nodes T < 2^w) (j : Fin T) :
    let idx := Cursor.index A S m nodes T (.inr (.inr j))
    Pref pub (itemState w (.inr (.inr j) : Cursor.Item A S m nodes T)) body rs compare
      (compareRegs rs idx.val A (Cursor.calls A S m nodes T) (Cursor.compareStart A S m nodes) j.val) 9 := by
  dsimp only
  let idx := Cursor.index A S m nodes T (.inr (.inr j))
  let start := Cursor.compareStart A S m nodes
  have hj : idx.val = start+j.val := Cursor.index_compare j
  have hs : start ≤ idx.val := by omega
  let mid := laterRegs rs idx.val A (Cursor.calls A S m nodes T) start
  have h48 : mid 48 = (idx.val : Word w) := by
    simp (config := { decide := true }) [mid, laterRegs, controlRegs, Function.update]
  have h17 : mid 17 = (start : Word w) := by simp [mid, laterRegs]
  have hge : ¬mid 48 < mid 17 := by rw [h48, h17, lt_word (idx.isLt.trans hfit) (start_le_calls.trans_lt hfit)]; omega
  apply ((later_pref (rs := rs) hw hfit idx.val (assembly_le_start.trans hs) (idx.isLt.trans hfit)).trans
    (Pref.ifLtNo hge)).trans (k := 1)
  apply Pref.line
  intro mem
  change some (Event.tick (w := w), Function.update mid 7 (mid 48 - mid 17), mem) = _
  have hd : mid 48 - mid 17 = (j.val : Word w) := by rw [h48, h17, hj, Nat.cast_add, add_sub_cancel_left]
  rw [hd]
  rfl

end PrimedCounter.Dispatch

end VPVNP
end Computability
end OAI
