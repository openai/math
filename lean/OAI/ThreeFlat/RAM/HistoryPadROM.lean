import OAI.ThreeFlat.RAM.HistoryPadDriver
import OAI.ThreeFlat.RAM.TickGenerateTable

namespace OAI
/-! # Installed padding table with a dynamic lower bound -/

namespace ThreeFlat.RAM.HistoryPadROM

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr HistoryPadDriver Fin.CommRing

variable {w k p r : ℕ} (base : Fin k)

def count := ((term (w:=w) base).labels+6)+2

@[simp] theorem count_eq : count (w:=w) base = 96 := by
  rw [count,Term.labels_eq,term_binds]

def sweep (loc : Fin (count (w:=w) base) → Fin p) (i : Fin ((term (w:=w) base).labels+6)) :=
  loc (i.castAdd 2)

def setup (loc : Fin (count (w:=w) base) → Fin p) (i : Fin 2) :=
  loc (Fin.natAdd ((term (w:=w) base).labels+6) i)

/-- The two additional entries fetch the lower bound; the existing scan table provides
the upper bound, unit, and all guard, descriptor, store and increment instructions. -/
def emit (last : Word w) (loc : Fin (count (w:=w) base) → Fin p)
    (reg : Fin (4+(term (w:=w) base).binds) ↪ Fin r) (exit : Fin p) :
    Fin (count (w:=w) base) → Instr w p r k :=
  let e := term (w:=w) base
  let R := TickGenerateTable.regs e reg
  Fin.append (TickGenerateTable.emit e 0 last (sweep base loc) reg exit)
    ![.publicWord (R 0) base (setup base loc 1),
      .readExternal (R 0) (R 0) (TickGenerateTable.driver e (sweep base loc) 1)]

/-- The same literal ROM runs from arbitrary caller registers on every selected suffix.
The upper bound is specified by the fixed capacity and the lower bound is read from RAM. -/
theorem generate (last : Word w) (M : Machine w p r k)
    (loc : Fin (count (w:=w) base) → Fin p)
    (reg : Fin (4+(term (w:=w) base).binds) ↪ Fin r) (exit : Fin p)
    (rom : ∀ i, M.code (loc i) = emit base last loc reg exit i)
    (lo n : ℕ) (force first tag : Word w) (c : Config w p r) (m : Memory w)
    (control : ∀ j : Fin 4, header (M.publicData base) m j = ![(lo : Word w),force,first,tag] j)
    (separate : ∀ j : Fin 4, let a := (M.publicData base+(j.val : Word w)).val; a < lo ∨ lo+n ≤ a)
    (span : last.val = lo+n) (entry : c.pc = setup base loc 0) :
    ∃ steps ≤ 5+62*n, ∃ out : Config w p r, out.pc = exit ∧
      advance M.program steps c m = some (out,fillSegment lo n (word lo force first tag) m) := by
  let e := term (w:=w) base
  let rows := sweep base loc
  let P := TickGenerateTable.driver e rows
  let R := TickGenerateTable.regs e reg
  have table (i) : M.code (rows i) = TickGenerateTable.emit e 0 last rows reg exit i := by
    simpa only [rows,sweep,emit,Fin.append_left] using rom (i.castAdd 2)
  have init (i : Fin 2) : M.code (setup base loc i) =
      ![.publicWord (R 0) base (setup base loc 1), .readExternal (R 0) (R 0) (P 1)] i := by
    simpa only [setup,emit,Fin.append_right] using rom (Fin.natAdd ((term (w:=w) base).labels+6) i)
  let x := m (M.publicData base).val
  let begin := (((c.put (setup base loc 1) (R 0) (M.publicData base)).put (P 1) (R 0) x).put
    (P 2) (R 1) last).put (P 3) (R 3) 1
  have src : x = (lo : Word w) := by simpa [header,x] using control 0
  have pre : advance M.program 4 c m = some (begin,m) := by
    have rb (i) := TickGenerateTable.installed_driver e M 0 last rows reg exit table i
    simp only [advance,Machine.program,entry,init,rb,TickGenerateTable.prologue,Instr.run,begin,P,R,
      x,Config.put,Function.update_self,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
  have start : (begin.reg (R 0)).val = lo := by
    have vlo : lo < 2^w := by have := last.isLt; omega
    have hz : begin.reg (R 0) = x := by simp [begin,Config.put,R.injective.eq_iff,Function.update]
    rw [hz,src,Fin.val_cast_of_lt vlo]
  have stop : (begin.reg (R 1)).val = lo+n := by
    have hz : begin.reg (R 1) = last := by simp [begin,Config.put,R.injective.eq_iff,Function.update]
    rw [hz,span]
  obtain ⟨s,hs,out,done,run⟩ := HistoryPadDriver.generate_padding M R (TickGenerateTable.labels e rows exit)
    (TickGenerateTable.installed e M 0 last rows reg exit table) base (TickGenerateTable.desc e rows) (TickGenerateTable.temp e reg)
    (TickGenerateTable.fresh e reg) rfl (TickGenerateTable.installed_desc e M 0 last rows reg exit table)
    lo n force first tag begin m control separate rfl start stop (Config.put_same ..)
  exact ⟨4+s,by omega,out,done,advance_trans pre run⟩

end ThreeFlat.RAM.HistoryPadROM

end OAI
