import OAI.Computability.VPVNP.PrimedCounterDispatch

/-!
# Native clear, root, visit and comparison calls

Each cursor reduces to the original small routine on its projected public
words and prepared local register file. The native call accepts at the last
item and returns the successor on all earlier successful items.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Dispatch

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM Program
open scoped Fin.CommRing

variable {w A S m nodes T : ℕ}

/-- Successful native execution on an individual schedule item. -/
abbrev NativeAt (pub : Pub → Word w) (regs : Regs w 52) (priv : Word w → Word w)
    (mem : Memory w) (bits : List Bool) (fuel : ℕ) (out : Report w) (i : Cursor.Item A S m nodes T) : Prop :=
  let M := table.instantiate w pub
  execute M.program fuel ⟨M.entry,itemState w i,regs,priv⟩ mem bits = some out

/-- Exact local execution and its effect on the report returned by the whole call. -/
abbrev LocalResult {r p : ℕ} (pub : Fin p → Word w) (small : Flow r p) (rs : Regs w r)
    (mem : Memory w) (bits : List Bool) (fuel : ℕ) (out : Report w) (i : Cursor.Item A S m nodes T) : Prop :=
  ∃ es smallOut m', Flow.Exec pub (itemState w i) small rs mem es smallOut m' ∧
    overhead i + es.length + 2 ≤ fuel ∧ choiceBits es = bits ∧
    out.events = (List.replicate (overhead i) .tick ++ es) ++ [.tick] ∧
    out.result = PrimedSchedule.control w (Cursor.calls A S m nodes T) ((Cursor.index A S m nodes T i).val+1) ∧
    after mem out.events = m'

/-- A scheduled native call is exactly the selected embedded routine with its
literal dispatch and exit opcodes. -/
theorem placed_execute_iff {pub : Pub → Word w} (hw : ScheduleWords pub A S m nodes T)
    (hfit : Cursor.calls A S m nodes T < 2^w) (i : Cursor.Item A S m nodes T)
    {r p : ℕ} (reg : Fin r ↪ Reg) (port : Fin p → Pub) (small : Flow r p)
    (hc : branch i = renameFlow reg port small)
    (houtside : (49 : Reg) ∉ Set.range reg ∧ (50 : Reg) ∉ Set.range reg)
    (regs : Regs w 52) (priv : Word w → Word w) (mem : Memory w) (bits : List Bool) (fuel : ℕ) (out : Report w) :
    NativeAt pub regs priv mem bits fuel out i ↔
      LocalResult (pub ∘ port) small (prepared regs i ∘ reg) mem bits fuel out i := by
  have hp := body_pref (rs := regs) hw hfit i
  rw [hc] at hp
  obtain ⟨h49,h50⟩ := prepared_controls regs i
  exact execute_pref_iff reg port small hp h49 h50 houtside.1 houtside.2
    (Cursor.index A S m nodes T i).isLt hfit priv mem bits fuel out

variable (inputs : Fin 16 → Word w) (parser : Fin 14 → Word w)
  (hm : parser (Admin.stackPublic 6) = (m : Word w)) (hfit : Cursor.calls A S m nodes T < 2^w)
  (regs : Regs w 52) (priv : Word w → Word w) (mem : Memory w) (bits : List Bool) (fuel : ℕ) (out : Report w)

include hm hfit in
private theorem admin_iff (i : Cursor.Item A S m nodes T) (small : Flow 16 14)
    (hc : branch i = renameFlow parserRegs parserPub small) :
    NativeAt (publicWords inputs parser A S m nodes T) regs priv mem bits fuel out i ↔
      LocalResult parser small (prepared regs i ∘ parserRegs) mem bits fuel out i := by
  have hh : publicWords inputs parser A S m nodes T ∘ parserPub = parser :=
    funext (public_parser inputs parser A S m nodes T)
  simpa only [hh] using placed_execute_iff (scheduleWords inputs parser hm) hfit i parserRegs parserPub
    small hc parser_outside regs priv mem bits fuel out

include hm hfit in
theorem clear_execute_iff (u : Fin S) (j : Fin m) :
    let i : Cursor.Item A S m nodes T := .inr (.inl (u,.inl j))
    NativeAt (publicWords inputs parser A S m nodes T) regs priv mem bits fuel out i ↔
      LocalResult parser Admin.clear (prepared regs i ∘ parserRegs) mem bits fuel out i :=
  admin_iff inputs parser hm hfit regs priv mem bits fuel out _ _ rfl

include hm hfit in
theorem init_execute_iff (u : Fin S) (j : Fin 1) :
    let i : Cursor.Item A S m nodes T := .inr (.inl (u,.inr (.inl j)))
    NativeAt (publicWords inputs parser A S m nodes T) regs priv mem bits fuel out i ↔
      LocalResult parser Admin.init (prepared regs i ∘ parserRegs) mem bits fuel out i :=
  admin_iff inputs parser hm hfit regs priv mem bits fuel out _ _ rfl

include hm hfit in
theorem node_execute_iff (u : Fin S) (j : Fin nodes) :
    let i : Cursor.Item A S m nodes T := .inr (.inl (u,.inr (.inr j)))
    NativeAt (publicWords inputs parser A S m nodes T) regs priv mem bits fuel out i ↔
      LocalResult (parser ∘ Admin.stackPublic) nodeFlow (prepared regs i ∘ parserRegs) mem bits fuel out i := by
  have hh : publicWords inputs parser A S m nodes T ∘ stackPub = parser ∘ Admin.stackPublic :=
    funext fun k => public_parser inputs parser A S m nodes T (Admin.stackPublic k)
  simpa only [hh] using placed_execute_iff (scheduleWords inputs parser hm) hfit
    (.inr (.inl (u,.inr (.inr j)))) parserRegs stackPub nodeFlow rfl parser_outside regs priv mem bits fuel out

include hm hfit in
theorem compare_execute_iff (j : Fin T) :
    let i : Cursor.Item A S m nodes T := .inr (.inr j)
    NativeAt (publicWords inputs parser A S m nodes T) regs priv mem bits fuel out i ↔
      LocalResult parser Admin.compare (prepared regs i ∘ parserRegs) mem bits fuel out i :=
  admin_iff inputs parser hm hfit regs priv mem bits fuel out _ _ rfl

end PrimedCounter.Dispatch

end VPVNP
end Computability
end OAI
