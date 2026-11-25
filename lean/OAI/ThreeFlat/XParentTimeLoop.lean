import OAI.ThreeFlat.RAM.DeterministicBlock
import OAI.ThreeFlat.RAM.ContinuationLink
import Mathlib.Data.ZMod.Defs

namespace OAI
/-! # A resident time cursor around the weighted per-slice parent body -/

namespace ThreeFlat.XParentTimeLoop

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.ContinuationLink
open scoped Fin.CommRing

variable {w b r k P R K : ℕ}

abbrev startPC : Fin 13 := 0
abbrev guardPC : Fin 13 := 3
abbrev afterBody : Fin 13 := 8

/-- Both public operands are addresses of external words. The body can reuse
all three registers because the guard and increment reload their inputs. -/
def row (loc : Fin 13→Fin P) (reg : Fin 3→Fin R) (params : Fin 2→Fin K)
    (body exit : Fin P) : Fin 13→Instr w P R K
  | 0 => .publicWord (reg 0) (params 0) (loc 1)
  | 1 => .constant (reg 1) 0 (loc 2)
  | 2 => .writeExternal (reg 0) (reg 1) (loc guardPC)
  | 3 => .publicWord (reg 0) (params 0) (loc 4)
  | 4 => .readExternal (reg 1) (reg 0) (loc 5)
  | 5 => .publicWord (reg 0) (params 1) (loc 6)
  | 6 => .readExternal (reg 2) (reg 0) (loc 7)
  | 7 => .jumpLt (reg 1) (reg 2) body exit
  | 8 => .publicWord (reg 0) (params 0) (loc 9)
  | 9 => .readExternal (reg 1) (reg 0) (loc 10)
  | 10 => .constant (reg 2) 1 (loc 11)
  | 11 => .binary .add (reg 1) (reg 1) (reg 2) (loc 12)
  | 12 => .writeExternal (reg 0) (reg 1) (loc guardPC)

abbrev ctlPC (pc : Fin (13+b) ↪ Fin P) := (Fin.castAddEmb b).trans pc
abbrev bodyPC (pc : Fin (13+b) ↪ Fin P) := (Fin.natAddEmb 13).trans pc

def block (D : Fin 3 ↪ Fin r) (address : Fin 2→Fin k) (body : Block w b r k) :
    Block w (13+b) r k where
  first := startPC.castAdd b
  emit pc reg pub exit := Fin.addCases
    (row (ctlPC pc) (reg ∘ D) (pub ∘ address) (bodyPC pc body.first) exit)
    (body.emit (bodyPC pc) reg pub (ctlPC pc afterBody))

structure Linked (M : Machine w P R K) (loc : Fin 13→Fin P) (D : Fin 3 ↪ Fin R)
    (address : Fin 2→Fin K) (body exit : Fin P) : Prop where
  fetch : ∀ i,M.code (loc i)=row loc D address body exit i

theorem installed (D : Fin 3 ↪ Fin r) (address : Fin 2→Fin k) (body : Block w b r k)
    (M : Machine w P R K) (pc : Fin (13+b) ↪ Fin P) (reg : Fin r ↪ Fin R)
    (pub : Fin k→Fin K) (exit : Fin P) (mounted : (block D address body).Installed M pc reg pub exit) :
    Linked M (ctlPC pc) (D.trans reg) (pub ∘ address) (bodyPC pc body.first) exit ∧
    body.Installed M (bodyPC pc) reg pub (ctlPC pc afterBody) := by
  refine ⟨⟨fun i => ?_⟩,fun i => ?_⟩
  · simpa [block,ctlPC] using mounted (i.castAdd b)
  · simpa [block,bodyPC] using mounted (Fin.natAdd 13 i)

variable {M : Machine w P R K} {loc : Fin 13→Fin P} {D : Fin 3 ↪ Fin R}
    {address : Fin 2→Fin K} {body exit : Fin P}
set_option quotPrecheck false
local notation "cur" => M.publicData (address 0)
local notation "last" => M.publicData (address 1)

private theorem store_eq (m : Memory w) (a v : Word w) : writeMemory m a v=Function.update m a.val v := by
  funext i
  simp [writeMemory,Function.update_apply]

theorem Linked.start (L : Linked M loc D address body exit) (c : Config w P R) (m : Memory w)
    (pc : c.pc=loc startPC) :
    ∃ z, advance M.program 3 c m=some (z,Function.update m (cur).val 0) ∧ z.pc=loc guardPC := by
  let z := (c.put (loc guardPC) (D 0) cur).put (loc guardPC) (D 1) 0
  refine ⟨z,?_,rfl⟩
  simp (config:={decide:=true}) [z,RAM.advance,Machine.program,pc,L.fetch,row,Instr.run,Config.put,
    D.injective.eq_iff,store_eq]

private theorem Linked.check (L : Linked M loc D address body exit) (c : Config w P R) (m : Memory w)
    (pc : c.pc=loc guardPC) :
    let target := if m (cur).val<m (last).val then body else exit
    ∃ z,advance M.program 5 c m=some (z,m) ∧ z.pc=target := by
  let target := if m (cur).val<m (last).val then body else exit
  let z := (((c.put target (D 0) cur).put target (D 1) (m (cur).val)).put target (D 0) last).put target (D 2) (m (last).val)
  refine ⟨z,?_,rfl⟩
  simp (config:={decide:=true}) [z,target,RAM.advance,Machine.program,pc,L.fetch,row,Instr.run,Config.put,
    D.injective.eq_iff]

theorem Linked.enter (L : Linked M loc D address body exit) (c : Config w P R) (m : Memory w) (i times : ℕ)
    (pc : c.pc=loc guardPC) (cursor : m (cur).val=(i:Word w)) (endWord : m (last).val=(times:Word w))
    (more : i<times) (fit : times<2^w) :
    ∃ z,advance M.program 5 c m=some (z,m) ∧ z.pc=body := by
  have lt : m (cur).val<m (last).val := by
    rw [cursor,endWord]
    change i%2^w<times%2^w
    rwa [Nat.mod_eq_of_lt (more.trans fit),Nat.mod_eq_of_lt fit]
  simpa only [ite_eq_left lt] using L.check c m pc

theorem Linked.finish (L : Linked M loc D address body exit) (c : Config w P R) (m : Memory w)
    (pc : c.pc=loc guardPC) (done : m (cur).val=m (last).val) :
    ∃ z,advance M.program 5 c m=some (z,m) ∧ z.pc=exit := by
  have le : ¬m (cur).val<m (last).val := by rw [done]; exact lt_irrefl _
  simpa only [ite_eq_right le] using L.check c m pc

theorem Linked.next (L : Linked M loc D address body exit) (c : Config w P R) (m : Memory w) (i : ℕ)
    (pc : c.pc=loc afterBody) (cursor : m (cur).val=(i:Word w)) :
    ∃ z,advance M.program 5 c m=some (z,Function.update m (cur).val ((i+1:ℕ):Word w)) ∧ z.pc=loc guardPC := by
  let g := loc guardPC
  let z := (((c.put g (D 0) cur).put g (D 1) (m (cur).val)).put g (D 2) 1).put g (D 1) (m (cur).val+1)
  refine ⟨z,?_,rfl⟩
  simp (config:={decide:=true}) [z,g,RAM.advance,Machine.program,pc,L.fetch,row,Instr.run,Config.put,
    D.injective.eq_iff,store_eq,BinaryOp.eval,cursor]

/-- Three initialization instructions, five for the final test, and ten per
accepted body return. The application's own weighted body cost is added separately. -/
def loopCost (times : ℕ) := 8+10*times

theorem loopCost_eq (times : ℕ) : 3+times*(5+5)+5=loopCost times := by unfold loopCost; omega


end ThreeFlat.XParentTimeLoop

end OAI
