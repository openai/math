import OAI.ThreeFlat.RAM.HistoryNodeDirectory

namespace OAI
/-! # Native forward scan over a selected slot's compact node IDs

The stored cursor is advanced before dispatch. A selected local kernel may
freely clobber all registers and is linked back to the guard. Only the
selected branch reads or writes any expanded coefficient or pin-map words.
-/

namespace ThreeFlat.RAM.HistoryNodeDirectory.Selected

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink

variable {w p r k : ℕ}

/-- Public pointers in order are cursor, reverse root-table, retained owner
directory, slot clock, root directory, and final-root count address. The
word after `cursor` stores the exclusive total node count. -/
def rows (P : Fin 35 → Fin p) (R : Fin 8 → Fin r) (pub : Fin 6 → Fin k) (take exit : Fin p)
    (pc : Fin 35) : Instr w p r k := match pc.val with
  | 0 => .publicWord (R 0) (pub 0) (P 1)
  | 1 => .constant (R 1) 0 (P 2)
  | 2 => .writeExternal (R 0) (R 1) (P 3)
  | 3 => .publicWord (R 2) (pub 4) (P 4)
  | 4 => .readExternal (R 2) (R 2) (P 5)
  | 5 => .publicWord (R 3) (pub 5) (P 6)
  | 6 => .readExternal (R 3) (R 3) (P 7)
  | 7 => .binary .add (R 2) (R 2) (R 3) (P 8)
  | 8 => .constant (R 4) 1 (P 9)
  | 9 => .binary .add (R 3) (R 0) (R 4) (P 10)
  | 10 => .writeExternal (R 3) (R 2) (P 11)
  | 11 => .publicWord (R 0) (pub 0) (P 12)
  | 12 => .readExternal (R 1) (R 0) (P 13)
  | 13 => .constant (R 4) 1 (P 14)
  | 14 => .binary .add (R 3) (R 0) (R 4) (P 15)
  | 15 => .readExternal (R 3) (R 3) (P 16)
  | 16 => .jumpLt (R 1) (R 3) (P 17) exit
  | 17 => .binary .add (R 2) (R 1) (R 4) (P 18)
  | 18 => .writeExternal (R 0) (R 2) (P 19)
  | 19 => .publicWord (R 5) (pub 1) (P 20)
  | 20 => .binary .add (R 5) (R 5) (R 1) (P 21)
  | 21 => .readExternal (R 5) (R 5) (P 22)
  | 22 => .binary .add (R 5) (R 5) (R 5) (P 23)
  | 23 => .publicWord (R 6) (pub 2) (P 24)
  | 24 => .binary .add (R 6) (R 6) (R 5) (P 25)
  | 25 => .readExternal (R 5) (R 6) (P 26)
  | 26 => .publicWord (R 7) (pub 3) (P 27)
  | 27 => .readExternal (R 2) (R 7) (P 28)
  | 28 => .jumpEq (R 2) (R 5) (P 29) (P 11)
  | 29 => .binary .add (R 6) (R 6) (R 4) (P 30)
  | 30 => .readExternal (R 5) (R 6) (P 31)
  | 31 => .constant (R 2) 3 (P 32)
  | 32 => .binary .add (R 7) (R 7) (R 2) (P 33)
  | 33 => .readExternal (R 2) (R 7) (P 34)
  | _ => .jumpEq (R 2) (R 5) take (P 11)

/-- Link a fixed preparation body back to the forward cursor reload. -/
def block {q : ℕ} (body : Block w q r k) (scratch : Fin 8 ↪ Fin r) (arg : Fin 6 → Fin k) : Block w (35+q) r k where
  first := (0:Fin 35).castAdd q
  emit pc reg pub exit :=
    let head i := pc ((i:Fin 35).castAdd q)
    let bodyLoc := (Fin.natAddEmb 35).trans pc
    Fin.append (rows head (reg ∘ scratch) (pub ∘ arg) (bodyLoc body.first) exit)
      (body.emit bodyLoc reg pub (head 11))

def Data (w : ℕ) := Fin 6 → Word w

def «initialize» (data : Data w) (m : Memory w) :=
  let start := writeMemory m (data 0) 0
  let len := start (data 4).val+start (data 5).val
  writeMemory start (data 0+1) len

def bump (data : Data w) (m : Memory w) := writeMemory m (data 0) (m (data 0).val+1)

def cur (data : Data w) (m : Memory w) := m (data 0).val

def owner (data : Data w) (m : Memory w) :=
  let root := (bump data m) (data 1+cur data m).val
  data 2+(root+root)

def groupOK (data : Data w) (m : Memory w) := bump data m (data 3).val = bump data m (owner data m).val

def slotOK (data : Data w) (m : Memory w) := bump data m (data 3+3).val = bump data m (owner data m+1).val

variable (M : Machine w p r k) (P : Fin 35 ↪ Fin p) (R : Fin 8 ↪ Fin r) (pub : Fin 6 → Fin k)
    (take exit : Fin p) (rom : ∀ i, M.code (P i) = rows P R pub take exit i)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
include rom in
theorem start (c : Config w p r) (m : Memory w) (pc : c.pc=P 0) :
    ∃ rs, advance M.program 11 c m = some (⟨P 11,c.persistent,rs,c.privateMem⟩,«initialize» (M.publicData∘pub) m) := by
  simp [advance,Machine.program,Instr.run,rows,rom,pc,Config.put,Function.update,R.injective.eq_iff,
    BinaryOp.eval,«initialize»]

set_option maxRecDepth 4096 in
open scoped Classical in
set_option maxHeartbeats 2500000 in
include rom in
theorem check (c : Config w p r) (m : Memory w) (pc : c.pc=P 11) :
    let data := M.publicData∘pub
    if cur data m < m (data 0+1).val then
      ∃ steps ≤ 24, ∃ rs, advance M.program steps c m = some
        (⟨if groupOK data m ∧ slotOK data m then take else P 11,c.persistent,rs,c.privateMem⟩,bump data m)
    else ∃ rs, advance M.program 6 c m = some (⟨exit,c.persistent,rs,c.privateMem⟩,m) := by
  classical
  dsimp only
  split
  · rename_i live
    by_cases g : groupOK (M.publicData∘pub) m
    · by_cases s : slotOK (M.publicData∘pub) m
      · refine ⟨24,by decide,?_⟩
        rw [ite_eq_left ⟨g,s⟩]
        simp only [groupOK,slotOK,owner,bump,cur,Function.comp_def] at g s live
        simp [advance,Machine.program,Instr.run,rows,rom,pc,Config.put,Function.update,R.injective.eq_iff,
          BinaryOp.eval,bump,live,g,s]
      · refine ⟨24,by decide,?_⟩
        rw [ite_eq_right (fun h=>s h.2)]
        simp only [groupOK,slotOK,owner,bump,cur,Function.comp_def] at g s live
        simp [advance,Machine.program,Instr.run,rows,rom,pc,Config.put,Function.update,R.injective.eq_iff,
          BinaryOp.eval,bump,live,g,s]
    · refine ⟨18,by decide,?_⟩
      rw [ite_eq_right (fun h=>g h.1)]
      simp only [groupOK,owner,bump,cur,Function.comp_def] at g live
      simp [advance,Machine.program,Instr.run,rows,rom,pc,Config.put,Function.update,R.injective.eq_iff,
        BinaryOp.eval,bump,live,g]
  · rename_i stop
    simp only [cur,Function.comp_def] at stop
    simp [advance,Machine.program,Instr.run,rows,rom,pc,Config.put,Function.update,R.injective.eq_iff,
      BinaryOp.eval,stop]

end ThreeFlat.RAM.HistoryNodeDirectory.Selected

end OAI
