import OAI.ThreeFlat.RAM.HistoryJoinScan

namespace OAI
/-! # Chronological execution of ordered child joins

A seven-word command holds the six join-header fields and the exclusive
output end. A fixed public parameter points to the current-command word;
the next memory word stores the exclusive end of the command stream.
The same code executes each join and then advances this cursor by seven.
-/

namespace ThreeFlat.RAM.HistoryJoinController

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr HistoryJoinScan

variable {w p r k : ℕ}

/-- Dispatch, load the output bounds, and advance to the following command. -/
def code (P : Fin 18 → Fin p) (R : Fin 4 ↪ Fin r) (base : Fin k) (inner exit : Fin p) (pc : Fin 18) : Instr w p r k :=
  match pc.val with
  | 0 => .publicWord (R 0) base (P 1)
  | 1 => .readExternal (R 1) (R 0) (P 2)
  | 2 => .constant (R 2) 1 (P 3)
  | 3 => .binary .add (R 2) (R 0) (R 2) (P 4)
  | 4 => .readExternal (R 2) (R 2) (P 5)
  | 5 => .jumpLt (R 1) (R 2) (P 6) exit
  | 6 => .constant (R 2) 1 (P 7)
  | 7 => .binary .add (R 2) (R 1) (R 2) (P 8)
  | 8 => .readExternal (R 0) (R 2) (P 9)
  | 9 => .constant (R 2) 6 (P 10)
  | 10 => .binary .add (R 2) (R 1) (R 2) (P 11)
  | 11 => .readExternal (R 1) (R 2) (P 12)
  | 12 => .constant (R 3) 1 inner
  | 13 => .publicWord (R 0) base (P 14)
  | 14 => .readExternal (R 1) (R 0) (P 15)
  | 15 => .constant (R 2) 7 (P 16)
  | 16 => .binary .add (R 1) (R 1) (R 2) (P 17)
  | _ => .writeExternal (R 0) (R 1) (P 0)

variable (M : Machine w p r k) (P : Fin 18 → Fin p) (R : Fin 4 ↪ Fin r)
    (base : Fin k) (inner exit : Fin p)

def dispatch (q : Fin p) (c : Config w p r) (m : Memory w) : Config w p r :=
  let b := M.publicData base
  let z := ((((c.put (P 1) (R 0) b).put (P 2) (R 1) (m b.val)).put (P 3) (R 2) 1).put
    (P 4) (R 2) (b+1)).put (P 5) (R 2) (m (b+1).val)
  {z with pc := q}

def loadBounds (c : Config w p r) (m : Memory w) : Config w p r :=
  let ptr := c.reg (R 1)
  ((((((c.put (P 7) (R 2) 1).put (P 8) (R 2) (ptr+1)).put (P 9) (R 0) (m (ptr+1).val)).put
    (P 10) (R 2) 6).put (P 11) (R 2) (ptr+6)).put (P 12) (R 1) (m (ptr+6).val)).put inner (R 3) 1

def bumped (c : Config w p r) (m : Memory w) : Config w p r :=
  let b := M.publicData base
  let v := m b.val
  let z := (((c.put (P 14) (R 0) b).put (P 15) (R 1) v).put (P 16) (R 2) 7).put
    (P 17) (R 1) (v+7)
  {z with pc := P 0}

def bumpMemory (ctrl : Word w) (m : Memory w) : Memory w := writeMemory m ctrl (m ctrl.val+7)

variable (rom : ∀ i, M.code (P i) = code P R base inner exit i)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
include rom in
theorem go_dispatch (c : Config w p r) (m : Memory w) (hc : c.pc = P 0) :
    let b := M.publicData base
    let q := if m b.val < m (b+1).val then P 6 else exit
    advance M.program 6 c m = some (dispatch M P R base q c m,m) := by
  simp [advance, Machine.program, hc, rom, code, Instr.run, Config.put, BinaryOp.eval,
    dispatch, Function.update, R.injective.eq_iff]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
include rom in
theorem go_bounds (c : Config w p r) (m : Memory w) (hc : c.pc = P 6) :
    advance M.program 7 c m = some (loadBounds P R inner c m,m) := by
  simp [advance, Machine.program, hc, rom, code, Instr.run, Config.put, BinaryOp.eval,
    loadBounds, Function.update, R.injective.eq_iff]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
include rom in
theorem go_bump (c : Config w p r) (m : Memory w) (hc : c.pc = P 13) :
    advance M.program 5 c m = some (bumped M P R base c m,bumpMemory (M.publicData base) m) := by
  simp [advance, Machine.program, hc, rom, code, Instr.run, Config.put, BinaryOp.eval,
    bumped, bumpMemory, Function.update, R.injective.eq_iff]

/-- Execution result and fuel bound computed entirely from the chronological
command list and the concrete memory at each command. This also permits a
later command to read output words written by an earlier command. -/
inductive Trace (ctrl : Word w) : Memory w → Memory w → ℕ → Prop where
  | done (m : Memory w) (end_ : ¬ m ctrl.val < m (ctrl+1).val) : Trace ctrl m m 6
  | step {m out fuel} (live : m ctrl.val < m (ctrl+1).val) (n : ℕ)
      (length : (m (m ctrl.val+1).val).val + n = (m (m ctrl.val+6).val).val)
      (ctrl_away : ctrl.val < (m (m ctrl.val+1).val).val ∨ (m (m ctrl.val+6).val).val ≤ ctrl.val)
      (sep : Separate (m ctrl.val) (m (m ctrl.val+1).val).val (m (m ctrl.val+6).val).val m)
      (rest : Trace ctrl (bumpMemory ctrl (fillSegment (m (m ctrl.val+1).val).val n
        (fun a => readWord (fetch (m ctrl.val) m) m (Fin.ofNat _ a)) m)) out fuel) :
      Trace ctrl m out (19 + n*254 + fuel)

include rom in
/-- One fixed program executes all commands, including the final failed test. -/
theorem run (L : DescriptorScan.Labels p) (jump : L.guard = inner) (back : L.exit = P 13)
    (loc : Fin (term (w := w) base).labels → Fin p) (tmp : Fin (term (w := w) base).binds ↪ Fin r)
    (fresh : ∀ i j, R i ≠ tmp j) (entry : loc (term base).first = L.describe)
    (scan : DescriptorScan.Installed M R L)
    (expr : ∀ i, M.code (loc i) = (term base).emit loc (fun _ => R 0) tmp (R 2) L.store i)
    {m out fuel} (tr : Trace (M.publicData base) m out fuel) (c : Config w p r) (hc : c.pc = P 0) :
    ∃ t ≤ fuel, ∃ d : Config w p r, d.pc = exit ∧ advance M.program t c m = some (d,out) := by
  induction tr generalizing c with
  | done m stop =>
    refine ⟨6,le_rfl,dispatch M P R base exit c m,rfl,?_⟩
    simpa only [ite_eq_right stop] using go_dispatch M P R base inner exit rom c m hc
  | @step m out fuel live n len away sep rest ih =>
    let v := M.publicData base
    let d := dispatch M P R base (P 6) c m
    let z := loadBounds P R inner d m
    have hd : advance M.program 6 c m = some (d,m) := by
      simpa only [d, ite_eq_left live] using go_dispatch M P R base inner exit rom c m hc
    have hz := go_bounds M P R base inner exit rom d m rfl
    have registers : z.reg (R 0) = m (m v.val + 1).val ∧
        z.reg (R 1) = m (m v.val + 6).val ∧ z.reg (R 3) = 1 := by
      simp [z,d,loadBounds,dispatch,Config.put,Function.update,R.injective.eq_iff,v]
    obtain ⟨s,hs,o,pc,o_run⟩ := HistoryJoinScan.generate M R L base loc tmp fresh entry scan expr
      m z n (by change inner = L.guard; exact jump.symm) registers.2.2
      (by simpa only [registers.1,registers.2.1] using len)
      (by simpa only [registers.1,registers.2.1] using away)
      (by simpa only [registers.1,registers.2.1] using sep)
    try dsimp only at o_run
    rw [registers.1] at o_run
    let m' := fillSegment (m (m v.val+1).val).val n
      (fun a => readWord (fetch (m v.val) m) m (Fin.ofNat _ a)) m
    have inc := go_bump M P R base inner exit rom o m' (pc.trans back)
    obtain ⟨t,ht,q,hq,qr⟩ := ih (bumped M P R base o m') rfl
    refine ⟨6+7+s+5+t, by omega, q, hq, ?_⟩
    exact advance_trans (advance_trans (advance_trans (advance_trans hd hz) o_run) inc) qr

end ThreeFlat.RAM.HistoryJoinController

end OAI
