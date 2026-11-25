import OAI.ThreeFlat.RAM.TickIntervalFill
import OAI.ThreeFlat.Diagonal.TickGroupIntervals

namespace OAI
/-! # The descriptor layout, clipped payload and register invariants of the interval cursor -/

namespace ThreeFlat.RAM.TickIntervalCursor

open Computability.VPVNP.BurstRAM PrivateRAM Fin.CommRing Diagonal.TickGroupIntervals

variable {w p r : ℕ}

structure Layout where
  chunkStart : ℕ
  chunkEnd : ℕ
  mapBase : ℕ
  group : ℕ

structure Layout.Fits (L : Layout) (w : ℕ) : Prop where
  ordered : L.chunkStart ≤ L.chunkEnd
  chunk : L.chunkEnd < 2^w
  map : L.mapBase+(L.chunkEnd-L.chunkStart) < 2^w
  group : L.group < 2^w

def rowSize (L : Layout) (e : Interval) := e.covered L.group L.chunkStart L.chunkEnd

def rowSteps (L : Layout) (e : Interval) :=
  10 + (if e.group = L.group then 10 else 0) + 5 * rowSize L e

def firstAddr (L : Layout) (e : Interval) := L.mapBase + (max e.first L.chunkStart - L.chunkStart)

def payload (L : Layout) (e : Interval) (addr : ℕ) : Word w :=
  ((1+e.packed+(L.chunkStart+(addr-L.mapBase)-e.first) : ℕ) : Word w)

def writeRow (L : Layout) (e : Interval) (m : Memory w) : Memory w :=
  fillSegment (firstAddr L e) (rowSize L e) (payload L e) m

def FitsRow (e : Interval) (w : ℕ) : Prop := e.group < 2^w ∧ e.first < 2^w ∧ e.stop < 2^w

structure StoresRow (m : Memory w) (a : ℕ) (e : Interval) : Prop where
  group : m a = (e.group : Word w)
  first : m (a+1) = (e.first : Word w)
  stop : m (a+2) = (e.stop : Word w)
  packed : m (a+3) = (e.packed : Word w)

/-- The descriptor cursor varies while the other five inputs and the unit remain fixed. -/
structure Ready (L : Layout) (reg : Fin 15 ↪ Fin r) (c : Config w p r) (a endAddr : ℕ) : Prop where
  cursor : c.reg (reg 0) = (a : Word w)
  stop : c.reg (reg 1) = (endAddr : Word w)
  lo : c.reg (reg 2) = (L.chunkStart : Word w)
  hi : c.reg (reg 3) = (L.chunkEnd : Word w)
  target : c.reg (reg 4) = (L.mapBase : Word w)
  group : c.reg (reg 5) = (L.group : Word w)
  unit : c.reg (reg 6) = 1

structure RecordRegs (reg : Fin 15 ↪ Fin r) (c : Config w p r) (e : Interval) : Prop where
  group : c.reg (reg 7) = (e.group : Word w)
  first : c.reg (reg 8) = (e.first : Word w)
  stop : c.reg (reg 9) = (e.stop : Word w)
  packed : c.reg (reg 10) = (e.packed : Word w)

structure Frame (reg : Fin 15 ↪ Fin r) (c d : Config w p r) : Prop where
  registers : ∀ i, (∀ j, i ≠ reg j) → d.reg i = c.reg i
  persistent : d.persistent = c.persistent
  privateMem : d.privateMem = c.privateMem

theorem Frame.trans {reg : Fin 15 ↪ Fin r} {a b c : Config w p r} (h : Frame reg a b)
    (h' : Frame reg b c) : Frame reg a c :=
  ⟨fun i hi => (h'.registers i hi).trans (h.registers i hi),h'.persistent.trans h.persistent,
    h'.privateMem.trans h.privateMem⟩

theorem frame_fetch (q : Fin p) (reg : Fin 15 ↪ Fin r) (c : Config w p r) (m : Memory w) :
    Frame reg c (fetched q reg m c) := by
  refine ⟨fun i hi => ?_,rfl,rfl⟩
  simp [fetched,fetchWord,Config.put,Function.update_of_ne,hi]

theorem frame_prepare (q : Fin p) (reg : Fin 15 ↪ Fin r) (c : Config w p r) :
    Frame reg c (prepared q reg c) := by
  refine ⟨fun i hi => ?_,rfl,rfl⟩
  simp [prepared,Config.put,Function.update_of_ne,hi]

theorem FillFrame.frame {reg : Fin 15 ↪ Fin r} {c d : Config w p r} (h : FillFrame reg c d) :
    Frame reg c d := ⟨fun i hi => h.registers i (hi 11) (hi 13) (hi 14),h.persistent,h.privateMem⟩

private theorem bump (x : ℕ) : (x : Word w)+1 = ((x+1 : ℕ) : Word w) := by simp

theorem fetched_fields (q : Fin p) (reg : Fin 15 ↪ Fin r) (c : Config w p r) (m : Memory w)
    (L : Layout) (a endAddr : ℕ) (e : Interval) (h : Ready L reg c a endAddr)
    (room : a+4 ≤ endAddr) (fit : endAddr < 2^w) (read : StoresRow m a e) :
    Ready L reg (fetched q reg m c) (a+4) endAddr ∧ RecordRegs reg (fetched q reg m c) e := by
  have h0 : a < 2^w := by omega
  have h1 : a+1 < 2^w := by omega
  have h2 : a+2 < 2^w := by omega
  have h3 : a+3 < 2^w := by omega
  constructor <;> constructor <;>
    simp (config := {decide := true}) [fetched,fetchWord,Config.put,Function.update,
      h.cursor,h.stop,h.lo,h.hi,h.target,h.group,h.unit,bump,
      Fin.val_cast_of_lt h0,Fin.val_cast_of_lt h1,Fin.val_cast_of_lt h2,Fin.val_cast_of_lt h3,
      read.group,read.first,read.stop,read.packed,-Nat.cast_add]

theorem Ready.prepared {L : Layout} {reg : Fin 15 ↪ Fin r} {c : Config w p r} {a endAddr : ℕ}
    (h : Ready L reg c a endAddr) (q : Fin p) : Ready L reg (prepared q reg c) a endAddr := by
  constructor <;> simp (config := {decide := true}) [TickIntervalCursor.prepared,Config.put,Function.update,
    h.cursor,h.stop,h.lo,h.hi,h.target,h.group,h.unit]

theorem Ready.of_fill {L : Layout} {reg : Fin 15 ↪ Fin r} {c d : Config w p r} {a endAddr : ℕ}
    (h : Ready L reg c a endAddr) (fr : FillFrame reg c d) : Ready L reg d a endAddr := by
  have eq (j : Fin 15) (h1 : j ≠ 11) (h2 : j ≠ 13) (h3 : j ≠ 14) :=
    fr.registers (reg j) (reg.injective.ne h1) (reg.injective.ne h2) (reg.injective.ne h3)
  exact ⟨(eq 0 (by decide) (by decide) (by decide)).trans h.cursor,
    (eq 1 (by decide) (by decide) (by decide)).trans h.stop,
    (eq 2 (by decide) (by decide) (by decide)).trans h.lo,
    (eq 3 (by decide) (by decide) (by decide)).trans h.hi,
    (eq 4 (by decide) (by decide) (by decide)).trans h.target,
    (eq 5 (by decide) (by decide) (by decide)).trans h.group,
    (eq 6 (by decide) (by decide) (by decide)).trans h.unit⟩

private theorem cast_min (a b : ℕ) (ha : a < 2^w) (hb : b < 2^w) :
    min (a : Word w) (b : Word w) = ((min a b : ℕ) : Word w) := by
  have h : (a : Word w) ≤ (b : Word w) ↔ a ≤ b := by
    simp [Fin.le_def,Fin.val_cast_of_lt ha,Fin.val_cast_of_lt hb]
  by_cases ab : a ≤ b
  · rw [min_eq_left (h.mpr ab), min_eq_left ab]
  · rw [min_eq_right (le_of_not_ge (mt h.mp ab)), min_eq_right (le_of_not_ge ab)]

private theorem cast_max (a b : ℕ) (ha : a < 2^w) (hb : b < 2^w) :
    max (a : Word w) (b : Word w) = ((max a b : ℕ) : Word w) := by
  have h : (a : Word w) ≤ (b : Word w) ↔ a ≤ b := by
    simp [Fin.le_def,Fin.val_cast_of_lt ha,Fin.val_cast_of_lt hb]
  by_cases ab : a ≤ b
  · rw [max_eq_right (h.mpr ab), max_eq_right ab]
  · rw [max_eq_left (le_of_not_ge (mt h.mp ab)), max_eq_left (le_of_not_ge ab)]

theorem prepared_fields (q : Fin p) (reg : Fin 15 ↪ Fin r) (c : Config w p r)
    (L : Layout) (a endAddr : ℕ) (e : Interval) (h : Ready L reg c a endAddr)
    (regs : RecordRegs reg c e) (fit : L.Fits w) (bounds : FitsRow e w) :
    let d := prepared q reg c
    let lo := max e.first L.chunkStart
    (d.reg (reg 11)).val = lo ∧ (d.reg (reg 12)).val = min e.stop L.chunkEnd ∧
    d.reg (reg 13) = (firstAddr L e : Word w) ∧
    d.reg (reg 14) = ((1+e.packed+(lo-e.first) : ℕ) : Word w) := by
  have hlo := fit.ordered.trans_lt fit.chunk
  have maxFit : max e.first L.chunkStart < 2^w := by have := bounds.2.1; omega
  have minFit : min e.stop L.chunkEnd < 2^w := (min_le_right _ _).trans_lt fit.chunk
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  all_goals simp (config := {decide := true}) [prepared,Config.put,Function.update,
    regs.first,regs.stop,regs.packed,h.lo,h.hi,h.target,cast_max _ _ bounds.2.1 hlo,
    cast_min _ _ bounds.2.2 fit.chunk,Fin.val_cast_of_lt maxFit,Fin.val_cast_of_lt minFit,
    firstAddr,Nat.cast_add,Nat.cast_one,Nat.cast_sub (le_max_left e.first L.chunkStart),
    Nat.cast_sub (le_max_right e.first L.chunkStart)] <;> try abel

end ThreeFlat.RAM.TickIntervalCursor

end OAI
