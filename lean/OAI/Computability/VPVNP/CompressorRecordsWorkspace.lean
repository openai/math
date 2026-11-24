import OAI.Computability.VPVNP.CompressorRecordsController
import OAI.Computability.VPVNP.CompressorRecordsSchedule

/-!
# The pair workspace as the compressor scheduler's native parameter bank

Public word two of the eleven-word pair ABI points to the workspace.
Its first six words supply the scheduler's parameters. The following three
words hold its tag, ordinal and row count. The active frame occupies the
next maximum-arity-plus-one words. One reserved word separates the frame
from the directory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Workspace

open BurstRAM BurstRAM.PrivateRAM
open scoped Fin.CommRing

variable {w d : ℕ}

/-- Locate the scheduler's active frame, directory, ordinal, row count, and tag relative to the
pair workspace base, allowing room for the maximum worker arity. -/
def ports (g : ℕ) (base : Word w) : Schedule.Ports w :=
  ⟨base+9, base+((11+g : ℕ) : Word w), base+7, base+8, base+6⟩

/-- The six public scheduler pointers stored in the workspace header. The internal scheduler
tag and its stage linker share one tag cell. -/
def bank (g : ℕ) (base : Word w) : Fin 6 → Word w :=
  LiveStageLink.publicData (ports g base).data (ports g base).tag

/-- The header's two tag parameters refer to the same external cell. -/
def Installed (g : ℕ) (base : Word w) (m : Memory w) : Prop :=
  (Frame.data base m : Fin 6 → Word w) = bank g base

variable (C : Schedule.Catalog d)

private abbrev inner := Schedule.template C (Controller.table (Schedule.arity C))

/-- The only public operand accessed by the enclosing frame loader is word two. -/
def table := LiveStageLink.widen (Frame.compile (inner C)) (Function.Embedding.refl _)
  (fun _ : Fin 1 ↦ (2 : Fin 11))

/-- Prefix a scheduler report with the events that load its six parameter words from the
workspace header. -/
def report (base : Word w) (m : Memory w) (rep : Report w) : Report w :=
  LiveStageLink.prependLog (Frame.loadEvents base m 0 6) rep

theorem execute_dispatch (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    (bits : List Bool) (cap : ℕ) (h : Installed (Schedule.arity C) (pub 2) m) :
    let W := ((table C).instantiate w pub).program
    let S := (Schedule.machine C (Controller.table (Schedule.arity C)) (ports (Schedule.arity C) (pub 2))).program
    execute W cap (W.start s) m bits =
      (execute S (cap-24) (S.start s) m bits).map (report (pub 2) m) := by
  dsimp only [table]
  rw [LiveStageLink.execute_widen_start]
  change execute (Frame.machine (inner C) (pub 2)).program cap
    ((Frame.machine (inner C) (pub 2)).program.start s) m bits = _
  rw [Frame.execute_cap, show (Frame.data (pub 2) m : Fin 6 → Word w) = _ from h]
  rfl

theorem report_effect (base : Word w) (m : Memory w) (rep : Report w) :
    (report base m rep).events.length = 24+rep.events.length ∧
      (report base m rep).probes = 6+rep.probes ∧
      choiceBits (report base m rep).events = choiceBits rep.events ∧
      after m (report base m rep).events = after m rep.events ∧
      (report base m rep).result = rep.result := Frame.frame_cost base m 0 6 rep

/-- A successful scheduler report with its exact branch stream lifts at a cost of
six external reads and eighteen private ticks. -/
theorem execute_dispatch_of (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    (bits : List Bool) (fuel : ℕ) (h : Installed (Schedule.arity C) (pub 2) m) (rep : Report w)
    (run : let S := (Schedule.machine C (Controller.table (Schedule.arity C))
        (ports (Schedule.arity C) (pub 2))).program
      execute S fuel (S.start s) m bits = some rep) :
    let W := ((table C).instantiate w pub).program
    execute W (fuel+24) (W.start s) m bits = some (report (pub 2) m rep) := by
  dsimp only at run ⊢
  rw [execute_dispatch C pub s m bits _ h, Nat.add_sub_cancel, run]
  rfl

/-- Offsets from the workspace base stored in the header. The last two cells
are control words initialized to zero. Row count at offset eight comes from
the level-directory constructor. -/
private def offset (g : ℕ) : Fin 8 → ℕ := ![9,11+g,7,8,6,6,0,0]

/-- Value installed in one of the first eight workspace cells. The first six hold scheduler
pointers, followed by the initial zero tag and ordinal. -/
def headerWord (g : ℕ) (base : Word w) (i : Fin 8) : Word w :=
  (if i.val < 6 then base else 0) + ((offset g i : ℕ) : Word w)

theorem headerWord_bank (g : ℕ) (base : Word w) (j : Fin 6) :
    headerWord g base (j.castLE (by decide)) = bank g base j := by
  fin_cases j <;> simp [headerWord, offset, bank, ports, LiveStageLink.publicData, Schedule.Ports.data]

private def width (g : ℕ) := Nat.clog 2 (g+12)
private theorem literal_fit (g i : ℕ) (h : i < g+12) : i < 2^width g :=
  h.trans_le (Nat.le_pow_clog (by decide : 1 < 2) _)

private def cell (j : Fin 8) (phase : Fin 5) : Fin 42 := (finProdFinEquiv (j,phase)).natAdd 2
private def next (j : ℕ) : Fin 42 := if h : j < 8 then cell ⟨j,h⟩ 0 else 1

private def cellCode (g : ℕ) (j : Fin 8) : Fin 5 → Instr (width g) 42 4 11
  | 0 => .constant 1 (Fin.ofNat _ j.val) (cell j 1)
  | 1 => .binary .add 1 0 1 (cell j 2)
  | 2 => .constant 2 (Fin.ofNat _ (offset g j)) (cell j 3)
  | 3 => .binary .add 2 (if j.val < 6 then 0 else 3) 2 (cell j 4)
  | 4 => .writeExternal 1 2 (next (j.val+1))

/-- One native call installs the six pointers and resets the scheduler's tag
and ordinal. Its accepting exit allows the outer linker to enter the next stage. -/
def initTable (g : ℕ) : Template 42 4 11 where
  literalWidth := width g
  entry := 0
  code := Fin.addCases (m := 2) (n := 40) (fun i ↦ if i.val = 0 then .publicWord 0 2 (next 0) else .accept)
    (fun k ↦ let p := finProdFinEquiv.symm k; cellCode g p.1 p.2)

/-- Instantiate the header initializer at the chosen word width using the pair ABI's public
words and maximum worker arity. -/
abbrev initMachine (g : ℕ) (pub : Fin 11 → Word w) := (initTable g).instantiate w pub

private theorem code_cell (g : ℕ) (pub : Fin 11 → Word w) (j : Fin 8) (i : Fin 5) :
    (initMachine g pub).code (cell j i) = (cellCode g j i).resize w := by
  simp [initMachine, initTable, cell, Template.instantiate]

private theorem code_end (g : ℕ) (pub : Fin 11 → Word w) :
    (initMachine g pub).code 1 = .accept := rfl

private def events (g : ℕ) (base : Word w) (i : ℕ) : ℕ → List (Event w)
  | 0 => []
  | n+1 =>
    let j : Fin 8 := Fin.ofNat _ i
    [.tick,.tick,.tick,.tick,.write (base+(i : Word w)) (headerWord g base j)] ++ events g base (i+1) n

/-- Accepting initialization report recording eight header writes to install the scheduler
pointers and reset its tag and ordinal. -/
def initReport (g : ℕ) (base : Word w) : Report w :=
  ⟨.tick :: events g base 0 8, none⟩

private theorem write_one (g : ℕ) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    (rs : Fin 4 → Word w) (z : rs 3 = 0) (j : Fin 8) (bs : List Bool) (f : ℕ) :
    let a := rs 0 + (j.val : Word w)
    let v := headerWord g (rs 0) j
    execute (initMachine g pub).program (f+5) ⟨next j.val,s,rs,fun _ ↦ 0⟩ m bs =
      (execute (initMachine g pub).program f ⟨next (j.val+1),s,
        Function.update (Function.update rs 1 a) 2 v,fun _ ↦ 0⟩ (writeMemory m a v) bs).map
        (LiveStageLink.prependLog [.tick,.tick,.tick,.tick,.write a v]) := by
  have hj := literal_fit g j.val (by have := j.isLt; omega)
  have ho := literal_fit g (offset g j) (by fin_cases j <;> simp [offset]; omega)
  rw [show next j.val = cell j 0 by simp [next,j.isLt]]
  by_cases h : j.val < 6 <;>
    simp (config := {decide := true}) [execute, Machine.program, code_cell, cellCode, Instr.resize,
      Instr.run, Config.put, BinaryOp.eval, Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt ho, h, z,
      Function.update_idem, Function.comp_def, Report.prepend, headerWord] <;> rfl

private theorem init_tail (g : ℕ) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    (rs : Fin 4 → Word w) (z : rs 3 = 0) (bs : List Bool) (f i n : ℕ) (hlen : i+n = 8) :
    execute (initMachine g pub).program (f+1+5*n) ⟨next i,s,rs,fun _ ↦ 0⟩ m bs =
      if bs = [] then some ⟨events g (rs 0) i n,none⟩ else none := by
  induction n generalizing i rs m with
  | zero =>
    simp only [Nat.add_zero] at hlen
    subst i
    simp [next, events, execute, Machine.program, code_end, Instr.run]
  | succ n ih =>
    let j : Fin 8 := ⟨i,by omega⟩
    have hj : Fin.ofNat 8 i = j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
    rw [show f+1+5*(n+1) = (f+1+5*n)+5 by omega, write_one g pub s m rs z j bs,
      ih _ _ (by simpa (config := {decide := true})) (i+1) (by omega)]
    by_cases h : bs = [] <;> simp (config := {decide := true}) [h, events, LiveStageLink.prependLog, j]
    exact congrArg (headerWord g (rs 0)) hj.symm

/-- The initializer executes exactly one deterministic accepting history at every
sufficient instruction cap. -/
theorem execute_init (g : ℕ) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    (bs : List Bool) (cap : ℕ) (budget : 42 ≤ cap) :
    execute (initMachine g pub).program cap ((initMachine g pub).program.start s) m bs =
      if bs = [] then some (initReport g (pub 2)) else none := by
  obtain ⟨f,rfl⟩ : ∃ f, cap = (f+1+5*8)+1 := ⟨cap-42,by omega⟩
  rw [execute]
  have hs : (initMachine g pub).program.step ((initMachine g pub).program.start s) =
      .localStep ⟨next 0,s,Function.update (fun _ ↦ 0) 0 (pub 2),fun _ ↦ 0⟩ := rfl
  simp only [hs]
  let rs : Fin 4 → Word w := Function.update (fun _ ↦ 0) 0 (pub 2)
  have hz : rs 3 = 0 := by simp (config := {decide := true}) [rs]
  rw [init_tail g pub s m rs hz bs f 0 8 (by decide)]
  by_cases h : bs = [] <;> simp [h, initReport, Report.prepend, rs]

theorem initReport_cost (g : ℕ) (base : Word w) :
    (initReport g base).events.length = 41 ∧ (initReport g base).probes = 8 ∧
      choiceBits (initReport g base).events = [] := ⟨rfl,rfl,rfl⟩

private theorem events_outside (g : ℕ) (base : Word w) (m : Memory w) (a i n : ℕ)
    (h : ∀ t, i ≤ t → t < i+n → a ≠ (base+(t : Word w)).val) :
    after m (events g base i n) a = m a := by
  induction n generalizing i m with
  | zero => rfl
  | succ n ih =>
    change after (writeMemory m (base+(i : Word w)) _) (events g base (i+1) n) a = m a
    rw [ih _ (i+1) (fun t h₁ h₂ ↦ h t (by omega) (by omega))]
    simp [writeMemory, h i le_rfl (by omega)]

theorem init_outside (g : ℕ) (base : Word w) (m : Memory w) (a : ℕ)
    (h : ∀ i : Fin 8, a ≠ (base+(i.val : Word w)).val) :
    after m (initReport g base).events a = m a :=
  events_outside g base m a 0 8 fun t _ ht ↦ h ⟨t, by omega⟩

private theorem address_ne (base : Word w) {i j : ℕ}
    (hi : i < 2^w) (hj : j < 2^w) (hne : i ≠ j) :
    (base+(i : Word w)).val ≠ (base+(j : Word w)).val := by
  intro e
  have hx : (i : Word w) = (j : Word w) := add_left_cancel (Fin.ext e)
  have hv := congrArg Fin.val hx
  simp only [Fin.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at hv
  exact hne hv

private theorem events_at (g : ℕ) (base : Word w) (m : Memory w) (k : Fin 8) (i n : ℕ)
    (lo : i ≤ k.val) (hi : k.val < i+n) (last : i+n = 8) (fit : 8 ≤ 2^w) :
    after m (events g base i n) (base+(k.val : Word w)).val = headerWord g base k := by
  induction n generalizing m i with
  | zero => omega
  | succ n ih =>
    change after (writeMemory m (base+(i : Word w)) _) (events g base (i+1) n) _ = _
    by_cases e : k.val = i
    · subst i
      rw [events_outside]
      · simp [writeMemory]
      · intro t h₁ h₂
        exact address_ne base (k.isLt.trans_le fit) (by omega) (by omega)
    · exact ih _ (i+1) (by omega) (by omega) (by omega)

/-- The eight contiguous installed words, including the two mutable control cells. -/
theorem init_cell (g : ℕ) (base : Word w) (m : Memory w) (i : Fin 8) (fit : 8 ≤ 2^w) :
    after m (initReport g base).events (base+(i.val : Word w)).val = headerWord g base i :=
  events_at g base m i 0 8 (by omega) i.isLt rfl fit

/-- The scheduler sees the computed pointer bank on its very first call. -/
theorem init_installed (g : ℕ) (base : Word w) (m : Memory w) (fit : 8 ≤ 2^w) :
    Installed g base (after m (initReport g base).events) := by
  funext i
  exact (init_cell g base m (i.castLE (by decide)) fit).trans (headerWord_bank g base i)

theorem init_controls (g : ℕ) (base : Word w) (m : Memory w) (fit : 8 ≤ 2^w) :
    after m (initReport g base).events (ports g base).tag.val = 0 ∧
      after m (initReport g base).events (ports g base).ordinal.val = 0 := by
  constructor
  · simpa [ports, headerWord, offset] using init_cell g base m 6 fit
  · simpa [ports, headerWord, offset] using init_cell g base m 7 fit

theorem init_rowCount (g : ℕ) (base : Word w) (m : Memory w) (fit : 8 < 2^w) :
    after m (initReport g base).events (ports g base).rows.val = m (ports g base).rows.val := by
  apply init_outside
  intro i
  exact address_ne base (i := 8) fit (i.isLt.trans fit) (by have := i.isLt; omega)

/-- Reuse of the header on later calls only requires that the six pointer cells
retain their values. The internal tag and ordinal may change on every row. -/
theorem Installed.preserve {g : ℕ} {base : Word w} {m m' : Memory w} (h : Installed g base m)
    (keep : ∀ i : Fin 6, m' (base+(i.val : Word w)).val = m (base+(i.val : Word w)).val) :
    Installed g base m' := (funext keep : (Frame.data base m' : Fin 6 → Word w) = Frame.data base m).trans h

/-- Consecutive native initialization and dispatch, using the memory left by the
initializer. The input row count and all precomputed directory entries may already
be present when initialization starts. -/
theorem execute_initialized (pub : Fin 11 → Word w) (initState state : Word w)
    (m : Memory w) (fit : 8 ≤ 2^w) (bits : List Bool) (cap : ℕ) :
    let g := Schedule.arity C
    let base := pub 2
    let setup := (initMachine g pub).program
    let m' := after m (initReport g base).events
    let W := ((table C).instantiate w pub).program
    let S := (Schedule.machine C (Controller.table g) (ports g base)).program
    execute setup 42 (setup.start initState) m [] = some (initReport g base) ∧
      execute W cap (W.start state) m' bits =
        (execute S (cap-24) (S.start state) m' bits).map (report base m') := by
  constructor
  · exact execute_init (Schedule.arity C) pub initState m [] 42 le_rfl
  · exact execute_dispatch C pub state _ bits cap (init_installed _ _ _ fit)

/-- After installing the workspace, the online scheduler begins at the calendar
stage whose tag follows the `d` data-worker tags. -/
def calendarStart (d : ℕ) : Template 6 3 11 where
  literalWidth := Nat.clog 2 (d+8)
  entry := 0
  code pc := match pc.val with
    | 0 => .publicWord 0 2 1
    | 1 => .constant 1 (Fin.ofNat _ 6) 2
    | 2 => .binary .add 1 0 1 3
    | 3 => .constant 2 (Fin.ofNat _ (d+1)) 4
    | 4 => .writeExternal 1 2 5
    | _ => .accept

/-- Accepting report for starting the calendar stage, with four private ticks and a write of
tag `d+1` at workspace offset six. -/
def calendarReport (d : ℕ) (base : Word w) : Report w :=
  ⟨[.tick,.tick,.tick,.tick,.write (base+6) ((d+1 : ℕ) : Word w)],none⟩

theorem execute_calendarStart (d : ℕ) (pub : Fin 11 → Word w) (s : Word w) (m : Memory w)
    (bits : List Bool) (cap : ℕ) (budget : 6 ≤ cap) :
    let M := (calendarStart d).instantiate w pub
    execute M.program cap (M.program.start s) m bits =
      if bits = [] then some (calendarReport d (pub 2)) else none := by
  obtain ⟨f,rfl⟩ : ∃ f, cap = f+6 := ⟨cap-6,by omega⟩
  let M := (calendarStart d).instantiate w pub
  have fit := Nat.le_pow_clog (by decide : 1 < 2) (d+8)
  have const₆ : M.code 1 = .constant 1 6 2 := by
    change Instr.constant _ (Fin.ofNat (2^w) (6 % 2^Nat.clog 2 (d+8))) _ = _
    rw [Nat.mod_eq_of_lt (by omega)]
    rfl
  have constTag : M.code 3 = .constant 2 ((d+1 : ℕ) : Word w) 4 := by
    change Instr.constant _ (Fin.ofNat (2^w) ((d+1) % 2^Nat.clog 2 (d+8))) _ = _
    rw [Nat.mod_eq_of_lt (by omega)]
    rfl
  have p0 : M.code 0 = .publicWord 0 2 1 := rfl
  have p2 : M.code 2 = .binary .add 1 0 1 3 := rfl
  have p4 : M.code 4 = .writeExternal 1 2 5 := rfl
  have p5 : M.code 5 = .accept := rfl
  change execute M.program (f+6) ⟨0,s,fun _ ↦ 0,fun _ ↦ 0⟩ m bits = _
  by_cases h : bits = [] <;>
    simp (config := {decide := true}) [execute, Machine.program, p0, p2, p4, p5,
      const₆, constTag, Instr.run, Config.put, BinaryOp.eval, h, calendarReport, Report.prepend, M]
  rfl

theorem calendar_effect (d g : ℕ) (base : Word w) (m : Memory w) :
    after m (calendarReport d base).events =
      writeMemory m (ports g base).tag ((d+1 : ℕ) : Word w) ∧
      (calendarReport d base).probes = 1 ∧ choiceBits (calendarReport d base).events = [] := ⟨rfl,rfl,rfl⟩

theorem calendar_installed (d g : ℕ) (base : Word w) (m : Memory w)
    (h : Installed g base m) (fit : 6 < 2^w) :
    Installed g base (after m (calendarReport d base).events) := by
  apply h.preserve
  intro i
  rw [(calendar_effect d g base m).1]
  have hi := i.isLt
  change writeMemory m (base+(6 : Word w)) _ (base+(i.val : Word w)).val = _
  exact ite_eq_right (address_ne base (i := i.val) (j := 6) (by omega) fit (by omega))

end CompressorRecords.Workspace

end VPVNP
end Computability
end OAI
