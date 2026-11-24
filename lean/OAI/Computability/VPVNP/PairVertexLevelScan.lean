import OAI.Computability.VPVNP.PairVertexLevelBounds
import OAI.Computability.VPVNP.PairNodeChildLoop

/-!
# Finding the producing level of a popped DFS node

The native program reads the starting row address of the last level and moves backwards
until the node lies at or above the current start. It uses one external read per tested
level. The successful exit computes the previous level header and the packed site number.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexLevel

open BurstRAM BurstRAM.PrivateRAM TraversalControllerInputs NodeArguments.ChildScan
open scoped Fin.CommRing
open private ReadPrefix ReadPrefix.nil ReadPrefix.tick ReadPrefix.read ReadPrefix.execute
  from OAI.Computability.VPVNP.PairSimulationPrivateSlices

variable {w p r : ℕ}

/-- Read the candidate level's DFS start, compare it with the popped node, and either finish or
step back one level. -/
def scan (pc : Fin 6 → Fin p) (reg : Fin 14 ↪ Fin r) (finish : Fin p) :
    Fin 6 → Instr w p r 11 :=
  ![.binary .add (reg 9) (reg 4) (reg 10) (pc 1), .readExternal (reg 5) (reg 9) (pc 2),
    .jumpLt (reg 0) (reg 5) (pc 3) finish, .binary .sub (reg 4) (reg 4) (reg 2) (pc 4),
    .binary .sub (reg 3) (reg 3) (reg 8) (pc 5), .jumpEq (reg 8) (reg 8) (pc 0) (pc 0)]

/-- Recover the old level, its child-header address, and the node's site ordinal from the
successful scan registers. -/
def finish (pc : Fin 5 → Fin p) (reg : Fin 14 ↪ Fin r) (done : Fin p) :
    Fin 5 → Instr w p r 11 :=
  ![.binary .sub (reg 13) (reg 3) (reg 8) (pc 1), .binary .sub (reg 11) (reg 4) (reg 2) (pc 2),
    .binary .add (reg 12) (reg 11) (reg 10) (pc 3), .binary .sub (reg 9) (reg 0) (reg 5) (pc 4),
    .binary .div (reg 7) (reg 9) (reg 6) done]

theorem resize_scan (pc : Fin 6 → Fin p) (reg : Fin 14 ↪ Fin r) (exit : Fin p) (j : Fin 6) :
    (scan (w := 5) pc reg exit j).resize w = scan pc reg exit j := by fin_cases j <;> rfl

theorem resize_finish (pc : Fin 5 → Fin p) (reg : Fin 14 ↪ Fin r) (done : Fin p) (j : Fin 5) :
    (finish (w := 5) pc reg done j).resize w = finish pc reg done j := by fin_cases j <;> rfl

/-- Events of one descending test, including the read of scalar 14 in the candidate level. -/
def testEvents (pub : Fin 11 → Word w) (m : Memory w) (j : ℕ) : List (Event w) :=
  [.tick, .read (levelHead pub m j + 14) (levelField pub m j 14), .tick]

/-- Test the levels from `j + later` down through `j`, including the final test. -/
def scanEvents (pub : Fin 11 → Word w) (m : Memory w) (j : ℕ) : ℕ → List (Event w)
  | 0 => testEvents pub m j
  | n + 1 => testEvents pub m (j + n + 1) ++ [.tick, .tick, .tick] ++ scanEvents pub m j n

@[simp] theorem scanEvents_length (pub : Fin 11 → Word w) (m : Memory w) (j n : ℕ) :
    (scanEvents pub m j n).length = 6 * n + 3 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [scanEvents, testEvents, ih]; omega

@[simp] theorem scanEvents_probes (pub : Fin 11 → Word w) (m : Memory w) (j n : ℕ) :
    countProbes (scanEvents pub m j n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [scanEvents, testEvents, countProbes, ih]; omega

@[simp] theorem scanEvents_choices (pub : Fin 11 → Word w) (m : Memory w) (j n : ℕ) :
    choiceBits (scanEvents pub m j n) = [] := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [scanEvents, testEvents, choiceBits] using ih

/-- Register invariant of the descending locator, recording the popped node, terminal geometry,
and the level currently being tested. -/
structure ScanState (pub : Fin 11 → Word w) (m : Memory w) (reg : Fin 14 ↪ Fin r)
    (node : Word w) (i : ℕ) (c : Config w p r) : Prop where
  node : c.reg (reg 0) = node
  header : c.reg (reg 1) = terminalHead pub
  pitch : c.reg (reg 2) = terminalField pub m 17
  index : c.reg (reg 3) = (i : Word w)
  current : c.reg (reg 4) = levelHead pub m i
  stride : c.reg (reg 6) = terminalField pub m 15
  one : c.reg (reg 8) = 1
  offset : c.reg (reg 10) = 14

/-- Frame condition preserving registers outside the locator bank, private memory, and
persistent state during level lookup. -/
structure Frame (reg : Fin 14 ↪ Fin r) (c d : Config w p r) : Prop where
  outside : ∀ i, i ∉ Set.range reg → d.reg i = c.reg i
  privateMem : d.privateMem = c.privateMem
  persistent : d.persistent = c.persistent

theorem Frame.trans {reg : Fin 14 ↪ Fin r} {c d out : Config w p r}
    (f : Frame reg c d) (g : Frame reg d out) : Frame reg c out :=
  ⟨fun i hi => (g.outside i hi).trans (f.outside i hi), g.privateMem.trans f.privateMem,
    g.persistent.trans f.persistent⟩

variable {M : Machine w p r 11} {pc : Fin 6 → Fin p} {reg : Fin 14 ↪ Fin r}
    {exit : Fin p} {m : Memory w} {node : Word w}

private theorem scan_at (link : ∀ i, M.code (pc i) = scan pc reg exit i)
    (i : Fin 6) (c : Config w p r) (hc : c.pc = pc i) :
    M.program.step c = (scan pc reg exit i).run M.publicData c := by
  simp only [Machine.program, hc, link]

private theorem test (link : ∀ i, M.code (pc i) = scan pc reg exit i)
    {i : ℕ} (c : Config w p r) (hc : c.pc = pc 0) (st : ScanState M.publicData m reg node i c) :
    ∃ d, Prefix M m c d [] (testEvents M.publicData m i) ∧
      d.pc = (if node < levelField M.publicData m i 14 then pc 3 else exit) ∧
      d.reg (reg 5) = levelField M.publicData m i 14 ∧
      ScanState M.publicData m reg node i d ∧ Frame reg c d := by
  let addr := levelHead M.publicData m i + 14
  let value := levelField M.publicData m i 14
  let x := c.put (pc 1) (reg 9) addr
  let y := x.put (pc 2) (reg 5) value
  let d : Config w p r := {y with pc := if node < value then pc 3 else exit}
  have hs₀ : M.program.step c = .localStep x := by
    rw [scan_at link 0 c hc]
    change CallAction.localStep (c.put _ _ (c.reg (reg 4) + c.reg (reg 10))) = _
    rw [st.current, st.offset]
  have hs₁ : M.program.step x = .read addr (fun v => x.put (pc 2) (reg 5) v) := by
    rw [scan_at link 1 x rfl]
    change CallAction.read (x.reg (reg 9)) _ = _
    rw [show x.reg (reg 9) = addr by simp [x]]
  have hs₂ : M.program.step y = .localStep d := by
    rw [scan_at link 2 y rfl]
    change CallAction.localStep {y with pc := if y.reg (reg 0) < y.reg (reg 5) then _ else _} = _
    simp [d, y, x, Config.put, st.node]
  have pre : ReadPrefix M m c (testEvents M.publicData m i) d :=
    ReadPrefix.tick hs₀ (ReadPrefix.read addr hs₁ (ReadPrefix.tick hs₂ (ReadPrefix.nil _)))
  have same (l : Fin 14) (h₅ : l ≠ 5) (h₉ : l ≠ 9) : d.reg (reg l) = c.reg (reg l) := by
    simp [d, y, x, Config.put, h₅, h₉]
  refine ⟨d, ReadPrefix.execute pre, rfl, by simp [d, y, value],
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, rfl, rfl⟩⟩
  all_goals first | exact (same _ (by decide) (by decide)).trans st.node
                  | exact (same _ (by decide) (by decide)).trans st.header
                  | exact (same _ (by decide) (by decide)).trans st.pitch
                  | exact (same _ (by decide) (by decide)).trans st.index
                  | exact (same _ (by decide) (by decide)).trans st.current
                  | exact (same _ (by decide) (by decide)).trans st.stride
                  | exact (same _ (by decide) (by decide)).trans st.one
                  | exact (same _ (by decide) (by decide)).trans st.offset
                  | skip
  intro l hl
  have h₅ : l ≠ reg 5 := fun e => hl ⟨5, e.symm⟩
  have h₉ : l ≠ reg 9 := fun e => hl ⟨9, e.symm⟩
  simp [d, y, x, Config.put, Function.update_of_ne h₅, Function.update_of_ne h₉]

private theorem descend (link : ∀ i, M.code (pc i) = scan pc reg exit i)
    {i : ℕ} (c : Config w p r) (hc : c.pc = pc 3)
    (st : ScanState M.publicData m reg node (i + 1) c) :
    ∃ d, Prefix M m c d [] [.tick, .tick, .tick] ∧ d.pc = pc 0 ∧
      ScanState M.publicData m reg node i d ∧ Frame reg c d := by
  let x := c.put (pc 4) (reg 4) (levelHead M.publicData m i)
  let y := x.put (pc 5) (reg 3) (i : Word w)
  let d : Config w p r := {y with pc := pc 0}
  have hs₀ : M.program.step c = .localStep x := by
    rw [scan_at link 3 c hc]
    change CallAction.localStep (c.put _ _ (c.reg (reg 4) - c.reg (reg 2))) = _
    rw [st.current, st.pitch]
    congr 3
    simp [levelHead, add_mul, ← add_assoc]
  have hs₁ : M.program.step x = .localStep y := by
    rw [scan_at link 4 x rfl]
    change CallAction.localStep (x.put _ _ (x.reg (reg 3) - x.reg (reg 8))) = _
    simp [y, x, Config.put, st.index, st.one]
  have hs₂ : M.program.step y = .localStep d := by
    rw [scan_at link 5 y rfl]
    change CallAction.localStep {y with pc := if _ then pc 0 else pc 0} = _
    simp [d]
  have pre : ReadPrefix M m c [.tick, .tick, .tick] d :=
    ReadPrefix.tick hs₀ (ReadPrefix.tick hs₁ (ReadPrefix.tick hs₂ (ReadPrefix.nil _)))
  refine ⟨d, ReadPrefix.execute pre, rfl, ?_, ⟨?_, rfl, rfl⟩⟩
  · constructor <;> simp [d, y, x, Config.put, st.node, st.header, st.pitch, st.stride,
      st.one, st.offset]
  · intro l hl
    have h₃ : l ≠ reg 3 := fun e => hl ⟨3, e.symm⟩
    have h₄ : l ≠ reg 4 := fun e => hl ⟨4, e.symm⟩
    simp [d, y, x, Config.put, Function.update_of_ne h₃, Function.update_of_ne h₄]

/-- Run the descending scan. Empty levels above the selected row are tested normally. -/
theorem scan_run (link : ∀ i, M.code (pc i) = scan pc reg exit i)
    (j n : ℕ) (c : Config w p r) (hc : c.pc = pc 0)
    (st : ScanState M.publicData m reg node (j + n) c)
    (start : levelField M.publicData m j 14 ≤ node)
    (later : ∀ i, j < i → i ≤ j + n → node < levelField M.publicData m i 14) :
    ∃ out, Prefix M m c out [] (scanEvents M.publicData m j n) ∧ out.pc = exit ∧
      out.reg (reg 5) = levelField M.publicData m j 14 ∧
      ScanState M.publicData m reg node j out ∧ Frame reg c out := by
  induction n generalizing c with
  | zero =>
    obtain ⟨d, path, pc', base, s, f⟩ := test link c hc st
    exact ⟨d, path, by simpa [start.not_gt] using pc', base, s, f⟩
  | succ n ih =>
    obtain ⟨d, pre, pc', _, s, f⟩ := test link c hc st
    have lt := later (j + n + 1) (by omega) (by omega)
    have go : d.pc = pc 3 := by simpa [← Nat.add_assoc, lt] using pc'
    obtain ⟨y, down, back, state, frame⟩ := descend link d go s
    obtain ⟨out, path, done, base, so, fo⟩ :=
      ih y back state (fun i hi bound => later i hi (by omega))
    exact ⟨out, (pre.trans down).trans path, done, base, so, f.trans (frame.trans fo)⟩

end PairSimulation.VertexLevel

end VPVNP
end Computability
end OAI
