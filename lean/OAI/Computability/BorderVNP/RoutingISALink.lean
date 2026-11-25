import OAI.Computability.BorderVNP.RoutingISARuns

/-!
# Instruction fetching in linked evaluator fragments

A fragment occupies a half-open interval of the fixed instruction table.
Its final label can be the next fragment's entry or the enclosing loop test.
The decoder preserves the runtime word bank and chronological events.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w p : ℕ}

/-- Interpret one fixed ordinary/signed opcode row at the current machine state. -/
def fetchLine (row : Line p) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : TeamOpcode.State w p 64) : TeamRAM.Instr w (TeamOpcode.State w p 64) :=
  match row.2 with
  | .native => if TeamOpcode.enabled row.1 s then
      TeamOpcode.nativeAction ((row.1.resize w).runLogged pub s.logged) else .reject
  | .sign b next => .localStep {s with pc := next} (if b then .minus else .plus)
  | .call j a l next => .call (s.reg a) (s.reg l).val (macros j) {s with pc := next}
  | .callReg idReg a l next =>
    match TeamOpcodeSelect.select 8 (s.reg idReg).val with
    | some j => .call (s.reg a) (s.reg l).val (macros j) {s with pc := next}
    | none => .reject

/-- Interpret an indexed table without changing the runtime instruction semantics. -/
def fetch (rows : Fin p → Line p) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : TeamOpcode.State w p 64) : TeamRAM.Instr w (TeamOpcode.State w p 64) :=
  fetchLine (rows s.pc) pub macros s

/-- Fetch of the assembled table uses the standard signed team dispatcher. -/
theorem fetch_row (c : Code) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : TeamOpcode.State w (c.slots+1) 64) :
    fetch c.row pub macros s = c.program.fetch pub macros s := by
  cases h : (c.row s.pc).2 <;> simp [fetch, fetchLine, Code.program, TeamOpcode.Program.fetch, h]
  all_goals first | rfl | (split <;> rename_i he <;> simp [he])

/-- Install a fixed continuation on every successful transition of a primitive
statement. No chronological memory event or private choice changes. -/
def resume (pc : Fin p) : TeamRAM.Instr w (Bank w) → TeamRAM.Instr w (TeamOpcode.State w p 64)
  | .accept => .accept
  | .reject => .reject
  | .localStep next b => .localStep ⟨pc, next⟩ b
  | .choose f => .choose fun b ↦ ⟨pc, f b⟩
  | .load a f => .load a fun v ↦ ⟨pc, f v⟩
  | .store a v s => .store a v ⟨pc, s⟩
  | .call a q run s => .call a q run ⟨pc, s⟩

/-- Installing the next PC preserves the requested memory operation. -/
theorem resume_action (pc : Fin p) (i : TeamRAM.Instr w (Bank w)) :
    (resume pc i).action = i.action := by cases i <;> rfl

/-- A resumed opcode carries exactly the same new bank and path sign. -/
theorem resume_advance (pc : Fin p) (i : TeamRAM.Instr w (Bank w))
    (bits : List Bool) (vs : List (Word w)) :
    (resume pc i).advance bits vs = (i.advance bits vs).map fun (s,b) ↦ (⟨pc,s⟩,b) := by
  cases i <;> cases bits <;> cases vs <;>
    simp [resume, TeamRAM.Instr.advance]
  all_goals first | rename_i tail; cases tail <;> rfl | split <;> simp_all [Function.comp_def]


/-- Fetching a primitive row gives its word operation with the linked continuation. -/
theorem fetch_atom (label : ℕ → Fin p) (pc start finish : ℕ) (c : Code)
    (hc : c.isAtom = true) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (s : Bank w) :
    fetchLine (c.emit label pc start finish) pub macros ⟨label pc,s⟩ =
      resume (label finish) (c.atom pub macros s) := by
  cases c <;> try contradiction
  case binary op d x y =>
    cases op <;> by_cases hz : s y = 0 <;>
      simp [Code.emit, Code.atom, fetchLine, TeamOpcode.enabled, TeamOpcode.permitted,
        TeamOpcode.divisor, Instr.resize, Instr.runLogged, Instr.nextLog, Instr.run,
        TeamOpcode.State.logged, TeamOpcode.nativeAction, CallAction.mapState, Config.put,
        LogConfig.denote, resume, hz]
  all_goals
    simp [Code.emit, Code.atom, fetchLine, TeamOpcode.enabled, TeamOpcode.permitted,
      TeamOpcode.divisor, Instr.resize, Instr.runLogged, Instr.nextLog, Instr.run,
      TeamOpcode.State.logged, TeamOpcode.nativeAction, CallAction.mapState, Config.put,
      LogConfig.denote, resume]

/-- The equality test changes only the program counter. -/
theorem fetch_jumpEq (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (pc a b : Fin p) (s : Bank w) (x y : Reg) :
    fetchLine (.jumpEq x y a b, .native) pub macros ⟨pc,s⟩ =
      .localStep ⟨if s x = s y then a else b, s⟩ .plus := by
  rfl

/-- The unsigned less-than test changes only the program counter. -/
theorem fetch_jumpLt (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (pc a b : Fin p) (s : Bank w) (x y : Reg) :
    fetchLine (.jumpLt x y a b, .native) pub macros ⟨pc,s⟩ =
      .localStep ⟨if s x < s y then a else b, s⟩ .plus := by
  rfl

/-- A guess chooses one of two fixed destinations, preserving the registers. -/
theorem fetch_choose (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (pc a b : Fin p) (s : Bank w) :
    fetchLine (.choose a b, .native) pub macros ⟨pc,s⟩ =
      .choose fun v ↦ ⟨if v then a else b, s⟩ := by rfl

/-- All fetched rows in the fragment's interval are the fixed rows emitted
for this fragment, including the jump to its enclosing continuation. -/
def Contains (rows : Fin p → Line p) (label : ℕ → Fin p) (start finish : ℕ) (c : Code) : Prop :=
  ∀ i, start ≤ i → i < start+c.slots → rows (label i) = c.emit label i start finish

private theorem NativePrefix.jump {S : Type*} {P : S → TeamRAM.Instr w S} {s m q es z mz}
    (hp : P s = .localStep q .plus) (tail : NativePrefix P q m es z mz) :
    NativePrefix P s m (tick w :: es) z mz :=
  .cons (by rw [hp]; rfl) (by rw [hp]; rfl) tail

private theorem NativePrefix.guess {S : Type*} {P : S → TeamRAM.Instr w S} {s m f es z mz} (b : Bool)
    (hp : P s = .choose f) (tail : NativePrefix P (f b) m es z mz) :
    NativePrefix P s m (choiceTick w b :: es) z mz :=
  .cons (by rw [hp]; rfl) (by rw [hp]; rfl) tail

/-- The true branch occupies the interval immediately after its test. -/
theorem Contains.forkLeft {rows : Fin p → Line p} {label : ℕ → Fin p}
    {c a b : Code} {start finish : ℕ} (hc : Contains rows label start finish c)
    (size : c.slots = 1 + a.slots + b.slots)
    (emit : ∀ i, start < i → i < start+1+a.slots →
      c.emit label i start finish = a.emit label i (start+1) finish) :
    Contains rows label (start+1) finish a := by
  intro i hlo hhi
  exact (hc i (by omega) (by omega)).trans (emit i (by omega) hhi)

/-- The false branch follows the test and the entire true branch. -/
theorem Contains.forkRight {rows : Fin p → Line p} {label : ℕ → Fin p}
    {c a b : Code} {start finish : ℕ} (hc : Contains rows label start finish c)
    (size : c.slots = 1 + a.slots + b.slots)
    (emit : ∀ i, start < i → start+1+a.slots ≤ i →
      c.emit label i start finish = b.emit label i (start+1+a.slots) finish) :
    Contains rows label (start+1+a.slots) finish b := by
  intro i hlo hhi
  exact (hc i (by omega) (by omega)).trans (emit i (by omega) hlo)

/-- Fetch the entry of a fragment from the containing table. -/
theorem fetch_entry {rows : Fin p → Line p} {label : ℕ → Fin p} {start finish : ℕ}
    {c : Code} (hc : Contains rows label start finish c) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (s : Bank w) :
    fetch rows pub macros ⟨label start,s⟩ =
      fetchLine (c.emit label start start finish) pub macros ⟨label start,s⟩ := by
  exact congrArg (fun l ↦ fetchLine l pub macros ⟨label start,s⟩)
    (hc start le_rfl (Nat.lt_add_of_pos_right c.slots_pos))

/-- Every normal structured execution is the actual word-ISA path in any
instruction table that contains the fragment at the given interval. -/
theorem Runs.nativePrefix {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} (run : Runs pub macros c s m es t mt)
    (rows : Fin p → Line p) (label : ℕ → Fin p) {start finish : ℕ}
    (hc : Contains rows label start finish c) :
    NativePrefix (fetch rows pub macros) ⟨label start,s⟩ m es ⟨label finish,t⟩ mt := by
  induction run generalizing start finish with
  | @atom c s m a s' sign bits atomic action advance =>
    have hf := (fetch_entry hc pub macros s).trans
      (fetch_atom label start start finish c atomic pub macros s)
    exact .cons (by rw [hf, resume_action, action])
      (by rw [hf, resume_advance, advance]; rfl) (.nil ..)
  | @seq a b s m es s' m' fs t mt first second ih₁ ih₂ =>
    have left : Contains rows label start (start+a.slots) a := by
      intro i hi hj
      rw [hc i hi (by simp only [Code.slots]; omega)]
      simp [Code.emit, hj]
    have right : Contains rows label (start+a.slots) finish b := by
      intro i hi hj
      rw [hc i (by omega) (by simp only [Code.slots]; omega)]
      simp [Code.emit, not_lt.mpr hi]
    exact (ih₁ left).append (ih₂ right)
  | @ifEq x y a b s m es t mt branch ih =>
    have hf := (fetch_entry hc pub macros s).trans (by
      simp only [Code.emit, ite_true]
      exact fetch_jumpEq pub macros (label start) (label (start+1)) (label (start+1+a.slots)) s x y)
    by_cases hbit : s x = s y
    · have child := hc.forkLeft (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_left (hi)])
      simp only [hbit, ite_true] at ih
      apply NativePrefix.jump _ (ih child)
      simpa only [hbit, ite_true] using hf
    · have child := hc.forkRight (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_right (not_lt.mpr hi)])
      simp only [hbit, ite_false] at ih
      apply NativePrefix.jump _ (ih child)
      simpa only [hbit, ite_false] using hf
  | @ifLt x y a b s m es t mt branch ih =>
    have hf := (fetch_entry hc pub macros s).trans (by
      simp only [Code.emit, ite_true]
      exact fetch_jumpLt pub macros (label start) (label (start+1)) (label (start+1+a.slots)) s x y)
    by_cases hbit : s x < s y
    · have child := hc.forkLeft (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_left (hi)])
      simp only [hbit, ite_true] at ih
      apply NativePrefix.jump _ (ih child)
      simpa only [hbit, ite_true] using hf
    · have child := hc.forkRight (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_right (not_lt.mpr hi)])
      simp only [hbit, ite_false] at ih
      apply NativePrefix.jump _ (ih child)
      simpa only [hbit, ite_false] using hf
  | @choose a b s m es t mt bit branch ih =>
    have hf := (fetch_entry hc pub macros s).trans (by
      simp only [Code.emit, ite_true]
      exact fetch_choose pub macros (label start) (label (start+1)) (label (start+1+a.slots)) s)
    by_cases hb : bit = true
    · have child := hc.forkLeft (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_left (hi)])
      simp only [hb, ite_true] at ih
      apply NativePrefix.guess bit hf
      simpa only [hb, ite_true] using ih child
    · have child := hc.forkRight (a := a) (b := b) rfl (fun i hlo hi ↦ by
        simp only [Code.emit, ite_eq_right (Nat.ne_of_gt hlo), ite_eq_right (not_lt.mpr hi)])
      simp [hb] at ih
      apply NativePrefix.guess bit hf
      simpa [hb] using ih child
  | @whileDone x y body s m h =>
    have hf := fetch_entry hc pub macros s
    apply NativePrefix.jump _ (.nil ..)
    simpa only [Code.emit, ite_true, fetch_jumpLt, ite_eq_right h] using hf
  | @whileStep x y body s m es s' m' fs t mt guard first loop ih₁ ih₂ =>
    have child : Contains rows label (start+1) start body := by
      intro i hlo hhi
      rw [hc i (by omega) (by simp only [Code.slots]; omega)]
      simp only [Code.emit, ite_eq_right (by omega : i ≠ start)]
    apply NativePrefix.jump _ ((ih₁ child).append (ih₂ hc))
    simpa only [Code.emit, ite_true, fetch_jumpLt, ite_eq_left guard] using fetch_entry hc pub macros s

/-- Closing the emitted top-level table at its accepting continuation gives
exactly the events and private choices of the structured execution. -/
theorem Runs.execute {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} (run : Runs pub macros c s m es t mt) :
    TeamRAM.execute (c.program.fetch pub macros) ⟨0,s⟩ m (es.map TeamRAM.Event.choices) = some es := by
  let lab (i : ℕ) : Fin (c.slots+1) := ⟨min i c.slots, by omega⟩
  have hc : Contains c.row lab 0 c.slots c := by
    intro i _ hi
    have hlt : i < c.slots := by omega
    simp [lab, Code.row, min_eq_left hlt.le, hlt]
  have pref := run.nativePrefix c.row lab hc
  rw [show fetch c.row pub macros = c.program.fetch pub macros by funext q; exact fetch_row c pub macros q] at pref
  have atZero : lab 0 = 0 := Fin.ext (by simp [lab])
  have atLast : lab c.slots = Fin.last c.slots := Fin.ext (by simp [lab])
  rw [atZero, atLast] at pref
  exact pref.execute (c.fetch_finish pub macros t)

end RoutingISA

end BorderVNP
end Computability
end OAI
