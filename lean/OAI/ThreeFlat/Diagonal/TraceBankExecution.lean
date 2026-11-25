import OAI.ThreeFlat.Diagonal.TraceBanks
import OAI.ThreeFlat.RAM.Weighted

namespace OAI
/-! # Register-only execution of the weighted RAM

A trace row holds just the program counter, the fixed incoming state word,
and the register file. An instruction produces at most one memory record.
The sorting checker therefore handles private and external accesses alike.
-/

namespace ThreeFlat.Diagonal.TraceBanks

open Computability.VPVNP.BurstRAM
open Computability.VPVNP.BurstRAM.PrivateRAM

variable {w p r k : ℕ} {F : Type*}

/-- The local machine information passed to the next trace row. -/
structure Snapshot (w p r : ℕ) where
  pc : Fin p
  persistent : Word w
  reg : Fin r → Word w
  deriving DecidableEq

def snapshot (c : Config w p r) : Snapshot w p r := ⟨c.pc, c.persistent, c.reg⟩

def Snapshot.put (s : Snapshot w p r) (next : Fin p) (d : Fin r) (v : Word w) :
    Snapshot w p r := {s with pc := next, reg := Function.update s.reg d v}

/-- Each memory operation now emits one explicit probe while the CPU state
at the next instruction contains no addressable memory. -/
def step (pub : Fin k → Word w) (s : Snapshot w p r) : Instr w p r k → CallAction (w+1) (Snapshot w p r)
  | .constant dst v next => .localStep (s.put next dst v)
  | .publicWord dst j next => .localStep (s.put next dst (pub j))
  | .stateWord dst next => .localStep (s.put next dst s.persistent)
  | .copy dst src next => .localStep (s.put next dst (s.reg src))
  | .binary op dst x y next => .localStep (s.put next dst (op.eval (s.reg x) (s.reg y)))
  | .loadPrivate dst addr next => .read (privateAddress (s.reg addr))
      (fun v => s.put next dst (narrow v))
  | .storePrivate addr src next => .write (privateAddress (s.reg addr)) (wide (s.reg src))
      {s with pc := next}
  | .jumpEq x y yes no => .localStep {s with pc := if s.reg x = s.reg y then yes else no}
  | .jumpLt x y yes no => .localStep {s with pc := if s.reg x < s.reg y then yes else no}
  | .choose yes no => .branch fun b => {s with pc := if b then yes else no}
  | .readExternal dst addr next => .read (wide (s.reg addr)) (fun v => s.put next dst (narrow v))
  | .writeExternal addr src next => .write (wide (s.reg addr)) (wide (s.reg src)) {s with pc := next}
  | .returnState src => .finish (some (wide (s.reg src)))
  | .accept => .finish none
  | .reject => .reject

/-- Combined-bank program with the same instruction count as the original. -/
def exposed (M : Machine w p r k) : Program (w+1) (Snapshot w p r) where
  start s := ⟨M.entry, narrow s, fun _ => 0⟩
  step s := step M.publicData s (M.code s.pc)

def wideCode (code : RAM.FieldCode F w) : RAM.FieldCode F (w+1) where
  encode := wide ∘ code.encode
  decode := code.decode ∘ narrow
  decode_encode x := by simp [code.decode_encode]

@[simp] theorem snapshot_put (s : Config w p r) (next : Fin p) (dst : Fin r) (v : Word w) :
    snapshot (s.put next dst v) = (snapshot s).put next dst v := rfl

@[simp] theorem snapshot_store (s : Config w p r) (next : Fin p) (a v : Word w) :
    snapshot (s.store next a v) = { snapshot s with pc := next } := rfl

/-- The weighted execution is unchanged after exposing every private access
to the same chronological read/write checker as the external accesses. -/
theorem mass_exposed [Semiring F] (code : RAM.FieldCode F w) (M : Machine w p r k)
    (fuel : ℕ) (c : Config w p r) (ext : Memory w) (bank : Memory (w+1))
    (hm : Matches bank ext c.privateMem) :
    RAM.mass (wideCode code) (exposed M) fuel (snapshot c) bank =
      RAM.mass code M.program fuel c ext := by
  induction fuel generalizing c ext bank with
  | zero => rfl
  | succ f ih =>
    simp only [RAM.mass, exposed, snapshot, Machine.program]
    cases hop : M.code c.pc with
    | constant dst v next => exact ih (c.put next dst v) ext bank hm
    | publicWord dst j next => exact ih (c.put next dst (M.publicData j)) ext bank hm
    | stateWord dst next => exact ih (c.put next dst c.persistent) ext bank hm
    | copy dst src next => exact ih (c.put next dst (c.reg src)) ext bank hm
    | binary op dst x y next => exact ih (c.put next dst (op.eval (c.reg x) (c.reg y))) ext bank hm
    | loadPrivate dst addr next =>
      simp only [step, Instr.run, hm.privateWord, narrow_wide]
      exact ih (c.put next dst (c.privateMem (c.reg addr))) ext bank hm
    | storePrivate addr src next =>
      exact ih (c.store next (c.reg addr) (c.reg src)) ext _ (hm.write_private ..)
    | jumpEq x y yes no => exact ih {c with pc := if c.reg x = c.reg y then yes else no} ext bank hm
    | jumpLt x y yes no => exact ih {c with pc := if c.reg x < c.reg y then yes else no} ext bank hm
    | choose yes no =>
      exact congrArg₂ (· + ·) (ih {c with pc := no} ext bank hm) (ih {c with pc := yes} ext bank hm)
    | readExternal dst addr next =>
      have hr : bank (wide (c.reg addr)).val = wide (ext (c.reg addr).val) := hm.external _
      simp only [step, Instr.run, hr, narrow_wide]
      exact ih (c.put next dst (ext (c.reg addr).val)) ext bank hm
    | writeExternal addr src next =>
      exact ih {c with pc := next} _ _ (hm.write_external ..)
    | returnState src => simp [step, Instr.run, RAM.FieldCode.terminal, wideCode]
    | accept | reject => rfl

theorem value_eq_exposed [Semiring F] (code : RAM.FieldCode F w) (M : Machine w p r k)
    (fuel : ℕ) (state : Word w) (memory : Memory w) :
    RAM.value code M fuel state memory =
      RAM.mass (wideCode code) (exposed M) fuel ((exposed M).start (wide state)) (inputBank memory) := by
  simpa [RAM.value, Machine.program, snapshot, exposed, narrow_wide] using
    (mass_exposed code M fuel (M.program.start state) memory (inputBank memory)
      (matches_inputBank memory)).symm

end ThreeFlat.Diagonal.TraceBanks

end OAI
