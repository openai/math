import OAI.Computability.VPVNP.PrimedInputRAMFlow

/-!
# Execution of a linked structured burst program

The interpreter for a finite control graph consumes one unit of fuel at
each label. Word operations use the native burst opcodes, and branches use
the supplied bit stream. The normal exit is a continuation, so the result
applies both to standalone calls and to blocks inside a larger program.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Flow

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w r k : ℕ}

/-- Continuation at a label with its updated registers and memory and the
remaining branch bits. -/
abbrev Next (pc : Type) (w r : ℕ) :=
  pc → Regs w r → Memory w → List Bool → Option (Report w)

/-- Interpret a single labeled jump on the current registers, memory and choice stream, passing
the result to the selected continuation. -/
def Jump.run {pc : Type} (pub : Fin k → Word w) (state : Word w) (next : Next pc w r)
    (i : Jump pc r k) (rs : Regs w r) (m : Memory w) (bits : List Bool) : Option (Report w) :=
  match i with
  | .line op dst => (op.effect pub state rs m).bind fun (ev,rs',m') ↦
      (next dst rs' m' bits).map (Report.prepend ev)
  | .ifEq l q y n => (next (if rs l = rs q then y else n) rs m bits).map (Report.prepend .tick)
  | .ifLt l q y n => (next (if rs l < rs q then y else n) rs m bits).map (Report.prepend .tick)
  | .branch y n =>
    match bits with
    | [] => none
    | b :: bs => (next (if b then y else n) rs m bs).map (Report.prepend (.choice b))

theorem Jump.run_map {A B : Type} (f : A → B) (pub : Fin k → Word w) (state : Word w)
    (next : Next B w r) (i : Jump A r k) (rs : Regs w r) (m : Memory w) (bits : List Bool) :
    (i.map f).run pub state next rs m bits = i.run pub state (next ∘ f) rs m bits := by
  cases i with
  | line op dst => rfl
  | ifEq l q y n => by_cases h : rs l = rs q <;> simp [Jump.map, Jump.run, h]
  | ifLt l q y n => by_cases h : rs l < rs q <;> simp [Jump.map, Jump.run, h]
  | branch y n => cases bits with
    | nil => rfl
    | cons b bs => cases b <;> rfl

/-- Execute a subgraph with a continuation at its normal exit. -/
def run (a : PrimedInputRAM.Flow r k) (pub : Fin k → Word w) (state : Word w)
    (exit : ℕ → Regs w r → Memory w → List Bool → Option (Report w)) :
    ℕ → a.Label → Regs w r → Memory w → List Bool → Option (Report w)
  | 0, _, _, _, _ => none
  | fuel+1, i, rs, m, bits =>
    (a.code i).run pub state (fun t ↦ match t with
      | none => exit fuel
      | some j => run a pub state exit fuel j) rs m bits

private theorem execute_bad {p : ℕ} (M : Machine w p r k) (bad : Fin p) (hb : M.code bad = .reject)
    (fuel : ℕ) (state : Word w) (rs : Regs w r) (priv : Word w → Word w) (m : Memory w)
    (bits : List Bool) :
    execute M.program fuel ⟨bad,state,rs,priv⟩ m bits = none := by
  cases fuel <;> simp [execute, Machine.program, hb, Instr.run]

private theorem execute_jump {p : ℕ} (M : Machine w p r k) (j : Jump (Fin p) r k)
    (cur bad : Fin p) (hc : M.code cur = (j.emit bad).resize w) (hb : M.code bad = .reject)
    (fuel : ℕ) (state : Word w) (rs : Regs w r) (priv : Word w → Word w) (m : Memory w)
    (bits : List Bool) :
    execute M.program (fuel+1) ⟨cur,state,rs,priv⟩ m bits =
      j.run M.publicData state (fun q regs mem bs ↦ execute M.program fuel ⟨q,state,regs,priv⟩ mem bs)
        rs m bits := by
  cases j with
  | line op dst =>
    cases op <;> simp only [execute, Machine.program, hc, Jump.emit, Instr.resize, Jump.run,
      Op.emit, Op.effect, Instr.run, Config.put, Option.bind_some]
    all_goals split <;> simp_all
    all_goals exact execute_bad M bad hb fuel state rs priv m bits
  | ifEq l q y n | ifLt l q y n =>
    simp [execute, Machine.program, hc, Jump.emit, Instr.resize, Instr.run, Jump.run]
  | branch y n =>
    cases bits <;> simp [execute, Machine.program, hc, Jump.emit, Instr.resize, Instr.run, Jump.run]

/-- The compiled table and the named control graph have the same execution
on every fuel and branch stream, including rejected and unfinished calls. -/
theorem Linked.execute {p : ℕ} {M : Machine w p r k} {a : PrimedInputRAM.Flow r k}
    {label : a.Label → Fin p} {stop bad : Fin p} (hl : Linked M a label stop bad)
    (hb : M.code bad = .reject) (state : Word w) (priv : Word w → Word w)
    (fuel : ℕ) (i : a.Label) (rs : Regs w r) (m : Memory w) (bits : List Bool) :
    execute M.program fuel ⟨label i,state,rs,priv⟩ m bits =
      run a M.publicData state
        (fun left regs mem bs ↦ execute M.program left ⟨stop,state,regs,priv⟩ mem bs)
        fuel i rs m bits := by
  induction fuel generalizing i rs m bits with
  | zero => rfl
  | succ fuel ih =>
    rw [execute_jump M _ (label i) bad (hl.atLabel i) hb, Jump.run_map, run]
    congr 1
    funext t regs mem bs
    cases t with
    | none => rfl
    | some q => exact ih q regs mem bs

/-- Execute from the entry of the compiled template, with freshly zeroed
registers and private memory. -/
theorem template_executes (a : PrimedInputRAM.Flow r k) (result : Option (Fin r))
    (pub : Fin k → Word w) (state : Word w) (mem : Memory w) (bits : List Bool) (fuel : ℕ) :
    let M := (a.template result).instantiate w pub
    execute M.program fuel (M.program.start state) mem bits =
      run a pub state (fun left rs mem' bs => execute M.program left ⟨a.exitPC,state,rs,fun _ => 0⟩ mem' bs)
        fuel a.entry (fun _ => 0) mem bits := by
  let M := (a.template result).instantiate w pub
  have hb : M.code a.rejectPC = .reject := by
    change ((a.template result).code a.rejectPC).resize w = _
    rw [template_reject]
    rfl
  exact (template_linked a result pub).execute hb state (fun _ => 0) fuel a.entry (fun _ => 0) mem bits

end PrimedInputRAM.Flow

end VPVNP
end Computability
end OAI
