import OAI.Computability.VPVNP.RAMUniform
import OAI.Computability.VPVNP.RAMTapeISAPorts
import OAI.Computability.VPVNP.RAMTapeWordComparison

/-!
# Instruction dispatch and its typed exits

A local instruction updates the register or private-log bank before reporting
the next program counter. Binary choices and external reads and writes are
returned to the call controller. This separates their charging and bit choices
from the deterministic work of fetching and interpreting the instruction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ISA

open BurstRAM PrivateRAM TapeWord

/-- Typed instruction exit carrying the next counter, a choice, an external access, a returned
state, or a halt decision. -/
inductive Callback (p r : ℕ) where
  | next (pc : Fin p)
  | choose (yes no : Fin p)
  | read (dst addr : Fin r) (next : Fin p)
  | write (addr src : Fin r) (next : Fin p)
  | returnState (src : Fin r)
  | accept
  | reject
  deriving DecidableEq, Fintype

variable {v w p r k : ℕ}

/-- Native continuation represented by the exit label and the resulting
architectural bank. The outer call controller handles the read answer and the
binary choice. -/
def Callback.action (cb : Callback p r) (c : LogConfig w p r) : CallAction w (LogConfig w p r) :=
  match cb with
  | .next j => .localStep {c with pc := j}
  | .choose yes no => .branch fun b => {c with pc := if b then yes else no}
  | .read dst addr j => .read (c.reg addr) fun x => {c with pc := j, reg := Function.update c.reg dst x}
  | .write addr src j => .write (c.reg addr) (c.reg src) {c with pc := j}
  | .returnState src => .finish (some (c.reg src))
  | .accept => .finish none
  | .reject => .reject

/-- The fields written by deterministic instruction preparation. The program
counter belongs to the finite control and is set by `Callback.action`. -/
def post (i : Instr v p r k) (pub : Fin k → Word w) (c : LogConfig w p r) : LogConfig w p r :=
  match i with
  | .constant dst val _ => {c with reg := Function.update c.reg dst (Fin.ofNat _ val.val)}
  | .publicWord dst j _ => {c with reg := Function.update c.reg dst (pub j)}
  | .stateWord dst _ => {c with reg := Function.update c.reg dst c.persistent}
  | .copy dst src _ => {c with reg := Function.update c.reg dst (c.reg src)}
  | .binary op dst x y _ => {c with reg := Function.update c.reg dst (op.eval (c.reg x) (c.reg y))}
  | .loadPrivate dst addr _ => {c with reg := Function.update c.reg dst (WriteLog.memory c.writes (c.reg addr))}
  | .storePrivate addr src _ => {c with writes := (c.reg addr, c.reg src) :: c.writes}
  | _ => c

theorem post_writes (i : Instr v p r k) (pub : Fin k → Word w) (c : LogConfig w p r) :
    (post i pub c).writes = (i.resize w).nextLog c := by cases i <;> rfl

theorem post_writes_length_le (i : Instr v p r k) (pub : Fin k → Word w) (c : LogConfig w p r) :
    (post i pub c).writes.length ≤ c.writes.length + 1 := by
  rw [post_writes]
  exact Instr.nextLog_length_le ..

/-- Determine an instruction’s typed exit, using the supplied test bit to select the target of
a conditional jump. -/
def exitFor (i : Instr v p r k) (test : Bool) : Callback p r :=
  match i with
  | .constant _ _ j | .publicWord _ _ j | .stateWord _ j | .copy _ _ j | .binary _ _ _ _ j
  | .loadPrivate _ _ j | .storePrivate _ _ j => .next j
  | .jumpEq _ _ yes no | .jumpLt _ _ yes no => .next (if test then yes else no)
  | .choose yes no => .choose yes no
  | .readExternal dst addr j => .read dst addr j
  | .writeExternal addr src j => .write addr src j
  | .returnState src => .returnState src
  | .accept => .accept
  | .reject => .reject

/-- Only conditional jumps leave a single-bit test result for the dispatcher. -/
def jumpTest (i : Instr v p r k) (c : LogConfig w p r) : Option Bool :=
  match i with
  | .jumpEq x y _ _ => some (Comparison.Op.eq.eval (c.reg x) (c.reg y))
  | .jumpLt x y _ _ => some (Comparison.Op.lt.eval (c.reg x) (c.reg y))
  | _ => none

theorem callback_action (i : Instr v p r k) (pub : Fin k → Word w) (c : LogConfig w p r) :
    (exitFor i ((jumpTest i c).getD false)).action (post i pub c) = (i.resize w).runLogged pub c := by
  cases i <;> simp [jumpTest, exitFor, Callback.action, post, Instr.resize, Instr.runLogged,
    Instr.run, LogConfig.denote, Instr.nextLog, CallAction.mapState, Config.put, Config.store,
    Comparison.Op.eval] <;> rfl

end RAMTape.ISA

end VPVNP
end Computability
end OAI
