import OAI.Computability.VPVNP.RAMTapeAddressLogControl
import OAI.Computability.VPVNP.StructuredStackRuns

/-!
# Stack bank and returning routines for fixed RAM instruction tables

The program counter is in finite control. Registers, the persistent word and
public words have distinct stack labels. The three stored private-log streams
share the address-log convention. Work ports 14 and 15 serve as scratch for
operand copies, independently of the arithmetic and address-log routines.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape

/-- A finite control packaged with its entry, so separately typed opcode
routines can form a single fixed program by sequencing. -/
structure FiniteRoutine (K : Type) where
  /-- Finite control-state type of the returning stack routine. -/
  State : Type
  [finiteState : Fintype State]
  /-- Stack routine on the specified ports and finite control states. -/
  body : Routine K State

attribute [instance] FiniteRoutine.finiteState

namespace FiniteRoutine

variable {K L Q : Type}

/-- Package a returning stack routine with its finite control-state type. -/
def ofRoutine [Fintype Q] (r : Routine K Q) : FiniteRoutine K := ⟨Q, r⟩

/-- Sequence two finite routines so the return from the first enters the second. -/
def followedBy (a b : FiniteRoutine K) : FiniteRoutine K := ofRoutine (a.body.followedBy b.body)

/-- The finite routine that immediately returns. -/
def ret : FiniteRoutine K := ofRoutine Routine.ret

/-- Execution of the routine from the input bank to the output bank in the given number of
steps. -/
abbrev Runs [DecidableEq K] (a : FiniteRoutine K) (n : ℕ) (s t : Stacks K) := a.body.Runs n s t

theorem Runs.followedBy [DecidableEq K] {a b : FiniteRoutine K} {m n : ℕ} {s t u : Stacks K}
    (ha : a.Runs m s t) (hb : b.Runs n t u) : (a.followedBy b).Runs (m + n) s u :=
  Routine.Runs.followedBy ha hb

/-- Redirect the normal halts of a finite subprogram into the caller. Rejection
remains a rejecting halt. No extra step is charged for a normal return. -/
def ofStackCode [Fintype Q] (src : StackCode K Q) (ports : K → L) (entry : Q)
    (normal : Q → Bool) : FiniteRoutine L := ofRoutine {
  entry := entry
  code := fun q => if normal q then .goto none else
    (src q).rename ports (fun j => if normal j then none else some j) }

theorem runs_ofStackCode [Fintype Q] [DecidableEq K] [DecidableEq L]
    {src : StackCode K Q} {ports : K → L} (hp : Function.Injective ports) {entry exit : Q}
    {normal : Q → Bool} (he : normal entry = false) (hx : normal exit = true)
    (hs : ∀ q, normal q = true → (src q).returns = true) (base : Stacks L)
    {t : ℕ} {s u : Stacks K} (h : StackRuns src t entry s exit u) :
    (ofStackCode src ports entry normal).Runs t (installStacks ports base s) (installStacks ports base u) := by
  let labels (q : Q) : Option Q := if normal q then none else some q
  let target := (ofStackCode src ports entry normal).body.standalone
  have hc (q : Q) (hn : (src q).returns = false) : target (labels q) = (src q).rename ports labels := by
    have hq : normal q = false := by
      cases h : normal q with
      | false => rfl
      | true => exact Bool.noConfusion ((hs q h).symm.trans hn)
    simp [target, labels, ofStackCode, ofRoutine, Routine.standalone, Routine.close, hq]
  have lifted := h.lift ports hp labels base hc
  simp only [labels, he, hx, Bool.false_eq_true, ite_false, ite_true] at lifted
  exact lifted

end FiniteRoutine

namespace ISA

open BurstRAM PrivateRAM

/-- Architectural, public, persistent, scratch, and private write-log stack labels for a fixed
instruction table. -/
inductive Port (r k : ℕ) where
  | reg (i : Fin r) | pub (i : Fin k) | persistent | work (i : Fin 16) | logPort (i : AddressLog.Port)
  deriving DecidableEq, Fintype

variable {r k w p : ℕ}

/-- Encode a private write log by its keys, values, and occupancy marks, with the other log
ports empty. -/
def logStacks (log : WriteLog w) : Stacks AddressLog.Port
  | .keys => AddressLog.keys log
  | .values => AddressLog.values log
  | .occupied => List.replicate log.length true
  | _ => []

/-- Between instructions, every work stack and address-log scratch stack is
empty. The architectural bank is independent of the program-counter label. -/
def bank (pub : Fin k → Word w) (persistent : Word w) (reg : Fin r → Word w) (log : WriteLog w) :
    Stacks (Port r k)
  | .reg i => wordBits (reg i)
  | .pub i => wordBits (pub i)
  | .persistent => wordBits persistent
  | .work _ => []
  | .logPort i => logStacks log i

/-- Encode the public words, persistent state, registers, and writes of a RAM configuration as
a stack bank. -/
def configBank (pub : Fin k → Word w) (c : LogConfig w p r) := bank pub c.persistent c.reg c.writes

theorem bank_updateReg (pub : Fin k → Word w) (persistent : Word w) (reg : Fin r → Word w)
    (log : WriteLog w) (i : Fin r) (v : Word w) :
    Function.update (bank pub persistent reg log) (.reg i) (wordBits v) =
      bank pub persistent (Function.update reg i v) log := by
  funext j
  cases j with
  | reg j => by_cases he : j = i <;> simp [bank, he]
  | pub | persistent | work | logPort => simp [bank]

end ISA
end RAMTape

end VPVNP
end Computability
end OAI
