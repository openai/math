import OAI.Computability.VPVNP.RAMTapeISAPorts

/-!
# Staging registers on the private-log ports

The private load and store routines share two staging words. All remaining
architectural ports retain their values while the log kernel is running.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ISA

open BurstRAM PrivateRAM

variable {w r k : ℕ}

/-- A bank in which the query and output log ports are occupied. -/
def stagedBank (pub : Fin k → Word w) (persistent : Word w) (reg : Fin r → Word w)
    (log : WriteLog w) (query out : List Bool) : Stacks (Port r k)
  | .logPort .query => query
  | .logPort .out => out
  | port => bank pub persistent reg log port

@[simp] theorem stagedBank_empty (pub : Fin k → Word w) (s : Word w) (reg : Fin r → Word w)
    (log : WriteLog w) : stagedBank pub s reg log [] [] = bank pub s reg log := by
  funext j
  cases j with
  | logPort j => cases j <;> rfl
  | _ => rfl

theorem stagedBank_update_query (pub : Fin k → Word w) (s : Word w) (reg : Fin r → Word w)
    (log : WriteLog w) (query out x : List Bool) :
    Function.update (stagedBank pub s reg log query out) (.logPort .query) x =
      stagedBank pub s reg log x out := by
  funext j
  cases j with
  | logPort j => cases j <;> rfl
  | _ => rfl

theorem stagedBank_update_out (pub : Fin k → Word w) (s : Word w) (reg : Fin r → Word w)
    (log : WriteLog w) (query out x : List Bool) :
    Function.update (stagedBank pub s reg log query out) (.logPort .out) x =
      stagedBank pub s reg log query x := by
  funext j
  cases j with
  | logPort j => cases j <;> rfl
  | _ => rfl

theorem stagedBank_update_reg (pub : Fin k → Word w) (s : Word w) (reg : Fin r → Word w)
    (log : WriteLog w) (query out : List Bool) (i : Fin r) (v : Word w) :
    Function.update (stagedBank pub s reg log query out) (.reg i) (wordBits v) =
      stagedBank pub s (Function.update reg i v) log query out := by
  funext j
  cases j with
  | reg j => by_cases h : j = i <;> simp [stagedBank, bank, h]
  | logPort j => cases j <;> rfl
  | _ => rfl

theorem logPort_injective : Function.Injective (@Port.logPort r k) := fun _ _ => Port.logPort.inj

/-- Installing the ten streams of a native log routine replaces precisely
the staged query, output, and log. The ambient registers are preserved. -/
theorem install_logBank (pub : Fin k → Word w) (s : Word w) (reg : Fin r → Word w)
    (baseLog : WriteLog w) (a : Word w) (out : List Bool) (log : WriteLog w) :
    installStacks Port.logPort (bank pub s reg baseLog) (AddressLog.bank a out log).stacks =
      stagedBank pub s reg log (wordBits a) out := by
  funext j
  cases j with
  | logPort j =>
    rw [installStacks_at logPort_injective]
    cases j <;> rfl
  | reg | pub | persistent | work =>
    rw [installStacks_outside _ _ (by simp)]
    rfl

end RAMTape.ISA

end VPVNP
end Computability
end OAI
