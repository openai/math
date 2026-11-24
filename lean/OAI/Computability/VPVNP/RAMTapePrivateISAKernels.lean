import OAI.Computability.VPVNP.RAMTapePrivateISABank
import OAI.Computability.VPVNP.RAMTapeAddressLogLoad
import OAI.Computability.VPVNP.RAMTapeAddressLogStore

/-!
# Private load and store kernels in the RAM instruction bank

The log's ten native ports are installed in the architectural bank. A normal
completion returns directly to the caller with the two operand ports staged.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.ISA

open BurstRAM PrivateRAM

variable {w r k : ℕ}

/-- Scan the private log for a staged address. -/
def logLoad : FiniteRoutine (Port r k) :=
  FiniteRoutine.ofStackCode AddressLog.loadCode Port.logPort .record (fun q => decide (q = .done))

/-- Add the staged address and value to the head of the private log. -/
def logStore : FiniteRoutine (Port r k) :=
  FiniteRoutine.ofStackCode AddressLog.storeCode Port.logPort .readKey (fun q => decide (q = .done))

theorem logLoad_run (pub : Fin k → Word w) (s : Word w) (reg : Fin r → Word w) (log : WriteLog w)
    (a : Word w) :
    logLoad.Runs (AddressLog.loadCost a log) (stagedBank pub s reg log (wordBits a) [])
      (stagedBank pub s reg log (wordBits a) (wordBits (WriteLog.memory log a))) := by
  have run := FiniteRoutine.runs_ofStackCode logPort_injective
    (normal := fun q : AddressLog.State => decide (q = .done)) rfl rfl
    (fun q h => by obtain rfl := of_decide_eq_true h; rfl) (bank pub s reg log)
    (AddressLog.load_run a [] log)
  simpa only [logLoad, install_logBank, List.append_nil] using run

theorem logStore_run (pub : Fin k → Word w) (s : Word w) (reg : Fin r → Word w) (log : WriteLog w)
    (a v : Word w) :
    logStore.Runs (10 * w + 3) (stagedBank pub s reg log (wordBits a) (wordBits v))
      (stagedBank pub s reg ((a, v) :: log) (wordBits a) (wordBits v)) := by
  have run := FiniteRoutine.runs_ofStackCode logPort_injective
    (normal := fun q : AddressLog.StoreState => decide (q = .done)) rfl rfl
    (fun q h => by obtain rfl := of_decide_eq_true h; rfl) (bank pub s reg log)
    (AddressLog.store_run a v log)
  simpa only [logStore, install_logBank] using run

end RAMTape.ISA

end VPVNP
end Computability
end OAI
