import OAI.Computability.VPVNP.RAMTapeInputLength
import OAI.Computability.VPVNP.RAMTapeInputPrefix
import OAI.Computability.VPVNP.StructuredStackCall

/-! # Callable length and prefix passes of the physical input reader -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.InputReader

/-- Callable length-measuring pass from scan entry to its successful return. -/
def lengthRoutine := Routine.ofCode lengthCode .scan .done
/-- Callable self-delimiting prefix reader from entry to its successful return. -/
def prefixRoutine := Routine.ofCode prefixCode .entry .done

theorem lengthRoutine_runs (s : Stacks InputPort) (ht : s .tmp = []) :
    lengthRoutine.Runs (5*(s .input).length+2) s
      (Function.update s .size (List.replicate (s .input).length true ++ s .size)) :=
  Routine.runs_ofCode (by decide) rfl (length_runs s ht)

theorem prefixRoutine_runs (s : Stacks InputPort) (t suffix : List Bool)
    (hin : s .input = (UniversalMachine.unary t.length ++ t) ++ suffix)
    (ht : s .tmp = []) (hc : s .count = []) (hp : s .prefix = []) :
    prefixRoutine.Runs (10*t.length+6) s
      (Function.update (Function.update s .input suffix) .prefix (UniversalMachine.unary t.length ++ t)) :=
  Routine.runs_ofCode (by decide) rfl (prefix_runs s t suffix hin ht hc hp)

end RAMTape.InputReader

end VPVNP
end Computability
end OAI
