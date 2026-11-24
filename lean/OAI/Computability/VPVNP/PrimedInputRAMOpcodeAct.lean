import OAI.Computability.VPVNP.PrimedInputRAMOpcodes
import OAI.Computability.VPVNP.PrimedInputRAMFlowEval

/-!
# Choice and copy instructions at the end of each data call

The owner flag controls one genuine burst-RAM choice. Nonowner cells of the
first pass skip the write. Second-pass cells write the literal or the word
obtained from one read. The next persistent cursor remains in register 29.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Opcodes

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ} (pub : Pub → Word w) (state : Word w) (rs : Regs w 48) (m : Memory w)

theorem act_choose (hf : rs 4 < rs 5) (ho : rs 28 = rs 1) (b : Bool) :
    Flow.Exec pub state act rs m
      [.tick,.tick,.choice b,.write (rs 30) (if b then rs 1 else rs 0)]
      rs (writeMemory m (rs 30) (if b then rs 1 else rs 0)) := by
  apply Flow.Exec.ifLtYes hf
  apply Flow.Exec.ifEqYes ho
  cases b
  · exact .branchNo (.line rfl)
  · exact .branchYes (.line rfl)

theorem act_skip (hf : rs 4 < rs 5) (ho : rs 28 ≠ rs 1) :
    Flow.Exec pub state act rs m [.tick,.tick,.tick]
      (Function.update rs (28 : Reg) (Fin.ofNat _ 0)) m :=
  .ifLtYes hf (.ifEqNo ho (.line rfl))

theorem act_literal (hf : ¬rs 4 < rs 5) (hl : rs 27 ≠ rs 1) :
    Flow.Exec pub state act rs m [.tick,.tick,.write (rs 30) (rs 26)]
      rs (writeMemory m (rs 30) (rs 26)) :=
  .ifLtNo hf (.ifEqNo hl (.line rfl))

theorem act_fetch (hf : ¬rs 4 < rs 5) (hl : rs 27 = rs 1) :
    Flow.Exec pub state act rs m [.tick,.tick,.read (rs 26) (m (rs 26).val),
      .write (rs 30) (m (rs 26).val)] (Function.update rs (26 : Reg) (m (rs 26).val))
        (writeMemory m (rs 30) (m (rs 26).val)) := by
  apply Flow.Exec.ifLtNo hf
  apply Flow.Exec.ifEqYes hl
  exact Flow.Exec.seq (Flow.Exec.line rfl) (Flow.Exec.line rfl)

end PrimedInputRAM.Opcodes

end VPVNP
end Computability
end OAI
