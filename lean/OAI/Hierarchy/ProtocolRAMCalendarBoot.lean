import OAI.Hierarchy.ProtocolRAMCalendarBootStart
import OAI.Hierarchy.ProtocolRAMCalendarFrozen
import OAI.Hierarchy.ProtocolRAMCalendarArena
import OAI.Hierarchy.ProtocolRAMPurchaseMarketMount
import OAI.Hierarchy.ProbeStageCheap
import OAI.Computability.VPVNP.RAMMemory

namespace OAI
/-! # The single subdivision run at the entrance to a finite purchase calendar -/

namespace Hierarchy.ProtocolRAM.Calendar.Boot

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseCT PurchaseFrozen
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing Classical

noncomputable section
variable {z d k jobs : ℕ}
/-- Link the subdivision directly in front of the calendar word machine. -/
def program {q n : ℕ} (C : Chart (wordBits z d copies) q n) (flag : ℕ) :=
  (subdivisionProgram z d).seq (checked C flag)

theorem cheap {q n : ℕ} (C : Chart (wordBits z d copies) q n) (flag : ℕ) :
    CheapCode (program C flag) := cheap_seq (subdivision_cheap z d) (checked_cheap C flag)

theorem checked_from_header {q n : ℕ} (C : Chart (wordBits z d copies) q n) (flag : ℕ)
    (v : Fin jobs → Market z d k) {size : ℕ} (layout : Layout v size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Tape z d)
    (authentic : ∀i : Fin (2^z), words i.val=((π i).val : Word _))
    (mounted : Calendar.mounted C (events C.mesh) (booted v size words))
    (fits : (historyFlag C (events C.mesh)).Fits (wordBits z d copies) flag) (word : flag+1<2^wordBits z d copies) :
    (program C flag).Exec (initial v size words) (checkedOut C flag (booted v size words))
      (subdivisionConstant d*2^z+checkedCost C) :=
  Procedure.Exec.then (start v layout hd π words authentic).1 (checked_exec C flag _ mounted fits word)

end
end Hierarchy.ProtocolRAM.Calendar.Boot

end OAI
