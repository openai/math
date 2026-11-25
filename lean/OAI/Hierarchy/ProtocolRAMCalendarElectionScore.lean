import OAI.Hierarchy.ProtocolRAMCalendarGlobalHeader
import OAI.Hierarchy.ProtocolRAMCalendarJointHeader
import OAI.Hierarchy.ProtocolRAMCalendarScalarHistory
import OAI.Hierarchy.ProtocolRAMSchedule

namespace OAI
/-! # Both global tests read only earlier physical pages and the previous active stock -/

namespace Hierarchy.ProtocolRAM.Calendar.GlobalTests
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AttemptGate
open scoped Classical Fin.CommRing

/-- Exact padded address bound of the real three-read score expression. The
rate ROM, the offset column, and the live stock are its only read banks. -/
theorem score_before {w : ℕ} (l : Layout) (z N k out bound : ℕ) (payload : Bool) (stocks : Bank)
    (cut : ℕ) (word : cut<2^w)
    (tables : stop l z N k+2^l.indexBits≤cut) (stock : stocks.base+stocks.size≤cut) :
    (check l z N k payload out bound stocks).term.Fits w cut := by
  apply Expr.fits_of_inputEnd _ _ word
  change max ((table l z N k payload).base+(table l z N k payload).size)
    (max (max ((offsets l).base+(offsets l).size) 0) (max (stocks.base+stocks.size) 0))≤cut
  have keys : l.base+2^l.indexBits≤cut := by
    unfold stop at tables
    omega
  obtain ⟨_,_,_,_⟩:=l
  cases payload <;> simp_all [table,offsets,Bank.size,stop] <;> omega

/-- The fitted lookup uses the actual deadline-ordinal page, even when that
page immediately precedes the private tape. The full power-of-two read
extent is accounted separately from valid logical score rows. -/
theorem deadline_score_before {w : ℕ} (b : JointHeader.Board) (z N k : ℕ) (c : Mesh) (a : Attempt)
    (payload : Bool) (out bound : ℕ) (stocks : Bank) (cut : ℕ)
    (word : cut<2^w)
    (pages : JointHeader.stop b z N k (DeadlineROM.count c)+2^(bits z N k)≤cut)
    (stock : stocks.base+stocks.size≤cut) :
    (check (DeadlineROM.scorePage c (JointHeader.scores b z N k) z N k a) z N k payload out bound stocks).term.Fits w cut := by
  apply score_before _ _ _ _ _ _ _ _ _ word _ stock
  let l:=JointHeader.scores b z N k
  change stop (page l z N k (DeadlineROM.index c a).val) z N k+2^(bits z N k)≤cut
  rw [page_stop]
  apply le_trans _ pages
  apply Nat.add_le_add_right
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (DeadlineROM.index c a).isLt) _

end Hierarchy.ProtocolRAM.Calendar.GlobalTests

end OAI
