import OAI.Hierarchy.ProtocolRAMScan
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Rounded address extents in a native word bank -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open ProtocolRAM Computability.VPVNP.BurstRAM

theorem ceilPage (n : ℕ) : n≤2^(Nat.clog 2 n) ∧ 2^(Nat.clog 2 n)≤2*(n+1) := by
  refine ⟨Nat.le_pow_clog (by decide) n,?_⟩
  have lo:=Nat.lt_pow_succ_log_self (by decide : 1<2) n
  have cap : 2^(Nat.clog 2 n) ≤ 2^(Nat.log 2 n + 1) :=
    Nat.pow_le_pow_right (by decide) (Nat.clog_le_of_le_pow lo.le)
  apply cap.trans
  by_cases zero:n=0
  · simp [zero]
  · have lower:=Nat.pow_log_le_self 2 zero
    rw [pow_succ];omega

theorem bankFits {w out : ℕ} (bank : Bank) (extent : bank.base+bank.size≤out) (cpu : out<2^w) :
    bank.Fits w out :=
  ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (extent.trans_lt cpu),extent⟩

end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
