import OAI.Hierarchy.DescentCompilerSlack
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # The original rotor board fits the selected block at every sufficiently large height -/
namespace Hierarchy.DescentDatedAddressBook.ResetMiddle
open DescentCompiler DescentCompiler.TerminalScale Filter

theorem sender_board_at (t c host gain cut d : ℕ) (hc : 0<c) :
    ∀ᶠ h : ℕ in atTop, d ≤ 2^groupBits t (Nat.log 2 h/(2*c)) host gain cut :=by
  filter_upwards [eventually_late (Nat.clog 2 (d+1)) c hc] with h hh
  have room : Nat.clog 2 (d+1) ≤ groupBits t (Nat.log 2 h/(2*c)) host gain cut :=by unfold groupBits;omega
  exact (Nat.le_succ d).trans ((Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) room))

end Hierarchy.DescentDatedAddressBook.ResetMiddle

end OAI
