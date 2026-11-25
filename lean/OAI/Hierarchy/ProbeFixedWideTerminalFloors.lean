import OAI.Hierarchy.ProbeFixedWideTerminal

namespace OAI
/-! # Physical bounds for the original eleven-column terminal role tape -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits work : ℕ)
local notation "b" => v.wideTerminalBoard h width bits work
local notation "L" => v.wideTurnWindow h width bits work
local notation "lo" => v.wideTerminalRankStart h width bits work
local notation "W" => Native.wordBits h (2^v.W) Native.copies

/-- The original directed site and role columns and both unnormalized endpoint-site
columns can all be copied from the complete board image, including inactive rows. -/
theorem wide_terminal_role_floors (room : v.wideTerminalWorkEnd h width bits work ≤ 2^W) :
    work ≤ (b).endAt ∧ (b).endAt+3*(b).old ≤ lo ∧ lo ≤ (L).floor ∧
    (L).floor ≤ (L).stop ∧ (b).old ≤ 2^W ∧ (b).edges ≤ 2^W := by
  have dataEnd : (b).endAt = work+4*(b).old+4*(b).edges := rfl
  have starts : (b).endAt+3*(b).old≤lo := by
    change (b).endAt+3*(b).old≤(b).endAt+3*(b).old+_+_
    omega
  have ranks : lo≤(L).floor := by
    change lo≤lo+_+_+_+_+_+_+_+_
    omega
  obtain ⟨a,c,d,e,f⟩ := (L).bounds
  have stop : (L).floor≤(L).stop := by omega
  have word : (L).stop≤2^W := room
  exact ⟨by omega,starts,ranks,stop,by omega,by omega⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
