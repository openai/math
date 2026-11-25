import OAI.Hierarchy.ProbeFixedWideSignedPartyTariff
import OAI.Hierarchy.ProbeFixedWidePacketRates
import OAI.Hierarchy.TaggedWideMaskWord

namespace OAI
/-! Both live party address formats fit the actual installed native word. -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open ProbeStage Tagged Filter
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "W" h => Native.wordBits h (2^v.W) Native.copies

structure PartyWordBounds (h width unitCost : ℕ) : Prop where
  lane : ∀a,2^(v.partyLaneBits h width a unitCost)<2^(W h)
  role : 2^(v.partyRoleBits h)≤2^(W h)

theorem cofinal_party_word {κ A : ℝ} (unitCost : ℕ) :
    ∀ᶠ x : WideParent κ A in WideParent.large κ A,v.PartyWordBounds x.h x.w unitCost := by
  obtain ⟨K,_,lanes⟩:=v.signed_party_dimensions unitCost
  let b:=Nat.log 2 (2*v.packetRowsRate+v.widePacketDegree)+1
  have tall : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop:=tendsto_comap
  filter_upwards [WideParent.columnBits_wordBits (κ:=κ) (A:=A) K,tall.eventually (eventually_ge_atTop b)] with x digits enough
  constructor
  · intro a
    exact ((lanes x.h x.w a x.formats.2.1).1).trans_lt ((WideParent.column_lt (K*x.w)).trans_le
      (Nat.pow_le_pow_right (by decide) (digits _ _)))
  · apply Nat.pow_le_pow_right (by decide)
    have exponent : v.partyRoleBits x.h=b:=by rw [partyRoleBits,v.packetRows_eq]
    rw [exponent,Native.wordBits_linear]
    omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
