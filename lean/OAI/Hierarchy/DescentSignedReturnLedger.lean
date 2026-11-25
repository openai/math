import OAI.Hierarchy.DescentSelectedReturnPrefix
import OAI.Hierarchy.DescentReturnSharedPages

namespace OAI
/-! # Charging the shared half-word pages to the actual original size -/
namespace Hierarchy.DescentCompiler.TerminalScale
open DescentSixParty DescentDatedAddressBook DescentSIMDLookup Filter

theorem signed_date_funded {F : Type} [Field F] (G : PoweredGadget F) (t f g reset ratio saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀J M tail i fee : ℕ,J≤Nat.log 2 h → 2^h≤2*M →
      let S:=stageNumbers G t J f g reset M tail
      let R:=ratio*scale J (Chronology.returnRate G t f g reset)
      fee≤R*MaterialProgram.purchased (S.hostSize i) (S.groupCount i) h →
      fee≤S.hostSize i*h*(R+1)+S.hostSize i*(S.groupCount i*S.radix)*R :=
  signed_date_funded_at G t f g reset ratio (Chronology.returnRate G t f g reset) saving

end Hierarchy.DescentCompiler.TerminalScale

end OAI
