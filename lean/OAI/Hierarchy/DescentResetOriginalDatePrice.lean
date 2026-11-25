import OAI.Hierarchy.DescentOriginalControlPrice
import OAI.Hierarchy.DescentResetClippedDatePrice
import OAI.Hierarchy.DescentResetReceivedVolume

namespace OAI
/-! The original-numbering traffic, including the global matrix-coordinate book, on the dated word scale. -/
namespace Hierarchy.DescentDatedAddressBook.OriginalControlPrice
open DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section

theorem date_price (D Y Z program shape rate receiver ratio saving : ℕ) :
    ∃lead exponent : ℕ, ∀ᶠ h : ℕ in atTop, ∀ j H G δ copies X cap gain b width rows w fee : ℕ,
      j≤Nat.log 2 h → 2^h≤copies → X≤ scale j rate → cap≤ scale j rate → gain≤ scale j rate →
      b≤ scale j rate → width≤ scale j receiver → w≤ratio*h → rows*h≤(2+X)*h+G*(32*X*b+16*width) →
      fee≤factorBound D Y Z program shape X cap gain*ResetOutput.receiptArea h H rows → 1≤δ →
      fee*w≤H*h*(lead*scale j exponent)+H*(G*δ)*(lead*scale j exponent)+copies/(2^j)^saving :=by
  obtain ⟨P,structural⟩:=factor_rate D Y Z program shape rate
  obtain ⟨L,E,dates⟩:=clipped_date_price 1 P 3 rate receiver ratio saving
  refine ⟨L,E,?_⟩
  filter_upwards [dates] with h date
  intro j H G δ copies X cap gain b width rows w fee age ambient cell count increase precision digits word scans bill steps
  apply date j H G δ copies (factorBound D Y Z program shape X cap gain) X b width rows w fee
    age ambient _ cell precision digits word scans bill steps
  simpa only [one_mul] using structural j X cap gain cell count increase

end
end Hierarchy.DescentDatedAddressBook.OriginalControlPrice

end OAI
