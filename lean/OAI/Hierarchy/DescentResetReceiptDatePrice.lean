import OAI.Hierarchy.DescentResetReceivedFactor
import OAI.Hierarchy.DescentResetClippedDatePrice

namespace OAI
/-! A uniform bit budget for the whole received candidate bank. All exponent
choices precede the physical log-height parameter and the choice of old memories. -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSixParty TerminalScale CandidateFront Filter
noncomputable section
set_option quotPrecheck false
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d) (D f g : ℕ)

structure ReceiptAt (rate j : ℕ) where
  v : ResetOutput
  sched : AtomSchedule
  k : ℕ
  tail : ℕ
  age : ℕ
  oldLane : ℕ
  newLane : ℕ
  field : ℕ
  «meta» : ℕ
  chart : ℕ
  packet : ℕ
  source : ℕ
  gain : ℕ
  calendar : List ℕ
  front : v.front=setupFront sched board k tail age D f g oldLane newLane field «meta» chart packet calendar
  window : 2^k ≤ scale j rate
  capacity : (calendar.take age).prod*256 ≤ scale j rate
  work : source ≤ scale j rate
  increase : gain ≤ scale j rate

/-- Changing the pricing exponent before the native height is selected makes
the bound valid even for a calendar with a small or zero number of dates. -/
theorem receipt_rate (rate : ℕ) :
    ∃E,∀j (a : ReceiptAt board D f g rate j),a.v.receiptFactor a.gain a.source ≤ scale j E := by
  let Q:=ReceiptAt board D f g rate
  have paid:=calendar_receipt_paid board D f g (ι:=Q) (J:=id)
    (fun _ a=>a.v) (fun _ a=>a.sched) (fun _ a=>a.k) (fun _ a=>a.tail) (fun _ a=>a.age)
    (fun _ a=>a.oldLane) (fun _ a=>a.newLane) (fun _ a=>a.field) (fun _ a=>a.meta) (fun _ a=>a.chart)
    (fun _ a=>a.packet) (fun _ a=>a.source) (fun _ a=>a.gain) (fun _ a=>a.calendar) (fun _ a=>a.front)
    ⟨rate,Eventually.of_forall fun _ a=>a.window⟩ ⟨rate,Eventually.of_forall fun _ a=>a.capacity⟩
    ⟨rate,Eventually.of_forall fun _ a=>a.work⟩ ⟨rate,Eventually.of_forall fun _ a=>a.increase⟩
  obtain ⟨E,late⟩:=paid
  obtain ⟨j₀,all⟩:=eventually_atTop.1 late
  refine ⟨E*(j₀+1),?_⟩
  intro j a
  have up:scale j rate ≤ scale (j+j₀) rate:=Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_left _ (by omega : j+1 ≤ j+j₀+1))
  let z:Q (j+j₀):={a with window:=a.window.trans up,capacity:=a.capacity.trans up,work:=a.work.trans up,increase:=a.increase.trans up}
  apply (all (j+j₀) (by omega) z).trans
  change 2^(E*(j+j₀+1)) ≤ 2^((E*(j₀+1))*(j+1))
  exact Nat.pow_le_pow_right (by decide) (by nlinarith only [Nat.zero_le (E*j*j₀)])

theorem receipt_date_price (rate receiver ratio saving : ℕ) :
    ∃C exponent : ℕ,∀ᶠ h : ℕ in atTop,∀ j (a : ReceiptAt board D f g rate j),∀ H groups δ copies N b width rows w fee,
      j ≤ Nat.log 2 h → 2^h ≤ copies → N ≤ scale j rate → b ≤ scale j rate → width ≤ scale j receiver →
      w ≤ ratio*h → rows*h ≤ (2+N)*h+groups*(32*N*b+16*width) →
      fee ≤ a.v.receiptFactor a.gain a.source*receiptArea h H rows → 1≤δ →
      fee*w ≤ H*h*(C*scale j exponent)+H*(groups*δ)*(C*scale j exponent)+copies/(2^j)^saving := by
  obtain ⟨E,localCost⟩:=receipt_rate board D f g rate
  obtain ⟨C,ex,paid⟩:=clipped_date_price 1 E 3 rate receiver ratio saving
  refine ⟨C,ex,?_⟩
  filter_upwards [paid] with h bound
  intro j a H groups δ copies N b width rows w fee age ambient cells walsh fieldBound word packed charged rad
  apply bound j H groups δ copies (a.v.receiptFactor a.gain a.source) N b width rows w fee age ambient _ cells walsh fieldBound word packed charged rad
  simpa only [one_mul] using localCost j a

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
