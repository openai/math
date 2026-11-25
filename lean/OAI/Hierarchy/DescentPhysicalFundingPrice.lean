import OAI.Hierarchy.DescentPhysicalFundingVolume
import OAI.Hierarchy.DescentResetClippedDatePrice
import OAI.Hierarchy.DescentPackedChunkWork

namespace OAI
/-! Funding on two independently selected input and output pitches. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs
open DescentFundedCensus DescentSIMDLookup DescentCompiler DescentCompiler.TerminalScale Filter
noncomputable section

def fundingRows (s : DescentFundedCensus.Setup) :=
  chunks s.oldGroups s.oldLanes+3*chunks s.oldGroups s.gatherLanes

theorem funding_area_rows (s : DescentFundedCensus.Setup) (t : DescentFundedCensus.Shape)
    (h : ℕ) (chunksFit : 2^s.high≤chunks s.oldGroups s.gatherLanes)
    (census : t.rows=s.hosts*chunks s.oldGroups s.gatherLanes) :
    fundingArea s t h≤3*(s.hosts+s.hosts*fundingRows s+(h+1)^2*2^(h/2)):=by
  have a:=Nat.mul_le_mul_left s.hosts chunksFit
  have small : 0<(h+1)^2*2^(h/2):=by positivity
  simp only [fundingArea,Overlap.rows,fundingRows,census]
  nlinarith only [a, small, Nat.zero_le s.hosts, Nat.zero_le (s.hosts*chunks s.oldGroups s.oldLanes),
    Nat.zero_le (s.hosts*chunks s.oldGroups s.gatherLanes)]

theorem funding_rows_paid (s : DescentFundedCensus.Setup) (h U : ℕ)
    (prior : h≤ s.oldLanes*U) (current : h≤ s.gatherLanes*U) :
    fundingRows s*h≤4*h+s.oldGroups*(4*U):=by
  have l:=DescentDatedSeedStartup.chunk_work 1 s.oldGroups s.oldLanes h U prior
  have r:=DescentDatedSeedStartup.chunk_work 1 s.oldGroups s.gatherLanes h U current
  simp only [Nat.one_mul] at l r
  unfold fundingRows
  nlinarith only [l,r]

theorem funding_date_price (lead price rate ratio saving : ℕ) :
    ∃C exponent : ℕ,∀ᶠ h : ℕ in atTop,∀(J radix copies base w U : ℕ)
      (s : DescentFundedCensus.Setup) (t : DescentFundedCensus.Shape),
      J≤Nat.log 2 h → 2^h≤copies → 1≤radix → w≤ratio*h → U≤ scale J rate →
      fundingFactor s t≤lead*scale J price → chunks s.oldGroups s.oldLanes*h≤U*h+s.oldGroups*U →
      chunks s.oldGroups s.gatherLanes*h≤U*h+s.oldGroups*U →
      2^s.high≤chunks s.oldGroups s.gatherLanes → t.rows=s.hosts*chunks s.oldGroups s.gatherLanes →
      s.oldLanes≤h → s.gatherLanes≤h → s.precision*s.oldLanes≤h/2 →
      (s.high+s.low)*(s.high+s.low)≤h/2 → (s.precision+s.precision)*2^s.low≤h/2 →
      DescentGLPacked.BankImage.SignedFields.joinWidth s.precision s.blocks*s.gatherLanes≤h/2 →
      s.flagWidth≤h/2 → t.width≤h/2 →
      (setupCharge s base w+fundedCharge t s.capacity)*w≤
        s.hosts*h*(C*scale J exponent)+s.hosts*(s.oldGroups*radix)*(C*scale J exponent)+copies/(2^J)^saving:=by
  obtain ⟨C,ex,priceIt⟩:=clipped_date_price (3*lead) price 2 (rate+2) rate ratio saving
  refine ⟨C,ex,?_⟩
  filter_upwards [priceIt] with h available
  intro J radix copies base w U s t height ambient positive word short factor prior current rows census
    oldLanes newLanes oldWidth matrix packed join flag width
  have four : 4≤ scale J 2:=by
    change 2^2≤2^(2*(J+1))
    apply Nat.pow_le_pow_right (by decide)
    omega
  have units : 4*U≤ scale J (rate+2):=by
    rw [←scale_mul]
    simpa only [Nat.mul_comm U 4] using (Nat.mul_le_mul four short).trans_eq (Nat.mul_comm ..)
  have paidUnits : U≤ scale J (rate+2):=
    (Nat.le_mul_of_pos_left U (by decide : 0<4)).trans units
  have priceRows:fundingRows s*h≤4*U*h+s.oldGroups*(4*U):=by
    unfold fundingRows
    nlinarith only [prior,current]
  have bound:=funding_volume s t base w h oldLanes newLanes oldWidth matrix packed join flag width
  have area:=Nat.mul_le_mul_left (fundingFactor s t) (funding_area_rows s t h rows census)
  apply available J s.hosts s.oldGroups radix copies (3*fundingFactor s t) (4*U) U U (fundingRows s) w
    (setupCharge s base w+fundedCharge t s.capacity) height ambient _ units paidUnits short word _ _ positive
  · simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 3 factor
  · nlinarith only [priceRows,Nat.zero_le h,Nat.zero_le (s.oldGroups*U),Nat.zero_le (s.oldGroups*U*U)]
  · exact bound.trans (area.trans_eq (by ring))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.FinalInputs

end OAI
