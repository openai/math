import OAI.Hierarchy.DescentResetIngressReachedKeys
import OAI.Hierarchy.DescentResetReceiverPitch

namespace OAI
/-! # Reset ingress at the selected receiver clip and a previously normalized venue -/
namespace Hierarchy.DescentSixParty.NativePitch
open DescentCompiler DescentPackedWalsh DescentDatedAddressBook DescentResetCanvasIngress
open ProtocolRAM DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d k i D n C f g cut tail h₀ z wire hist : ℕ}
    {bs : P→ℕ} {W : MarkedWorld F d P bs} {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ}
    (r : Reached W G q ε S k i z D wire hist)
    (rates : ResetRates G S k D n h₀ C f g cut tail)
    (p payload drift degree previous nextM packet oldLanes primitiveLanes printedBits : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (addr : ℕ→ℕ→Bank) (roster : Bank)
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "rawCap" => (((cal).take i).prod*256)
local notation "count" => (S.groupWidth k tail i)
local notation "b" => (S.localWalshBits p (count+k) f (quota S.rounds))
local notation "pitch" => (incoming S k tail p f payload ordinary i)
local notation "prior" => (DescentNamedFundedChart.previous S k i p D cal pitch)
local notation "canonical" => (PhysicalReset.named G S rates.board k tail i p f g drift degree payload
  0 previous 1 nextM C packet oldLanes primitiveLanes printedBits prior addr roster)
local notation "date" v => (PhysicalReset.selected G S rates.board k tail i p f g drift degree payload
  previous nextM C packet oldLanes primitiveLanes printedBits v addr roster)

/-- The post-Walsh receiver clip and the original three pre-normalization pitches
are absent from the actual reset intake. Only these three stored prior fields enter. -/
theorem selected_ingress_eq (v : StageVenueTail.Date) (floor : ℕ) (branch : v.degree=D)
    (bits : v.paidBits=S.censusBits p) (lanes : v.lanes=pitch) :
    ((date v) floor).ingress=(canonical floor).ingress := by
  let make (degree amount source : ℕ) : DescentResetCanvasIngress.Layout :=
    ⟨⟨S.hostSize i,2^count,source,2^(resetCut S k tail p f payload i),k,degree,rawCap,
      Nat.clog 2 (degree+1)⟩,amount,b,S.firstWidth G.b p,
      S.epochPower^S.priceExponent*(S.grainAt G.b p (i+1)*G.b)⟩
  change make v.degree v.paidBits v.lanes=make D (S.censusBits p) pitch
  rw [branch,bits,lanes]

theorem selected_ingress_price (v : StageVenueTail.Date) (floor w ratio : ℕ)
    (branch : v.degree=D) (bits : v.paidBits=S.censusBits p) (lanes : v.lanes=pitch)
    (hosts : 0<S.hostSize i) (word : w≤ratio*payload) (alive : i<S.length)
    (boundary : i%(S.rounds+1)=S.rounds) (cap : r.placement.cap=rawCap) (small : 8*b≤payload) :
    let s:=((date v) floor).ingress
    let unit:=16*2^k*b
    s.bill 7*w≤ s.hosts*payload*(65536*(s.columns+1)*ratio)+
      s.hosts*s.groups*(65536*(s.columns+1)*ratio*unit)+
      (65536*(s.columns+1)*ratio*(payload+1)^3)*2^(payload/2) := by
  dsimp only
  rw [selected_ingress_eq rates p payload drift degree previous nextM packet oldLanes primitiveLanes
    printedBits ordinary addr roster v floor branch bits lanes]
  exact named_ingress_price r rates p payload drift degree 0 previous 1 nextM packet oldLanes
    primitiveLanes printedBits ordinary addr roster floor w ratio hosts word alive boundary cap small

end
end Hierarchy.DescentSixParty.NativePitch

end OAI
