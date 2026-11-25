import OAI.Hierarchy.DescentResetRankedInvoice

namespace OAI
/-! # The mounted rank and signed-window pages have a linear volume invoice -/
namespace Hierarchy.DescentResetRankedWindows.Layout
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentOrdinaryAtomFieldRAM
open DescentResetSignedScan DescentPackedFlowBatch DescentColonies.SplitRAM
noncomputable section
variable {X K : ℕ} (L : Layout X K)

/-- The raw and source-search dictionaries share their address width. -/
structure PageBounds (E : ℕ) : Prop where
  raw : 2^((L.bits*7+L.originalBits)*L.lanes)≤E
  ticket : 2^(DescentResetSourceTicketBank.span L.originalBits L.lanes)≤E
  sourceReturn : 2^((DescentResetSourceSeekRAM.keyBits 4 K+L.bits)*L.lanes)≤E
  key : 2^(RankInput.width L.bits L.lanes)≤E
  prefixPage : 2^(Ranks.width L.bits L.lanes)≤E
  assembly : 2^(DescentResetFieldAssembler.width L.bits L.lanes)≤E
  signedPage : 2^(DescentNextSignedWindow.Native.ROM.width L.bits L.lanes)≤E

private def panelBill (n : ℕ) := 4+10*n+7*(15*(n+1))
def panelFactor (m : ℕ) := 109+115*m
def scanFactor (n u : ℕ) := 4+n*(4+(2*u+4))+7*scanNames n u

def rankedFactor (X K cap lim : ℕ) :=
  panelFactor 6+panelFactor 2+panelFactor (K*2)+panelFactor ((4*K)*2)+
    panelFactor 2+panelFactor 4+panelFactor 32+panelFactor ((8+2*cap)*2)+
    scanFactor (X*K) (originalWork K lim)+scanFactor (Ranks.count X K) (prefixWork K lim)+
    scanFactor (DescentNextSignedWindow.Native.All.count X cap) (signedTermWork K lim)

private theorem panel {E a : ℕ} (one : 1≤E) (p : a≤E) (m : ℕ) :
    panelBill (m*a) ≤ panelFactor m*E := by
  have h := Nat.mul_le_mul_left m p
  unfold panelBill panelFactor
  nlinarith only [one,h]

private theorem scan {E rows : ℕ} (one : 1≤E) (r : rows≤E) (n u : ℕ) :
    scans n rows u+7*scanNames n u≤ scanFactor n u*E := by
  have constant := Nat.mul_le_mul_left (4+n*4+7*scanNames n u) one
  have variableRows := Nat.mul_le_mul_left (n*(2*u+4)) r
  unfold scans scanFactor
  nlinarith only [constant,variableRows]

theorem ranked_volume (cap lim E : ℕ) (one : 1≤E) (rows : L.hosts*chunks L.groups L.lanes≤E)
    (pages : L.PageBounds E) :
    (L.clockBudget lim+7*L.textBudget lim)+(L.tailClock cap lim+7*L.tailText cap lim) ≤
      rankedFactor X K cap lim*E := by
  let R := L.hosts*chunks L.groups L.lanes
  let signed := DescentNextSignedWindow.Native.All.count X cap
  let assembly := 32*2^(DescentResetFieldAssembler.width L.bits L.lanes)
  let heads := DescentNextSignedWindow.Native.All.headWords cap L.bits L.lanes
  have account :
      (L.clockBudget lim+7*L.textBudget lim)+(L.tailClock cap lim+7*L.tailText cap lim) =
      panelBill L.rawWords+panelBill L.ticketWords+panelBill L.searchWords+panelBill L.returnWords+
      panelBill L.keyWords+panelBill L.prefixWords+panelBill assembly+panelBill heads+
      (scans (X*K) R (originalWork K lim)+7*scanNames (X*K) (originalWork K lim))+
      (scans (Ranks.count X K) R (prefixWork K lim)+7*scanNames (Ranks.count X K) (prefixWork K lim))+
      (scans signed R (signedTermWork K lim)+7*scanNames signed (signedTermWork K lim)) := by
    unfold clockBudget textBudget tailClock tailText inputTime seekTime panelBill rawWords searchWords
      returnWords DescentResetSourceTicketPair.width R signed assembly heads scanNames
    ring
  have raw : panelBill L.rawWords≤panelFactor 6*E := panel one pages.raw 6
  have ticket : panelBill L.ticketWords≤panelFactor 2*E := panel one pages.ticket 2
  have search : panelBill L.searchWords≤panelFactor (K*2)*E := panel one pages.raw _
  have ret : panelBill L.returnWords≤panelFactor ((4*K)*2)*E := panel one pages.sourceReturn _
  have key : panelBill L.keyWords≤panelFactor 2*E := panel one pages.key 2
  have pref : panelBill L.prefixWords≤panelFactor 4*E := panel one pages.prefixPage 4
  have pack : panelBill assembly≤panelFactor 32*E := panel one pages.assembly 32
  have head : panelBill heads≤panelFactor ((8+2*cap)*2)*E := panel one pages.signedPage _
  have a := scan one rows (X*K) (originalWork K lim)
  have b := scan one rows (Ranks.count X K) (prefixWork K lim)
  have c := scan one rows signed (signedTermWork K lim)
  rw [account]
  unfold rankedFactor
  simp only [Nat.add_mul] at head ⊢
  dsimp only [R,signed] at *
  omega

end
end Hierarchy.DescentResetRankedWindows.Layout

end OAI
