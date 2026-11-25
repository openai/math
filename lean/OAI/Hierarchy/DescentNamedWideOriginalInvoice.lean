import OAI.Hierarchy.DescentNamedVerdictPrice
import OAI.Hierarchy.DescentWideSeedOriginalInvoice

namespace OAI
/-! The shared profile chart on the actual issued named epoch tree has the paid original header. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice DescentTerminalEpochDecoder
open DescentPackedEpochShelves DescentPackedProfileInstall DescentSeedRoot Catalyst Computability.BorderVNP.Crossing
open DescentWideSeedFlags
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n stageH C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n stageH C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate stageH C*(1-(2-G.rate)/4)^S.rounds≤1/2)
set_option quotPrecheck false
local notation "rs" => (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
local notation "o" => inputOrder X G S ordinary reset branch positive room shorten
local notation "s" => S.firstWidth G.b p
variable (h bw : ℕ) (fit : S.firstWidth G.b p<2^bw)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten bw fit
local notation "ss" => (ch).layout
local notation "gr" => grain (h/2) G.C

theorem issued_wide_shape : (ss).length ≤ S.length ∧ seatBill ss ≤ S.length*S.batch :=by
  have shape:=epochs_layout G _ _ rs o (seedChart X S.copies s bw fit)
  have levels : (ss).length = S.height*S.rounds:=by simpa [normalizedPackedChart,packedChart,seedChart] using shape.1
  have rows : seatBill ss=epochSeats G _ _ rs:=by simpa [normalizedPackedChart,packedChart,seedChart,seatBill] using shape.2
  have calendar : (ss).length ≤ S.length:=by
    rw [levels];unfold AtomSchedule.length;rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm S.rounds];omega
  exact ⟨calendar,rows.trans_le (seats X G S ordinary reset branch positive room shorten)⟩

theorem wide_original_tariff (j rest E factor T B : ℕ) (large : 10 ≤ h) (cutoff : 0 < B)
    (age : S.height=Nat.log 2 h/(2*B)) (dates : S.length ≤ S.initialSites)
    (sBound : s ≤ h) (nonzero : 0 < S.copies) (seedWidth : 2*digitsNeeded s ≤ h)
    (profileWidth : 2*unit G.C ≤ h/2) (portWidth : DescentExteriorShelf.tableBits j rest s ≤ h/2)
    (arch : bw ≤ factor*h) (ambient : 2^h≤2*(S.initialSites*S.copies))
    (realRows : S.copies=2^(j+(j+rest))) (bulk : h≤32*((2^j)*s)) (time : T ≤ s) :
    let first:=selectorBase X S.copies s h (ss).length
    (end_ (first+extent gr ss) G.C gr+17*DescentExteriorShelf.span j rest s E)*bw*T ≤ factor*(originalBill S G.C B h*T)+1133*factor*((S.copies*s)*(S.initialSites+T*E)) := by
  obtain ⟨calendar,paidSeats⟩:=issued_wide_shape X G S ordinary reset branch positive room shorten bw fit
  exact DescentWideSeedFlags.original_tariff X S.copies s h G.C ss j rest E S bw factor T B
    large cutoff age rfl calendar dates room paidSeats
    sBound nonzero seedWidth profileWidth portWidth arch ambient realRows bulk time

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
