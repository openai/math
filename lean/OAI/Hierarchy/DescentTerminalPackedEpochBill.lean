import OAI.Hierarchy.DescentPackedEpochBill
import OAI.Hierarchy.DescentPackedEpochReader

namespace OAI
/-! # Packed rejection cost for the common independent-copy coefficient run -/
namespace Hierarchy.DescentBundleHistory
open DescentSixParty DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalEpochDecoder DescentPackedEpochShelves DescentPackedEpochFold
open DescentSeedRoot Catalyst Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
set_option quotPrecheck false
local notation "r" => (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
local notation "o" => normalizedIssuedInputOrders X G S ordinary reset branch positive room shorten
local notation "q" => S.firstWidth G.b p
variable (w : ℕ) (sFit : S.firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w sFit

theorem paid_packed_verdict (lo seed : ℕ) (count exterior : ℕ→ℕ) (digits : 2*unit G.C ≤ w) :
    let R:=grain w G.C
    let ts:=controls lo G.C R (ch).layout count exterior
    bill seed (final lo G.C R (ch).layout) ts*w≤64*w+578*S.length*w+680*(S.length*S.batch)*unit G.C := by
  have paid:=invoice lo G.C w seed (ch).layout count exterior digits
  have shape:=epochs_layout G _ _ r o (seedChart X S.copies q w sFit)
  have dates : (ch).layout.length=S.height*S.rounds:=by simpa [normalizedPackedChart,actualWith,seedChart] using shape.1
  have seats : seatBill (ch).layout=epochSeats G _ _ r:=by simpa [normalizedPackedChart,actualWith,seedChart,seatBill] using shape.2
  have levels : (ch).layout.length ≤ S.length:=by
    rw [dates];unfold AtomSchedule.length;rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm S.rounds];omega
  have purchase:=(seats.trans_le (normalizedSeats X G S ordinary reset branch positive room shorten))
  calc
    _ ≤ _ := paid
    _ ≤ _ := Nat.add_le_add
      (Nat.add_le_add_left (Nat.mul_le_mul_right w (Nat.mul_le_mul_left 578 levels)) _)
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 680 purchase))

end
end Hierarchy.DescentBundleHistory

end OAI
