import OAI.Hierarchy.DescentWideSeedOriginalInvoice
import OAI.Hierarchy.DescentWideFullPinInvoice
import OAI.Hierarchy.DescentWideOriginalCalendarBill
import OAI.Hierarchy.DescentPhysicalPortCount
import OAI.Hierarchy.DescentTerminalSeedCircuit

namespace OAI
/-! # Full startup charge of the physical seed circuit on a dated input -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentPackedEpochShelves DescentPackedProfileInstall DescentSeedRoot
open DescentTerminalEpochChart DescentTerminalEpochDecoder DescentWideSeedFlags DescentExterior
open Catalyst CorrectionFrame
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F A : Type} [Field F] [Fintype A] {cp nP : ℕ}
variable (X : Approximation F cp nP) (S : AtomSchedule) (s h C bw : ℕ)
variable (ss : List (Source A)) (seed : Select X S.copies s → A)
variable {j rest q W K piece codes rows pub : ℕ}
local notation "E" => Fintype.card (Port nP X.width)
local notation "R" => S.copies
local notation "D" => (R*s)
local notation "extra" => DescentTerminalPublicIdentity.total K W q piece codes rows pub
local notation "original" => Port (D*nP) (copiesWidth D X.width)
local notation "All" => DescentTerminalFullPins.Candidate (A ⊕ Hidden E j rest s) K W q piece rows
local notation "net" => DescentTerminalSeedChip.circuit X (fun i : Select X R s => (Sum.inl (Sum.inl (Sum.inl (seed i))) : All))
local notation "gr" => grain (h/2) C
local notation "front" => end_ (selectorBase X R s h ss.length+extent gr ss) C gr+17*DescentExteriorShelf.span j rest s E

/-- The three chart measurements are precisely its number of stored dates,
its number of selector seats and its pin count. The input embeds the original
seed in the full candidate's three left branches. -/
theorem physical_initial_bill (factor T B compiler budget bus extraRate : ℕ)
    (room : 10*(X.size+1) ≤ S.initialSites)
    (length : ss.length ≤ S.length) (seats : seatBill ss ≤ S.length*S.batch)
    (pins : Fintype.card A ≤ 80*R*(X.size+1)*(s.log2+1)+(S.length*S.batch)*DescentTerminalEpochBits.width C)
    (large : 10 ≤ h) (cutoff : 0 < B) (age : S.height=Nat.log 2 h/(2*B))
    (dates : S.length ≤ S.initialSites) (sBound : s ≤ h) (nonzero : 0 < R)
    (seedWidth : 2*digitsNeeded s ≤ h) (profileWidth : 2*unit C ≤ h/2)
    (portWidth : DescentExteriorShelf.tableBits j rest s ≤ h/2)
    (arch : bw ≤ factor*h) (ambient : 2^h ≤ 2*(S.initialSites*R))
    (realRows : R=2^(j+(j+rest))) (bulk : h ≤ 32*((2^j)*s)) (time : T ≤ s)
    (mode : q*(W*piece) ≤ bw) (decode : budget+1 ≤ bus*bw)
    (calendar : originalBill S C B h*T ≤ 2*(S.initialSites*D))
    (appendix : extra*bw*T ≤ extraRate*(D*(S.initialSites+T*E))) :
    (4*((net).cells+(net).internal)+Fintype.card All+Fintype.card original+
      compiler*(front+extra)*(budget+1))*T ≤
      (5+extraRate+compiler*bus*(1135*factor+extraRate))*(D*(S.initialSites+T*E)) :=by
  let fund:=D*(S.initialSites+T*E)
  let init:=originalBill S C B h
  let raw:=80*R*(X.size+1)*(s.log2+1)
  let profiles:=(S.length*S.batch)*DescentTerminalEpochBits.width C
  have both:5*raw+profiles ≤ init:=choice_bits S C B h s X.size cutoff age sBound (by omega)
  have chip:(net).cells+(net).internal ≤ raw:=by
    rw [DescentTerminalSeedChip.size]
    simpa only [DescentSeedRoot.Select,DescentSeedRoot.CountKey,Fintype.card_prod,Fintype.card_fin] using
      (select_bound X R s)
  have picks:Fintype.card A ≤ raw+profiles:=pins
  have initial:4*((net).cells+(net).internal)+Fintype.card A ≤ init:=by omega
  have pins:=DescentTerminalFullPins.candidate_card_paid A E j rest s K W q piece rows codes pub bw mode
  rw [←realRows] at pins
  have exterior:Fintype.card original=D*E:=physical_port_count X D
  have f0:S.initialSites*D ≤ fund:=by
    rw [Nat.mul_comm S.initialSites];exact Nat.mul_le_mul_left _ (Nat.le_add_right ..)
  have f1:D*E*T ≤ fund:=by
    change _ ≤ D*(S.initialSites+T*E)
    calc
      _ = D*(T*E) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_add_left ..)
  have cal:init*T ≤ 2*fund:=calendar.trans (Nat.mul_le_mul_left _ f0)
  have frontPay:=DescentWideSeedFlags.original_tariff X R s h C ss j rest E S bw factor T B
    large cutoff age rfl length dates room seats sBound nonzero seedWidth profileWidth portWidth arch ambient realRows bulk time
  have zero:front*bw*T ≤ 1135*factor*fund:=by
    change _ ≤ factor*(init*T)+1133*factor*fund at frontPay
    exact frontPay.trans (by nlinarith only [Nat.mul_le_mul_left factor cal])
  have scalar:4*((net).cells+(net).internal)+Fintype.card All+Fintype.card original ≤ init+3*(D*E)+extra*bw:=by
    rw [exterior]
    have base : 2*E*D=2*(D*E):=by ring
    rw [base] at pins
    omega
  have rawPay:(4*((net).cells+(net).internal)+Fintype.card All+Fintype.card original)*T ≤ (5+extraRate)*fund:=by
    have gain:=Nat.mul_le_mul_right T scalar
    change extra*bw*T ≤ extraRate*fund at appendix
    nlinarith only [gain,cal,f1,appendix]
  have firstPay:compiler*(front+extra)*(budget+1)*T ≤ compiler*bus*(1135*factor+extraRate)*fund:=by
    change extra*bw*T ≤ extraRate*fund at appendix
    calc
      _ ≤ compiler*(front+extra)*(bus*bw)*T :=
        Nat.mul_le_mul_right T (Nat.mul_le_mul_left (compiler*(front+extra)) decode)
      _ = compiler*bus*(front*bw*T+extra*bw*T) := by ring
      _ ≤ compiler*bus*(1135*factor*fund+extraRate*fund) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add zero appendix)
      _ = _ := by ring
  calc
    _ = (4*((net).cells+(net).internal)+Fintype.card All+Fintype.card original)*T+compiler*(front+extra)*(budget+1)*T := by ring
    _ ≤ _ := (Nat.add_le_add rawPay firstPay).trans (le_of_eq (by ring))

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
