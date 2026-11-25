import OAI.Hierarchy.DescentSeedPublicFront
import OAI.Hierarchy.DescentWideSeedCalendarFee
import OAI.Hierarchy.DescentSeedHeaderCharge
import OAI.Hierarchy.DescentOriginalEpochSheetCharge
import OAI.Hierarchy.DescentPublicExteriorRelocation
import OAI.Hierarchy.DescentTerminalExteriorPacketBill
import OAI.Hierarchy.DescentProfileSeatCalendar
import OAI.Hierarchy.DescentPrivateGateScale

namespace OAI
/-! The short seed, every packed selector, and the seventeen exterior columns in the same original input. -/
namespace Hierarchy.DescentWideSeedFlags
open DescentInitialHost DescentSeedRoot DescentPackedEpochShelves DescentTerminalEpochChart DescentPackedProfileInstall
open DescentSixParty DescentCompiler DescentCompiler.TerminalScale DescentSIMDLookup DescentTerminalEpochDecoder Catalyst Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F A : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (R s h C : ℕ)
set_option quotPrecheck false

local notation "gr" => grain (h/2) C
local notation "lut" => 2^(h/2)
local notation "need" => DescentPackedSeed.headerWords X R s h
variable (ss : List (Source A)) (j rest E : ℕ)
local notation "first" => selectorBase X R s h ss.length
local notation "front" => end_ (first+extent gr ss) C gr+17*DescentExteriorShelf.span j rest s E
local notation "packets" => DescentExteriorShelf.rows j rest E

theorem initial_bits (large : 10 ≤ h) (seedWidth : 2*digitsNeeded s ≤ h)
    (profileWidth : 2*unit C ≤ h/2) (portWidth : DescentExteriorShelf.tableBits j rest s ≤ h/2) :
    front*h ≤ 3*((6+90*(X.size+1))*h+320*(X.size+1)*R*digitsNeeded s) +
      30*ss.length*h+48*seatBill ss*unit C+34*packets*h+45*lut*h := by
  let slots_ := (ss.map fun v=>DescentPackedProfileTape.slots v.seats gr).sum
  have seed:=DescentTerminalPackedSeedFlags.header_extent X R s h ([]:List (Source Unit)) seedWidth
  change endInput X R s h ≤ 2*need+1+0+lut at seed
  have rows_ : DescentPackedSeed.rows X R s h ≤ need:=Nat.le_add_left _ _
  have stored:=DescentPackedEpochShelves.extent_le gr ss
  change extent gr ss≤4*slots_+2*ss.length at stored
  have shared := DescentPackedProfileInstall.extent (first+extent gr ss) C gr
  have key : (DescentTerminalEpochBits.width C+1)*gr ≤ h/2:=
    (show (DescentTerminalEpochBits.width C+1)*gr≤(h/2)/2 by
      change unit C * lanes (h/2) (unit C) ≤ (h/2)/2
      rw [Nat.mul_comm]
      exact lanes_fit (h/2) (unit C)).trans (Nat.div_le_self ..)
  have lutSize:=Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) key
  have rSmall : gr ≤ h/2:=Nat.div_le_self ..
  have rFit : gr ≤ lut:=rSmall.trans (show h/2 < 2^(h/2) from Nat.lt_two_pow_self).le
  have outer:=DescentExteriorShelf.span_price j rest s E portWidth
  have addrs : front ≤ 3*need+4*slots_+3*ss.length+34*packets+45*lut := by
    dsimp only [selectorBase] at shared ⊢
    have young : 0 < lut:=Nat.two_pow_pos _
    omega
  have chunks:=chunks_charge (h/2) C ss profileWidth
  change slots_*(h/2) ≤ 2*ss.length*(h/2)+4*seatBill ss*unit C at chunks
  have expanded : slots_*h ≤ 6*ss.length*h+12*seatBill ss*unit C := calc
    _ ≤ slots_*(3*(h/2)) := Nat.mul_le_mul_left _ (by omega)
    _ = 3*(slots_*(h/2)) := by ring
    _ ≤ 3*(2*ss.length*(h/2)+4*seatBill ss*unit C) := Nat.mul_le_mul_left _ chunks
    _ ≤ 6*ss.length*h+12*seatBill ss*unit C := by
      have z:=Nat.mul_le_mul_left (6*ss.length) (Nat.div_le_self h 2)
      nlinarith only [z]
  have census:=DescentPackedSeed.startup_bits X R s h seedWidth
  have top:=Nat.mul_le_mul_right h addrs
  nlinarith only [top,expanded,census,Nat.zero_le (ss.length*h)]

variable (S : AtomSchedule)
local notation "rate" => (S.rounds+1)*(S.hostGain+S.capGain+1)+11
/-- The first summand can be issued as a single date-zero charge in the same native calendar.
The other terms use the original exterior port volume and one shared small ROM. -/
theorem original_tariff (bw factor T B : ℕ) (large : 10 ≤ h) (cut : 0 < B)
    (age : S.height=Nat.log 2 h/(2*B)) (copies : R=S.copies) (length_ : ss.length ≤ S.length)
    (dates : S.length ≤ S.initialSites) (size : 10*(X.size+1) ≤ S.initialSites)
    (seats : seatBill ss ≤ S.length*S.batch) (sBound : s ≤ h) (_nonzero : 0 < S.copies)
    (seedWidth : 2*digitsNeeded s ≤ h) (profileWidth : 2*unit C ≤ h/2)
    (portWidth : DescentExteriorShelf.tableBits j rest s ≤ h/2)
    (arch : bw ≤ factor*h) (ambient : 2^h≤2*(S.initialSites*R))
    (realRows : R=2^(j+(j+rest))) (bulk : h≤32*((2^j)*s)) (time : T ≤ s) :
    front*bw*T ≤ factor*(originalBill S C B h*T)+1133*factor*((R*s)*(S.initialSites+T*E)) := by
  let D:=scale S.height rate
  let H:=S.hostSize 0*(S.groupCount 0*S.radix)
  let fund:=(R*s)*(S.initialSites+T*E)
  have hd : 0 < rate:=by omega
  have ages : S.height+1 ≤ D:=(show S.height+1≤2^S.height from Nat.lt_two_pow_self).trans
    (Nat.pow_le_pow_right (by decide) (by have:=Nat.le_mul_of_pos_left (S.height+1) hd;omega))
  have rows0 : H=S.initialSites*R := by
    rw [copies]
    dsimp [H,AtomSchedule.hostSize,AtomSchedule.groupCount,AtomSchedule.copies]
    rw [pow_succ S.radix S.length]
    simp only [Nat.mul_one]
    ring
  have source : X.size+1 ≤ S.initialSites:=by omega
  have some : 1 ≤ S.initialSites:=by omega
  have rawSize:=Nat.mul_le_mul_right R source
  have div:=seed_digits sBound cut
  rw [←age] at div
  have dig : (X.size+1)*R*digitsNeeded s ≤ H*(2*B*D):=by
    rw [rows0]
    exact Nat.mul_le_mul rawSize (div.trans (Nat.mul_le_mul_left _ ages))
  have cap : seatBill ss ≤ H*D := selector_seats S (i:=0) (Nat.zero_le _) seats
  have entries : ss.length ≤ S.initialSites:=length_.trans dates
  have fixed0:=Nat.mul_le_mul_right h source
  have t0:=Nat.mul_le_mul_right h entries
  have base:=Nat.mul_le_mul_right h some
  have chk:=initial_bits X R s h C ss j rest E large seedWidth profileWidth portWidth
  have cmp : front*h ≤ originalBill S C B h+34*packets*h+45*lut*h:=by
    change front*h≤328*S.initialSites*h+(1920*B+48*unit C)*H*D+34*packets*h+45*lut*h
    nlinarith only [chk,dig,cap,t0,base,fixed0,Nat.mul_le_mul_right (unit C) cap,Nat.zero_le (S.initialSites*h)]
  have pack:=DescentTerminalCompiledPrefix.AddressPlan.packet_bill R s E j rest h h 1 realRows bulk (by simp)
  have extM:packets*h*T≤32*fund:=by
    have t:=Nat.mul_le_mul_right T pack
    dsimp [fund,DescentExteriorShelf.rows]
    nlinarith only [t,Nat.zero_le ((R*s)*S.initialSites)]
  have funded:=table_fund large ambient
  have rom:lut*h*T ≤ fund:=by
    calc
      _ ≤ (S.initialSites*R)*s := Nat.mul_le_mul funded time
      _ ≤ fund := by dsimp [fund];rw [Nat.mul_add];nlinarith only [Nat.zero_le ((R*s)*(T*E))]
  calc
    _ ≤ factor*((front*h)*T) := by
      have a:=Nat.mul_le_mul_right T (Nat.mul_le_mul_left front arch)
      nlinarith only [a]
    _ ≤ factor*(originalBill S C B h*T+(34*packets*h)*T+(45*lut*h)*T) :=
      Nat.mul_le_mul_left _ (by simpa only [Nat.add_mul] using Nat.mul_le_mul_right T cmp)
    _ = factor*(originalBill S C B h*T+(34*(packets*h*T)+45*(lut*h*T))) := by ring
    _ ≤ factor*(originalBill S C B h*T+(34*(32*fund)+45*fund)) :=
      Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.add_le_add
        (Nat.mul_le_mul_left 34 extM) (Nat.mul_le_mul_left 45 rom)) _)
    _ = factor*(originalBill S C B h*T)+1133*factor*fund := by ring

end
end Hierarchy.DescentWideSeedFlags

end OAI
