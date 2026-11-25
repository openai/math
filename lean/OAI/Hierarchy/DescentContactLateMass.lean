import OAI.Hierarchy.DescentContactMaskShape
import OAI.Hierarchy.DescentContactDonorFront
import OAI.Hierarchy.DescentContactSenderMass

namespace OAI
/-! # Recovering true contact grain counts after the compact trunk, from saved original donors -/
namespace Hierarchy.DescentContactMaskShape
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentContactDonorFront
open DescentSixParty.Chronology ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (A : Shape) (donorStart first : ℕ) {w : ℕ}
variable (u : DescentContactSenderDate.Prior A.degree A.lows A.cap A.n A.residual)
local notation "S" => A.sender donorStart
local notation "H" => A.hosts
local notation "G" => A.groups
local notation "M" => A.batch
local notation "N" => donors A
local notation "Q" => sockets A

def program (w : ℕ):=DescentContactSenderMass.Date.program (S) first w
def memory (m : Memory w):=DescentContactSenderMass.Date.output (S) first m
def ticks:=DescentContactSenderMass.Date.ticks (S) first
def bank (j : Fin Q):=DescentContactSenderMass.Date.bank (S) first j

theorem end_eq : DescentContactSenderMass.Date.endAddress (S) first=massEnd A first:=rfl

variable (before : A.idBase donorStart≤first) (r : A.Space donorStart u w) (room : massEnd A first<2^w)
include before r in
theorem prior_banks (s : Bool) (t : Fin A.lows×Fin (2*A.cap)) : ((S).senderBank s t 0).Fits w first:=by
  have seen:=((A.sensor_banks donorStart u r s t).1 0).1
  exact ⟨seen.1,seen.2.1,seen.2.2.trans before⟩

include before r room in
theorem any (m : Memory w) :
    (program A donorStart first w).Exec m (memory A donorStart first m) (ticks A donorStart first) ∧
    CheapCode (program A donorStart first w) ∧
    ∀addr,addr<first ∨ massEnd A first≤addr→memory A donorStart first m addr=m addr:=
  DescentContactSenderMass.Date.any (S) first (prior_banks A donorStart first u before r) m room

def phase : NativePhase w:=
  ⟨program A donorStart first w,ticks A donorStart first,memory A donorStart first,
    (any A donorStart first u before r room (fun _=>0)).2.1⟩

theorem tariff :
    ticks A donorStart first≤DescentContactSenderMass.Date.clockBound (S) first ∧
    DescentStaticWordColumn.names (program A donorStart first w)≤DescentContactSenderMass.Date.nameBound (S) first:=
  DescentContactSenderMass.Date.priced (S) first

variable (xs : Fin A.hosts→Fin A.groups→Fin (DescentOldContactSender.count A.degree A.lows A.cap A.n A.residual)→Cell A.fieldBits)
variable (next : Fin A.hosts→Fin A.degree→Option (Fin A.hosts))
variable (raw : Fin A.lows→Fin (2*A.cap)→Fin A.hosts→Fin A.groups→Cell A.fieldBits)
def realAmount (j : Fin Q) : Fin H→Fin G→Cell A.fieldBits:=
  DescentContactSenderMass.Date.values (S) (fun s t=>(S).sentValue xs s (finProdFinEquiv.symm t) 0) j

include before r room in
theorem published (initial postTrunk : Memory w) (oldRoom : (S).Packed w) (acquired : (S).Before u xs next raw initial)
    (retained : ∀addr,addr<A.idBase donorStart→postTrunk addr=A.memory donorStart u initial addr)
    (packing : M*max (A.fieldBits*(N+1)) A.fieldBits≤w/2)
    (keys : DescentResetLocalRoster.rootSlots A.residual (2^A.n)*(2^A.n+2^A.height)<2^A.fieldBits)
    (j : Fin Q) : Reads (bank A donorStart first j) (realAmount A donorStart xs j) M (memory A donorStart first postTrunk):=by
  have small:=(A.ordered donorStart).2.1.trans_lt ((A.ordered donorStart).2.2.trans_lt ((Nat.le_add_right ..).trans_lt r.extent))
  obtain ⟨old,_⟩:=(S).sources u xs next raw initial r.sender oldRoom small acquired
  apply DescentContactSenderMass.Date.published (S) first (prior_banks A donorStart first u before r) postTrunk
    room oldRoom.positive packing keys _ _ j
  intro s t p
  let coordinate:=finProdFinEquiv.symm t
  obtain ⟨valid,wide⟩:=(A.sensor_banks donorStart u r s coordinate).1 0
  have owned : ((S).senderBank s coordinate 0).base+(row H G M p).val<A.idBase donorStart:=
    (Nat.add_lt_add_left ((row H G M p).isLt.trans_le wide) _).trans_le valid.2.2
  exact (retained _ owned).trans ((A.sender_frame donorStart u r initial _ owned).trans (old s coordinate 0 p))

end
end Hierarchy.DescentContactMaskShape

end OAI
