import OAI.Hierarchy.DescentPrivateDonorDateLedger
import OAI.Hierarchy.DescentPrivateDonorInstallBill
import OAI.Hierarchy.DescentPrivateInstalledWidth
import OAI.Hierarchy.DescentResidentDonorClock
import OAI.Hierarchy.DescentTerminalEpochBits
import OAI.Hierarchy.DescentPrivateWholeDonorEnd
import OAI.Hierarchy.DescentResidentGeometryPrice
import OAI.Hierarchy.DescentPrivateDonorUniform
import OAI.Hierarchy.DescentPrivateGatherPhase
import OAI.Hierarchy.DescentPrivateNativeReplay

namespace OAI
/-! # Dating the actual ordinary donor instructions in the selected physical RAM history -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentHostDegree DescentPackedPrivateSum DescentRawCablePanel DescentSIMDLookup
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
variable {S : DescentCompiler.AtomSchedule} {q u ε : ℝ} {k j i z₀ D₀ z D wire hist bw : ℕ}
variable {W₀ W : MarkedWorld F d P bits} {start : Reached W₀ G q ε S k j z₀ D₀ wire hist}
variable {source : Reached W G q ε S k i z D wire hist}
section
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
variable {n : Normalize ((T.result he).state c)} {z' D' : ℕ}
variable {target : Reached n.result G q ε S k (i+1) z' D' wire hist} (ticket : OrdinaryLink source he T c n target)

open DescentCompiler.TerminalScale DescentStaticWordColumn

local notation "rows₀" => hostRows (S.hostSize i)
local notation "pad₀" => source.valid.host.trans (hostPad (S.hostSize i))
local notation "short₀" => max (k+3) (Nat.clog 2 (source.placement.degree+1))
local notation "prof₀" => DescentTerminalEpochBits.width G.C
local notation "fmt₀" => ticket.depotShape short₀
local notation "match₀" => DescentPacking.PackedMatch.Local.shape (2^k) source.placement.degree (2*source.placement.cap) prof₀

/-- The operands of the two native procedures at one selected ordinary transition. -/
structure DonorVisit (header h bw K p : ℕ) where
  base : ℕ
  setupBase : ℕ
  priorHub : ProtocolRAM.Bank
  tables : DepotRAM.Tables6
  addresses : DepotRAM.Resident.Addressed fmt₀ (2^(k+1))
  banks : DescentSIMDLookup.Banks
  live : 0<ticket.installedDonorWidth short₀ prof₀
  wide : 2*(ticket.installedDonorWidth short₀ prof₀)≤h
  fits : MeterPort.Fits ticket (OrdinaryLink.sizedDepotPort rows₀ pad₀ base h (ticket.installedDonorWidth short₀ prof₀)) header bw K
  quantum : T.z=S.grainAt G.b p i

namespace DonorVisit
variable {ticket}
variable {header h K p : ℕ} (r : DonorVisit ticket header h bw K p)

def age (_ : DonorVisit ticket header h bw K p) := i

def amount (_ : DonorVisit ticket header h bw K p) :=ticket.installedDonorWidth short₀ prof₀
def «fields» :=DepotRAM.Resident.fields fmt₀ match₀
    (DepotRAM.Resident.addressed fmt₀ r.addresses rows₀) rows₀
    (S.groupCount i) (lanes h r.amount)
def tableCount (_ : DonorVisit ticket header h bw K p) := 2*DepotRAM.Binary.count (ticket.depotShape short₀)+3+2^(k+1)
def gatherGrade := DepotRAM.fieldWork r.fields+25*r.tableCount+200
def grade := r.gatherGrade+venueGrade (2^k) source.placement.degree source.placement.cap

def venue : NativePhase bw :=
  DepotRAM.Resident.Dynamic.Placement.issuedPhase rows₀ (S.groupCount i) (lanes h r.amount)
    source.placement.degree (2^k) (2*source.placement.cap) short₀ source.placement.cap prof₀ bw
    (ticket.donorStart short₀ prof₀ rows₀ h r.setupBase) r.addresses.source.peers.roster r.priorHub
    (DepotRAM.Resident.addressed fmt₀ r.addresses rows₀).terrain

def install : NativePhase bw :=
  DepotRAM.Setup.phase (ticket.depotShape short₀)
    (DescentPacking.PackedMatch.Local.shape (2^k) source.placement.degree (2*source.placement.cap) prof₀)
    (2^(k+1)) rows₀ (S.groupCount i) (lanes h r.amount) r.amount r.setupBase
    source.placement.cap prof₀ G.C G.k source.placement.z G.b (2^(packExponent 20 T.Δ)+2) bw

def port : MeterPort source := OrdinaryLink.sizedDepotPort rows₀ pad₀ r.base h r.amount

def gather : NativePhase bw :=DepotRAM.phase r.tables r.fields r.banks (r.base+1)
  rows₀ (S.groupCount i) (lanes h r.amount) bw

def mainBill : ℕ := ticket.donorDateBill rows₀ pad₀ r.base h r.amount header K
  r.tables r.fields r.banks (r.base+1) bw

def bill := (r.mainBill+(r.install.ticks+names r.install.program)*bw)+(r.venue.ticks+names r.venue.program)*bw

theorem billed (block : 0<S.radix) (hosts : 0<S.hostSize i)
    (pages : 2^(h/2)≤S.hostSize i)
    (grain : ProtocolRAMPortScale.bitWidth (S.grainAt G.b p i)≤S.hostSize i) :
    r.bill≤S.hostSize i*h*((2*K)*(1274+6*r.grade))+
       S.hostSize i*(S.groupCount i*S.radix)*((2*K)*(4*r.amount*(342+2*r.grade))) := by
  have covers := (ticket.installed_donor_widths short₀ prof₀).1
  have padded := hostPad (S.hostSize i)
  have main:=ticket.donor_date_bill short₀ rows₀ pad₀ r.base h r.amount header K
    r.tables r.fields r.banks (r.base+1) bw covers r.wide r.fits r.live (hosts.trans_le padded) block
    (by rw [r.quantum];exact grain.trans padded) (pages.trans padded)
  have setup : (r.install.ticks+names r.install.program)*bw≤
      rows₀*h*(K*(107+25*r.tableCount))+rows₀*(S.groupCount i)*(K*(200*r.amount)) := by
    unfold install
    rw [DepotRAM.Setup.names]
    apply donor_install_bill (hosts.trans_le padded) r.fits.overhead (pages.trans padded)
      (volume _ _ h r.amount r.live r.wide)
      (ticket.installed_donor_books short₀ prof₀ rows₀ h)
  have geometry:=DepotRAM.Resident.Dynamic.Placement.geometry_word_bill rows₀ (S.groupCount i) (lanes h r.amount)
    source.placement.degree (2^k) (2*source.placement.cap) short₀ source.placement.cap prof₀ bw
    (ticket.donorStart short₀ prof₀ rows₀ h r.setupBase) r.addresses.source.peers.roster r.priorHub
    (DepotRAM.Resident.addressed fmt₀ r.addresses rows₀).terrain rfl r.live r.wide
    (ticket.ownerCode_fit short₀ prof₀) (pages.trans padded) r.fits.overhead
  have venueTickets:=DepotRAM.Resident.terrain_work fmt₀ r.addresses rows₀
  apply (donor_venue_bill block venueTickets (donor_installed_row block main setup) geometry).trans
  change rows₀*h*(K*(1274+6*r.grade))+rows₀*(S.groupCount i*S.radix)*(K*(4*r.amount*(342+2*r.grade))) ≤ _
  simpa only [Nat.mul_assoc] using
    Nat.add_le_add (pad_bill (work:=h) (unit:=K*(1274+6*r.grade)) hosts)
      (pad_bill (work:=S.groupCount i*S.radix) (unit:=K*(4*r.amount*(342+2*r.grade))) hosts)

end DonorVisit
end

variable {p header h K : ℕ}

/-- Ordinary records are tied to the specific selected ticket and previous memory.
Reset and earlier preparation are accounted for in their own native procedures. -/
inductive DonorDiary (start : Reached W₀ G q ε S k j z₀ D₀ wire hist) (header h bw K p : ℕ) :
    {W : MarkedWorld F d P bits}→{i z D : ℕ}→{source : Reached W G q ε S k i z D wire hist}→
    {path : Path start source}→MeterCalendar start header bw path→Type 2 where
  | seed : DonorDiary start header h bw K p .seed
  | ordinary {W : MarkedWorld F d P bits} {i z D z' D' : ℕ}
      {source : Reached W G q ε S k i z D wire hist} {path : Path start source}
      {earlier : MeterCalendar start header bw path}
      (old : DonorDiary start header h bw K p earlier) {u : ℝ} {he : 0≤ε} {T : StageInput W G u ε}
      {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
      {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
      {ticket : OrdinaryLink source he T c n target} (r : DonorVisit ticket header h bw K p)
      (prepare : NativePhase bw) :
      DonorDiary start header h bw K p (earlier.ordinary ticket r.port (prepare.seq ((r.install.seq r.venue).seq r.gather)))
  | ordinaryAfter {W : MarkedWorld F d P bits} {i z D z' D' : ℕ}
      {source : Reached W G q ε S k i z D wire hist} {path : Path start source}
      {earlier : MeterCalendar start header bw path}
      (old : DonorDiary start header h bw K p earlier) {u : ℝ} {he : 0≤ε} {T : StageInput W G u ε}
      {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
      {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
      {ticket : OrdinaryLink source he T c n target} (r : DonorVisit ticket header h bw K p)
      (prepare finish : NativePhase bw) :
      DonorDiary start header h bw K p (earlier.ordinary ticket r.port
        ((prepare.seq ((r.install.seq r.venue).seq r.gather)).seq finish))
  | reset {W : MarkedWorld F d P bits} {i z D n hC C f g cut tail : ℕ}
      {source : Reached W G q ε S k i z D wire hist} {path : Path start source}
      {earlier : MeterCalendar start header bw path} (old : DonorDiary start header h bw K p earlier)
      {ctl : ResetRates G S k D n hC C f g cut tail} (closed : ClosedReset source ctl) (emit : NativePhase bw) :
      DonorDiary start header h bw K p (earlier.reset closed emit)

namespace DonorDiary
variable {path : Path start source} {calendar : MeterCalendar start header bw path}
variable (diary : DonorDiary start header h bw K p calendar)

/-- The numerical register and opcode counts are taken from the stored program. -/
structure Entry where
  cost : ℕ := 0
  work : ℕ := 0
  amount : ℕ := 0

def rows : ℕ→Entry := by
  induction diary with
  | seed=>exact fun _=>{}
  | ordinary _ r _ prev | ordinaryAfter _ r _ _ prev=>
    exact Function.update prev r.age ⟨r.bill,r.grade,r.amount⟩
  | reset _ _ _ prev=>exact prev

def total : ℕ := by
  induction diary with
  | seed=>exact 0
  | ordinary _ r _ prev | ordinaryAfter _ r _ _ prev=>exact prev+r.bill
  | reset _ _ _ prev=>exact prev

theorem no_future {u : ℕ} (future : i≤u) : diary.rows u={} := by
  induction diary with
  | seed=>rfl
  | ordinary old r _ ih | ordinaryAfter old r _ _ ih=>
    change Function.update old.rows r.age _ u=_
    have lt : r.age<u :=future
    rw [Function.update_of_ne lt.ne']
    exact ih lt.le
  | reset old closed emit ih=>exact ih (by omega)

theorem total_rows : (∑v ∈ Finset.range i,(diary.rows v).cost)=diary.total := by
  induction diary with
  | seed=>simp [rows,total]
  | ordinary old r _ ih | ordinaryAfter old r _ _ ih=>
    rw [Finset.sum_range_succ]
    change (∑v ∈ Finset.range r.age,(Function.update old.rows r.age _ v).cost)+
      (Function.update old.rows r.age _ r.age).cost=old.total+r.bill
    rw [Function.update_self]
    apply congrArg (·+r.bill)
    refine Eq.trans (Finset.sum_congr rfl (fun v hv=>?_)) ih
    rw [Function.update_of_ne (Finset.mem_range.mp hv).ne]
  | reset old closed emit ih=>
    rw [Finset.sum_range_succ]
    change (∑v ∈ Finset.range _,(old.rows v).cost)+(old.rows _).cost=old.total
    rw [ih,old.no_future (le_refl _)]
    exact Nat.add_zero _

theorem entries_sum (cut : i≤S.length+1) : (∑v : Fin (S.length+1),(diary.rows v.val).cost)=diary.total := by
  rw [Fin.sum_univ_eq_sum_range (fun v => (diary.rows v).cost) (S.length+1),←diary.total_rows]
  symm
  apply Finset.sum_subset_zero_on_sdiff (Finset.range_mono cut) _ (fun _ _=>rfl)
  intro v hv
  have live : i≤v :=by simpa using (Finset.mem_sdiff.mp hv).2
  rw [diary.no_future live]

theorem rows_charge (radix : 0<S.radix) (rooms : ∀v,0<S.hostSize v ∧ 2^(h/2)≤S.hostSize v ∧
    ProtocolRAMPortScale.bitWidth (S.grainAt G.b p v)≤S.hostSize v) (v : ℕ) :
    (diary.rows v).cost≤S.hostSize v*h*((2*K)*(1274+6*(diary.rows v).work))+
      S.hostSize v*(S.groupCount v*S.radix)*((2*K)*(4*(diary.rows v).amount*(342+2*(diary.rows v).work))) := by
  induction diary with
  | seed=>exact Nat.zero_le _
  | ordinary old r _ ih | ordinaryAfter old r _ _ ih=>
    by_cases eqv : v=r.age
    · subst v
      simpa only [rows,Function.update_self,DonorVisit.age] using
        r.billed radix (rooms r.age).1 (rooms r.age).2.1 (rooms r.age).2.2
    · simpa only [rows,Function.update_of_ne eqv] using ih
  | reset old closed emit ih=>exact ih

end DonorDiary
end
end Hierarchy.DescentSixParty.Chronology

end OAI
