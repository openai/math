import OAI.Hierarchy.DescentContactDonorFront
import OAI.Hierarchy.DescentPhysicalResetStemFront
import OAI.Hierarchy.DescentPhysicalResetEvidence
import OAI.Hierarchy.DescentPhysicalResetPeers
import OAI.Hierarchy.DescentContactPreROM
import OAI.Hierarchy.DescentResetTrunkCompactScalar

namespace OAI
/-! # Chronological execution from the preceding physical actor census through all receiver stems -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront
open DescentSixParty.Chronology DescentSIMDLookup ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable (v : CandidateFront) (base : ℕ)
local notation "p₀" => v.peer
def contactLayout : DescentContactPreROM.Layout :={v.contact with first:=v.donorEnd base}
local notation "C" => v.contactLayout base
local notation "scalarBase" => (p₀).endAddress (v.peers base)

/-- All fields here are fixed operand instructions or previously reserved bank locations. -/
structure Scene where
  evidence : v.Evidence
  rotorPorts : ℕ
  rotor : NonlinearExpanders.Graph v.contact.n rotorPorts
  boardReads : Fin v.contact.oldFields→Expr
  donor : DescentContactSenderDate.Prior v.donor.degree v.donor.lows v.donor.cap v.donor.n v.donor.residual
  donorSlots : v.contact.half=v.donor.lows*(2*v.donor.cap)
  peers : (p₀).Inputs
  count : Bank
  inverse : Bank
  rawHeader : Expr
  stems : v.StemInputs

variable (s : v.Scene)
def sensor (d : Bool) (j : Fin v.contact.half) (f : Fin 5) : Expr :=
  v.donor.priorSensor (v.donorStart base) d (j.cast s.donorSlots) f

structure SceneRoom (w : ℕ) : Prop where
  before : ∀q i,(s.evidence.source q i).Fits w base
  sameLanes : v.oldLanes=(p₀).evidenceLanes
  evidenceFit : v.rawTablesEnd base<2^w
  donor : v.donor.Space (v.donorStart base) s.donor w
  contact : (C).Space s.boardReads (v.sensor base s) w
  peers : (p₀).Room s.peers (v.peers base) w
  count : s.count.Fits w scalarBase
  inverse : s.inverse.Fits w scalarBase
  scalar : s.rawHeader.Fits w scalarBase
  parent : v.parentStart base<2^w
  stems : v.StemRoom s.stems base w

variable {w : ℕ} (safe : v.SceneRoom base s w)
def originalPhase : NativePhase w :=
  ⟨v.originalEvidence s.evidence base w,v.evidenceClock s.evidence base,v.evidenceImage s.evidence base,
    (v.evidence_any s.evidence base (fun _=>0) safe.before safe.sameLanes safe.evidenceFit).2.2⟩
def donorPhase : NativePhase w := v.donor.native (v.donorStart base) s.donor safe.donor
def contactPhase : NativePhase w :=
  ⟨(C).program s.rotor s.boardReads (v.sensor base s) safe.contact,
   (C).ticks s.rotor s.boardReads (v.sensor base s) safe.contact,
   (C).memory s.rotor s.boardReads (v.sensor base s) safe.contact,
   ((C).any s.rotor s.boardReads (v.sensor base s) safe.contact (fun _=>0)).2.1⟩
private def nativeFromRun (code : Procedure w) (ticks : ℕ) (image : Memory w → Memory w)
    (frame : Prop) (receipt : code.Exec (fun _ => 0) (image (fun _ => 0)) ticks ∧ frame ∧ CheapCode code) :
    NativePhase w :=
  ⟨code, ticks, image, @And.right _ _ (@And.right _ _ receipt)⟩

def triplePhase : NativePhase w :=
  nativeFromRun ((p₀).program s.peers (v.peers base) w) ((p₀).ticks s.peers (v.peers base))
    ((p₀).memory s.peers (v.peers base)) _ ((p₀).any s.peers (v.peers base) (fun _ => 0) safe.peers)
def scalarPhase (w : ℕ) := DescentResetTrunkCompactScalar.phase w v.newHosts scalarBase s.count s.inverse s.rawHeader
def parentStemPhase : NativePhase w :=
  ⟨v.stemFront s.stems base w safe.stems,v.stemTime s.stems base w safe.stems,v.stemImage s.stems base safe.stems,
   (v.stem_any s.stems base safe.stems (fun _=>0)).2.2⟩

def received : NativePhase w :=
  (((((v.originalPhase base s safe).seq (v.donorPhase base s safe)).seq (v.contactPhase base s safe)).seq
     (v.triplePhase base s safe)).seq (v.scalarPhase base s w)).seq (v.parentStemPhase base s safe)

private def segment (p : NativePhase w) (lo hi : ℕ) : Prop :=
  lo≤hi ∧ ∀m,p.Runs m ∧ ∀i,i<lo ∨ hi≤ i → p.image m i=m i

private theorem adjacent {p q : NativePhase w} {lo mid hi : ℕ} (a : segment p lo mid) (b : segment q mid hi) :
    segment (p.seq q) lo hi := by
  refine ⟨a.1.trans b.1,?_⟩
  intro m
  obtain ⟨one,keep⟩:=a.2 m
  obtain ⟨two,tail⟩:=b.2 (p.image m)
  refine ⟨p.seq_runs q m one two,?_⟩
  rintro i (s|t)
  · exact (tail i (.inl (s.trans_le a.1))).trans (keep i (.inl s))
  · exact (tail i (.inr t)).trans (keep i (.inr (b.1.trans t)))

private theorem received_segment : segment (v.received base s safe) base (v.mixed base) := by
  have orig : segment (v.originalPhase base s safe) base (v.rawTablesEnd base) := by
    refine ⟨?_,fun m=>?_⟩
    · have start : base≤v.oldKeys base:=by dsimp [oldKeys,DescentResetStemKey.Columns.stop,DescentResetStemKey.Columns.start];omega
      rw [←v.tables_end base safe.sameLanes,(v.rawTables base).end_eq]
      exact start.trans (Nat.le_add_right ..)
    · have evidenceRun:=v.evidence_any s.evidence base m safe.before safe.sameLanes safe.evidenceFit
      exact ⟨evidenceRun.1,evidenceRun.2.1⟩
  have donor : segment (v.donorPhase base s safe) (v.rawTablesEnd base) (v.donorEnd base) := by
    obtain ⟨h,i,j⟩:=v.donor.ordered (v.donorStart base)
    refine ⟨(h.trans i).trans j,fun m=>?_⟩
    have k:=v.donor.any (v.donorStart base) s.donor safe.donor m
    exact ⟨k.1,k.2.2⟩
  have contact : segment (v.contactPhase base s safe) (v.donorEnd base) (v.peers base) := by
    obtain ⟨a,b,c,d,e⟩:=(C).ordered
    refine ⟨(((a.trans b).trans c).trans d).trans e,fun m=>?_⟩
    have c:=(C).any s.rotor s.boardReads (v.sensor base s) safe.contact m
    exact ⟨c.1,c.2.2⟩
  have triple : segment (v.triplePhase base s safe) (v.peers base) scalarBase := by
    obtain ⟨a,b,c,d⟩:=(p₀).ordered (v.peers base)
    refine ⟨((a.trans b).trans c).trans d,fun m=>?_⟩
    have c:=(p₀).any s.peers (v.peers base) m safe.peers
    exact ⟨c.1,c.2.1⟩
  have header : segment (v.scalarPhase base s w) scalarBase (v.parentStart base) := by
    refine ⟨Nat.le_add_right ..,fun m=>?_⟩
    have c:=DescentResetTrunkCompactScalar.any v.newHosts scalarBase s.count s.inverse s.rawHeader m safe.count
      safe.inverse safe.scalar safe.parent
    exact ⟨c.1,c.2.1⟩
  have stems : segment (v.parentStemPhase base s safe) (v.parentStart base) (v.mixed base) := by
    have e:=DescentResetParentAperture.extent (v.parentStart base) (p₀).hosts v.newHosts
    have le:v.parentStart base≤v.parentEnd base:=by change _≤DescentResetParentAperture.endAddress _ _ _;rw [e];omega
    have hi:v.parentEnd base≤v.projected base:=by unfold projected;rw [DescentResetStemProject.extent];omega
    have end_:v.projected base≤v.mixed base:=by unfold mixed;rw [DescentResetStemPackedIssue.Mixed.affine];omega
    refine ⟨(le.trans hi).trans end_,fun m=>?_⟩
    have c:=v.stem_any s.stems base safe.stems m
    exact ⟨c.1,c.2.1⟩
  exact adjacent (adjacent (adjacent (adjacent (adjacent orig donor) contact) triple) header) stems

include safe in
theorem received_start : base≤v.mixed base:=(received_segment v base s safe).1

theorem received_any (m : Memory w) :
    let p:=v.received base s safe
    p.Runs m ∧ ∀i,i<base ∨ v.mixed base≤ i → p.image m i=m i := by
  intro p
  exact (received_segment v base s safe).2 m

end
end Hierarchy.DescentDatedAddressBook.CandidateFront

end OAI
