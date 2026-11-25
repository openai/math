import OAI.Hierarchy.DescentDatePopulation
import OAI.Hierarchy.DescentOrdinaryDatedEntry

namespace OAI
/-! # The host and group axes of the actual registered ordinary sections -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentCompiler.TerminalScale DescentPacking.PackedMatch.Local.Stage
open DescentDatedAddressBook ProtocolRAM
noncomputable section
set_option quotPrecheck false

namespace OrdinaryBooks
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) (op : RotorSpec)

theorem atDate_axes (gain k age p tail drift degree payload seats : ℕ) (prior : DatePorts) :
    let b:=atDate G S op gain k age p tail drift degree payload seats prior
    b.bornBook.hosts=hostRows (S.hostSize age) ∧ b.bornBook.groups=S.groupCount age ∧
    b.vector.hosts=hostRows (S.hostSize age) ∧ b.vector.groups=S.groupCount (age+1) ∧
    b.resolver.hosts=b.vector.hosts*b.vector.lows ∧ b.resolver.groups=b.vector.groups ∧
    b.metadata.chart.hosts=b.resolver.hosts ∧ b.metadata.chart.groups=b.resolver.groups :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end OrdinaryBooks

namespace PhysicalOrdinary
variable {F P : Type} [Field F]

/-- The old input, compact successor and uncompressed successor each have a different host axis. -/
structure SectionPopulation (Y : PhysicalOrdinary F P) (A : ArgumentEntry Y) (S : AtomSchedule) (i : ℕ) : Prop where
  donor : Y.material.oldHosts=hostRows (S.hostSize i) ∧ Y.material.oldGroups=S.groupCount i
  material : Y.material.hosts=NativePitch.incomingHosts S (i+1) ∧ Y.material.groups=S.groupCount (i+1)
  signed : Y.signed.priorHosts=Y.material.oldHosts ∧ Y.signed.hosts=Y.material.hosts ∧ Y.signed.groups=Y.material.groups
  clip : A.clip.venue.hosts=Y.material.oldHosts ∧ A.clip.venue.groups=Y.material.oldGroups
  born : Y.bornBook.hosts=Y.material.oldHosts ∧ Y.bornBook.groups=Y.material.oldGroups
  vector : Y.vector.hosts=Y.material.oldHosts ∧ Y.vector.groups=Y.material.groups
  resolver : Y.resolver.hosts=Y.vector.hosts*Y.vector.lows ∧ Y.resolver.groups=Y.vector.groups
  metadata : Y.metadata.chart.hosts=Y.resolver.hosts ∧ Y.metadata.chart.groups=Y.resolver.groups
  venue : Y.venue.hosts=Y.material.hosts ∧ Y.venue.groups=Y.material.groups
  compact : Y.resolver.hosts≤Y.material.hosts
  group_partition : S.groupCount (i+1)*S.radix=S.groupCount i
  old_hosts : Y.material.oldHosts≤2*S.hostSize i
  new_hosts : Y.material.hosts≤2*(S.hostSize i*(2^S.hostGain*S.radix))

/-- When a physical group digit becomes a host digit, its radix cancels in the row population. -/
theorem SectionPopulation.rectangles {Y : PhysicalOrdinary F P} {A : ArgumentEntry Y} {S : AtomSchedule}
    {i : ℕ} (r : SectionPopulation Y A S i) :
    Y.material.oldHosts*Y.material.oldGroups ≤ 2*(S.hostSize i*S.groupCount i) ∧
    Y.material.hosts*Y.material.groups ≤ (2*2^S.hostGain)*(S.hostSize i*S.groupCount i) ∧
    Y.resolver.hosts*Y.resolver.groups ≤ (2*2^S.hostGain)*(S.hostSize i*S.groupCount i) := by
  have newRect : Y.material.hosts*Y.material.groups ≤ (2*2^S.hostGain)*(S.hostSize i*S.groupCount i) := calc
    _ ≤ (2*(S.hostSize i*(2^S.hostGain*S.radix)))*S.groupCount (i+1) :=
      Nat.mul_le_mul r.new_hosts r.material.2.le
    _ = (2*2^S.hostGain)*(S.hostSize i*(S.groupCount (i+1)*S.radix)) := by ring
    _ = _ := by rw [r.group_partition]
  refine ⟨?_,newRect,(Nat.mul_le_mul r.compact (r.resolver.2.trans r.vector.2).le).trans newRect⟩
  exact (Nat.mul_le_mul r.old_hosts r.donor.2.le).trans_eq (Nat.mul_assoc ..)
end PhysicalOrdinary

namespace DatePorts
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule}
    {d k i z D z' D' wire hist : ℕ} {q ε u : ℝ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {prevWorld : Reached W G q ε S k i z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
    {choice : (T.result he).Choice} {n : Normalize ((T.result he).state choice)}
    {next : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (prior : DatePorts) (ticket : OrdinaryLink prevWorld he T choice n next)
    (op : RotorSpec) (gain tail p f drift degree payload seats hostLanes : ℕ) (old : Bank)
    (ordinary : ℕ→Dated.Ordinary) (floor : ℕ)
local notation "book" => OrdinaryBooks.atDate G S op gain k i p tail drift degree payload seats prior
local notation "v" => (book).onTicket ticket gain tail p f payload seats hostLanes old ordinary
local notation "Y" => (v).registeredFrom prior floor
local notation "A" => (v).registeredEntry prior floor

theorem registered_section_population {t J reset M : ℕ} (scheduled : S=stageNumbers G t J f gain reset M tail)
    (live : 0<S.hostSize i) (radix : S.radix=2^k) : PhysicalOrdinary.SectionPopulation (Y) (A) S i := by
  have active:=ticket.hubRows.choose
  have rounds : 0<t:=by
    obtain ⟨j,jt,_⟩:=ticket.degreeSlot
    rw [scheduled] at jt
    exact (Nat.zero_le _).trans_lt jt
  let date:=DonorDate.atDate G S gain k i p
  have slot : 4*DescentOrdinaryVenueReturn.shapeSlots date.degree ≤ 2^S.hostGain := by
    change 4*DescentOrdinaryVenueReturn.shapeSlots (OrdinaryLink.publicDegree S.rounds G.b _)≤2^S.hostGain
    rw [scheduled]
    exact public_slot_room rounds reset G.b _
  have smaller:=OrdinaryBooks.compact_host_room S live active radix slot
  have cut := Fintype.card_congr (S.groupDigits (show i<S.length by omega) radix)
  have partition : S.groupCount (i+1)*S.radix=S.groupCount i := by
    simpa only [Fintype.card_prod,Fintype.card_fin,radix] using cut.symm
  have hop : S.hostSize (i+1)=S.hostSize i*(2^S.hostGain*S.radix) := by
    unfold AtomSchedule.hostSize
    rw [pow_succ]
    ring
  have lively : 0<S.hostSize (i+1) := by rw [hop,radix];positivity
  have high := (NativePitch.hosts_bounds S (i+1) active).2.trans (hostRows_double lively)
  rw [hop] at high
  exact ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩,⟨rfl,rfl,rfl⟩,⟨rfl,rfl⟩,⟨rfl,rfl⟩,⟨rfl,rfl⟩,
    ⟨rfl,rfl⟩,⟨rfl,rfl⟩,⟨rfl,rfl⟩,smaller,partition,hostRows_double live,high⟩

end DatePorts
end
end Hierarchy.DescentSixParty.Chronology

end OAI
