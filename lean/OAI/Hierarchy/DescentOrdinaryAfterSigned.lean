import OAI.Hierarchy.DescentOrdinaryDateArguments
import OAI.Hierarchy.DescentOrdinaryVenueClipRun
import OAI.Hierarchy.DescentOrdinaryBirthChip
import OAI.Hierarchy.DescentOrdinaryRoleHostPad
import OAI.Hierarchy.DescentOrdinaryRoleControlPrice

namespace OAI
/-! # Compilation of the original ordinary receiving phase after the signed panel -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentDatedPriorOperand DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open DescentOrdinaryVenueIngress ProtocolRAM DescentOrdinaryReferenceInputs DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P)

/-- The fields are numerical operands of the date program. The earlier tape
directory supplies the predecessor's seven-word and primitive-label banks. -/
structure ArgumentEntry (v : PhysicalOrdinary F P) where
  clip : Clip
  venue : Inputs
  previous : DescentDatedPriorOperand.Layout
  previousBase : ℕ
  rolePitch : ℕ
  roleBits : ℕ
  role : Fin previous.blocks→Bank

namespace ArgumentEntry
variable (A : ArgumentEntry v)

def priorStart (floor : ℕ) :=A.clip.fullEnd (v.signedEnd floor)
def roleStart (floor : ℕ) :=DescentOrdinaryPriorPad.roof A.previous A.clip.venue.hosts A.clip.working (A.priorStart v floor)
def roleLayout : DescentOrdinaryRoleHostPad.Layout :=
  ⟨A.previous.blocks,A.previous.hosts,A.clip.venue.hosts,A.clip.venue.groups,A.rolePitch,A.clip.working,
   A.roleBits*v.reference.oldNodes⟩
def roleValues {a : ℕ} (roles : Fin A.previous.blocks→Fin A.previous.hosts→Fin A.clip.venue.groups→Cell a) :=
  fun x=>DescentOrdinaryHostPad.extend A.clip.venue.hosts (roles x)

def chipStart (floor : ℕ) := (A.roleLayout v).roof (A.roleStart v floor)
def chip : DescentOrdinaryBirthChip.Layout :=
  ⟨A.clip.venue.socket,A.clip.venue.hosts,A.clip.venue.groups,A.clip.working,
   A.clip.venue.profile,v.gadget.b,A.clip.venue.slots⟩
def chipSource (floor : ℕ) := (A.clip.clipped (v.signedEnd floor) A.venue).panel
def populationBase (floor : ℕ) := (A.chip v).finish (A.chipStart v floor)
def population (floor : ℕ) : RoleControl.Layout :=
  ⟨A.populationBase v floor,A.clip.venue.hosts,A.clip.venue.groups,A.clip.working,A.clip.venue.paths,
    A.previous.blocks,v.reference.oldNodes,A.roleBits,v.reference.countBits,v.vector.lows⟩
def ports (floor : ℕ) :=A.clip.ports (v.signedEnd floor)
def labels (floor : ℕ) (x : Fin A.previous.blocks) :=(A.roleLayout v).bank (A.roleStart v floor) x
def chipBank (floor : ℕ) :=(A.chip v).bank (A.chipStart v floor)
def finish (floor : ℕ) :=(A.population v floor).endAddress

/-- Literal storage before this date's fixed reference table. All five terms
are the corresponding emitted programs' translation-invariant extents. -/
def words :=
  let populations := {A.population v 0 with base:=0}
  (((A.clip.fullEnd 0 + DescentOrdinaryPriorPad.roof A.previous A.clip.venue.hosts A.clip.working 0) +
    (A.roleLayout v).roof 0) + (A.chip v).finish 0) + populations.endAddress

theorem paid_extent (floor : ℕ) : A.finish v floor=v.signedEnd floor+A.words v:=by
  have inlet:=A.clip.translated (v.signedEnd floor)
  have previous:=DescentOrdinaryPriorPad.translated A.previous A.clip.venue.hosts A.clip.working (A.priorStart v floor)
  have roles:=(A.roleLayout v).translated (A.roleStart v floor)
  have chipShift : A.populationBase v floor=A.chipStart v floor+(A.chip v).finish 0:=by
    simp only [populationBase, DescentOrdinaryBirthChip.Layout.finish, DescentMaskedColumn.Layout.finish,
      DescentMaskedColumn.Layout.result, DescentMaskedColumn.Layout.bank, Bank.size, Nat.zero_add, Nat.add_assoc]
  have populationShift : A.finish v floor=A.populationBase v floor+({A.population v 0 with base:=0}:RoleControl.Layout).endAddress:=by
    simp only [finish, RoleControl.Layout.endAddress, RoleControl.Layout.outBase, population, Nat.zero_add, Nat.add_assoc]
    rfl
  rw [populationShift,chipShift]
  unfold chipStart
  rw [roles]
  unfold roleStart
  rw [previous]
  unfold priorStart
  rw [inlet]
  simp only [words,Nat.add_assoc]

theorem ends_at_refs (floor : ℕ) (charged : v.ingressWords=A.words v) : A.finish v floor=v.refsStart floor:=by
  rw [A.paid_extent v floor,refsStart,charged]

structure Match (floor : ℕ) : Prop where
  post : v.vector.lanes=A.clip.postPitch
  radix : v.vector.radix=A.clip.radix
  refPitch : v.reference.lanes=A.clip.working
  bornPitch : v.bornBook.lanes=A.clip.working
  paths : A.clip.venue.paths=breadth v.reference.degree
  oldBlocks : A.previous.blocks=2^v.reference.k
  oldArgs : A.previous.operands≤v.vector.operands
  newBlocks : v.bornBook.blocks=2^v.reference.k
  newCap : v.bornBook.cap=v.reference.capacity
  newArgs : v.bornBook.args=v.vector.operands
  atRefs : A.finish v floor=v.refsStart floor

def directory (floor : ℕ) (match_ : A.Match v floor) : Directory (v.refChart floor) v.vector :=
  v.dateDirectory floor A.previous (A.priorStart v floor) (A.population v floor) A.clip.core (A.clip.setupStart (v.signedEnd floor))
    match_.paths match_.paths rfl match_.oldBlocks match_.oldArgs match_.newBlocks match_.newCap match_.newArgs

def inlet (floor w : ℕ) : NativePhase w :=
  ((((A.clip.phase A.venue (v.signedEnd floor) w).seq
    (DescentOrdinaryPriorPad.phase A.previous A.clip.venue.hosts A.clip.working (A.priorStart v floor) A.previousBase w)).seq
    ((A.roleLayout v).phase (A.roleStart v floor) A.role w)).seq
    ((A.chip v).phase (A.chipStart v floor) (A.chipSource v floor) w)).seq
    ((A.population v floor).phase (A.ports v floor) (A.labels v floor) w)

theorem inlet_order (floor : ℕ) :
    v.signedEnd floor≤A.priorStart v floor ∧ A.priorStart v floor≤A.roleStart v floor ∧
    A.roleStart v floor≤A.chipStart v floor ∧ A.chipStart v floor≤A.populationBase v floor ∧
    A.populationBase v floor≤A.finish v floor:=by
  have tile:=DescentOrdinaryPriorPad.base_le A.previous A.clip.venue.hosts A.clip.working (A.priorStart v floor)
  have labels:=(A.roleLayout v).base_le (A.roleStart v floor)
  refine ⟨?_,tile,labels,?_,?_⟩
  · rw [priorStart,A.clip.translated]
    exact Nat.le_add_right ..
  · change _ ≤ A.chipStart v floor + _ + _ + _
    exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  · change _ ≤ A.populationBase v floor + _ + _
    exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)

structure Room (floor w : ℕ) : Prop where
  venue : A.clip.Room A.venue (v.signedEnd floor) w
  prior : ∀x p,(previousBank A.previous A.previousBase x p).Fits w (A.priorStart v floor)
  roles : ∀x,(A.role x).Fits w (A.roleStart v floor)
  chipLow : (A.chipSource v floor).base+(A.chipSource v floor).size≤A.chipStart v floor
  chipRows : (A.chip v).rows≤(A.chipSource v floor).size
  chipBits : A.clip.working*max (DescentRawCablePanel.DepotRAM.totalBits A.clip.venue.socket)
      (DescentRawCablePanel.DepotRAM.outputBits A.clip.venue.socket)≤w/2
  walk : ∀x,Accessible (A.ports v floor) (A.labels v floor x)
      A.clip.venue.hosts A.clip.venue.groups A.clip.working w (A.population v floor).outBase
  ceiling : A.finish v floor<2^w

theorem inlet_any {w} (floor : ℕ) (safe : A.Room v floor w) (m : Memory w) :
    (A.inlet v floor w).Runs m ∧
    ∀i,i<v.signedEnd floor ∨ A.finish v floor≤ i→(A.inlet v floor w).image m i=m i:=by
  obtain ⟨u₀,u₁,u₂,u₃,u₄⟩:=A.inlet_order v floor
  have hi:=safe.ceiling
  have h₄:=u₄.trans_lt hi
  have h₃:=u₃.trans_lt h₄
  have h₂:=u₂.trans_lt h₃
  let p:=A.clip.phase A.venue (v.signedEnd floor) w
  let q:=DescentOrdinaryPriorPad.phase A.previous A.clip.venue.hosts A.clip.working (A.priorStart v floor) A.previousBase w
  let r:=(A.roleLayout v).phase (A.roleStart v floor) A.role w
  let c:=(A.chip v).phase (A.chipStart v floor) (A.chipSource v floor) w
  have a:=A.clip.any A.venue (v.signedEnd floor) m safe.venue
  have b:=DescentOrdinaryPriorPad.any A.previous A.clip.venue.hosts A.clip.working (A.priorStart v floor) A.previousBase
    (p.image m) safe.prior h₂
  have d:=(A.roleLayout v).any (A.roleStart v floor) A.role (q.image (p.image m)) safe.roles h₃
  have e:=(A.chip v).framed (A.chipStart v floor) (A.chipSource v floor)
    (r.image (q.image (p.image m))) safe.chipLow safe.chipRows safe.chipBits h₄
  have f:=(A.population v floor).any (A.ports v floor) (A.labels v floor)
    (c.image (r.image (q.image (p.image m)))) safe.walk hi
  constructor
  · exact NativePhase.seq_runs _ _ _ (NativePhase.seq_runs _ _ _ (NativePhase.seq_runs _ _ _
      (NativePhase.seq_runs _ _ _ a.1 b.1) d.1) e.1) f.1
  · intro i apart
    have hh₀:=u₀.trans u₁
    have hh₁:=hh₀.trans u₂
    have hh₂:=hh₁.trans u₃
    have high₀:=u₃.trans u₄
    have high₁:=u₂.trans high₀
    have high₂:=u₁.trans high₁
    exact (f.2.2.2 i (apart.imp_left (·.trans_le hh₂))).trans <|
      (e.2 i (apart.imp (·.trans_le hh₁) (u₄.trans ·))).trans <|
      (d.2 i (apart.imp (·.trans_le hh₀) (high₀.trans ·))).trans <|
      (b.2 i (apart.imp (·.trans_le u₀) (high₁.trans ·))).trans (a.2 i (apart.imp_right (high₂.trans ·)))


end ArgumentEntry

/-- The signed output is already in memory. All subsequent date-specific
lookups and scans are fixed by the preceding tape directory and the public
geometry. The owner's eight expressions have a single preparation program. -/
def argumentPhaseAfterSigned {w} (floor : ℕ) (A : ArgumentEntry v)
    (match_ : A.Match v floor) (src : OriginSources v) (prepare : NativePhase w)
    (donorFit : (A.chipBank v floor).Fits w (v.refsStart floor))
    (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2) : NativePhase w :=
  (A.inlet v floor w).seq (v.resolvedPhase floor (A.directory v floor match_) src prepare
    (A.chipBank v floor) donorFit shape fit wide)

theorem argumentAfterSigned_any {w} (floor : ℕ) (A : ArgumentEntry v)
    (match_ : A.Match v floor) (src : OriginSources v) (prepare : NativePhase w)
    (donorFit : (A.chipBank v floor).Fits w (v.refsStart floor))
    (shape : v.VectorShape) (fit : v.endAddress floor<2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (inlet : A.Room v floor w) (gather : (A.directory v floor match_).refs.Room w (v.vectorStart floor))
    (bounds : ∀j f,(src j f).Fits w (v.origin.outputBase (v.routedStart floor)))
    (cpu : ∀m,prepare.Runs m ∧ ∀i,i<v.routedStart floor ∨ v.origin.grainBase (v.routedStart floor)≤ i → prepare.image m i=m i)
    (m : Memory w) :
    (v.argumentPhaseAfterSigned floor A match_ src prepare donorFit shape fit wide).Runs m ∧
    ∀i,i<v.signedEnd floor ∨ v.endAddress floor≤ i →
      (v.argumentPhaseAfterSigned floor A match_ src prepare donorFit shape fit wide).image m i=m i:=by
  have left:=A.inlet_any v floor inlet m
  have right:=v.resolved_any floor (A.directory v floor match_) src prepare (A.chipBank v floor)
    donorFit gather shape fit wide bounds cpu ((A.inlet v floor w).image m)
  have low : v.signedEnd floor≤v.refsStart floor:=Nat.le_add_right ..
  obtain ⟨x,y⟩:=v.mount_order floor
  have high:=(x.trans y).trans ((v.vector_before floor).trans ((v.routed_le floor).trans (v.resolver.floor_le _)))
  refine ⟨NativePhase.seq_runs _ _ _ left.1 right.1,?_⟩
  intro i apart
  exact (right.2.1 i (apart.imp_left (·.trans_le low))).trans <|
    left.2 i (apart.imp_right (fun k=>match_.atRefs.le.trans (high.trans k)))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
