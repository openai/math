import OAI.Hierarchy.DescentOrdinaryInletControls
import OAI.Hierarchy.DescentOrdinaryRoleControlFields

namespace OAI
/-! # The previous, newborn, and receiver controls on one mounted ordinary tape -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentPackedColony DescentPackedZip DescentOrdinaryAtomFieldRAM DescentSIMDLookup DescentSharedCableNames
open DescentDatedPriorOperand DescentOperandStateBanks DescentRawCablePanel DescentOrdinaryBorn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : ArgumentEntry v)
variable (floor : ℕ) {w : ℕ} (m : Memory w)
local notation "H₀" => A.clip.venue.hosts
local notation "G₀" => A.clip.venue.groups
local notation "M₀" => A.clip.working
local notation "L₀" => A.population v floor
local notation "P₀" => A.ports v floor
local notation "field₀" => A.clip.fieldBank (v.signedEnd floor)
local notation "pre₀" => (A.inlet v floor w).image m

def mountedTape:=v.mountImage floor (A.chipBank v floor) ((A.inlet v floor w).image m)

theorem chip_fits (safe : A.Room v floor w) («matching» : A.Match v floor) :
    (A.chipBank v floor).Fits w (v.refsStart floor) :=by
  obtain ⟨_,_,_,_,last⟩:=A.inlet_order v floor
  have ending : (A.chipBank v floor).base+(A.chipBank v floor).size=A.populationBase v floor:=rfl
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (ending.le.trans_lt (last.trans_lt safe.ceiling)),
    ending.le.trans (last.trans «matching».atRefs.le)⟩

theorem mounted_old (safe : A.Room v floor w) («matching» : A.Match v floor) (space : v.vectorStart floor<2^w)
    (x : Fin A.previous.blocks) (p : Pages A.previous.operands)
    (value : Fin A.previous.hosts →Fin A.previous.groups → Cell (DescentOrdinaryPriorRetile.digits A.previous))
    (positive : 0<A.previous.lanes) (early : (previousBank A.previous A.previousBase x p).Fits w (v.signedEnd floor))
    (held : Reads (previousBank A.previous A.previousBase x p) value A.previous.lanes m) :
    Reads (DescentOrdinaryPriorPad.bank A.previous A.clip.venue.hosts A.clip.working (A.priorStart v floor) x p)
      (DescentOrdinaryPriorPad.extend A.clip.venue.hosts value) A.clip.working (A.mountedTape v floor m) :=by
  obtain ⟨_,_,a,b,c⟩:=A.inlet_order v floor
  have low:=a.trans (b.trans c)
  have placed:=DescentOrdinaryPriorPad.placed A.previous A.clip.venue.hosts A.clip.working (A.priorStart v floor) (low.trans_lt safe.ceiling) x p
  have now:=v.mount_run floor (A.chipBank v floor) pre₀ (A.chip_fits v floor safe «matching») space
  exact reads_through (A.prior_final v floor m safe x p value positive early held)
    (placed.1.2.2.trans (low.trans «matching».atRefs.le)) placed.2 (fun i hi=>now.2.2.1 i (.inl hi))

/-- All unavailable predecessor operands use the same cleared page. -/
theorem mounted_zero (safe : A.Room v floor w) («matching» : A.Match v floor)
    (space : v.vectorStart floor<2^w) (bits : ℕ) :
    Reads (DescentOrdinaryPriorPad.zero A.previous H₀ M₀ (A.priorStart v floor))
      (fun (_ : Fin H₀) (_ : Fin A.previous.groups)=> (0 : Cell bits)) M₀ (A.mountedTape v floor m) :=by
  obtain ⟨_,_,roles,chips,count⟩:=A.inlet_order v floor
  have cut:=roles.trans (chips.trans count)
  have frame:=A.inlet_frames v floor m safe
  have zero:=DescentOrdinaryPriorPad.zero_reads A.previous H₀ M₀ (A.priorStart v floor)
    A.previousBase (A.clippedTape v floor m) (bits:=bits)
  have placed:=DescentOrdinaryPriorPad.zero_placed A.previous H₀ M₀ (A.priorStart v floor)
    (cut.trans_lt safe.ceiling)
  have mount:=v.mount_run floor (A.chipBank v floor) pre₀ (A.chip_fits v floor safe «matching») space
  apply reads_through zero placed.1.2.2 placed.2
  intro i low
  exact (mount.2.2.1 i (.inl (low.trans_le (cut.trans «matching».atRefs.le)))).trans
    ((frame.count i (low.trans_le (roles.trans chips))).trans
      ((frame.chip i (low.trans_le roles)).trans (frame.role i low)))

theorem mounted_controls {b : ℕ} (safe : A.Room v floor w) («matching» : A.Match v floor)
    (space : v.vectorStart floor<2^w) (order : Fin H₀→Fin (L₀).walks→Option (Fin H₀))
    («fields» : Fin H₀→Fin G₀→Cell b) (roles : Fin A.previous.blocks→Fin A.previous.hosts→Fin G₀→Cell ((L₀).roleBits*(L₀).nodes))
    (someBlock : Fin A.previous.blocks) (positive : 0<A.rolePitch)
    (early : ∀x,(A.role x).base+(A.role x).size≤v.signedEnd floor) (capacity : ∀x,A.previous.hosts*chunks G₀ A.rolePitch≤(A.role x).size)
    (before : ∀x,Reads (A.role x) (roles x) A.rolePitch m)
    (venue : Reads field₀ «fields» M₀ (A.clippedTape v floor m))
    (mounted : Mounted P₀ (DescentSortedRoster.indexed order) (A.clippedTape v floor m) G₀ M₀)
    (ports : ∀bank : Bank,bank.Fits w (A.priorStart v floor)→H₀*chunks G₀ M₀≤bank.size→
      Accessible P₀ bank H₀ G₀ M₀ w (A.priorStart v floor)) :
    let dst:=A.mountedTape v floor m
    Mounted P₀ (DescentSortedRoster.indexed order) dst G₀ M₀ ∧
      Source (.lookup field₀ .row) «fields» M₀ dst ∧ Source (L₀).counts ((L₀).dataCount order (A.roleValues v roles)) M₀ dst ∧
      (∀l,Source ((L₀).want P₀ l) (fun (_ : Fin H₀) (_ : Fin G₀)=>Packed.token (some l)) M₀ dst) ∧
      (∀b : Bank,b.Fits w (v.vectorStart floor)→H₀*chunks G₀ M₀≤b.size→Accessible P₀ b H₀ G₀ M₀ w (v.vectorStart floor)) ∧
      (∀l,((L₀).want P₀ l).Fits w (v.vectorStart floor) ∧ (L₀).counts.Fits w (v.vectorStart floor)) ∧
      (Expr.lookup field₀ .row).Fits w (v.vectorStart floor) ∧ (v.refChart floor).Issued dst :=by
  intro dst
  obtain ⟨_,old,role,chip,pop⟩:=A.inlet_order v floor
  have top:=old.trans (role.trans (chip.trans pop))
  have cut:=top.trans «matching».atRefs.le
  have all:=v.mount_run floor (A.chipBank v floor) pre₀ (A.chip_fits v floor safe «matching») space
  have frame (i : ℕ) (low : i<v.refsStart floor) : dst i=pre₀ i:=all.2.2.1 i (.inl low)
  obtain ⟨wired,counts,wanted,can⟩:=A.inlet_controls v floor m safe order roles someBlock positive early capacity before mounted ports
  have limit : (field₀).Fits w (A.priorStart v floor):=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt safe.venue.space,le_rfl⟩
  have accessible:=ports field₀ limit A.clip.core.rowRoom
  have end_:=limit.2.2.trans cut
  have reading:=reads_through (A.venue_final v floor m safe «fields» venue) end_ A.clip.core.rowRoom frame
  have label:=(A.roleLayout v).placed (A.roleStart v floor) (chip.trans_lt (pop.trans_lt safe.ceiling)) someBlock
  have addr:=can _ (old.trans (role.trans chip)) (A.labels v floor someBlock)
    ⟨label.1.1,label.1.2.1,label.1.2.2.trans chip⟩ label.2
  have fits:=(L₀).input_fits P₀ (A.labels v floor) someBlock addr «matching».atRefs.le («matching».atRefs ▸ safe.ceiling)
  have path:=(v.mount_order floor).1.trans (v.mount_order floor).2
  have geometries l := And.intro (ProtocolRAMGeneratedWrite.fits_mono _ path (fits l).1)
    (ProtocolRAMGeneratedWrite.fits_mono _ path (fits l).2)
  have vFit : (Expr.lookup field₀ .row).Fits w (v.vectorStart floor):=
    ⟨⟨limit.1,limit.2.1,end_.trans path⟩,trivial⟩
  constructor
  · exact RoleControl.Layout.previous_mounted accessible _ (fun i h=>frame i (h.trans_le cut)) wired
  refine ⟨source_column field₀ _ ⟨limit.1,limit.2.1,end_⟩ dst «fields» A.clip.core.rowRoom reading,?_,?_,can _ (cut.trans path),geometries,vFit,all.2.2.2⟩
  · intro row_
    have fitCounts : (L₀).counts.Fits w (v.refsStart floor) :=
      ⟨(L₀).result_fit («matching».atRefs ▸ safe.ceiling) «matching».atRefs.le,trivial⟩
    exact (eval_below _ _ _ _ fitCounts frame).trans (counts row_)
  · intro l row_
    exact (eval_below _ _ _ _ (fits l).1 frame).trans (wanted l row_)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
