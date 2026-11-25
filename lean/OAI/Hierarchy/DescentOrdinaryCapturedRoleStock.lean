import OAI.Hierarchy.DescentOrdinaryPrimitiveOrigin
import OAI.Hierarchy.DescentRegisteredRoleStock
import OAI.Hierarchy.DescentOrdinaryMountedBirth

namespace OAI
/-! The complete outgoing primitive register from the received ordinary inlet and W operands. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentOrdinaryAtomFieldRAM.ScalarOperand DescentPackedColony DescentOrdinaryOriginMask
open DescentOrdinaryPrimitiveCheckpoint DescentRawCablePanel DescentDatedAddressBook ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
set_option quotPrecheck false
noncomputable section
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I)
variable (floor w : ℕ) (c : v.SignedChart) (A : v.ArgumentEntry) (mat : A.Match v floor)
    (shape : v.VectorShape) (blocks : v.resolver.blocks=v.material.blocks) (pg : Fin (7*v.vector.operands))
    (admission : v.TicketAdmission floor w c A mat pg)
    (total : v.origin.preparationWords=v.originControlWords+v.originMouthWords+v.rootSourceSize)
    (donor : (A.chipBank v floor).Fits w (v.refsStart floor)) (fit : v.endAddress floor<2^w)
    (wide : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤w/2)
    (paid : NativePhase w) (charge : Span paid (v.endAddress floor) (v.rasterEnd floor))
    (columns : StageVenueTail.Sources) (survivors : v.ResultRoom floor columns w) (m : Memory w)
local notation "L" => v.paletteShape
local notation "C" => (A.directory v floor mat).refs
local notation "prep" => v.nativeTicketPreparation floor w c A mat shape blocks pg
local notation "src" => v.nativeTicketExpr floor c A mat shape blocks
local notation "installed" => v.mountImage floor (A.chipBank v floor) ((A.inlet v floor w).image m)
local notation "args_" => (v.argumentPhaseAfterSigned floor A mat src prep donor shape fit wide).image m
local notation "atPrimitive" => (v.returnPhase floor columns w survivors).image (paid.image args_)

def primitiveRoster {H J D E} (hs : H=J) (ds : D=E) (roster : Fin J→Fin E→Option (Fin J)) (h : Fin H) (i : Fin D) :=
  (roster (h.cast hs) (i.cast ds)).map (Fin.cast hs.symm)

private theorem retarget_read {H J D E w} (hs : H=J) (ds : D=E) (roster : Fin J→Fin E→Option (Fin J))
    (b : Bank) (m : Memory w) (found : ∀h i,m (b.base+(h.val*E+i.val))=(DescentPackedColony.target (roster h i):Word w)) :
    ∀h i,m (b.base+(h.val*D+i.val))=(DescentPackedColony.target (primitiveRoster hs ds roster h i):Word w):=by
  subst J
  subst E
  simpa [primitiveRoster] using found

include admission total charge in
theorem captured_role_stock {a nb mb : ℕ} (radix : v.vector.radix=2^v.reference.k)
    (inlet : A.Room v floor w) (gather : (C).Room w (v.vectorStart floor))
    (primitive : v.PrimitiveRoom floor A w) (capacity : (L).Capacity (v.primitiveSources floor A mat radix))
    (birth : A.BirthShape v) (hosts : (L).hosts=v.bornBook.hosts) (groups : (L).oldGroups=v.bornBook.groups)
    (pitch : (L).priorLanes=A.clip.working) (cell : A.roleBits=(L).primitiveBits)
    (top : (v.area.matcher v.old floor).layout.topology.Fits w (v.primitiveEnd floor))
    (high : v.returnedEnd floor<2^w)
    (previous : Fin A.previous.blocks→Fin A.previous.hosts→Fin A.clip.venue.groups→Cell (A.roleLayout v).bits)
    (oldPitch : 0<A.rolePitch) (held : ∀x,(A.role x).base+(A.role x).size≤v.signedEnd floor ∧
      A.previous.hosts*chunks A.clip.venue.groups A.rolePitch≤(A.role x).size ∧ Reads (A.role x) (previous x) A.rolePitch m)
    (parts : Fin A.clip.venue.hosts→Fin A.clip.venue.groups→DepotRAM.Parts A.clip.venue.socket)
    (pos : 0<A.clip.panelPitch) (board : Reads A.venue.panel (fun h g=>DepotRAM.combine A.clip.venue.socket (parts h g))
        A.clip.panelPitch m)
    (real : Fin A.clip.venue.hosts→Fin A.clip.venue.paths→Option (Fin A.clip.venue.hosts))
    (roster : Mounted (A.ports v floor) real (A.clippedTape v floor m) A.clip.venue.groups A.clip.working)
    (portRoom : Accessible (A.ports v floor) (A.clip.fieldBank (v.signedEnd floor))
      A.clip.venue.hosts A.clip.venue.groups A.clip.working w (A.priorStart v floor))
    (V : Fin v.vector.lows→Values v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity
      v.vector.hosts (v.vector.groups*v.vector.radix) a nb mb)
    (measured : ∀i,Measured ((C) pg i) (V i) v.resolver.nodes (v.vector.lanes*v.vector.radix) (v.vectorStart floor) installed) :
    let old:=fun x : Fin (L).blocks=>ArgumentEntry.rowsAt (hosts.trans birth.hosts) (groups.trans birth.groups)
      (congrArg (·*v.reference.oldNodes) cell) (DescentOrdinaryHostPad.extend A.clip.venue.hosts (previous (x.cast mat.oldBlocks.symm)))
    let origin:=fun x : Fin (L).blocks=>DescentScalarBookReshape.book (fun l h g=>selection v.originCandidates
      v.resolver.nodes v.originBits (marked (V l) h g)) (x.cast radix.symm)
    let next:=primitiveRoster (hosts.trans birth.hosts) mat.paths.symm real
    let st:=v.paletteStock floor A mat old (A.nativeChips v birth parts) hosts groups origin next
    let post:=(v.primitiveUpdate floor A mat radix w).image atPrimitive
    (L).Published st (DatePorts.ordinary v floor).archive.roles.bank ((v.counter floor w).image post):=by
  intro old origin next st post
  obtain ⟨_,_,toOutput,toNormal,toEnd⟩:=v.routed_order floor
  have equal:=v.grain_after_sources floor total
  have ready : v.preparedUntil floor<2^w:=equal ▸ (toOutput.trans (toNormal.trans toEnd)).trans_lt fit
  have checked:=v.ticket_preparation_any floor w c A mat shape blocks pg admission ready
  have fits : ∀j f,(src j f).Fits w (v.origin.outputBase (v.routedStart floor)):=fun j f=>
    ProtocolRAMGeneratedWrite.fits_mono _ (equal ▸ toOutput) ((checked m).2 j f)
  have cpu (ram : Memory w) : (prep).Runs ram ∧ ∀j,j<v.routedStart floor ∨ v.origin.grainBase (v.routedStart floor)≤j →
      (prep).image ram j=ram j:=by
    have done:=(checked ram).1
    exact ⟨done.run,fun j away=>done.frame j (away.imp_right (fun h=>equal ▸ h))⟩
  have chip:=v.primitive_donor floor A mat src prep donor shape fit wide inlet gather fits cpu
    paid charge columns survivors m pos parts board
  have dir:=v.primitive_halo floor A mat src prep donor shape fit wide inlet gather fits cpu
    paid charge columns survivors m real roster portRoom
  have banks (x : Fin A.previous.blocks):=v.primitive_prior floor A mat src prep donor shape fit wide inlet gather fits cpu
    paid charge columns survivors m x (previous x) oldPitch (held x).1 (held x).2.1 (held x).2.2
  have cells : v.bornBook.rows≤(A.chipBank v floor).size:=by
    have sized : (A.chip v).rows≤(A.chipBank v floor).size:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
    change A.clip.venue.hosts * chunks A.clip.venue.groups A.clip.working ≤ _ at sized
    simpa only [DescentOrdinaryBorn.Chart.rows, birth.hosts, birth.groups, mat.bornPitch] using sized
  apply v.registered_role_stock floor A mat radix primitive capacity old (A.nativeChips v birth parts)
    hosts groups origin next atPrimitive
  · intro x
    exact ArgumentEntry.reads_at (hosts.trans birth.hosts) (groups.trans birth.groups)
      (congrArg (·*v.reference.oldNodes) cell) pitch (banks (x.cast mat.oldBlocks.symm))
  · exact cells
  · exact ArgumentEntry.reads_at birth.hosts birth.groups birth.width mat.bornPitch chip
  · intro x
    exact v.primitive_origin_from_W floor w c A mat shape blocks pg admission total donor fit wide paid charge columns
      survivors m gather V measured (x.cast radix.symm)
  · exact retarget_read (hosts.trans birth.hosts) mat.paths.symm real _ _ dir.roster
  · exact top
  · exact high

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
