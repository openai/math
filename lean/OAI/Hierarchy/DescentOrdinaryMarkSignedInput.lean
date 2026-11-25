import OAI.Hierarchy.DescentOrdinaryMarkAfterHosts
import OAI.Hierarchy.DescentDatedSignedInput

namespace OAI
/-! The actual mark term of each public signed-program socket reads the preceding physical mark image. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentOrdinaryMarkProject DescentPacking.PackedMatch.Local
open DescentSIMDLookup DescentPackedColony DescentSharedCableNames DescentHaloWalkRAM
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) (input : Stage.Dated.Operands)
  (count parts adj : Bank) {w : ℕ}
local notation "ss" => v.signed
local notation "ms" => v.markShape
local notation "base₀" => v.donorEnd floor
local notation "start" => v.materialStart floor
local notation "end₀" => v.materialEnd floor
local notation "H" => v.area.H
local notation "G" => (ss).groups
local notation "M" => (ss).lanes
local notation "D" => (ss).degree
local notation "rank₀" => PriorHeader.reverseRank H G M D (base₀)
local notation "head₀" => PriorHeader.phase H G M D (base₀) adj w
local notation "oldPorts" => (⟨count,input.roster,input.hubs⟩:DescentOrdinaryVenueReturn.Sources)
local notation "hosts" => DescentOrdinaryVenueReturn.phase (oldPorts) (end₀) v.k H v.area.D v.venue.hosts v.venue.degree w
local notation "pre" => (v.beforeSignedMaterial floor parts adj w).seq (hosts)
local notation "readMark" => v.mark floor input w
local notation "slab" => (ms).markStart (v.peerTail floor)

def markBits (c : v.SignedChart) (fit : Fintype.card v.prior.V≤H)
    (groups : G*(ss).blocks=v.schedule.groupCount v.age) (R : Fin H→Fin D→Option (Fin H))
    (x : Fin (ss).blocks) (j : Fin ((ss).reach*(ss).residentSlots)) :=
  DescentOrdinaryMarkProject.bits («H»:=(ss).hosts) (Gather.select (Gather.reaching R)) (v.markVenuePanel fit groups)
    v.markBorn v.materialPitch x (Fin.cast (congrArg (fun n=>(ss).reach*n) c.markSlots) j)

/-- The dated operand on the real trace reads the old group selected by the schedule
and the original signed source port at the predecessor rack. -/
theorem markBits_at_age (c : v.SignedChart) (fit : Fintype.card v.prior.V≤H)
    (groups : G*(ss).blocks=v.schedule.groupCount v.age) (R : Fin H→Fin D→Option (Fin H))
    (atAge : v.age<v.schedule.length) (radix : v.schedule.radix=2^v.k)
    (newGroups : G=v.schedule.groupCount (v.age+1)) (newBlocks : (ss).blocks=2^v.k)
    (x : Fin (ss).blocks) (j : Fin ((ss).reach*(ss).residentSlots)) :
    let lane:=fun t:Fin (G*(ss).blocks)=>(v.schedule.groupDigits atAge radix).symm
      (finProdFinEquiv.symm (Fin.cast (congrArg₂ (·*·) newGroups newBlocks) t))
    v.markBits c fit groups R x j=DescentOrdinaryMarkProject.bits («H»:=(ss).hosts) (Gather.select (Gather.reaching R))
      (DescentOrdinarySignedMeta.donorPanel v.world v.gadget v.prior.placement
        (v.prior.order.trans Fin.valEmbedding) v.schedule v.prior.valid
        (DescentStageEdgeReceipt.groupRank ((Function.Embedding.refl _).trans Fin.valEmbedding)
          (v.prior.vertex.trans Fin.valEmbedding)) (v.markHost fit) lane)
      v.markBorn v.materialPitch x (Fin.cast (congrArg (fun n=>(ss).reach*n) c.markSlots) j) :=by
  dsimp only
  unfold markBits
  rw [v.markVenuePanel_eq fit groups]
  have same (t : Fin (G*(ss).blocks)) :
      (v.schedule.groupDigits atAge radix).symm (finProdFinEquiv.symm
        (Fin.cast (congrArg₂ (·*·) newGroups newBlocks) t))=Fin.cast groups t :=by
    have shape : v.schedule.groupCount (v.age+1)*2^v.k=v.schedule.groupCount v.age :=by
      rw [←newGroups,←newBlocks]
      exact groups
    exact (mark_group_digit atAge radix shape _).trans (Fin.ext rfl)
  simp only [same]
  rfl

private theorem bits_ports {d e a b c f oldH newH o cableDegree cap : ℕ}
    (sd : d=e) (sg : a=b) (sx : c=f)
    (R : Fin oldH→Fin e→Option (Fin oldH))
    (P : Fin o→Fin oldH→Fin (b*f)→Option (Stage.Live cableDegree cap)) (fresh : Fin o→Bool)
    (pitch : ℕ) (x : Fin c) (j : Fin (breadth d*o)) (h : Fin newH) (g : Fin a) :
    DescentOrdinaryMarkProject.bits
      (Gather.select (Gather.reaching (fun h t=>R h (Fin.cast sd t))))
      (fun n v t=>P n v (Fin.cast (congrArg₂ (·*·) sg sx) t)) fresh pitch x j h g =
    DescentOrdinaryMarkProject.bits (Gather.select (Gather.reaching R)) P fresh pitch (Fin.cast sx x)
      (Fin.cast (congrArg (fun t=>breadth t*o) sd) j) h (Fin.cast sg g) :=by
  subst e;subst b;subst f;rfl

/-- Evaluate the signed socket directly on the original old rotor. The socket's
path, donor slot, block and group retain their numeric ordinals across the public chart. -/
theorem markBits_original (c : v.SignedChart) (fit : Fintype.card v.prior.V≤H)
    (groups : G*(ss).blocks=v.schedule.groupCount v.age)
    (R : Fin H→Fin v.prior.placement.degree→Option (Fin H))
    (atAge : v.age<v.schedule.length) (radix : v.schedule.radix=2^v.k)
    (newGroups : G=v.schedule.groupCount (v.age+1))
    (x : Fin (ss).blocks) (j : Fin ((ss).reach*(ss).residentSlots))
    (h : Fin (ss).hosts) (g : Fin G) :
    let lane:=fun t:Fin (v.schedule.groupCount (v.age+1)*2^v.k)=>
      (v.schedule.groupDigits atAge radix).symm (finProdFinEquiv.symm t)
    v.markBits c fit groups (fun h t=>R h (Fin.cast c.degree t)) x j h g=
    DescentOrdinaryMarkProject.bits (Gather.select (Gather.reaching R))
      (DescentOrdinarySignedMeta.donorPanel v.world v.gadget v.prior.placement
        (v.prior.order.trans Fin.valEmbedding) v.schedule v.prior.valid
        (DescentStageEdgeReceipt.groupRank Fin.valEmbedding (v.prior.vertex.trans Fin.valEmbedding))
        (v.markHost fit) lane) v.markBorn v.materialPitch (Fin.cast c.blocks x)
        (Fin.cast (congrArg₂ (·*·) (congrArg breadth c.degree) c.markSlots) j) h (Fin.cast newGroups g) :=by
  dsimp only
  rw [v.markBits_at_age c fit groups _ atAge radix newGroups c.blocks]
  let panel:=DescentOrdinarySignedMeta.donorPanel v.world v.gadget v.prior.placement
    (v.prior.order.trans Fin.valEmbedding) v.schedule v.prior.valid
    (DescentStageEdgeReceipt.groupRank Fin.valEmbedding (v.prior.vertex.trans Fin.valEmbedding))
    (v.markHost fit) (fun t : Fin (v.schedule.groupCount (v.age+1)*2^v.k)=>
      (v.schedule.groupDigits atAge radix).symm (finProdFinEquiv.symm t))
  exact bits_ports c.degree newGroups c.blocks R panel v.markBorn v.materialPitch x
    (Fin.cast (congrArg (fun n=>(ss).reach*n) c.markSlots) j) h g

theorem signed_mark_after_hosts (c : v.SignedChart) (fit : Fintype.card v.prior.V≤H)
    (groups : G*(ss).blocks=v.schedule.groupCount v.age)
    (m : Memory w) (oldPos : 0<(ms).oldLanes) (lanes : 0<M) (blocks : 0<(ss).blocks)
    (before : PriorHeader.Room adj H G M D (base₀) w) (mat : v.MaterialRoom (start) parts (rank₀) w)
    (venueRoom : DescentOrdinaryVenueReturn.Room (oldPorts) (end₀) H v.area.D v.venue.hosts v.venue.degree w)
    (space : v.markEnd floor<2^w)
    (matcher : v.area.Space input w floor)
    (precision sourceFloor : ℕ) (sourceAdj : Fin H→Fin v.degree→Option (Fin H))
    (source : stageVenue v.prior fit input (ms).oldLanes precision sourceFloor sourceAdj m)
    (R : Fin H→Fin D→Option (Fin H)) (neighbors : ∀u j,m (adj.base+u.val*D+j.val)=(number (R u j):Word w)) :
    ∀x j,
      let a:=(v.signedInput floor c).mark (x,j)
      a.Fits w (v.markEnd floor) ∧ DescentPackedZip.Source a (v.markBits c fit groups R x j)
        M (((pre).seq (readMark)).image m) :=by
  intro x j
  exact v.mark_after_hosts floor input count parts adj fit groups m oldPos lanes blocks before mat venueRoom
    space matcher precision sourceFloor sourceAdj source R neighbors x
    (Fin.cast (congrArg (fun n=>(ss).reach*n) c.markSlots) j)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
