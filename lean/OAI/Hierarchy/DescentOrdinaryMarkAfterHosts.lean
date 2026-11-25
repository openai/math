import OAI.Hierarchy.DescentOrdinaryMarkFromVenue
import OAI.Hierarchy.DescentDatedOrdinaryAny
import OAI.Hierarchy.DescentDatedBeforeSignedMaterial
import OAI.Hierarchy.DescentDatedPriorHeaderHeld
import OAI.Hierarchy.DescentOrdinaryVenueMachine

namespace OAI
/-! The selected prior mark after the actual material, host roster and mark programs. -/
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

/-- The earlier matcher already counted and bounded every signed input wire in its own lane format. -/
theorem mark_original_wires (groups : G*(ss).blocks=v.schedule.groupCount v.age)
    (matcher : v.area.Space input w floor) (o : Fin (ms).slots) :
    (v.markWire input o).Fits w (base₀) ∧ (ms).sourceRows≤(v.markWire input o).size :=by
  let col : Fin ((ms).priorBlocks*(ms).cap) × Fin 11:=finProdFinEquiv.symm o
  let pair : Fin (ms).priorBlocks × Fin (ms).cap:=finProdFinEquiv.symm col.1
  have original:=matcher.wires pair.1 (finProdFinEquiv ((0:Fin 2),pair.2))
  have old : floor≤(base₀):=by rw [v.donor_shift];exact Nat.le_add_right ..
  refine ⟨⟨original.1.1,original.1.2.1,original.1.2.2.trans old⟩,?_⟩
  change v.area.H*chunks (G*(ss).blocks) v.area.lanesAt≤_
  rw [groups];exact original.2

theorem mark_after_hosts (fit : Fintype.card v.prior.V≤H)
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
      let a:=DescentOrdinaryMarkProject.markExpr (slab) (ss).reach (ms).slots H (ss).hosts G (ss).blocks (ms).degree (ms).cap (ms).oldLanes M x j
      a.Fits w (v.markEnd floor) ∧ DescentPackedZip.Source a
        (DescentOrdinaryMarkProject.bits («H»:=(ms).hosts) (Gather.select (Gather.reaching R)) (v.markVenuePanel fit groups)
          v.markBorn v.materialPitch x j) M (((pre).seq (readMark)).image m) :=by
  have wire:=v.mark_original_wires floor input groups matcher
  let first:=(head₀).image m
  let second:=(v.beforeSignedMaterial floor parts adj w).image m
  let next:=(hosts).image second
  have matRun:=v.material_any mat first
  have venue:=DescentOrdinaryVenueReturn.any (oldPorts) (end₀) v.k H v.area.D v.venue.hosts v.venue.degree w second venueRoom
  have lower:(start)≤(end₀):=by rw [materialEnd,v.material.translated];exact Nat.le_add_right ..
  have keep (a : ℕ) (lt : a<(start)) :
      next a=PriorHeader.image H G M D (base₀) adj m a :=by
    exact (venue.2 _ (.inl (lt.trans_le lower))).trans ((matRun.2 a (.inl lt)).trans
      (congrFun (PriorHeader.phase_image H G M D (base₀) adj w m) a))
  have visited := (PriorHeader.held_ports (base₀) adj before m R neighbors next keep).2
  have prev:=(v.signed_stage_paid floor).1.trans (v.signed_stage_paid floor).2.1
  have room:=v.mark_room_at floor input lanes blocks space (fun o=>
    ⟨⟨(wire o).1.1,(wire o).1.2.1,(wire o).1.2.2.trans prev⟩,(wire o).2⟩)
  apply v.mark_issued floor input room oldPos (Gather.select (Gather.reaching R)) (v.markVenuePanel fit groups) next visited.roster
  intro o
  let col:Fin ((ms).priorBlocks*(ms).cap)×Fin 11 :=finProdFinEquiv.symm o
  let pair:Fin (ms).priorBlocks×Fin (ms).cap:=finProdFinEquiv.symm col.1
  let grain := finProdFinEquiv ((0:Fin 2),pair.2)
  let bank := input.wire pair.1.val grain.val
  let sheet (h : Fin H) (g : Fin (v.schedule.groupCount v.age)) :=
    DescentSignedCableCodec.encode (Stage.Prepare.signed v.prior.placement (v.prior.order.trans Fin.valEmbedding)
      v.schedule v.prior.valid (Function.Embedding.refl _) (v.prior.vertex.trans (Fin.castLEEmb fit)) pair.1 grain h g)
  have atSource : Reads bank sheet (ms).oldLanes m := source.2.2.2.1 pair.1 grain
  have read : Reads (v.markWire input o) (fun h g=>DescentSignedCableCodec.encode (v.markVenuePanel fit groups o h g))
      (ms).oldLanes m := by
    change Reads bank (fun h g=>sheet h (Fin.cast groups g)) (ms).oldLanes m
    exact mark_reads_cast groups bank sheet m atSource
  have endFrame:=(v.before_signed_any floor parts adj before mat m).2
  intro p
  have k : (row _ _ _ p).val<(v.markWire input o).size := (row _ _ _ p).isLt.trans_le (wire o).2
  have lt := (Nat.add_lt_add_left k (v.markWire input o).base).trans_le (wire o).1.2.2
  exact (venue.2 _ (.inl (lt.trans_le (v.signed_stage_paid floor).1))).trans
    ((endFrame _ (.inl lt)).trans (read p))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
