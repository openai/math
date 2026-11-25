import OAI.Hierarchy.DescentDatedPrimitiveRead
import OAI.Hierarchy.DescentDatedPrimitiveFunding
import OAI.Hierarchy.DescentOrdinaryOriginPersistence
import OAI.Hierarchy.DescentOrdinaryDatedEntry

namespace OAI
/-! Both the chamber limits and the actual receiver row capacities come from
the emitted ingress, origin and fresh role banks. -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryPrimitiveCheckpoint ProtocolRAM DescentPackedColony DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ)
    (A : ArgumentEntry v) (match_ : A.Match v floor) (radix : v.vector.radix=2^v.reference.k)
local notation "L" => v.paletteShape
local notation "edge" => v.operandEnd floor
local notation "base" => v.primitiveFirst edge
local notation "src" => v.primitiveSources floor A match_ radix

include match_ in
theorem primitive_input_order (reserved : v.originControlWords≤v.origin.preparationWords) :
    A.finish v floor≤edge ∧ v.originPortFloor floor≤edge:=by
  have edges:=v.routed_order floor
  have stop : v.endAddress floor≤edge:=by
    rw [operandEnd,v.operandBook.affine,metaEnd,v.metadata.ordinary_translate,metaStart,venueEnd,v.venue.translates,
      rasterEnd,StageVenueTail.OrdinaryRaster.translated]
    omega
  have scan : v.origin.grainBase (v.routedStart floor)≤edge:=
    edges.2.2.1.trans (edges.2.2.2.1.trans (edges.2.2.2.2.trans stop))
  have raw : v.refsStart floor≤v.routedStart floor:=by
    refine (show v.refsStart floor≤v.birthStart floor from Nat.le_add_right ..).trans (le_trans ?_ edges.1)
    rw [vectorStart,v.bornBook.affine];exact Nat.le_add_right ..
  have foot : v.originPortEnd floor≤v.origin.grainBase (v.routedStart floor):=by
    rw [v.originPort_span floor]
    exact Nat.add_le_add_left reserved _
  exact ⟨match_.atRefs.le.trans (raw.trans (edges.2.1.trans scan)),(Nat.le_add_right _ _).trans (foot.trans scan)⟩

theorem registered_primitive_input_order (ports : DatePorts) (enough : ports.argumentsPerNode≤v.vector.operands) :
    let Y:=v.registeredFrom ports floor
    let input:=v.registeredEntry ports floor
    input.finish Y floor≤Y.operandEnd floor ∧ Y.originPortFloor floor≤Y.operandEnd floor:=by
  intro Y input
  apply primitive_input_order Y floor input (v.registered_match ports floor enough)
  have allocation:=(v.fundedFrom ports floor).origin_reservation
  change Y.originControlWords≤Y.origin.preparationWords
  change Y.origin.preparationWords=Y.originControlWords+Y.originMouthWords+Y.rootSourceSize at allocation
  omega

theorem primitive_input_rooms {w h unit : ℕ} (inlet : A.Room v floor w) (local_ : (L).Funding h unit)
    (afterInlet : A.finish v floor≤edge) (afterOrigins : v.originPortFloor floor≤edge)
    (ceiling : v.primitiveRoof edge<2^w) (host : A.clip.venue.hosts=(L).hosts)
    (group : A.clip.venue.groups=(L).oldGroups) (pitch : A.clip.working=(L).priorLanes)
    (chipH : v.bornBook.hosts=(L).hosts) (chipG : v.bornBook.groups=(L).oldGroups) :
    v.PrimitiveRoom floor A w ∧ (L).Capacity src:=by
  have edgeFit : edge<2^w:=(v.primitive_spent edge).2.trans_lt ceiling
  have room : base<2^w:=by
    have span:=(L).translated base
    exact (show base≤(L).roof base by rw [span];exact Nat.le_add_right ..).trans_lt ceiling
  have walkBefore : (A.population v floor).outBase≤edge:=(Nat.le_add_right _ _).trans afterInlet
  have birthBefore : A.populationBase v floor≤edge:=(Nat.le_add_right _ _).trans walkBefore
  have chipFit : (A.chipBank v floor).Fits w edge:=by
    have top : (A.chipBank v floor).base+(A.chipBank v floor).size≤edge:=birthBefore
    change 0<2^_ ∧ _<2^w ∧ _≤edge
    exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (top.trans_lt edgeFit),top⟩
  have sample : Fin A.previous.blocks:=⟨0,by rw [match_.oldBlocks];exact Nat.two_pow_pos _⟩
  have adj:=inlet.walk sample
  have oldSpan : A.clip.venue.hosts*A.clip.venue.paths≤(A.ports v floor).roster.size:=adj.rosterRoom
  have id₀ (x : Fin v.vector.radix) :=
    v.originChart.grid.returned_fits (v.originChart.rowsAt (v.routedStart floor)) x (afterOrigins.trans_lt edgeFit)
  refine ⟨⟨fun x=>Layout.widen walkBefore (inlet.walk x).source,chipFit,
      fun x=>Layout.widen afterOrigins (id₀ x).1,Layout.widen walkBefore adj.roster,?_,ceiling⟩,
    ⟨?_,?_,?_,local_.old.positive,local_.newborn.positive,local_.ranks.positive,local_.working.positive⟩⟩
  · rw [host,match_.paths] at oldSpan;exact oldSpan
  · intro x
    have source:=(inlet.walk (x.cast match_.oldBlocks.symm)).srcRoom
    rw [host,group,pitch] at source
    exact source
  · intro x
    have published:=(DescentOrdinaryPaletteBirth.placed v.bornBook edge room
      (x.cast (show (L).fields=DescentOrdinaryPaletteBirth.fields v.bornBook from by
        change 2^v.reference.k*v.reference.capacity*6=v.bornBook.blocks*v.bornBook.cap*6
        rw [match_.newBlocks,match_.newCap]))).2
    change v.bornBook.hosts*chunks v.bornBook.groups v.bornBook.lanes≤_ at published
    change (L).hosts * chunks (L).oldGroups v.bornBook.lanes ≤ (DescentOrdinaryPaletteBirth.bank v.bornBook edge _).size
    rw [chipH, chipG] at published
    exact published
  · intro x
    exact (id₀ (x.cast radix.symm)).2

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
