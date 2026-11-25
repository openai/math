import OAI.Hierarchy.DescentRegisteredOrdinaryGeometry
import OAI.Hierarchy.DescentNamedSignedCalibrated
import OAI.Hierarchy.DescentNamedOrdinaryMarkRoom
import OAI.Hierarchy.DescentIssuedMaterialExtentRoom
import OAI.Hierarchy.DescentOrdinaryVenueExtent

namespace OAI
/-! # Native material, current hosts, marks and signed ordinals preceding the vector read -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentSixParty DescentCompiler DescentCompiler.TerminalScale
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {ι : ℕ→Type*} {Pins : ∀h,ι h→Type}
    (v : ∀h (i:ι h),PhysicalOrdinary F (Pins h i))
    (t f g reset τ B : ℕ) (sites age p seats floor root : ∀h,ι h→ℕ)
    (roster : ∀h,ι h→ProtocolRAM.Bank)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h) f g reset (sites h i) (tail τ (J_ h))
local notation "k_" h:arg =>groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "don_" h:arg i:arg => DonorDate.atDate G (S_ h i) g (k_ h) (age h i) (p h i)
local notation "core_" h:arg i:arg => StaticCore.atAge G (S_ h i) g (k_ h) (age h i) (p h i) h (seats h i) (root h i) (roster h i)



theorem reverse_from_material
    (r : MaterialExtent.ScalarRoom (fun h i=>(v h i).material)) :
    Bounded (fun h i=>(v h i).reverseWords) :=by
  apply PriorHeader.rate _ _ _ _ r.oldHosts r.reach
  exact r.oldHosts.mul ((r.groups.add r.lanes).of_le (fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)))

theorem ordinary_survivor_cost (source : Bounded sites)
    (active : ∀h i,age h i<(S_ h i).length)
    (bought : SignedStage.unitRate G t f g reset<B)
    (realized : ∀h i,(v h i).staticCore (floor h i)=core_ h i)
    (payload : ∀h i,(v h i).payload=h)
    (format : ∀h i,(v h i).signedLayout.format h=(v h i).signed)
    (outDegree : Bounded (fun h i=>(v h i).venue.degree)) :
    MaterialExtent.ScalarRoom (fun h i=>(v h i).material) ∧ Bounded (fun h i=>(v h i).survivorWords) :=by
  have geo:=ordinary_geometry G t f g reset τ B sites age p source (fun h i=>(active h i).le)
  have old (h : ℕ) (i : ι h) : (v h i).ticket.donorDate=don_ h i:=
    congrArg StaticCore.donor (realized h i)
  have a (h : ℕ) (i : ι h) : (v h i).area=(don_ h i).schedule h (seats h i) ((S_ h i).censusBits (p h i)):=
    congrArg StaticCore.area (realized h i)
  have s (h : ℕ) (i : ι h) : (v h i).signed=SignedStage.signedAt G (S_ h i) g (k_ h) (age h i) h:=
    congrArg StaticCore.signed (realized h i)
  have current : Bounded (fun h i=>NativePitch.incomingHosts (S_ h i) (age h i+1)) :=
    geo.axis.newHost.padded.of_le (fun h i=>(NativePitch.hosts_bounds _ _ (active h i)).2)
  have h₀ : Bounded (fun h i=>(v h i).area.H):=
    geo.axis.oldHost.padded.of_le (fun h i=>by rw [a]; rfl)
  have degree : Bounded (fun h i=>(v h i).prior.placement.degree):=
    geo.degree.of_le (fun h i=>(congrArg DonorDate.degree (old h i)).le)
  have cap (h : ℕ) (i : ι h) : (v h i).prior.placement.cap=(don_ h i).cap:=
    congrArg DonorDate.cap (old h i)
  have positive (h : ℕ) (i : ι h) : 256≤(v h i).prior.placement.cap:=by
    rw [cap]
    exact Nat.le_mul_of_pos_left _ (DonorDate.prefix_cap_pos G.b t g (J_ h) (age h i)
      (by have:=G.paid;omega))
  have material:=material_extent_room v payload format positive h₀
    (geo.axis.oldGroup.of_le (fun h i=>by rw [a]; rfl))
    (current.of_le (fun h i=>by rw [s]; rfl))
    (geo.axis.newGroup.of_le (fun h i=>by rw [s]; rfl))
    (geo.blocks.of_le (fun h i=>by rw [show (v h i).k=k_ h from congrArg DonorDate.exponent (old h i)]))
    degree (geo.cap.of_le (fun h i=>(cap h i).le))
  have reverse:=reverse_from_material v material
  have oldDegree : Bounded (fun h i => (v h i).area.D) :=
    geo.degree.of_le (fun h i => by rw [a]; rfl)
  have peer:=DescentOrdinaryVenueReturn.rate h₀ oldDegree
    (current.of_le (fun h i=>(congrArg (fun c:StaticCore=>c.prefixProgram.nextHosts) (realized h i)).le)) outDegree
  have marks:=VenueProgram.Registered.atAge_mark_room G (fun h i=>S_ h i) (fun _ _=>g) (fun h _=>k_ h) age p
    active geo.axis.oldHost geo.axis.newHost geo.axis.newGroup geo.blocks geo.degree geo.cap
  have markCost:=DescentOrdinaryMarkProject.Shape.extent_rate _ marks
  have booked : Bounded (fun h i=>(v h i).markShape.endAddress 0):=markCost.of_le (fun h i=>
    (congrArg (fun c:StaticCore=>c.prefixProgram.marked.endAddress 0) (realized h i)).le)
  have signed:=SignedStage.signedAt_unitRate_roof G t f g reset τ B bought sites age source
    (fun h i=>(active h i).le)
  have printed : Bounded (fun h i=>(v h i).signed.roof 0) :=signed.of_le (fun h i=>by rw [s])
  exact ⟨material,(((reverse.add (MaterialExtent.extent_rate _ material)).add peer).add booked).add printed⟩

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
