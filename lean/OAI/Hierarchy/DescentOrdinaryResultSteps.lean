import OAI.Hierarchy.DescentOrdinaryAfterSigned
import OAI.Hierarchy.DescentDatedOrdinaryVenueModel
import OAI.Hierarchy.DescentDatedOrdinaryFinal
import OAI.Hierarchy.DescentDatedPrimitiveUpdate

namespace OAI
/-! # Use the retained ordinary field and the same four-hop roster on both sides of the resolver -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentPacking.PackedMatch.Local.Stage DescentSIMDLookup DescentPackedColony DescentDatedAddressBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) (i : Dated.Operands)
    (A : ArgumentEntry v)

/-- The old paid-site census reads exactly the actor and roster banks emitted by
the earlier clipped ordinary ingress. -/
def fundedFromEntry (paths : A.clip.venue.paths=StageVenueTail.OrdinaryRaster.paths v.area) : v.FundedInputs :=
  ⟨A.clip.fieldBank (v.signedEnd floor),paths ▸ A.ports v floor⟩

variable {w : ℕ} (matched : A.Match v floor)
    (paths : A.clip.venue.paths=StageVenueTail.OrdinaryRaster.paths v.area)
    (src : OriginSources v) (producer : NativePhase w)
    (chipFit : (A.chipBank v floor).Fits w (v.refsStart floor))
    (shape : v.VectorShape) (fit : v.endAddress floor< 2^w)
    (packed : v.resolver.lanes*DescentPackedOperand.unit v.resolver.size≤ w/2)
    (radix : v.vector.radix=2^v.reference.k)
    (funded : v.FundedRoom floor (v.fundedFromEntry floor A paths) i w)
local notation "gather_" => v.argumentPhaseAfterSigned floor A matched src producer chipFit shape fit packed
local notation "held" => v.fundedRaster floor (v.fundedFromEntry floor A paths) i w funded

def ordinaryResultSteps : ResultSteps w:=
  ⟨A.venue.panel,A.venue.adjacency,gather_,held,v.primitiveUpdate floor A matched radix w⟩

theorem result_inputs
    (inlet : A.Room v floor w) (gather : (A.directory v floor matched).refs.Room w (v.vectorStart floor))
    (bounds : ∀j f,(src j f).Fits w (v.origin.outputBase (v.routedStart floor)))
    (cpu : ∀m,producer.Runs m ∧ ∀j,j< v.routedStart floor ∨ v.origin.grainBase (v.routedStart floor)≤ j →
      producer.image m j=m j) :
    let steps:=v.ordinaryResultSteps floor i A matched paths src producer chipFit shape fit packed radix funded
    Span steps.arguments (v.signedEnd floor) (v.endAddress floor) ∧ Span steps.paid (v.endAddress floor) (v.rasterEnd floor) :=by
  intro steps
  have first : v.signedEnd floor≤ v.endAddress floor:=by
    have h₁ := v.mount_order floor
    have h₂ := v.routed_order floor
    exact (Nat.le_add_right _ v.ingressWords).trans (h₁.1.trans (h₁.2.trans (h₂.1.trans (h₂.2.1.trans (h₂.2.2.1.trans (h₂.2.2.2.1.trans h₂.2.2.2.2))))))
  have second : v.endAddress floor≤ v.rasterEnd floor:=by
    change _≤ StageVenueTail.OrdinaryRaster.roof v.area v.venue v.rasterLanes (v.endAddress floor)
    rw [StageVenueTail.OrdinaryRaster.translated]
    exact Nat.le_add_right ..
  exact ⟨⟨first,v.argumentAfterSigned_any floor A matched src producer chipFit shape fit packed inlet gather bounds cpu⟩,
    ⟨second,v.fundedRaster_run floor (v.fundedFromEntry floor A paths) i w funded⟩⟩
theorem primitive_input (space : v.PrimitiveRoom floor A w) :
    Span (v.primitiveUpdate floor A matched radix w) (v.operandEnd floor) (v.primitiveEnd floor) :=
  ⟨(v.primitive_spent _).2,v.primitive_run floor A matched radix space⟩
end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
