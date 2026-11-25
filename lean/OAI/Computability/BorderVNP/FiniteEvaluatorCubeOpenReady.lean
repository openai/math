import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenRoom
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenControls

/-! # Complete signed precondition of the four-program cube suffix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SignedTaskArena

open Packing BottomReports BorderVNP.Cube FiniteEvaluator

variable (t : Layout) {team frame offsets control live ports bundles b w : ℕ}
variable (owner : Fin bundles → Fin t.cube.cells) (header : Fin bundles → BundleHeader)

local notation "H" => t.openInputs team frame offsets control live ports bundles b owner header

/-- The true header fields, the marked sort from the physical geometry, and the
numerical allocation suffice to execute the complete suffix. Each intermediate
load is discharged on the actual memory image of its preceding instructions. -/
theorem Layout.ready_of_signed {m : ℕ → ℕ} (fields : t.OpenFields team frame offsets control live ports bundles m)
    (controlWords : ∀ i : Fin 37, m (control+i.val)=t.controls i.val)
    (room : t.OpenRoom frame offsets control live ports bundles (2^b) w)
    (bank : t.p.bundleInverse=t.p.bundlePayload+2^b)
    (sort : BundleSort.SectionSpec room.markers owner header m t.p.bundlePayload)
    (padding : Padding.HeaderFits w frame m) (padFit : (Padding.Layout.fromFrame frame m).Fits w m)
    (hostFit : (HostScatter.Layout.fromFrame frame m).Fits w m)
    (hostDest : let h := HostScatter.Layout.fromFrame frame m
      ∀ i < h.count, ∀ side, h.Owned m i side → t.cube.cellBank ≤ h.dest m i side) :
    OpenSuffix.Ready (H) frame m w := by
  obtain ⟨hdr,banks,_⟩ := t.open_table_order
  have low : frame+112 ≤ t.cube.cellBank := by have := room.primary; omega
  obtain ⟨load,sections,total,rows⟩ := t.open_inputs_read owner header fields controlWords room.markers bank sort
    low (room.controlEnd.trans hdr) (room.rankEnd.trans hdr) hostDest
  exact ⟨padding,padFit,hostFit,padding.frameEnd,padding.declarationEnd,load,room.bundle_fit,sections,total,
    rfl,rows,room.controls_fit team⟩

/-- The profile bank certificate and signed controls can be read at their
original execution. Their entire lower geometry region and the ten indicated
frame fields suffice at entry to the post-ownership suffix. -/
theorem Layout.ready_of_resident {m profile : ℕ → ℕ}
    (fields : t.OpenFields team frame offsets control live ports bundles profile)
    (controlWords : ∀ i : Fin 37, profile (control+i.val)=t.controls i.val)
    (room : t.OpenRoom frame offsets control live ports bundles (2^b) w)
    (bank : t.p.bundleInverse=t.p.bundlePayload+2^b)
    (sort : BundleSort.SectionSpec room.markers owner header profile t.p.bundlePayload)
    (frameWords : ∀ i ∈ [0,1,7,15,65,66,67,72,87,92], m (frame+i)=profile (frame+i))
    (geometry : ∀ a, control ≤ a → a<t.cube.header.header → m a=profile a)
    (payload : control ≤ t.p.bundlePayload)
    (padding : Padding.HeaderFits w frame m) (padFit : (Padding.Layout.fromFrame frame m).Fits w m)
    (hostFit : (HostScatter.Layout.fromFrame frame m).Fits w m)
    (hostDest : let h := HostScatter.Layout.fromFrame frame m
      ∀ i < h.count, ∀ side, h.Owned m i side → t.cube.cellBank ≤ h.dest m i side) :
    OpenSuffix.Ready (H) frame m w := by
  have retained := sort.transfer (m':=m) (fun a lo hi => geometry a (payload.trans lo)
    (by have h := room.rankEnd; omega))
  exact t.ready_of_signed owner header (fields.transfer t frameWords) (fun i =>
    (geometry _ (Nat.le_add_right ..) (by have h := i.isLt; have hc := room.controlEnd; omega)).trans (controlWords i))
    room bank retained padding padFit hostFit hostDest

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
