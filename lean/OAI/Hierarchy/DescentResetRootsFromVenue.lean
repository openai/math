import OAI.Hierarchy.DescentResetAtlasPrefix

namespace OAI
/-! # The original wire operands of a reset date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.RootInputs
open DescentSixParty DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (a : PhysicalReset)
local notation "middle₀" => a.successor.middle

/-- The physical root phase reads the old signed column with the original block followed
by its signed socket. The date's single measured atlas supplies every template. -/
def fromVenue (io : Dated.Operands) (Ht : ℕ) (ratio : 0<(middle₀).signedRatio)
    (batch : 0<(middle₀).signedLanes)
    (split : (middle₀).rootGroups=((middle₀).rootGroups/((middle₀).signedRatio*(middle₀).signedLanes))*
      ((middle₀).signedRatio*(middle₀).signedLanes)) : a.RootInputs :=
  ⟨(middle₀).rootField,Ht,fun s x=>io.wire x.val s.val,ratio,batch,split⟩

theorem wire (io : Dated.Operands) (Ht : ℕ) (ratio batch split) (s x) :
    (fromVenue a io Ht ratio batch split).old s x=io.wire x.val s.val :=rfl

/-- Both seed and successor venue charts state the two halves of this inequality
on the same physical bank. No values from a reached memory are needed. -/
theorem prefix_from_venue (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ)
    (io : Dated.Operands) (Ht : ℕ) (ratio batch split) (w : ℕ) (shape : a.RootShape)
    (previous : ℕ) (floor_bound : previous≤(a.stencilPhase sh floor count hub g Y).endAddress)
    (wire_room : ∀(x : Fin (middle₀).oldBlocks) (s : Fin (2*(a.c/2))),
      (io.wire x.val s.val).Fits w previous ∧
        (middle₀).signedHosts*chunks (middle₀).rootGroups ((middle₀).signedRatio*(middle₀).signedLanes)≤(io.wire x.val s.val).size)
    (high : (middle₀).stencil.c=(middle₀).high+a.e) (pitch : (middle₀).signedLanes=2^a.e)
    (width : (middle₀).signedLanes*max (DescentFallbackPeriod.Projected.maxBits (middle₀).stencil.t
      a.ports (a.c/2) (2^(middle₀).rootDepth)) (middle₀).rootField ≤ w/2)
    (last : (a.rootPhase sh floor count hub g Y (fromVenue a io Ht ratio batch split) w).projectionEnd < 2^w) :
    (a.rootPhase sh floor count hub g Y (fromVenue a io Ht ratio batch split) w).PrefixFits := by
  apply a.atlas_prefix sh floor count hub g Y (fromVenue a io Ht ratio batch split) shape _ _ high pitch width last
  · intro s x
    have h:=(wire_room x s).1
    exact ⟨h.1,h.2.1,h.2.2.trans floor_bound⟩
  · exact fun s x=>(wire_room x s).2

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.RootInputs

end OAI
