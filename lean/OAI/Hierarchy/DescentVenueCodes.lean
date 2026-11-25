import OAI.Hierarchy.DescentPackedVenueOrdinals
import OAI.Hierarchy.DescentColoredHost
import OAI.Hierarchy.DescentHubOccupancy

namespace OAI
/-! # Stable packed venue numbers and the actual old and born quotient locations -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentHostDirectory DescentPacking GadgetNetwork
open scoped Classical
noncomputable section
variable {V C : Type} [Fintype C] [DecidableEq C]
variable {d : ℕ} {P : Type} {bits : P→ℕ} (N : Network d P bits)
variable (core : Finset N.Edge) (home : N.Site→C) (color : N.Site→Bool) (B : ℕ)
variable (col : C↪V×(ℕ×ℕ)) (same : ∀e∈core,color (N.src e)=color (N.dst e)) (l : Bool)
local notation "pick" => colorPick N core home color B
local notation "pack" => coloredPack N core home color B
local notation "slot" => chosenSlot N core home color B
local notation "center" => chosenCenter N core home color B l
local notation "key" => nativeKey N core home color B col same l
local notation "base" => packAddress N core home color B col

/-- An old site uses the resolved venue of its actual colored pack. -/
theorem venue_old (u : N.Site) :
    key (newSite N pick l pack (.inl u))=base (resolve slot center (pack u)) := rfl

/-- Published party rows gather only one of the three authentic old endpoints. -/
theorem venue_birth (i : NativePair N core home color B) (j : Fin 6) :
    key (newSite N pick l pack (.inr (i,j)))=
      key (newSite N pick l pack (.inl (endpoint N pick i (cluster l j)))) := rfl

/-- The key stored by every potential competing write for the same thin slot is
identical. It is the pack at the live thick endpoint. -/
theorem thin_resolves (i : NativePair N core home color B) :
    key (newSite N pick l pack (.inl (N.src (pick (i,1)))))=
      base (pack (thickCenter N pick l i)) := by
  have thin : pack (N.src (pick (i,1))) = .inr (slot i) :=
    colorPick_thin_src N core home color B i
  have thick : pack (thickCenter N pick l i) = .inl (center i) :=
    native_centerAt N core home color B same l i
  have coherent : ∀ x y, slot x = slot y → center x = center y :=
    native_coherent (fun _ => nativeTraffic N core home) B (thinList home color)
      (thickList home color) (fun _ c => c) l
  exact congrArg base (((congrArg (resolve slot center) thin).trans
    (resolve_active slot center coherent i)).trans thick.symm)

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
