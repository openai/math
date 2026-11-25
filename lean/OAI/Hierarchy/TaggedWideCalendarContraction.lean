import OAI.Hierarchy.TaggedWideCalendarSites
import OAI.Hierarchy.TaggedWidePartyTerm
import OAI.Hierarchy.TaggedWireActiveRouting

namespace OAI
/-! # The literal chronological site network contracts to the original selected route -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing
open AdaptiveProbe WireTelescope TaggedPrune Tagged ProtocolRAM.Calendar WireTelescope.CalendarTape
open scoped Classical BigOperators
set_option quotPrecheck false
variable {F : Type*} [Field F] {X : Type} {z d k w R M den : ℕ}
  {slots : Event → Slot X} {es : List Event} {state : Equiv.Perm (Row z) → X}
  (Z : CalendarTerms F z d k w R M den slots es state)
  (Shared : Type) [Fintype Shared] (p : Equiv.Perm (Row z)) (i : Fin ((Z.nativeRouting Shared).count p))
local notation "B" => (Prefix.start : Prefix slots es (state p) es (state p))
local notation "C" => (Prefix.cursorSlot (slot:=slots) (events:=es) (x₀:=state p))
local notation "V₀" => Prefix.atCursor B
local notation "ws" => Prefix.atWidth (Z.width p)
local notation "step" => Prefix.atStep (Z.width p) (Z.operator p)
local notation "rep" => cursorReport p (Z.width p) (Z.reported p)
local notation "branch" => (Prefix.histories B) ((Fintype.equivFin (Path slots es (state p))).symm i)
local notation "words" => (∀ e, Fin (2^(rep branch).widthAt e))
local notation "Sites" => Fin (siteLast z d k+1)
local notation "Ports" => OpenPins z w (fun _ : Fin k => Fintype.card (Columns z d)*R)

/-- The outer and inner sums run over the selected original row words and the
public chronological aperture. Every factor is the value of one fixed physical
network. Only its native observations depend on the selected branch. -/
theorem route_site_network {N : ℕ} {V : Type} [Fintype V]
    (ext : Ports → Bool)
    (place : PartyBit C ws es V₀ branch ↪ Fin N)
    (pins : words → (Fin N→Bool) → V→Bool)
    (entryNet endNet : Sites → WideCalendarSites.Net F V)
    (rowNet : Sites → Fin es.length → WideCalendarSites.Net F V)
    (first : ∀ a (z₀ : SiteChoices C ws es V₀ branch) s,
      TypedWiring.value (entryNet s) (pins a (placedBits C ws es V₀ branch place z₀)) =
        entry p ws V₀ (Z.head p) s (fun t=>ext (routingPort t.val)) (z₀ s).1)
    (finish : ∀ a (z₀ : SiteChoices C ws es V₀ branch) s,
      TypedWiring.value (endNet s) (pins a (placedBits C ws es V₀ branch place z₀)) =
        (rep branch).finish s (WideCalendarSites.last C ws s es V₀ branch (z₀ s).1 (z₀ s).2)
          ((rep branch).ports a s))
    (steps : ∀ a (z₀ : SiteChoices C ws es V₀ branch) s,
      WideCalendarSites.Reads C ws step s es V₀ branch (z₀ s).1 (z₀ s).2 (fun j=>
        TypedWiring.value (rowNet s j) (pins a (placedBits C ws es V₀ branch place z₀)))) :
    (∑ a : words, ∑ data : Fin N→Bool,
       if ∀ j, data j=true → j∈Set.range place then
         TypedWiring.value (WideCalendarSites.network entryNet endNet rowNet) (pins a data) else 0) =
       (Z.nativeRouting Shared).route ⟨p,i⟩ ext := by
  simp only [WideCalendarSites.network_value]
  rw [Z.route_pins]
  apply site_apertures p C es ws V₀ (Z.head p) step
    (Prefix.atStep_sum (Z.width p) (Z.operator p) (Z.step p)) rep branch
    (fun _ t=>ext (routingPort t.val)) place
    (fun a v s=>TypedWiring.value (WideCalendarSites.site (entryNet s) (endNet s) (rowNet s)) (pins a v))
  intro a q s
  exact WideCalendarSites.site_on_state C ws step s es V₀ branch (q s).1 (q s).2
    (fun t=>(rep branch).finish s t ((rep branch).ports a s)) _
    (entryNet s) (endNet s) (rowNet s) _ (first a q s) (finish a q s) (steps a q s)

end Hierarchy.ProbeStage.CoreBoard.PhysicalTerm.CalendarTerms

end
end OAI
