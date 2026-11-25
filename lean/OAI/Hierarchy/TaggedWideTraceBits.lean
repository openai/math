import OAI.Hierarchy.TaggedWireSiteBits
import OAI.Hierarchy.TaggedWirePartyTrace
import OAI.Hierarchy.TaggedWidePadding
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # Static zero-padded coordinates for the actual chronological site states -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open LinearAlgebra.SpectralBooks ChordGraph ProtocolRAM.Calendar
open scoped Classical BigOperators

variable {S : ℕ} {X : Type} (slot : Event→Slot X) (wire : X→Widths S)

def LaterBit (s : Fin S) : (es : List Event)→(x : X)→Path slot es x→Type
  | [],_,_=>Empty
  | e::es,x,j=>SiteBit (wire ((slot e).next x j.1)) s ⊕ LaterBit s es ((slot e).next x j.1) j.2

def laterBits (s : Fin S) : ∀ es x j,PartyStates slot wire s es x j ≃ (LaterBit slot wire s es x j→Bool)
  | [],_,_=>Equiv.ofUnique Unit (Empty→Bool)
  | e::es,x,j=>
    let y := (slot e).next x j.1
    ((siteBits (wire y) s).prodCongr (laterBits s es y j.2)).trans
      (Equiv.sumArrowEquivProdArrow _ _ Bool).symm

abbrev PartyBit (es : List Event) (x : X) (j : Path slot es x) :=
  (s : Fin S) × (SiteBit (wire x) s ⊕ LaterBit slot wire s es x j)

abbrev SiteChoices (es : List Event) (x : X) (j : Path slot es x) :=
  ∀s,State (wire x) s × PartyStates slot wire s es x j

/-- One coordinate for each actual site, time boundary, incident chord and
bit. In particular a transition output is the next transition's same input. -/
def partyBits (es : List Event) (x : X) (j : Path slot es x) :
    SiteChoices slot wire es x j ≃ (PartyBit slot wire es x j→Bool) :=
  (Equiv.piCongrRight (fun s=>((siteBits (wire x) s).prodCongr (laterBits slot wire s es x j)).trans
    (Equiv.sumArrowEquivProdArrow _ _ Bool).symm)).trans
      (Equiv.piCurry (fun (s : Fin S) (_ : SiteBit (wire x) s ⊕ LaterBit slot wire s es x j)=>Bool)).symm

def placedBits {N : ℕ} (es : List Event) (x : X) (j : Path slot es x)
    (place : PartyBit slot wire es x j ↪ Fin N) (z : SiteChoices slot wire es x j) : Fin N→Bool :=
  Tagged.WidePadding.pad (fun i=>i∈Set.range place)
    ((Equiv.arrowCongr (Equiv.ofInjective place place.injective) (Equiv.refl Bool)) (partyBits slot wire es x j z))

/-- Contracting a finite fixed site workspace with zero tests on inactive
ports yields precisely the actual party-state sum. The physical receipt
`place` need only be injective on the live sites/times/chord bits. -/
theorem sum_party_states {F : Type*} [CommSemiring F] {N : ℕ} (es : List Event) (x : X) (j : Path slot es x)
    (place : PartyBit slot wire es x j ↪ Fin N) (φ : (Fin N→Bool)→F) :
    (∑ a : Fin N→Bool, if ∀i,a i=true → i∈Set.range place then φ a else 0) =
      ∑ z : SiteChoices slot wire es x j,φ (placedBits slot wire es x j place z) := by
  let used := fun i=>i∈Set.range place
  let e := (partyBits slot wire es x j).trans
    (Equiv.arrowCongr (Equiv.ofInjective place place.injective) (Equiv.refl Bool))
  exact (Tagged.WidePadding.sum_padded used φ).trans
    (e.sum_comp (fun a=>φ (Tagged.WidePadding.pad used a))).symm

end Hierarchy.WireTelescope.CalendarTape

end
end OAI
