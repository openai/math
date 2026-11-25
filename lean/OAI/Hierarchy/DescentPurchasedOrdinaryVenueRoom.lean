import OAI.Hierarchy.DescentNamedOrdinaryVenueRoom
import OAI.Hierarchy.DescentNamedPurchasedOrdinaryBooks

namespace OAI
/-! # Address bounds for the ordinary venue at the published funded clip -/
namespace Hierarchy.DescentSixParty.StageVenueTail.Date
open DescentDatedAddressBook DescentCompiler DescentCompiler.TerminalScale Chronology
open DescentPacking.PackedMatch.Local.Stage Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) {ι : ℕ→Type*}
variable (t f g reset τ : ℕ)
local notation "J_" h:arg B:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg B:arg n:arg => stageNumbers G t (J_ h B) f g reset n (tail τ (J_ h B))
local notation "k_" h:arg B:arg => groupBits t (J_ h B) (hostRate t reset) (capRate G t g) (cutRate t f g)

theorem purchased_venue_room_at : ∀ B : ℕ,SignedStage.unitRate G t f g reset<B → τ≤B →
    ∀ sites age grain : (∀h,ι h→ℕ),∀ programs : (∀h,ι h→ℕ→Dated.Ordinary),
    ∀ books : (∀h,ι h→OrdinaryBooks),∀ core : (∀h,ι h→PhysicalOrdinary.StaticCore),
    ∀ ports : (∀h,ι h→DatePorts),Bounded sites →
      (∀h i,age h i<(S_ h B (sites h i)).length) → (∀h i j,(programs h i j).payload=h) →
      (∀h i,(core h i).area.payload=h) →
      ScalarRoom (fun h i=>
        let S:=S_ h B (sites h i)
        let c:=OrdinaryBooks.purchaseClip G (books h i) (core h i) (ports h i) (S.censusBits (grain h i))
        atOrdinary G S g (k_ h B) (tail τ (J_ h B)) (grain h i) f h (programs h i) (age h i) c.postPitch) := by
  intro B slack tailRoom sites age grain programs books core ports source before issued height
  let c:=fun h i=>OrdinaryBooks.purchaseClip G (books h i) (core h i) (ports h i) ((S_ h B (sites h i)).censusBits (grain h i))
  apply ordinary_venue_room G t f g reset τ B sites age grain (fun h i=>(c h i).postPitch) programs
    (by omega) tailRoom source before issued
  · intro h i
    have fit:=PhysicalOrdinary.fundedClipAt_paid_pitch (core h i).area (core h i).format
      (core h i).donor.amount ((S_ h B (sites h i)).censusBits (grain h i))
      ((books h i).argumentCost G (core h i) (ports h i) ((S_ h B (sites h i)).censusBits (grain h i)))
    change (c h i).postPitch≤(core h i).area.payload ∧ _ ≤ (core h i).area.payload/4 at fit
    rw [height] at fit
    exact fit
  · exact (SignedStage.unitRate_cofinal G t f g reset B slack).mono fun _ free i=>free _ _ _ _ (before _ i).le

theorem purchased_venue_room : ∃e : ℕ,∀ B : ℕ,e<B → τ≤B →
    ∀ sites age grain : (∀h,ι h→ℕ),∀ programs : (∀h,ι h→ℕ→Dated.Ordinary),
    ∀ books : (∀h,ι h→OrdinaryBooks),∀ core : (∀h,ι h→PhysicalOrdinary.StaticCore),
    ∀ ports : (∀h,ι h→DatePorts),Bounded sites →
      (∀h i,age h i<(S_ h B (sites h i)).length) → (∀h i j,(programs h i j).payload=h) →
      (∀h i,(core h i).area.payload=h) →
      ScalarRoom (fun h i=>
        let S:=S_ h B (sites h i)
        let c:=OrdinaryBooks.purchaseClip G (books h i) (core h i) (ports h i) (S.censusBits (grain h i))
        atOrdinary G S g (k_ h B) (tail τ (J_ h B)) (grain h i) f h (programs h i) (age h i) c.postPitch) :=
  ⟨SignedStage.unitRate G t f g reset,purchased_venue_room_at G t f g reset τ⟩

end
end Hierarchy.DescentSixParty.StageVenueTail.Date

end OAI
