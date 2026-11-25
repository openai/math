import OAI.Hierarchy.DescentNamedSignedUnit
import OAI.Hierarchy.DescentNamedSignedRoom

namespace OAI
/-! # Choosing a single signed address budget before the original dates -/
namespace Hierarchy.DescentDatedAddressBook.SignedStage
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentDatedSeedStartup Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ : ℕ)
local notation "J_" h:arg B:arg => Nat.log 2 h/(2*B)
local notation "k_" j:arg => groupBits t j (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "S_" j:arg n:arg => stageNumbers G t j f g reset n (tail τ j)

/-- All real ordinary pages fit a fixed linear address exponent on this family. -/
theorem signedAt_unitRate_roof {ι : ℕ→Type*} :
    ∀ B : ℕ,unitRate G t f g reset<B → ∀ sites age : (∀h,ι h→ℕ),Bounded sites →
      (∀h i,age h i≤(S_ (J_ h B) (sites h i)).length) →
      Bounded (fun h i=>(signedAt G (S_ (J_ h B) (sites h i)) g (k_ (J_ h B)) (age h i) h).roof 0) := by
  intro B slack sites age source before
  apply signedAt_roof_bounded G t f g reset τ B sites age source before
  exact (unitRate_cofinal G t f g reset B slack).mono fun _ free i=>free _ _ _ _ (before _ i)

theorem signedAt_calibrated_roof {ι : ℕ→Type*} :
    ∃e : ℕ,∀ B : ℕ,e<B → ∀ sites age : (∀h,ι h→ℕ),Bounded sites →
      (∀h i,age h i≤(S_ (J_ h B) (sites h i)).length) →
      Bounded (fun h i=>(signedAt G (S_ (J_ h B) (sites h i)) g (k_ (J_ h B)) (age h i) h).roof 0) :=
  ⟨unitRate G t f g reset,signedAt_unitRate_roof G t f g reset τ⟩

end
end Hierarchy.DescentDatedAddressBook.SignedStage

end OAI
