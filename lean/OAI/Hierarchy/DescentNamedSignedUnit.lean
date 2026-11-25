import OAI.Hierarchy.DescentNamedSignedDate
import OAI.Hierarchy.DescentSignedStageRates
import OAI.Hierarchy.DescentCapAtAge
import OAI.Hierarchy.DescentSeedNumberRates

namespace OAI
/-! # Choosing a single signed address budget before the original dates -/
namespace Hierarchy.DescentDatedAddressBook.SignedStage
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentDatedSeedStartup Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ : ℕ)
local notation "J_" h:arg B:arg => Nat.log 2 h/(2*B)
local notation "k_" j:arg => groupBits t j (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "S_" j:arg n:arg => stageNumbers G t j f g reset n (tail τ j)

/-- A signed format exponent fixed before the terminal tail, the number of sites and the date. -/
def unitRate : ℕ := (uniform t (hostRate t reset) (capRate G t g) (cutRate t f g)
  (initialDegreeMax t) G.b G.C G.k 0).choose

theorem unitRate_atDate (J M frozen a H : ℕ) (before : a≤(t+1)*J) :
    (atDate G (stageNumbers G t J f g reset M frozen) g (k_ J) a H).unit ≤
      scale J (unitRate G t f g reset) := by
  let S:=stageNumbers G t J f g reset M frozen
  let date:=atDate G S g (k_ J) a H
  have degree : date.oldDegree ≤ initialDegreeMax t := seed_degree t G.b _
  have capacity : date.oldCap ≤ 2^(8+capRate G t g*((t+1)*J)) :=
    (NativePitch.cap_at_age G t g J a).trans (Nat.pow_le_pow_right (by decide : 0<2)
      (Nat.add_le_add_left (Nat.mul_le_mul_left _ before) 8))
  have witness:=(uniform t (hostRate t reset) (capRate G t g) (cutRate t f g)
    (initialDegreeMax t) G.b G.C G.k 0).choose_spec.choose_spec
  exact (witness J date.oldDegree date.oldCap 0 date.oldHosts date.newHosts date.groups 0
    degree capacity (Nat.zero_le _)).1

theorem unitRate_cofinal (B : ℕ) (slack : unitRate G t f g reset<B) :
    ∀ᶠ h : ℕ in atTop,∀ M frozen a H : ℕ,a≤(t+1)*(J_ h B) →
      2*(atDate G (stageNumbers G t (J_ h B) f g reset M frozen) g (k_ (J_ h B)) a H).unit≤h := by
  filter_upwards [AgeBound.payload_room (unitRate G t f g reset) B slack] with h large
  exact fun M frozen a H before=>(Nat.mul_le_mul_left 2
    (unitRate_atDate G t f g reset _ M frozen a H before)).trans large

theorem signedAt_unit_calibration :
    ∃e : ℕ,(∀ J M a H : ℕ,a≤(t+1)*J → (atDate G (S_ J M) g (k_ J) a H).unit ≤ scale J e) ∧
      ∀ B : ℕ,e<B → ∀ᶠ h : ℕ in atTop,∀ M a H : ℕ,a≤(t+1)*(J_ h B) →
        2*(atDate G (S_ (J_ h B) M) g (k_ (J_ h B)) a H).unit ≤ h := by
  refine ⟨unitRate G t f g reset,fun J M a H=>unitRate_atDate G t f g reset J M _ a H,?_⟩
  exact fun B slack=>(unitRate_cofinal G t f g reset B slack).mono fun _ fits M a H=>fits M _ a H

end
end Hierarchy.DescentDatedAddressBook.SignedStage

end OAI
