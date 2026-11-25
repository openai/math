import OAI.Hierarchy.DescentSeedChosenLayoutCore
import OAI.Hierarchy.DescentSeedNumberRates

namespace OAI
/-! # Uniform price of the first donor width computed by the selected startup layout -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem first_donor_amount_rate (t f g reset : ℕ) :
    ∃a : ℕ,∀ J M tail p : ℕ,
      let S:=stageNumbers G t J f g reset M tail
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      firstDonor G S g k p ≤ scale J a :=by
  obtain ⟨_,a,bound⟩:=donor_uniform t (hostRate t reset) (capRate G t g) (cutRate t f g)
    (initialDegreeMax t) G.b G.C G.k
  refine ⟨a,?_⟩
  intro J M tail p S k
  let degree:=originalDegree G S g
  have allowed : degree ≤ initialDegreeMax t :=seed_degree _ _ _
  have cap : 256 ≤ 2^(8+capRate G t g*((t+1)*J)) := by
    change (2:ℕ)^8 ≤ 2^(8+capRate G t g*((t+1)*J))
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right ..)
  exact (bound J degree 256 allowed cap).2

end Hierarchy.DescentDatedSeedStartup

end OAI
