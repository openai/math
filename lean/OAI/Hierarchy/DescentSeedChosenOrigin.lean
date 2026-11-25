import OAI.Hierarchy.DescentSeedOriginIdentity
import OAI.Hierarchy.DescentSeedEarnedLink

namespace OAI
/-! # The original reached source used by the named epoch history -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentCompiler DescentHostDegree Catalyst
noncomputable section
variable {F : Type} [Field F] {cp pins : ℕ}

/-- Select the actual initialized placement and its row receipts together. -/
def originalOrigin (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
    {z f k s : ℕ} (grain : 0 < z) (bits : 0 < k) (positive : 0 < S.height)
    (cut : packExponent 20 3 ≤ f) (radix : S.radix=2^k)
    (width : k=groupBits S.rounds S.height S.hostGain S.capGain f)
    (budget : 10*(X.size+1) ≤ S.initialSites) (size : s=z*G.b)
    (c : (initialGroup X S.copies s).Choice) :
    let wire := S.epochPower^S.priceExponent
    let q := 1/((s:ℝ)*wire)
    let fee := ((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower
    Origin X (G:=G) (S:=S) (z:=z) (wire:=wire) (q:=q) (fee:=fee) c (S.initialDigits radix) := by
  subst s
  let ticket := Chronology.initial_link X G S grain bits positive cut radix width budget c
  exact ⟨ticket.choose,ticket.choose_spec⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
