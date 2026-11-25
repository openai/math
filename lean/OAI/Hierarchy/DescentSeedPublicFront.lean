import OAI.Hierarchy.DescentSeedPackedHeaderNumbers
import OAI.Hierarchy.DescentWideSeedCalendarFee
import OAI.Hierarchy.DescentPackedEpochShelfLayout
import OAI.Hierarchy.DescentEpochAdviceLayoutNumbers
import OAI.Hierarchy.DescentExteriorShelfNumbers

namespace OAI
/-! # The physical address of the complete public prefix and of its selector directory -/
namespace Hierarchy.DescentWideSeedFlags
open DescentInitialHost DescentPackedEpochShelves DescentTerminalEpochChart DescentPackedProfileInstall
open DescentExterior Catalyst
noncomputable section
section
variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (R s h : ℕ)

/-- Packed original words, one seed verdict, and one returned count per dated profile. -/
def selectorBase (dates : ℕ) := endInput X R s h+DescentPackedSeed.rows X R s h+1+dates

end
variable {F : Type} [Field F] {cp nP : ℕ}
def publicFront (X : Approximation F cp nP) {A : Type} (R s payload C : ℕ) (steps : List (Source A))
    (j rest : ℕ) :=
  let lo := selectorBase X R s payload steps.length
  let grain_ := grain (payload/2) C
  end_ (lo+extent grain_ steps) C grain_+17*DescentExteriorShelf.span j rest s (ExteriorCount X)

end
end Hierarchy.DescentWideSeedFlags

end OAI
