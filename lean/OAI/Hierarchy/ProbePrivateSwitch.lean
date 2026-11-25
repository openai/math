import OAI.Hierarchy.ProbeSiteAddress
import OAI.Hierarchy.TaggedShorterZero

namespace OAI
/-! # Ordinary scale-zero switches on the actual free links of the core -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open Computability.VPVNP.BurstRAM
open ThreeFlat Routing
open AdaptiveProbe TaggedShorterZero
open scoped Classical

variable {F : Type*} [CommRing F] {S : PurchaseSampler} {h d k address b w : ℕ}

def privateNames (f : Free S h d k) (fits : siteLast h d k+1≤2^address) :
    Bool → Fin 1 → Word address := fun side _ =>
  (siteNumber h d k (if side then (freeEnds f).2 else (freeEnds f).1)).castLE fits

/-- One candidate and one slot on each side implement a private link.
The pins contain the same global site ordinals used by the routed board. -/
def privateSwitch (f : Free S h d k) (fits : siteLast h d k+1≤2^address) (hw : w≤2^b) :=
  network (F:=F) (L:=1) (privateNames f fits) hw

theorem private_read (f : Free S h d k) (fits : siteLast h d k+1≤2^address) (hw : w≤2^b)
    (width : Fin 1 → Word b) (ends : Fin 1 → Bool → Word address)
    (data : Bool → Fin 1 → Fin w → Bool)
    (live : 0<(width 0).val → ∀side,ends 0 side=privateNames f fits side 0) :
    TypedWiring.value (privateSwitch (F:=F) f fits hw) (pins ends width data)=
      if ∀ j : Fin w,j.val<(width 0).val → data false 0 j=data true 0 j then 1 else 0 := by
  rw [privateSwitch,checks]
  congr 1
  apply propext
  constructor
  · intro ok j inside
    have use := live (by omega)
    exact ok 0 0 0 j (use false) (use true) inside
  · intro ok i s t j _ _ take
    have hi : i=0 := Subsingleton.elim ..
    have hs : s=0 := Subsingleton.elim ..
    have ht : t=0 := Subsingleton.elim ..
    subst i; subst s; subst t
    exact ok j take

theorem private_cells (f : Free S h d k) (fits : siteLast h d k+1≤2^address) (hw : w≤2^b) :
    (privateSwitch (F:=F) f fits hw).cells≤2*(100*address+100)+w*(100*b+100) := by
  simpa only [privateSwitch,Nat.mul_one,Nat.one_mul] using
    (cells (F:=F) (L:=1) (privateNames f fits) hw)

theorem private_price (f : Free S h d k) (fits : siteLast h d k+1≤2^address) (hw : w≤2^b) :
    let gate := privateSwitch (F:=F) f fits hw
    gate.cells+gate.internal ≤ 2+2*(2*(100*address+100)+w*(100*b+100)) := by
  intro gate
  have cells := private_cells (F:=F) f fits hw
  have hidden := internal (F:=F) (L:=1) (privateNames f fits) hw
  change gate.cells≤_ at cells
  change gate.internal≤2*1*1+gate.cells at hidden
  omega

end Hierarchy.ProbeStage.CoreBoard

end
end OAI
