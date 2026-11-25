import OAI.Hierarchy.DescentOrdinaryPriorPadPrice
import OAI.Hierarchy.DescentOrdinaryArgumentRetilePrice
import OAI.Hierarchy.DescentNativePhaseInvoice

namespace OAI
/-! # Retiling the previous argument image with different source and destination host counts -/
namespace Hierarchy.DescentOrdinaryPriorPad
open DescentSixParty.Chronology DescentDatedPriorOperand DescentSIMDLookup DescentDatedSeedStartup
open DescentStaticWordColumn
noncomputable section
variable (l : Layout) (currentH lanes base prior w h ratio u₀ u₁ : ℕ)

theorem padded_word_bill (old : 0<l.lanes) (new_ : 0<lanes) (live : 0<l.hosts)
    (inCap : l.lanes≤h) (outCap : lanes≤h) (short : DescentOrdinaryPriorRetile.digits l*l.lanes≤h/2)
    (inFill : h≤l.lanes*u₀) (outFill : h≤lanes*u₁) (bus : w≤ratio*h) :
    let pages:=DescentOrdinaryPriorRetile.pages l
    (phase l currentH lanes base prior w).wordInvoice≤
      4096*ratio*(pages+1)*(h+3*l.hosts*h+l.hosts*l.groups*(2*u₀+u₁))+
      (4096*ratio)*(2*(h+1)^2*2^(h/2))*h+
      512*ratio*(pages+1)*(h+currentH*h+currentH*l.groups*u₁) :=by
  intro count
  have before:=DescentOrdinaryPriorRetile.word_bill l lanes base prior w h ratio u₀ u₁
    old new_ live inCap outCap short inFill outFill bus
  have ext:=extension_fee l currentH lanes base w
  have rounded:=chunk_work currentH l.groups lanes h u₁ outFill
  have copy : (extension l currentH lanes base w).wordInvoice≤512*ratio*(count+1)*(h+currentH*h+currentH*l.groups*u₁) :=by
    refine (Nat.mul_le_mul ext bus).trans ?_
    calc
      _=512*ratio*(count+1)*(h+(currentH*chunks l.groups lanes)*h) :=by unfold rows;ring
      _≤_ :=by rw [Nat.add_assoc h];gcongr
  exact (NativePhase.wordInvoice_seq ..).le.trans (Nat.add_le_add before copy)

end
end Hierarchy.DescentOrdinaryPriorPad

end OAI
