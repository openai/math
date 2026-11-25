import OAI.Hierarchy.DescentOrdinaryPriorRetileRate
import OAI.Hierarchy.DescentOrdinaryRoleRetileRate
import OAI.Hierarchy.DescentRetileWordVolume

namespace OAI
/-! # Both true argument-entry retile programs, measured on their unequal physical pitches -/
namespace Hierarchy
open DescentSIMDLookup DescentStaticWordColumn
namespace DescentOrdinaryPriorRetile
noncomputable section
variable (l : DescentDatedPriorOperand.Layout) (lanes base prior w h ratio u₀ u₁ : ℕ)

theorem word_bill (old : 0<l.lanes) (new : 0<lanes) (live : 0<l.hosts)
    (inCap : l.lanes≤h) (outCap : lanes≤h) (short : digits l*l.lanes≤h/2)
    (inFill : h≤l.lanes*u₀) (outFill : h≤lanes*u₁) (bus : w≤ratio*h) :
    let p:=phase l lanes base prior w
    (p.ticks+7*names p.program)*w≤
      4096*ratio*(pages l+1)*(h+3*l.hosts*h+l.hosts*l.groups*(2*u₀+u₁))+
      (4096*ratio)*(2*(h+1)^2*2^(h/2))*h :=
  Overlap.page_word_bill l.hosts l.groups l.lanes lanes (digits l) (pages l) h w ratio u₀ u₁ _ live inCap outCap short inFill outFill bus (shared_fee l lanes base prior w old new)
end
end DescentOrdinaryPriorRetile

namespace DescentOrdinaryRoleRetile.Layout
noncomputable section
variable (L : Layout) (base : ℕ) (prior : Fin L.blocks→ProtocolRAM.Bank) (w h ratio u₀ u₁ : ℕ)
theorem word_bill (old : 0<L.beforeLanes) (new : 0<L.afterLanes) (live : 0<L.hosts)
    (inCap : L.beforeLanes≤h) (outCap : L.afterLanes≤h) (short : L.bits*L.beforeLanes≤h/2)
    (inFill : h≤L.beforeLanes*u₀) (outFill : h≤L.afterLanes*u₁) (bus : w≤ratio*h) :
    let p:=L.phase base prior w
    (p.ticks+7*names p.program)*w≤
      4096*ratio*(L.blocks+1)*(h+3*L.hosts*h+L.hosts*L.groups*(2*u₀+u₁))+
      (4096*ratio)*(2*(h+1)^2*2^(h/2))*h :=
  Overlap.page_word_bill L.hosts L.groups L.beforeLanes L.afterLanes L.bits L.blocks h w ratio u₀ u₁ _ live inCap outCap short inFill outFill bus (shared_fee L base prior w old new)
end
end DescentOrdinaryRoleRetile.Layout
end Hierarchy

end OAI
