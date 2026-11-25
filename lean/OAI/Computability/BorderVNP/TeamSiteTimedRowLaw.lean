import OAI.Computability.BorderVNP.TeamSiteTimedRowCoverage
import OAI.Computability.BorderVNP.TeamSiteTimedRowLive
import OAI.Computability.BorderVNP.TeamSiteTimedRowHalt

/-! # The timed processor realizes the complete signed endpoint relation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor.Row

open VPVNP RAMTape BurstRAM TeamTapeHandoff TeamLocalClock
open RAMTape.PublicExprMachine
variable {Q Γ : Type} {p r k a m g n d e w : ℕ} {P : TeamOpcode.Program p r k a}
variable {lib : Fin a → Macro Q Γ m g} {mark : Fin a → Γ}
variable (X : Site P lib mark n d e w)
local notation "N" => X.raw.length^25

private theorem cast_model {bits sg pass pass' T T'} (model : Model X bits sg pass T) (eq : pass ↔ pass') (le : T ≤ T') :
    Model X bits sg pass' T' := by
  obtain rfl := propext eq
  obtain ⟨t,ht,q,out,b,rest⟩ := model
  exact ⟨t,ht.trans_le le,q,out,b,rest⟩

/-- The finite physical processor replays every source endpoint on its exact choice
word, starting with its true private timer and checking the entire outgoing frame
and sorter data. -/
theorem forward_all : forward X N := by
  intro es out cert
  unfold Endpoint at cert
  cases hf : X.frame with
  | live word regs elapsed =>
    rw [hf] at cert
    obtain ⟨ok,pc,z,fin,hpc,chunk,finish⟩ := cert
    subst word
    let s : TeamOpcode.State w p r := ⟨pc,regs⟩
    rcases finish with ⟨guard,rfl⟩ | ⟨guard,rfl⟩
    · exact live_model X s z elapsed hf ok es fin none chunk (Or.inl ⟨rfl,congrArg Prod.fst guard⟩)
    · exact live_model X s z elapsed hf ok es fin (some z.pc) chunk (Or.inr ⟨rfl,congrArg Prod.fst guard⟩)
  | accepted elapsed =>
    rw [hf] at cert
    obtain ⟨rfl,safe,rfl⟩ := cert
    apply cast_model X (halted_model X elapsed hf)
    · cases h : X.last <;> simp [TeamSite.Endpoint.haltValid,Processor.Row.Context.guard,h,safe,Frame.halted]
    · unfold budget Processor.Row.Context.cost Processor.Budget.endpoint
      omega

/-- Both directions of the complete physical timed row model hold on arbitrary
raw private data with the timer constructed from the actual site input. -/
theorem models (distinct : ∀ j, (lib j).alphabet.blank ≠ mark j) :
    forward X N ∧ supplied X N :=
  ⟨forward_all X,supplied_of_forward X distinct (forward_all X)⟩

end TeamSite.TimedProcessor.Row

end BorderVNP
end Computability
end OAI
