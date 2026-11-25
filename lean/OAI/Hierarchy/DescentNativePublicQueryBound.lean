import OAI.Hierarchy.DescentPrivateTreeEdgeBudget
import OAI.Hierarchy.DescentFallbackMixedQueryBound
import OAI.Hierarchy.DescentResetRosterFunctions

namespace OAI
/-! # Signed public query room for the physical fallback and rotor menu -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentResetLocalRoster DescentResetCableSlots DescentPrivateTreeTemplate DescentSIMDLookup
noncomputable section
set_option quotPrecheck false
variable {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (D k cap Ht bits query lanes grains args nodes packet gain mult payload : ℕ)
local notation "cfg" => publicMenu board D k cap Ht bits query lanes grains args nodes packet gain mult payload
local notation "F₀" => (cfg).oldConfig

/-- Empty physical rows issue query zero. On live rows the loaded capacity and the
publicly allocated tree height bound the entire directory, including padded rows. -/
theorem public_query_room (x : (cfg).Data n) (j : Fin (F₀).mouths)
    (earned : ((F₀).header ((cfg).basic x) 0).val≠0 →
      (((cfg).reg x) 0).val=cap) :
    ((cfg).column board query none j x).val≤2*publicSlots board Ht k cap :=by
  classical
  by_cases blank : ((F₀).header ((cfg).basic x) 0).val=0
  · simp [DescentResetPublicOperandBook.Config.column,DescentResetPublicOperandBook.Config.mixed,blank]
  have capacity:=earned blank
  have slots_ : ∀t≤Ht,Fintype.card (Edge t)≤cableCap board Ht :=by
    intro t small
    exact (edge_bound t).trans ((Nat.pow_le_pow_right (by decide : 0<2) (Nat.add_le_add_right small 1)).trans (Nat.le_max_right _ _))
  have positive : 0<cableCap board Ht :=(Nat.two_pow_pos _).trans_le (Nat.le_max_right _ _)
  have read:=(cfg).column_query_bound board query j x rfl (Nat.le_refl _) (le_of_eq capacity.symm) positive slots_
  rw [capacity] at read
  exact read

end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
