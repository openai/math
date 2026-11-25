import OAI.Hierarchy.DescentExposedRoleFields
import OAI.Hierarchy.DescentFreshRoleHeaderData
import OAI.Hierarchy.DescentGadgetHistory

namespace OAI
/-! # Computing all six fresh scalar headers directly from the selected profile -/
namespace Hierarchy.DescentFreshRoleFields
open DescentBundleHistory DescentSixParty DescentKernelHistory Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F)
variable {P I : Type} [Fintype I] {d Z p : ℕ} {bits : P→ℕ} (N : Network d P bits)
    (pick : I×Fin 2↪N.Edge) (z : I→ℕ) (room : ∀i,z i≤Z) (a : I→Profile G.C)
    (fit : ∀i t,N.width (pick (i,t))=z i*G.b)
local notation "M" => GadgetNetwork.physical N pick (branchWidth G z a)
local notation "role" => roleRecipe G N pick z room a

include fit

theorem real_width (i : I) (j : Fin 6) (t : RolePort j) :
    boundaryWidth M (.inr (i,j)) (nativeRole N pick (branchWidth G z a) i j t)=width G (z i) (a i) j t := by
  rcases t with (t|t)|(t|t)
  · exact fit i t.val
  · exact fit i t.val
  · rfl
  · rfl

variable (hp : 0<p) (i : I) (j : Fin 6)
    (pub : ∀b,p∣boundaryWidth (GadgetNetwork.physical N pick (branchWidth G z a)) (.inr (i,j)) b)
    (priv : ∀h,p∣(roleRecipe G N pick z room a i j).width h)
local notation "s" => exposed (role i j) (boundaryWidth M (.inr (i,j))) hp pub priv


theorem real_header :
    (((s).recipe hp).tag ())=((⟨z i,Nat.lt_succ_of_le (room i)⟩,a i,j),header G p (z i) (a i) j) := by
  refine (fresh_tag hp (role i j) (boundaryWidth M (.inr (i,j))) pub priv ()).trans ?_
  apply congrArg (Prod.mk ((⟨z i,Nat.lt_succ_of_le (room i)⟩ : Fin (Z+1)),a i,j))
  apply congrArg List.ofFn
  funext t
  exact congrArg (fun n : ℕ => List.replicate (n/p) (⟨0,1,1⟩ : SliceCode))
    (real_width G N pick z a fit i j ((roleIndex j).symm t))

theorem real_arity : (((s).recipe hp).arity ())=arity G p (z i) (a i) j := by
  refine (fresh_arity hp (role i j) (boundaryWidth M (.inr (i,j))) pub priv ()).trans ?_
  apply Finset.sum_congr rfl
  intro t _
  exact congrArg (·/p) (real_width G N pick z a fit i j ((roleIndex j).symm t))

end
end Hierarchy.DescentFreshRoleFields

end OAI
