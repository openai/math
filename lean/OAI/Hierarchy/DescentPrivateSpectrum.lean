import OAI.Hierarchy.DescentLivePrivateWords
import OAI.Hierarchy.DescentBundleTerminal
import OAI.Hierarchy.ProtocolStackContraction

namespace OAI
/-! # Exact cancellation of idle words and one binary multiplicity menu for the whole terminal graph -/

namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {K U P : Type} [Field K] {p D : ℕ} {bits : P→ℕ}
variable (hp : 0<p) (N : Network D P bits) (scalar : U→List (List Bool)→K)
    (r : SiteBits (U:=U) N) (t : N.Tables K) (valid : ReadsBits N scalar r t) (s : ∀v,Shape p (r v))
local notation "row" => fun v=>Shape.recipe hp (s v)

/-- The integer exponent comes from the difference between the physical private word ledger
and the number of distinct local addresses actually read. -/
theorem dead_exponent (v : N.Site) :
    (row v).deadBits=((Fintype.card (Private (r v) p))-Fintype.card (row v).UsedWord)*p := by
  change (∑_ : (row v).DeadWord,p)=_
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 1
  exact Fintype.card_subtype_compl (row v).Used

include valid in
theorem restricted_product (a : N.Assignment) (x : Ports bits) :
    (∏v,N.read t a x v)=
      (2:K)^(∑v,(row v).deadBits)*
      ∏v,(row v).restricted.value (bundleScalar p scalar)
        (fun b=>wordList (fun j=>bitInput N a x v (b.atBit j))) := by
  rw [←Finset.prod_pow_eq_pow_sum,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  rw [←site_read hp N scalar r t valid s v a x]
  exact (row v).factor_value _ _

include valid in
/-- One public menu of binary powers suffices for all sites, including idle private bits
over a field of characteristic two. -/
theorem fixed_powers (a : N.Assignment) (x : Ports bits) (n : ℕ)
    (fit : (∑v,(row v).deadBits)<2^n) :
    (∏v,N.read t a x v)=
    (∏j : Fin n,if (∑v,(row v).deadBits).testBit j.val then (2:K)^(2^j.val) else 1)*
      ∏v,(row v).restricted.value (bundleScalar p scalar)
        (fun b=>wordList (fun j=>bitInput N a x v (b.atBit j))) := by
  rw [←ProtocolStackContraction.power_bits (2:K) _ n fit]
  exact restricted_product hp N scalar r t valid s a x

end
end Hierarchy.DescentBundleHistory

end OAI
