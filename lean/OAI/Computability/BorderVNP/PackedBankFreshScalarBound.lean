import OAI.Computability.BorderVNP.PackedBankTerminalScalarBound
import OAI.Computability.BorderVNP.PackedBankPaidScalarBound
import OAI.Computability.BorderVNP.PackedBankRoundSites

/-! # A common numerical word bound at every actual birth in a crossing round -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.CombiningStep Shortening.SeedIntervals Shortening.StaticRows InheritedProfile
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- The fixed identity determines the coefficient, and the numerical birth
bound grows linearly in the expanded tile load and the old bin population. -/
theorem birthScalarLimit_le (M B : ℕ) :
    birthScalarLimit e M B ≤ (birthWordCoefficient e + 8)*(BankCharges.bound e+1)*(M+B+1) := by
  unfold birthScalarLimit birthCapacity
  ring_nf
  omega

/-- The count of any old bin fits the public old edge count times its largest
width, including all the live old cables when empty rows are retained. -/
theorem population_le_edge_budget {P : Type*} {S : Type} {bits : P → ℕ} (N : Network D P bits)
    (bin : N.Edge → Option S) (a : S) {E W : ℕ}
    (he : Fintype.card N.Edge ≤ E) (hw : ∀ i, N.width i ≤ W) : count N bin a ≤ E*W := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (f := N.width) (g := fun _ => W) (fun i _ => hw i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
  exact (population_le_total N bin a).trans (hs.trans (Nat.mul_le_mul_right W he))

variable [NeZero D] {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
    (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    {T : Type*} (tile : (output e p bin perm positive first q).layout.Site → T) (prior payload : p.layout.Site → ℕ)
    (M : ℕ) (cap : BirthTileCap e p bin perm positive first q tile prior payload M) (hm : 0 < m)
    (a : S) {ns ne np : ℕ} (siteID : (output e p bin perm positive first q).layout.Site ↪ Fin ns)
    (edgeID : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (binName : S → ℕ) (position : e.Entry → ℕ) (B : ℕ) (pool : ∀ s, count p.layout bin s ≤ B)

include cap hm pool in
/-- The concrete replay can use a single uniform scalar bound on the origin,
every terminal and every paid site actually inserted by the round. -/
theorem roundSites_fresh_scalarBound (old : p.layout.Site → Site) (cuts : p.layout.Site → List Slice)
    (v : TemplateSite e) :
    (roundSites e p bin perm positive first q binName position siteID edgeID portID old cuts (.inr ⟨a,v⟩)).ScalarBound
      (birthScalarLimit e M B) := by
  rcases v with _ | t | ⟨i,v⟩
  · exact origin_scalarBound e p bin perm positive first q tile prior payload M cap hm a siteID edgeID portID B
  · exact terminal_scalarBound e p bin perm positive first q tile prior payload M cap a siteID edgeID portID binName B pool hm t
  · exact paid_scalarBound e p bin perm positive first q tile prior payload M cap hm a i v edgeID portID position B

end Packing.Inherited

end BorderVNP
end Computability
end OAI
