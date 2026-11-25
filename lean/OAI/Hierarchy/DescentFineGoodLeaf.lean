import OAI.Hierarchy.DescentFineRows
import OAI.Hierarchy.DescentResetPlacementPrice
import OAI.Hierarchy.DescentBadBundles

namespace OAI
/-! # An unmarked physical base is exactly one terminal leaf -/

namespace Hierarchy.DescentFineTerminals
open DescentColonies DescentGL DescentBaseProfile
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {k Δ f B K : ℕ}
variable (near : V→Finset V) (wt : V→Block k→ℕ) (room : ∀v x,wt v x≤B)
variable (traffic : V→V→Block k→ℝ) (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k)
local notation "nativeGap" => (32*Nat.clog 2 (2*Δ))
local notation "wtL" => rearrangedLoad wt L
local notation "roomL" => fun v i=>room v (Equiv.symm (rearrange L) i)

/-- The same true forced-key set that pays for excess load makes the refined
directory coincide with the base directory on every unmarked old item. -/
theorem unflagged_leaf (o : V×Block k)
    (good : baseOf b hk L o∉validBases b (resetKeys near Δ f B K wt traffic b hk L)) :
    leaf (D:=nativeGap) (f:=f) near wtL roomL b o.1 (rearrange L o.2)=b o.1 := by
  let x := rearrange L o.2
  apply max_eq_left
  by_contra! deep
  have exceeds := earlier_split wtL (fun v w=>w∈near v) nativeGap (f+1) B roomL o.1 x deep
  have marked : (o.1,group (b o.1) x)∈forced wtL (fun v w=>w∈near v) nativeGap (2*(2^f*B)) b := by
    apply Finset.mem_biUnion.mpr
    refine ⟨o.1,Finset.mem_univ _,Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩⟩
    convert exceeds using 1; ring
  apply good
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,Finset.mem_union_left _ ?_⟩
  simpa only [label,baseOf,layout_id,x] using marked

omit [Fintype V] [DecidableEq V] in
/-- The native smoothing exponent is below the spacing used by the two
physical exceptional trees, in either orientation of a host edge. -/
theorem smooth_for_terminals (branch : 0<Δ) (sym : ∀v w,w∈near v ↔ v∈near w)
    (smooth : ∀v w,w∈near v→b w≤b v+decayExponent Δ) :
    ∀v w,w∈near v→b v≤b w+nativeGap := by
  intro v w edge
  have old := smooth w v ((sym v w).mp edge)
  have bound := (decay_parameters branch).1
  omega

end
end Hierarchy.DescentFineTerminals

end OAI
