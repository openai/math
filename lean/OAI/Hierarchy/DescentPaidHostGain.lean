import OAI.Hierarchy.DescentHostDegree
import OAI.Hierarchy.DescentMergedSiteLoad

namespace OAI
/-! # Paying the local load of a physical contracted gadget at the chosen dyadic gain -/

namespace Hierarchy.DescentSixParty.GadgetNetwork

open Computability.BorderVNP.Crossing DescentHostDegree
open scoped BigOperators Classical
noncomputable section

variable {D d : ℕ} {P : Type*} {bits : P → ℕ} {I C : Type} [Fintype I]
variable (N : Network D P bits) (pick : I × Fin 2 ↪ N.Edge) (layout : Bool) (pack : N.Site→C)
variable (pos : Merged N pick layout pack→EuclideanSpace ℝ (Fin d)) (hpos : ∀c,‖pos c‖≤1)
variable (v : Merged N pick layout pack)
local notation "Fiber" => {u : N.Site // newSite N pick layout pack (Sum.inl u) = v}

/-- Old sites in a given quotient fiber may include multiple original block
positions per pack. Each pack's full load is counted just once. -/
theorem fiber_load {U C : Type*} [Fintype U] (loc : U → Prop) (name : U → C)
    (pay : U → ℕ) (roster : Finset C) (cap : ℕ) (covered : ∀u,loc u→name u∈roster)
    (paid : ∀p∈roster, (∑u, if name u=p then pay u else 0) ≤ cap) :
    (∑u : {u // loc u}, pay u.val) ≤ roster.card*cap := by
  classical
  let used := Finset.univ.filter loc
  rw [←Finset.sum_subtype used (fun u => by simp [used]) pay]
  calc
    _ = ∑u∈used,∑p∈roster,if name u=p then pay u else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      have present := covered u (Finset.mem_filter.mp hu).2
      simp [present]
    _ = ∑p∈roster,∑u∈used,if name u=p then pay u else 0 := Finset.sum_comm
    _ ≤ ∑ _∈roster,cap := Finset.sum_le_sum fun p hp =>
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ used) (fun _ _ _ => Nat.zero_le _)).trans (paid p hp)
    _ = _ := by simp

/-- The old site descriptions carry forward additively. The actual surviving
physical wires use the universal factor five at the same old fiber. -/
theorem paid_host_gain {F : Type*} [Field F] (G : PoweredGadget F) (z : I→ℕ)
    (p : I→Profile G.C) (fit : ∀i s,N.width (pick (i,s))=z i*G.b)
    (carried : N.Site→ℕ) (roster : Finset C) (a₀ Δ B : ℕ)
    (covered : ∀u,newSite N pick layout pack (.inl u)=v → pack u∈roster)
    (count : roster.card≤1+allowedSources Δ*(2^packExponent a₀ Δ+1))
    (paid : ∀c∈roster,(∑u : N.Site,if pack u=c then siteLoad N u+carried u else 0)≤2^packExponent a₀ Δ*B) :
    let w := fun i e => z i*(((p i).1 e).val+G.k)
    2*(siteLoad (merged N pick w layout pack pos hpos) v+(∑u : Fiber,carried u.val))≤
      2^gainExponent a₀ Δ*B := by
  classical
  dsimp only
  have wires := merged_site_load_five N pick layout pack pos hpos v G z p fit
  let old := ∑u : Fiber,siteLoad N u.val
  let info := ∑u : Fiber,carried u.val
  have loads : old+info ≤ roster.card*(2^packExponent a₀ Δ*B) := by
    simpa only [Finset.sum_add_distrib,old,info] using (fiber_load
      (fun u=>newSite N pick layout pack (.inl u)=v) pack (fun u=>siteLoad N u+carried u)
      roster (2^packExponent a₀ Δ*B) covered paid)
  have total := loads.trans (Nat.mul_le_mul_right _ count)
  have prior : siteLoad (merged N pick (fun i e=>z i*(((p i).1 e).val+G.k)) layout pack pos hpos) v+
      info≤5*(old+info) := by change _≤5*old at wires;omega
  exact ((Nat.mul_le_mul_left 2 prior).trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 5 total))).trans
    (by simpa only [Nat.mul_assoc] using gain_covers a₀ Δ B)

end
end Hierarchy.DescentSixParty.GadgetNetwork

end OAI
