import OAI.Hierarchy.DescentMergedSiteLoad

namespace OAI
/-! # Charging the six newly recorded matrix atoms at each actual selected site -/

namespace Hierarchy.DescentSixParty.GadgetNetwork
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {D : ℕ} {P : Type*} {bits : P→ℕ} {I C : Type} [Fintype I]
variable (N : Network D P bits) (pick : I×Fin 2 ↪ N.Edge) (layout : Bool) (pack : N.Site→C)
local notation "site" => newSite N pick layout pack
local notation "loc" => (fun u : N.Site => site (Sum.inl u))

/-- Count exactly the retained matrix descriptions at a particular physical site. -/
def siteBirths (v : Merged N pick layout pack) :=
  Fintype.card {ij : I×Fin 6 // site (.inr ij)=v}

omit [Fintype I] in
private theorem landing (i : I) (j : Fin 6) :
    ∃s : Fin 2,touches N loc (site (.inr (i,j))) (pick (i,s)) := by
  have covers (l : Bool) (h : Fin 6) : (∃s,cluster l (demandSrc s)=cluster l h) ∨
      ∃s,cluster l (demandDst s)=cluster l h := by decide +revert
  rcases covers layout j with ⟨s,hs⟩|⟨s,hs⟩
  · exact ⟨s,Or.inl ((source_merge N pick layout pack i s).trans (Quot.sound (.privateWire i _ _ hs)))⟩
  · exact ⟨s,Or.inr ((target_merge N pick layout pack i s).trans (Quot.sound (.privateWire i _ _ hs)))⟩

set_option maxHeartbeats 800000 in
/-- Each of the six matrix atoms of a matched pair is covered by the bill of one of its
two actual picked cables. Different pairs have disjoint picked cables. -/
theorem siteBirths_paid (v : Merged N pick layout pack) (hist wireScale : ℕ)
    (enough : ∀ i s,6*hist≤wireScale*N.width (pick (i,s))) :
    siteBirths N pick layout pack v*hist ≤
      wireScale*(∑u : {u : N.Site // loc u=v},siteLoad N u.val) := by
  classical
  let atTarget (ij : I×Fin 6) := site (.inr ij)=v
  let charge (e : N.Edge) := wireScale*oldBill N loc v e
  have count : siteBirths N pick layout pack v*hist=∑ij : I×Fin 6,if atTarget ij then hist else 0 := by
    let s := Finset.univ.filter atTarget
    change Fintype.card (Subtype atTarget)*hist=_
    have card : Fintype.card (Subtype atTarget)=s.card :=
      Fintype.card_of_subtype s fun x =>
        ⟨fun hx => (Finset.mem_filter.mp hx).2,
          fun hx => Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    rw [card,←Finset.sum_filter]
    simp [s]
  have pair_bound (i : I) : (∑j : Fin 6,if atTarget (i,j) then hist else 0)≤∑s : Fin 2,charge (pick (i,s)) := by
    by_cases live : ∃j,atTarget (i,j)
    · obtain ⟨j,hj⟩ := live
      obtain ⟨s,touches⟩ := landing N pick layout pack i j
      change site (.inr (i,j))=v at hj
      rw [hj] at touches
      have six : (∑j : Fin 6,if atTarget (i,j) then hist else 0)≤6*hist := by
        calc
          _ ≤ ∑_j : Fin 6,hist := Finset.sum_le_sum fun j _=> by
            split <;> first | exact le_rfl | exact Nat.zero_le _
          _ = _ := by simp
      have edge : 6*hist≤charge (pick (i,s)) := by
        change 6*hist ≤ wireScale * oldBill N loc v (pick (i,s))
        rw [oldBill, ite_eq_left touches]
        exact enough i s
      exact six.trans (edge.trans (Finset.single_le_sum (f:=fun s=>charge (pick (i,s)))
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ s)))
    · have none (j : Fin 6) : ¬ atTarget (i,j) := fun hj => live ⟨j,hj⟩
      simp [none]
  have all : (∑t : I×Fin 2,charge (pick t))≤∑e : N.Edge,charge e := by
    have h := Finset.sum_le_sum_of_subset (f:=charge) (Finset.subset_univ (Finset.univ.map pick))
    simpa only [Finset.sum_map] using h
  calc
    _ = _ := count
    _ = ∑i,∑j,if atTarget (i,j) then hist else 0 :=
      Fintype.sum_prod_type (fun ij : I × Fin 6 => if atTarget ij then hist else 0)
    _ ≤ ∑i,∑s,charge (pick (i,s)) := Finset.sum_le_sum fun i _=>pair_bound i
    _ = ∑t : I×Fin 2,charge (pick t) := (Fintype.sum_prod_type (fun t => charge (pick t))).symm
    _ ≤ ∑e : N.Edge,charge e := all
    _ = wireScale*(∑e : N.Edge,oldBill N loc v e) := (Finset.mul_sum ..).symm
    _ ≤ _ := Nat.mul_le_mul_left _ (oldBill_le N loc v)

end
end Hierarchy.DescentSixParty.GadgetNetwork

end OAI
