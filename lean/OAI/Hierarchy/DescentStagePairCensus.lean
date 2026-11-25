import OAI.Hierarchy.DescentGroupStageData
import OAI.Hierarchy.DescentChosenOccupied

namespace OAI
/-! # The actual incoming live pairs fit the stage's block directory -/

namespace Hierarchy.DescentSixParty.GroupStage
open Computability.BorderVNP.Crossing DescentColonies StarKeys
open scoped BigOperators Classical
noncomputable section

variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable (A : GroupStage W G price ε J V k)

/-- Count an outgoing occurrence of every core wire before assigning its site
to a group and binary block. A loop is charged to its own source site as well. -/
theorem liveWidth_le_capacity :
    W.liveWidth≤(A.z*G.b)*((Fintype.card J*Fintype.card V*2^k)*A.cap) := by
  let units := W.siteUnits (fun u=>A.hub (A.pos u).2) A.records A.wire 256 A.hist
  let src := fun v : W.graph.Site=>∑e,if v=W.graph.src e then A.wire*W.graph.width e else 0
  have covered (v : W.graph.Site) : src v≤units v := by
    unfold src units MarkedWorld.siteUnits
    apply le_trans _ (Nat.le_add_right _ _)
    apply le_trans _ (Nat.le_add_right _ _)
    apply Finset.sum_le_sum
    intro e _
    by_cases atSource : v=W.graph.src e
    · simp only [ite_eq_left atSource]
      by_cases hub : A.hub (A.pos (W.graph.src e)).2 = true
      · rw [ite_eq_left hub]
        omega
      · rw [ite_eq_right hub, Nat.mul_one]
    · simp [atSource]
  have total : (∑v,src v)=∑e,A.wire*W.graph.width e := by
    unfold src
    rw [Finset.sum_comm]
    simp
  have live : W.liveWidth≤∑e,W.graph.width e :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  have paid : A.wire*W.liveWidth≤∑v,units v := calc
    _ ≤ A.wire*(∑e,W.graph.width e) := Nat.mul_le_mul_left _ live
    _ = ∑v,src v := by rw [total,Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun v _=>covered v
  have upper : (∑v,units v)≤A.wire*((A.z*G.b)*((Fintype.card J*Fintype.card V*2^k)*A.cap)) := by
    rw [←total_blockMass W.graph A.pos A.block units]
    calc
      _ ≤ ∑ _ : J×V,∑ _ : Block k,A.wire*(A.z*G.b)*A.cap :=
        Finset.sum_le_sum fun v _=>Finset.sum_le_sum fun i _=>A.small v i
      _ = _ := by simp [Block];ring
  exact Nat.le_of_mul_le_mul_left (paid.trans upper) A.wirePos

theorem live_pairs_le_capacity :
    W.liveWidth/(2*(A.z*G.b)) ≤ (Fintype.card J*Fintype.card V*2^k)*A.cap := by
  apply Nat.div_le_of_le_mul
  exact A.liveWidth_le_capacity.trans
    (Nat.mul_le_mul_right _ (show A.z*G.b≤2*(A.z*G.b) by omega))

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
