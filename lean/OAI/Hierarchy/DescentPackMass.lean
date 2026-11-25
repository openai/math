import OAI.Hierarchy.DescentStageMeasures
import OAI.Hierarchy.DescentColoredHost

namespace OAI
/-! # The full local load of every native pre-layout pack -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentPacking DescentHostDirectory DescentColonies
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {k d : ℕ} {P : Type*} {bits : P→ℕ}
variable (N : Network d P bits) (pos : N.Site → V) (block : N.Site → Block k) (full : N.Site → ℕ)

variable (near : V → Finset V) (D a B : ℕ) (small : ∀v x,blockMass N pos block full v x≤B)

abbrev occupiedHome := colonyOf N B near D a (blockMass N pos block full) small pos block

omit [Fintype V] in
/-- Every occupied-group fiber lies inside its actual first-unsplit dyadic
interval, measured using the complete input load including information bits. -/
theorem occupied_mass (c : occupied N B near D a (blockMass N pos block full) small pos block) :
    ∑u ∈ Finset.univ.filter (fun u : N.Site => occupiedHome N pos block full near D a B small u=c),full u≤
      2^a*B := by
  obtain ⟨w,hw⟩ := colonyOf_surjective N B near D a (blockMass N pos block full) small pos block c
  let load := blockMass N pos block full
  let v := pos w
  let x := block w
  let level := depthAt B near D a load small v x
  have subset : ∀u : N.Site,occupiedHome N pos block full near D a B small u=c →
      pos u=v ∧ block u∈interval level x := by
    intro u h
    have id : colonyCode N B near D a load small pos block u=
        colonyCode N B near D a load small pos block w := by
      calc
        _ = occupiedAddress N B near D a load small pos block
            (colonyOf N B near D a load small pos block u) :=
          (occupiedAddress_colonyOf N B near D a load small pos block u).symm
        _ = _ := (congrArg (occupiedAddress N B near D a load small pos block)
          (h.trans hw.symm)).trans (occupiedAddress_colonyOf N B near D a load small pos block w)
    have vh := congrArg Prod.fst id
    have dh := congrArg (fun p : V×(ℕ×ℕ) => p.2.1) id
    have ih := congrArg (fun p : V×(ℕ×ℕ) => p.2.2) id
    change pos u=v at vh
    change depthAt B near D a load small (pos u) (block u)=level at dh
    change group (depthAt B near D a load small (pos u) (block u)) (block u)=group level x at ih
    rw [dh] at ih
    exact ⟨vh,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ih⟩⟩
  apply le_trans _ (leaf_load load (fun p q=>q∈near p) D a B small v x)
  change _ ≤ ∑t∈interval level x,∑u : N.Site,if pos u=v ∧ block u=t then full u else 0
  rw [Finset.sum_comm,Finset.sum_filter]
  apply Finset.sum_le_sum
  intro u _
  by_cases atC : occupiedHome N pos block full near D a B small u=c
  · obtain ⟨pv,inRange⟩ := subset u atC
    simp [atC,pv,inRange,eq_comm]
  · simp [atC]

/-- Recover each pack's own colony from its address before any star merging. -/
def packColony {C : Type} {slot : C→Type} : C ⊕ (Σ c,slot c) → C
  | .inl c => c
  | .inr t => t.1

theorem pack_home {C : Type} [Fintype C] [DecidableEq C] (group : N.Site→C)
    (color : N.Site→Bool) (core : Finset N.Edge) (u : N.Site) :
    packColony (coloredPack N core group color B u)=group u := by
  unfold coloredPack packLabel
  split <;> rfl

omit [Fintype V] in
theorem full_pack_mass (color : N.Site→Bool) (core : Finset N.Edge) (p) :
    ∑u ∈ Finset.univ.filter (fun u : N.Site =>
      coloredPack N core (occupiedHome N pos block full near D a B small) color B u=p),full u≤2^a*B := by
  apply le_trans _ (occupied_mass N pos block full near D a B small (packColony p))
  apply Finset.sum_le_sum_of_subset
  intro u h
  have eqn := (Finset.mem_filter.mp h).2
  apply Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  exact (pack_home N B _ color core u).symm.trans (congrArg packColony eqn)

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
