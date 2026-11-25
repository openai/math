import OAI.Hierarchy.ProbeStageChains
import OAI.Hierarchy.ProbeBalls

namespace OAI
/-! # Bounded physical test neighborhoods on the routed partial matching -/

namespace Hierarchy.ProbeStage.Tiles
open AdaptiveProbe
open scoped Classical
noncomputable section

variable {R G : Type*} [Fintype R] [DecidableEq R] [DecidableEq G] {m : ℕ}

/-- With the group fixed, input and output sockets remain separate even when their
numeric ranks happen to coincide. The adjacency records every actual tile and every
sampler join, including joins whose opposite socket is unoccupied. -/
def incoming (stage : Tiles R G m) (g : G) (j : Fin m) : Finset R :=
  Finset.univ.filter fun r => stage.group r=g ∧ stage.input r=j

def outgoing (stage : Tiles R G m) (g : G) (j : Fin m) : Finset R :=
  Finset.univ.filter fun r => stage.group r=g ∧ stage.output r=j

def localNext (stage : Tiles R G m) (g : G) (next : Fin m → List (Fin m)) :
    (Fin m ⊕ Fin m) → Finset (Fin m ⊕ Fin m)
  | .inl i => (((incoming stage g i).image stage.output) ∪
      (Finset.univ.filter fun o => i ∈ next o)).image Sum.inr
  | .inr o => (((outgoing stage g o).image stage.input) ∪ (next o).toFinset).image Sum.inl

omit [DecidableEq R] in
theorem ports_degree (stage : Tiles R G m) (g : G) (next : Fin m → List (Fin m))
    (D : ℕ) (left : ∀ i, (Finset.univ.filter fun o => i ∈ next o).card ≤ D)
    (right : ∀ o, (next o).length ≤ D) (v : Fin m ⊕ Fin m) :
    (localNext stage g next v).card ≤ D+1 := by
  classical
  cases v with
  | inl j =>
    have small : (incoming stage g j).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨ga,ea⟩ := (Finset.mem_filter.mp ha).2
      obtain ⟨gb,eb⟩ := (Finset.mem_filter.mp hb).2
      exact stage.input_inj (Prod.ext (ga.trans gb.symm) (ea.trans eb.symm))
    apply Finset.card_image_le.trans
    apply (Finset.card_union_le _ _).trans
    exact (Nat.add_le_add (Finset.card_image_le.trans small) (left j)).trans_eq (Nat.add_comm 1 D)
  | inr j =>
    have small : (outgoing stage g j).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      obtain ⟨ga,ea⟩ := (Finset.mem_filter.mp ha).2
      obtain ⟨gb,eb⟩ := (Finset.mem_filter.mp hb).2
      exact stage.output_inj (Prod.ext (ga.trans gb.symm) (ea.trans eb.symm))
    apply Finset.card_image_le.trans
    apply (Finset.card_union_le _ _).trans
    exact (Nat.add_le_add (Finset.card_image_le.trans small)
      ((List.toFinset_card_le _).trans (right j))).trans_eq (Nat.add_comm 1 D)

omit [DecidableEq R] in
theorem across (stage : Tiles R G m) (g : G) (next : Fin m → List (Fin m)) (i o : Fin m) :
    Sum.inr o ∈ localNext stage g next (.inl i) ↔
      (∃ r, stage.group r=g ∧ stage.input r=i ∧ stage.output r=o) ∨ i ∈ next o := by
  classical
  simp [localNext,incoming,and_assoc]

omit [DecidableEq R] in
theorem back (stage : Tiles R G m) (g : G) (next : Fin m → List (Fin m)) (i o : Fin m) :
    Sum.inl i ∈ localNext stage g next (.inr o) ↔
      (∃ r, stage.group r=g ∧ stage.input r=i ∧ stage.output r=o) ∨ i ∈ next o := by
  classical
  simp [localNext,outgoing,and_left_comm,and_comm]

omit [DecidableEq R] in
theorem ports_symmetric (stage : Tiles R G m) (g : G) (next : Fin m → List (Fin m))
    (x y : Fin m ⊕ Fin m) : x ∈ localNext stage g next y → y ∈ localNext stage g next x := by
  cases x with
  | inl i =>
    cases y with
    | inl j => simp [localNext]
    | inr o => exact ((across stage g next i o).trans (back stage g next i o).symm).mpr
  | inr o =>
    cases y with
    | inl i => exact ((across stage g next i o).trans (back stage g next i o).symm).mp
    | inr j => simp [localNext]

end
end Hierarchy.ProbeStage.Tiles

end OAI
