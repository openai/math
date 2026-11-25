import OAI.Hierarchy.DescentNetworkSubstitution

namespace OAI
/-! # Exact degree at every site after substituting open networks -/

namespace Hierarchy.DescentNetworkSubstitution
open Computability.BorderVNP.Crossing
open scoped BigOperators Classical
noncomputable section

variable {D d : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable (M : (v : N.Site) → Network d (Slot N v) (slotWidth N v))
local notation "Q" => network N M

private abbrev Flag (A : Network D P bits) := P ⊕ (A.Edge × Bool)
private def owner (A : Network D P bits) : Flag A → A.Site :=
  Sum.elim A.attach (fun eb => if eb.2 then A.dst eb.1 else A.src eb.1)

/-- The exterior port and the two ends of every joining cable are the three kinds of gadget slots. -/
private def flags : Flag Q ≃ Σ v : N.Site, Flag (M v) where
  toFun
    | .inl p => ⟨N.attach p, .inl (.inr (.inr ⟨p,rfl⟩))⟩
    | .inr (.inl e, false) => ⟨N.src e, .inl (.inl ⟨e,rfl⟩)⟩
    | .inr (.inl e, true) => ⟨N.dst e, .inl (.inr (.inl ⟨e,rfl⟩))⟩
    | .inr (.inr ⟨v,e⟩, b) => ⟨v,.inr (e,b)⟩
  invFun
    | ⟨_, .inl (.inl e)⟩ => .inr (.inl e.val,false)
    | ⟨_, .inl (.inr (.inl e))⟩ => .inr (.inl e.val,true)
    | ⟨_, .inl (.inr (.inr p))⟩ => .inl p.val
    | ⟨v, .inr (e,b)⟩ => .inr (.inr ⟨v,e⟩,b)
  left_inv t := by
    rcases t with p | ⟨e | ⟨v,e⟩, b⟩
    · rfl
    · cases b <;> rfl
    · rfl
  right_inv t := by
    rcases t with ⟨v, (s | ⟨e,b⟩)⟩
    · rcases s with ⟨e,rfl⟩ | (⟨e,rfl⟩ | ⟨p,rfl⟩) <;> rfl
    · rfl

private theorem owner_flags (t : Flag Q) : owner Q t =
    ⟨(flags N M t).1, owner (M _) (flags N M t).2⟩ := by
  rcases t with p | ⟨e | ⟨v,e⟩, b⟩
  · rfl
  · cases b <;> rfl
  · cases b <;> rfl

private theorem degree_sum [Fintype P] (A : Network D P bits) (u : A.Site) :
    A.bitDegree u = ∑ t : Flag A, if owner A t = u then 1 else 0 := by
  simp only [Network.bitDegree,Finset.card_filter,owner]
  apply Finset.sum_congr rfl
  intro t _
  split <;> rename_i test <;> simp_all

/-- Degrees count both ends of every loop. Substitution preserves the full gadget-site degree. -/
theorem degree [Fintype P] (v : N.Site) (j : (M v).Site) :
    (Q).bitDegree ⟨v,j⟩ = (M v).bitDegree j := by
  classical
  rw [degree_sum, degree_sum]
  let count (z : Σ u : N.Site, Flag (M u)) : ℕ := if (⟨z.1,owner (M z.1) z.2⟩ : Site N M) = ⟨v,j⟩ then 1 else 0
  calc
    _ = ∑ z, count z := Fintype.sum_equiv (flags N M) _ _ fun t => by
      dsimp only [count]
      rw [owner_flags]
      split <;> rename_i test <;> simp_all
    _ = _ := by
      rw [Fintype.sum_sigma, Finset.sum_eq_single v]
      · simp [count]
      · intro u _ ne
        apply Finset.sum_eq_zero
        intro s _
        exact ite_eq_right fun h => ne (congrArg Sigma.fst h)
      · simp

/-- An external flag carries its named pin width, and either end of an internal cable carries
that cable's full physical width. -/
private def flagWidth (A : Network D P bits) : Flag A → ℕ :=
  Sum.elim bits (fun eb => A.width eb.1)

/-- Local physical bit load, counting both incidences of a loop. -/
def portLoad [Fintype P] (A : Network D P bits) (u : A.Site) : ℕ :=
  ∑ t : Flag A, if owner A t=u then flagWidth A t else 0

theorem portLoad_eq [Fintype P] (A : Network D P bits) (u : A.Site) :
    portLoad A u = (∑p,if A.attach p=u then bits p else 0) +
      (∑e,if A.src e=u then A.width e else 0) + (∑e,if A.dst e=u then A.width e else 0) := by
  unfold portLoad
  rw [Fintype.sum_sum_type,Fintype.sum_prod_type]
  simp [flagWidth,owner,Finset.sum_add_distrib,add_assoc,add_comm]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hit : A.attach p=u <;> simp [hit]

/-- The width of any particular incident wire is included on its physical side of the site. -/
theorem cable_width_le_portLoad [Fintype P] (A : Network D P bits) (u : A.Site) (e : A.Edge)
    (hit : A.src e=u ∨ A.dst e=u) : A.width e≤portLoad A u := by
  rw [portLoad_eq]
  rcases hit with h|h
  · have one:=Finset.single_le_sum (s:=Finset.univ) (f:=fun t=>if A.src t=u then A.width t else 0)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ e)
    rw [ite_eq_left h] at one
    omega
  · have one:=Finset.single_le_sum (s:=Finset.univ) (f:=fun t=>if A.dst t=u then A.width t else 0)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ e)
    rw [ite_eq_left h] at one
    omega

/-- Only widths of ports and cable ends actually incident to this site consume its allowance. -/
theorem portLoad_le_of_incident [Fintype P] (A : Network D P bits) (u : A.Site) (bound : ℕ)
    (pin : ∀p,A.attach p=u→bits p≤bound) (src : ∀e,A.src e=u→A.width e≤bound)
    (dst : ∀e,A.dst e=u→A.width e≤bound) : portLoad A u ≤ A.bitDegree u*bound := by
  rw [degree_sum,Finset.sum_mul]
  unfold portLoad
  apply Finset.sum_le_sum
  intro t _
  by_cases h : owner A t=u
  · simp only [h,ite_true,one_mul]
    rcases t with p | ⟨e,b⟩
    · exact pin p h
    · cases b
      · exact src e h
      · exact dst e h
  · simp [h]

theorem portLoad_le_of_widths [Fintype P] (A : Network D P bits) (u : A.Site) (bound : ℕ)
    (pin : ∀p,bits p≤bound) (edge : ∀e,A.width e≤bound) : portLoad A u≤A.bitDegree u*bound :=
  portLoad_le_of_incident A u bound (fun p _=>pin p) (fun e _=>edge e) (fun e _=>edge e)

private theorem width_flags (t : Flag Q) : flagWidth Q t=flagWidth (M _) (flags N M t).2 := by
  rcases t with p | ⟨e | ⟨v,e⟩,b⟩
  · rfl
  · cases b <;> rfl
  · rfl

/-- Each gadget site keeps the exact physical width of its incident slots and private cables. -/
theorem portLoad_substitute [Fintype P] (v : N.Site) (j : (M v).Site) :
    portLoad Q ⟨v,j⟩=portLoad (M v) j := by
  classical
  let cost (z : Σ u : N.Site,Flag (M u)) := if (⟨z.1,owner (M z.1) z.2⟩ : Site N M)=⟨v,j⟩
    then flagWidth (M z.1) z.2 else 0
  unfold portLoad
  calc
    _ = ∑ z,cost z := Fintype.sum_equiv (flags N M) _ _ fun t => by
      dsimp only [cost]
      rw [owner_flags,width_flags]
      split <;> rename_i test <;> simp_all
    _ = _ := by
      rw [Fintype.sum_sigma,Finset.sum_eq_single v]
      · simp [cost]
      · intro u _ ne
        apply Finset.sum_eq_zero
        intro s _
        exact ite_eq_right fun h => ne (congrArg Sigma.fst h)
      · simp

end
end Hierarchy.DescentNetworkSubstitution

end OAI
