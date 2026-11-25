import OAI.Computability.BorderVNP.PackedSubdivisionRelay

/-! # Exact input and fiber cardinalities of an interior relay -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision

open Crossing
open scoped Classical

variable {D ne np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (routes : N.WireRoutes)
local notation "G" => N.subdivide routes
variable (edgeID : (N.subdivide routes).Edge ↪ Fin ne) (portID : P ↪ Fin np)
variable (j : (e : N.Edge) × Fin (routes.interior e))

omit [Fintype P] in
private theorem from_relay (e : N.Edge) (t : Fin (routes.interior e+1)) :
    (N.subdivide routes).src ⟨e,t⟩ = .inr j → (⟨e,t⟩ : (N.subdivide routes).Edge) = (rightHop N routes j).val := by
  induction t using Fin.cases with
  | zero => intro h; cases h
  | succ u =>
    intro h
    have eq : (⟨e,u⟩ : (e : N.Edge) × Fin (routes.interior e)) = j := Sum.inr.inj (by
      simpa only [Network.subdivide,Fin.cases_succ] using h)
    subst j
    rfl

omit [Fintype P] in
private theorem to_relay (e : N.Edge) (t : Fin (routes.interior e+1)) :
    (N.subdivide routes).dst ⟨e,t⟩ = .inr j → (⟨e,t⟩ : (N.subdivide routes).Edge) = (leftHop N routes j).val := by
  induction t using Fin.lastCases with
  | last => intro h; simp [Network.subdivide] at h
  | cast u =>
    intro h
    have eq : (⟨e,u⟩ : (e : N.Edge) × Fin (routes.interior e)) = j := Sum.inr.inj (by
      simpa only [Network.subdivide,Fin.lastCases_castSucc] using h)
    subst j
    rfl

omit [Fintype P] in
private theorem incident (h : Incident G (.inr j)) :
    h = leftHop N routes j ∨ h = rightHop N routes j := by
  rcases h.property with hs | hd
  · exact .inr (Subtype.ext (from_relay N routes j h.val.1 h.val.2 hs))
  · exact .inl (Subtype.ext (to_relay N routes j h.val.1 h.val.2 hd))

omit [Fintype P] in
private theorem apart : leftHop N routes j ≠ rightHop N routes j := by
  intro same
  have h := congrArg (fun c : Incident G (.inr j) => c.val.2.val) same
  change j.2.val = j.2.val+1 at h
  omega

private def inputLane (h : Fin (N.width j.1) ⊕ Fin (N.width j.1)) : InputLane G (.inr j) :=
  h.elim (fun k => .inl ⟨leftHop N routes j,k⟩) (fun k => .inl ⟨rightHop N routes j,k⟩)

/-- An interior relay has exactly two incident width-w words and no attached ports,
even if the original routed edge is a self-loop. -/
theorem relay_incoming : incoming G (.inr j) = 2*N.width j.1 := by
  classical
  have bij : Function.Bijective (inputLane N routes j) := by
    constructor
    · rintro (a|a) (b|b) h
      · apply congrArg Sum.inl
        exact eq_of_heq (Sigma.mk.inj (Sum.inl.inj h)).2
      · exact (apart N routes j (Sigma.mk.inj (Sum.inl.inj h)).1).elim
      · exact (apart N routes j (Sigma.mk.inj (Sum.inl.inj h)).1.symm).elim
      · apply congrArg Sum.inr
        exact eq_of_heq (Sigma.mk.inj (Sum.inl.inj h)).2
    · rintro (⟨h,k⟩ | ⟨p,k⟩)
      · rcases incident N routes j h with rfl | rfl
        · exact ⟨.inl k,rfl⟩
        · exact ⟨.inr k,rfl⟩
      · cases p.property
  have card := Fintype.card_congr ((Equiv.ofBijective _ bij).trans (sourceOrder G (Fintype.equivFin _).toEmbedding (Fintype.equivFin _).toEmbedding (.inr j)))
  simp only [Fintype.card_sum,Fintype.card_fin] at card
  omega

/-- Count the work assignments in every fiber: one exactly for equal words and the
empty observation list, zero otherwise. -/
theorem relay_fiber_card (z : ∀ h : Incident G (.inr j), Fin ((N.subdivide routes).width h.val) → Bool)
    (x : ∀ p : Attached G (.inr j), Fin (bits p.val) → Bool) (obs : List (Bool × Option ℕ)) :
    Nat.card ((relaySite N routes edgeID portID j).Fiber (inputWords G edgeID portID (.inr j) z x) obs) =
      if z (leftHop N routes j) = z (rightHop N routes j) ∧ obs = [] then 1 else 0 := by
  let S := (relaySite N routes edgeID portID j).Fiber (inputWords G edgeID portID (.inr j) z x) obs
  have sub : Subsingleton S := by
    change Subsingleton {g : Fin 0 → Bool // _}
    infer_instance
  by_cases h : z (leftHop N routes j) = z (rightHop N routes j) ∧ obs = []
  · rw [ite_eq_left h]
    let _ : Nonempty S := (relay_fiber_nonempty N routes edgeID portID j z x obs).mpr h
    change Nat.card S = 1
    exact Nat.card_of_subsingleton (Classical.choice (inferInstance : Nonempty S))
  · rw [ite_eq_right h]
    let _ : IsEmpty S := not_nonempty_iff.mp (fun e => h ((relay_fiber_nonempty N routes edgeID portID j z x obs).mp e))
    change Nat.card S = 0
    exact Nat.card_of_isEmpty

end Packing.Inherited.Subdivision

end BorderVNP
end Computability
end OAI
