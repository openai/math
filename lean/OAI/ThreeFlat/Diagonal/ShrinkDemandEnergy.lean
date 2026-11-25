import OAI.ThreeFlat.Diagonal.ShrinkDemands

namespace OAI
/-! # Energy of the actual six-party demand assignment -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression
open scoped Classical BigOperators
noncomputable section

variable {c d Q : ℕ} {V H Tag L : Type*} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] (P : PackingData V H Tag L d c)

/-- Exactly one quarter of the old wires above a packed slot are thick at
both ends. This is the fiber used by the concrete AB payloads. -/
theorem card_thickAt (p : Site V Tag L × Fin d) : Fintype.card (ThickAt P p) = 2^(c-2)*d := by
  let e : ThickAt P p ≃ endpointFiber P p 1 1 := {
    toFun := by
      rintro ⟨⟨q,z⟩,hq,hz⟩
      change q = p at hq
      subst q
      exact ⟨z,hz⟩
    invFun := fun t => ⟨(p,t.val),rfl,t.property⟩
    left_inv := by rintro ⟨⟨q,z⟩,rfl,hz⟩; rfl
    right_inv := fun _ => rfl
  }
  exact (Fintype.card_congr e).trans (endpoint_count P p 1 1)

/-- Label all old arcs by their thick bundle membership or their CD motif. -/
def classifyArc : Arc V H Tag L d c ≃ (Σ p, ThickAt P p) ⊕ P.Motif where
  toFun e := if h : P.thick (sourcePosition e) ∧ P.thick (sourcePosition (P.actual e)) then
    .inl ⟨e.1,⟨e,rfl,h⟩⟩ else .inr ⟨e,h⟩
  invFun := Sum.elim (fun t => t.2.val) Subtype.val
  left_inv := by intro e; dsimp only; split <;> rfl
  right_inv := by
    rintro (⟨p,⟨e,hp,h⟩⟩ | ⟨e,h⟩)
    · subst p; simp [h]
    · simp [h]

theorem old_arc_sum (f : Arc V H Tag L d c → ℝ) :
    (∑ p, ∑ a : ThickAt P p, f a.val) + (∑ m : P.Motif, f m.val) = ∑ e, f e := by
  have h := (classifyArc P).symm.sum_comp f
  rw [Fintype.sum_sum_type, Fintype.sum_sigma] at h
  simpa [classifyArc] using h

/-- One packed source slot uses all its thick arcs at the old mass and
allocates balanced AB slices of relative mass one third. -/
theorem assigned_bundle_le (w : Arc V H Tag L d c → ℕ) (p : Site V Tag L × Fin d) (hQ : 0 < Q)
    (hcount : Q = 3 * (2^(c-2)*d)) {μ : ℝ} (hμ : 0 < μ) :
    (∑ i : Fin Q, (SlotEnergy.piece (thickWidth P w p) Q i : ℝ)^2 / ((1/3)*μ)) ≤
      (∑ a : ThickAt P p, (w a.val : ℝ)^2 / μ) + Q/(4*(1/3)*μ) := by
  let e := (Fintype.equivFinOfCardEq (card_thickAt P p)).symm
  have hmatch : (Q : ℝ)*(1/3) = (2^(c-2)*d : ℕ) := by rw [hcount]; push_cast; ring
  have h := SlotEnergy.packed_demand_le (fun j => w (e j).val) hQ hμ (by norm_num) hmatch
  rw [e.sum_comp (fun a : ThickAt P p => w a.val),
    e.sum_comp (fun a : ThickAt P p => (w a.val : ℝ)^2 / μ)] at h
  exact h

/-- Total energy of all AB/CD pairs relative to the energy of the graph
before the shrink. The additive term is precisely the integer-rounding
allowance per thick bundle. -/
theorem assigned_demands_le (w : Arc V H Tag L d c → ℕ) (hQ : 0 < Q)
    (hcount : Q = 3*(2^(c-2)*d)) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q)
    {μ : ℝ} (hμ : 0 < μ) :
    (∑ m : P.Motif, ((SlotEnergy.piece (thickWidth P w (num m).1) Q (num m).2 : ℝ)^2 / ((1/3)*μ)
      + (w m.val : ℝ)^2 / μ)) ≤
      (∑ e, (w e : ℝ)^2 / μ) + Fintype.card (Site V Tag L × Fin d)*(Q/(4*(1/3)*μ)) := by
  let f := fun p : (Site V Tag L × Fin d) × Fin Q =>
    (SlotEnergy.piece (thickWidth P w p.1) Q p.2 : ℝ)^2 / ((1/3)*μ)
  rw [Finset.sum_add_distrib, num.sum_comp f, Fintype.sum_prod_type]
  have h := Finset.sum_le_sum (s := Finset.univ) fun p _ => assigned_bundle_le P w p hQ hcount hμ
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [← old_arc_sum P (fun e => (w e : ℝ)^2 / μ)]
  dsimp only [f] at *
  linarith

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
