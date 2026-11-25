import OAI.ThreeFlat.Diagonal.SlotRefinement

namespace OAI
/-! # Placing parallel pieces and one-state pads on named physical slots -/

namespace ThreeFlat.Diagonal.SlotRefinement

open LinearAlgebra.SpectralBooks
open scoped Classical BigOperators
noncomputable section

variable {V E D Pad : Type} {I : E → Type} (edge : ((Σ e, I e) ⊕ Pad) ≃ D)
variable (S : PortGraph V E) (A : E → Type) (T : PortGraph V D) (B : D → Type)
variable [∀ p : Pad, Unique (B (edge (.inr p)))]

/-- Interleave the source-numbered pieces on the actual graph with unique
padding labels. Every physically present arc receives a label. -/
def parallelBoundary (words : ∀ e, A e ≃ (∀ i : I e, B (edge (.inl ⟨e,i⟩)))) :
    (∀ e, A e) ≃ (∀ d, B d) :=
  (Equiv.piCongrRight words).trans <|
    (Equiv.piCurry (fun e (i : I e) => B (edge (.inl ⟨e,i⟩)))).symm.trans <|
    (Equiv.prodUnique _ ((p : Pad) → B (edge (.inr p)))).symm.trans <|
    (Equiv.sumPiEquivProdPi (fun p => B (edge p))).symm.trans (Equiv.piCongrLeft B edge)

@[simp] theorem parallelBoundary_piece (words : ∀ e, A e ≃ (∀ i : I e, B (edge (.inl ⟨e,i⟩))))
    (a : ∀ e, A e) (e : E) (i : I e) :
    parallelBoundary edge A B words a (edge (.inl ⟨e,i⟩)) = words e (a e) i := by
  unfold parallelBoundary
  simp only [Equiv.trans_apply,Equiv.piCongrLeft_apply_apply]
  rfl

/-- Reconstruct the incident word from the local parallel half-indices.
The incidence hypothesis is checked separately at the two ends. -/
def parallel (words : ∀ e, A e ≃ (∀ i : I e, B (edge (.inl ⟨e,i⟩))))
    (ends : ∀ e (i : I e) side, T.vertex (edge (.inl ⟨e,i⟩)) side = S.vertex e side) :
    Refines S A T B where
  boundary := parallelBoundary edge A B words
  read v y p := (words p.1.1).symm fun i => y ⟨(edge (.inl ⟨p.1.1,i⟩),p.1.2),
    (ends p.1.1 i p.1.2).trans p.property⟩
  read_at a v := by
    funext p
    change (words p.1.1).symm (fun i => parallelBoundary edge A B words a
      (edge (.inl ⟨p.1.1,i⟩))) = a p.1.1
    simp

/-- Canonical width for each numbered physical slot. -/
def actualWidth (n b : E → ℕ) (cover : ((Σ e, Fin (n e)) ⊕ Pad) ≃ D) (d : D) : ℕ :=
  Sum.elim (fun p => SlotEnergy.piece (b p.1) (n p.1) p.2) (fun _ => 0) (cover.symm d)

/-- The old alphabet may already be a selector–payload pair; its single-word
encoding is independent of the physical source/destination slot numbers. -/
def actualWords (n b : E → ℕ) (hn : ∀ e, 0 < n e) (cover : ((Σ e, Fin (n e)) ⊕ Pad) ≃ D)
    (code : ∀ e, A e ≃ Fin (2^b e)) (e : E) :
    A e ≃ (∀ i : Fin (n e), Fin (2^actualWidth n b cover (cover (.inl ⟨e,i⟩)))) :=
  (code e).trans ((splitWord _ _ (hn e)).trans (Equiv.piCongrRight fun i => finCongr (by
    simp [actualWidth])))

/-- One history refinement puts all crossing edge words on the actual numbered
graph, splitting them into balanced intervals and padding with empty words. -/
def balanced (n b : E → ℕ) (hn : ∀ e, 0 < n e) (cover : ((Σ e, Fin (n e)) ⊕ Pad) ≃ D)
    (code : ∀ e, A e ≃ Fin (2^b e))
    (ends : ∀ e (i : Fin (n e)) side, T.vertex (cover (.inl ⟨e,i⟩)) side = S.vertex e side) :
    Refines S A T (fun a => Fin (2^actualWidth n b cover a)) := by
  letI : ∀ p : Pad, Unique (Fin (2^actualWidth n b cover (cover (.inr p)))) :=
    fun p => by simp [actualWidth]; infer_instance
  exact parallel cover S A T _ (actualWords A n b hn cover code) ends

/-- The physical padded graph has exactly the balanced-piece energy that
was budgeted on the old crossing incidences. -/
theorem actual_energy [Fintype E] [Fintype D] [Fintype Pad] (n b : E → ℕ)
    (cover : ((Σ e, Fin (n e)) ⊕ Pad) ≃ D) (p : ℝ) :
    (∑ d, (actualWidth n b cover d : ℝ)^2 / p) =
      ∑ e, ∑ i, (SlotEnergy.piece (b e) (n e) i : ℝ)^2 / p := by
  rw [← cover.sum_comp (fun d => (actualWidth n b cover d : ℝ)^2 / p)]
  simp [actualWidth,Fintype.sum_sum_type,Fintype.sum_sigma]

/-- Capacity follows from the public numbering itself. -/
theorem piece_capacity [Fintype E] [Fintype D] [Fintype Pad] (n : E → ℕ)
    (cover : ((Σ e, Fin (n e)) ⊕ Pad) ≃ D) : (∑ e, n e) ≤ Fintype.card D := by
  have h := Fintype.card_congr cover
  simp only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] at h
  omega

/-- Bound the actual output energy, using the relative mass guarantee for
each type and the number of arcs in the whole padded target. -/
theorem actual_energy_le [Fintype E] [Fintype D] [Fintype Pad] [Nonempty D] (n b : E → ℕ)
    (hn : ∀ e, 0 < n e) (cover : ((Σ e, Fin (n e)) ⊕ Pad) ≃ D) (mass : E → ℝ)
    (hm : ∀ e, 0 < mass e) {δ : ℝ} (hδ : δ < 1)
    (enough : ∀ e, (1-δ)*mass e ≤ n e * (1/(Fintype.card D : ℝ))) :
    (∑ d, (actualWidth n b cover d : ℝ)^2 / (1/(Fintype.card D : ℝ))) ≤
      (∑ e, (b e : ℝ)^2 / mass e) / (1-δ) + (Fintype.card D : ℝ)^2/4 := by
  rw [actual_energy]
  apply SlotEnergy.regularized_energy_le _ _ _ (by exact_mod_cast Fintype.card_pos (α := D)) hδ hn hm enough
  exact_mod_cast piece_capacity n cover

end
end ThreeFlat.Diagonal.SlotRefinement

end OAI
