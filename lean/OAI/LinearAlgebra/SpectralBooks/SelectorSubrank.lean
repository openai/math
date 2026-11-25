import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortWiringClass

namespace OAI
/-! # Sending a common selector through connected port wiring -/

noncomputable section

namespace LinearAlgebra.SpectralBooks.PortGraph

open SiteTensor
open scoped BigOperators Classical

variable {V E : Type} [Fintype V] [Nonempty V] [Fintype E] (G : PortGraph V E)
    (K : Type*) [Field K] (v₀ : V)

private theorem restrict_of_coordinate {I : Type*} [Fintype I] {F : Type*} [CommSemiring F]
    {A B : I → Type*} [∀ i, Fintype (A i)] (e : ∀ i, B i → A i)
    {X : (∀ i, B i) → F} {Y : (∀ i, A i) → F} (h : ∀ x, X x = Y (fun i => e i (x i))) :
    Crossing.IsRestriction X Y := by
  classical
  refine ⟨fun i b a => if a = e i b then 1 else 0, fun x => ?_⟩
  rw [h x]
  simp_rw [Fintype.prod_boole]
  have heq (a : ∀ i, A i) : (∀ i, a i = e i (x i)) ↔ a = fun i => e i (x i) :=
    funext_iff.symm
  simp [heq, mul_ite]

/-- Each vertex copies its label to all incident ports. If all edge checks pass,
each label equals the one at the base vertex. -/
theorem natCast_le_rawWiring_of_connected (A : Type) [Fintype A]
    (conn : ∀ f : V → Bool, (∀ e, f (G.tail e) = f (G.head e)) → ∀ v, f v = f v₀) :
    (Fintype.card A : TensorClass.{0} V K) ≤ ofRaw (G.rawWiring K (fun _ => A)) := by
  classical
  calc
    (Fintype.card A : TensorClass.{0} V K) = ofRaw (Raw.diagonal V K A) :=
      (ofRaw_diagonal_eq_natCast V K A).symm
    _ ≤ _ := ofRaw_le_iff.mpr ?_
  let copy (v : V) (b : A) : G.State (fun _ => A) v := fun _ => b
  apply restrict_of_coordinate copy
  intro x
  rw [Raw.diagonal_coeff_at v₀]
  change _ = G.wiring (fun _ => A) (fun i => copy i (x i))
  unfold wiring
  have heq : (∀ v, x v = x v₀) ↔ (∀ e, x (G.tail e) = x (G.head e)) := by
    refine ⟨fun h e => (h (G.tail e)).trans (h (G.head e)).symm, fun h v => ?_⟩
    have hb := conn (fun i => decide (x i = x v₀))
      (fun e => by simp only [h e]) v
    simpa using hb
  split
  · rename_i constant
    split
    · rfl
    · rename_i mismatch
      exact (mismatch (heq.mp constant)).elim
  · rename_i nonconstant
    split
    · rename_i compatible
      exact (nonconstant (heq.mpr compatible)).elim
    · rfl

/-- One bit on each edge of a connected port graph carries one common bit. -/
theorem two_le_rawWiring_of_connected
    (conn : ∀ f : V → Bool, (∀ e, f (G.tail e) = f (G.head e)) → ∀ v, f v = f v₀) :
    2 ≤ ofRaw (G.rawWiring K (fun _ => Fin 2)) := by
  simpa using G.natCast_le_rawWiring_of_connected K v₀ (Fin 2) conn

end LinearAlgebra.SpectralBooks.PortGraph

end
end OAI
