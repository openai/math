import OAI.ThreeFlat.Diagonal.RefreshArrival

namespace OAI
/-! # The exact kernel for a complete degree-refresh step -/

namespace ThreeFlat.Diagonal.RefreshTies

open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression
open scoped Classical BigOperators
noncomputable section

private theorem sum_congr_instances {I K : Type*} [AddCommMonoid K] {u v : Fintype I}
    {f g : I → K} (h : ∀ i, f i = g i) :
    (∑ i ∈ @Finset.univ I u, f i) = ∑ i ∈ @Finset.univ I v, g i := by
  cases Subsingleton.elim u v
  exact Finset.sum_congr rfl (fun i _ => h i)

/-- Replace both dense families of port ties in every block simultaneously.
A global term records one tile choice per block. A new wiring assignment
consists of the tuple on each shared external arc and one word on every
sparse supply arc. Only the original local half-wire values at the tail of
a dense tie and the external bundle incident at its head enter each kernel. -/
theorem refresh_kernel {V C L : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L]
    {m : ℕ} (G : LiftedSlots V m (C × L)) (port : Fin m ≃ C)
    {K : Type*} [Field K] (A : Address (V × L) m → Type) [∀ e, Fintype (A e)]
    (H S : V × L → Type) [∀ u, Fintype (H u)] [∀ u, Fintype (S u)]
    (P : ∀ u, PortGraph (Fin m) (S u)) (B : ∀ u, H u → S u → Type) [∀ u h s, Fintype (B u h s)]
    (M : ∀ u h v, (RefreshMotif.denseGraph m).State (fun e => A (addr (arrival G port) u e)) v →
      (P u).State (B u h) v → K)
    (tile : ∀ u x, (RefreshMotif.denseGraph m).wiring (fun e => A (addr (arrival G port) u e)) x =
      ∑ h, ∑ w : ∀ e, B u h e, ∏ v, M u h v (x v) ((P u).atVertex w v))
    (x y : ∀ e, A e) :
    (if x = y then (1 : K) else 0) =
      ∑ h : ∀ u, H u, ∑ z : External A, ∑ w : ∀ u e, B u (h u) e,
        ∏ u, ∏ v, M u (h u) v (portFields (arrival G port) u v
          (readOld (arrival G port) x y u v) (readBundle (arrival G port) z u v)) ((P u).atVertex (w u) v) := by
  simp_rw [← tieState_local]
  rw [old_wiring_eq_bundles (arrival G port) x y]
  simp_rw [tile]
  conv_rhs => rw [Finset.sum_comm]
  apply sum_congr_instances
  intro z
  rw [Fintype.prod_sum]
  apply sum_congr_instances
  intro h
  rw [Fintype.prod_sum]

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
