import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortChordWidths

namespace OAI
/-! # Reading a finite tensor identity as maps on the incident ports

A chord representation can merge parallel edges and remove loops. Local
restriction back to the original incidence format recovers the full set of
half-wire indices. Each supply edge then has just one shared index in the
sum for the kernel.
-/

namespace ThreeFlat.Diagonal

open LinearAlgebra.SpectralBooks SiteTensor
open scoped Classical BigOperators
noncomputable section

variable {V E S H : Type} [Fintype V] [Fintype E] [Fintype S] [Fintype H]
variable {F : Type*} [Field F]

/-- Move an ordinary sum of restricted chord wirings onto the two actual
port graphs, obtaining a separately evaluated matrix at each port vertex. -/
theorem port_kernel_of_tile (D : PortGraph V E) (P : PortGraph V S)
    (A : E → Type) [∀ e, Fintype (A e)] (B : H → S → Type) [∀ h s, Fintype (B h s)]
    (T : Raw.{0} V F) (toDemand : (D.rawWiring F A).Restricts T)
    (terms : H → (∀ v, T.Leg v) → F) (tile : T.coeff = ∑ h, terms h)
    (toSupply : ∀ h, ({T with coeff := terms h} : Raw V F).Restricts (P.rawWiring F (B h))) :
    ∃ M : ∀ h v, D.State A v → P.State (B h) v → F,
      ∀ x, D.wiring A x = ∑ h, ∑ z : ∀ s, B h s, ∏ v, M h v (x v) (P.atVertex z v) := by
  obtain ⟨left, hleft⟩ := toDemand
  let entry (h : H) (x : ∀ v, D.State A v) := ∑ a, terms h a * ∏ v, left v (x v) (a v)
  have split (x : ∀ v, D.State A v) : D.wiring A x = ∑ h, entry h x := by
    calc
      _ = ∑ a, T.coeff a * ∏ v, left v (x v) (a v) := hleft x
      _ = _ := by simp only [tile, Finset.sum_apply, Finset.sum_mul, entry]; rw [Finset.sum_comm]
  have res (h : H) : Crossing.IsRestriction (entry h) (P.rawWiring F (B h)).coeff :=
    restrict_trans (Y := terms h) ⟨left, fun _ => rfl⟩ (toSupply h)
  choose M hM using res
  refine ⟨M, fun x => (split x).trans ?_⟩
  apply Finset.sum_congr rfl
  intro h _
  calc
    entry h x = ∑ a, P.wiring (B h) a * ∏ v, M h v (x v) (a v) := hM h x
    _ = P.contraction (A := B h) (fun v a => M h v (x v) a) :=
      (P.contraction_eq_wiring (B h) (fun v a => M h v (x v) a)).symm
    _ = _ := rfl

end
end ThreeFlat.Diagonal

end OAI
