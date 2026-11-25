import OAI.Computability.MultitapeWeakETH.Padding
import OAI.Computability.MultitapeWeakETH.ShiftLaw

/-! # Common supply, terminal and root estimates on the folded network -/

namespace OAI.Computability.MultitapeWeakETH.FoldedNetwork

open Finset
open scoped Classical BigOperators
noncomputable section

private theorem mean_abs {N : ℕ} [NeZero N] (d : Fin N → Fin N → ℝ) (E : ℝ)
    (bound : (∑ j, ∑ i, (d i j-1)^2) ≤ 12*(N:ℝ)*E) :
    (𝔼 i, 𝔼 j, |d i j-1|) ≤ Real.sqrt (12*E/N) := by
  let f (ij : Fin N × Fin N) := |d ij.1 ij.2-1|
  have cs := Finset.expect_mul_sq_le_sq_mul_sq univ f (fun _ => (1:ℝ))
  have cs' : (𝔼 ij, f ij)^2 ≤ 𝔼 ij, (f ij)^2 := by simpa using cs
  have avg : (𝔼 ij, f ij) = 𝔼 i, 𝔼 j, |d i j-1| := by
    rw [← expect_product']; simp [f]
  rw [← avg]
  apply Real.le_sqrt_of_sq_le
  apply cs'.trans
  rw [Fintype.expect_eq_sum_div_card,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
  have pos : 0 < (N:ℝ) := Nat.cast_pos.mpr (NeZero.pos _)
  apply (div_le_iff₀ (mul_pos pos pos)).mpr
  rw [Fintype.sum_prod_type,sum_comm]
  simp only [f,sq_abs]
  apply bound.trans_eq
  field_simp

theorem folded_geometry (price : PriceZero) (D C : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∃ m₀ : ℕ, ∀ {n b N : ℕ} [NeZero N] (_hb : 0 < b) (G : Network n b),
      let m := n ⌈/⌉ b
      let P := Fintype.card (Site G N)
      let E := K*P/Real.log P
      m₀ ≤ P → m ≤ C*N → G.Bounded D →
        ∃ (X : SpectralTarget) (p : Site G N → X.carrier) (o : X.carrier) (a : ℝ), 0 < a ∧
        supplyCost G p a ≤ ((D+2)*b:ℕ)*Real.sqrt ((4*D+7+C:ℕ)*P)*Real.sqrt E ∧
        (𝔼 i, 𝔼 j, |a*dist (p (terminal G i)) (p (terminal G j))-1|) ≤ Real.sqrt (12*E/N) ∧
        ∀ h : Site G N → ℝ, (∀ v, 0 ≤ h v ∧ h v ≤ 4*b) →
          (∑ v, h v*(a*dist (p v) o)) ≤ (∑ v, h v)/Real.sqrt 2 +
            Real.sqrt (4*b*∑ v, h v)*Real.sqrt E := by
  obtain ⟨K,hK,m₀,geom⟩ := graph_geometry price (4*D+7+C)
  refine ⟨K,hK,m₀,?_⟩
  intro n b N _ hb G m P E large fold bounded
  let e := Fintype.equivFin (Site G N)
  obtain ⟨X,p,o,a,ha,edges,terminals,root⟩ := geom P large (e ∘ src G) (e ∘ dst G) (by
    intro v
    obtain ⟨j,rfl⟩ := e.surjective v
    simpa only [Function.comp_apply,e.injective.eq_iff] using degree_le G fold bounded j)
  let term : Fin N ↪ Fin P := ⟨fun i => e (terminal G i),e.injective.comp (fun _ _ h => Sum.inr.inj (Sum.inr.inj h))⟩
  refine ⟨X,p ∘ e,o,a,ha,?_,mean_abs _ E (terminals N term term),?_⟩
  · exact edges _ _ (by positivity) (fun w => by exact_mod_cast width_le G hb bounded w)
  · intro h bounds
    have center := root (h ∘ e.symm) (fun j => (bounds _).1)
    have reindex (f : Site G N → ℝ) : (∑ v : Fin P, f (e.symm v)) = ∑ j, f j := e.symm.sum_comp _
    have cost : (∑ j, h j*(a*dist (p (e j)) o)) = ∑ j, (h ∘ e.symm) j*(a*dist (p j) o) := by
      apply Fintype.sum_equiv e
      simp
    simp only [Function.comp_apply]
    rw [cost]
    apply center.trans
    simp only [Function.comp_apply] at *
    rw [reindex h,reindex (fun x => (h x)^2)]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply Real.sqrt_le_sqrt
    rw [mul_sum]
    exact sum_le_sum fun j _ => by rw [sq]; exact mul_le_mul_of_nonneg_right (bounds j).2 (bounds j).1

end
end OAI.Computability.MultitapeWeakETH.FoldedNetwork
