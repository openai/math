import OAI.Computability.MultitapeWeakETH.Overlay
import OAI.Computability.MultitapeWeakETH.Cloud

/-! # A single placement controlling supply and all scalar tests -/

namespace OAI.Computability.MultitapeWeakETH

open MetricKMedian.PCP VPVNP.SpectralGeometry

/-- Given the dyadic padding used by the zigzag family, a bounded-degree
supply matrix can be augmented and regularized. Both the low edge energy
and the scalar variance estimates hold for one placement. -/
theorem common_placement (price : PriceZero) (k e : ℕ)
    (large : 10000*(e+3) ≤ 176*k)
    (gap : 2*(2:ℝ)^e/(2:ℝ)^88 ≤ (176*k:ℕ)/(10000*((e:ℝ)+3)))
    (N : Matrix (Fin (2^(176*k))) (Fin (2^(176*k))) ℕ) (symm : ∀ i j, N i j = N j i)
    (degree : ∀ i, (∑ j, N i j) + 2^88 ≤ 2^e) :
    ∃ H : Matrix (Fin (2^(176*k))) (Fin (2^(176*k))) ℕ,
      (∀ i j, N i j ≤ H i j) ∧
      HasPoincareBound ℝ (normalizeArcs H (2^e)) (2*(2:ℝ)^e/(2:ℝ)^88) ∧
      ∃ X : SpectralTarget, ∃ p : Fin (2^(176*k)) → X.carrier,
        ((176*k:ℕ)/(10000*((e:ℝ)+3))) * walkEnergy (normalizeArcs H (2^e)) p <
          (∑ i, ∑ j, dist (p i) (p j)^2) / Fintype.card (Fin (2^(176*k))) := by
  classical
  have growth : ExpanderFamily.growth = 2^176 := by unfold ExpanderFamily.growth; rw [← pow_mul]
  have card : Fintype.card (ExpanderFamily.Vertex k) = Fintype.card (Fin (2^(176*k))) := by
    rw [ExpanderFamily.card_vertex,growth,Fintype.card_fin,pow_mul]
  let G := (ExpanderFamily.graph k).relabel (Fintype.equivOfCardEq card) (Equiv.refl _)
  have contraction : G.Contracts (1/2) :=
    (ExpanderFamily.graph k).relabel_contracts _ _ (ExpanderFamily.graph_contracts k)
  have cardD : Fintype.card ExpanderFamily.Degree = 2^88 := by
    change Fintype.card (Fin (2^44) × Fin (2^44)) = 2^88
    rw [Fintype.card_prod,Fintype.card_fin,← pow_add]
  let combined i j := N i j + ports G i j
  have sumBound (i) : (∑ j, combined i j) ≤ 2^e := by
    simpa only [combined,Finset.sum_add_distrib,ports_sum,cardD] using degree i
  have sym (i j) : combined i j = combined j i := by
    simp only [combined,symm i j,ports_symm G i j]
  let H := withLoops combined (2^e)
  obtain ⟨hs,rows,inc⟩ := withLoops_regular combined (2^e) sumBound sym
  have scalar : HasPoincareBound ℝ (normalizeArcs H (2^e)) (2*(2:ℝ)^e/(2:ℝ)^88) := by
    have h := poincare_overlay G contraction H (show 0 < 2^e by positivity)
      (fun i j => (Nat.le_add_left _ _).trans (inc i j))
    simpa only [cardD,Nat.cast_pow,Nat.cast_ofNat] using h
  refine ⟨H,fun i j => (Nat.le_add_right _ _).trans (inc i j),scalar,?_⟩
  apply exists_logarithmic_placement price (176*k) e large H hs rows
  intro f
  exact (scalar f).trans (mul_le_mul_of_nonneg_right gap
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (sq_nonneg _)))

end OAI.Computability.MultitapeWeakETH
