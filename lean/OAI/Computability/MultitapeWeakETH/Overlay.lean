import OAI.Computability.MultitapeWeakETH.Scalar
import OAI.Computability.VPVNP.GraphRounding

/-! # Superimposing a scalar expander on the supply graph -/

namespace OAI.Computability.MultitapeWeakETH

open MetricKMedian.PCP VPVNP.SpectralGeometry
open scoped BigOperators

variable {V D : Type} [Fintype V] [Fintype D] [DecidableEq V]

def ports (G : PortGraph V D) (v w : V) : ℕ :=
  (Finset.univ.filter fun d => G.step v d = w).card

theorem ports_sum (G : PortGraph V D) (v : V) : ∑ w, ports G v w = Fintype.card D := by
  classical
  simpa [ports] using (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset D))
    (t := (Finset.univ : Finset V)) (f := G.step v) (fun _ _ => Finset.mem_univ _)).symm

omit [Fintype V] in
theorem ports_symm (G : PortGraph V D) (v w : V) : ports G v w = ports G w v := by
  classical
  have back (a b : V) (d : D) (h : G.step a d = b) : G.rotate (b,G.back a d) = (a,d) := by
    subst b
    exact G.involutive (a,d)
  apply Finset.card_nbij' (G.back v) (G.back w)
  · intro d hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg Prod.fst (back v w d (Finset.mem_filter.mp hd).2)⟩
  · intro d hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg Prod.fst (back w v d (Finset.mem_filter.mp hd).2)⟩
  · intro d hd
    exact congrArg Prod.snd (back v w d (Finset.mem_filter.mp hd).2)
  · intro d hd
    exact congrArg Prod.snd (back w v d (Finset.mem_filter.mp hd).2)

private theorem ports_cost (G : PortGraph V D) (cost : V → V → ℝ) (v : V) :
    ∑ w, (ports G v w : ℝ)*cost v w = ∑ d, cost v (G.step v d) := by
  classical
  have term (w : V) : (ports G v w : ℝ)*cost v w =
      ∑ d, if G.step v d = w then cost v w else 0 := by
    rw [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const,nsmul_eq_mul,ports]
  simp_rw [term]
  rw [Finset.sum_comm]
  simp

/-- A fixed-degree scalar subgraph gives a Poincaré inequality for every
regular superposition, including multiplicities and diagonal arcs. -/
theorem poincare_overlay [Nonempty V] [Nonempty D] (G : PortGraph V D) (contract : G.Contracts (1/2))
    (H : Matrix V V ℕ) {degree : ℕ} (positive : 0 < degree)
    (contains : ∀ v w, ports G v w ≤ H v w) :
    HasPoincareBound ℝ (normalizeArcs H degree) (2*degree/Fintype.card D) := by
  intro f
  let cost (v w : V) := (f v-f w)^2
  have point (v w : V) : dist (f v) (f w)^2 = cost v w := by simp [cost,Real.dist_eq]
  have base := scalar_poincare G contract f
  change (𝔼 v, 𝔼 w, cost v w) ≤ 2*(𝔼 v, 𝔼 d, cost v (G.step v d)) at base
  simp only [Fintype.expect_eq_sum_div_card,← Finset.sum_div] at base
  have posV : (0:ℝ) < Fintype.card V := Nat.cast_pos.mpr Fintype.card_pos
  have posD : (0:ℝ) < Fintype.card D := Nat.cast_pos.mpr Fintype.card_pos
  have posH : (0:ℝ) < degree := Nat.cast_pos.mpr positive
  have leCost : (∑ v, ∑ d, cost v (G.step v d)) ≤ ∑ v, ∑ w, (H v w : ℝ)*cost v w := by
    simp_rw [← ports_cost G cost]
    exact Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast contains v w) (sq_nonneg _)
  have energy : walkEnergy (normalizeArcs H degree) f = (∑ v, ∑ w, (H v w : ℝ)*cost v w)/degree := by
    simp only [walkEnergy,normalizeArcs,Finset.sum_div,div_mul_eq_mul_div]
    congr 1
    funext v
    congr 1
    funext w
    rw [dist_comm,point]
  simp only [point,energy]
  field_simp at base ⊢
  nlinarith only [base,mul_le_mul_of_nonneg_right leCost posV.le]

/-- The remaining regularity is filled with diagonal arcs. -/
def withLoops (H : Matrix V V ℕ) (degree : ℕ) (v w : V) : ℕ :=
  H v w + if w = v then degree - ∑ u, H v u else 0

theorem withLoops_regular (H : Matrix V V ℕ) (degree : ℕ) (bound : ∀ v, ∑ w, H v w ≤ degree)
    (symm : ∀ v w, H v w = H w v) :
    (∀ v w, withLoops H degree v w = withLoops H degree w v) ∧
    (∀ v, ∑ w, withLoops H degree v w = degree) ∧
    (∀ v w, H v w ≤ withLoops H degree v w) := by
  constructor
  · intro v w
    by_cases eq : w = v
    · subst w; rfl
    · simp [withLoops,eq,Ne.symm eq,symm v w]
  constructor
  · intro v
    simp [withLoops,Finset.sum_add_distrib,Nat.add_sub_of_le (bound v)]
  · intro v w
    exact Nat.le_add_right _ _

end OAI.Computability.MultitapeWeakETH
