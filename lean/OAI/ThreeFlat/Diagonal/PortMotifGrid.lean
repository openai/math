import OAI.LinearAlgebra.SpectralBooks.WireIdentity
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortChordWidths
import OAI.Computability.VPVNP.MotifGrid

namespace OAI
/-! # Finite width-grid identities in site-tensor port coordinates

A quadratic spectral distance comparison supplies a finite selector for
each rounded demand. The identity is an equality of actual coefficients,
with local restrictions on every summand. Parallel directed edges and loops
are allowed in the input graphs.
-/

namespace ThreeFlat.Diagonal.PortMotifGrid

open LinearAlgebra.SpectralBooks SiteTensor ChordGraph Computability.VPVNP.MotifGrid
open scoped BigOperators Classical

variable {m : ℕ} {E S : Type} [Fintype E] [Fintype S]

/-- Chord collection preserves the first moment of a symmetric distance
which vanishes on loops. -/
theorem chordWidths_value (G : PortGraph (Fin m) E) (w : E → ℕ) (d : Fin m → Fin m → ℝ)
    (sym : ∀ x y, d x y = d y x) (loop : ∀ x, d x x = 0) :
    (∑ e : Chord m, (G.chordWidths w e : ℝ) * d e.1.1 e.1.2) =
      ∑ e, (w e : ℝ) * d (G.tail e) (G.head e) := by
  classical
  simp only [PortGraph.chordWidths, Finsupp.finsetSum_apply, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  unfold PortGraph.chordWidth
  split_ifs with h h'
  · simp [Finsupp.single_apply, ite_mul]
  · simp [Finsupp.single_apply, ite_mul, sym (G.head e) (G.tail e)]
  · have he : G.tail e = G.head e := le_antisymm (le_of_not_gt h') (le_of_not_gt h)
    simp [he, loop]

/-- The zero-distance branch also provides a valid selector when every
demand and supply wire is collapsed in a given placement. -/
theorem grid_selector {p : E → ℝ} {q : S → ℝ} {H R : ℝ}
    (G : StrictGrids p q H R) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i)
    {t : ℕ} (ht : 0 < t) (z : G.demands) (d : E → ℝ) (e : S → ℝ)
    (he : ∀ i, 0 ≤ e i) (hcomp : distanceEnergy p d ≤ H * distanceEnergy q e) :
    ∃ w : G.supplies, wireValue (fun i => (G.demandWidths t z i : ℝ)) d ≤
      wireValue (fun i => (G.supplyWidths t w i : ℝ)) e := by
  by_cases hpos : 0 < distanceEnergy q e
  · obtain ⟨w, hw⟩ := G.integer_strict ht z d e he hpos hcomp
    exact ⟨w, hw.le⟩
  have hzero : distanceEnergy q e = 0 := le_antisymm (le_of_not_gt hpos)
    (Finset.sum_nonneg fun i _ => mul_nonneg (hq i) (sq_nonneg _))
  rw [hzero, mul_zero] at hcomp
  have hd (i : E) : d i = 0 := by
    have hi := (Finset.single_le_sum (f := fun j => p j * (d j)^2)
      (fun j _ => mul_nonneg (hp j).le (sq_nonneg _)) (Finset.mem_univ i)).trans hcomp
    by_contra hn
    exact (mul_pos (hp i) (sq_pos_of_ne_zero hn)).not_ge hi
  refine ⟨⟨_, G.zero_mem_supplies⟩, ?_⟩
  simp only [wireValue, hd, mul_zero, Finset.sum_const_zero]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (he _)

variable {K : Type*} [Field K] [Nonempty (Fin m)]

/-- A finite grid gives an actual ordinary sum identity with controlled
selector length for every one of its demand profiles. -/
theorem exists_port_grid_tile (D : PortGraph (Fin m) E) (S' : PortGraph (Fin m) S)
    {p : E → ℝ} {q : S → ℝ} {H R : ℝ} (G : StrictGrids p q H R)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 ≤ q i)
    (comparison : ∀ φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} (Fin m) K → _ → Prop),
      distanceEnergy p (fun i => rawWireDistance φ 1 (D.tail i) (D.head i)) ≤
        H * distanceEnergy q (fun i => rawWireDistance φ 1 (S'.tail i) (S'.head i)))
    {t : ℕ} (ht : 0 < t) (z : G.demands) {η : ℝ} (hη : 0 < η) (N : ℕ) :
    let a := D.chordWidths (G.demandWidths t z)
    let U := fun j : G.supplies => S'.chordWidths (G.supplyWidths t j)
    ∃ b s : ℕ, N < b ∧ (s : ℝ) ≤ η * b ∧
      let X := raw K (b • a)
      ∃ L : ℕ, L ≤ 2 ^ s ∧ ∃ v : Fin L → (∀ i, X.Leg i) → K,
        X.coeff = ∑ l, v l ∧ ∀ l, ∃ n : G.supplies → ℕ, ∑ j, n j = b ∧
          ({X with coeff := v l} : Raw (Fin m) K).Restricts (raw K (∑ j, n j • U j)) := by
  classical
  have : Nonempty G.supplies := ⟨⟨_, G.zero_mem_supplies⟩⟩
  apply exists_finite_wire_tile K _ _ _ hη N
  intro φ
  let d := rawWireDistance φ 1
  have ds : ∀ x y, d x y = d y x := rawWireDistance_symm φ 1
  have dl : ∀ x, d x x = 0 := rawWireDistance_self φ 1 zero_le_one
  obtain ⟨w, hw⟩ := grid_selector G hp hq ht z _ _
    (fun i => rawLogPrice_nonneg φ zero_le_one _) (comparison φ)
  refine ⟨w, ?_⟩
  rw [chordWidths_value D _ (rawWireDistance φ 1) ds dl, chordWidths_value S' _ (rawWireDistance φ 1) ds dl]
  exact hw

end ThreeFlat.Diagonal.PortMotifGrid

end OAI
