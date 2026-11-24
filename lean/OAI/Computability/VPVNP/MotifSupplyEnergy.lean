import OAI.Computability.VPVNP.MotifGrid
import OAI.Computability.VPVNP.MotifSelector
import OAI.Computability.VPVNP.WireSpectrum

/-!
# Positive spectral energy of a connected supply motif

In Theorem 6.1 the binary supply network restricts to the two-entry diagonal:
at each party the local map selects the same output color on every incident
wire. The selected coefficient is one precisely when the coloring is
constant along every edge. Connectivity therefore forces the sum of the
supply wire distances to be at least one at each spectral point.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifSelector.Supply

/-- Edgewise agreement of colors propagates along paths of the supply graph. -/
theorem color_eq_of_connected {J E I : Type*} (G : MotifSelector.Supply J E) (color : J → I)
    (h : ∀ e, color (G.src e) = color (G.dst e)) (j l : J) : color j = color l := by
  induction G.connected j l with
  | refl => rfl
  | tail _ step ih =>
    rcases step with ⟨e, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ih.trans (h e)
    · exact ih.trans (h e).symm

end MotifSelector.Supply

namespace WireTensor

variable {k J : Type*} [Fintype J] [Nonempty J]

/-- A connected network of equality wires realizes the diagonal by selecting
the output color on every incident half-wire. -/
theorem connectedNetwork_restricts_diagonal [CommSemiring k] {E I : Type*}
    [Fintype E] [Fintype I] (a b : E → J)
    (hconn : ∀ x : J → I, (∀ e, x (a e) = x (b e)) → ∀ i j, x i = x j) :
    Restricts (wireNetwork (k := k) a b (fun _ ↦ I)) (diagonal I) := by
  classical
  let W := wireNetwork (k := k) a b (fun _ ↦ I)
  let select (j : J) (i : I) : W.Basis j := ⟨fun _ _ ↦ i, fun _ _ ↦ i⟩
  refine ⟨_, (applyLocal_pullback select W.coeff).trans ?_⟩
  funext x
  simp only [W, select, wireNetwork, diagonal, Fintype.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h
    let j : J := Classical.ofNonempty
    exact ⟨x j, fun i ↦ hconn x h i j⟩
  · rintro ⟨c, hc⟩ e
    exact (hc (a e)).trans (hc (b e)).symm

namespace SpectralPoint

variable [Field k] {E : Type} [Fintype E] (F : SpectralPoint k J) (a b : E → J)
variable (hconn : ∀ x : J → Fin 2, (∀ e, x (a e) = x (b e)) → ∀ i j, x i = x j)
include hconn

/-- The binary supply network has value at least two, giving a logarithmic
lower bound on the sum of the edge distances. -/
theorem one_le_sum_connected_wireDistance : 1 ≤ ∑ e, F.wireDistance (a e) (b e) := by
  have h := F.monotone (connectedNetwork_restricts_diagonal (k := k) a b hconn)
  rw [F.value_diagonal_fin] at h
  have hreal : (2 : ℝ) ≤ F.value (wireNetwork a b (fun _ ↦ Fin 2)) := by exact_mod_cast h
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hreal
  have hsum := F.log2_value_binary_wireNetwork a b (fun _ ↦ 1)
  simpa only [pow_one, Nat.cast_one, one_mul] using
    ((one_le_div (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 hlog).trans_eq hsum

/-- Some supply edge has positive spectral distance. -/
theorem exists_pos_connected_wireDistance : ∃ e, 0 < F.wireDistance (a e) (b e) := by
  by_contra! h
  have hnonpos := Finset.sum_nonpos (s := Finset.univ) (fun e _ ↦ h e)
  linarith [F.one_le_sum_connected_wireDistance a b hconn]

/-- The weighted supply energy in Theorem 6.1 is positive for every
spectral point when all edge masses are positive. -/
theorem connected_distanceEnergy_pos (q : E → ℝ) (hq : ∀ e, 0 < q e) :
    0 < MotifGrid.distanceEnergy q (fun e ↦ F.wireDistance (a e) (b e)) := by
  obtain ⟨e, he⟩ := F.exists_pos_connected_wireDistance a b hconn
  apply (mul_pos (hq e) (sq_pos_of_pos he)).trans_le
  exact Finset.single_le_sum (fun i _ ↦ mul_nonneg (hq i).le (sq_nonneg (F.wireDistance (a i) (b i))))
    (Finset.mem_univ e)

end SpectralPoint
end WireTensor

end VPVNP
end Computability
end OAI
