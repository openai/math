import OAI.Hierarchy.FixedGraphForcing
import OAI.Hierarchy.ForcedRankSums
import OAI.Hierarchy.OrthogonalCutLoad
import OAI.Hierarchy.GraphWirePrice

namespace OAI
/-! # A fixed family of cuts with large orthogonal load forces large summand rank -/

namespace Hierarchy.IncidenceGraph

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators Classical

/-- Rebuilding a raw tensor with another enumeration of each finite leg preserves it. -/
theorem raw_with_finiteLeg {I : Type} {F : Type*} (T : Raw.{0} I F)
    (fin : ∀ i, Fintype (T.Leg i)) : (⟨T.Leg, fin, T.coeff⟩ : Raw.{0} I F) = T := by
  cases T with
  | mk legs original coeff =>
    have eq : fin = original := Subsingleton.elim _ _
    cases eq
    rfl

/-- The rank threshold holds uniformly in the edge alphabet once the graph,
the finite menu of cuts, and its flat are fixed. -/
theorem fixed_cut_family_hard (F : Type*) [Field F] (G : IncidenceGraph) [Nonempty G.E]
    (P : HomogeneousFlat F (Fintype.card G.E)) (C : Finset (Finset G.V)) (b k : ℕ)
    (crosses : ∀ U∈C, b ≤ (G.boundaryEdges U).card) (slope : (k:ℝ)+1 < Real.sqrt b) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℕ,
      (equalityWireRaw G.E F n).coeff ∈ affineZariskiClosure
        (ABPFirstCut.rankSumsOn (fun U : C => ABPFirstCut.legsOfCut G.portOwner U.val) t) →
      n^k < t := by
  classical
  let I := G.E × Bool
  let J := ↥C
  let x := G.orthogonalSite
  let δ := P.prices.price (Raw.diagonal I F (Fin 2)) x
  let B := |1 + δ*Real.logb 2 (Fintype.card J)|
  let A := 2*(Fintype.card I:ℝ)
  have hA : 0≤A := by dsimp [A]; positivity
  obtain ⟨N, growth⟩ := fixedGraph_eventually_superpower A B (Real.sqrt b) k hA (abs_nonneg _) slope
  refine ⟨max N 2, ?_⟩
  intro n hn t closure
  have hn2 : 2≤n := (le_max_right ..).trans hn
  have pos : 0<n := by omega
  let w := Real.logb 2 n
  have hw : 0≤w := Real.logb_nonneg (by norm_num) (by exact_mod_cast (show 1≤n by omega))
  let cuts (U : J) := ABPFirstCut.legsOfCut G.portOwner U.val
  have unit (i : I) : ‖x i‖ = 1 := by
    obtain ⟨e,z⟩ := i
    cases z
    · exact G.orthogonalSite_unit e
    · simpa [x,G.orthogonalSite_antipodal] using G.orthogonalSite_unit e
  have loads (U : J) : Real.sqrt b*w ≤ ‖∑ i ∈ cuts U, Real.logb 2 (Fintype.card (Fin n)) • x i‖ := by
    change _ ≤ ‖∑ i ∈ Finset.univ.filter (fun p : G.E × Bool => G.portOwner p ∈ U.val),
      Real.logb 2 (Fintype.card (Fin n)) • G.orthogonalSite i‖
    rw [Fintype.card_fin, G.norm_orthogonal_cut U.val hw, mul_comm (Real.sqrt b)]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast crosses U.val U.property)) hw
  have price := equalityWireRaw_price_antipodal P.prices x n pos
    G.orthogonalSite_unit G.orthogonalSite_antipodal
  have force := @HomogeneousFlat.hard_load_le_of_rankSumsOn F _ I _ _ _
    (fun _ : I => Fin n) (fun _ => Fin.fintype n) J _ _ P x unit cuts t
    (equalityWireRaw G.E F n).coeff closure (equalityWireRaw_coeff_ne_zero G.E F n pos)
    (by
      exact (congrArg (fun T : Raw.{0} I F => P.prices.price T x)
        (raw_with_finiteLeg (equalityWireRaw G.E F n) (fun _ => Fin.fintype n))).trans
        (by simpa only [Fintype.card_fin] using price))
    (Real.sqrt b*w) loads 1 (by norm_num)
  apply growth n ((le_max_left ..).trans hn) t
  apply force.trans
  apply add_le_add le_rfl
  apply Real.sqrt_le_sqrt
  have total : (∑ _i : I, Real.logb 2 (Fintype.card (Fin n))) = (Fintype.card I:ℝ)*w := by
    simp only [w, Fintype.card_fin, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [total]
  change 2*((Fintype.card I:ℝ)*w)*(1+δ*Real.logb 2 (Fintype.card J)) ≤ A*w*B
  rw [←mul_assoc (2:ℝ)]
  exact mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg hA hw)


end Hierarchy.IncidenceGraph

end OAI
