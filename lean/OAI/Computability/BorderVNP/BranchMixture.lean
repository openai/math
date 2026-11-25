import OAI.Computability.BorderVNP.BranchMixtureSelection
import OAI.Computability.BorderVNP.BranchIncidenceRelation
import OAI.Computability.BorderVNP.BranchGraphBadLocus
import OAI.Computability.BorderVNP.BranchWeightedGraph
import OAI.Computability.BorderVNP.BranchGridExtension

/-!
# Finite intersection by a short tuple of weighted slices

For the actual graph chart, a bounded tuple of affine residuals is encoded in one
univariate polynomial. After adjoining its roots to the generic parameter algebra,
each graph coordinate obeys a bounded relation with the roots. A common finite
constant grid keeps one coefficient of every relation nonzero. Thus the entire
intersection is finite, including all retained points of the original graph fiber.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Branch

open MvPolynomial Incidence

variable {I K : Type*} [Field K] [IsAlgClosed K] [Fintype I] {h : ℕ}

/-- Side length sufficient for the simultaneous incidence coefficient exclusions. -/
def mixtureBound (h B n d : ℕ) : ℕ := B * n * ((h+1) * radius h B d)

omit [IsAlgClosed K] in
/-- Over a sufficiently large finite grid, the weighted equations admit exactly `h`
scalar specializations with a finite intersection on the graph. -/
theorem finite_weighted_graph_slice {E : Type*} [Field E] [Fintype E] (embed : E →+* K)
    (Y : I → MvPolynomial (Fin h) K) (k : Option (Fin h)) {d B : ℕ}
    (hY : ∀ i, (Y i).totalDegree ≤ d) (hh : 0 < h)
    (F : Polynomial (MvPolynomial (Option (Fin h) ⊕ I) K)) (hF : F.natDegree ≤ B)
    (hFc : ∀ j, (F.coeff j).totalDegree ≤ 1)
    (base : {v ∈ zeroLocus K (RingHom.ker (graphChartMap Y k)) | F.map (eval v) = 0}.Finite)
    (hsize : mixtureBound h B (Fintype.card (Option (Fin h) ⊕ I)) (d+1) < Fintype.card E) :
    ∃ a : Fin h → E, {v ∈ zeroLocus K (RingHom.ker (graphChartMap Y k)) |
      ∀ j, (F.map (eval v)).eval (embed (a j)) = 0}.Finite := by
  classical
  obtain ⟨den, num, hden, hd, hn, hg⟩ := graphValues_rational Y k hY
  let rrel (r : Fin B) (i : Option (Fin h) ⊕ I) :=
    exists_root_relation (affineParameter h K) (graphValues Y k) den num hden
      (hd.trans (by omega : 1 ≤ d+1)) hn hg (X i) (F.coeff (r.val+1))
      (fun j : Fin (r.val+1) => F.coeff j.val) (by simp) (hFc _) (fun _ => hFc _)
  choose W hw hdeg hspec using rrel
  have hD (r : Fin B) (i : Option (Fin h) ⊕ I) :
      (W r i).totalDegree ≤ (h+1)*radius h B (d+1) := by
    apply (hdeg r i).trans
    unfold radius
    gcongr
    exact r.isLt
  obtain ⟨a, ha⟩ := finite_coordinate_strata embed W _ hw hD (by simpa [mixtureBound] using hsize)
  refine ⟨a, (base.union ha).subset ?_⟩
  intro v hv
  by_cases he : F.map (eval v) = 0
  · exact Or.inl ⟨hv.1, he⟩
  obtain ⟨r, hr, hroots⟩ := top_stratum_of_roots F v (embed ∘ a) hh hF he hv.2
  apply Or.inr
  apply Set.mem_iUnion.mpr
  refine ⟨r, fun i => ?_⟩
  have hgraph (p : MvPolynomial (Option (Fin h) ⊕ I) K) (hp : aeval (graphValues Y k) p = 0) :
      eval v p = 0 := by
    rw [← aeval_eq_eval]
    apply hv.1 p
    rw [← graphChartAlgHom_toRingHom]
    exact hp
  simpa only [eval_X] using hspec r i v (embed ∘ a) hgraph hr hroots

/-- Choose the entire tuple in an extension of singly exponential cardinality.
Every retained point survives all the cuts. -/
theorem exists_short_weighted_slice (E₀ : Type*) [Field E₀] [Fintype E₀] [Algebra E₀ K]
    (Y : I → MvPolynomial (Fin h) K) (k : Option (Fin h)) {d B : ℕ}
    (hY : ∀ i, (Y i).totalDegree ≤ d) (hh : 0 < h)
    (F : Polynomial (MvPolynomial (Option (Fin h) ⊕ I) K)) (hF : F.natDegree ≤ B)
    (hFc : ∀ j, (F.coeff j).totalDegree ≤ 1)
    (base : {v ∈ zeroLocus K (RingHom.ker (graphChartMap Y k)) | F.map (eval v) = 0}.Finite) :
    ∃ (E : IntermediateField E₀ K), Finite E ∧ Nat.card E ≤ Fintype.card E₀ *
        max (mixtureBound h B (Fintype.card (Option (Fin h) ⊕ I)) (d+1)) 1 ∧
      ∃ a : Fin h → E,
        let cut := {v ∈ zeroLocus K (RingHom.ker (graphChartMap Y k)) |
          ∀ j, (F.map (eval v)).eval (a j : K) = 0}
        cut.Finite ∧ {v ∈ zeroLocus K (RingHom.ker (graphChartMap Y k)) | F.map (eval v) = 0} ⊆ cut := by
  obtain ⟨E, hf, hlo, hhi⟩ := exists_gridExtension E₀ K (mixtureBound h B _ (d+1))
  let := Fintype.ofFinite E
  obtain ⟨a, ha⟩ := finite_weighted_graph_slice E.subtype Y k hY hh F hF hFc base
    (by simpa only [Nat.card_eq_fintype_card] using hlo)
  exact ⟨E, hf, hhi, a, ha, fun _ hv => ⟨hv.1, by simp [hv.2]⟩⟩

end Branch

end BorderVNP
end Computability
end OAI
