import OAI.LinearAlgebra.SpectralBooks.ChordGraph.BoundedPatchReplacementClass
import OAI.LinearAlgebra.SpectralBooks.BoundedPatchReplacementMaps
import OAI.LinearAlgebra.SpectralBooks.BoundedPatchReplacementTerm
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchBatchCost

/-! # Replacing a bounded polygon patch by an ordinary sum of ordered trees

The straightening matrices depend only on the coordinate wiring. The entries of
the corner tables can in particular be independent polynomial indeterminates.
One division-free arithmetic program computes every entry of every pruned tree.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical BigOperators

namespace ChordGraph

open SiteTensor PlanarPatch Arithmetic

private theorem transformed_cost (w : ℕ) : (2^(4*w)+1)*2+1 ≤ 2^(7*(w+1)) := by
  have h : 1 ≤ 2^(4*w) := Nat.one_le_pow _ _ (by decide)
  calc
    _ ≤ 2^(4*w)*2^3 := by omega
    _ = 2^(4*w+3) := (pow_add 2 _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

/-- The uniform bound holds for all polynomial inputs in a finite local format
representing the wiring. The final polygon site carries the distinguished output
stub, and each of the other stubs appears in the polygon order. -/
theorem bounded_replacement_in_format {F : Type*} [Field F]
    (noPlane : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 2))))
    (K : ℕ) (hK : 0 < K) :
    ∃ c : ℕ, ∀ {n w : ℕ}, 0 < n → n+1 ≤ 5*K → ∀ (g : Widths (n+1)),
      total g ≤ 4*K*w → (∀ i, load i g ≤ 4*w) →
      ∀ R : Raw.{0} (Fin (n+1)) F, ofRaw R = graphClass F g →
      (∀ i, Fintype.card (R.Leg i) ≤ 2^(4*w)) →
      ∀ {V I : Type} {d : V → ℕ} (U : ∀ i, CornerTable (MvPolynomial I F) d (R.Leg i))
        (v : V), (U (Fin.last n)).label = some v →
      (∀ i b, (U i).label = some b → d b ≤ 2^(8*w)) → (∀ i, (U i).FormulaBound 1) →
      let labels := (List.finRange n).filterMap (fun i => (U i.castSucc).label)
      2 ≤ labels.length →
      ∃ (L : ℕ) (u : Fin L → TrivalentTree (MvPolynomial I F) d (d v)),
        L ≤ 2^(w+c) ∧
        (∀ j, (u j).labels = labels ∧ (u j).Bounded (2^(8*w)) ∧
          (u j).vertices + 2 = labels.length + 1) ∧
        (∀ j, (u j).FormulaBound (2^((20*(2*(5*K)+1)+7)*(w+1)))) ∧
        (∀ x, tablePairing MvPolynomial.C R.coeff (fun i => (U i).value x) =
          ∑ j, (u j).eval x (x v)) ∧
        ∃ (r : ℕ) (p : Program F I r) (out : (j : Fin L) → (u j).Entry → Fin r),
          (∀ j e, registerPolynomial p (out j e) = (u j).entry e) ∧
          p.cost ≤ 2^((c+1+5*K+24+20*(2*(5*K)+1)+7)*(w+1)) := by
  obtain ⟨c,hc⟩ := bounded_patch_maps noPlane K hK
  refine ⟨c,?_⟩
  intro n w hn hnk g hg hload R hR hcard V I d U v hv hlabel hform labels hlen
  obtain ⟨L,t,M,hL,hterms,heq⟩ := hc n hnk w g hg R hR (raw F) (ofRaw_raw F)
  let U' (j : Fin L) (i : Fin (n+1)) := (U i).transpose (fun b a => MvPolynomial.C (M j i b a))
  have hlabel' (j i) : (U' j i).label = (U i).label := CornerTable.label_transpose _ _
  have hf (j i) : (U' j i).FormulaBound ((2^(4*w)+1)*2) := by
    have h := (U i).transpose_formulaBound (M j i) (hform i)
    cases hU : U i with
    | scalar f =>
      simp only [U', hU, CornerTable.transpose, CornerTable.FormulaBound] at *
      exact fun b => (h b).mono (by gcongr; exact hcard i)
    | stub s f =>
      simp only [U', hU, CornerTable.transpose, CornerTable.FormulaBound] at *
      exact fun b o => (h b o).mono (by gcongr; exact hcard i)
  choose trees hlabels hb hh hf' heval using fun j => noncrossing_term_tree hn (t j)
    (hterms j).1 (fun i => ((hterms j).2 i).trans (hload i)) (U' j) v
    ((hlabel' j _).trans hv) (fun i b h => hlabel i b ((hlabel' j i).symm.trans h)) (hf j)
  have hl (j) : (trees j).labels = labels := by
    simpa only [hlabel', labels] using hlabels j
  have hln : labels.length ≤ n := by
    exact (List.length_filterMap_le _ _).trans_eq List.length_finRange
  obtain ⟨u,hu,hformulas,r,p,out,he,hcost⟩ := compile_pruned_patch_with_formulas (w := w) (D := 2^(8*w)) (C := (2^(4*w)+1)*2+1) (c := c) (a := 7) (H := 5*K)
    (n := 5*K) trees (by simpa only [Fintype.card_fin] using hL) le_rfl (Nat.le_add_left 1 _) (transformed_cost w) hb hf'
    (fun j => (hh j).trans (Nat.le_trans (Nat.le_succ n) hnk)) (fun j => (hl j).symm ▸ hlen)
    (fun j => by rw [hl]; exact hln.trans ((Nat.le_succ _).trans (hnk.trans (Nat.le_succ _))))
  refine ⟨L,u,hL,fun j => ⟨(hu j).1.trans (hl j),(hu j).2.1,by rw [(hu j).2.2.1, hl]⟩,
    hformulas,?_,r,p,out,he,hcost⟩
  let z (j : Fin L) (b : ∀ i, R.Leg i) :=
    ∑ a, (raw F (t j)).coeff a * ∏ i, M j i (b i) (a i)
  have hz : R.coeff = ∑ j, z j := by
    ext x
    rw [Finset.sum_apply]
    exact heq x
  intro x
  rw [hz, tablePairing_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [congrFun ((hu j).2.2.2 x) (x v), heval]
  rw [tablePairing_transpose MvPolynomial.C (z j) (raw F (t j)).coeff (M j) (fun _ => Finset.sum_congr (by ext; simp) (fun _ _ => rfl))]
  congr 1
  funext i a
  exact ((U i).value_transpose (fun b s => MvPolynomial.C (M j i b s)) x a).symm

end ChordGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
