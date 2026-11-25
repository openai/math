import OAI.Hierarchy.GridThroughPlacement
import OAI.Hierarchy.GridIdentity
import OAI.Hierarchy.GridSum
import OAI.Hierarchy.CatalystSubstitutionPinned

namespace OAI
/-! # Cell-dependent pinned tensors in the reuse grid

The pins may differ at every cell. The expansion uses the same wiring for all
cell words, and every nonempty error set pays at least one copy of the gap.
-/

noncomputable section
namespace Hierarchy
open Catalyst CatalystSubstitution UniversalGrid GridLens
open LinearAlgebra.SpectralBooks
open scoped BigOperators Classical

namespace UniversalGrid.Wiring
variable {F : Type*} [Field F] {E A : Type} {L : ℕ}

/-- Each selected occurrence uses its own error against its own exact table. -/
def changeCells (base actual : Fin L → (A → Bool) → F) (S : Finset (Fin L)) (i : Fin L) :
    (A → Bool) → F := if i ∈ S then actual i - base i else base i

theorem mixedEval_difference (W : Wiring E A L) (base actual : Fin L → (A → Bool) → F) :
    W.mixedEval actual - W.mixedEval base =
      ∑ S : {S : Finset (Fin L) // S ≠ ∅}, W.mixedEval (changeCells base actual S.val) := by
  funext x
  rw [Finset.sum_apply x Finset.univ (fun S : {S : Finset (Fin L) // S ≠ ∅} =>
    W.mixedEval (changeCells base actual S.val))]
  unfold mixedEval
  rw [Pi.sub_apply, ← Finset.sum_sub_distrib, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  by_cases legal : ∀ uv ∈ W.equal, bit x h uv.1 = bit x h uv.2
  · simp only [ite_eq_left legal]
    rw [GridSum.expand]
    apply Finset.sum_congr (by ext s; simp)
    intro S _
    symm
    rw [← Finset.prod_mul_prod_compl S.val (fun i =>
      changeCells base actual S.val i (fun j => bit x h (W.pin i j)))]
    congr 1
    · exact Finset.prod_congr rfl (fun i hi => by simp [changeCells,hi])
    · apply Finset.prod_congr (by ext i; simp)
      intro i hi
      have hn : i ∉ S.val := by simpa using hi
      simp [changeCells,hn]
  · simp only [ite_eq_right legal,sub_self,Finset.sum_const_zero]
end UniversalGrid.Wiring

namespace GridThrough.Program
variable {F : Type*} [Field F] {k p n E : ℕ}

/-- Spectral value bound summed across an actual grid with differently pinned
approximation networks in its cells, all using one directional through format. -/
theorem pinned_product_error (X : Approximation F k p) (P : Program (Fin E) n 0 X.width)
    (pin : Fin ((n+1)^k) → Fin p → Bool) (f : (Fin p → Bool) → F) {D : ℝ}
    (gap : X.PointwiseGap f D) (hD : 0 < D) [Nonempty (Fin E)] [Nontrivial (Fin k × Bool)]
    (R : ℝ) (far : 8*((n:ℝ)+1) ≤ R) (Q : SpectralPlacementPrices F (Space k)) :
    let actual := P.wiring.mixedEval (fun i => (pinWord X (pin i)).coeff)
    let exactCells := P.wiring.mixedEval (fun i => ideal X.width (fun _ : Fin 0 → Bool => f (pin i)))
    actual - exactCells = 0 ∨
      Q.price (GridDiagonal.raw (actual - exactCells)) (fun u => GridDiagonal.focus R (P.direction u.1,u.2)) ≤
        2*R*E + 18*((k-1:ℕ):ℝ)*E*((n:ℝ)+1)^2/R - D + 2*k*R*((n+1)^k : ℕ) := by
  let L := (n+1)^k
  let base (i : Fin L) := ideal X.width (fun _ : Fin 0 → Bool => f (pin i))
  let actual (i : Fin L) := (pinWord X (pin i)).coeff
  let rows (s : {s : Finset (Fin L) // s ≠ ∅}) := P.wiring.mixedEval (Wiring.changeCells base actual s.val)
  let h := P.placement (pinWord X (fun _ => false)) R
  let ends (u : GridDiagonal.Ends (Fin E)) := GridDiagonal.focus R (P.direction u.1,u.2)
  let : Nonempty P.wiring.Sites := ⟨GridAddress.outputSite (Classical.arbitrary (Fin E),false)⟩
  have rowPrice (s : {s : Finset (Fin L) // s ≠ ∅}) (nz : rows s ≠ 0) :
      Q.price (GridDiagonal.raw (rows s)) ends ≤
        2*R*E + 18*((k-1:ℕ):ℝ)*E*((n:ℝ)+1)^2/R - D := by
    let cells := Wiring.changeCells base actual s.val
    let T := 2 * ∑ j, (X.width j : ℝ)
    have bound (i : Fin L) :
        Q.price (CorrectionProducts.raw (cells i)) (P.wiring.cellAt h.position i) ≤
          T - (if i ∈ s.val then D else 0) := by
      rw [h.cell_eq]
      let shift (z : Space k) := cellCenter (h.cell i) + z
      have iso : Isometry shift := by
        apply Isometry.of_dist_eq
        intro u v
        simp only [shift,dist_eq_norm]
        congr 1
        abel
      by_cases bad : i ∈ s.val
      · have discount := (pinWord X (pin i)).gap_at (pinWord_gap X (pin i) f gap) Q shift iso
        have nzcell := P.wiring.cells_nonzero_of_mixedEval cells nz i
        have eqCell : cells i = ((pinWord X (pin i)).error (fun _ => f (pin i))).coeff := by
          simp [cells,Wiring.changeCells,bad,actual,base,Approximation.error]
        rw [eqCell] at nzcell ⊢
        rw [ite_eq_left bad]
        have paid := discount.resolve_left nzcell
        convert paid using 1; first | rfl'
      · simp only [cells,Wiring.changeCells,ite_eq_right bad,sub_zero]
        exact CorrectionBenchmark.price_le (Q.pullback shift iso) X.width (base i)
    have bounds := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => bound i)
    have saved : (∑ i : Fin L, if i ∈ s.val then D else 0) = (s.val.card:ℝ)*D := by
      simp [Finset.sum_ite_mem, nsmul_eq_mul]
    rw [Finset.sum_sub_distrib,saved] at bounds
    have geom := (equality_cost_add_catalysts_le P.direction h.row R X.width h.cell
      (P.wiring.edgeAt h.position) h.paths).trans (total_rail_cost_le P.direction h.row R far)
    change (∑ i, dist (P.wiring.edgeAt h.position i false) (P.wiring.edgeAt h.position i true)) +
      (∑ _ : Fin L, T) ≤ _ at geom
    have wired := P.wiring.mixedEval_price_le Q h.position cells nz
    rw [h.focus] at wired
    have one : 1 ≤ (s.val.card : ℝ) := by exact_mod_cast (Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr s.property))
    change Q.price (GridDiagonal.raw (P.wiring.mixedEval cells)) _ ≤ _
    linarith [mul_le_mul_of_nonneg_right one hD.le]
  change P.wiring.mixedEval actual - P.wiring.mixedEval base = 0 ∨ _
  rw [P.wiring.mixedEval_difference base actual]
  change ∑ s, rows s = 0 ∨ Q.price (GridDiagonal.raw (∑ s, rows s)) ends ≤ _
  by_cases zero : ∑ s, rows s = 0
  · exact Or.inl zero
  right
  have hR : 0 < R := by linarith [Nat.cast_nonneg (α:=ℝ) n]
  let y : Fin k × Bool ↪ Space k := ⟨GridDiagonal.focus R, GridDiagonal.focus_injective hR⟩
  let atSite : GridDiagonal.Ends (Fin E) → Fin k × Bool := fun u => (P.direction u.1,u.2)
  obtain ⟨s,nz,price⟩ := GridSum.price_sum Q y atSite rows zero
  have count : Fintype.card {s : Finset (Fin L) // s ≠ ∅} ≤ 2^L :=
    (Fintype.card_subtype_le _).trans (by simp)
  have pos : 0 < Fintype.card {s : Finset (Fin L) // s ≠ ∅} := Fintype.card_pos_iff.mpr ⟨s⟩
  have lg : Real.logb 2 (Fintype.card {s : Finset (Fin L) // s ≠ ∅}) ≤ L := by
    have z := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (by exact_mod_cast pos)
      (show (Fintype.card {s : Finset (Fin L) // s ≠ ∅} : ℝ) ≤ (2:ℝ)^L by exact_mod_cast count)
    simpa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] using z
  have scale := mul_le_mul_of_nonneg_left lg (Q.diagonal_pos y).le
  have star := mul_le_mul_of_nonneg_right (GridDiagonal.focus_scale Q R hR.le) (Nat.cast_nonneg (α:=ℝ) L)
  exact price.trans (add_le_add (rowPrice s nz) (scale.trans star))

end GridThrough.Program
end Hierarchy

end
end OAI
