import OAI.Hierarchy.ProtocolRAMPrune

namespace OAI
/-! # Reading the named unordered graph from a controller's physical endpoints -/

namespace Hierarchy.ProtocolRAMEmit.Geometry
open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.ChordGraph
open TaggedPrune CorrectionFrame
open scoped BigOperators
variable {w n k h M den : ℕ} {b : Fin k → ℕ} {D : TaggedPrune.Layout h w b} {rows : Fin n → Row}
variable (G : Geometry D M den rows)

theorem installedWidths_eq_flip (A : PortGraph (Fin (D.last+1)) (Fin n))
    (ends : ∀ i : ActiveRows rows,
      (A.tail i.val = (rows i.val).leftSite (G.fits i) ∧ A.head i.val = (rows i.val).rightSite (G.fits i)) ∨
      (A.tail i.val = (rows i.val).rightSite (G.fits i) ∧ A.head i.val = (rows i.val).leftSite (G.fits i))) :
    AdaptiveProbe.installedWidths G.links.ends G.links.bits = A.chordWidths (fun i => (rows i).width) := by
  classical
  let f := fun i : Fin n => A.chordWidth i (rows i).width
  have active (i : ActiveRows rows) : (rows i.val).width • unitChord (G.edge i) = f i.val := by
    change _ = A.chordWidth i.val (rows i.val).width
    unfold PortGraph.chordWidth edge chord
    rcases ends i with ⟨tail,head⟩|⟨tail,head⟩
    all_goals
      simp only [tail,head,unitChord,Finsupp.smul_single,smul_eq_mul,mul_one]
      by_cases h : (rows i.val).endpoint < (rows i.val).opposite
      · have lr : (rows i.val).leftSite (G.fits i) < (rows i.val).rightSite (G.fits i) := h
        simp only [dite_eq_left h,dite_eq_left lr,dite_eq_right (not_lt.mpr lr.le)]
      · have lr : (rows i.val).rightSite (G.fits i) < (rows i.val).leftSite (G.fits i) :=
          show (rows i.val).opposite < (rows i.val).endpoint by have := G.distinct i; omega
        simp only [dite_eq_right h,dite_eq_left lr,dite_eq_right (not_lt.mpr lr.le)]
  have idle : (∑ i : {j : Fin n // ¬ 0<(rows j).width}, f i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have zero : (rows i.val).width=0 := Nat.eq_zero_of_not_pos i.property
    dsimp only [f]
    rw [zero]
    unfold PortGraph.chordWidth
    split_ifs <;> simp
  calc
    _ = ∑ j, f (activeIndex rows j).val :=
      Finset.sum_congr rfl fun j _ => active (activeIndex rows j)
    _ = ∑ i : ActiveRows rows, f i.val :=
      (Fintype.equivFin (ActiveRows rows)).symm.sum_comp (fun i => f i.val)
    _ = _ := by
      have split := Fintype.sum_subtype_add_sum_subtype (fun i : Fin n => 0<(rows i).width) f
      rw [idle,add_zero] at split
      exact split

end Hierarchy.ProtocolRAMEmit.Geometry

end OAI
