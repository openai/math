import OAI.Computability.BorderVNP.CoverLorentzFrames
import OAI.Computability.BorderVNP.CoverHeckeCorrespondenceDomain
import Mathlib.Data.Prod.Lex

/-!
# Measurable fundamental tiles for the frame action

A compact window meets every orbit, and the window contains only finitely many
representatives of a given orbit. Taking the lexicographically least matrix in
each such finite set produces a bounded Borel tile with exact boundary choices.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover

open Matrix Set MeasureTheory
open scoped MatrixGroups

/-- The Borel σ-algebra on the real frame group. -/
local instance frameMeasurableSpace : MeasurableSpace SL(2,ℝ) := borel _
/-- The frame-group measurable structure is its topological Borel structure. -/
local instance frameBorelSpace : BorelSpace SL(2,ℝ) := ⟨rfl⟩

/-- Countability of the integral quaternion group follows from its four integer coordinates. -/
instance countableGamma (l : ℕ) : Countable (gamma l) := by
  apply Function.Injective.countable (f := fun u : gamma l => QuaternionAlgebra.equivTuple 2 0 3 u.val.val)
  exact (QuaternionAlgebra.equivTuple 2 0 3).injective.comp
    (Units.val_injective.comp Subtype.val_injective)

private def rankMatrix (g : SL(2,ℝ)) : ℝ ×ₗ ℝ ×ₗ ℝ ×ₗ ℝ :=
  toLex (g 0 0,toLex (g 0 1,toLex (g 1 0,g 1 1)))

private theorem rankMatrix_inj : Function.Injective rankMatrix := by
  intro g h he
  apply Subtype.ext
  have e : (g 0 0,(g 0 1,(g 1 0,g 1 1))) = (h 0 0,(h 0 1,(h 1 0,h 1 1))) := he
  simp only [Prod.mk.injEq] at e
  ext i j; fin_cases i <;> fin_cases j
  exacts [e.1,e.2.1,e.2.2.1,e.2.2.2]

private theorem rank_le_measurable (a : SL(2,ℝ)) :
    MeasurableSet {g : SL(2,ℝ) | rankMatrix g ≤ rankMatrix (a*g)} := by
  have hlt (i j : Fin 2) : MeasurableSet {g : SL(2,ℝ) | g i j < (a*g) i j} :=
    (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
  have heq (i j : Fin 2) : MeasurableSet {g : SL(2,ℝ) | g i j = (a*g) i j} :=
    (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet
  have hle : MeasurableSet {g : SL(2,ℝ) | g 1 1 ≤ (a*g) 1 1} :=
    (isClosed_le (by fun_prop) (by fun_prop)).measurableSet
  simp only [rankMatrix,Prod.Lex.toLex_le_toLex]
  exact (hlt 0 0).union ((heq 0 0).inter ((hlt 0 1).union ((heq 0 1).inter
    ((hlt 1 0).union ((heq 1 0).inter hle)))))

private theorem finite_window (l : ℕ) {K : Set SL(2,ℝ)} (hK : IsCompact K) (g : SL(2,ℝ)) :
    {u : gamma l | gammaSL l u * g ∈ K}.Finite := by
  let L := (fun a : SL(2,ℝ) => (a*g⁻¹).val) '' K
  have hL : IsCompact L := hK.image (by fun_prop)
  let v (u : gamma l) := u.val.val
  have hi : Function.Injective v := Units.val_injective.comp Subtype.val_injective
  apply ((split_preimage_compact_finite hL).preimage hi.injOn).subset
  intro u hu
  refine ⟨gammaSL l u*g,hu,?_⟩
  change (gammaSL l u*g*g⁻¹).val = (gammaSL l u).val
  rw [mul_inv_cancel_right]

/-- A bounded Borel fundamental set for the actual right cosets of each quaternion level group. -/
theorem exists_measurable_frame_tile (l : ℕ) :
    ∃ K D : Set SL(2,ℝ), IsCompact K ∧ D ⊆ K ∧ MeasurableSet D ∧
      BorderVNP.Hecke.ExactTile (frameGroup l) D := by
  classical
  obtain ⟨K,hK,hmeet⟩ := exists_compact_representatives l
  let D := {g : SL(2,ℝ) | g ∈ K ∧ ∀ u : gamma l,
    gammaSL l u*g ∈ K → rankMatrix g ≤ rankMatrix (gammaSL l u*g)}
  refine ⟨K,D,hK,fun _ h => h.1,?_,?_⟩
  · change MeasurableSet (K ∩ {g : SL(2,ℝ) | ∀ u : gamma l, _})
    apply hK.isClosed.measurableSet.inter
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro u
    change MeasurableSet {g : SL(2,ℝ) | g ∈ (fun z => gammaSL l u*z) ⁻¹' K →
      rankMatrix g ≤ rankMatrix (gammaSL l u*g)}
    rw [show {g : SL(2,ℝ) | g ∈ (fun z => gammaSL l u*z) ⁻¹' K →
      rankMatrix g ≤ rankMatrix (gammaSL l u*g)} =
      ((fun z => gammaSL l u*z) ⁻¹' K)ᶜ ∪ {g | rankMatrix g ≤ rankMatrix (gammaSL l u*g)} by
        ext; simp [imp_iff_not_or]]
    exact ((hK.isClosed.preimage (by fun_prop)).measurableSet.compl).union (rank_le_measurable _)
  · intro g
    let s := (finite_window l hK g).toFinset
    obtain ⟨j,hj⟩ := hmeet g
    have hs : s.Nonempty := ⟨j,(finite_window l hK g).mem_toFinset.mpr hj⟩
    obtain ⟨u,hu,hmin⟩ := s.exists_min_image (fun u => rankMatrix (gammaSL l u*g)) hs
    have hD : gammaSL l u*g ∈ D := by
      refine ⟨(finite_window l hK g).mem_toFinset.mp hu,?_⟩
      intro v hv
      have hmem : v*u ∈ s := (finite_window l hK g).mem_toFinset.mpr
        (by change gammaSL l (v*u)*g ∈ K; simpa only [map_mul,mul_assoc] using hv)
      simpa only [map_mul,mul_assoc] using hmin _ hmem
    refine ⟨⟨gammaSL l u,u,rfl⟩,hD,?_⟩
    rintro ⟨a,v,rfl⟩ hv
    change gammaSL l v*g ∈ D at hv
    have huv := hD.2 (v*u⁻¹)
    have hvu := hv.2 (u*v⁻¹)
    simp only [map_mul,map_inv,mul_assoc,inv_mul_cancel_left] at huv hvu
    exact Subtype.ext (mul_right_cancel (rankMatrix_inj (le_antisymm (hvu hD.1) (huv hv.1))))

end Cover

end BorderVNP
end Computability
end OAI
