import OAI.Computability.BorderVNP.CoverMotionFibers
import OAI.Computability.BorderVNP.CoverLorentzPlaneTile
import OAI.Computability.BorderVNP.CoverFrameCoordinates

/-!
# Relative position tables for moving whole networks

Normalize the position of a frame into the tie-resolved base tile, retaining
its direction. One finite table, indexed by the low residue and relative
segment type, gives the new relative frame and an integral tile carry. The
modular correction supplies the other factor of the output tile address.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

open UpperHalfPlane Set BorderVNP.Hecke

/-- Unique quaternion moving a position into the tie-resolved base tile. -/
noncomputable def toBaseTile (z : UpperHalfPlane) : gamma 1 :=
  (existsUnique_mem_planeTile 0 z).exists.choose

/-- The chosen quaternion puts the position in the exact tile. -/
theorem toBaseTile_mem (z : UpperHalfPlane) : gammaSL 1 (toBaseTile z) • z ∈ planeTile 0 :=
  (existsUnique_mem_planeTile 0 z).exists.choose_spec

/-- Multiplying a position by a lattice element changes its normalization by the inverse element. -/
theorem toBaseTile_smul (b : gamma 1) (z : UpperHalfPlane) :
    toBaseTile (gammaSL 1 b • z) = toBaseTile z * b⁻¹ := by
  apply (existsUnique_mem_planeTile 0 (gammaSL 1 b • z)).unique (toBaseTile_mem _)
  rw [map_mul, map_inv, mul_smul, inv_smul_smul]
  exact toBaseTile_mem z

/-- Representative retaining the actual direction after translating the position into the base tile. -/
noncomputable def relativeFrame (x : SL) : SL := gammaSL 1 (toBaseTile (x • I)) * x

/-- Integral tile carry of a frame. -/
noncomputable def frameCarry (x : SL) : gamma 1 := (toBaseTile (x • I))⁻¹

/-- Recover the exact frame from the carry and its representative, including on seams. -/
theorem carry_mul_relative (x : SL) : gammaSL 1 (frameCarry x) * relativeFrame x = x := by
  simp [frameCarry, relativeFrame]

/-- The relative frame lies over the position tile. -/
theorem relativeFrame_mem (x : SL) : relativeFrame x • I ∈ planeTile 0 := by
  rw [relativeFrame,mul_smul]
  exact toBaseTile_mem _

/-- An integral deck translation changes only the tile address. -/
theorem relativeFrame_translate (b : gamma 1) (x : SL) :
    relativeFrame (gammaSL 1 b * x) = relativeFrame x := by
  simp [relativeFrame, mul_smul, toBaseTile_smul, mul_assoc]

/-- Carries transform by the same integral translation as the full frame. -/
theorem frameCarry_translate (b : gamma 1) (x : SL) :
    frameCarry (gammaSL 1 b * x) = b * frameCarry x := by
  simp [frameCarry, mul_smul, toBaseTile_smul]

/-- Low-key table for a fixed relative type. Its frame data are independent of the depth. -/
noncomputable def movedLowFrame (g : SL) {a : ℕ} (low : Deck (1+2*a)) (frame : SL) : SL :=
  g * ((deckTileEquiv (1+2*a) low).out : SL) * frame

private theorem moved_low_factor {g : SL} {a : ℕ} (hg : Clears g a) (b : gamma 1) (frame : SL) : g * (gammaSL 1 b * frame) = gammaSL 1 (baseFrame.symm (correction hg (baseFrame b))) *
      movedLowFrame g (b : Deck (1+2*a)) frame := by
    change g * (gammaSL 1 b * frame) = (baseFrame (baseFrame.symm (correction hg (baseFrame b))) : SL) *
      (g * (lowRepresentative a (baseFrame b) : SL) * frame)
    rw [baseFrame.apply_symm_apply, ← mul_assoc (correction hg (baseFrame b) : SL), correction_formula, mul_assoc]
    rfl

/-- The relative frame after motion is exactly the low-table representative. -/
theorem moved_relative_eq {g : SL} {a : ℕ} (hg : Clears g a) (b : gamma 1) (frame : SL) :
    relativeFrame (g * (gammaSL 1 b * frame)) =
      relativeFrame (movedLowFrame g (b : Deck (1+2*a)) frame) := by
  rw [moved_low_factor hg b frame, relativeFrame_translate]

/-- The low table supplies a finite displacement; the modular correction accounts for
the remaining high digits. Together they give the actual output tile of every frame. -/
theorem moved_carry_eq {g : SL} {a d : ℕ} (hg : Clears g a) (hd : 1 ≤ d)
    (b : gamma 1) (frame : SL) :
    (frameCarry (g * (gammaSL 1 b * frame)) : Deck (d+2*a)) =
      placedTile hg hd (fun low => (frameCarry (movedLowFrame g low frame) : Deck (d+2*a)))
        (b : Deck (d+2*a+2*a)) := by
  rw [moved_low_factor hg b frame, frameCarry_translate, QuotientGroup.mk_mul, placedTile]
  congr 1

/-- Finite relative-type catalogs are closed under a fixed finite motion list,
uniformly over all deep levels and all tile addresses. -/
theorem finite_relative_catalog {a : ℕ} {M T : Type*} [Finite M] [Finite T]
    (motion : M → SL) (hg : ∀ i, Clears (motion i) a) (typeFrame : T → SL) :
    ∃ S : Set SL, S.Finite ∧ ∀ i t (b : gamma 1),
      relativeFrame (motion i * (gammaSL 1 b * typeFrame t)) ∈ S := by
  let f (v : M × Deck (1+2*a) × T) := relativeFrame (movedLowFrame (motion v.1) v.2.1 (typeFrame v.2.2))
  refine ⟨range f,finite_range f,?_⟩
  intro i t b
  exact ⟨(i,(b : Deck (1+2*a)),t),(moved_relative_eq (hg i) b (typeFrame t)).symm⟩

end Cover.Frame

end BorderVNP
end Computability
end OAI
