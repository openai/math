import OAI.Computability.BorderVNP.CoverDeckTower
import OAI.Computability.BorderVNP.CoverMotionAddress

/-!
# Modular labels for geometric tiles and finite motion tables

The congruence quotient by left cosets and the frame construction's right
cosets represent exactly the same tile. Normality is essential here: the
correspondence takes each representative to its matrix image, without
inverting it. Thus the group operation in the modular label is compatible
with the correction table of §5.2.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.Frame

/-- The faithful matrix parametrization of the base lattice. -/
noncomputable def baseFrame : gamma 1 ≃* lattice 1 :=
  MonoidHom.ofInjective (gammaSL_injective 1)

private theorem mem_frame_iff (d : ℕ) (x : gamma 1) :
    gammaSL 1 x ∈ lattice d ↔ x.val ∈ gamma d := by
  constructor
  · rintro ⟨y,hy⟩
    have he : y.val = x.val := Units.ext (split_injective (congrArg Subtype.val hy))
    exact he ▸ y.property
  · intro hx
    exact ⟨⟨x.val,hx⟩, rfl⟩

/-- The deck group and the geometric frame tile addresses are in bijection
using the image of each integral quaternion representative. -/
noncomputable def deckTileEquiv (d : ℕ) : Deck d ≃ Tile d :=
  Quotient.congr baseFrame.toEquiv (fun x y => by
    rw [QuotientGroup.leftRel_apply,QuotientGroup.rightRel_apply]
    change x.val⁻¹*y.val ∈ gamma d ↔ gammaSL 1 y * (gammaSL 1 x)⁻¹ ∈ lattice d
    rw [← map_inv, ← map_mul, mem_frame_iff]
    exact ⟨(gammaNormal d).mem_comm, (gammaNormal d).mem_comm⟩)

/-- The correspondence on representatives has the same orientation as the
matrix motion in the manuscript. -/
theorem deckTileEquiv_rep (d : ℕ) (x : gamma 1) :
    deckTileEquiv d (x : Deck d) = tile d (baseFrame x) := rfl

/-- Four congruence coordinates test equality of geometric tile labels. -/
theorem tile_eq_iff_address (d : ℕ) (x y : gamma 1) :
    tile d (baseFrame x) = tile d (baseFrame y) ↔
      (addressHom d x).val = (addressHom d y).val := by
  rw [← deckTileEquiv_rep, ← deckTileEquiv_rep, (deckTileEquiv d).injective.eq_iff,
    ← (deckAddress_injective d).eq_iff, ← Units.val_inj]
  rfl

/-- The finite correction table acts directly on deck labels. -/
noncomputable def motionDeck {g : SL} {a d : ℕ} (hg : Clears g a) (hd : 1 ≤ d) :
    Deck (d+2*a) → Deck d :=
  (deckTileEquiv d).symm ∘ motionAddress hg hd ∘ deckTileEquiv (d+2*a)

/-- On an integral representative the transported correction has exactly the
geometric output address produced by the full frame formula. -/
theorem motionDeck_rep {g : SL} {a d : ℕ} (hg : Clears g a) (hd : 1 ≤ d) (x : gamma 1) :
    deckTileEquiv d (motionDeck hg hd (x : Deck (d+2*a))) =
      tile d (correction hg (baseFrame x)) := by
  simp only [motionDeck,Function.comp_apply,Equiv.apply_symm_apply,deckTileEquiv_rep,
    motionAddress_tile]

end Cover.Frame

end BorderVNP
end Computability
end OAI
