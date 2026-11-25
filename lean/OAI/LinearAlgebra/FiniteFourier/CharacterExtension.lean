import OAI.LinearAlgebra.FiniteFourier.Transform

/-! # Character tables after extending a splitting field -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {G K L : Type*} [AddCommGroup G] [Fintype G] [Field K] [Field L]

/-- A field extension preserves both splitting assumptions on `G`. -/
theorem Admissible.map (h : Admissible G K) (f : K →+* L) : Admissible G L := by
  obtain ⟨hN, z, hz⟩ := h
  exact ⟨by simpa only [map_natCast, map_zero] using (f.injective.ne hN), ⟨f z, hz.map_of_injective f.injective⟩⟩

/-- Extending a character means applying the field embedding to each of its unit values. -/
def extendCharacter (f : K →+* L) (χ : Character G K) : Character G L :=
  (Units.map f.toMonoidHom).comp χ

omit [Fintype G] in
theorem injective_extendCharacter (f : K →+* L) : Function.Injective (extendCharacter (G := G) f) := by
  intro a b h
  apply DFunLike.ext
  intro x
  apply Units.map_injective (f := f.toMonoidHom) f.injective
  exact DFunLike.congr_fun h x

/-- In a splitting field all the characters are already present. -/
noncomputable def characterExtensionEquiv (h : Admissible G K) (f : K →+* L) :
    Character G K ≃ Character G L :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨injective_extendCharacter f, (card_character G K h).trans (card_character G L (h.map f)).symm⟩)

/-- Extending every entry of a Fourier matrix agrees with evaluating the extended characters. -/
theorem fourierMatrix_map (h : Admissible G K) (f : K →+* L) :
    (fourierMatrix G K).map f = (fourierMatrix G L).submatrix (characterExtensionEquiv h f) id := rfl

end FiniteFourier
end LinearAlgebra
end OAI
