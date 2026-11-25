import OAI.Computability.NearSquareRoot.InterchangeStageLift
import OAI.Computability.NearSquareRoot.InterchangeStageTransport

/-!
# Specializing address changes supported on selected physical fields

On a selected output field, a selected input basis vector gives the small
matrix entry. A basis vector outside the selection has zero projection onto
the selected fields. On the unselected outputs the extended map is the identity.
This accounts for both directions of the physical change of coordinates.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange
open IntegerMultiplication.Port InterchangeStageLift

/-- Flat field coordinates and P192's physical two-wing address. -/
def duplexCoords (J R : Type) [CommRing R] : (Spot J → R) ≃ₗ[R] Duplex J R where
  toFun x := (fun j => x (false,j), fun j => x (true,j))
  invFun := hear
  left_inv x := by funext u; rcases u with ⟨_ | _, j⟩ <;> rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem hear_duplexCoords {J R : Type} [CommRing R] (x : Spot J → R) (u : Spot J) :
    hear (duplexCoords J R x) u = x u := by rcases u with ⟨_ | _, j⟩ <;> rfl

/-- Express a physical address permutation in its flat field coordinates. -/
def coordinateAddress {J R : Type} [CommRing R] (F : Duplex J R ≃ₗ[R] Duplex J R) :
    (Spot J → R) ≃ₗ[R] (Spot J → R) :=
  ((duplexCoords J R).trans F).trans (duplexCoords J R).symm

@[simp] theorem coordinateAddress_apply {J R : Type} [CommRing R]
    (F : Duplex J R ≃ₗ[R] Duplex J R) (x : Spot J → R) (u : Spot J) :
    coordinateAddress F x u = hear (F (duplexCoords J R x)) u := rfl

@[simp] theorem coordinateAddress_symm {J R : Type} [CommRing R]
    (F : Duplex J R ≃ₗ[R] Duplex J R) : (coordinateAddress F).symm = coordinateAddress F.symm := rfl

@[simp] theorem coordinateAddress_trans {J R : Type} [CommRing R]
    (F G : Duplex J R ≃ₗ[R] Duplex J R) :
    (coordinateAddress F).trans (coordinateAddress G) = coordinateAddress (F.trans G) := by
  apply LinearEquiv.ext
  intro x
  simp [coordinateAddress]

theorem coordinateAddress_injective {J R : Type} [CommRing R] :
    Function.Injective (coordinateAddress (J := J) (R := R)) := by
  intro F G h
  apply LinearEquiv.ext
  intro x
  have := congrArg (fun e : (Spot J → R) ≃ₗ[R] (Spot J → R) =>
    duplexCoords J R (e ((duplexCoords J R).symm x))) h
  simpa [coordinateAddress] using this

private theorem supported_symm {I J R : Type} [CommRing R] (slot : I ↪ Spot J)
    (F : (I → R) ≃ₗ[R] (I → R)) : (linearEquiv slot F).symm = linearEquiv slot F.symm := by
  ext x <;> rfl

variable {I J : Type} [DecidableEq I] [DecidableEq J] (slot : I ↪ Spot J)

private theorem view_single {R : Type} [CommRing R] (b : I) :
    view slot (duplexCoords J R (Pi.single (slot b) 1)) = Pi.single b 1 := by
  funext i
  simp [view, Pi.single_apply]

omit [DecidableEq I] in
private theorem view_outside_single {R : Type} [CommRing R] (j : Spot J) (hj : ∀ b, j ≠ slot b) :
    view slot (duplexCoords J R (Pi.single j 1)) = 0 := by
  funext i
  simp [view, (hj i).symm]

variable [Fintype I] [Fintype J] {R : Type} [CommRing R]

private theorem supported_forward {F : (I → ℚ) ≃ₗ[ℚ] (I → ℚ)} {G : (I → R) ≃ₗ[R] (I → R)}
    (h : MatrixToken (addressMatrix F) (addressMatrix G)) :
    MatrixToken (addressMatrix (coordinateAddress (linearEquiv slot F)))
      (addressMatrix (coordinateAddress (linearEquiv slot G))) := by
  intro i j
  change Token (hear (update slot F (duplexCoords J ℚ (Pi.single j 1))) i)
    (hear (update slot G (duplexCoords J R (Pi.single j 1))) i)
  by_cases hi : ∃ a, slot a = i
  · obtain ⟨a, rfl⟩ := hi
    rw [update_selected, update_selected]
    by_cases hj : ∃ b, slot b = j
    · obtain ⟨b, rfl⟩ := hj
      rw [view_single, view_single]
      exact h a b
    · have hx : ∀ b, j ≠ slot b := fun b e => hj ⟨b,e.symm⟩
      simpa only [view_outside_single slot j hx, map_zero, Pi.zero_apply] using
        (Token.zero : Token 0 (0 : R))
  · have hx : ∀ a, i ≠ slot a := fun a e => hi ⟨a,e.symm⟩
    rw [update_outside _ _ _ _ hx, update_outside _ _ _ _ hx, hear_duplexCoords, hear_duplexCoords]
    by_cases e : i = j
    · subst j; simpa using (Token.unit : Token 1 (1 : R))
    · simpa [e] using (Token.zero : Token 0 (0 : R))

/-- A specialized coordinate change can be extended along any injection into
the physical fields, keeping every spectator field fixed in both directions. -/
theorem AddressToken.supported {F : (I → ℚ) ≃ₗ[ℚ] (I → ℚ)} {G : (I → R) ≃ₗ[R] (I → R)}
    (h : AddressToken F G) :
    AddressToken (coordinateAddress (linearEquiv slot F)) (coordinateAddress (linearEquiv slot G)) :=
  ⟨supported_forward slot h.forward, by
    simpa only [coordinateAddress_symm, supported_symm] using supported_forward slot h.backward⟩

end Interchange

end NearSquareRoot
end Computability
end OAI
