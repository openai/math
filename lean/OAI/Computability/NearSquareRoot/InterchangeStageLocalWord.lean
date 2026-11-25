import OAI.Computability.NearSquareRoot.InterchangeStagePrepare
import OAI.Computability.NearSquareRoot.InterchangeSupport
import OAI.Computability.NearSquareRoot.InterchangeSupportedToken

/-!
# A zero-price endpoint change in the original P192 slot order

The two main fields lie between the early complement and the late
differences. Thus the local endpoint matrix already has its unit lower
triangular order in the complete physical address.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeStageLift

open IntegerMultiplication.Port NearSquareRoot.Interchange NearSquareRoot.InterchangeSlots

variable {a c e m : ℕ}

theorem addressMatrix_endpointAddress {R : Type*} [CommRing R] {b : ℕ}
    (G : Matrix (Fin b) (Fin c) R) (D : Matrix (Fin e) (Fin b) R) :
    addressMatrix (endpointAddress G D) = endpointMatrix G D :=
  LinearMap.toMatrix'_toLin' _

/-- The free local arrow of a single queried rectangle. -/
noncomputable def endpointPiece (hce : c+e=a) (j : Fin m)
    (G : Matrix (Fin 2) (Fin c) ℚ) (D : Matrix (Fin e) (Fin 2) ℚ) :
    Support.Piece (Fin (a+m+a)) Fin.val where
  dim := c+(2+e)
  slot := rectSlots hce j
  change := endpointAddress G D
  free := true
  ordered := fun _ => active_order hce j
  lower := fun _ => addressMatrix_endpointAddress G D ▸ endpointMatrix_lower G D
  diagonal := fun _ => addressMatrix_endpointAddress G D ▸ endpointMatrix_diagonal G D

/-- As a supported word, its address has the desired effect at zero cost. -/
noncomputable def endpointWord (hce : c+e=a) (j : Fin m)
    (G : Matrix (Fin 2) (Fin c) ℚ) (D : Matrix (Fin e) (Fin 2) ℚ) :
    Support.Word (Fin (a+m+a)) Fin.val :=
  .atom (endpointPiece hce j G D)

@[simp] theorem endpointWord_price (hce : c+e=a) (j : Fin m)
    (G : Matrix (Fin 2) (Fin c) ℚ) (D : Matrix (Fin e) (Fin 2) ℚ) :
    (endpointWord hce j G D).price = 0 := rfl

theorem endpointWord_address (hce : c+e=a) (j : Fin m)
    (G : Matrix (Fin 2) (Fin c) ℚ) (D : Matrix (Fin e) (Fin 2) ℚ) :
    (endpointWord hce j G D).address.toEquiv =
      perm (rectSlots hce j) (endpointAddress G D).toEquiv := rfl

/-- Physical linear maps implementing the main pivot have a coordinate matrix
equal to the transposition matrix, at every radix. -/
theorem coordinateAddress_mainSwap {R : Type} [CommRing R] (a : ℕ) (j : Fin m)
    (F : Duplex (Fin (a+m+a)) R ≃ₗ[R] Duplex (Fin (a+m+a)) R)
    (h : F.toEquiv = perm (querySlots a j) (querySwap a R)) :
    coordinateAddress F = LinearEquiv.funCongrLeft R R
      (Equiv.swap (false,mainRank a j) (true,mainRank a j)) := by
  apply LinearEquiv.ext
  intro x
  funext u
  have hx := DFunLike.congr_fun h (duplexCoords _ R x)
  change F (duplexCoords _ R x) = update (querySlots a j) (querySwap a R) _ at hx
  rw [coordinateAddress_apply,hx,physical_main_swap]
  exact hear_duplexCoords x _

/-- The main physical pivot after specialization of a rational layout.
The hypotheses use only the rational address identity and the matrix token. -/
theorem specialize_mainSwap {R : Type} [CommRing R] (a : ℕ) (j : Fin m)
    (F : Duplex (Fin (a+m+a)) ℚ ≃ₗ[ℚ] Duplex (Fin (a+m+a)) ℚ)
    (G : Duplex (Fin (a+m+a)) R ≃ₗ[R] Duplex (Fin (a+m+a)) R)
    (h : F.toEquiv = perm (querySlots a j) (querySwap a ℚ))
    (hG : AddressToken (coordinateAddress F) (coordinateAddress G)) :
    G.toEquiv = perm (querySlots a j) (querySwap a R) := by
  rw [coordinateAddress_mainSwap a j F h] at hG
  have hplain := hG.unique (AddressToken.coordinate
    (Equiv.swap (false,mainRank a j) (true,mainRank a j)))
  apply Equiv.ext
  intro x
  apply hear_all
  intro u
  change hear (G x) u = hear (update (querySlots a j) (querySwap a R) x) u
  rw [physical_main_swap]
  exact congrArg (fun L : (Spot (Fin (a+m+a)) → R) ≃ₗ[R] (Spot (Fin (a+m+a)) → R) => L (hear x) u) hplain

end InterchangeStageLift

end NearSquareRoot
end Computability
end OAI
