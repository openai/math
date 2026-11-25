import OAI.Computability.NearSquareRoot.InterchangeStageConjugate
import OAI.Computability.NearSquareRoot.InterchangeSupport
import OAI.Computability.NearSquareRoot.InterchangeSupportedToken

/-!
# A supported word for the occupied-reserve exchange

Only the `e` exchanged fields on each wing participate. The dense piece
therefore costs at most `36 * e` pivots, independent of the intervening main
fields. The address identity includes all the fields outside the exchange.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeStageLift

open IntegerMultiplication.Port NearSquareRoot.InterchangeSlots NearSquareRoot.Interchange.Support

variable {c e a m : ℕ}

/-- All occupied pairs in two consecutive blocks in the active address vector. -/
def reservePairSlots (hce : c+e=a) : Fin (e+e) ↪ Spot (Fin (a+m+a)) where
  toFun := Fin.append (fun i => (false,earlyReserve hce i)) (fun i => (true,lateReserve hce i))
  inj' := by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro h
      apply congrArg (Fin.castAdd e)
      exact earlyReserve_injective (m:=m) hce (by simpa only [Fin.append_left, Fin.append_right] using congrArg Prod.snd h)
    · simp only [Fin.append_left, Fin.append_right, Prod.mk.injEq, Bool.false_eq_true, false_and, false_implies]
    · simp only [Fin.append_left, Fin.append_right, Prod.mk.injEq, Bool.true_eq_false, false_and, false_implies]
    · intro h
      apply congrArg (Fin.natAdd e)
      exact lateReserve_injective (m:=m) hce (by simpa only [Fin.append_left, Fin.append_right] using congrArg Prod.snd h)

@[simp] theorem reservePairSlots_left (hce : c+e=a) (i : Fin e) :
    reservePairSlots (m:=m) hce (Fin.castAdd e i) = (false,earlyReserve hce i) := by
  change Fin.append (fun j => (false,earlyReserve (m:=m) hce j)) (fun j => (true,lateReserve hce j)) (Fin.castAdd e i) = _
  rw [Fin.append_left]

@[simp] theorem reservePairSlots_right (hce : c+e=a) (i : Fin e) :
    reservePairSlots (m:=m) hce (Fin.natAdd e i) = (true,lateReserve hce i) := by
  change Fin.append (fun j => (false,earlyReserve (m:=m) hce j)) (fun j => (true,lateReserve hce j)) (Fin.natAdd e i) = _
  rw [Fin.append_right]

/-- Swapping the two complete coordinate blocks interchanges each occupied pair. -/
def exchangeReservePairs (e : ℕ) : Equiv.Perm (Fin (e+e)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin e) (Fin e))).trans finSumFinEquiv

@[simp] theorem exchangeReservePairs_left (i : Fin e) :
    exchangeReservePairs e (Fin.castAdd e i) = Fin.natAdd e i := by
  simp only [exchangeReservePairs, Equiv.trans_apply, finSumFinEquiv_symm_apply_castAdd,
    Equiv.sumComm_apply, Sum.swap_inl, finSumFinEquiv_apply_right]

@[simp] theorem exchangeReservePairs_right (i : Fin e) :
    exchangeReservePairs e (Fin.natAdd e i) = Fin.castAdd e i := by
  simp only [exchangeReservePairs, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumComm_apply, Sum.swap_inr, finSumFinEquiv_apply_left]

/-- The rational instruction whose active map is just a coordinate permutation. -/
def reserveWord (rank : Fin (a+m+a) → ℕ) (hce : c+e=a) : Word (Fin (a+m+a)) rank :=
  .atom (.dense (reservePairSlots hce) (LinearEquiv.funCongrLeft ℚ ℚ (exchangeReservePairs e)))

theorem reserveWord_price (rank : Fin (a+m+a) → ℕ) (hce : c+e=a) :
    (reserveWord rank hce).price = 36 * e := by
  change 18 * (e+e) = 36 * e
  omega

/-- The linear address map on a full pair of wings over any residue ring. -/
noncomputable def reserveLinear (R : Type) [CommRing R] (hce : c+e=a) :
    Duplex (Fin (a+m+a)) R ≃ₗ[R] Duplex (Fin (a+m+a)) R :=
  linearEquiv (reservePairSlots hce) (LinearEquiv.funCongrLeft R R (exchangeReservePairs e))

theorem reserveLinear_eq_shift (R : Type) [CommRing R] (hce : c+e=a) :
    (reserveLinear (m:=m) R hce).toEquiv = reserveShift hce := by
  apply Equiv.ext
  intro x
  symm
  obtain ⟨pair, outside⟩ := reserveShift_effect hce x
  apply eq_update
  · intro i
    change hear (reserveShift hce x) (reservePairSlots hce i) =
      hear x (reservePairSlots hce (exchangeReservePairs e i))
    refine Fin.addCases (fun k => ?_) (fun k => ?_) i
    · rw [reservePairSlots_left, exchangeReservePairs_left, reservePairSlots_right]
      exact (pair k).1
    · rw [reservePairSlots_right, exchangeReservePairs_right, reservePairSlots_left]
      exact (pair k).2
  · intro u hu
    apply outside u
    intro i
    exact ⟨by simpa only [reservePairSlots_left] using hu (Fin.castAdd e i),
      by simpa only [reservePairSlots_right] using hu (Fin.natAdd e i)⟩

open NearSquareRoot.Interchange in
theorem reserveWord_token (R : Type) [CommRing R] (rank : Fin (a+m+a) → ℕ) (hce : c+e=a) :
    AddressToken (coordinateAddress (reserveWord rank hce).address)
      (coordinateAddress (reserveLinear R hce)) :=
  (AddressToken.coordinate (R:=R) (exchangeReservePairs e)).supported (reservePairSlots hce)

theorem reserveWord_address (rank : Fin (a+m+a) → ℕ) (hce : c+e=a) :
    (reserveWord rank hce).address.toEquiv = reserveShift hce :=
  reserveLinear_eq_shift ℚ hce

/-- The full reserve exchange has one rational supported word, for every main-field count. -/
theorem exists_reserveWord (rank : Fin (a+m+a) → ℕ) (hce : c+e=a) :
    ∃ W : Word (Fin (a+m+a)) rank, W.price ≤ 36*a ∧ W.address.toEquiv = reserveShift hce := by
  refine ⟨reserveWord rank hce, ?_, reserveWord_address rank hce⟩
  rw [reserveWord_price]
  omega

end InterchangeStageLift

end NearSquareRoot
end Computability
end OAI
