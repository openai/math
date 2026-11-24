import OAI.Computability.VPVNP.ShiftedCrossing
import OAI.Computability.VPVNP.WireTensor

/-!
# Placing the two crossing wires at tensor parties

The four roles in Lemma 3.2 are the positive and negative endpoints of the two
wires. An arbitrary map from roles to parties may put several endpoints at one
party. Its local basis retains a coordinate for each role at that party.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Crossing

open VPVNP.WireTensor
open scoped BigOperators

/-- The two copies of `Bool` label the two wires. On either wire, `false` is
the positive endpoint and `true` is the negative endpoint. -/
abbrev Terminal := Bool ⊕ Bool

/-- Basis label carried by each terminal. -/
abbrev terminalBasis (x y : ℕ) : Terminal → Type
  | .inl _ => Fin x
  | .inr _ => Fin y

instance (x y : ℕ) (r : Terminal) : Fintype (terminalBasis x y r) := by
  cases r <;> exact inferInstanceAs (Fintype (Fin _))

variable {x y plus minus : ℕ} {J k : Type*}

/-- The first ordinary summand uses the cut pairing equal endpoint signs. -/
def plusArray (k : Type*) [Ring k] (f : IntegralCrossing x y plus minus) :
    WireTensor.Array k (terminalBasis x y) := fun z =>
  ∑ a, (f.leftPlus a (z (.inl false)) (z (.inr false)) : k) *
    (f.rightPlus a (z (.inl true)) (z (.inr true)) : k)

/-- The second ordinary summand pairs opposite endpoint signs. -/
def minusArray (k : Type*) [Ring k] (f : IntegralCrossing x y plus minus) :
    WireTensor.Array k (terminalBasis x y) := fun z =>
  ∑ a, (f.leftMinus a (z (.inl false)) (z (.inr true)) : k) *
    (f.rightMinus a (z (.inl true)) (z (.inr false)) : k)

/-- The chosen integral crossing factors sum to the product of the two
Kronecker deltas in any coefficient ring. -/
theorem plusArray_add_minusArray [Ring k] (f : IntegralCrossing x y plus minus)
    (z : (r : Terminal) → terminalBasis x y r) :
    plusArray k f z + minusArray k f z =
      (if (z (.inl false) : Fin x) = z (.inl true) then 1 else 0) *
      (if (z (.inr false) : Fin y) = z (.inr true) then 1 else 0) := by
  simpa only [plusArray, minusArray, map_add, map_mul, map_sum, apply_ite (Int.castRingHom k),
    map_one, map_zero, Int.coe_castRingHom] using congrArg (Int.castRingHom k)
    (f.identity (z (.inl false)) (z (.inl true)) (z (.inr false)) (z (.inr true)))

variable [Fintype J] [CommRing k]

/-- Product of the two identity wires at the designated parties. -/
noncomputable def terminalWires (p : Terminal → J) (x y : ℕ) : Tensor k J :=
  tensorProduct (wire (p (.inl false)) (p (.inl true)) (Fin x))
    (wire (p (.inr false)) (p (.inr true)) (Fin y))

private def terminalEquiv (p : Terminal → J) (x y : ℕ) (j : J) :
    (terminalWires (k := k) p x y).Basis j ≃
      ((r : Terminal) → j = p r → terminalBasis x y r) where
  toFun w
    | .inl false => w.1.1
    | .inl true => w.1.2
    | .inr false => w.2.1
    | .inr true => w.2.2
  invFun z := ((z (.inl false), z (.inl true)), z (.inr false), z (.inr true))
  left_inv _ := rfl
  right_inv z := by funext r; rcases r with (_ | _) | (_ | _) <;> rfl

/-- The direct sum of the two placed ordinary summands locally restricts to
the two-wire tensor. This covers arbitrary coincidences among all terminals. -/
theorem placed_crossing_restricts (p : Terminal → J) (f : IntegralCrossing x y plus minus) :
    Restricts (directSum (placedTensor p (terminalBasis x y) (plusArray k f))
      (placedTensor p (terminalBasis x y) (minusArray k f))) (terminalWires p x y) := by
  let P := placedTensor p (terminalBasis x y) (plusArray k f)
  let M := placedTensor p (terminalBasis x y) (minusArray k f)
  apply (directSum_restricts_add P.coeff M.coeff).trans
  apply (restricts_of_reindex (fun j => terminalEquiv p x y j) _).1
  intro z
  let coords : (r : Terminal) → terminalBasis x y r :=
    fun r => terminalEquiv p x y (p r) (z (p r)) r rfl
  change (terminalWires p x y).coeff z = plusArray k f coords + minusArray k f coords
  rw [plusArray_add_minusArray]
  have hxPlus : coords (.inl false) = (z (p (.inl false))).1.1 rfl := rfl
  have hxMinus : coords (.inl true) = (z (p (.inl true))).1.2 rfl := rfl
  have hyPlus : coords (.inr false) = (z (p (.inr false))).2.1 rfl := rfl
  have hyMinus : coords (.inr true) = (z (p (.inr true))).2.2 rfl := rfl
  simp only [terminalWires, tensorProduct, wire, hxPlus, hxMinus, hyPlus, hyMinus]
  split_ifs <;> simp_all

/-- Side of the two-center cut. The second cut reverses the ends of the Y wire. -/
def cutSide (flipY : Bool) : Terminal → Bool
  | .inl b => b
  | .inr b => b.xor flipY

/-- The four terminal wires to their respective centers and the wire carrying
the factorization index between the two centers. -/
noncomputable def crossingNetwork (p : Terminal → J) (center : Bool → J)
    (flipY : Bool) (x y rank : ℕ) : Tensor k J :=
  wireNetwork (cutSource p center) (cutTarget (cutSide flipY) center)
    (cutBasis (terminalBasis x y) (Fin rank))

/-- Realize the two shifted factors at independently placed pairs of centers.
A local restriction of the direct sum of the two wire networks gives the two
original identity wires at the four terminals. -/
theorem crossingNetworks_restricts (p : Terminal → J) (centerPlus centerMinus : Bool → J)
    (f : IntegralCrossing x y plus minus) :
    Restricts (directSum (crossingNetwork p centerPlus false x y plus)
      (crossingNetwork p centerMinus true x y minus)) (terminalWires (k := k) p x y) := by
  apply Restricts.trans _ (placed_crossing_restricts p f)
  apply directSum_restricts
  · exact cutFactorization_restricts p (cutSide false) centerPlus (terminalBasis x y) (Fin plus)
      (fun z a => (f.leftPlus a (z (.inl false) rfl) (z (.inr false) rfl) : k))
      (fun z a => (f.rightPlus a (z (.inl true) rfl) (z (.inr true) rfl) : k))
  · exact cutFactorization_restricts p (cutSide true) centerMinus (terminalBasis x y) (Fin minus)
      (fun z a => (f.leftMinus a (z (.inl false) rfl) (z (.inr true) rfl) : k))
      (fun z a => (f.rightMinus a (z (.inl true) rfl) (z (.inr false) rfl) : k))

end Crossing

end VPVNP
end Computability
end OAI
