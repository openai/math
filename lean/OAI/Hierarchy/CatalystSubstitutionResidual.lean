import OAI.Hierarchy.CatalystSubstitutionHost
import OAI.Hierarchy.CatalystSubstitutionNetwork
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # A physical host with a residual bank of future calls

One contraction hides precisely the current call word. Every later call bit
remains exposed, so a list of replacements can reuse this operation directly.
-/

noncomputable section
namespace Hierarchy.CatalystSubstitution
open Catalyst ThreeFlat Routing
open scoped Classical BigOperators

variable {F : Type*} [Field F] {k p q : ℕ} {H : Type} [Fintype H]

private def hostWire (b c : Fin k → ℕ) :
    Port p b ⊕ (Fin q ⊕ H) → (Port p (fun j => b j+c j) ⊕ H) ⊕ Fin q
  | .inl t => .inl (.inl (oldPort b c t))
  | .inr (.inl h) => .inr h
  | .inr (.inr i) => .inl (.inr i)

private def nextWire (b c : Fin k → ℕ) :
    Port q c → (Port p (fun j => b j+c j) ⊕ H) ⊕ Fin q
  | .inl h => .inr h
  | .inr w => .inl (.inl (newPort b c w))

def residual (C : Host F k p (Fin q ⊕ H)) (X : Approximation F k q) : Host F k p H where
  width := fun j => C.width j+X.width j
  network := plugPair C.network X.network (hostWire C.width X.width) (nextWire C.width X.width)

theorem residual_coeff (C : Host F k p (Fin q ⊕ H)) (X : Approximation F k q)
    (x : Port p (fun j => C.width j+X.width j) → Bool) (r : H → Bool) :
    (residual C X).coeff x r = ∑ h : Fin q → Bool,
      C.coeff (x ∘ oldPort C.width X.width) (Sum.elim h r) *
        X.coeff (Sum.elim h (x ∘ newPort C.width X.width)) := by
  change TypedWiring.value (plugPair _ _ _ _) (Sum.elim x r) = _
  rw [plugPair_value]
  apply Finset.sum_congr (by ext h; simp)
  intro h _
  have oldRead : Sum.elim (Sum.elim x r) h ∘ hostWire C.width X.width =
      Sum.elim (x ∘ oldPort C.width X.width) (Sum.elim h r) := by
    funext u
    rcases u with a | (b | c) <;> rfl
  have newRead : Sum.elim (Sum.elim x r) h ∘ nextWire C.width X.width =
      Sum.elim h (x ∘ newPort C.width X.width) := by
    funext u
    cases u <;> rfl
  rw [oldRead,newRead]; rfl

omit [Field F] in
theorem residual_cells (C : Host F k p (Fin q ⊕ H)) (X : Approximation F k q) :
    (residual C X).network.cells = C.network.cells + X.network.cells := plugPair_cells ..

omit [Field F] in
theorem residual_internal (C : Host F k p (Fin q ⊕ H)) (X : Approximation F k q) :
    (residual C X).network.internal = q + (C.network.internal + X.network.internal) := by
  rw [residual, plugPair_internal, Fintype.card_fin]

private def finalPins (P : Type) [Fintype P] (i : Fin (Fintype.card (P ⊕ Empty))) :
    Option (Fin (Fintype.card P)) :=
  some (Fintype.equivFin P (Equiv.sumEmpty P Empty ((Fintype.equivFin _).symm i)))

/-- Readdress the finished host without adding a table or an internal bit. -/
def finish (C : Host F k p Empty) : Approximation F k p where
  width := C.width
  network := C.network.restrictPins (finalPins _)

theorem finish_coeff (C : Host F k p Empty) (x : Port p C.width → Bool) :
    (finish C).coeff x = C.coeff x isEmptyElim := by
  unfold finish Approximation.coeff Host.coeff TypedWiring.value
  rw [BitNetwork.restrictPins_eval]
  apply congrArg C.network.eval
  funext i
  simp only [finalPins, Option.map_some, Option.getD_some, Equiv.symm_apply_apply]
  cases (Fintype.equivFin (Port p C.width ⊕ Empty)).symm i with
  | inl t => rfl
  | inr t => exact t.elim

omit [Field F] in
theorem finish_cells (C : Host F k p Empty) : (finish C).network.cells = C.network.cells := rfl

omit [Field F] in
theorem finish_internal (C : Host F k p Empty) :
    (finish C).network.internal = C.network.internal := rfl

end Hierarchy.CatalystSubstitution

end
end OAI
