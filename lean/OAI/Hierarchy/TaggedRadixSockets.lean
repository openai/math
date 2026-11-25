import OAI.Hierarchy.CatalystSubstitutionHost

namespace OAI
/-! # Socket indices and exact weights on appended banks of gates -/

noncomputable section
namespace Hierarchy.Tagged.RadixStage
open Catalyst CatalystSubstitution ThreeFlat Routing
open scoped Classical BigOperators

variable {F : Type*} [Field F] {k p : ℕ}

def socketsAppend (xs ys : List (Occurrence F k)) :
    Sockets (xs++ys) ≃ Sockets xs ⊕ Sockets ys := match xs with
  | [] => (Equiv.emptySum Empty (Sockets ys)).symm
  | o::os => (Equiv.sumCongr (Equiv.refl (Fin o.arity)) (socketsAppend os ys)).trans
      (Equiv.sumAssoc _ _ _).symm

def appendBits (xs ys : List (Occurrence F k)) (x : Sockets xs→Bool) (y : Sockets ys→Bool) :
    Sockets (xs++ys) → Bool := match xs with
  | [] => y
  | _o::os => Sum.elim (x ∘ Sum.inl) (appendBits os ys (x ∘ Sum.inr) y)

omit [Field F] in
theorem appendBits_eq (xs ys : List (Occurrence F k)) (x : Sockets xs→Bool) (y : Sockets ys→Bool) :
    appendBits xs ys x y = Sum.elim x y ∘ socketsAppend xs ys := by
  induction xs with
  | nil => rfl
  | cons o os ih =>
    funext i
    rcases i with i|i
    · rfl
    · change appendBits os ys (x ∘ Sum.inr) y i = _
      rw [ih]
      change Sum.elim (x ∘ Sum.inr) y (socketsAppend os ys i) =
        Sum.elim x y (Sum.elim (fun j => Sum.inl (Sum.inr j)) Sum.inr (socketsAppend os ys i))
      cases socketsAppend os ys i <;> rfl

theorem exactWeight_append (xs ys : List (Occurrence F k)) (x : Sockets xs→Bool) (y : Sockets ys→Bool) :
    exactWeight (xs++ys) (Sum.elim x y ∘ socketsAppend xs ys) = exactWeight xs x*exactWeight ys y := by
  rw [←appendBits_eq]
  induction xs with
  | nil => simp [appendBits,exactWeight]
  | cons o os ih =>
    change o.target (x ∘ Sum.inl)*exactWeight (os++ys) (appendBits os ys (x∘Sum.inr) y) =
      (o.target (x ∘ Sum.inl)*exactWeight os (x∘Sum.inr))*exactWeight ys y
    rw [ih,mul_assoc]

omit [Field F] in
theorem sockets_card (os : List (Occurrence F k)) : Fintype.card (Sockets os) = (os.map (·.arity)).sum := by
  induction os with
  | nil => change Fintype.card Empty=0; simp
  | cons o os ih =>
    change Fintype.card (Fin o.arity ⊕ Sockets os) = o.arity+(os.map (·.arity)).sum
    rw [Fintype.card_sum,Fintype.card_fin,ih]

end Hierarchy.Tagged.RadixStage

end
end OAI
