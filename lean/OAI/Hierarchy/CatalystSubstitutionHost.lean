import OAI.Hierarchy.Catalyst
import OAI.ThreeFlat.Routing.TypedWiring

namespace OAI
/-! # Open physical hosts and their exact oracle contractions -/

noncomputable section
namespace Hierarchy.CatalystSubstitution
open Catalyst ThreeFlat Routing
open scoped Classical BigOperators

structure Host (F : Type*) (k p : ℕ) (H : Type) [Fintype H] where
  width : Fin k → ℕ
  network : BitNetwork F (Fintype.card (Port p width ⊕ H))

variable {F : Type*} [Field F] {k p : ℕ} {H : Type} [Fintype H]

def Host.coeff (C : Host F k p H) (x : Port p C.width → Bool) (r : H → Bool) : F :=
  TypedWiring.value C.network (Sum.elim x r)

structure Occurrence (F : Type*) (k : ℕ) where
  arity : ℕ
  target : (Fin arity → Bool) → F
  replacement : Approximation F k arity

/-- The data sockets are disjoint even for repeated occurrences of one call. -/
def Sockets : List (Occurrence F k) → Type
  | [] => Empty
  | o :: os => Fin o.arity ⊕ Sockets os

instance socketsFinite : (os : List (Occurrence F k)) → Fintype (Sockets os)
  | [] => inferInstanceAs (Fintype Empty)
  | o :: os => by
    letI : Fintype (Sockets os) := socketsFinite os
    exact inferInstanceAs (Fintype (Fin o.arity ⊕ Sockets os))

/-- Product of the exact call values at one setting of all sockets. -/
def exactWeight : (os : List (Occurrence F k)) → (Sockets os → Bool) → F
  | [], _ => 1
  | o :: os, h => o.target (h ∘ Sum.inl) * exactWeight os (h ∘ Sum.inr)

def exactValue (os : List (Occurrence F k)) (C : Host F k p (Sockets os))
    (x : Port p C.width → Bool) : F := ∑ h, C.coeff x h * exactWeight os h

/-- A coefficient-table presentation used while proving prices of intermediate
contractions. The final network uses the original host and replacements. -/
def tableApprox (b : Fin k → ℕ) (v : (Port p b → Bool) → F) : Approximation F k p :=
  ⟨b, TypedWiring.localTable v⟩

@[simp] theorem tableApprox_coeff (b : Fin k → ℕ) (v : (Port p b → Bool) → F)
    (x : Port p b → Bool) : (tableApprox b v).coeff x = v x :=
  TypedWiring.localTable_value v x

/-- The host size includes the open formal sockets, which become internal bits
when their occurrences are installed. -/
def hostSize {H : Type} [Fintype H] (C : Host F k p H) : ℕ :=
  C.network.cells + C.network.internal + Fintype.card (Port p C.width ⊕ H)

/-- Equality of the labelled coefficient tables, allowing different physical
realizations. An opened oracle refilled by its exact table presents the current
contraction in precisely this sense. -/
def Agrees (A B : Approximation F k p) : Prop :=
  ∃ h : A.width = B.width, ∀ x : Port p B.width → Bool,
    A.coeff (fun i => x (h ▸ i)) = B.coeff x

protected theorem Agrees.refl (A : Approximation F k p) : Agrees A A := ⟨rfl,fun _ => rfl⟩

end Hierarchy.CatalystSubstitution

end
end OAI
