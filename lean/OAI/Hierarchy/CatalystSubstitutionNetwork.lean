import OAI.Hierarchy.CatalystSubstitutionPorts
import OAI.ThreeFlat.Routing.TypedWiring

namespace OAI
/-! # Plugging a physical tensor network into one open call

The same hidden bits supply the call data on the two sides of the cut.
The old and new catalysts stay exposed on disjoint blocks in each direction.
-/

noncomputable section
namespace Hierarchy.CatalystSubstitution

open Catalyst ThreeFlat Routing
open scoped Classical BigOperators

structure Context (F : Type*) (k p q : ℕ) where
  width : Fin k → ℕ
  network : BitNetwork F (Fintype.card (Port p width ⊕ Fin q))

variable {F : Type*} [Field F] {k p q : ℕ}

def Context.coeff (C : Context F k p q) (x : Port p C.width → Bool) (h : Fin q → Bool) : F :=
  TypedWiring.value C.network (Sum.elim x h)

def Context.size (C : Context F k p q) : ℕ :=
  C.network.cells + C.network.internal + Fintype.card (Port p C.width ⊕ Fin q)

private def side (A B : Type) : Bool → Type
  | true => A
  | false => B

private instance {A B : Type} [Fintype A] [Fintype B] (b : Bool) : Fintype (side A B b) :=
  match b with
  | true => inferInstanceAs (Fintype A)
  | false => inferInstanceAs (Fintype B)

section Pair
variable {A B Y H : Type} [Fintype A] [Fintype B] [Fintype Y] [Fintype H]
    (M : BitNetwork F (Fintype.card A)) (N : BitNetwork F (Fintype.card B))
    (u : A → Y ⊕ H) (v : B → Y ⊕ H)

private def parts : (b : Bool) → BitNetwork F (Fintype.card (side A B b))
  | true => M
  | false => N

private def wiring : (b : Bool) → side A B b → Y ⊕ H
  | true => u
  | false => v

/-- Contract two physical networks along independently numbered shared bits. -/
def plugPair := TypedWiring.glue (parts M N) (wiring u v)

theorem plugPair_value (x : Y → Bool) :
    TypedWiring.value (plugPair M N u v) x =
      ∑ h : H → Bool, TypedWiring.value M (Sum.elim x h ∘ u) *
        TypedWiring.value N (Sum.elim x h ∘ v) := by
  rw [plugPair, TypedWiring.glue_value]
  simp only [Fintype.prod_bool, parts, wiring, Function.comp_def]
  apply Finset.sum_congr (by ext h; simp)
  intro h _
  first | rfl'

omit [Field F] in
theorem plugPair_cells :
    (plugPair M N u v).cells = M.cells + N.cells := by
  simp only [plugPair, TypedWiring.glue_cells, Fintype.sum_bool, parts]

omit [Field F] in
theorem plugPair_internal :
    (plugPair M N u v).internal = Fintype.card H + (M.internal + N.internal) := by
  simp only [plugPair, TypedWiring.glue_internal, Fintype.sum_bool, parts]
end Pair

private def contextWire {A B H : Type} (e : A → B) : (A ⊕ H) → (B ⊕ H) :=
  Sum.elim (Sum.inl ∘ e) Sum.inr

private theorem read_context {A B H : Type} (e : A → B) (x : B → Bool) (h : H → Bool) :
    Sum.elim x h ∘ contextWire e = Sum.elim (x ∘ e) h := by
  funext i
  cases i <;> rfl

private def callWire (b c : Fin k → ℕ) : Port q c → Port p (fun j => b j + c j) ⊕ Fin q :=
  Sum.elim Sum.inr (Sum.inl ∘ newPort b c)

private theorem read_call (b c : Fin k → ℕ) (x : Port p (fun j => b j+c j) → Bool)
    (h : Fin q → Bool) :
    Sum.elim x h ∘ callWire b c = Sum.elim h (x ∘ newPort b c) := by
  funext i
  cases i <;> rfl

/-- Plug a catalyst-bearing approximation into the actual `q`-bit hole. -/
def approxPlug (C : Context F k p q) (X : Approximation F k q) : Approximation F k p where
  width := fun j => C.width j + X.width j
  network := plugPair C.network X.network (contextWire (oldPort C.width X.width))
    (callWire C.width X.width)

theorem approxPlug_coeff (C : Context F k p q) (X : Approximation F k q)
    (x : Port p (fun j => C.width j + X.width j) → Bool) :
    (approxPlug C X).coeff x =
      ∑ h : Fin q → Bool, C.coeff (x ∘ oldPort C.width X.width) h *
        X.coeff (Sum.elim h (x ∘ newPort C.width X.width)) := by
  change TypedWiring.value (plugPair _ _ _ _) x = _
  rw [plugPair_value]
  simp only [read_context, read_call, Context.coeff]
  apply Finset.sum_congr (by ext h; simp)
  intro h _
  first | rfl'

/-- An arbitrary exact implementation of the call may be plugged in without
adding any new catalyst slots. -/
def exactPlugNetwork (C : Context F k p q) (N : BitNetwork F (Fintype.card (Fin q))) :
    Approximation F k p where
  width := C.width
  network := plugPair C.network N id Sum.inr

theorem exactPlugNetwork_coeff (C : Context F k p q) (N : BitNetwork F (Fintype.card (Fin q)))
    (x : Port p C.width → Bool) :
    (exactPlugNetwork C N).coeff x =
      ∑ h : Fin q → Bool, C.coeff x h * TypedWiring.value N h := by
  change TypedWiring.value (plugPair _ _ _ _) x = _
  rw [plugPair_value]
  apply Finset.sum_congr (by ext h; simp)
  intro h _
  first | rfl'

def exactPlug (C : Context F k p q) (f : (Fin q → Bool) → F) : Approximation F k p :=
  exactPlugNetwork C (TypedWiring.localTable f)

theorem exactPlug_coeff (C : Context F k p q) (f : (Fin q → Bool) → F)
    (x : Port p C.width → Bool) :
    (exactPlug C f).coeff x = ∑ h : Fin q → Bool, C.coeff x h * f h := by
  simp only [exactPlug, exactPlugNetwork_coeff, TypedWiring.localTable_value]

omit [Field F] in
theorem approxPlug_cells (C : Context F k p q) (X : Approximation F k q) :
    (approxPlug C X).network.cells = C.network.cells + X.network.cells := plugPair_cells ..

omit [Field F] in
theorem approxPlug_internal (C : Context F k p q) (X : Approximation F k q) :
    (approxPlug C X).network.internal = q + (C.network.internal + X.network.internal) := by
  rw [approxPlug, plugPair_internal, Fintype.card_fin]

omit [Field F] in
theorem exactPlugNetwork_cells (C : Context F k p q) (N : BitNetwork F (Fintype.card (Fin q))) :
    (exactPlugNetwork C N).network.cells = C.network.cells + N.cells := plugPair_cells ..

omit [Field F] in
theorem exactPlugNetwork_internal (C : Context F k p q) (N : BitNetwork F (Fintype.card (Fin q))) :
    (exactPlugNetwork C N).network.internal = q + (C.network.internal + N.internal) := by
  rw [exactPlugNetwork, plugPair_internal]
  exact congrArg (fun n => n + (C.network.internal + N.internal)) (Fintype.card_fin q)

omit [Field F] in
/-- The physical plug counts the shared hole bits once, as hidden bits. -/
theorem approxPlug_size (C : Context F k p q) (X : Approximation F k q) :
    (approxPlug C X).size + q = C.size + X.size := by
  have pack := (Fintype.card_congr (portEquiv (p:=p) C.width X.width)).symm
  rw [Fintype.card_sum (α:=Port p C.width) (β:=Wire X.width × Bool)] at pack
  change (approxPlug C X).network.cells + (approxPlug C X).network.internal +
    Fintype.card (Port p (fun j => C.width j+X.width j)) + q =
    C.network.cells + C.network.internal + Fintype.card (Port p C.width ⊕ Fin q) +
      (X.network.cells + X.network.internal + Fintype.card (Fin q ⊕ Wire X.width × Bool))
  rw [approxPlug_cells, approxPlug_internal]
  have left := Fintype.card_sum (α := Port p C.width) (β := Fin q)
  have right := Fintype.card_sum (α := Fin q) (β := Wire X.width × Bool)
  have hidden := Fintype.card_fin q
  omega

omit [Field F] in
theorem exactPlugNetwork_size (C : Context F k p q) (N : BitNetwork F (Fintype.card (Fin q))) :
    (exactPlugNetwork C N).size = C.size + N.cells + N.internal := by
  change (exactPlugNetwork C N).network.cells + (exactPlugNetwork C N).network.internal +
    Fintype.card (Port p C.width) =
    C.network.cells + C.network.internal + Fintype.card (Port p C.width ⊕ Fin q) + N.cells + N.internal
  rw [exactPlugNetwork_cells, exactPlugNetwork_internal]
  have left := Fintype.card_sum (α := Port p C.width) (β := Fin q)
  have hidden := Fintype.card_fin q
  omega

theorem exactPlug_size (C : Context F k p q) (f : (Fin q → Bool) → F) :
    (exactPlug C f).size = C.size + 2^q*(q+2) + 2^q*(q+1) := by
  simp only [exactPlug, exactPlugNetwork_size, TypedWiring.localTable,
    TableCompiler.localTableNetwork_cells, TableCompiler.localTableNetwork_internal, Fintype.card_fin]

end Hierarchy.CatalystSubstitution

end
end OAI
