import OAI.Hierarchy.CatalystSubstitutionHost
import OAI.Hierarchy.CatalystSubstitutionNetwork
import OAI.Hierarchy.TaggedOracleCut
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # A physical host built from open shorter and control networks -/

noncomputable section
namespace Hierarchy.Tagged.WideHost
open Catalyst CatalystSubstitution ThreeFlat Routing
open scoped Classical BigOperators

variable {F : Type*} [Field F] {k p : ℕ}

/-- Change a component's public pin labels, allowing unrelated components to
read the same selector, intermediate data, and parent pins. -/
def onPins {V A : Type} [Fintype V] [Fintype A] (N : BitNetwork F (Fintype.card A))
    (wire : A → V) : BitNetwork F (Fintype.card V) :=
  N.restrictPins (fun i => some (Fintype.equivFin V (wire ((Fintype.equivFin A).symm i))))

theorem onPins_value {V A : Type} [Fintype V] [Fintype A] (N : BitNetwork F (Fintype.card A))
    (wire : A → V) (v : V → Bool) :
    TypedWiring.value (onPins N wire) v = TypedWiring.value N (v ∘ wire) := by
  simp [onPins,TypedWiring.value,BitNetwork.restrictPins_eval]

private def localLiteral {A V : Type} [Fintype A] [Fintype V] (wire : A → V ⊕ Bool)
    (i : Fin (Fintype.card A)) : BitSource 0 (Fintype.card V) :=
  match wire ((Fintype.equivFin A).symm i) with
  | .inl p => .pin (Fintype.equivFin _ p)
  | .inr b => .constant b

private theorem localLiteral_read {A V : Type} [Fintype A] [Fintype V] (wire : A → V ⊕ Bool)
    (v : V → Bool) (z : Fin 0 → Bool) (i : Fin (Fintype.card A)) :
    (localLiteral wire i).read z (v ∘ (Fintype.equivFin V).symm) =
      Sum.elim v id (wire ((Fintype.equivFin A).symm i)) := by
  cases h : wire ((Fintype.equivFin A).symm i) <;> simp [localLiteral,h,BitSource.read]

/-- Glue the zero-scale checks, site kernels and native CPU verifier to a
single set of free bits. Fixed advice and padding are literals. No shared
selector, data bit or advice bit creates an additional hidden choice. -/
def localFamily {I V : Type} [Fintype I] [Fintype V] {A : I → Type} [∀ i,Fintype (A i)]
    (N : ∀ i,BitNetwork F (Fintype.card (A i))) (wire : ∀ i,A i → V ⊕ Bool) :
    BitNetwork F (Fintype.card V) :=
  BitNetwork.glue N (fun i => localLiteral (wire i))

theorem localFamily_eval {I V : Type} [Fintype I] [Fintype V] {A : I → Type} [∀ i,Fintype (A i)]
    (N : ∀ i,BitNetwork F (Fintype.card (A i))) (wire : ∀ i,A i → V ⊕ Bool) (v : V → Bool) :
    TypedWiring.value (localFamily N wire) v =
      ∏ i, TypedWiring.value (N i) (Sum.elim v id ∘ wire i) := by
  simp only [TypedWiring.value,localFamily,BitNetwork.glue_eval,Fintype.sum_unique]
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg (N i).eval
  funext j
  exact localLiteral_read (wire i) v _ j

omit [Field F] in
theorem localFamily_size {I V : Type} [Fintype I] [Fintype V] {A : I → Type} [∀ i,Fintype (A i)]
    (N : ∀ i,BitNetwork F (Fintype.card (A i))) (wire : ∀ i,A i → V ⊕ Bool) :
    (localFamily N wire).cells+(localFamily N wire).internal = ∑ i,((N i).cells+(N i).internal) := by
  simp [localFamily,BitNetwork.glue_cells,BitNetwork.glue_internal,Finset.sum_add_distrib]

/-- A native history checker can couple many width-one sort holes. Its
socket words live in the common workspace. Each such word is copied to
its own occurrence using one binary equality per bit, while the checker
itself occurs once among the local sites. -/
def readback {V : Type} [Fintype V] (F : Type*) [Field F] {q : ℕ} (read : Fin q → V) :
    BitNetwork F (Fintype.card (V ⊕ Fin q)) :=
  OracleCut.network (r:=fun _ : Empty => 0) (z:=0) (fun i => nomatch i) (fun i => nomatch i)
    (fun j => .pin (Fintype.equivFin V (read j)))

theorem readback_contract {V : Type} [Fintype V] {q : ℕ}
    (read : Fin q → V) (v : V → Bool) (f : (Fin q → Bool) → F) :
    (∑ z,TypedWiring.value (readback F read) (Sum.elim v z)*f z) = f (v ∘ read) := by
  unfold readback
  rw [OracleCut.contract,Fintype.sum_unique]
  simp [BitSource.read,Function.comp_def]

theorem readback_cost {V : Type} [Fintype V] {q : ℕ} (read : Fin q → V) :
    (readback F read).cells+(readback F read).internal=28*q := by
  unfold readback
  rw [OracleCut.size]
  simp

universe u

/-- Independent open occurrences have a common input word and disjoint output
sockets. Every element of the list retains its original physical network. -/
def Parts (F : Type u) (V : Type) [Fintype V] : List (Occurrence F k) → Type u
  | [] => PUnit
  | o::os => BitNetwork F (Fintype.card (V ⊕ Fin o.arity)) × Parts F V os

variable {V : Type} [Fintype V]

private def first {q : ℕ} {S : Type} : V ⊕ Fin q → (V ⊕ (Fin q ⊕ S)) ⊕ Empty :=
  Sum.inl ∘ Sum.map id Sum.inl

private def rest {q : ℕ} {S : Type} : V ⊕ S → (V ⊕ (Fin q ⊕ S)) ⊕ Empty :=
  Sum.inl ∘ Sum.map id Sum.inr

def network (localPart : BitNetwork F (Fintype.card V)) :
    (os : List (Occurrence F k)) → Parts F V os →
      BitNetwork F (Fintype.card (V ⊕ Sockets os))
  | [], _ => onPins localPart Sum.inl
  | _::os, b => plugPair b.1 (network localPart os b.2) first rest

/-- Fill each bank's own cut with its ideal target while keeping all common
inputs fixed, then multiply by the local sites. -/
def closed (localPart : BitNetwork F (Fintype.card V)) :
    (os : List (Occurrence F k)) → Parts F V os → (V → Bool) → F
  | [], _, v => TypedWiring.value localPart v
  | o::os, b, v =>
    (∑ z, TypedWiring.value b.1 (Sum.elim v z)*o.target z) * closed localPart os b.2 v

private theorem network_cons (localPart : BitNetwork F (Fintype.card V)) (o : Occurrence F k)
    (os : List (Occurrence F k)) (b : Parts F V (o::os)) (v : V → Bool)
    (z : Sockets (o::os) → Bool) :
    TypedWiring.value (network localPart (o::os) b) (Sum.elim v z) =
      TypedWiring.value b.1 (Sum.elim v (z ∘ Sum.inl)) *
      TypedWiring.value (network localPart os b.2) (Sum.elim v (z ∘ Sum.inr)) := by
  change TypedWiring.value (plugPair _ _ first rest) _ = _
  erw [plugPair_value,Fintype.sum_unique]
  congr 1
  · apply congrArg (TypedWiring.value b.1)
    funext i; cases i <;> rfl
  · apply congrArg (TypedWiring.value (network localPart os b.2))
    funext i; cases i <;> rfl

/-- Exact evaluation of the combined exposed board contracts each individual
batch using precisely its numbered data socket. -/
theorem contract (localPart : BitNetwork F (Fintype.card V)) (os : List (Occurrence F k))
    (b : Parts F V os) (v : V → Bool) :
    (∑ z, TypedWiring.value (network localPart os b) (Sum.elim v z)*exactWeight os z) =
      closed localPart os b v := by
  induction os with
  | nil =>
    let : IsEmpty (Sockets ([] : List (Occurrence F k))) := inferInstanceAs (IsEmpty Empty)
    erw [Fintype.sum_unique]
    simp only [network,closed,exactWeight,mul_one,onPins_value]; rfl
  | cons o os ih =>
    let : DecidableEq (Fin o.arity ⊕ Sockets os) := Classical.decEq _
    change (∑ z : Fin o.arity ⊕ Sockets os → Bool,
        TypedWiring.value (network localPart (o::os) b) (Sum.elim v z) *
        (o.target (z ∘ Sum.inl) * exactWeight os (z ∘ Sum.inr))) =
      (∑ z, TypedWiring.value b.1 (Sum.elim v z)*o.target z)*closed localPart os b.2 v
    rw [← ih b.2,Finset.sum_mul]
    erw [← (Equiv.sumArrowEquivProdArrow (Fin o.arity) (Sockets os) Bool).symm.sum_comp,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tail _
    erw [network_cons localPart o os b v]
    change (TypedWiring.value b.1 (Sum.elim v z) *
          TypedWiring.value (network localPart os b.2) (Sum.elim v tail)) *
          (o.target z * exactWeight os tail) =
      (TypedWiring.value b.1 (Sum.elim v z) * o.target z) *
        (TypedWiring.value (network localPart os b.2) (Sum.elim v tail) * exactWeight os tail)
    ring

/-- Add the actual cells and hidden bits of the components once. -/
def partsCost : (os : List (Occurrence F k)) → Parts F V os → ℕ
  | [], _ => 0
  | _::os, b => b.1.cells+b.1.internal+partsCost os b.2

omit [Field F] in
theorem network_size (localPart : BitNetwork F (Fintype.card V)) (os : List (Occurrence F k))
    (b : Parts F V os) :
    (network localPart os b).cells + (network localPart os b).internal =
      localPart.cells+localPart.internal+partsCost os b := by
  induction os with
  | nil => rfl
  | cons o os ih =>
    let N := network localPart os b.2
    let u := first (V:=V) (q:=o.arity) (S:=Sockets os)
    let v := rest (V:=V) (q:=o.arity) (S:=Sockets os)
    change (plugPair b.1 N u v).cells + (plugPair b.1 N u v).internal =
      localPart.cells + localPart.internal + (b.1.cells + b.1.internal + partsCost os b.2)
    calc
      _ = (b.1.cells + N.cells) + (Fintype.card Empty + (b.1.internal + N.internal)) :=
        congrArg₂ Nat.add (plugPair_cells b.1 N u v) (plugPair_internal b.1 N u v)
      _ = _ := by
        have tail : N.cells + N.internal = localPart.cells + localPart.internal + partsCost os b.2 := ih b.2
        rw [Fintype.card_empty]
        omega

/-- Form a block of native cut networks in the same order as the occurrence
list. All shared pins remain public until the single outer contraction. -/
private theorem list_parts {I : Type} (is : List I) (o : I → Occurrence F k)
    (N : ∀ i,BitNetwork F (Fintype.card (V ⊕ Fin (o i).arity)))
    (localPart : BitNetwork F (Fintype.card V)) (tail : List (Occurrence F k)) (b : Parts F V tail) :
    ∃ c : Parts F V (is.map o ++ tail),
      (∀ v, closed localPart _ c v =
        (is.map (fun i => ∑ z,TypedWiring.value (N i) (Sum.elim v z)*(o i).target z)).prod *
          closed localPart tail b v) ∧
      partsCost _ c = (is.map (fun i => (N i).cells+(N i).internal)).sum + partsCost tail b := by
  induction is with
  | nil => exact ⟨b,fun _ => by simp; rfl,by simp; rfl⟩
  | cons i is ih =>
    obtain ⟨c,eval,cost⟩ := ih
    refine ⟨⟨N i,c⟩,fun v => ?_,?_⟩
    · change (_ * closed localPart (is.map o ++ tail) c v) = _
      rw [eval]
      simp only [List.map_cons,List.prod_cons,mul_assoc]
    · change (N i).cells+(N i).internal+partsCost (is.map o ++ tail) c = _
      rw [cost]
      simp only [List.map_cons,List.sum_cons,add_assoc]

/-- An entire homogeneous batch is one member of this list; its tensor arity
can differ from that of every other member. The exact cost and contraction
apply to an empty block as well. -/
theorem ofFn_parts {n : ℕ} (o : Fin n → Occurrence F k)
    (N : ∀ i,BitNetwork F (Fintype.card (V ⊕ Fin (o i).arity)))
    (localPart : BitNetwork F (Fintype.card V)) (tail : List (Occurrence F k)) (b : Parts F V tail) :
    ∃ c : Parts F V (List.ofFn o ++ tail),
      (∀ v, closed localPart _ c v =
        (∏ i,∑ z,TypedWiring.value (N i) (Sum.elim v z)*(o i).target z) *
          closed localPart tail b v) ∧
      partsCost _ c = (∑ i,((N i).cells+(N i).internal)) + partsCost tail b := by
  rw [List.ofFn_eq_map (f:=o)]
  simpa only [← Fin.prod_univ_def,← Fin.sum_univ_def] using
    list_parts (List.finRange n) o N localPart tail b

variable {H : Type} [Fintype H]

private def hideWire {P S : Type} : ((P ⊕ H) ⊕ S) → ((P ⊕ S) ⊕ H)
  | .inl (.inl x) => .inl (.inl x)
  | .inl (.inr z) => .inr z
  | .inr t => .inl (.inr t)

def host (w : Fin k → ℕ) (localPart : BitNetwork F (Fintype.card (Catalyst.Port p w ⊕ H)))
    (os : List (Occurrence F k)) (b : Parts F (Catalyst.Port p w ⊕ H) os) :
    Host F k p (Sockets os) where
  width := w
  network := TypedWiring.glue (fun _ : Unit => network localPart os b)
    (fun _ => hideWire)

private theorem host_coeff (w : Fin k → ℕ) (localPart : BitNetwork F (Fintype.card (Catalyst.Port p w ⊕ H)))
    (os : List (Occurrence F k)) (b : Parts F (Catalyst.Port p w ⊕ H) os) (x : Catalyst.Port p w → Bool)
    (z : Sockets os → Bool) :
    (host w localPart os b).coeff x z =
      ∑ a : H → Bool,TypedWiring.value (network localPart os b) (Sum.elim (Sum.elim x a) z) := by
  unfold Host.coeff host
  rw [TypedWiring.glue_value]
  simp only [Fintype.prod_unique]
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg (TypedWiring.value _)
  funext i
  rcases i with (i|i)|i <;> rfl

theorem exactValue_host (w : Fin k → ℕ) (localPart : BitNetwork F (Fintype.card (Catalyst.Port p w ⊕ H)))
    (os : List (Occurrence F k)) (b : Parts F (Catalyst.Port p w ⊕ H) os) (x : Catalyst.Port p w → Bool) :
    exactValue os (host w localPart os b) x =
      ∑ a : H → Bool,closed localPart os b (Sum.elim x a) := by
  unfold exactValue
  simp only [host_coeff,Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => contract localPart os b (Sum.elim x a))

omit [Field F] in
theorem host_size (w : Fin k → ℕ) (localPart : BitNetwork F (Fintype.card (Catalyst.Port p w ⊕ H)))
    (os : List (Occurrence F k)) (b : Parts F (Catalyst.Port p w ⊕ H) os) :
    hostSize (host w localPart os b) =
      localPart.cells+localPart.internal+partsCost os b+Fintype.card H+
        Fintype.card (Catalyst.Port p w ⊕ Sockets os) := by
  simp only [hostSize,host,TypedWiring.glue_cells,TypedWiring.glue_internal,Fintype.sum_unique]
  apply congrArg₂ Nat.add _ (Fintype.card_congr (Equiv.refl (Catalyst.Port p w ⊕ Sockets os)))
  have := network_size localPart os b
  omega

end Hierarchy.Tagged.WideHost

end
end OAI
