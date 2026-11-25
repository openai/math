import OAI.Hierarchy.TaggedRadixSockets
import OAI.Hierarchy.TaggedRadixStages

namespace OAI
/-! # Numbering the oracle sockets of a chain of radix passes -/

noncomputable section
namespace Hierarchy.Tagged.RadixStage

open Catalyst CatalystSubstitution
open scoped BigOperators Classical

variable {F : Type*} [Field F] {k : ℕ}

/-- A bank with one product oracle has precisely its consecutive data pins. -/
def singleSocket (o : Occurrence F k) : Fin o.arity ≃ Sockets [o] :=
  (Equiv.sumEmpty (Fin o.arity) Empty).symm

@[simp] theorem singleSocket_weight (o : Occurrence F k) (z : Fin o.arity → Bool) :
    exactWeight [o] (z ∘ (singleSocket o).symm) = o.target z := by
  change o.target _ * 1 = _
  rw [mul_one]
  rfl

def chainCalls (os : ℕ → List (Occurrence F k)) : ℕ → List (Occurrence F k)
  | 0 => os 0
  | n+1 => chainCalls os n ++ os (n+1)

omit [Field F] in
theorem chainCalls_length (os : ℕ → List (Occurrence F k)) (n : ℕ) :
    (chainCalls os n).length = ∑ i ∈ Finset.range (n+1), (os i).length := by
  induction n with
  | zero => simp [chainCalls]
  | succ n ih => rw [chainCalls, List.length_append, ih, Finset.sum_range_succ (n:=n+1)]

omit [Field F] in
theorem chainCalls_total (os : ℕ → List (Occurrence F k)) (size : Occurrence F k → ℕ) (n : ℕ) :
    ((chainCalls os n).map size).sum = ∑ i ∈ Finset.range (n+1), ((os i).map size).sum := by
  induction n with
  | zero => simp [chainCalls]
  | succ n ih => rw [chainCalls, List.map_append, List.sum_append, ih, Finset.sum_range_succ (n:=n+1)]

def chainSockets (holes : ℕ → Type) (os : ℕ → List (Occurrence F k))
    (e : ∀ i, holes i ≃ Sockets (os i)) :
    (n : ℕ) → Bank holes n ≃ Sockets (chainCalls os n)
  | 0 => e 0
  | n+1 => (Equiv.sumCongr (chainSockets holes os e n) (e (n+1))).trans
      (socketsAppend (chainCalls os n) (os (n+1))).symm

private theorem pair_socket_weight {H J : Type} (xs ys : List (Occurrence F k))
    (e : H ≃ Sockets xs) (f : J ≃ Sockets ys) (z : H ⊕ J → Bool) :
    exactWeight (xs++ys)
        (z ∘ ((Equiv.sumCongr e f).trans (socketsAppend xs ys).symm).symm) =
      exactWeight xs ((z ∘ Sum.inl) ∘ e.symm) * exactWeight ys ((z ∘ Sum.inr) ∘ f.symm) := by
  have split : z ∘ ((Equiv.sumCongr e f).trans (socketsAppend xs ys).symm).symm =
      Sum.elim ((z ∘ Sum.inl) ∘ e.symm) ((z ∘ Sum.inr) ∘ f.symm) ∘ socketsAppend xs ys := by
    funext j
    change z ((Equiv.sumCongr e f).symm (socketsAppend xs ys j)) =
      Sum.elim _ _ (socketsAppend xs ys j)
    cases socketsAppend xs ys j <;> rfl
  rw [split, exactWeight_append]

theorem exactWeight_chain (holes : ℕ → Type) (os : ℕ → List (Occurrence F k))
    (e : ∀ i, holes i ≃ Sockets (os i)) (n : ℕ) (z : Bank holes n → Bool) :
    exactWeight (chainCalls os n) (z ∘ (chainSockets holes os e n).symm) =
      weights holes (fun i a => exactWeight (os i) (a ∘ (e i).symm)) n z := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let read : Bank holes n ⊕ holes (n+1) → Bool := z
    exact (pair_socket_weight (chainCalls os n) (os (n+1)) (chainSockets holes os e n)
      (e (n+1)) read).trans (congrArg
        (fun a => a * exactWeight (os (n+1)) ((read ∘ Sum.inr) ∘ (e (n+1)).symm))
        (ih (read ∘ Sum.inl)))


end Hierarchy.Tagged.RadixStage

end
end OAI
