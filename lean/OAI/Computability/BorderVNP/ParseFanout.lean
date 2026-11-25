import OAI.Computability.BorderVNP.CrossingNetwork
import Mathlib.Logic.Equiv.Fintype

/-! # Splitting shared Boolean variables into bit wires

A constraint can refer to the same Boolean variable as many other constraints.
For each variable make a chain of ternary equality tensors, one for each use.
An external variable is pinned at its first endpoint. The first bit of a private
chain is summed freely. Every choice of private variables extends uniquely to
an assignment of nonzero equality factors.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatch

open scoped BigOperators Classical
open Crossing

/-- Incidence list of local factors on visible and private variables.
The slots of the factors are listed exactly once among the uses of their variables. -/
structure Layout (X W T : Type) where
  /-- Number of bit arguments to each local factor. -/
  arity : T → ℕ
  /-- Number of occurrences of each variable, possibly zero. -/
  fanout : X ⊕ W → ℕ
  /-- Assignment of variable occurrences to the slots of factors. -/
  slots : (Σ u, Fin (fanout u)) ≃ (Σ t, Fin (arity t))

namespace Layout

variable {X W T : Type} [Fintype X] [Fintype W] [Fintype T]
variable (L : Layout X W T)

/-- A junction that distributes a variable to one occurrence in a local factor. -/
abbrev Use := Σ u, Fin (L.fanout u)

/-- Successive wires that carry a variable past its junctions. -/
abbrev Spine := Σ u, Fin (L.fanout u + 1)

/-- The factor vertices, initial endpoints, junctions and final endpoints. -/
abbrev Site := T ⊕ ((X ⊕ W) ⊕ (L.Use ⊕ (X ⊕ W)))

/-- The chain wires and the separate wires from junctions to factor occurrences. -/
abbrev Edge := L.Spine ⊕ L.Use

private abbrev start (u : X ⊕ W) : L.Site := .inr (.inl u)
private abbrev junction (j : L.Use) : L.Site := .inr (.inr (.inl j))
private abbrev finish (u : X ⊕ W) : L.Site := .inr (.inr (.inr u))

/-- The graph with one bit per internal wire and per external port. -/
noncomputable abbrev network : Crossing.Network 0 X (fun _ => 1) where
  Site := L.Site
  Edge := L.Edge
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src := Sum.elim (fun j => Fin.cases (L.start j.1) (fun i => L.junction ⟨j.1, i⟩) j.2) L.junction
  dst := Sum.elim (fun j => Fin.lastCases (L.finish j.1) (fun i => L.junction ⟨j.1, i⟩) j.2)
    (fun j => .inl (L.slots j).1)
  width _ := 1
  attach x := L.start (.inl x)
  position _ := 0
  in_ball _ := by simp

variable {R : Type*} [CommSemiring R]

/-- Original factor values before splitting variables into wire occurrences. -/
abbrev Factors (R : Type*) := (t : T) → (Fin (L.arity t) → Bool) → R

/-- The original contraction, summed over the private variables only. -/
noncomputable def contract (f : L.Factors R) (x : X → Bool) : R :=
  ∑ w : W → Bool, ∏ t, f t fun i => Sum.elim x w (L.slots.symm ⟨t,i⟩).1

private theorem wire_dst_factor (t : T) (i : Fin (L.arity t)) :
    L.network.dst (.inr (L.slots.symm ⟨t,i⟩)) = .inl t := by simp [network]

/-- Tables for the original factors and the new unary, binary and ternary copy sites. -/
noncomputable def tables (f : L.Factors R) : L.network.Tables R
  | .inl t => fun a _ => f t fun i =>
    a ⟨.inr (L.slots.symm ⟨t,i⟩), Or.inr (L.wire_dst_factor t i)⟩ 0
  | .inr (.inl (.inl x)) => fun a ports =>
    if a ⟨.inl ⟨.inl x,0⟩, Or.inl (by simp [network])⟩ 0 = ports ⟨x,rfl⟩ 0 then 1 else 0
  | .inr (.inl (.inr _)) => fun _ _ => 1
  | .inr (.inr (.inl ⟨u,i⟩)) => fun a _ =>
    let prev := a ⟨.inl ⟨u,i.castSucc⟩, Or.inr (by simp [network])⟩ 0
    let next := a ⟨.inl ⟨u,i.succ⟩, Or.inl (by simp [network])⟩ 0
    let leaf := a ⟨.inr ⟨u,i⟩, Or.inl rfl⟩ 0
    if prev = next ∧ prev = leaf then 1 else 0
  | .inr (.inr (.inr _)) => fun _ _ => 1

/-- The unique wire assignment induced by the original variable values. -/
def wires (x : X → Bool) (w : W → Bool) : L.network.Assignment :=
  fun e _ => Sum.elim (fun j : L.Spine => Sum.elim x w j.1)
    (fun j : L.Use => Sum.elim x w j.1) e

private noncomputable def extract (a : L.network.Assignment) (j : W) : Bool :=
  a (.inl ⟨.inr j, 0⟩) 0

private def Consistent (x : X → Bool) (a : L.network.Assignment) : Prop :=
  (∀ i : X, a (.inl ⟨.inl i,0⟩) 0 = x i) ∧ ∀ j : L.Use,
    a (.inl ⟨j.1,j.2.castSucc⟩) 0 = a (.inl ⟨j.1,j.2.succ⟩) 0 ∧
    a (.inl ⟨j.1,j.2.castSucc⟩) 0 = a (.inr j) 0

private theorem consistent_wires (x : X → Bool) (w : W → Bool) :
    L.Consistent x (L.wires x w) := ⟨fun _ => rfl, fun _ => ⟨rfl, rfl⟩⟩

private theorem wires_extract (x : X → Bool) (a : L.network.Assignment)
    (h : L.Consistent x a) : L.wires x (L.extract a) = a := by
  have hc (u : X ⊕ W) (i : Fin (L.fanout u + 1)) :
      Sum.elim x (L.extract a) u = a (.inl ⟨u,i⟩) 0 := by
    induction i using Fin.induction with
    | zero => cases u with
      | inl j => exact (h.1 j).symm
      | inr j => rfl
    | succ i ih => exact ih.trans (h.2 ⟨u,i⟩).1
  funext e b
  have hb : b = 0 := Subsingleton.elim ..
  subst b
  cases e with
  | inl j => exact hc j.1 j.2
  | inr j => exact (hc j.1 j.2.castSucc).trans (h.2 j).2

private theorem product_read (f : L.Factors R) (x : X → Bool) (a : L.network.Assignment) :
    (∏ v, L.network.read (L.tables f) a (fun i _ => x i) v) =
      if L.Consistent x a then ∏ t, f t (fun i => a (.inr (L.slots.symm ⟨t,i⟩)) 0) else 0 := by
  classical
  simp only [network, Network.read, Fintype.prod_sum_type, tables, Finset.prod_const_one,
    mul_one, Consistent]
  simp [Finset.prod_boole, ← ite_and, mul_ite]
  congr 1
  exact propext and_comm

/-- Summing the network wires gives exactly the original contraction, over any commutative
semiring. Copying a variable adds no multiplicity. -/
theorem network_value (f : L.Factors R) (x : X → Bool) :
    L.network.value (L.tables f) (fun i _ => x i) = L.contract f x := by
  classical
  trans ∑ a : L.network.Assignment, if L.Consistent x a then
    ∏ t, f t (fun i => a (.inr (L.slots.symm ⟨t,i⟩)) 0) else 0
  · unfold Network.value
    apply Finset.sum_congr _ fun a _ => L.product_read f x a
    ext
    simp
  unfold contract
  rw [← Finset.sum_filter]
  apply Finset.sum_bij' (fun a _ => L.extract a) (fun w _ => L.wires x w)
  · intro _ _; exact Finset.mem_univ _
  · intro _ _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, L.consistent_wires ..⟩
  · intro a h; exact L.wires_extract x a (Finset.mem_filter.mp h).2
  · intro _ _; rfl
  · intro a h
    have hw := L.wires_extract x a (Finset.mem_filter.mp h).2
    apply Finset.prod_congr rfl
    intro t _
    apply congrArg (f t)
    funext i
    exact (congrFun (congrFun hw (.inr (L.slots.symm ⟨t,i⟩))) 0).symm

/-- If the original factor tests force one private assignment, splitting all occurrences
preserves its coefficient and forces the corresponding internal wire assignment. This
identity also applies when the distinguished coefficient is zero. -/
theorem product_read_of_unique (f : L.Factors R) (x : X → Bool) (w₀ : W → Bool) (c : R)
    (hf : ∀ w : W → Bool,
      (∏ t, f t fun i => Sum.elim x w (L.slots.symm ⟨t,i⟩).1) = if w = w₀ then c else 0)
    (a : L.network.Assignment) :
    (∏ v, L.network.read (L.tables f) a (fun i _ => x i) v) =
      if a = L.wires x w₀ then c else 0 := by
  classical
  rw [L.product_read]
  by_cases ha : L.Consistent x a
  · rw [ite_eq_left ha]
    let w := L.extract a
    have hw : L.wires x w = a := L.wires_extract x a ha
    rw [← hw]
    change (∏ t, f t fun i => Sum.elim x w (L.slots.symm ⟨t,i⟩).1) = _
    rw [hf]
    by_cases he : w = w₀
    · simp [he]
    · have hne : L.wires x w ≠ L.wires x w₀ := fun h => he (congrArg L.extract h)
      simp [he, hne]
  · have hne : a ≠ L.wires x w₀ := fun h => ha (h ▸ L.consistent_wires x w₀)
    simp [ha, hne]

end Layout
end ParseBatch

end BorderVNP
end Computability
end OAI
