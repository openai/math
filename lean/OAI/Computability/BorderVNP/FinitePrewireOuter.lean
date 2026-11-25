import OAI.Computability.BorderVNP.ParseBatchPrewireValue
import OAI.Computability.BorderVNP.PackedGridInitial

/-! # Physical equality fanout and zero clamps for an arbitrary input bit network

The outer tensor has one visible terminal for each retained field slot and one
joining terminal per original query bit. Each private interior edge name is one
summed Boolean index. A degree-two test at each joining terminal installs its
literal clamp or its equality to the corresponding public or interior wire.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FinitePrewire

open Crossing ParseBatch
open scoped BigOperators Classical

variable {X Y I : Type} [Fintype X] [Fintype Y] [Fintype I]
    (f : X → (Y ⊕ I) ⊕ Bool)

/-- The join bit and its source. For a clamp the second incidence is unused by
the truth table and uses the join bit's existing equality chain. -/
def operand (x : X) (j : Fin 2) : (Y ⊕ X) ⊕ I :=
  if j = 0 then .inl (.inr x) else
    match f x with
    | .inl (.inl y) => .inl (.inl y)
    | .inl (.inr e) => .inr e
    | .inr _ => .inl (.inr x)

/-- The bounded-degree physical fanout and join-test layout. -/
noncomputable abbrev outer := Layout.ofArguments (fun _ : X => 2) (operand f)

/-- At each join compare the old input with its wired source or its actual clamp. -/
def test {A : Type*} [Zero A] [One A] (x : X) (u : Fin 2 → Bool) : A :=
  if u 0 = (f x).elim (fun _ => u 1) id then 1 else 0

omit [Fintype X] [Fintype Y] [Fintype I] in
private theorem test_read {A : Type*} [Zero A] [One A]
    (y : Y → Bool) (x : X → Bool) (h : I → Bool) (t : X) :
    test (A := A) f t (fun j => Sum.elim (Sum.elim y x) h (operand f t j)) =
      if x t = Prewire.readInput f y h t then 1 else 0 := by
  rcases ht : f t with (v | e) | b <;> simp [test, operand, Prewire.readInput, ht]

/-- The boundary tensor of the fanout component, before attaching the old input
network. The same interior assignment supplies every occurrence of a named bit. -/
theorem outer_value {A : Type*} [CommSemiring A] (y : Y → Bool) (x : X → Bool) :
    (outer f).network.value ((outer f).tables (test (A := A) f)) (fun p _ => p.elim y x) =
      ∑ h : I → Bool, if x = Prewire.readInput f y h then 1 else 0 := by
  refine ((outer f).network_value (test (A := A) f) (Sum.elim y x)).trans ?_
  unfold Layout.contract
  apply Finset.sum_congr (Finset.ext fun _ => by simp)
  intro h _
  change (∏ t, test f t (fun j => Sum.elim (Sum.elim y x) h (operand f t j))) = _
  simp_rw [test_read]
  rw [Fintype.prod_boole]
  by_cases he : x = Prewire.readInput f y h
  · simp [he]
  · simp [he, funext_iff.not.mp he]

/-- The fanout model has bit cables, distinct visible leaf sites and at most
three incident endpoints at every vertex. -/
theorem outer_trivalent : (outer f).network.Trivalent := by
  refine ⟨fun _ => rfl,fun v => ?_⟩
  have ht := (outer f).degree_le_three (fun _ => by change 2 ≤ 3; decide) v
  unfold Network.bitDegree
  convert ht using 2
  ext e
  rcases e with p | ⟨e,b⟩
  · simp [Layout.incident]
  · cases b <;> simp [Layout.incident]

/-- The full wiring overhead is linear in the number of old input slots.
The bound includes both the old join leaves and the retained public leaves. -/
theorem outer_volume (h : Fintype.card Y + Fintype.card I ≤ Fintype.card X) :
    (outer f).network.bitVolume ≤ 15 * Fintype.card X := by
  unfold Network.bitVolume
  rw [Layout.volume_eq,Layout.uses_eq]
  simp only [outer,Layout.ofArguments,Fintype.card_sum,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id]
  omega

end FinitePrewire

end BorderVNP
end Computability
end OAI
