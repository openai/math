import OAI.Computability.BorderVNP.CubePhysicalHost
import OAI.Computability.BorderVNP.CubePhysicalPaddingZeros

/-! # Removing zero padding from the original cell contraction

The sum with shared antipodal words is the same as the original fine
network's contraction. The correspondence uses the public bit-slot
injection and the private/public partition of the actual network edges.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing Diagonal.CellEntries MvPolynomial
open scoped Classical

set_option synthInstance.maxSize 512
set_option maxRecDepth 3000

variable {n d blocks width D : ℕ} {P : Type*} {bits : P → ℕ}
variable {Cell : Type} [Fintype Cell] [DecidableEq Cell]
variable {Param Gadget E : Type*} [CommSemiring E]

private theorem split_sum {A U V R : Type*} [Fintype A] [Fintype U] [Fintype V] [AddCommMonoid R]
    (e : A ≃ U × V) (f : U → V → R) (g : A → R) (he : ∀ x y, f x y = g (e.symm (x,y))) :
    ∑ x, ∑ y, f x y = ∑ a, g a :=
  (Fintype.sum_prod_type (fun v : U × V => f v.1 v.2)).symm.trans
    (Fintype.sum_equiv e.symm _ g fun v => he v.1 v.2)

private theorem same_sum {A R : Type*} [AddCommMonoid R] (i j : Fintype A) (f : A → R) :
    ∑ x ∈ @Finset.univ A i, f x = ∑ x ∈ @Finset.univ A j, f x :=
  congrArg (fun t : Fintype A => ∑ x ∈ @Finset.univ A t, f x) (Subsingleton.elim i j)

private theorem pinned_explicit {A B R : Type*} [Fintype A] [Fintype B] [AddCommMonoid R]
    (bi : Fintype (B → Bool)) (ai : Fintype (A → Bool)) (e : A ↪ B) (w : (A → Bool) → R) :
    (∑ x ∈ @Finset.univ (B → Bool) bi, if ∀ j ∉ Set.range e, x j = false then w (x ∘ e) else 0) =
      ∑ y ∈ @Finset.univ (A → Bool) ai, w y := by
  exact (same_sum bi _ _).trans ((sum_pinned e w).trans (same_sum _ ai w))

private theorem split_pinned {A B U V R : Type*} [Fintype A] [Fintype B] [Fintype U] [Fintype V]
    [AddCommMonoid R] (ai : Fintype (A → Bool)) (e : (B → Bool) ≃ U × V) (slot : A ↪ B)
    (f : U → V → R) (w : (A → Bool) → R)
    (hp : ∀ u v, (∀ j ∉ Set.range slot, e.symm (u,v) j = false) → f u v = w (e.symm (u,v) ∘ slot))
    (hn : ∀ u v, (¬∀ j ∉ Set.range slot, e.symm (u,v) j = false) → f u v = 0) :
    (∑ u, ∑ v, f u v) = ∑ y ∈ @Finset.univ (A → Bool) ai, w y := by
  let g (x : B → Bool) := if ∀ i ∉ Set.range slot, x i = false then w (x ∘ slot) else 0
  have hg (u v) : f u v = g (e.symm (u,v)) := by
    unfold g
    split
    · exact hp _ _ ‹_›
    · exact hn _ _ ‹_›
  exact (split_sum e f g hg).trans (pinned_explicit inferInstance ai slot w)

/-- Fix the private assignments. The two equal end words of each antipodal
pair and the retained singleton wires are exactly the original exterior bits
after deleting the zero-filled tails. -/
theorem sum_host_common (N : Network D P bits) (cell : N.Site → Cell)
    (slot : LiveBit N cell ↪ Slot n d blocks width)
    (tags : N.Tables (Entry Param Gadget)) (values : Gadget → E) (x : Ports bits)
    (privateBits : ∀ c, N.InsideAssignment cell c) :
    (∑ single, ∑ pairs : Packet n d blocks → Vertex n → Fin width → Bool,
      interpret values (host N cell slot tags x privateBits single (fun p e => pairs p e.1))) =
    ∑ y : LiveBit N cell → Bool, interpret values (assignmentEntry N tags
      ((N.cellAssignmentEquiv cell).symm ((fun e j => y ⟨e,j⟩), privateBits)) x) := by
  let w (y : LiveBit N cell → Bool) := interpret values (assignmentEntry N tags
    ((N.cellAssignmentEquiv cell).symm ((fun e j => y ⟨e,j⟩), privateBits)) x)
  let f (single : SingleSlot n d blocks width → Bool) (pairs : Packet n d blocks → Vertex n → Fin width → Bool) :=
    interpret values (host N cell slot tags x privateBits single (fun p e => pairs p e.1))
  apply split_pinned inferInstance (commonEquiv n d blocks width) slot f w
  · intro single pairs hp
    unfold f
    rw [host_common, ite_eq_left hp]
    rfl
  · intro single pairs hn
    unfold f
    rw [host_common, ite_eq_right hn, map_zero]

/-- Sum all shared crossing bits and all private cell assignments, counting
each full assignment once and reading the original exterior port values. -/
theorem sum_common_eq_value (N : Network D P bits) (cell : N.Site → Cell)
    (slot : LiveBit N cell ↪ Slot n d blocks width)
    (tags : N.Tables (Entry Param Gadget)) (values : Gadget → E) (x : Ports bits) :
    (∑ privateBits, ∑ single, ∑ pairs : Packet n d blocks → Vertex n → Fin width → Bool,
      interpret values (host N cell slot tags x privateBits single (fun p e => pairs p e.1))) =
    N.value (fun v r p => interpret values (tags v r p)) x := by
  simp_rw [sum_host_common N cell slot tags values x]
  rw [value_eq_tag_sum, Finset.sum_comm]
  let outer : (LiveBit N cell → Bool) ≃ N.CrossingAssignment cell :=
    Equiv.piCurry (fun e : N.CrossingEdge cell => fun _ : Fin (N.width e.val) => Bool)
  let e := (outer.prodCongr (Equiv.refl (∀ c, N.InsideAssignment cell c))).trans
    (N.cellAssignmentEquiv cell).symm
  let f (v : (LiveBit N cell → Bool) × (∀ c, N.InsideAssignment cell c)) :=
    interpret values (assignmentEntry N tags (e v) x)
  exact (Fintype.sum_prod_type f).symm.trans (Fintype.sum_equiv e _ _ fun _ => rfl)

end Cube.Physical

end BorderVNP
end Computability
end OAI
