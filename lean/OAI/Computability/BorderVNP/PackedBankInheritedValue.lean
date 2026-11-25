import OAI.Computability.BorderVNP.PackedBankInheritedDense
import OAI.Computability.BorderVNP.PackedInheritedAddresses
import OAI.Computability.BorderVNP.PackedInheritedStaging

/-! # Retaining the contraction of a nondeterministic private site

A site's value is the sum over its private choices. The new interval rows
determine exactly one copy of its old incident words for each successor
assignment, while the old private choices and their weights are preserved.
The reconstruction is expressed in the physical virtual-cell input order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.CombiningStep
open scoped Classical

variable {D ne np : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np) (v : N.Site)

/-- Pack the actual old incident words and attached exterior ports in virtual-cell order. -/
noncomputable def inputWords (z : ∀ c : Incident N v, Fin (N.width c.val) → Bool)
    (x : ∀ u : Attached N v, Fin (bits u.val) → Bool) (k : Fin (incoming N v)) : Bool :=
  ((sourceOrder N edgeID portID v).symm k).elim (fun b => z b.1 b.2) (fun b => x b.1 b.2)

/-- The stored input vector returns the physical cable at its exact source ordinal. -/
theorem inputWords_wire (z : ∀ c : Incident N v, Fin (N.width c.val) → Bool)
    (x : ∀ u : Attached N v, Fin (bits u.val) → Bool) (c : Incident N v) (k : Fin (N.width c.val)) :
    inputWords N edgeID portID v z x (sourceOrder N edgeID portID v (.inl ⟨c,k⟩)) = z c k := by
  rw [inputWords,(sourceOrder N edgeID portID v).symm_apply_apply]; rfl

/-- The stored input vector returns the external port at its exact source ordinal. -/
theorem inputWords_port (z : ∀ c : Incident N v, Fin (N.width c.val) → Bool)
    (x : ∀ u : Attached N v, Fin (bits u.val) → Bool) (u : Attached N v) (k : Fin (bits u.val)) :
    inputWords N edgeID portID v z x (sourceOrder N edgeID portID v (.inr ⟨u,k⟩)) = x u k := by
  rw [inputWords,(sourceOrder N edgeID portID v).symm_apply_apply]; rfl

/-- A private program realizes the physical local table after summing all of its
old work bits for every cable and port input. -/
def Site.Models {R : Type*} [AddCommMonoid R] (s : Site) (hsize : s.incoming = Inherited.incoming N v)
    (weight : List (Bool × Option ℕ) → R) (table : N.Tables R) : Prop :=
  ∀ z x, s.value weight (fun k => inputWords N edgeID portID v z x (Fin.cast hsize k)) = table v z x

variable [NeZero D] {K : Type*} [Field K] {m : ℕ} (e : PaidIdentity K D m)
    (p : Pack D P bits K) {A : Type} [Fintype A] (bin : p.layout.Edge → Option A)
    (perm : Fin D → Equiv.Perm A) (positive : p.layout.Edge → Bool) (first : Fin D × Bool)
    (q : Counts e p bin perm)

private noncomputable abbrev out := output e p bin perm positive first q

/-- Once the concrete interval cover reads the physical successor bits, retaining
the older sparse state realizes the actual old-site entry of the sewn pack.
This includes arbitrary multiplicity of successful old private assignments. -/
theorem value_retain_read (v : p.layout.Site) (oldID : p.layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (s : Site) (hsize : s.incoming = incoming p.layout v) (locality : s.Local)
    (weight : List (Bool × Option ℕ) → K) (models : s.Models p.layout oldID portID v hsize weight p.table)
    {n : ℕ} (cuts : List Slice) (read : Fin s.incoming → Fin n) (cover : Covers s.incoming n cuts read)
    (input : Fin n → Bool) (y : (out e p bin perm positive first q).layout.Assignment)
    (x : Ports bits) (hread : ∀ k, input (read k) = inputWords p.layout oldID portID v
      (oldWireWords e p bin perm positive first q y v) (oldPortWords p x v) (Fin.cast hsize k)) :
    (s.retain n cuts).value weight input =
      (out e p bin perm positive first q).layout.read (out e p bin perm positive first q).table y x (.inl v) := by
  rw [value_retain s locality cuts read cover,old_table_read]
  exact (congrArg (s.value weight) (funext hread)).trans (models _ _)

end Packing.Inherited

end BorderVNP
end Computability
end OAI
