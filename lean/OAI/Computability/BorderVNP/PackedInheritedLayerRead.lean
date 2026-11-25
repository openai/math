import OAI.Computability.BorderVNP.PackedInheritedPieces
import OAI.Computability.BorderVNP.PackedBankInheritedValue

/-! # The layer projection reads the exact whole input words of the inherited table

The virtual-site source orders on the two generations enclose the concrete
band/port projection. Applying that projection to the current physical input
vector retrieves precisely the old table's incident cable and exterior words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.CombiningStep Shortening.SeedIntervals
open scoped Classical

variable {D m ne nf np : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
    {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

private noncomputable abbrev G := (output e p bin perm positive first q).layout

variable (v : p.layout.Site) (oldID : p.layout.Edge ↪ Fin ne)
    (nextID : (G e p bin perm positive first q).Edge ↪ Fin nf) (portID : P ↪ Fin np)

/-- The concrete packed successor inputs at the retained site's current physical
address, using the actual cable assignment and the supplied free port words. -/
noncomputable def successorInput (y : (G e p bin perm positive first q).Assignment) (x : Ports bits) :
    Fin (incoming (G e p bin perm positive first q) (.inl v)) → Bool :=
  inputWords (G e p bin perm positive first q) nextID portID (.inl v) (fun u => y u.val) (fun u => x u.val)

/-- Reassembly of the old site's complete packed input by the actual physical layer map. -/
theorem layerRead_inputs (y : (G e p bin perm positive first q).Assignment) (x : Ports bits) :
    successorInput e p bin perm positive first q v nextID portID y x ∘
      layerRead e p bin perm positive first q v oldID nextID portID =
      inputWords p.layout oldID portID v (oldWireWords e p bin perm positive first q y v) (oldPortWords p x v) := by
  let G := G e p bin perm positive first q
  let O := sourceOrder p.layout oldID portID v
  let S := sourceOrder G nextID portID (.inl v)
  let z := fun u : Incident G (.inl v) => y u.val
  let t := fun u : Attached G (.inl v) => x u.val
  funext i
  obtain ⟨l,rfl⟩ := O.surjective i
  change inputWords G nextID portID (.inl v) z t
    (S (laneOfOld e p bin perm positive first q v (O.symm (O l)))) = _
  rw [O.symm_apply_apply]
  rcases l with ⟨u,k⟩ | ⟨u,k⟩
  · let b := (p.layout.bandIndex (label p.layout bin perm m) u.val).symm k
    change inputWords G nextID portID (.inl v) z t
      (S (.inl ⟨oldBandWire e p bin perm positive first q v u b.1,
        Fin.cast (oldBandWire_width e p bin perm positive first q v u b.1).symm b.2⟩)) = _
    let edge := oldBandWire e p bin perm positive first q v u b.1
    let index := Fin.cast (oldBandWire_width e p bin perm positive first q v u b.1).symm b.2
    exact (inputWords_wire G nextID portID (.inl v) z t edge index).trans
      ((oldBandWord_read e p bin perm positive first q y v u b.1 b.2).symm.trans
        (inputWords_wire p.layout oldID portID v (oldWireWords e p bin perm positive first q y v) (oldPortWords p x v) u k).symm)
  · change inputWords G nextID portID (.inl v) z t (S (.inr ⟨portOfOld e p bin perm positive first q v u,k⟩)) = _
    exact (inputWords_port G nextID portID (.inl v) z t (portOfOld e p bin perm positive first q v u) k).trans
      (inputWords_port p.layout oldID portID v (oldWireWords e p bin perm positive first q y v) (oldPortWords p x v) u k).symm

/-- Transfer a physical cover to a site state with the same certified input extent. -/
theorem Covers.castOld {a b n : ℕ} {cuts : List Slice} {read : Fin b → Fin n} (ha : a = b)
    (cover : Covers b n cuts read) : Covers a n cuts (read ∘ Fin.cast ha) := by
  subst a
  exact cover

end Packing.Inherited

end BorderVNP
end Computability
end OAI
