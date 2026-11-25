import OAI.Computability.BorderVNP.PackedBankInheritedRead
import OAI.Computability.BorderVNP.PackedOldDirectory

/-! # Inherited site words in public sparse and dense cable order

The old private table uses its own cable addresses. Relabeling a cable in the
public array or compacting the occupied rows pulls back each original bit
with its original lane ordinal. Virtual rows have no lanes and introduce no
extra input or observation. The same formula holds for tagged and field tables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.CombiningStep Shortening.SeedIntervals DirectoryCircuit
open Diagonal.CellEntries
open scoped Classical

variable {D M : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
  (rows : N.Edge ↪ Fin M) (dummy : Fin M → N.Site)

/-- Pull the site-local input words on a public cable array back to the live
old incidents and their actual bit indices. No virtual array entry is read. -/
noncomputable def liveWords (v : N.Site)
    (w : ∀ z : Incident (Names.layout N rows dummy) v, Fin ((Names.layout N rows dummy).width z.val) → Bool)
    (z : Incident N v) (k : Fin (N.width z.val)) : Bool :=
  w ⟨Names.slot N rows z.val, z.property.imp (fun h => (Names.src_slot N rows dummy z.val).trans h)
    (fun h => (Names.dst_slot N rows dummy z.val).trans h)⟩
    (Fin.cast (Names.width_slot N rows dummy z.val).symm k)

/-- Exact old row of a named physical array, pointwise before any private contraction. -/
theorem named_table {R : Type*} (t : N.Tables R) (v : N.Site)
    (w : ∀ z : Incident (Names.layout N rows dummy) v, Fin ((Names.layout N rows dummy).width z.val) → Bool)
    (port : ∀ u : {u : P // N.attach u = v}, Fin (bits u.val) → Bool) :
    Names.tables N rows dummy t v w port = t v (liveWords N rows dummy v w) port := rfl

/-- Unoccupied virtual rows contribute no bit to any old site. -/
theorem no_virtual_input (r : Fin M) (hr : r ∉ Set.range rows) :
    IsEmpty (Fin ((Names.layout N rows dummy).width (Names.rowSlot r))) := by
  rw [(Names.unused_row N rows dummy r hr).2.2]
  infer_instance

variable {K : Type*} [Field K] {m : ℕ} [NeZero D] (e : PaidIdentity K D m) (p : Pack D P bits K)
    (slot : p.layout.Edge ↪ Fin M) {A : Type} [Fintype A]
    (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool)

private noncomputable abbrev dense := densePack p slot
private noncomputable abbrev which := CutCircuit.denseBin p.layout slot bin
private noncomputable abbrev orient := positive ∘ (Names.denseSlot p.layout slot).symm

variable (q : Counts e (dense p slot) (which p slot bin) perm)

private noncomputable abbrev next := output e (dense p slot) (which p slot bin) perm (orient p slot positive) first q

/-- The reconstructed input of the original site after the actual dense-save,
band split, cut and simultaneous profile insertion. -/
noncomputable def denseOldWords (y : (next e p slot bin perm positive first q).layout.Assignment)
    (v : p.layout.Site) : ∀ z : Incident p.layout v, Fin (p.layout.width z.val) → Bool :=
  liveWords p.layout (Names.denseRank p.layout slot).toEmbedding
    (fun k => p.layout.src ((Names.denseRank p.layout slot).symm k)) v
    (oldWireWords e (dense p slot) (which p slot bin) perm (orient p slot positive) first q y v)

/-- The dense successor reads the original field table once at these old words
and at the original external port words, on every assignment. -/
theorem dense_old_read (y : (next e p slot bin perm positive first q).layout.Assignment)
    (x : Ports bits) (v : p.layout.Site) :
    let out := next e p slot bin perm positive first q
    out.layout.read out.table y x (.inl v) =
      p.table v (denseOldWords e p slot bin perm positive first q y v) (oldPortWords p x v) :=
  old_table_read e (dense p slot) (which p slot bin) perm (orient p slot positive) first q y x v

/-- Arbitrary original tagged rows survive dense-save and the actual tagged
combining round with their old internal and external input ordinals. -/
theorem dense_tagged_read {Param Gadget : Type*} (tags : p.layout.Tables (Entry Param Gadget))
    (position : e.Entry → Gadget) (y : (next e p slot bin perm positive first q).layout.Assignment)
    (x : Ports bits) (v : p.layout.Site) :
    let src : Pack D P bits (Entry Param Gadget) := densePack ⟨p.layout,tags⟩ slot
    let out := roundTags src (which p slot bin) perm e position (orient p slot positive) first q
    out.layout.read out.table y x (.inl v) =
      tags v (denseOldWords e p slot bin perm positive first q y v) (oldPortWords p x v) :=
  old_tagged_read e (dense p slot) (which p slot bin) perm (orient p slot positive) first q
    (densePack (⟨p.layout,tags⟩ : Pack D P bits (Entry Param Gadget)) slot).table position y x v

end Packing.Inherited

end BorderVNP
end Computability
end OAI
