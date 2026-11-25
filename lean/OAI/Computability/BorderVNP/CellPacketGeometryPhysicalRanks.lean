import OAI.Computability.BorderVNP.CellPacketGeometryHistoryOutput
import OAI.Computability.BorderVNP.CellPacketGeometryDescriptorInverse

/-! # Exclusive ends of physical descriptor sections in the native history packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native

open Packing.Inherited.FrozenTape VPVNP.VerifierNetwork ParseBatchSort CellSparse Packet LiveWords

variable {a C cap k w d t q : ℕ} {R B U V E Orig σ : Type}
variable [Fintype R] [Fintype B] [Fintype U] [Fintype V] [Fintype E] [Fintype σ]
variable (F : Feeds σ R B U V E a d t k w) (S : Schema R B) (L : Schema U V)
    (boxes : Fin a → List (Source.Box Orig)) (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ u, (L.tags u).length≤cap)
    (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E))
    (hd : d≤q) (ht : t≤q) (room : a<2^q) (key : C<2^k)
    (hs : ∀ r, S.width r≤w) (hl : ∀ u, L.width u≤w)
    (baseOwner : Fin (roster a S L).length → Fin (C+1)) (pointer : Orig → (template S L boxes sh lh priv rep).Fields)
    (pad : (roster a S L).length<2^q) (dest H : ℕ) (x : σ → Bool) (mem : ℕ → ℕ)
local notation3 (prettyPrint := false) "T₀" => template S L boxes sh lh priv rep
local notation3 (prettyPrint := false) "emit" => F.ordered S L boxes sh lh priv rep hd ht room key hs hl baseOwner pointer pad dest H

set_option maxHeartbeats 800000 in
/-- Every rank word of the *second* physical sort identifies a real
descriptor position. In particular the last, exclusive rank of a real
cell's operand sequence is strictly below the next reserved native array. -/
theorem Feeds.descriptor_room (wide : 2^(T₀).chunkDepth≤2^w) (upper : ℕ)
    (gap : descriptorBank dest (T₀).publicDepth+2^(T₀).chunkDepth ≤ upper)
    (read : ∀ i : Fin (Total (T₀).publicDepth (T₀).chunkDepth), mem (dest+i.val) =
      value (fun j => (emit).eval x (.inl (i,j)))) :
    ∀ i : Fin (2^(T₀).chunkDepth), let base := descriptorBank dest (T₀).publicDepth
      mem (base+(2^(T₀).chunkDepth+i.val)) < 2^(T₀).chunkDepth ∧
      base+mem (base+(2^(T₀).chunkDepth+i.val)) < upper := by
  let up := source (cap := cap) S L (access : Access R B U V E (Bundle R B U V E a d t k w) a d t k w)
    hd ht room key hs hl
  let anchors₀ := anchors S L (access : Access R B U V E (Bundle R B U V E a d t k w) a d t k w) hd ht room
  have output (i : Fin (Total (T₀).publicDepth (T₀).chunkDepth)) : mem (dest+i.val)=value (fun j =>
      ((T₀).orderedFrame up anchors₀ baseOwner pointer pad dest H).eval (F.frame.eval x) (.inl (i,j))) :=
    (read i).trans (congrArg value (funext fun j => F.ordered_eval S L boxes sh lh priv rep hd ht room key hs hl
      baseOwner pointer pad dest H x (.inl (i,j))))
  obtain ⟨π,rank⟩ := descriptorInverse_of_output _ _ (F.frame.eval x) dest mem wide output
  intro i base
  have got : mem (base+(2^(T₀).chunkDepth+i.val)) < 2^(T₀).chunkDepth := by
    rw [← Nat.add_assoc]
    exact (rank i).trans_lt (π.symm i).isLt
  exact ⟨got,(Nat.add_lt_add_left got base).trans_le gap⟩

end CellPacketGeometry.History.Native

end BorderVNP
end Computability
end OAI
