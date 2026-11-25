import OAI.Computability.BorderVNP.PackedBottomReports
import OAI.Computability.BorderVNP.PackedInheritedAddresses
import OAI.Computability.BorderVNP.PackedGridExternal

/-! # Public strided incidence ties at an original bottom box

Each public cable or grouped external port contributes a single record. That
record routes every copy's complete subword into the copy's padded private box.
The work area can therefore use copy-major order while the public incident
words use cable-major order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomRepeat

open Crossing Inherited CellSparse BottomReports
open scoped Classical

variable {D qe qa : ℕ} {A : Type} [Fintype A] {width : A → ℕ}
variable (N : Network D A width) (edges : N.Edge ↪ Fin qe) (ports : A ↪ Fin qa) (v : N.Site)

/-- The public bottom network with all internal and grouped external widths repeated. -/
abbrev wide (copies : ℕ) : Network D A (fun p => copies*width p) where
  Site := N.Site
  Edge := N.Edge
  finiteSite := N.finiteSite
  finiteEdge := N.finiteEdge
  src := N.src
  dst := N.dst
  width e := copies*N.width e
  attach := N.attach
  position := N.position
  in_ball := N.in_ball

/-- A public cable end or a grouped port attached to this site. -/
abbrev Row := Incident N v ⊕ Attached N v

/-- The one-copy width of the physical incidence word. -/
def rowWidth : Row N v → ℕ := Sum.elim (fun e => N.width e.val) (fun a => width a.val)

/-- Base of the word in a one-copy canonical virtual site. -/
noncomputable def oneStart : Row N v → ℕ :=
  Sum.elim (wireStart N edges ports v) (portStart N edges ports v)

/-- Base in the repeated incidence area immediately following the private work slab. -/
noncomputable def wideStart (copies : ℕ) : Row N v → ℕ :=
  Sum.elim (wireStart (wide N copies) edges ports v) (portStart (wide N copies) edges ports v)

/-- The single public record for all copies and lanes of one physical word. -/
noncomputable def tie (copies capFine stride : ℕ) (r : Row N v) : Record :=
  .equal copies (rowWidth N v r)
    ⟨capFine+oneStart N edges ports v r,stride,1⟩
    ⟨copies*stride+wideStart N edges ports v copies r,rowWidth N v r,1⟩

/-- The public row directory contains exactly one record per physical incidence word. -/
noncomputable def ties (copies capFine stride : ℕ) : List Record :=
  Finset.univ.toList.map (tie N edges ports v copies capFine stride)

/-- The sparse public description is independent of the number of copies and widths. -/
@[simp] theorem ties_length (copies capFine stride : ℕ) :
    (ties N edges ports v copies capFine stride).length = Fintype.card (Row N v) := by
  simp [ties]

/-- The public equality reader fixes each staged word to its copy slice of the
current input, counting loop wires only once. -/
theorem ties_valid (copies capFine stride : ℕ) (boxes : List (List Factor)) (bank : ℕ → Bool) :
    (∀ r ∈ ties N edges ports v copies capFine stride, r.Valid boxes bank) ↔
    ∀ r : Row N v, ∀ i : Fin copies, ∀ k : Fin (rowWidth N v r),
      bank (i.val*stride+capFine+oneStart N edges ports v r+k.val) =
        bank (copies*stride+wideStart N edges ports v copies r+i.val*rowWidth N v r+k.val) := by
  simp only [ties,List.forall_mem_map,Finset.mem_toList,Finset.mem_univ,forall_true_left,
    tie,Record.Valid,equalValid,Port.atBit,Nat.mul_one]
  constructor
  · intro h r i k
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h r i.val i.isLt k.val k.isLt
  · intro h r i hi k hk
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h r ⟨i,hi⟩ ⟨k,hk⟩

/-- The exact repeated input lane from which the staged one-copy bit is read. -/
def repeatInput (copies : ℕ) (i : Fin copies) : InputLane N v → InputLane (wide N copies) v
  | .inl ⟨e,k⟩ => .inl ⟨e,finProdFinEquiv (i,k)⟩
  | .inr ⟨p,k⟩ => .inr ⟨p,finProdFinEquiv (i,k)⟩

/-- Every one-copy incidence lane, in the virtual-site ordering of the true
allocator, reads the slice for the same physical endpoint and copy. -/
theorem tie_reads (copies capFine stride : ℕ) (boxes : List (List Factor)) (bank : ℕ → Bool)
    (h : ∀ r ∈ ties N edges ports v copies capFine stride, r.Valid boxes bank)
    (i : Fin copies) (k : InputLane N v) :
    bank (i.val*stride+capFine+(sourceOrder N edges ports v k).val) =
      bank (copies*stride+
        (sourceOrder (wide N copies) edges ports v (repeatInput N v copies i k)).val) := by
  have pair {a b : ℕ} (i : Fin a) (j : Fin b) : (finProdFinEquiv (i,j)).val = i.val*b+j.val := by
    change j.val+b*i.val = _
    ac_rfl
  have ht := (ties_valid N edges ports v copies capFine stride boxes bank).mp h
  rcases k with ⟨e,k⟩ | ⟨p,k⟩
  · simpa only [repeatInput,wireOrdinal,oneStart,wideStart,rowWidth,Sum.elim_inl,
      pair,Nat.add_assoc,Nat.mul_comm] using ht (.inl e) i k
  · simpa only [repeatInput,portOrdinal,oneStart,wideStart,rowWidth,Sum.elim_inr,
      pair,Nat.add_assoc,Nat.mul_comm] using ht (.inr p) i k

omit [Fintype A] in
/-- Specializing to the grouped physical deck gives exactly the bottom network's
actual copy layout. -/
theorem wide_grouped {P : Type} (G : Network D P (fun _ => 1))
    (owner : A → G.Site) (copies : ℕ) :
    wide (G.packExternal width owner) copies = G.groupedRepeat width owner copies := rfl

end Packing.BottomRepeat

end BorderVNP
end Computability
end OAI
