import OAI.Computability.BorderVNP.CubePhysicalEnds
import OAI.Computability.BorderVNP.DiagonalCellEntries

/-! # Reading original local tensors after separating the packet ends

Private cables are still guessed once in their cells. For a cable crossing
cells, the source and destination now read their own packet-end bits.
Every unused slot is pinned at both ends. When all antipodal word pairs
agree this reads exactly the original tagged contraction, on its original
external bits and every private assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing Diagonal.CellEntries MvPolynomial
open scoped Classical

variable {n d blocks width D : ℕ} {P : Type*} {bits : P → ℕ}
variable {Cell : Type} [Fintype Cell] [DecidableEq Cell]
variable (N : Network D P bits) (cell : N.Site → Cell)

/-- Every individual bit of the original cross-cell cables. -/
abbrev LiveBit := (e : N.CrossingEdge cell) × Fin (N.width e.val)

/-- Read a cable word at one specified site. The two ends of a private
wire refer to the same private assignment. -/
noncomputable def siteWord (v : N.Site) (i : {e : N.Edge // N.src e = v ∨ N.dst e = v})
    (privateBits : ∀ c, N.InsideAssignment cell c)
    (publicBit : Bool → LiveBit N cell → Bool) (j : Fin (N.width i.val)) : Bool :=
  if hc : cell (N.src i.val) = cell (N.dst i.val) then
    privateBits _ ⟨i.val, rfl, hc.symm⟩ j
  else
    publicBit (decide (N.src i.val ≠ v)) ⟨⟨i.val, hc⟩, j⟩

omit [Fintype Cell] in
/-- At common public end bits, each site reads precisely the corresponding
wire in the inverse of the public/private assignment bijection. -/
theorem siteWord_common (v : N.Site) (i : {e : N.Edge // N.src e = v ∨ N.dst e = v})
    (privateBits : ∀ c, N.InsideAssignment cell c) (common : LiveBit N cell → Bool) :
    siteWord N cell v i privateBits (fun _ => common) =
      (N.cellAssignmentEquiv cell).symm ((fun e j => common ⟨e,j⟩), privateBits) i.val := by
  funext j
  by_cases h : cell (N.src i.val) = cell (N.dst i.val)
  · simp [siteWord, Network.cellAssignmentEquiv, h]
  · simp [siteWord, Network.cellAssignmentEquiv, h]

variable {Param Gadget : Type*}

/-- The local entries read in one cell, with independently supplied exterior
ends. This retains every occurrence of a tagged unary or gadget position. -/
noncomputable def cellTag (tags : N.Tables (Entry Param Gadget)) (x : Ports bits)
    (privateBits : ∀ c, N.InsideAssignment cell c) (pub : Bool → LiveBit N cell → Bool)
    (c : Cell) : Entry Param Gadget :=
  ∏ v : {v : N.Site // cell v = c}, tags v.val (fun i => siteWord N cell v.val i privateBits pub)
    (fun p => x p.val)

/-- The product of local tags becomes the unexpanded tagged path when
public wires have one common bit at their two ends. -/
theorem prod_cellTag_common (tags : N.Tables (Entry Param Gadget)) (x : Ports bits)
    (privateBits : ∀ c, N.InsideAssignment cell c) (common : LiveBit N cell → Bool) :
    (∏ c, cellTag N cell tags x privateBits (fun _ => common) c) =
      assignmentEntry N tags
        ((N.cellAssignmentEquiv cell).symm ((fun e j => common ⟨e,j⟩), privateBits)) x := by
  change (∏ c, ∏ v : {v : N.Site // cell v = c}, _) = _
  simp_rw [siteWord_common]
  exact Fintype.prod_fiberwise cell (N.read tags ((N.cellAssignmentEquiv cell).symm
    ((fun e j => common ⟨e,j⟩), privateBits)) x)

/-- Tag the original sites and enforce the two physical zero pins on every
padded position missing from the crossing-edge directory. -/
noncomputable def host (slot : LiveBit N cell ↪ Slot n d blocks width)
    (tags : N.Tables (Entry Param Gadget)) (x : Ports bits)
    (privateBits : ∀ c, N.InsideAssignment cell c)
    (single : SingleSlot n d blocks width → Bool)
    (ends : Packet n d blocks → Vertex n × Bool → Fin width → Bool) : Entry Param Gadget :=
  if ∀ i ∉ Set.range slot, readEnd single ends false i = false ∧ readEnd single ends true i = false then
    ∏ c, cellTag N cell tags x privateBits (fun dir i => readEnd single ends dir (slot i)) c
  else 0

/-- Replacing separated cube ends by common words recovers the pinned
host value exactly, even when a selected scalar table entry evaluates to zero. -/
theorem host_common (slot : LiveBit N cell ↪ Slot n d blocks width)
    (tags : N.Tables (Entry Param Gadget)) (x : Ports bits)
    (privateBits : ∀ c, N.InsideAssignment cell c)
    (single : SingleSlot n d blocks width → Bool) (pairs : Packet n d blocks → Vertex n → Fin width → Bool) :
    let a := (commonEquiv n d blocks width).symm (single, pairs)
    host N cell slot tags x privateBits single (fun p e => pairs p e.1) =
      if ∀ i ∉ Set.range slot, a i = false then
        assignmentEntry N tags
          ((N.cellAssignmentEquiv cell).symm ((fun e j => a (slot ⟨e,j⟩)), privateBits)) x
      else 0 := by
  dsimp only
  simp only [host, readEnd_common, and_self, prod_cellTag_common]

end Cube.Physical

end BorderVNP
end Computability
end OAI
