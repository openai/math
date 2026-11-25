import OAI.Computability.BorderVNP.CubePhysicalPaddingBalance
import OAI.Computability.BorderVNP.CubePhysicalHost
import OAI.Computability.BorderVNP.CubePhysicalPaddingZeros

/-! # Embedding a profile's actual crossing cables into the padded packet layout

For a fixed pack at the end of an epoch path the local grid absorbs all
within-cell edges. The remaining oriented cables are taken in their public
order. The balancing inequality supplies enough slots in every pair of product
labels, and their occupied intervals recover exactly the public bit assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing
open scoped Classical

variable {D m n d : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type}
variable (N : Network D P bits) (cell : N.Site → Cell)

/-- Source cell of a surviving, oriented crossing cable. -/
abbrev crossSrc (e : N.CrossingEdge cell) : Cell := cell (N.src e.val)

/-- Destination cell of a surviving, oriented crossing cable. -/
abbrev crossDst (e : N.CrossingEdge cell) : Cell := cell (N.dst e.val)

/-- Public bit width of the surviving cable. -/
abbrev crossWidth (e : N.CrossingEdge cell) : ℕ := N.width e.val

/-- Number the crossing cables without changing any within-cable bit ordinal. -/
def numberedBits (ord : N.CrossingEdge cell ≃ Fin m) :
    LiveBit N cell ≃ ((i : Fin m) × Fin (crossWidth N cell (ord.symm i))) :=
  Equiv.sigmaCongr ord fun e => finCongr (by rw [ord.symm_apply_apply])

/-- Embed each actual crossing bit in its interval. The interval's bin is the
ordered pair of the two cells' public product labels. -/
def packedSlotEmbedding (ord : N.CrossingEdge cell ≃ Fin m)
    (label : Cell → Label (n+1) d) (blocks bc : ℕ)
    (cap : ∀ u, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
      (crossWidth N cell ∘ ord.symm) u ≤ blocks*bc) :
    LiveBit N cell ↪ Slot n d blocks bc :=
  (numberedBits N cell ord).toEmbedding.trans (slotEmbedding _ _ blocks bc cap)

/-- The endpoint labels and exact interval offset of every real bit on the
chosen profile path. Distinct bits remain distinct even if their labels agree. -/
theorem packedSlot_address (ord : N.CrossingEdge cell ≃ Fin m)
    (label : Cell → Label (n+1) d) (blocks bc : ℕ) (cap)
    (e : N.CrossingEdge cell) (j : Fin (N.width e.val)) :
    let u := cablePair ord (crossSrc N cell) (crossDst N cell) label
    let s := packedSlotEmbedding N cell ord label blocks bc cap ⟨e,j⟩
    s.1 = (label (crossSrc N cell e),label (crossDst N cell e)) ∧
      s.2.val = intervalStart u (crossWidth N cell ∘ ord.symm) (ord e) + j.val := by
  let u := cablePair ord (crossSrc N cell) (crossDst N cell) label
  let y := numberedBits N cell ord ⟨e,j⟩
  have he := slotEmbedding_address u (crossWidth N cell ∘ ord.symm) blocks bc cap y.1 y.2
  have hf : u y.1 = (label (crossSrc N cell e),label (crossDst N cell e)) := by
    change (label (crossSrc N cell (ord.symm (ord e))),label (crossDst N cell (ord.symm (ord e)))) = _
    rw [ord.symm_apply_apply]
  exact ⟨he.1.trans hf, he.2⟩

/-- The unused physical slots of each label pair are precisely the tail
beginning at its total live width. -/
theorem mem_range_packedSlot_iff (ord : N.CrossingEdge cell ≃ Fin m)
    (label : Cell → Label (n+1) d) (blocks bc : ℕ) (cap)
    (u : Label (n+1) d × Label (n+1) d) (j : Fin (blocks*bc)) :
    (u,j) ∈ Set.range (packedSlotEmbedding N cell ord label blocks bc cap) ↔
      j.val < load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
        (crossWidth N cell ∘ ord.symm) u := by
  let E := numberedBits N cell ord
  let s := slotEmbedding _ _ blocks bc cap
  have h : Set.range (s ∘ E) = Set.range s := E.surjective.range_comp s
  change (u,j) ∈ Set.range (s ∘ E) ↔ _
  rw [h]
  exact mem_range_slotEmbedding_iff ..

variable [Fintype Cell] [DecidableEq Cell]

/-- The capacity follows from the actual bit-load inequalities at the chosen
cells, and uses the same block-rounded width as the paper. -/
noncomputable def balancedPackedEmbedding (ord : N.CrossingEdge cell ≃ Fin m)
    (label : Cell → Label (n+1) d) {W : ℝ} (hW : 0 ≤ W) {bc Z : ℕ} (hb : 0 < bc) (hZ : 0 < Z)
    (balanced : ∀ u v, Balancing.load (Balancing.cable
      (fun b : LiveBit N cell => crossSrc N cell b.1) (fun b : LiveBit N cell => crossDst N cell b.1)
      u v) label ≤ 4*W/(Z : ℝ)^2) :
    LiveBit N cell ↪ Slot n d (blocksFor W bc Z) bc :=
  packedSlotEmbedding N cell ord label _ _ (load_le_blocks ord (crossSrc N cell) (crossDst N cell)
    (crossWidth N cell) label (fun e => e.property) hW hb hZ balanced)

omit [Fintype Cell] [DecidableEq Cell] in
/-- A physical packet assignment reconstructs a single bit on each crossing
wire. Conversely, each crossing assignment has exactly one padded completion
satisfying the pins. -/
theorem existsUnique_padded {blocks bc : ℕ} (e : LiveBit N cell ↪ Slot n d blocks bc)
    (w : N.CrossingAssignment cell) :
    ∃! a : Slot n d blocks bc → Bool, (∀ s ∉ Set.range e, a s = false) ∧ ∀ b, a (e b) = w b.1 b.2 := by
  let v (b : LiveBit N cell) := w b.1 b.2
  refine ⟨zeroExtend e v, ⟨fun s hs => zeroExtend_unused e v hs, fun b => zeroExtend_image e v b⟩, ?_⟩
  intro a ha
  have h : a ∘ e = v := funext ha.2
  simpa only [← h] using (zeroExtend_of_pinned e a ha.1).symm

end Cube.Physical

end BorderVNP
end Computability
end OAI
