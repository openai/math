import OAI.Computability.BorderVNP.CubeBudget

/-! # Physical packet-end slots on the padded ordered label pairs

Each scalar wire bit has a slot in an ordered pair of labels and an offset
in that pair. A pair differing in every coordinate is assigned to its
subcube, orientation, and block. The remaining pairs keep singleton wires.
At a cube end the first Boolean tag refers to its source and the second
to its destination; singleton ends refer to the same independent bit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open scoped Classical

/-- An ordinal among the padded wires of a public ordered label pair. -/
abbrev Slot (n d blocks width : ℕ) :=
  (Label (n+1) d × Label (n+1) d) × Fin (blocks * width)

/-- Wires whose ordered labels share a symbol stay as singletons. -/
abbrev SingleSlot (n d blocks width : ℕ) :=
  {p : Label (n+1) d × Label (n+1) d // ¬∀ i, p.1 i ≠ p.2 i} × Fin (blocks * width)

private def cornerEquiv (n : ℕ) : (Fin n → Bool) ≃ Vertex n :=
  Equiv.piCongrRight fun _ => finTwoEquiv.symm

/-- Split a bit slot into its unique full packet incidence or singleton bit,
retaining the public pair order and contiguous within-pair block numbers. -/
def splitSlot (n d blocks width : ℕ) :
    Slot n d blocks width ≃
      (Packet n d blocks × (Vertex n × Fin width)) ⊕ SingleSlot n d blocks width := by
  let differ (p : Label (n+1) d × Label (n+1) d) := ∀ i, p.1 i ≠ p.2 i
  let pieces := ((Equiv.sumCompl differ).symm.prodCongr (Equiv.refl (Fin (blocks * width)))).trans
    (Equiv.sumProdDistrib _ _ _)
  let packet := ((Equiv.refl (FullPair (n+1) d)).prodCongr finProdFinEquiv.symm).trans
    ((packetEquiv n d blocks width).trans ((Equiv.refl _).prodCongr
      ((cornerEquiv n).prodCongr (Equiv.refl _))))
  exact pieces.trans (Equiv.sumCongr packet (Equiv.refl _))

/-- Read one original end from the local bits of a cube or its retained singleton. -/
def readEnd {n d blocks width : ℕ} (single : SingleSlot n d blocks width → Bool)
    (ends : Packet n d blocks → Vertex n × Bool → Fin width → Bool)
    (dst : Bool) (slot : Slot n d blocks width) : Bool :=
  match splitSlot n d blocks width slot with
  | .inl (p, i, j) => ends p (i, dst) j
  | .inr s => single s

/-- Before expanding any packets, their two end words agree. This is a
bijection between all shared bit assignments on padded slots and the
singleton bits together with one word per antipodal pair in every packet. -/
def commonEquiv (n d blocks width : ℕ) :
    (Slot n d blocks width → Bool) ≃
      (SingleSlot n d blocks width → Bool) ×
        (Packet n d blocks → Vertex n → Fin width → Bool) :=
  ((splitSlot n d blocks width).arrowCongr (Equiv.refl _)).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).trans ((Equiv.prodComm _ _).trans
      ((Equiv.refl _).prodCongr ((Equiv.curry _ _ _).trans
        (Equiv.piCongrRight fun _ => Equiv.curry _ _ _)))))

/-- With shared antipodal bits, reading either end is inverse to the slot
reindexing, including pairs with no live wires and empty block families. -/
theorem readEnd_common {n d blocks width : ℕ} (single : SingleSlot n d blocks width → Bool)
    (pairs : Packet n d blocks → Vertex n → Fin width → Bool) (dst : Bool)
    (slot : Slot n d blocks width) :
    readEnd single (fun p e => pairs p e.1) dst slot =
      (commonEquiv n d blocks width).symm (single, pairs) slot := by
  change _ = Sum.elim (fun s => pairs s.1 s.2.1 s.2.2) single (splitSlot n d blocks width slot)
  unfold readEnd
  cases splitSlot n d blocks width slot <;> rfl

end Cube.Physical

end BorderVNP
end Computability
end OAI
