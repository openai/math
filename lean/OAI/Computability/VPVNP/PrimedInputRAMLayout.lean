import OAI.Computability.VPVNP.RAMSharedFields
import OAI.Computability.VPVNP.RAMSerialization

/-!
# The rectangle of primed input positions

Sections 9.2 and 11 fix two consecutive groups with the same literal program
prefix. Every row of the rectangle consists of that prefix, the site address,
four header and cut bits, the incident ports, and zero padding. Only a middle
cut bit at the first group or an existing send port is a branch location.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM

open RAMLayout RAMSerialization

/-- Lengths of the pair's supplied header arrays. -/
structure Lengths where
  /-- Number of bits in the index of each of the two consecutive groups. -/
  index : ℕ
  /-- Number of advice bits supplied in the pair's common header. -/
  advice : ℕ
  /-- Number of supplied cut bits on the incoming side of the first group. -/
  leftCut : ℕ
  /-- Number of shared cut bits chosen between the first and second groups. -/
  middleCut : ℕ
  /-- Number of supplied cut bits on the outgoing side of the second group. -/
  rightCut : ℕ
  /-- Number of header words reserved for each of the left and right cut arrays. -/
  cutCapacity : ℕ
  leftFit : leftCut ≤ cutCapacity
  rightFit : rightCut ≤ cutCapacity

/-- Public fixed offsets of one-bit-per-word header fields. -/
inductive Header (L : Lengths)
  | group (g : Fin 2) (i : Fin L.index)
  | advice (i : Fin L.advice)
  | leftCut (i : Fin L.leftCut)
  | rightCut (i : Fin L.rightCut)
  deriving DecidableEq

/-- Size of the reserved header in words. Three cut lengths precede two group indices, the
advice and two outer cut arrays. -/
def Header.count (L : Lengths) := 3 + 2*L.index + L.advice + 2*L.cutCapacity

/-- Physical word address of a supplied header bit, using one word per bit and the reserved
stride between the outer cuts. -/
def Header.address {L : Lengths} (j : Header L) : Fin (Header.count L) :=
  match j with
  | .group g i => ⟨3 + g.val * L.index + i.val, by
      rcases (show g.val = 0 ∨ g.val = 1 by have := g.isLt; omega) with hg | hg <;>
        simp [hg, Header.count] <;> omega⟩
  | .advice i => ⟨3 + 2*L.index + i.val, by unfold Header.count; omega⟩
  | .leftCut i => ⟨3 + 2*L.index + L.advice + i.val, by have := L.leftFit; unfold Header.count; omega⟩
  | .rightCut i => ⟨3 + 2*L.index + L.advice + L.cutCapacity + i.val, by have := L.rightFit; unfold Header.count; omega⟩

/-- Index a complete internal assignment, allowing every value on all
directed transcript bits as well as on the middle cut. -/
abbrev Internal (L : Lengths) (r H w : ℕ) :=
  (Fin L.middleCut) ⊕ (Fin 2 × RAMLayout.SharedBit r H w)

/-- A site in the pair of primed groups, identified by its group and its `r`-bit site index. -/
abbrev Site (r : ℕ) := Fin 2 × Fin (2^r)

/-- The five parts of a row, in the paper's order. -/
abbrev Field (P r H w pad : ℕ) :=
  Fin P ⊕ Fin r ⊕ Fin 4 ⊕ RAMLayout.Slot r H w ⊕ Fin pad

/-- One bit position in the input rectangle, specified by a group, a site and a field within
that site's row. -/
abbrev Cell (P r H w pad : ℕ) := Site r × Field P r H w pad

/-- The position within a row has exactly the arithmetic offset obtained by
concatenating its fields. -/
def fieldIndex (P r H w pad : ℕ) :
    Field P r H w pad ≃ Fin (P+(r+(4+(width r H w+pad)))) :=
  let ports := ((offset r H w).sumCongr (Equiv.refl (Fin pad))).trans finSumFinEquiv
  let header := ((Equiv.refl (Fin 4)).sumCongr ports).trans finSumFinEquiv
  let address := ((Equiv.refl (Fin r)).sumCongr header).trans finSumFinEquiv
  ((Equiv.refl (Fin P)).sumCongr address).trans finSumFinEquiv

/-- Row-major flattening for the two groups, all their sites and all their
bit positions. -/
def cellIndex (P r H w pad : ℕ) : Cell P r H w pad ≃
    Fin ((2 * 2^r) * (P+(r+(4+(width r H w+pad))))) :=
  (finProdFinEquiv.prodCongr (fieldIndex P r H w pad)).trans finProdFinEquiv

variable {P r H w pad : ℕ} {L : Lengths}

/-- Prefix and address are private literals. The only external probes in a
row position are a prescribed header read or a read at a chosen endpoint. -/
inductive Ref (L : Lengths) (r H w : ℕ)
  | literal (value : Bool)
  | header (j : Header L)
  | shared (b : Internal L r H w)

/-- Resolve the four bits following the address. Beyond a supplied field's
length the bit is a literal zero. -/
def headerRef (L : Lengths) (g : Fin 2) (v : Fin (2^r)) (i : Fin 4) : Ref L r H w :=
  match i.val with
  | 0 => if h : v.val < L.index then .header (.group g ⟨v.val,h⟩) else .literal false
  | 1 => if h : v.val < L.advice then .header (.advice ⟨v.val,h⟩) else .literal false
  | 2 => if g = 0 then
      if h : v.val < L.leftCut then .header (.leftCut ⟨v.val,h⟩) else .literal false
    else if h : v.val < L.middleCut then .shared (.inl ⟨v.val,h⟩) else .literal false
  | _ => if g = 0 then
      if h : v.val < L.middleCut then .shared (.inl ⟨v.val,h⟩) else .literal false
    else if h : v.val < L.rightCut then .header (.rightCut ⟨v.val,h⟩) else .literal false

/-- Resolve a row bit to a literal, a supplied header bit or an internal shared bit. Padding
and missing ports resolve to zero. -/
def cellRef (L : Lengths) (prefixBits : Fin P → Bool) (c : Cell P r H w pad) : Ref L r H w :=
  match c.2 with
  | .inl p => .literal (prefixBits p)
  | .inr (.inl a) => .literal (RAMSerialization.wordBits r c.1.2 a)
  | .inr (.inr (.inl i)) => headerRef L c.1.1 c.1.2 i
  | .inr (.inr (.inr (.inl port))) =>
    match hs : source (c.1.2, port) with
    | none => .literal false
    | some u => .shared (.inr (c.1.1, ⟨u, source_shared hs⟩))
  | .inr (.inr (.inr (.inr _))) => .literal false

/-- Read the Boolean value of a row reference using the supplied header and the assignment to
internal bits. -/
def Ref.value (hdr : Header L → Bool) (bits : Internal L r H w → Bool) : Ref L r H w → Bool
  | .literal b => b
  | .header j => hdr j
  | .shared j => bits j

/-- Only the outgoing middle-cut slot of group zero and existing send slots
are visited as binary branches during the first pass. -/
def cellOwner (L : Lengths) (c : Cell P r H w pad) : Bool :=
  match c.2 with
  | .inr (.inr (.inl j)) => decide (j = 3 ∧ c.1.1 = 0 ∧ c.1.2.val < L.middleCut)
  | .inr (.inr (.inr (.inl port))) => decide (IsSend (c.1.2, port))
  | _ => false

private def owner (hmid : L.middleCut ≤ 2^r) (b : Internal L r H w) : Cell P r H w pad :=
  match b with
  | .inl v => ((0, ⟨v.val, v.isLt.trans_le hmid⟩), .inr (.inr (.inl 3)))
  | .inr (g, port) => ((g, port.val.1), .inr (.inr (.inr (.inl port.val.2))))

private theorem owner_designated (hmid : L.middleCut ≤ 2^r) (b : Internal L r H w) :
    cellOwner L (owner (P := P) (pad := pad) hmid b) = true := by
  rcases b with v | ⟨g, port⟩
  · simp [owner, cellOwner, v.isLt]
  · simpa [owner, cellOwner] using port.property

private def ownerBit (c : {c : Cell P r H w pad // cellOwner L c = true}) : Internal L r H w := by
  rcases c with ⟨⟨⟨g,v⟩, p | (a | (i | (port | padbit)))⟩, hc⟩
  · simp [cellOwner] at hc
  · simp [cellOwner] at hc
  · simp [cellOwner] at hc
    exact .inl ⟨v.val,hc.2.2⟩
  · exact .inr (g, ⟨(v,port), by simpa [cellOwner] using hc⟩)
  · simp [cellOwner] at hc

/-- A bijection, including multiplicities, from the bits in (9.4) to the
exact cells where the first-pass RAM makes a branch. -/
def ownerEquiv (P pad : ℕ) (hmid : L.middleCut ≤ 2^r) :
    Internal L r H w ≃ {c : Cell P r H w pad // cellOwner L c = true} where
  toFun b := ⟨owner hmid b, owner_designated hmid b⟩
  invFun := ownerBit
  left_inv b := by
    rcases b with v | ⟨g, port⟩
    · rfl
    · rfl
  right_inv c := by
    rcases c with ⟨⟨⟨g,v⟩, p | (a | (i | (port | padbit)))⟩, hc⟩
    · simp [cellOwner] at hc
    · simp [cellOwner] at hc
    · obtain ⟨rfl,rfl,hv⟩ : i = 3 ∧ g = 0 ∧ v.val < L.middleCut := by simpa [cellOwner] using hc
      rfl
    · rfl
    · simp [cellOwner] at hc

/-- Physical cell that stores one chosen bit, for second-pass random access. -/
def chosenAddress (P pad : ℕ) (hmid : L.middleCut ≤ 2^r) (b : Internal L r H w) :=
  cellIndex P r H w pad ((ownerEquiv P pad hmid b).val)

end PrimedInputRAM

end VPVNP
end Computability
end OAI
