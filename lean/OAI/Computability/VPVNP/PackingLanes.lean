import OAI.Computability.VPVNP.BitSlotIndex
import OAI.Computability.VPVNP.SlotOtherEnd
import OAI.Computability.VPVNP.SlotSeparation
import Mathlib.Data.Nat.Log
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Choosing and consuming binary lane coordinates

Appendix C uses one bit per base color, enough bits to index an outgoing
slot, and a tag large enough for the greedy exclusions. All three block
lengths depend only on the degree. The remaining coordinates are arbitrary.
The input may have any displacement on any directed base arc.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression

/-- Split a binary vector into two coordinate blocks. Addition splits in the
same way, so both blocks retain constant displacements on each base arc. -/
def splitBitWord (a b : ℕ) : BitWord (a + b) ≃+ BitWord a × BitWord b where
  toEquiv := (finSumFinEquiv.symm.arrowCongr (Equiv.refl (ZMod 2))).trans
    (Equiv.sumArrowEquivProdArrow _ _ _)
  map_add' _ _ := rfl

/-- Logarithmic tag length sufficient to avoid all forbidden choices. -/
def packingTagBits (d : ℕ) : ℕ := Nat.log 2 (2 * d * ((d + 1) + (d + 1) ^ 2)) + 1

theorem packingTagBits_sufficient (d : ℕ) :
    2 * d * ((d + 1) + (d + 1) ^ 2) < 2 ^ packingTagBits d :=
  Nat.lt_pow_succ_log_self (by decide) _

/-- For degree `2^a` and `g` unused coordinates, this is the whole original
lane length. Only the color and slot fields reduce the position count. -/
abbrev packingLaneBits (a g : ℕ) :=
  (2 * 2 ^ a + 1) + (a + (packingTagBits (2 ^ a) + g))

/-- Separate the color, slot, tag, and remaining-lane fields. -/
def packingFields (a g : ℕ) : BitWord (packingLaneBits a g) ≃+
    BitWord (2 * 2 ^ a + 1) × (BitWord a × (BitWord (packingTagBits (2 ^ a)) × BitWord g)) :=
  (splitBitWord _ _).trans ((AddEquiv.refl _).prodCongr
    ((splitBitWord _ _).trans ((AddEquiv.refl _).prodCongr (splitBitWord _ _))))

/-- Packing data for bit-word slots, tag shifts and residual lanes, with dyadic degree and the
corresponding finite color bound. -/
abbrev DyadicPackingData (V : Type*) (a g : ℕ) :=
  PackingData V (BitWord a) (BitWord (packingTagBits (2 ^ a))) (BitWord g)
    (2 ^ a) (2 * 2 ^ a + 1)

variable {V : Type*} {a g : ℕ}

/-- Reorder the actual arc coordinates after splitting its lane. -/
def packingArcEquiv (V : Type*) (a g : ℕ) :
    (V × Fin (2 ^ a)) × BitWord (packingLaneBits a g) ≃
    Arc V (BitWord a) (BitWord (packingTagBits (2 ^ a))) (BitWord g) (2 ^ a) (2 * 2 ^ a + 1) where
  toFun p :=
    let f := packingFields a g p.2
    (((p.1.1,f.2.2),p.1.2),f.1,f.2.1)
  invFun p := ((p.1.1.1,p.1.2),(packingFields a g).symm (p.2.1,p.2.2,p.1.1.2))
  left_inv := by rintro ⟨⟨x,i⟩, w⟩; simp
  right_inv := by rintro ⟨⟨⟨x,t,h⟩,i⟩,u,k⟩; simp

section Ordered

variable (G : LiftedSlots V (2 ^ a) (BitWord (packingLaneBits a g)))

/-- Construct the packing data by scanning the supplied base order. Candidate
tags are enumerated by their binary integers, independently of the unused lanes. -/
def orderedDyadicPacking {N : ℕ} (order : V ≃ Fin N) : DyadicPackingData V a g where
  slots := G.base
  color := G.base.orderedColor order
  proper := G.base.orderedColor_proper order
  slotLabel := bitWordFinEquiv a
  offset := G.base.orderedTagOffsets order (bitWordFinEquiv (packingTagBits (2 ^ a)))
    (fun p ↦ (packingFields a g (G.displacement p)).2.2.1) (packingTagBits_sufficient (2 ^ a))
  bitShift p := (packingFields a g (G.displacement p)).1
  slotShift p := (packingFields a g (G.displacement p)).2.1
  siteShift p := (packingFields a g (G.displacement p)).2.2

theorem orderedDyadicPacking_validTags {N : ℕ} (order : V ≃ Fin N) :
    G.base.ValidTagOffsets (orderedDyadicPacking G order).tagShift
      (orderedDyadicPacking G order).offset :=
  G.base.orderedTagOffsets_valid order (bitWordFinEquiv (packingTagBits (2 ^ a)))
    (fun p ↦ (packingFields a g (G.displacement p)).2.2.1) (packingTagBits_sufficient (2 ^ a))

/-- The relabeling respects the directed endpoints, slot numbers, and all
translated fields of the actual input for every choice of base order. -/
theorem orderedDyadicPacking_actual {N : ℕ} (order : V ≃ Fin N)
    (p : (V × Fin (2 ^ a)) × BitWord (packingLaneBits a g)) :
    (orderedDyadicPacking G order).actual (packingArcEquiv V a g p) =
      packingArcEquiv V a g (G.actualTarget p) := by
  rcases p with ⟨e,w⟩
  simp only [LiftedSlots.actualTarget_apply, packingArcEquiv, Equiv.coe_fn_mk, map_add]
  rfl

end Ordered

variable [Finite V] (G : LiftedSlots V (2 ^ a) (BitWord (packingLaneBits a g)))

/-- Apply the ordered construction using a chosen enumeration of a finite base. -/
noncomputable def dyadicPacking : DyadicPackingData V a g := by
  letI := Fintype.ofFinite V
  exact orderedDyadicPacking G (Fintype.equivFin V)

theorem dyadicPacking_validTags : G.base.ValidTagOffsets (dyadicPacking G).tagShift
    (dyadicPacking G).offset := by
  unfold dyadicPacking
  exact orderedDyadicPacking_validTags G _

theorem dyadicPacking_actual (p : (V × Fin (2 ^ a)) × BitWord (packingLaneBits a g)) :
    (dyadicPacking G).actual (packingArcEquiv V a g p) =
      packingArcEquiv V a g (G.actualTarget p) := by
  unfold dyadicPacking
  exact orderedDyadicPacking_actual G _ p

/-- Position count before packing is `K` times the new count. The tag moves
into the base, while the color and slot fields are removed. -/
theorem packing_position_count (V : Type*) [Fintype V] (a g : ℕ) :
    Fintype.card (V × BitWord (packingLaneBits a g)) =
      (2 ^ (2 * 2 ^ a + 1) * 2 ^ a) * Fintype.card (Site V (BitWord (packingTagBits (2 ^ a)))
        (BitWord g)) := by
  simp only [packingLaneBits, Site, BitWord, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    ZMod.card, pow_add]
  ring

end Compression

end VPVNP
end Computability
end OAI
