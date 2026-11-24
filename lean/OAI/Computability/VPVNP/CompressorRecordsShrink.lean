import OAI.Computability.VPVNP.CompressorRecordRefreshOldWidths
import OAI.Computability.VPVNP.BitSlotXor
import OAI.Computability.VPVNP.CompressorRecordPlacement
import OAI.Computability.VPVNP.ShrinkStateInput

/-!
# Numeric addresses in the shrinking placement pass

An old position is scanned in base, color-mask, slot-label, tag, residual-lane order.
The four directory reads are the base color, base offset, base slot mate, and its
displacement. The low tag and lane fields are kept together when the offset and the
base displacement are applied. This computes both possible layout owners even when
the two endpoints are thin.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Shrink

open Compression

/-- Concatenate a most-significant field and a low binary field. -/
def join (g x y : ℕ) := x * 2 ^ g + y

private theorem join_div (g x : ℕ) {y : ℕ} (hy : y < 2 ^ g) : join g x y / 2 ^ g = x := by
  rw [join, Nat.mul_comm x, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hy, Nat.add_zero]

private theorem join_mod (g x : ℕ) {y : ℕ} (hy : y < 2 ^ g) : join g x y % 2 ^ g = y :=
  Nat.mul_add_mod_of_lt hy

private theorem join_lt {g j x y : ℕ} (hx : x < 2^j) (hy : y < 2^g) :
    join g x y < 2 ^ (j+g) := by
  rw [join, pow_add]
  calc
    x * 2^g + y < x * 2^g + 2^g := by omega
    _ = (x+1)*2^g := by ring
    _ ≤ 2^j*2^g := Nat.mul_le_mul_right _ hx

theorem join_xor (g x t : ℕ) {y l : ℕ} (hy : y < 2^g) (hl : l < 2^g) :
    join g x y ^^^ join g t l = join g (x ^^^ t) (y ^^^ l) := by
  rw [← Nat.mod_add_div (join g x y ^^^ join g t l) (2^g)]
  rw [Nat.xor_mod_two_pow, Nat.xor_div_two_pow, join_mod g x hy, join_mod g t hl,
    join_div g x hy, join_div g t hl, join]
  ac_rfl

/-- The color bit selected by the indexed greedy coloring, in big-endian lane order. -/
theorem bitWord_test {c : ℕ} (u : BitWord c) (j : Fin c) :
    (bitWordFinEquiv c u).val.testBit (c-1-j.val) = decide (u j = 1) := by
  induction c with
  | zero => exact j.elim0
  | succ n ih =>
    rw [bitWordFinEquiv_val, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (bitWordFinEquiv n (Fin.tail u)).isLt]
    induction j using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.sub_zero, Nat.add_sub_cancel, lt_self_iff_false, ite_false, Nat.sub_self]
      generalize u 0 = b
      decide +revert
    | succ j =>
      have h : n - (j.val+1) < n := by have := j.isLt; omega
      rw [Fin.val_succ, Nat.add_sub_cancel, ite_eq_left h, show n-(j.val+1)=n-1-j.val by omega, ih]
      rfl

/-- The four natural-number fields obtained by decoding an old site for the shrinking placement
scan. -/
structure Fields where
  /-- The index of the old base vertex whose greedy color and offset are consulted. -/
  base : ℕ
  /-- The old site's color mask, tested at its base vertex's assigned color to determine
  thickness. -/
  mask : ℕ
  /-- The old site's slot label, used to look up the mate and displacement at its base port. -/
  slot : ℕ
  /-- The combined tag and residual-lane bits, kept together when applying the greedy offset
  and the arc displacement. -/
  low : ℕ

/-- The concatenated tag and residual lane occupy the least significant bits. -/
def decode (a c lowBits i : ℕ) : Fields :=
  let v := i / 2^lowBits
  let b := v / 2^a
  ⟨b / 2^c, b % 2^c, v % 2^a, i % 2^lowBits⟩

theorem decode_join (a c l b u h low : ℕ) (hu : u < 2^c) (hh : h < 2^a) (hl : low < 2^l) :
    decode a c l (join l (join a (join c b u) h) low) = ⟨b,u,h,low⟩ := by
  simp [decode, join_div _ _ hu, join_div _ _ hh, join_div _ _ hl,
    join_mod _ _ hu, join_mod _ _ hh, join_mod _ _ hl]

/-- The packed site, bundle endpoints, assigned port, thickness, and layout-dependent owner
calculated for one old position. -/
structure Row (α : Type) where
  /-- The packed index obtained by retaining the old position's base, tag, and residual lane. -/
  packed : α
  /-- The bundle's source site A, obtained by applying the base vertex's greedy offset to the
  low lane bits. -/
  source : α
  /-- The bundle's target site B, obtained from the base mate and the displaced source lane. -/
  target : α
  /-- The bundle's outgoing port, combining its source-site index with the old slot label. -/
  assigned : α
  /-- Whether the bit at the old base vertex's greedy color is set in this position's mask. -/
  thick : Bool
  /-- The packed owner of the old position, using the packed site for a thick position and the
  chosen bundle endpoint for a thin one. -/
  owner : α
  deriving DecidableEq

/-- Four source columns and a layout bit determine the records for this position. -/
def row (a c j g : ℕ) (layout : Bool) (color offset mate displacement : ℕ → ℕ)
    (i : ℕ) : Row ℕ :=
  let f := decode a c (j+g) i
  let e := f.base * 2^a + f.slot
  let thick := f.mask.testBit (c-1-color f.base)
  let laneA := f.low ^^^ (offset f.base * 2^g)
  let A := join (j+g) f.base laneA
  let B := join (j+g) (mate e / 2^a) (laneA ^^^ (displacement e % 2^(j+g)))
  let packed := join (j+g) f.base f.low
  ⟨packed,A,B,A*2^a + f.slot,thick,if thick then packed else if layout then B else A⟩

variable {V : Type} {n a g : ℕ}
/-- Number of packing-tag bits for a graph whose degree is two to the given exponent. -/
abbrev J (a : ℕ) := packingTagBits (2^a)
/-- The number of greedy colors for the old graph, twice its degree plus one. -/
abbrev colors (a : ℕ) := 2 * 2^a + 1
/-- A site after shrinking, consisting of a base vertex, packing tag, and residual lane. -/
abbrev Packed (V : Type) (a g : ℕ) := Site V (BitWord (J a)) (BitWord g)
/-- A position before shrinking, with its base site, tag, residual lane, color mask, and slot
label. -/
abbrev Old (V : Type) (a g : ℕ) := Position V (BitWord a) (BitWord (J a)) (BitWord g) (colors a)

/-- Concatenate the binary packing tag above the residual-lane bits to form the low part of a
site number. -/
def lowNumber (v : BitWord (J a) × BitWord g) : ℕ :=
  join g (bitWordFinEquiv (J a) v.1).val (bitWordFinEquiv g v.2).val

/-- Number a packed site by concatenating the ordered base vertex with the tag-and-lane number. -/
def packedNumber (order : V ≃ Fin n) (v : Packed V a g) : ℕ :=
  join (J a + g) (order v.1).val (lowNumber v.2)

/-- Number an old position in base, mask, slot-label, tag, and residual-lane order. -/
def oldNumber (order : V ≃ Fin n) (x : Old V a g) : ℕ :=
  join (J a + g) (join a (join (colors a) (order x.1.1).val
    (bitWordFinEquiv (colors a) x.2.1).val) (bitWordFinEquiv a x.2.2).val) (lowNumber x.1.2)

theorem decode_oldNumber (order : V ≃ Fin n) (x : Old V a g) :
    decode a (colors a) (J a+g) (oldNumber order x) =
      ⟨(order x.1.1).val, (bitWordFinEquiv (colors a) x.2.1).val,
       (bitWordFinEquiv a x.2.2).val, lowNumber x.1.2⟩ :=
  decode_join _ _ _ _ _ _ _ (Fin.isLt _) (Fin.isLt _) (join_lt (Fin.isLt _) (Fin.isLt _))

private theorem lowNumber_add (u v : BitWord (J a) × BitWord g) :
    lowNumber (u+v) = lowNumber u ^^^ lowNumber v := by
  unfold lowNumber
  rw [join_xor _ _ _ (Fin.isLt _) (Fin.isLt _)]
  simp only [Prod.fst_add, Prod.snd_add, bitWordFinEquiv_add_val]

private theorem lowNumber_offset (u : BitWord (J a) × BitWord g) (s : BitWord (J a)) :
    lowNumber (u.1+s,u.2) = lowNumber u ^^^ ((bitWordFinEquiv (J a) s).val * 2^g) := by
  have hz : (bitWordFinEquiv g (0 : BitWord g)).val = 0 := by
    simpa using bitWordFinEquiv_add_val (0 : BitWord g) 0
  have h := lowNumber_add u (s,0)
  simpa [lowNumber, join, hz] using h

/-- Directory invariant at the start of a placement scan. Base slots retain both their
outgoing and incoming numbers; displacement is stored in the full old lane order. -/
structure Directory (G : LiftedSlots V (2^a) (BitWord (packingLaneBits a g)))
    (order : V ≃ Fin n) (color offset mate displacement : ℕ → ℕ) : Prop where
  color_at : ∀ v, color (order v).val = ((orderedDyadicPacking G order).color v).val
  offset_at : ∀ v, offset (order v).val =
    (bitWordFinEquiv (J a) ((orderedDyadicPacking G order).offset v)).val
  mate_at : ∀ v h, mate (join a (order v).val h.val) =
    join a (order (G.base.target (v,h)).1).val (G.base.target (v,h)).2.val
  shift_at : ∀ v h, displacement (join a (order v).val h.val) =
    (bitWordFinEquiv (packingLaneBits a g) (G.displacement (v,h))).val

theorem packingFields_number (x : BitWord (packingLaneBits a g)) :
    (bitWordFinEquiv _ x).val = join (J a+g)
      (join a (bitWordFinEquiv (colors a) (packingFields a g x).1).val
        (bitWordFinEquiv a (packingFields a g x).2.1).val) (lowNumber (packingFields a g x).2.2) := by
  let y := (splitBitWord (colors a) (a+(J a+g)) x).2
  let z := (splitBitWord a (J a+g) y).2
  rw [splitBitWord_number (colors a) (a+(J a+g)) x,
    show (splitBitWord (colors a) (a+(J a+g)) x).2 = y from rfl, splitBitWord_number a (J a+g) y,
    show (splitBitWord a (J a+g) y).2 = z from rfl, splitBitWord_number (J a) g z]
  change _ = ((bitWordFinEquiv (colors a) ((splitBitWord _ _ x).1)).val * 2^a +
    (bitWordFinEquiv a ((splitBitWord _ _ y).1)).val) * 2^(J a+g) +
    ((bitWordFinEquiv (J a) ((splitBitWord _ _ z).1)).val * 2^g +
      (bitWordFinEquiv g ((splitBitWord _ _ z).2)).val)
  rw [pow_add 2 a]
  ring

/-- The full old site scan follows the order of the original compression state. -/
theorem oldNumber_original (order : V ≃ Fin n) (x : Old V a g) :
    oldNumber order x = (order x.1.1).val * 2^(packingLaneBits a g) +
      (bitWordFinEquiv _ ((packingInputSites V a g x).2)).val := by
  let l := (packingFields a g).symm (x.2.1,x.2.2,x.1.2)
  change _ = _ + (bitWordFinEquiv _ l).val
  rw [packingFields_number, show packingFields a g l = (x.2.1,x.2.2,x.1.2) from
    (packingFields a g).apply_symm_apply _]
  simp only [oldNumber, join, packingLaneBits, pow_add]
  ring

/-- Correctness for every old site, including the color and tie conventions of Appendix C. -/
theorem row_exact (G : LiftedSlots V (2^a) (BitWord (packingLaneBits a g)))
    (order : V ≃ Fin n) {color offset mate displacement : ℕ → ℕ}
    (d : Directory G order color offset mate displacement) (layout : Bool) (x : Old V a g) :
    let P := orderedDyadicPacking G order
    let e := P.assignedBundle x
    row a (colors a) (J a) g layout color offset mate displacement (oldNumber order x) =
      ⟨packedNumber order x.1, packedNumber order e.1, packedNumber order (P.siteGraph.target e).1,
       join a (packedNumber order e.1) e.2.val, decide (P.thick x), packedNumber order (P.placement layout x)⟩ := by
  let P := orderedDyadicPacking G order
  let h := bitWordFinEquiv a x.2.2
  let v := x.1.1
  let e := P.assignedBundle x
  have htag : lowNumber e.1.2 = lowNumber x.1.2 ^^^ (offset (order v).val * 2^g) := by
    rw [d.offset_at]
    exact lowNumber_offset x.1.2 (P.offset v)
  have hs := packingFields_number (G.displacement (v,h))
  have hsmod : displacement (join a (order v).val h.val) % 2^(J a+g) =
      lowNumber (P.siteShift (v,h)) := by
    have hlow : lowNumber ((packingFields a g) (G.displacement (v,h))).2.2 < 2^(J a+g) :=
      join_lt (Fin.isLt _) (Fin.isLt _)
    rw [d.shift_at, hs, join_mod _ _ hlow]
    rfl
  have hb : mate (join a (order v).val h.val) / 2^a = (order (G.base.target (v,h)).1).val := by
    rw [d.mate_at, join_div _ _ (Fin.isLt _)]
  have ht : (bitWordFinEquiv (colors a) x.2.1).val.testBit (colors a-1-color (order v).val) =
      decide (P.thick x) := by rw [d.color_at]; exact bitWord_test _ _
  have hA : packedNumber order e.1 = join (J a+g) (order v).val
      (lowNumber x.1.2 ^^^ (offset (order v).val * 2^g)) := by rw [← htag]; rfl
  have hB : packedNumber order (P.siteGraph.target e).1 =
      join (J a+g) (order (G.base.target (v,h)).1).val (lowNumber e.1.2 ^^^ lowNumber (P.siteShift (v,h))) := by
    rw [← lowNumber_add]
    rfl
  let sa := join (J a+g) (order v).val (lowNumber x.1.2 ^^^ (offset (order v).val * 2^g))
  let sb := join (J a+g) (mate (join a (order v).val h.val) / 2^a)
    ((lowNumber x.1.2 ^^^ (offset (order v).val * 2^g)) ^^^
      (displacement (join a (order v).val h.val) % 2^(J a+g)))
  have eqB : sb = packedNumber order (P.siteGraph.target e).1 := by
    dsimp only [sb]; rw [hb, hsmod, ← htag, ← hB]
  unfold row
  rw [decode_oldNumber]
  change Row.mk (packedNumber order x.1) sa sb (join a sa h.val) _
      (if _ then packedNumber order x.1 else if layout then sb else sa) =
    Row.mk _ (packedNumber order e.1) (packedNumber order (P.siteGraph.target e).1)
      (join a (packedNumber order e.1) h.val) (decide (P.thick x)) (packedNumber order (P.placement layout x))
  rw [ht, eqB, show sa = packedNumber order e.1 from hA.symm]
  by_cases hx : P.thick x <;> cases layout <;> simp [PackingData.placement, hx, e]


/-- Old sites are scanned in the original state numbering. -/
def oldIndex (order : V ≃ Fin n) : Old V a g ≃ Fin (n * 2^(packingLaneBits a g)) :=
  (packingInputSites V a g).trans ((order.prodCongr (bitWordFinEquiv _)).trans finProdFinEquiv)

/-- The packed vertex combines the promoted tag and remaining lane. -/
def packedIndex (order : V ≃ Fin n) : Packed V a g ≃ Fin (n * (2^(J a) * 2^g)) :=
  (order.prodCongr (((bitWordFinEquiv (J a)).prodCongr (bitWordFinEquiv g)).trans
    finProdFinEquiv)).trans finProdFinEquiv

theorem oldIndex_val (order : V ≃ Fin n) (x : Old V a g) :
    (oldIndex order x).val = oldNumber order x := by
  rw [oldNumber_original]
  change _ + _ * _ = _ * _ + _
  ac_rfl

theorem packedIndex_val (order : V ≃ Fin n) (x : Packed V a g) :
    (packedIndex order x).val = packedNumber order x := by
  change (bitWordFinEquiv g x.2.2).val + 2^g * (bitWordFinEquiv (J a) x.2.1).val +
    (2^(J a)*2^g) * (order x.1).val = _ * 2^(J a+g) + (_ * _ + _)
  rw [pow_add]
  ring

/-- On the numerical old-site prefix, the computed owner is exactly the placement
whose fibers are scanned by the native preimage-list builder. -/
theorem owner_encoded (G : LiftedSlots V (2^a) (BitWord (packingLaneBits a g)))
    (order : V ≃ Fin n) {color offset mate displacement : ℕ → ℕ}
    (d : Directory G order color offset mate displacement) (layout : Bool)
    {w : ℕ} (ho : n * 2^(packingLaneBits a g) ≤ 2^w) (hn : n * (2^(J a) * 2^g) ≤ 2^w)
    (i : Fin (n * 2^(packingLaneBits a g))) :
    (row a (colors a) (J a) g layout color offset mate displacement i.val).owner =
      (encodedPlacement (oldIndex order) (packedIndex order)
        ((orderedDyadicPacking G order).placement layout) (Fin.ofNat (2^w) i.val)).val := by
  rw [encodedPlacement_eq _ _ _ ho hn i, packedIndex_val]
  have he : i.val = oldNumber order ((oldIndex order).symm i) := by
    rw [← oldIndex_val, Equiv.apply_symm_apply]
  rw [he, row_exact G order d]

/-- Read the two endpoint rows to determine the thin C role and opposite D owner.
The source is used as C when both endpoints are thin. -/
def demandRoles (src dst : Row ℕ) : ℕ × ℕ × ℕ × ℕ :=
  let C := if src.thick then dst else src
  let D := if src.thick then src else dst
  (C.assigned,C.source,C.target,D.owner)

theorem demandRoles_exact (G : LiftedSlots V (2^a) (BitWord (packingLaneBits a g)))
    (order : V ≃ Fin n) {color offset mate displacement : ℕ → ℕ}
    (d : Directory G order color offset mate displacement) (layout : Bool)
    (m : (orderedDyadicPacking G order).Motif) :
    let P := orderedDyadicPacking G order
    let readRow := fun x : Old V a g => row a (colors a) (J a) g layout color offset mate
      displacement (oldNumber order x)
    demandRoles (readRow (sourcePosition m.val)) (readRow (sourcePosition (P.actual m.val))) =
      (join a (packedNumber order (P.roleA m)) (P.bundle m).2.val,
       packedNumber order (P.roleA m), packedNumber order (P.roleB m),
       packedNumber order (P.roleD layout m)) := by
  dsimp only
  rw [row_exact G order d, row_exact G order d]
  by_cases ht : (orderedDyadicPacking G order).thick (sourcePosition m.val) <;>
    simp [demandRoles, PackingData.roleA, PackingData.roleB, PackingData.roleD, PackingData.bundle,
      PackingData.C, PackingData.D, ht]

end CompressorRecords.Shrink

end VPVNP
end Computability
end OAI
