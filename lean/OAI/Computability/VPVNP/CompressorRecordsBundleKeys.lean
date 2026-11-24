import OAI.Computability.VPVNP.CompressorRecordsShrink
import OAI.Computability.VPVNP.SlotBundleNumbering

/-!
# Bundle addresses and relative sorting keys from physical source ports

The classifying scan reads both thickness flags and the bundle assignment at each
endpoint. Its table separates thick wires from CD wires while retaining every
old port as its absolute identifier. Sorting keys remove the residual lane and
retain the original port, mask, and slot-label fields.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleKeys

open Compression VPVNP.CompressorRecords.Shrink

/-- The two bundle arrays are adjacent. A CD wire belongs to its thin endpoint,
with the source used when both endpoints are thin. -/
def numericBucket (numBundles degree srcOwner srcAssigned dstAssigned slot : ℕ)
    (srcThick dstThick : Bool) : ℕ :=
  if srcThick && dstThick then srcOwner*degree+slot
  else numBundles + (if srcThick then dstAssigned else srcAssigned)

/-- The thick-wire key uses the two suppressed source fields. The motif key
includes the normalized source base, tag and physical outgoing slot. -/
def numericKey (degree tagCount colorCount base tag slot mask label : ℕ) (both : Bool) : ℕ :=
  let thick := mask*degree+label
  if both then thick else (((base*tagCount+tag)*degree+slot)*colorCount+mask)*degree+label

variable {V : Type} {n a g : ℕ}
variable (G : LiftedSlots V (2^a) (BitWord (packingLaneBits a g))) (order : V ≃ Fin n)
local notation "P" => orderedDyadicPacking G order

/-- An arc in the pre-shrink graph, carrying the source port, lane information, and mask used
to classify it into a packed bundle. -/
abbrev OldArc (V : Type) (a g : ℕ) := Arc V (BitWord a) (BitWord (J a)) (BitWord g)
    (2^a) (colors a)

/-- Scan each physical outgoing slot, keeping the separate parallel-port numbers. -/
def oldArcOrder : OldArc V a g ≃ Fin ((n*2^(packingLaneBits a g))*2^a) :=
  let endpoints : OldArc V a g ≃ Old V a g × Fin (2^a) :=
    ⟨fun e ↦ (sourcePosition e,e.1.2), fun p ↦ ((p.1.1,p.2),p.1.2),fun _ ↦ rfl,fun _ ↦ rfl⟩
  endpoints.trans (((oldIndex order).prodCongr (Equiv.refl _)).trans finProdFinEquiv)

theorem oldArcOrder_val (e : OldArc V a g) :
    (oldArcOrder order e).val = oldNumber order (sourcePosition e)*2^a+e.1.2.val := by
  change e.1.2.val + 2^a*(oldIndex order (sourcePosition e)).val = _
  rw [oldIndex_val]; ac_rfl

/-- Numeric owner of either kind of bundle in the combined count and row arrays. -/
def bundleAddress (b : Packed V a g × Fin (2^a)) : ℕ := packedNumber order b.1 * 2^a+b.2.val

/-- Number of packed port bundles in one of the two classification arrays, also the offset
where the CD bundle array begins. -/
def numBundles (n a g : ℕ) := (n*(2^(J a)*2^g))*2^a

/-- Compute an old arc's within-bundle sort key from the decoded source number and outgoing
slot, using the thick-wire or CD ordering as selected. -/
def keyAt (both : Bool) (e : OldArc V a g) : ℕ :=
  let f := Shrink.decode a (colors a) (J a+g) (oldNumber order (sourcePosition e))
  numericKey (2^a) (2^(J a)) (2^(colors a)) f.base (f.low/2^g) e.1.2.val f.mask f.slot both

private theorem tag_value (z : BitWord (J a) × BitWord g) :
    lowNumber z / 2^g = (bitWordFinEquiv (J a) z.1).val := by
  unfold lowNumber join
  rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt (bitWordFinEquiv g z.2).isLt,
    Nat.add_zero]

/-- The value emitted in a thick bundle equals its sort key at its actual lane. -/
theorem thick_key (b : Packed V a g × Fin (2^a)) (wire : (P).ThickFiber b) :
    keyAt order true wire.val.val = ((P).thickFiberIndex b wire).val := by
  rw [keyAt, decode_oldNumber, numericKey]
  change _ * 2^a + _ = _ + 2^a * _
  ac_rfl

/-- The CD sorting key is the key of the normalized original arc in Appendix C. -/
theorem motif_key (m : (P).Motif) :
    keyAt order false m.val = ((P).baseMotifIndex order (bitWordFinEquiv (J a)) ((P).baseMotif m)).val := by
  rw [keyAt, decode_oldNumber, numericKey]
  dsimp only
  rw [tag_value]
  change (((_ * 2^(J a) + _) * 2^a + _) * 2^(colors a) + _) * 2^a + _ =
    (_ + 2^a * _) + 2^(colors a)*2^a * _ + 2^a*(2^(colors a)*2^a) * _ +
      2^(J a)*(2^a*(2^(colors a)*2^a)) * _
  have arithmetic (x t s mask h d T C : ℕ) :
      (((x*T+t)*d+s)*C+mask)*d+h = (h+d*mask)+C*d*s+d*(C*d)*t+T*(d*(C*d))*x := by ring
  exact arithmetic ..

/-- Four stored placement columns and the source and target vertices of the assigned
bundle, expressed solely in terms of the constructed packing. -/
def siteRow (layout : Bool) (x : Old V a g) : Shrink.Row ℕ :=
  let e := (P).assignedBundle x
  ⟨packedNumber order x.1, packedNumber order e.1, packedNumber order ((P).siteGraph.target e).1,
   join a (packedNumber order e.1) e.2.val, decide ((P).thick x),
   packedNumber order ((P).placement layout x)⟩

/-- Look up the independently stored source and destination placement records. -/
def bucketFromRows (num degree port : ℕ) (src dst : Shrink.Row ℕ) : ℕ :=
  numericBucket num degree src.owner src.assigned dst.assigned port src.thick dst.thick

theorem thick_bucket (layout : Bool) (wire : (P).ThickWire) :
    bucketFromRows (numBundles n a g) (2^a) wire.val.1.2.val
      (siteRow G order layout (sourcePosition wire.val))
      (siteRow G order layout (sourcePosition ((P).actual wire.val))) =
      bundleAddress order wire.val.1 := by
  have ⟨hs,ht⟩ := wire.property
  simp [bucketFromRows, siteRow, numericBucket, hs, ht, PackingData.placement, bundleAddress]
  rfl

theorem motif_bucket (layout : Bool) (m : (P).Motif) :
    bucketFromRows (numBundles n a g) (2^a) m.val.1.2.val
      (siteRow G order layout (sourcePosition m.val)) (siteRow G order layout (sourcePosition ((P).actual m.val))) =
      numBundles n a g + bundleAddress order ((P).bundle m) := by
  by_cases hs : (P).thick (sourcePosition m.val)
  · have ht : ¬(P).thick (sourcePosition ((P).actual m.val)) := fun h ↦ m.property ⟨hs,h⟩
    simp [bucketFromRows, numericBucket, siteRow, hs, ht, bundleAddress, join, PackingData.bundle, PackingData.C]
  · simp [bucketFromRows, numericBucket, siteRow, hs, bundleAddress, join, PackingData.bundle, PackingData.C]

end CompressorRecords.BundleKeys

end VPVNP
end Computability
end OAI
