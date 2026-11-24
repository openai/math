import OAI.Computability.VPVNP.CompressorRecordsBundleRAM
import OAI.Computability.VPVNP.CompressorRecordsBundleKeys

/-!
# Exact bundle keys from the native classifier

An old physical site ends in a tag and a residual lane. Successive word
quotients separate those digits without multiplying their radices in a word.
The old outgoing port is a further least-significant digit. The resulting
keys agree with the thick-fiber and motif numbering of the compressor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleRAM

open BurstRAM Compression
open ShrinkRAM (div mod select)
open scoped Fin.CommRing

variable {w : ℕ}

/-- The binary radices are exact for digit decoding. The bucket offset
enters only sums and products, so its word encoding suffices. -/
structure Params (p : Fin 11 → Word w) (a c j g numBundles : ℕ) : Prop where
  degree : (p 0).val = 2^a
  residual : (p 1).val = 2^g
  tag : (p 2).val = 2^j
  mask : (p 3).val = 2^c
  offset : p 4 = (numBundles : Word w)

private theorem of_val {x : Word w} {n : ℕ} (h : x.val = n) : x = (n : Word w) := by
  subst n
  exact Fin.ext (Nat.mod_eq_of_lt x.isLt).symm

private theorem div_val (x y : Word w) : (div x y).val = x.val / y.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)

private theorem mod_val (x y : Word w) : (mod x y).val = x.val % y.val :=
  Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt x.isLt)

theorem decode_exact {p : Fin 11 → Word w} {a c j g B : ℕ}
    (hp : Params p a c j g B) (i : Word w) :
    let f := Shrink.decode a c (j+g) (i.val / 2^a)
    decode p i = ⟨(f.base : Word w), (f.low / 2^g : ℕ), (i.val % 2^a : ℕ),
      (f.mask : Word w), (f.slot : Word w)⟩ := by
  have q (x : ℕ) : x / 2^g / 2^j = x / 2^(j+g) := by
    rw [Nat.div_div_eq_div_mul, pow_add, Nat.mul_comm (2^j)]
  have t (x : ℕ) : x / 2^g % 2^j = x % 2^(j+g) / 2^g := by
    rw [pow_add, Nat.mod_mul_left_div_self]
  dsimp only [decode, Shrink.decode]
  congr 1 <;> apply of_val <;>
    simp only [div_val, mod_val, hp.degree, hp.residual, hp.tag, hp.mask, q, t]

/-- The five shrinking values the classifier reads from its old source and
destination. The destination index is obtained by its first, actual-mate read. -/
structure ReadsPlacement (p : Fin 11 → Word w) (m : Memory w) (i : Word w)
    (src dst : Shrink.Row ℕ) : Prop where
  srcThick : readValue p m i 1 = (src.thick.toNat : Word w)
  dstThick : readValue p m i 2 = (dst.thick.toNat : Word w)
  owner : readValue p m i 3 = (src.owner : Word w)
  srcAssigned : readValue p m i 4 = (src.assigned : Word w)
  dstAssigned : readValue p m i 5 = (dst.assigned : Word w)

/-- The emitted words encode the combined bucket and its numerical sorting key,
with the layout and the two endpoint rows supplied by the previous pass. -/
theorem classify_rows {p : Fin 11 → Word w} {a c j g B : ℕ} (hp : Params p a c j g B)
    {m : Memory w} {i : Word w} {src dst : Shrink.Row ℕ} (hr : ReadsPlacement p m i src dst) :
    let f := Shrink.decode a c (j+g) (i.val / 2^a)
    let slot := i.val % 2^a
    bucket p m i = (BundleKeys.bucketFromRows B (2^a) slot src dst : Word w) ∧
      key p m i = (BundleKeys.numericKey (2^a) (2^j) (2^c) f.base (f.low / 2^g) slot f.mask
        f.slot (src.thick && dst.thick) : Word w) := by
  dsimp only [bucket, key]
  rw [decode_exact hp, hr.srcThick, hr.dstThick, hr.owner, hr.srcAssigned, hr.dstAssigned,
    hp.offset, of_val hp.degree, of_val hp.tag, of_val hp.mask]
  cases hs : src.thick <;> cases hd : dst.thick <;>
    simp [BundleKeys.bucketFromRows, BundleKeys.numericBucket, BundleKeys.numericKey, hs, hd]

/-- The persistent index of a typed old arc gives the same source site and
outgoing port to the native classifier and to the two fiber orders. -/
theorem classify_oldArc {V : Type} {n a g : ℕ} (order : V ≃ Fin n)
    {p : Fin 11 → Word w} (hp : Params p a (Shrink.colors a) (Shrink.J a) g (BundleKeys.numBundles n a g))
    (e : BundleKeys.OldArc V a g) {i : Word w} (hi : i.val = (BundleKeys.oldArcOrder order e).val)
    {m : Memory w} {src dst : Shrink.Row ℕ} (hr : ReadsPlacement p m i src dst) :
    bucket p m i = (BundleKeys.bucketFromRows (BundleKeys.numBundles n a g) (2^a) e.1.2.val src dst : Word w) ∧
      key p m i = (BundleKeys.keyAt order (src.thick && dst.thick) e : Word w) := by
  obtain ⟨hb, hk⟩ := classify_rows hp hr
  rw [BundleKeys.oldArcOrder_val] at hi
  have hs : i.val % 2^a = e.1.2.val := hi ▸ Nat.mul_add_mod_of_lt e.1.2.isLt
  have hv : i.val / 2^a = Shrink.oldNumber order (sourcePosition e) := by
    rw [hi, Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt e.1.2.isLt, Nat.add_zero]
  rw [hs, hv] at hk
  exact ⟨hs ▸ hb, hk⟩

end CompressorRecords.BundleRAM

end VPVNP
end Computability
end OAI
