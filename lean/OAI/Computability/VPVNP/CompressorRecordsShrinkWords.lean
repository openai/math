import OAI.Computability.VPVNP.CompressorRecordsShrinkRAM

/-!
# Word correctness of the shrinking owner computation

The native directory arithmetic is carried out modulo the machine word size. Only
the low-field XOR and the color-bit test need a nonwrapping intermediate. Addresses
of the four inputs are taken in the actual external memory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkRAM

open BurstRAM BurstRAM.PrivateRAM Compression

variable {w : ℕ}

/-- Encode a natural number as a machine word by reducing it modulo `2^w`. -/
abbrev word (w n : ℕ) : Word w := Fin.ofNat (2^w) n

private theorem word_val {n : ℕ} (h : n < 2^w) : (word w n).val = n := Nat.mod_eq_of_lt h

private theorem word_of_val (z : Word w) : word w z.val = z := Fin.ext (word_val z.isLt)

private theorem word_add (x y : ℕ) : word w x + word w y = word w (x+y) := by
  apply Fin.ext; exact (Nat.add_mod ..).symm

private theorem word_mul (x y : ℕ) : word w x * word w y = word w (x*y) := by
  apply Fin.ext; exact (Nat.mul_mod ..).symm

private theorem word_sub_val (x y : Word w) (h : y.val ≤ x.val) : (x-y).val = x.val-y.val := by
  rw [Fin.val_sub, show 2^w-y.val+x.val = x.val-y.val+2^w by have := y.isLt; omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

@[simp] private theorem div_val (x y : Word w) : (div x y).val = x.val/y.val :=
  Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)

@[simp] private theorem mod_val (x y : Word w) : (mod x y).val = x.val%y.val :=
  Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt x.isLt)

private theorem bit_value (z k : ℕ) : z / 2^k % 2 = (z.testBit k).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (z / 2^k) with h | h <;> simp [h]

private theorem shiftBit_val (z last col : Word w) (hc : col.val ≤ last.val)
    (hw : last.val < w) (hw2 : 2 < 2^w) :
    (mod (BinaryOp.shiftRight.eval z (last-col)) 2).val =
      (z.val.testBit (last.val-col.val)).toNat := by
  have hk := word_sub_val last col hc
  have fit : (last-col).val < w := by omega
  have h2 : (2 : Word w).val = 2 := Nat.mod_eq_of_lt hw2
  have hz : z.val >>> (last.val-col.val) < 2^w := by
    rw [Nat.shiftRight_eq_div_pow]; exact (Nat.div_le_self ..).trans_lt z.isLt
  rw [mod_val, BinaryOp.eval, ite_eq_left fit, hk, Fin.val_ofNat, Nat.mod_eq_of_lt hz, h2,
    Nat.shiftRight_eq_div_pow, bit_value]

/-- Conditions on the shrinking worker's public radices, last color, and layout selector that
justify decoding the low field and testing the color bit in a machine word. -/
structure Params (p : Fin 14 → Word w) (a c j g : ℕ) (layout : Bool) : Prop where
  lane : (p 0).val = 2^g
  tag : (p 1).val = 2^j
  degree : (p 2).val = 2^a
  mask : (p 3).val = 2^c
  last : (p 4).val = c-1
  choose : p 5 = if layout then 1 else 0
  low_fit : 2^(j+g) < 2^w
  color_fit : c-1 < w
  two_fit : 2 < 2^w

/-- Read the natural value in a column at the given index, adding the index to its public base
address in word arithmetic. -/
def column (p : Fin 14 → Word w) (m : Memory w) (c : Fin 14) (index : ℕ) : ℕ :=
  (m (p c + word w index).val).val

private theorem chunk_val {p : Fin 14 → Word w} {a c j g : ℕ} {layout : Bool}
    (h : Params p a c j g layout) : (p 1*p 0).val = 2^(j+g) := by
  rw [Fin.val_mul, h.tag, h.lane, ← pow_add, Nat.mod_eq_of_lt h.low_fit]

/-- Decode the fixed-width old position into its base, mask, slot and low lane. -/
theorem decode_exact {p : Fin 14 → Word w} {a c j g : ℕ} {layout : Bool}
    (h : Params p a c j g layout) (i : Word w) :
    let f := Shrink.decode a c (j+g) i.val
    decode p i = ⟨word w f.base,word w f.mask,word w f.slot,word w f.low⟩ := by
  unfold decode Shrink.decode
  simp only [div, mod, BinaryOp.eval, Fin.val_ofNat, h.degree, h.mask, chunk_val h]
  have h₁ := (Nat.div_le_self i.val (2^(j+g))).trans_lt i.isLt
  have h₂ := (Nat.div_le_self (i.val / 2^(j+g)) (2^a)).trans_lt h₁
  rw [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂]

private theorem select_bit (z : Word w) (b : Bool) (hz : z.val = b.toNat) (x y : Word w) :
    select z x y = if b then y else x := by
  cases b with
  | false => have e : z = 0 := Fin.ext hz; simp [e]
  | true =>
    have e : z = 1 := by
      apply Fin.ext
      have h : 1 < 2^w := by have := z.isLt; simp at hz; omega
      exact hz.trans (Nat.mod_eq_of_lt h).symm
    simp [e]

set_option maxHeartbeats 850000 in
/-- Numeric correctness for one native position. Output addresses remain words, so
only values used inside bit-field operations require a fit bound. -/
theorem outputs_row {p : Fin 14 → Word w} {a c j g : ℕ} {layout : Bool}
    (hp : Params p a c j g layout) (m : Memory w) (i : Word w)
    (hc : column p m 6 (Shrink.decode a c (j+g) i.val).base ≤ c-1)
    (hj : column p m 7 (Shrink.decode a c (j+g) i.val).base < 2^j) :
    let r := Shrink.row a c j g layout (column p m 6) (column p m 7) (column p m 8) (column p m 9) i.val
    outputs p m i = ⟨word w r.owner, word w r.thick.toNat, word w r.assigned, word w r.target⟩ := by
  let f := Shrink.decode a c (j+g) i.val
  let e := f.base*2^a+f.slot
  let co := m (p 6 + word w f.base).val
  let off := m (p 7 + word w f.base).val
  let mate := m (p 8 + word w e).val
  let shift := m (p 9 + word w e).val
  let t := f.mask.testBit (c-1-co.val)
  let lo := f.low ^^^ (off.val*2^g)
  let chunk := p 1*p 0
  let A := Shrink.join (j+g) f.base lo
  let B := Shrink.join (j+g) (mate.val / 2^a) (lo ^^^ (shift.val % 2^(j+g)))
  let pack := Shrink.join (j+g) f.base f.low
  have hdeg : p 2 = word w (2^a) := by rw [← hp.degree, word_of_val]
  have hchunk : chunk = word w (2^(j+g)) := by rw [← chunk_val hp, word_of_val]
  have hr : p 0 = word w (2^g) := by rw [← hp.lane, word_of_val]
  have he : baseArc p ⟨word w f.base,word w f.mask,word w f.slot,word w f.low⟩ = word w e := by
    simp only [baseArc,hdeg,word_mul,word_add,e]
  have hm : f.mask < 2^w := by
    dsimp [f,Shrink.decode]
    exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans (hp.mask ▸ (p 3).isLt)
  have hl : f.low < 2^w := by
    exact (Nat.mod_lt _ (Nat.two_pow_pos _)).trans hp.low_fit
  have hoff : off.val * 2^g < 2^w := by
    exact (Nat.mul_lt_mul_of_pos_right hj (Nat.two_pow_pos _)).trans (by simpa [pow_add] using hp.low_fit)
  have hbit : (mod (BinaryOp.shiftRight.eval (word w f.mask) (p 4-co)) 2).val = t.toNat := by
    rw [shiftBit_val _ _ _ (hp.last ▸ hc) (hp.last ▸ hp.color_fit) hp.two_fit, word_val hm, hp.last]
  have hlow : xor (word w f.low) (off*p 0) = word w lo := by
    rw [← word_of_val off, hr, word_mul]
    change word w ((word w f.low).val ^^^ (word w (off.val*2^g)).val) = _
    rw [word_val hl, word_val hoff]
  have hlowfit : lo < 2^w := Nat.xor_lt_two_pow hl hoff
  have hB : div mate (p 2) * chunk + xor (word w lo) (mod shift chunk) = word w B := by
    have hdiv : div mate (p 2) = word w (mate.val/2^a) := by simp [div, BinaryOp.eval,hp.degree,word]
    have hx : xor (word w lo) (mod shift chunk) = word w (lo ^^^ (shift.val % 2^(j+g))) := by
      change word w ((word w lo).val ^^^ (mod shift chunk).val) = _
      rw [word_val hlowfit, mod_val, show chunk.val = _ from chunk_val hp]
    rw [hdiv, hx, hchunk, word_mul, word_add]; rfl
  have hA : word w f.base * chunk + word w lo = word w A := by rw [hchunk, word_mul, word_add]; rfl
  have hpack : word w f.base * chunk + word w f.low = word w pack := by rw [hchunk, word_mul, word_add]; rfl
  let fw : Fields w := ⟨word w f.base,word w f.mask,word w f.slot,word w f.low⟩
  have hdc : decode p i = fw := decode_exact hp i
  have hcs : readColumns p m fw = (co,off,mate,shift) := by
    dsimp only [readColumns,fw]
    rw [he]
  unfold outputs
  rw [hdc]
  dsimp only
  rw [hcs]
  change Outputs.mk (select _ (select _ (word w f.base*chunk+xor (word w f.low) (off*p 0))
    (div mate (p 2)*chunk+xor (xor (word w f.low) (off*p 0)) (mod shift chunk)))
    (word w f.base*chunk+word w f.low)) _ _ _ = _
  dsimp only [fw]
  rw [hlow, hA, hB, hpack, select_bit _ t hbit, hp.choose]
  rw [show word w A * p 2 + word w f.slot = word w (A*2^a+f.slot) by rw [hdeg, word_mul, word_add]]
  have ht : mod (BinaryOp.shiftRight.eval (word w f.mask) (p 4-co)) 2 = word w t.toNat := by
    rw [← hbit, word_of_val]
  rw [ht]
  change Outputs.mk (if t then word w pack else select (if layout then 1 else 0) (word w A) (word w B))
      (word w t.toNat) (word w (A*2^a+f.slot)) (word w B) =
    Outputs.mk (word w (if t then pack else if layout then B else A))
      (word w t.toNat) (word w (A*2^a+f.slot)) (word w B)
  cases layout <;> cases t <;> simp

/-- Word values written by the opcode table on a genuine old position, in the
numbering used by the next level's site and incidence directories. -/
theorem outputs_exact {V : Type} {a g n : ℕ} (G : LiftedSlots V (2^a) (BitWord (packingLaneBits a g)))
    (order : V ≃ Fin n) (p : Fin 14 → Word w) (m : Memory w) (layout : Bool)
    (hp : Params p a (Shrink.colors a) (Shrink.J a) g layout)
    (d : Shrink.Directory G order (column p m 6) (column p m 7) (column p m 8) (column p m 9))
    (hOld : n * 2^(packingLaneBits a g) ≤ 2^w)
    (hSlots : n * (2^(Shrink.J a) * 2^g) * 2^a ≤ 2^w) (x : Shrink.Old V a g) :
    let P := orderedDyadicPacking G order
    let i := word w (Shrink.oldNumber order x)
    let out := outputs p m i
    (out.owner.val, out.thick.val, out.assigned.val, out.target.val) =
      (Shrink.packedNumber order (P.placement layout x), (decide (P.thick x)).toNat,
       Shrink.join a (Shrink.packedNumber order (P.assignedBundle x).1) (P.assignedBundle x).2.val,
       Shrink.packedNumber order (P.siteGraph.target (P.assignedBundle x)).1) := by
  let P := orderedDyadicPacking G order
  let i := word w (Shrink.oldNumber order x)
  have hi : i.val = Shrink.oldNumber order x := by
    apply word_val
    rw [← Shrink.oldIndex_val]
    exact (Fin.isLt _).trans_le hOld
  have hd := Shrink.decode_oldNumber order x
  have hco : column p m 6 (Shrink.decode a (Shrink.colors a) (Shrink.J a+g) i.val).base ≤ Shrink.colors a-1 := by
    rw [hi, hd, d.color_at]
    exact Nat.le_sub_one_of_lt (P.color x.1.1).isLt
  have hj : column p m 7 (Shrink.decode a (Shrink.colors a) (Shrink.J a+g) i.val).base < 2^(Shrink.J a) := by
    rw [hi,hd,d.offset_at]; exact Fin.isLt _
  have he := outputs_row hp m i hco hj
  dsimp only at he ⊢
  rw [hi, Shrink.row_exact G order d] at he
  change ((outputs p m i).owner.val, (outputs p m i).thick.val, (outputs p m i).assigned.val,
    (outputs p m i).target.val) = _
  rw [he]
  have hsite (v : Shrink.Packed V a g) :
      Shrink.packedNumber order v < n * (2^(Shrink.J a) * 2^g) := by
    rw [← Shrink.packedIndex_val]; exact Fin.isLt _
  have hsiteWord (v : Shrink.Packed V a g) : Shrink.packedNumber order v < 2^w :=
    (hsite v).trans_le ((Nat.le_mul_of_pos_right _ (Nat.two_pow_pos a)).trans hSlots)
  have hefit : Shrink.join a (Shrink.packedNumber order (P.assignedBundle x).1) (P.assignedBundle x).2.val < 2^w := by
    unfold Shrink.join
    calc
      _ < Shrink.packedNumber order (P.assignedBundle x).1 * 2^a + 2^a := by
        exact Nat.add_lt_add_left (Fin.isLt _) _
      _ = (Shrink.packedNumber order (P.assignedBundle x).1+1)*2^a := by ring
      _ ≤ _ := (Nat.mul_le_mul_right _ (hsite (P.assignedBundle x).1)).trans hSlots
  have boundBit (b : Bool) : b.toNat < 2 := by cases b <;> decide
  have htfit := (boundBit (decide (P.thick x))).trans hp.two_fit
  change ((word w (Shrink.packedNumber order (P.placement layout x))).val,
    (word w (decide (P.thick x)).toNat).val,
    (word w (Shrink.join a (Shrink.packedNumber order (P.assignedBundle x).1) (P.assignedBundle x).2.val)).val,
    (word w (Shrink.packedNumber order (P.siteGraph.target (P.assignedBundle x)).1)).val) = _
  rw [word_val (hsiteWord _), word_val htfit, word_val hefit, word_val (hsiteWord _)]

end CompressorRecords.ShrinkRAM

end VPVNP
end Computability
end OAI
