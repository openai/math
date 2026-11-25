import OAI.Computability.BorderVNP.CubePhysicalVertices

/-! # Numbering exactly the packet vertices incident at one group

For one packet and one of its two grouping symbols, the selected cube bit
is fixed. Insert this bit into the little-endian rank of the remaining
coordinates. Division and remainder recover the local rank and all physical
vertex numbers in that group occur exactly once.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.VertexIndex

variable {n d blocks : ℕ}

/-- Little-endian index of the binary cube vertex. -/
def number {a : ℕ} : Vertex a ≃ Fin (2^a) := finFunctionFinEquiv

/-- Bit read from a product-alphabet label's little-endian word. -/
theorem digit_number {a b : ℕ} (u : Label a b) (i : Fin a) :
    (finFunctionFinEquiv u).val / b^i.val % b = (u i).val :=
  congrArg Fin.val (congrFun (finFunctionFinEquiv.symm_apply_apply u) i)

/-- Insert one digit at the binary place `scale`, preserving the other digits. -/
def insertBit (scale bit k : ℕ) := scale*(2*(k/scale)+bit) + k%scale

/-- Delete the binary digit at the given place. -/
def removeBit (scale k : ℕ) := scale*(k/scale/2) + k%scale

/-- The upper or lower alphabet symbol at the chosen grouping coordinate. -/
def groupSymbol (p : Packet n d blocks) (i : Fin (n+1)) (high : Bool) : Fin d :=
  if high then (p.1.1 i).val.2 else (p.1.1 i).val.1

/-- Reversing a packet flips just the first coordinate's grouping bit. -/
def ownerBit (i : Fin (n+1)) (orientation high : Bool) : Bool :=
  if i = 0 then xor high orientation else high

private theorem vertex_iff (p : Packet n d blocks) (v : Vertex (n+1)) (i : Fin (n+1)) (high : Bool) :
    vertexLabel p v i = groupSymbol p i high ↔ finTwoEquiv (v i) = ownerBit i p.1.2 high := by
  have h := (p.1.1 i).property.ne
  by_cases hi : i = 0
  · subst i
    cases high <;> cases hor : p.1.2 <;> cases hv : finTwoEquiv (v 0) <;>
      simp [vertexLabel, cornerBits, groupSymbol, ownerBit, hor, hv, h, h.symm]
  · cases high <;> cases hor : p.1.2 <;> cases hv : finTwoEquiv (v i) <;>
      simp [vertexLabel, cornerBits, groupSymbol, ownerBit, hi, hv, h, h.symm]

private theorem bool_injective : Function.Injective Bool.toNat := by decide

private theorem bit_toNat (v : Fin 2) : (finTwoEquiv v).toNat = v.val := by fin_cases v <;> rfl

private theorem mixed_lt {scale high low top : ℕ} (hl : low < scale) (hh : high < top) :
    scale*high + low < scale*top := by
  calc
    _ < scale*high+scale := Nat.add_lt_add_left hl _
    _ = scale*(high+1) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hh

private theorem high_count (i : Fin (n+1)) : 2^i.val * 2^(n-i.val) = 2^n := by
  rw [← pow_add, Nat.add_sub_of_le (by omega : i.val ≤ n)]

/-- Inserting one bit preserves the full-vertex index bound. -/
theorem insert_lt (i : Fin (n+1)) (bit : Bool) (k : Fin (2^n)) :
    insertBit (2^i.val) bit.toNat k.val < 2^(n+1) := by
  have hs : 0 < 2^i.val := pow_pos (by decide) _
  have hk : k.val / 2^i.val < 2^(n-i.val) := (Nat.div_lt_iff_lt_mul hs).mpr (by
    simpa only [mul_comm (2^(n-i.val)), high_count i] using k.isLt)
  have hh : 2*(k.val/2^i.val)+bit.toNat < 2*(2^(n-i.val)) := by have := bit.toNat_le; omega
  calc
    _ < 2^i.val * (2 * (2^(n-i.val))) := mixed_lt (Nat.mod_lt _ hs) hh
    _ = _ := by rw [mul_left_comm, high_count, pow_succ']

private theorem remove_lt (i : Fin (n+1)) (v : Fin (2^(n+1))) : removeBit (2^i.val) v.val < 2^n := by
  have hs : 0 < 2^i.val := pow_pos (by decide) _
  have hh : v.val / 2^i.val < 2*(2^(n-i.val)) := (Nat.div_lt_iff_lt_mul hs).mpr (by
    rw [mul_assoc, mul_comm (2^(n-i.val)), high_count, ← pow_succ']; exact v.isLt)
  exact (mixed_lt (Nat.mod_lt v.val hs) (show v.val / 2^i.val / 2 < 2^(n-i.val) by omega)).trans_eq
    (high_count i)

private theorem insert_digit {s : ℕ} (hs : 0 < s) (b : Bool) (k : ℕ) :
    insertBit s b.toNat k / s % 2 = b.toNat := by
  simp only [insertBit, Nat.mul_add_div hs, Nat.div_eq_of_lt (Nat.mod_lt _ hs), add_zero, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by have := b.toNat_le; omega)

private theorem remove_insert {s : ℕ} (hs : 0 < s) (b : Bool) (k : ℕ) :
    removeBit s (insertBit s b.toNat k) = k := by
  simp only [removeBit, insertBit, Nat.mul_add_div hs, Nat.div_eq_of_lt (Nat.mod_lt _ hs), add_zero,
    Nat.mul_add_div (by decide : 0 < 2), Nat.div_eq_of_lt (show b.toNat < 2 by have := b.toNat_le; omega),
    Nat.mul_add_mod, Nat.mod_mod, Nat.div_add_mod]

private theorem insert_remove {s v : ℕ} (hs : 0 < s) {b : ℕ} (h : v/s % 2 = b) :
    insertBit s b (removeBit s v) = v := by
  simp only [← h, removeBit, insertBit, Nat.mul_add_div hs, Nat.div_eq_of_lt (Nat.mod_lt _ hs),
    add_zero, Nat.div_add_mod, Nat.mul_add_mod, Nat.mod_mod]

/-- The native integer loop index enumerates precisely the vertices of the
packet incident at one specified symbol of the grouping coordinate. -/
def owned (p : Packet n d blocks) (i : Fin (n+1)) (high : Bool) :
    Fin (2^n) ≃ {v : Vertex (n+1) // vertexLabel p v i = groupSymbol p i high} where
  toFun k :=
    let b := ownerBit i p.1.2 high
    let x : Fin (2^(n+1)) := ⟨insertBit (2^i.val) b.toNat k.val, insert_lt i b k⟩
    ⟨number.symm x, (vertex_iff p _ i high).mpr (by
      apply bool_injective
      rw [bit_toNat (number.symm x i), ← digit_number (b := 2) (number.symm x) i, show finFunctionFinEquiv (number.symm x) = x from number.apply_symm_apply x]
      exact insert_digit (pow_pos (by decide) _) _ _)⟩
  invFun v := ⟨removeBit (2^i.val) (number v.val).val, remove_lt i _⟩
  left_inv k := Fin.ext (by
    dsimp only
    rw [number.apply_symm_apply]
    exact remove_insert (pow_pos (by decide) _) _ _)
  right_inv v := by
    apply Subtype.ext
    apply number.injective
    simp only [number.apply_symm_apply]
    apply Fin.ext
    apply insert_remove (pow_pos (by decide) _)
    rw [show number v.val = finFunctionFinEquiv v.val from rfl, digit_number (b := 2) v.val i, ← bit_toNat (v.val i),
      (vertex_iff ..).mp v.property]

/-- The inserted index is the actual table ordinal of the owned vertex. -/
theorem number_owned (p : Packet n d blocks) (i : Fin (n+1)) (high : Bool) (k : Fin (2^n)) :
    (number ((owned p i high k).val)).val = insertBit (2^i.val) (ownerBit i p.1.2 high).toNat k.val :=
  congrArg Fin.val (number.apply_symm_apply _)

end Cube.Physical.VertexIndex

end BorderVNP
end Computability
end OAI
