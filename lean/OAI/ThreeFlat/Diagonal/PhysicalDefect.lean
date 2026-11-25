import OAI.ThreeFlat.Diagonal.PhysicalBlock

namespace OAI
/-! # Rank defect on the actual external halves

Each chunk and the auxiliary register have `a` bits. The same type indexes
both external halves, so the identity factor which remains on the active
half has exactly the dimension of the catalyst.
-/

namespace ThreeFlat.Diagonal

abbrev BitString (a : ℕ) := Fin a → Bool

/-- A fixing has two chunk words per tick, one initial auxiliary word, and
one subsequent auxiliary word per tick. -/
theorem card_blockFixing_le (a n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (BlockFixing n (BitString a) (BitString a)) ≤ 2 ^ (4 * n * a) := by
  simp only [BlockFixing, BitString, Fintype.card_prod, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, ← Nat.pow_mul, ← Nat.pow_add]
  apply Nat.pow_le_pow_right (by decide)
  have h : a ≤ a * n := Nat.le_mul_of_pos_right a hn
  calc
    _ ≤ a * n + (a * n + (a * n + a * n)) := by omega
    _ = 4 * n * a := by ring

/-- The matrix observed outside the machine after the auxiliary memory is
initialized and tested for zero. -/
noncomputable def physicalRun {F I β : Type*} [Field F] [Fintype I] [DecidableEq I]
    {a n : ℕ} (blocks : List β) (slot : β → Fin n → I) (active : β → Bool)
    (X : β → BlockFixing n (BitString a) (BitString a) → Matrix (I → BitString a) (I → BitString a) F) :
    Matrix (Bool → I → BitString a) (Bool → I → BitString a) F :=
  ((blocks.map fun t => ∑ f, physicalFixing (slot t) (active t) f (X t f)).prod).submatrix
    (fun x => (x, fun _ => false)) (fun y => (y, fun _ => false))

/-- A full identity shift is impossible on the two external memory halves at
these scales, after all consistent per-block auxiliary paths have been summed. -/
theorem physical_replacement_ne_identity_add {F I β : Type*} [Field F] [Fintype I] [DecidableEq I]
    {a n w d : ℕ} (blocks : List β) (slot : β → Fin n → I) (active : β → Bool)
    (tick : β → Fin n → BitString a → BitString a → Matrix (BitString a) (BitString a) F)
    (X : β → BlockFixing n (BitString a) (BitString a) → Matrix (I → BitString a) (I → BitString a) F)
    (ha : a = 2 ^ (w ^ 10 - w ^ 4)) (hw : d + 8 ≤ w) (hn : 1 ≤ n) (hmax : n ≤ w ^ d)
    (hsave : 2 ^ (w ^ 3) * 2 ^ (w ^ 10 - w) ≤ a * Fintype.card I)
    (nsteps : blocks.length ≤ 2 ^ (w ^ 6) / n)
    (approx : ∀ t ∈ blocks, ∀ f, (X t f - fixingWeight (tick t) f • 1).rank ≤
      2 ^ (a * Fintype.card I - 2 ^ (w ^ 3) * 2 ^ (w ^ 10 - w))) :
    physicalRun blocks slot active (fun t f => fixingWeight (tick t) f • 1) ≠
      1 + physicalRun blocks slot active X := by
  let c := a * Fintype.card I
  have hrem : Fintype.card (I → BitString a) ≤ 2 ^ (2 * c - c) := by
    simp only [BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← Nat.pow_mul]
    apply Nat.pow_le_pow_right (by decide)
    dsimp only [c]; omega
  have hext : Fintype.card (Bool → I → BitString a) = 2 ^ (2 * c) := by
    simp only [BitString, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← Nat.pow_mul]
    rw [Nat.mul_comm 2 c]
  apply diagonal_replacement_ne_identity_add (β := β) (ι := MachineState I (BitString a) (BitString a))
    (w := w) (d := d) (L := n) (B := 2 * c) (c := c) blocks Finset.univ
    (fun t _ => halfCoordinates (slot t) (active t)) (fun t _ => halfCoordinates (slot t) (active t))
    (fun _ f => checkEnd (f.1, f.2.2.1)) (fun _ f => checkEnd (f.2.1, endWord n f.2.2.1 f.2.2.2))
    (fun t => fixingWeight (tick t)) X (fun x => (x, fun _ => false)) hw hmax hsave (by omega) nsteps
  · rw [Finset.card_univ, ← ha]
    exact card_blockFixing_le a n hn
  · exact hrem
  · exact hext
  · exact fun t ht f _ => approx t ht f

end ThreeFlat.Diagonal

end OAI
