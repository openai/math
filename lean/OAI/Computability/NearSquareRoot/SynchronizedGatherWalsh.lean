import OAI.Computability.NearSquareRoot.SynchronizedBitAddress
import OAI.Computability.NearSquareRoot.SynchronizedWalshLow

/-! # The physical Walsh pass after gathering its selected positions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

open Matrix Finset
noncomputable section
variable {k : ℕ}

theorem offBits_image (bits : Finset (Fin k)) (p : Equiv.Perm (Fin k)) (x y : Fin (2^k)) :
    offBits (bits.image p) (bitAddress p x) (bitAddress p y) ↔ offBits bits x y := by
  constructor
  · intro h i hi
    have hn : p i ∉ bits.image p := by simpa using hi
    simpa using h (p i) hn
  · intro h t ht
    obtain ⟨i,rfl⟩ := p.surjective t
    have hn : i ∉ bits := by simpa using ht
    simpa using h i hn

theorem physicalOverlap_image (bits : Finset (Fin k)) (p : Equiv.Perm (Fin k)) (x y : Fin (2^k)) :
    physicalOverlap (bits.image p) (bitAddress p x) (bitAddress p y) = physicalOverlap bits x y := by
  unfold physicalOverlap
  rw [filter_image, card_image_of_injective _ p.injective]
  simp

/-- The matrix stays the same when the same permutation reorders the data bits
and the chosen Walsh positions. -/
theorem flatWalsh_image (bits : Finset (Fin k)) (p : Equiv.Perm (Fin k)) :
    flatWalsh bits = (flatWalsh (bits.image p)).submatrix (bitAddress p) (bitAddress p) := by
  classical
  ext x y
  simp [flatWalsh, offBits_image, physicalOverlap_image, card_image_of_injective _ p.injective]

theorem gather_image (bits : Finset (Fin k)) (p : Equiv.Perm (Fin k))
    (hp : ∀ i, (p i).val < bits.card ↔ i ∈ bits) :
    bits.image p = lowBits k bits.card := by
  ext j
  obtain ⟨i,rfl⟩ := p.surjective j
  simp [hp]

/-- For an arbitrary completion of the gathered array outside its physical
bounds, each original entry is the low-field Walsh output at its gathered rank. -/
theorem gatherWalsh_mulVec_of_values (bits : Finset (Fin k)) (p : Equiv.Perm (Fin k))
    (hp : ∀ i, (p i).val < bits.card ↔ i ∈ bits) (x : Fin (2^k) → ℂ) (w : ℕ → ℂ)
    (hw : ∀ j : Fin (2^k), w j.val = x ((bitAddress p).symm j)) (i : Fin (2^k)) :
    (flatWalsh bits *ᵥ x) i = FlatWalshNode.activeRow bits.card 1 w (bitAddress p i).val := by
  have hs : bits.card ≤ k := by simpa using bits.card_le_univ
  rw [flatWalsh_image bits p, gather_image bits p hp, submatrix_mulVec_equiv]
  change (flatWalsh (lowBits k bits.card) *ᵥ (fun j => x ((bitAddress p).symm j))) _ = _
  rw [← funext hw]
  exact lowWalsh_mulVec hs w _

/-- Concrete gather of the input tape, zero-extended above its physical size. -/
def gatheredArray (p : Equiv.Perm (Fin k)) (x : Fin (2^k) → ℂ) (z : ℕ) : ℂ :=
  if hz : z < 2^k then x ((bitAddress p).symm ⟨z,hz⟩) else 0

theorem gatherWalsh_mulVec (bits : Finset (Fin k)) (p : Equiv.Perm (Fin k))
    (hp : ∀ i, (p i).val < bits.card ↔ i ∈ bits) (x : Fin (2^k) → ℂ) (i : Fin (2^k)) :
    (flatWalsh bits *ᵥ x) i =
      FlatWalshNode.activeRow bits.card 1 (gatheredArray p x) (bitAddress p i).val :=
  gatherWalsh_mulVec_of_values bits p hp x _ (fun j => by simp [gatheredArray,j.isLt]) i

/-- The ordered even-piece traversal and its terminal zero- or one-bit pass
give the original arbitrary-layer matrix after ungathering. -/
theorem gatherWalsh_pieces (bits : Finset (Fin k)) (p : Equiv.Perm (Fin k))
    (hp : ∀ i, (p i).val < bits.card ↔ i ∈ bits)
    (A W : ℕ) (hA : 1 < A) (hW : 0 < W) (width : ℕ) (x : Fin (2^k) → ℂ) (i : Fin (2^k)) :
    (flatWalsh bits *ᵥ x) i =
      FlatWalshNode.activeRow (bits.card%2) 1
        ((PhysicalWalsh.Pieces.schedule A W hW k bits.card width).foldl
          (fun y q => FlatWalshNode.idealRow A q y) (gatheredArray p x)) (bitAddress p i).val := by
  rw [PhysicalWalsh.Pieces.ideal_complete A W hA hW]
  exact gatherWalsh_mulVec bits p hp x i

end
end BoxFin

end NearSquareRoot
end Computability
end OAI
