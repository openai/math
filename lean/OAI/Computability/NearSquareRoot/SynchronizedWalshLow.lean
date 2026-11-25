import OAI.Computability.NearSquareRoot.PhysicalWalshSelectedMeaning

/-! # The Walsh action on the low address bits -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

open Matrix

/-- The low `s` bits in a physical address of width `k`, indexed from zero. -/
def lowBits (k s : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun p => p.val < s)

@[simp] theorem mem_lowBits {k s : ℕ} (p : Fin k) : p ∈ lowBits k s ↔ p.val < s := by
  simp [lowBits]

theorem lowBits_eq_window {k s : ℕ} (hs : s ≤ k) :
    lowBits k s = FlatWalshWindow.bits k s 0 (by omega) := by
  ext p
  simp [FlatWalshWindow.mem_bits]

@[simp] theorem card_lowBits {k s : ℕ} (hs : s ≤ k) : (lowBits k s).card = s := by
  rw [lowBits_eq_window hs, FlatWalshWindow.bits, Finset.card_image_of_injective _ (Function.Embedding.injective _)]
  simp

/-- In the packed record order the normalized Walsh matrix on the low bits
applies the full physical Walsh row independently in each consecutive block. -/
theorem lowWalsh_mulVec {k s : ℕ} (hs : s ≤ k) (x : ℕ → ℂ) (i : Fin (2^k)) :
    (flatWalsh (lowBits k s) *ᵥ (fun j => x j.val)) i = FlatWalshNode.activeRow s 1 x i.val := by
  rw [lowBits_eq_window hs]
  exact congrFun (PhysicalWalsh.Pieces.activeRow_low k s hs x).symm i

end BoxFin

end NearSquareRoot
end Computability
end OAI
