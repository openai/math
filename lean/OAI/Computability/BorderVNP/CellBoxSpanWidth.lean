import OAI.Computability.BorderVNP.CellBoxSpanStatic

/-! # Combined private box span for arbitrary binary identifier widths

Global record IDs may be numerically large. Their contribution to the
source and resolved block tables is through their canonical binary length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

/-- The raw numerical maximum enters the block-span estimate only through its binary width. -/
theorem blockSpan_static_width (D : Directory) (p : ℕ) {A M U : ℕ} (hs : D.StaticBounds A M)
    (hstore : storedMass D ≤ A*(M+1)^2) (h : RawFields D p U) :
    blockSpan D ≤ (300*(8*A+4)+8*A)*(M+1)^2*(U.size+1) := by
  have hw := words_length_from_static D p hs hstore
  have hd := (typed_directory_length D p h).trans
    (Nat.mul_le_mul_right (U.size+1) (Nat.mul_le_mul_left 300 hw))
  have hm : M+1 ≤ (M+1)^2 := Nat.le_self_pow (by decide) _
  have hb := (resolved_length_le D h).trans
    (Nat.mul_le_mul_right (U.size+1) (Nat.mul_le_mul_left 8 (hs.boxes.trans (Nat.mul_le_mul_left A hm))))
  exact (Nat.add_le_add hd hb).trans_eq (by ring)

/-- An actual degree-`d` clock on box span gives degree `2*d` in local load and
degree `j*d` in any global width scale controlling the scalar fields. -/
theorem meter_width_of_blockSpan {β : Type} {eb : β → List Bool} {f : Directory → β}
    {d : ℕ} {prog : Procedure Typed.directory eb f} (hp : Procedure.Measured blockSpan d prog id)
    (A B j : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (D : Directory) (p M U L : ℕ), 0 < L →
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → U.size+1 ≤ B*L^j →
      prog.meter D ≤ C*(M+1)^(2*d)*L^(j*d) := by
  obtain ⟨K,hK⟩ := hp
  let H := (300*(8*A+4)+8*A)*B
  refine ⟨(K+1)*(H+1)^d,by positivity,?_⟩
  intro D p M U L hL hs hstore h hu
  have hb := (blockSpan_static_width D p hs hstore h).trans (Nat.mul_le_mul_left _ hu)
  let S := (M+1)^2*L^j
  have hS : 0 < S := by dsimp [S]; positivity
  have hspan : blockSpan D+1 ≤ (H+1)*S := by
    have : (300*(8*A+4)+8*A)*(M+1)^2*(B*L^j) = H*S := by dsimp [H,S]; ring
    rw [this] at hb
    rw [Nat.add_mul,Nat.one_mul]; omega
  calc prog.meter D ≤ K*(blockSpan D+1)^d := hK D
       _ ≤ (K+1)*((H+1)*S)^d := Nat.mul_le_mul (Nat.le_succ K) (Nat.pow_le_pow_left hspan d)
       _ = _ := by simp only [S,Nat.mul_pow,← pow_mul,Nat.mul_assoc]

/-- The visit counter works with every width scale that bounds the stored binary IDs. -/
theorem getVisitCount_meter_static_width (A B j : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (D : Directory) (p M U L : ℕ), 0 < L →
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → U.size+1 ≤ B*L^j →
      getVisitCount.meter D ≤ C*(M+1)^60*L^(j*30) :=
  meter_width_of_blockSpan measured_getVisitCount A B j

/-- The resolved-block routine has the same uniform bit-width guarantee. -/
theorem getBlocks_meter_static_width (A B j : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (D : Directory) (p M U L : ℕ), 0 < L →
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → U.size+1 ≤ B*L^j →
      getBlocks.meter D ≤ C*(M+1)^60*L^(j*30) :=
  meter_width_of_blockSpan measured_getBlocks A B j

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
