import OAI.Computability.BorderVNP.CellTypedDirectorySize
import OAI.Computability.BorderVNP.CellTypedBlockSize
import OAI.Computability.BorderVNP.CellBoxResolutionMeter

/-! # Static bound for source and resolved box words

Resolving a reference may repeat a one-copy table. Its output length is charged
to the directory's resolved box mass. Together with the complete typed input
this controls the actual cost of reference resolution and the visit counter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram

/-- Static size of the source and resolved one-copy block tables combined. -/
theorem blockSpan_static_le (D : Directory) (p : ℕ) {A M U B j n : ℕ}
    (hs : D.StaticBounds A M) (hstore : storedMass D ≤ A*(M+1)^2) (hraw : RawFields D p U)
    (hu : U ≤ B*(n+2)^j) :
    blockSpan D ≤ (300*(8*A+4)+8*A)*(B.size+j+1)*(M+1)^2*(n.size+1) := by
  have hs₁ := typed_directory_length_static D p hs hstore hraw hu
  have hs₂ := resolved_length_le D hraw
  have hb := CellMacro.Generator.size_of_polynomial_field hu
  have hwidth : U.size+1 ≤ (B.size+j+1)*(n.size+1) := by
    rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]
    have := Nat.le_mul_of_pos_right B.size (by omega : 0 < n.size+1)
    omega
  have hm : M+1 ≤ (M+1)^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ M+1) (by decide : 1 ≤ 2)
  have hbox := hs.boxes.trans (Nat.mul_le_mul_left A hm)
  unfold blockSpan
  calc _ ≤ 300*(8*A+4)*(B.size+j+1)*(M+1)^2*(n.size+1)+8*D.boxMass*(U.size+1) :=
           Nat.add_le_add hs₁ hs₂
       _ ≤ 300*(8*A+4)*(B.size+j+1)*(M+1)^2*(n.size+1)+8*(A*(M+1)^2)*((B.size+j+1)*(n.size+1)) :=
           Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left 8 hbox) hwidth) _
       _ = _ := by ring

/-- A fixed clock of degree `d` on the actual combined table lengths incurs degree
`2*d` in the local load and degree `d` in the global binary width. -/
theorem meter_static_of_blockSpan {β : Type} {eb : β → List Bool} {f : Directory → β}
    {d : ℕ} {prog : Procedure Typed.directory eb f} (hp : Procedure.Measured blockSpan d prog id)
    (A B j : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (D : Directory) (p M U n : ℕ),
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → U ≤ B*(n+2)^j →
      prog.meter D ≤ C*(M+1)^(2*d)*(n.size+1)^d := by
  obtain ⟨K,hK⟩ := hp
  let T := (300*(8*A+4)+8*A)*(B.size+j+1)
  refine ⟨(K+1)*(T+1)^d,by positivity,?_⟩
  intro D p M U n hs hstore hraw hu
  have hb := blockSpan_static_le D p hs hstore hraw hu
  let L := (M+1)^2*(n.size+1)
  have hL : 0 < L := by dsimp [L]; positivity
  have hspan : blockSpan D+1 ≤ (T+1)*L := by
    change blockSpan D ≤ T*(M+1)^2*(n.size+1) at hb
    rw [Nat.mul_assoc] at hb
    change blockSpan D ≤ T*L at hb
    rw [Nat.add_mul,Nat.one_mul]
    omega
  calc prog.meter D ≤ K*(blockSpan D+1)^d := hK D
       _ ≤ (K+1)*((T+1)*L)^d := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hspan d)
       _ = (K+1)*(T+1)^d*(M+1)^(2*d)*(n.size+1)^d := by
          simp only [L,Nat.mul_pow,← pow_mul,Nat.mul_assoc]

/-- Clock for the physical visit-count subroutine, with one coefficient valid for all
directories, private-wire counts and local loads at these fixed scale parameters. -/
theorem getVisitCount_meter_static (A B j : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (D : Directory) (p M U n : ℕ),
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → U ≤ B*(n+2)^j →
      getVisitCount.meter D ≤ C*(M+1)^60*(n.size+1)^30 :=
  meter_static_of_blockSpan measured_getVisitCount A B j

/-- The physical reference-resolution procedure has the same clock exponents. -/
theorem getBlocks_meter_static (A B j : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ (D : Directory) (p M U n : ℕ),
      D.StaticBounds A M → storedMass D ≤ A*(M+1)^2 → RawFields D p U → U ≤ B*(n+2)^j →
      getBlocks.meter D ≤ C*(M+1)^60*(n.size+1)^30 :=
  meter_static_of_blockSpan measured_getBlocks A B j

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
