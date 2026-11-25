import OAI.Computability.BorderVNP.CellDirectoryCompact
import OAI.Computability.BorderVNP.CellDirectoryDepth
import OAI.Computability.BorderVNP.CellDirectoryLexical
import OAI.Computability.BorderVNP.CellSerializedLength
import OAI.Computability.BorderVNP.CellVisitWidth
import OAI.Computability.BorderVNP.RoutingISASparseCells

/-! # Physical length of the sparse program supplied to a private cell

The cell's local load controls its static syntax mass. A polynomial bound on numeric
fields contributes just one factor of the binary width of the global input length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro.Generator

/-- Quantitative one-copy description and report bounds at local load scale `M`. -/
structure Directory.StaticBounds (D : Directory) (A M : ℕ) : Prop where
  /-- Wiring and profile descriptors. -/
  records : D.recordMass ≤ A*(M+1)^2
  /-- One-copy box table dimensions for one static sweep. -/
  boxes : D.boxMass ≤ A*(M+1)
  /-- Total binary digits reported for all gadget positions. -/
  digits : D.reportWidth ≤ A*(M+1)^2
  /-- Number of subtotal scans, one per reported position. -/
  reports : D.reportedCounts.length ≤ A*(M+1)

/-- A coefficient independent of the cell size absorbs the additional scans and their
binary-digit comparisons. -/
def directoryMassCoefficient (A : ℕ) : ℕ := A^2 + 2004*A + 1010

/-- Static syntax mass grows quadratically with the physical local load. -/
theorem Directory.program_mass_quadratic (D : Directory) (p : ℕ) {A M : ℕ} (h : D.StaticBounds A M) :
    (D.program p).mass ≤ directoryMassCoefficient A*(M+1)^2 := by
  let X := M+1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hX2 : X ≤ X^2 := by simpa [pow_two] using Nat.mul_le_mul_left X hX
  have ha : A*X ≤ A*X^2 := Nat.mul_le_mul_left A hX2
  obtain ⟨hr,hb,hw,hn⟩ := h
  apply (D.program_mass_le p).trans
  unfold Directory.gadgetMass
  calc
    _ ≤ A*X^2 + A*X + ((A*X+1)*(A*X) + 1000*(A*X^2+A*X+1)) + 10 := by
      gcongr
    _ ≤ _ := by
      change _ ≤ directoryMassCoefficient A*X^2
      unfold directoryMassCoefficient
      nlinarith only [ha,hX,hX2,Nat.zero_le (A*X^2)]

/-- Length of the actual framed command stream from an arbitrary polynomial upper bound
on its source fields. The numerical exponent enters only the constant coefficient. -/
theorem Directory.program_serialized_length_le (D : Directory) (p : ℕ) {A M U B j n : ℕ}
    (h : D.StaticBounds A M) (hf : D.CompactFields p U) (hu : U ≤ B*(n+2)^j) :
    (serialized 8 (D.program p)).length ≤
      (16^4*64^9 * directoryMassCoefficient A * ((10000*(B+2)^3).size+3*j+3)) *
        (M+1)^2 * (n.size+1) := by
  let s := D.program p
  have hp : 1 ≤ (n+2)^j := Nat.one_le_pow _ _ (by omega)
  have hu' : U+2 ≤ (B+2)*(n+2)^j := by rw [Nat.add_mul]; omega
  have hfield : s.field ≤ (10000*(B+2)^3)*(n+2)^(3*j) := by
    apply (D.program_field_le p hf).trans
    calc 10000*(U+2)^3 ≤ 10000*((B+2)*(n+2)^j)^3 := by gcongr
         _ = _ := by rw [mul_pow,← pow_mul,Nat.mul_comm j 3]; ring
  have hsize := size_of_polynomial_field hfield
  have hlex : s.lexical ≤ 2 := D.program_lexical_le p
  have hdigits : 1+s.field.size+s.lexical ≤ ((10000*(B+2)^3).size+3*j+3)*(n.size+1) := by
    simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one] at hsize ⊢
    omega
  apply (serialized_length 8 3 s (D.program_fitsDepth p)).trans
  calc
    _ ≤ (16^4*64^9)*(directoryMassCoefficient A*(M+1)^2)*
          (((10000*(B+2)^3).size+3*j+3)*(n.size+1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (D.program_mass_quadratic p h)) hdigits
    _ = _ := by ring

/-- The cubic field scale from local and external loads gives one logarithmic factor
in the global length, uniformly over all cells and all private-wire counts. -/
theorem uniform_program_input_size (A : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ n M E p : ℕ, ∀ D : Directory, M ≤ n → E ≤ n →
      D.StaticBounds A M → D.CompactFields p (4*(M+E+1)^3) →
      (D.program p).mass ≤ C*(M+1)^2 ∧
      (serialized 8 (D.program p)).length ≤ C*(M+1)^2*(n.size+1) := by
  let C := 16^4*64^9 * directoryMassCoefficient A * ((10000*((32:ℕ)+2)^3).size+3*3+3)
  refine ⟨C+directoryMassCoefficient A+1, by omega, ?_⟩
  intro n M E p D hM hE hs hf
  have hn : M+E+1 ≤ 2*(n+2) := by omega
  have hu : 4*(M+E+1)^3 ≤ 32*(n+2)^3 := by
    apply (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hn 3)).trans
    rw [mul_pow]; omega
  exact ⟨(D.program_mass_quadratic p hs).trans (Nat.mul_le_mul_right _ (by omega)),
    (D.program_serialized_length_le p hs hf hu).trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (show C ≤ C+directoryMassCoefficient A+1 by omega)))⟩

end CellSparse

namespace RoutingISA.CompactMachine

open CellSparse CellMacro.Generator CellDispatch

/-- The exact seeded input retains a linear additive charge for external bits. -/
theorem CellInput.serialized_size_le (c : CellInput) {A M U B j n : ℕ}
    (hs : c.directory.StaticBounds A M) (hf : c.directory.CompactFields c.privateWires U)
    (hu : U ≤ B*(n+2)^j) :
    (serialized 8 c.stmt).length ≤ 12*c.external.length +
      (16^4*64^9 * directoryMassCoefficient A * ((10000*(B+2)^3).size+3*j+3)) *
        (M+1)^2 * (n.size+1) := by
  rw [CellInput.stmt,serialized_withExternal,List.length_append,length_externalRecords]
  exact Nat.add_le_add_left (c.directory.program_serialized_length_le _ hs hf hu) _

end RoutingISA.CompactMachine

end BorderVNP
end Computability
end OAI
