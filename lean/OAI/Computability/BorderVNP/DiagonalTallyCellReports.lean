import OAI.Computability.BorderVNP.DiagonalTallyCellOperands

/-! # The fixed gadget count fields in a cell's supplemental input -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

/-- The gadget words precede the variable-length use tail. Addresses here are indices
in the private macro's full assignment, including its private wires. -/
def countFields (base gadgets width : ℕ) : List (List ℕ) :=
  List.ofFn fun g : Fin gadgets => List.ofFn fun j : Fin width => base+g.val*width+j.val

@[simp] theorem countFields_length (base gadgets width : ℕ) :
    (countFields base gadgets width).length = gadgets := by simp [countFields]

theorem countField_length (base gadgets width : ℕ) {bits : List ℕ}
    (hb : bits ∈ countFields base gadgets width) : bits.length = width := by
  simp only [countFields,List.mem_ofFn] at hb
  obtain ⟨i,rfl⟩ := hb
  simp

/-- Each bit of a declared count is at its canonical little-endian assignment index. -/
theorem countFields_at (base gadgets width : ℕ) (g : Fin gadgets) (j : Fin width) :
    ((countFields base gadgets width)[g.val]'(by simp))[j.val]'(by simp [countFields]) =
      base+g.val*width+j.val := by simp [countFields]

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
