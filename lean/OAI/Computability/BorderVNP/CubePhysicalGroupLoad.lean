import OAI.Computability.BorderVNP.CubePhysicalDeclaration
import OAI.Computability.BorderVNP.CubeCableChoice

/-! # Communication and delivery widths at a grouping symbol -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

/-- The shared lists incident to a symbol. A same-symbol row has no shared list. -/
def incidentWidth {n d : ℕ} (blocks K h : ℕ) (D : LengthDeclaration n d) (s : Fin d) :=
  ∑ t : Fin d, if s = t then 0 else
    D.2 (Sym2.mk s t) D.1 + rowSelectorBits n d blocks K h D.1 (Sym2.mk s t)

/-- All delivery bits whose receiving cell is in a specified symbol group. -/
def incomingWidth {n d : ℕ} {Cell A : Type*} [Fintype A]
    (label : Cell → Label (n+1) d) (recv : A → Cell) (w : A → ℕ) (i : Fin (n+1)) (s : Fin d) :=
  ∑ a, if label (recv a) i = s then w a else 0

/-- A label's unit-bit delivery count equals the sum of the actual widths of
the delivery descriptors at that label. -/
theorem datum_load_eq_widths {n d : ℕ} {Cell A : Type*} [Fintype Cell] [DecidableEq Cell] [Fintype A]
    (label : Cell → Label (n+1) d) (recv : A → Cell) (w : A → ℕ) (u : Label (n+1) d) :
    Balancing.load (Balancing.datum (fun b : Balancing.Bits w => recv b.1) u) label =
      ∑ a, if label (recv a) = u then (w a : ℝ) else 0 := by
  simp only [Balancing.load,Balancing.hit,Balancing.datum,Finset.mem_singleton,forall_eq]
  rw [Balancing.sum_bits w (fun a => if label (recv a) = u then (1 : ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro a _
  split <;> simp

end Cube.Physical

end BorderVNP
end Computability
end OAI
