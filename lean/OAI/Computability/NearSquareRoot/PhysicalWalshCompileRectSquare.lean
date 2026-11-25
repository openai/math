import OAI.Computability.NearSquareRoot.PhysicalWalshCompileRect
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapData
import OAI.Computability.NearSquareRoot.PhysicalWalshXorSquare

/-! # Degree-independent Walsh rectangles with a squared logarithmic reserve -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileRect
open IntegerMultiplication Code PhysicalWalsh PhysicalWalshNode PhysicalWalshNode.SlotSwap
open ElementarySchedule (slotWidth)

/-- A factor depending only on the cost degree absorbs the entire native
setup. Its value is never calculated or sent to the rectangular machine. -/
theorem square_fit_at (D a W : ℕ) (i j : Fin (a+1)) (ne : i ≠ j) (s : Shape) (step : 0 < s.level)
    (x : Data s) :
    let q := Header.scale (a+1) s
    let d := Nat.clog 2 (q+1)
    let b := bank W d i j s x
    b.geometry.wing=0 ∨ (size b.geometry.header+1)^D ≤ 2^(D^2)*b.width := by
  intro q d b
  let L := slotWidth (a+1) s
  let c := reserve d (a+1) s
  have guard : c = min L (XorSquare.cut q) := by
    simp only [c,reserve,Controlled.payloadBits,L,XorSquare.cut,d,q,pow_two]
  by_cases zero : b.geometry.wing = 0
  · exact Or.inl zero
  right
  change ¬ L-c = 0 at zero
  have cut_le : XorSquare.cut q ≤ c := by rw [guard] at zero ⊢;omega
  have lower := cut_le.trans (Nat.le_add_left c ((a+1-1-max i.val j.val)*L))
  have pos : 0 < s.suff*(2*(s.w+1)) := Nat.mul_pos s.suff_pos (by omega)
  have cap := XorSquare.polynomial_slack (D:=D) lower pos
  have header := SlotSwap.header_le (W:=W) i j ne s step c (min_le_left ..)
  apply (Nat.pow_le_pow_left (Nat.succ_le_succ header) D).trans
  simpa only [b,bank,wordWidth,stride,trailBits,XorReserve.pack,Nat.mul_assoc] using cap

/-- Uniform over the two slots, all nonterminal levels and all data. -/
theorem square_fit (D a W : ℕ) : ∃ M : ℕ, ∀ (i j : Fin (a+1)), i ≠ j → ∀ s : Shape,
    0 < s.level → ∀ x : Data s,
    let d := Nat.clog 2 (Header.scale (a+1) s+1)
    let b := bank W d i j s x
    b.geometry.wing=0 ∨ (size b.geometry.header+1)^D ≤ M*b.width :=
  ⟨2^(D^2),square_fit_at D a W⟩

end PhysicalWalshCompileRect

end NearSquareRoot
end Computability
end OAI
