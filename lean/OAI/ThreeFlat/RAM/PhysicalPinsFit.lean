import OAI.ThreeFlat.RAM.PhysicalPinsBounds

namespace OAI
namespace ThreeFlat.RAM.PhysicalPinsExpr

open Estimate
variable {n w b : ℕ}

/-- A single size bound on the inputs works for each of the four fixed expressions. -/
structure Small (f : Formula n) : Prop where
  allowed : (analyze f).allowed=true
  shape : (analyze f).needed.shape ≤ 5
  word : (analyze f).needed.word=0
  extra : (analyze f).needed.extra ≤ 128

theorem Small.fits {f : Formula n} (h : Small f)
    (data : Param → ℕ) (mem : ℕ → ℕ) (v : Fin n → ℕ) (margin : 5*b+128≤w)
    (hd : ∀ i,data i<2^b) (hm : ∀ i,mem i<2^w) (hv : ∀ i,v i<2^b) :
    f.Fits w data mem v := by
  apply (Estimate.sound f data mem v hd hm hv h.allowed ?_).1
  simp only [Bits.total,h.word,Nat.zero_mul,Nat.add_zero]
  exact (Nat.add_le_add (Nat.mul_le_mul_right b h.shape) h.extra).trans margin

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
theorem small_pin (block raw : Fin n) : Small (pinFormula (.reg block) (.reg raw)) := by
  constructor <;> cbv

theorem small_copy (cell col : Fin n) : Small (copyFormula (.reg cell) (.reg col)) := by
  constructor <;> cbv

theorem small_guard (right : Bool) (block raw : Fin n) :
    Small (guardFormula right (.reg block) (.reg raw)) := by
  cases right <;> constructor <;> cbv

end ThreeFlat.RAM.PhysicalPinsExpr

end OAI
