import OAI.Hierarchy.ProtocolRAMHistogram

namespace OAI
/-! # Physical operand bounds of the native bounded-multiplication expression -/

namespace Hierarchy.ProtocolRAM.Calendar.PaidAmount
private theorem scale_fits {W B : ℕ} (n : ℕ) (x : Expr) (h : x.Fits W B) : (scale n x).Fits W B := by
  induction n with
  | zero=>trivial
  | succ n ih=>exact ⟨h,ih⟩

theorem product_fits {W B : ℕ} (n : ℕ) (x y : Expr) (hx : x.Fits W B) (hy : y.Fits W B) :
    (boundedMul n x y).Fits W B := by
  induction n with
  | zero=>trivial
  | succ n ih=>exact ⟨hy,trivial,scale_fits (n+1) x hx,ih⟩

end Hierarchy.ProtocolRAM.Calendar.PaidAmount

end OAI
