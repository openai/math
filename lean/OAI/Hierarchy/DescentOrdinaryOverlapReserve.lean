import OAI.Hierarchy.DescentGlobalControlRoom
import OAI.Hierarchy.DescentOriginalPitchPages

namespace OAI
/-! # Half-word overlap pages and their shared charge over original dates -/
namespace Hierarchy.DescentSIMDLookup.Overlap
open Filter

theorem half_pages (h G A B a : ℕ) (old : A≤h) (next : B≤h) (bits : a*A≤h/2) :
    (pieces G A B+1)*(A+1)*2^(a*A)≤2*(h+1)^2*2^(h/2) := by
  have count : chunks B A≤B+A := (Nat.div_le_self _ _).trans (Nat.sub_le ..)
  have pieceBound : pieces G A B≤chunks B A+1:=Nat.min_le_right ..
  have one : pieces G A B+1≤2*(h+1):=by omega
  have two : A+1≤h+1:=Nat.succ_le_succ old
  exact (Nat.mul_le_mul (Nat.mul_le_mul one two) (Nat.pow_le_pow_right (by decide) bits)).trans_eq (by ring)

/-- A fixed polynomial number of fields per date can each carry the genuine half-word
literal pages, including the original pitch and remainder geometry. -/
theorem charged_half_pages (C K degree saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀J u original : ℕ,J≤Nat.log 2 h → u≤K*(J+1)^degree → 2^h≤original →
      (C*2^u)*(2*(h+1)^2*2^(h/2))*h≤original/(2^J)^saving := by
  filter_upwards [DescentCompiler.global_control_shared (2*C) 3 K degree saving] with h charge
  intro J u original age exponent ambient
  calc
    _ ≤ (C*2^u)*(2*(h+1)^2*2^(h/2))*(h+1) :=Nat.mul_le_mul_left _ (Nat.le_succ _)
    _ = ((2*C)*(h+1)^3*2^u)*2^(h/2) := by ring
    _ ≤ _ :=charge J u original age exponent ambient

end Hierarchy.DescentSIMDLookup.Overlap

end OAI
