import Mathlib.Tactic

namespace OAI
/-! # Arithmetic of the original eight instruction groups on one ordinary date -/
namespace Hierarchy.DescentSixParty

theorem private_coefficients (A W ratio : ℕ) (pa : 1≤A) (pw : 1≤W) :
    7*(2*ratio)*(1274+6*W)≤(40000*ratio)*(A*W) ∧
    7*(2*ratio)*(4*A*(342+2*W))≤(40000*ratio)*(A*W) :=by
  have aw : W≤A*W:=by simpa only [Nat.one_mul] using Nat.mul_le_mul_right W pa
  constructor
  · calc
      _ ≤ 7*(2*ratio)*(1280*W):=by gcongr; omega
      _ ≤ 40000*ratio*(A*W):=by
        have first:=Nat.mul_le_mul_left (17920*ratio) aw
        calc
          _ = (17920*ratio)*W := by ring
          _ ≤ (17920*ratio)*(A*W) := first
          _ ≤ _ := by gcongr; decide
  · calc
      _ ≤ 7*(2*ratio)*(4*A*(344*W)):=by gcongr; omega
      _ = (19264*ratio)*(A*W):=by ring
      _ ≤ _ :=by gcongr; decide

theorem eight_charges {a b c d e f g r u v : ℕ} (s₀ : a≤u) (s₁ : b≤u) (s₂ : c≤u) (s₃ : d≤u)
    (s₄ : e≤2*u+3*v) (s₅ : f≤u+v) (s₆ : g≤u) (s₇ : r≤u+v) :
    a+b+c+d+e+f+g+r≤9*u+5*v := by omega

end Hierarchy.DescentSixParty

end OAI
