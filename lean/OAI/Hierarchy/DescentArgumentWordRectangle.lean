import OAI.Hierarchy.DescentNativePhaseInvoice
import Mathlib.Tactic

namespace OAI
/-! # Elementary word-volume estimates for the registered phase census -/
namespace Hierarchy.DescentArgumentWordRectangle

/-- Each field contains a finite number of rectangular packed columns. -/
theorem rows {h H G Z : ℕ} (origin : h≤Z) (host : H*h≤Z) (cells : H*G≤Z) (u : ℕ) :
    h+H*h+H*G*u≤(2+u)*Z :=by
  calc
    _≤Z+Z+Z*u:=by gcongr
    _=_:=by ring

theorem squareRows {h H G r Z : ℕ} (origin : h≤Z) (host : H*h≤Z)
    (prior : H*(G*r)≤Z) (cells : H*G≤Z) (u v : ℕ) :
    h+2*H*h+H*(G*r)*u+H*G*v≤(3+u+v)*Z :=by
  calc
    _=h+2*(H*h)+(H*(G*r))*u+(H*G)*v:=by ring
    _≤Z+2*Z+Z*u+Z*v:=by gcongr
    _=_:=by ring

/-- Dictionary and row prices use the same unit, including short last rows. -/
theorem three_terms {a b c p q r U Z s t : ℕ} (pa : a≤U) (pb : b≤U) (pc : c≤U)
    (wp : p≤(2+s)*Z) (wq : q≤(2+s)*Z) (wr : r≤Z) (width : s≤U) :
    a*t*p+b*t*q+(a+b+c)*t*r≤(7+2*U)*U*t*Z :=by
  have pcap:=wp.trans (Nat.mul_le_mul_right Z (Nat.add_le_add_left width 2))
  have qcap:=wq.trans (Nat.mul_le_mul_right Z (Nat.add_le_add_left width 2))
  calc
    _≤U*t*((2+U)*Z)+U*t*((2+U)*Z)+(U+U+U)*t*Z:=by gcongr
    _=_:=by ring

theorem two_terms {a b p q U Z t : ℕ} (pa : a≤U) (pb : b≤U) (wp : p≤(2+U)*Z) (wq : q≤Z) :
    a*t*p+b*t*q≤(3+U)*U*t*Z :=by
  calc
    _≤U*t*((2+U)*Z)+U*t*Z:=by gcongr
    _=_:=by ring

theorem control {h : ℕ} : 2^(h/2)*h≤(h+1)^2*2^(h/2)*h :=
  Nat.mul_le_mul_right h (by
    simpa only [one_mul] using Nat.mul_le_mul_right (2^(h/2)) (Nat.one_le_pow 2 (h+1) (by omega)))

theorem h_control {h : ℕ} : (h+1)*h≤(h+1)^2*2^(h/2)*h :=by
  apply Nat.mul_le_mul_right
  calc
    h+1≤(h+1)^2:=by nlinarith
    _≤(h+1)^2*2^(h/2):=Nat.le_mul_of_pos_right _ (by positivity)

end Hierarchy.DescentArgumentWordRectangle

end OAI
