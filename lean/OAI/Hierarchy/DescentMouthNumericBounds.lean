import OAI.Hierarchy.DescentTerminalChartScale
import Mathlib.Tactic

namespace OAI
/-! Width and bit-volume coefficients of the actual three-column ordinary mouth return. -/
namespace Hierarchy.DescentMouthNumericBounds
open DescentCompiler.TerminalScale

private theorem up {U x i j : ℕ} (u : 1≤U) (h : x≤U^i) (ij : i≤j) : x≤U^j :=
  h.trans (Nat.pow_le_pow_right u ij)

private theorem times {U x y i j : ℕ} (h : x≤U^i) (k : y≤U^j) : x*y≤U^(i+j) :=
  (Nat.mul_le_mul h k).trans_eq (pow_add U i j).symm

private theorem plus {U x y i j : ℕ} (u : 2≤U) (h : x≤U^i) (k : y≤U^j) : x+y≤U^(max i j+1) := by
  have h':=up (by omega : 1≤U) h (Nat.le_max_left i j)
  have k':=up (by omega : 1≤U) k (Nat.le_max_right i j)
  calc
    x+y≤2*U^max i j :=by omega
    _≤U*U^max i j :=Nat.mul_le_mul_right _ u
    _=U^(max i j+1) :=by rw [pow_succ,Nat.mul_comm]

/-- The unit bounds concern individual scalar fields of an ordinary date. Host population,
group count, RAM width, branch, and number of dates never enter their degrees. -/
theorem coefficients {D r K c K' Q args names widths bits U : ℕ} (large : 2048≤U)
    (degree : D+1≤U) (radix : r≤U) (old : K≤U) (cap : c≤U) (next : K'≤U) (lows : Q≤U)
    (ports : args≤U) (labels : names≤U) (sizes : widths≤U) (digit : bits≤U) :
    let fields:=((r*c*6)*args)*7
    let src:=26+34+((D+1)^4*r*(K+c*6))*61
    let n:=(args*3)*Q
    let fixed:=1217+977*fields+n*(81+28*src)
    let rows:=68*fields+n*(2*src+4+284*r)
    let rom:=115*(2*(1+fields)+r)
    let width:=max ((4+5*(3+1+names)+10*widths)*(r*c)) (bits*K')
    fixed≤U^20 ∧ rows≤U^20 ∧ rom≤U^20 ∧ width≤U^8 :=by
  intro fields src n fixed rows rom width
  have u : 2≤U:=by omega
  have pos : 1≤U:=by omega
  have small {x : ℕ} (h : x≤U) : x≤U^1:=by simpa using h
  have lit (x : ℕ) (h : x≤2048) : x≤U^1:=small (h.trans large)
  have f : fields≤U^5 :=times (times (times (times (small radix) (small cap)) (lit 6 (by decide))) (small ports)) (lit 7 (by decide))
  have s : src≤U^10:=plus u (lit 60 (by decide)) (times (times (times (Nat.pow_le_pow_left degree 4) (small radix))
    (plus u (small old) (times (small cap) (lit 6 (by decide))))) (lit 61 (by decide)))
  have q : n≤U^3:=times (times (small ports) (lit 3 (by decide))) (small lows)
  refine ⟨?_,?_,?_,?_⟩
  · exact up pos (plus u (plus u (lit 1217 (by decide)) (times (lit 977 (by decide)) f))
      (times q (plus u (lit 81 (by decide)) (times (lit 28 (by decide)) s)))) (by decide)
  · exact up pos (plus u (times (lit 68 (by decide)) f)
      (times q (plus u (plus u (times (lit 2 (by decide)) s) (lit 4 (by decide)))
        (times (lit 284 (by decide)) (small radix))))) (by decide)
  · exact up pos (times (lit 115 (by decide))
      (plus u (times (lit 2 (by decide)) (plus u (lit 1 (by decide)) f)) (small radix))) (by decide)
  · apply max_le
    · exact up pos (times (plus u (plus u (lit 4 (by decide))
          (times (lit 5 (by decide)) (plus u (lit 4 (by decide)) (small labels))))
          (times (lit 10 (by decide)) (small sizes))) (times (small radix) (small cap))) (by decide)
    · exact up pos (times (small digit) (small next)) (by decide)

theorem power_scale (J a e : ℕ) : (scale J a)^e=scale J (e*a) :=by
  unfold scale
  rw [←pow_mul]
  congr 1
  ring

end Hierarchy.DescentMouthNumericBounds

end OAI
