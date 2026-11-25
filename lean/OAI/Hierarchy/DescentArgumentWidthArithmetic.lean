import OAI.Hierarchy.DescentOrdinaryRefsShape
import Mathlib.Tactic

namespace OAI
/-! Bounds on the binary keys of the ordinary reference, birth and return books. -/
namespace Hierarchy.DescentArgumentWidthArithmetic
open DescentOrdinaryRefsROM

theorem raise {U x i j : ℕ} (positive : 0<U) (bound : x≤U^i) (le : i≤j) : x≤U^j :=
  bound.trans (Nat.pow_le_pow_right positive le)

theorem mul {U x y i j : ℕ} (xle : x≤U^i) (yle : y≤U^j) : x*y≤U^(i+j) :=
  (Nat.mul_le_mul xle yle).trans_eq (pow_add U i j).symm

theorem add {U x y i j : ℕ} (large : 2≤U) (xle : x≤U^i) (yle : y≤U^j) :
    x+y≤U^(max i j+1) :=by
  have hx:=raise (by omega : 0<U) xle (Nat.le_max_left i j)
  have hy:=raise (by omega : 0<U) yle (Nat.le_max_right i j)
  calc
    x+y≤2*U^max i j:=by omega
    _≤U*U^max i j:=Nat.mul_le_mul_right _ large
    _=U^(max i j+1):=by rw [pow_succ,Nat.mul_comm]

theorem one {U x : ℕ} (h : x≤U) : x≤U^1 :=by simpa using h

/-- Both the reference rank dictionary and its old-ordinal projection are bounded
by local capacities before either physical lane count is chosen. -/
theorem reference (C : Chart) (U : ℕ) (large : 16≤U)
    (degree : C.degree+1≤U) (radix : 2^C.k≤U) (old : C.oldNodes≤U)
    (cap : C.capacity≤U) (field : C.bits≤U) (name : C.nameBits≤U) (count : C.countBits≤U) :
    C.keyBits≤U^11 ∧ C.bits*C.oldNodes≤U^2 :=by
  have pos : 0<U:=by omega
  have big : 2≤U:=by omega
  have six : 6≤U^1:=one (by omega)
  have donors : C.donors≤U^5:=by
    exact mul (Nat.pow_le_pow_left degree 4) (one radix)
  have nodes : C.nodes≤U^8:=
    mul donors (add big (one old) (mul (one cap) six))
  have actors : C.actors≤U^8:=
    mul donors (add big (one (by omega : 1≤U)) (mul (one cap) six))
  constructor
  · unfold Chart.keyBits
    refine max_le ?_ (max_le ?_ (max_le ?_ ?_))
    · exact raise pos (add big (one name) (mul (one name) actors)) (by decide)
    · simpa only [one_mul] using raise pos (add big actors (mul (one count) donors)) (by decide : 9≤11)
    · simpa only [one_mul] using raise pos (add big nodes (mul (one field) nodes)) (by decide : 10≤11)
    · exact raise pos (add big (mul (one field) nodes) (one field)) (by decide)
  · exact mul (one field) (one old)

/-- The actual one-lane encoding of all six parties' newborn instructions. -/
theorem births {B cap labels widths U : ℕ} (large : 16≤U)
    (blocks : B≤U) (capacity : cap≤U) (names : labels≤U) (sizes : widths≤U) :
    (4+5*(3+1+labels)+10*widths)*(B*cap)≤U^8 :=by
  have small {t : ℕ} (h : t≤16) : t≤U^1:=one (by omega)
  have big : 2≤U:=by omega
  exact raise (by omega) (mul (add big (add big (small (by decide))
     (mul (small (by decide)) (add big (small (show 3+1≤16 by decide)) (one names))))
     (mul (small (by decide)) (one sizes))) (mul (one blocks) (one capacity))) (by decide)

/-- Cost-relevant per-lane width of the last table for all seven returned fields. -/
theorem returned {role arity nodes size ports U : ℕ} (large : 16≤U)
    (r : role≤U) (a : arity≤U) (n : nodes≤U) (s : size≤U) (p : ports≤U) :
    let scalar:=max (role*nodes) (max (arity*nodes) (max ((size+2)*nodes) ((size+4)*5)))
    scalar*(3+nodes*ports)+scalar≤U^8 :=by
  intro scalar
  have big : 2≤U:=by omega
  have pos : 0<U:=by omega
  have small {t : ℕ} (h : t≤16) : t≤U^1:=one (by omega)
  have scalarBound : scalar≤U^3:= max_le (raise pos (mul (one r) (one n)) (by decide))
    (max_le (raise pos (mul (one a) (one n)) (by decide))
      (max_le (mul (add big (one s) (small (by decide))) (one n))
              (mul (add big (one s) (small (by decide))) (small (by decide)))))
  exact raise pos (add big (mul scalarBound (add big (small (by decide)) (mul (one n) (one p))))
      scalarBound) (by decide)

end Hierarchy.DescentArgumentWidthArithmetic

end OAI
