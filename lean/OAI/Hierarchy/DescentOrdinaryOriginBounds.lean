import OAI.Hierarchy.DescentTerminalChartScale
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Public numerical bounds for every W origin rank, including its one-based sentinel -/
namespace Hierarchy.DescentOrdinaryOriginBounds
open DescentCompiler.TerminalScale Filter

def actorCount (D r K c : ℕ) :=(D+1)^4*r*(K+c*6)
def originWidth (D r K c K' : ℕ) :=
  let N:=actorCount D r K c
  max (2*N) (Nat.clog 2 (N+1)*K')

theorem local_width {D r K c K' U : ℕ} (big : 8≤U) (degree : D+1≤U) (radix : r≤U)
    (previous : K≤U) (cap : c≤U) (next : K'≤U) :
    originWidth D r K c K'≤U^9 :=by
  have mono {a b : ℕ} (le : a≤b) : U^a≤U^b:=Nat.pow_le_pow_right (by omega) le
  have slot : K+c*6≤U^2:=calc
    K+c*6≤U+U*6 :=Nat.add_le_add previous (Nat.mul_le_mul_right 6 cap)
    _=U*7 :=by ring
    _≤U*U :=Nat.mul_le_mul_left _ (by omega)
    _=U^2 :=by ring
  have n : actorCount D r K c≤U^7:=calc
    (D+1)^4*r*(K+c*6)≤U^4*U*U^2 :=Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left degree _) radix) slot
    _=U^7 :=by ring
  have twoN: 2*actorCount D r K c≤U^8:=calc
    _≤U*U^7 :=Nat.mul_le_mul (by omega) n
    _=U^8 :=by ring
  have one : 1≤U^7:=Nat.one_le_pow _ _ (by omega)
  have digit : Nat.clog 2 (actorCount D r K c+1)≤U^8:=calc
    _≤actorCount D r K c+1 :=Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    _≤2*U^7 :=by omega
    _≤U*U^7 :=Nat.mul_le_mul_right _ (by omega)
    _=U^8 :=by ring
  exact max_le (twoN.trans (mono (by decide))) ((Nat.mul_le_mul digit next).trans_eq (by ring))

theorem width_at (D r K c K' J a : ℕ) (big : 8≤scale J a)
    (degree : D+1≤scale J a) (radix : r≤scale J a) (previous : K≤scale J a)
    (cap : c≤scale J a) (next : K'≤scale J a) :
    originWidth D r K c K'*r≤scale J (10*a) :=calc
  _≤(scale J a)^9*scale J a:=Nat.mul_le_mul (local_width big degree radix previous cap next) radix
  _=(scale J a)^10:=by ring
  _=scale J (10*a):=by unfold scale;rw [←pow_mul];congr 1;ring

theorem cofinal (a B : ℕ) (positive : 0<B) (cut : 20*a≤B) :
    ∀ᶠ h : ℕ in atTop,
      let J := Nat.log 2 h / (2*B)
      ∀ D r K c K' : ℕ,
        let U := scale J a
        8 ≤ U → D+1 ≤ U → r ≤ U → K ≤ U → c ≤ U → K' ≤ U →
          4 * originWidth D r K c K' * r ≤ h := by
  filter_upwards [eventually_home 0 0 (10*a) B positive (by omega)] with h room
  let J := Nat.log 2 h / (2*B)
  dsimp only
  intro D r K c K' large degree radix previous cap next
  have fit := width_at D r K c K' J a large degree radix previous cap next
  have physical := room.2 0 1 (originWidth D r K c K' * r) (by simp [tail]) (by simp) fit
  simp only [Nat.one_mul] at physical
  rw [Nat.mul_assoc]
  exact (Nat.mul_le_mul_right _ (by decide : 4 ≤ 32)).trans physical

end Hierarchy.DescentOrdinaryOriginBounds

end OAI
