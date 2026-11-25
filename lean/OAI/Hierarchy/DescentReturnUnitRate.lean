import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # A common density for the three physical return pitches -/
namespace Hierarchy.DescentCompiler.TerminalScale
def tailUnitRate (funded signed destination : ℕ) := 3+max funded (max signed destination)

theorem tail_unit_rows {J funds s a next : ℕ} (f : a≤scale J funds) (b : s≤scale J next) (dest : ℕ) :
    let u:=scale J (tailUnitRate funds next dest)
    8*a≤u ∧ 4*s≤u ∧ scale J dest≤u :=by
  intro u
  let e:=max funds (max next dest)
  have mono {p q : ℕ} (h : p≤q) : scale J p≤scale J q:=Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ h)
  have eight : 8≤scale J 3:=show 2^3≤2^(3*(J+1)) from Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by omega)
  have price : 8*scale J e≤u:=(Nat.mul_le_mul_right _ eight).trans_eq (scale_mul J 3 e)
  have prev:=f.trans (mono (le_max_left .. : funds≤e))
  have paid:=b.trans (mono ((le_max_left ..).trans (le_max_right ..) : next≤e))
  refine ⟨(Nat.mul_le_mul_left _ prev).trans price,(Nat.mul_le_mul (by decide : 4≤8) paid).trans price,?_⟩
  exact mono ((le_max_right .. : dest≤max next dest).trans ((le_max_right ..).trans (Nat.le_add_left ..)))

end Hierarchy.DescentCompiler.TerminalScale

end OAI
