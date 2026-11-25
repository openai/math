import OAI.Hierarchy.DescentCensusPrecision
import OAI.Hierarchy.DescentTerminalChartScale
import OAI.Hierarchy.DescentCalendarNumbers

namespace OAI
/-! # The actual signed census precision fits within one ordinary block count -/
namespace Hierarchy.DescentCompiler.TerminalScale
open DescentSixParty Filter
variable {F : Type} [Field F] (G : PoweredGadget F)

theorem census_board_room (t f g reset B : ℕ) (positive : 0<B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
      ∀ M τ p : ℕ,p≤h →
        (stageNumbers G t J f g reset M τ).censusBits p ≤
          2^groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g) := by
  let C:=(stageNumbers G t 0 f g reset 0 0).censusExponent
  filter_upwards [eventually_late (2*B+C+1) B positive] with h late
  let J:=Nat.log 2 h/(2*B)
  change 2*B+C+1≤J at late
  dsimp only
  intro M τ p hp
  have prec : Nat.clog 2 (p+1)≤Nat.log 2 h+1 :=
    Nat.clog_le_of_le_pow (Nat.succ_le_of_lt (hp.trans_lt (Nat.lt_pow_succ_log_self (by decide) h)))
  have rem:=Nat.mod_lt (Nat.log 2 h) (show 0<2*B by omega)
  have div:=Nat.mod_add_div (Nat.log 2 h) (2*B)
  change Nat.log 2 h%(2*B)+(2*B)*J=Nat.log 2 h at div
  have cost : Nat.clog 2 (p+1)+J*C ≤(2*B+C+1)*(J+1) :=by nlinarith only [prec,div,rem]
  have prod : (2*B+C+1)*(J+1)≤2^J*2^J := Nat.mul_le_mul (late.trans Nat.lt_two_pow_self.le)
    (Nat.succ_le_of_lt Nat.lt_two_pow_self)
  have gain : 1≤hostRate t reset+capRate G t g:=by unfold capRate;omega
  have times : J≤(hostRate t reset+capRate G t g)*((t+1)*J) :=
    (Nat.le_mul_of_pos_left J (Nat.succ_pos t)).trans (Nat.le_mul_of_pos_left _ gain)
  have dimension : J+J≤groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g):=by
    unfold groupBits;omega
  change Nat.clog 2 (p+1)+J*C≤_
  rw [←pow_add] at prod
  exact cost.trans (prod.trans (Nat.pow_le_pow_right (by decide) dimension))

end Hierarchy.DescentCompiler.TerminalScale

end OAI
