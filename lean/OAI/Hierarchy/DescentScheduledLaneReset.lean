import OAI.Hierarchy.DescentPaidResetRecipes
import OAI.Hierarchy.DescentBatchedReentry

namespace OAI
/-! # The actual scheduled, powered reset preserves its full recipe-node allowance -/

namespace Hierarchy.DescentSixParty.ResetInput
open Computability.BorderVNP.Crossing DescentRotor DescentResetGates DescentKernelHistory DescentCompiler
open DescentResetTrunks DescentMixedRouter DescentNetworkSubstitution
open scoped Classical BigOperators
noncomputable section
variable {F P H : Type} [Field F] {bits : P→ℕ} {d h C Ht L : ℕ} {A : MarkedWorld F d P bits}
    {price ε : ℝ} (Z : ResetInput A price ε h C Ht) (T : Terminals Z) (S : AtomSchedule)
variable (old : A.graph.Site→List H) (wire hist f g B : ℕ)
variable (bill : ActorBudget Z T old wire hist f g B)
variable (rotor : 3*(2+rotorRate h C)*((2^f*B : ℕ) : ℝ)+hist≤((2^g*B : ℕ) : ℝ))
variable (rows : 9*((2^f*B : ℕ) : ℝ)+hist≤((2^g*B : ℕ) : ℝ))
variable (hubBound : 3*((2^g*B : ℕ) : ℝ)/256+hist≤((2^g*B : ℕ) : ℝ))

def calendarLanes (b i : ℕ) := S.grainAt b 1 i*b

theorem calendar_fit (b p i : ℕ) (unit : Z.unit=S.grainAt b p i*b) : Z.unit=calendarLanes S b i*p := by
  rw [unit]
  simp [calendarLanes,AtomSchedule.grainAt]
 ; ring

include bill rotor rows hubBound in
theorem paid_lane_reset (before : BitDescription A) (key : A.graph.Edge↪Fin L)
    (menu : ∀π,Configures F Z.graph.arcs C Z.width π) {i r p b cap : ℕ}
    (height : 0<S.height) (hw : 0<wire) (hh : 0<hist) (hp : 0<p) (hb : 0<b)
    (age : i<S.length) (positions : Fintype.card Z.V≤S.hostSize i)
    (range : Z.k-T.commonDepth≤r) (hostGain : resetHostGain h (2^Z.n) Ht≤S.hostGain)
    (radix : 2^r≤S.radix) (blocks : 2^T.commonDepth≤S.groupCount (i+1)*S.radix)
    (unit : Z.unit=S.grainAt b p (i+1)*b) (scale : wire*Z.unit*cap=(2^g*B : ℕ))
    (capacity : cap≤2^(8+(S.capGain-(b+3))*(i+1))) (budget : b≤S.capGain)
    (past : S.Within i (∑u,Fintype.card (before.recipe u).Node)) :
    let m := calendarLanes S b (i+1)
    let fit := calendar_fit Z S b p (i+1) unit
    let next := before.fromBank Z T key _ (Z.laneRecipe key m p hp fit) (Z.lane_valid key m p hp fit menu)
    let total := ∑u,Fintype.card (next.recipe u).Node
    (1/((hist:ℝ)*(S.epochPower:ℝ)^S.priceExponent))*hist*(total:ℝ)≤
      ((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower ∧ S.Within (i+1) total := by
  let m := calendarLanes S b (i+1)
  have fit : Z.unit=m*p := calendar_fit Z S b p (i+1) unit
  have hm : 0< m := by dsimp [m,calendarLanes,AtomSchedule.grainAt];positivity
  have room : m≤b^(S.rounds*S.height+1) := by
    simpa only [one_mul,m,calendarLanes] using S.normalized_grain_le b 1 (i+1) hb
  exact paid_reset_recipes (i:=i) (r:=r) (p:=p) (b:=b) (logb:=b)
    (physicalGain:=S.capGain-(b+3)) (grain:=m) (cap:=cap)
    Z T S old wire hist f g B bill rotor rows hubBound before key _
    (Z.laneRecipe key m p hp fit) (Z.lane_valid key m p hp fit menu) height hw hh hp age positions range hostGain
    radix blocks (by rw [fit];exact Nat.le_mul_of_pos_left p hm)
    (by rw [Nat.mul_comm p m,←fit,scale]) (Z.lane_count_mul_le key m p hp fit)
    ((Nat.lt_two_pow_self (n:=b)).le) room capacity (by omega) past

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
