import OAI.Hierarchy.ProtocolRAMNativeGlobalTests
import OAI.Hierarchy.ProtocolRAMCalendarScoreWords

namespace OAI
/-! # Uniform fixed-point precision for both public outer score thresholds -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AttemptGate AdaptiveProbe
open scoped BigOperators
noncomputable section

variable {w n : ℕ} {I X : Type*} [Fintype I]

/-- A single precision for the finite commodity alphabet works for every site
count. The downward rounding errors sum to at most one eighth per site. -/
theorem score_precision (sites lanes rows Q : ℕ) (count : rows≤lanes*sites) (room : 8*lanes≤Q)
    (pos : 0<Q) : (rows:ℝ)/Q≤(sites:ℝ)/8 := by
  rw [div_le_div_iff₀ (Nat.cast_pos.mpr pos) (by norm_num)]
  exact_mod_cast calc
    rows*8 ≤ (lanes*sites)*8 := Nat.mul_le_mul_right _ count
    _ = sites*(8*lanes) := by ring
    _ ≤ sites*Q := Nat.mul_le_mul_left _ room

theorem score_slack (sites lanes rows Q : ℕ) (baseline : ℝ) (count : rows≤lanes*sites)
    (room : 8*lanes≤Q) (pos : 0<Q) :
    scoreCut sites baseline+(rows:ℝ)/Q≤(baseline+1/2)*sites := by
  have round := score_precision sites lanes rows Q count room pos
  unfold scoreCut
  linarith

/-- Outer injection can only advance when its actual payload quote sum is at
most 3n/2. Every ledger coefficient is the retained site's physical value word. -/
def payload_calibration {B : OuterBank I X} {x : X} {width : ℕ} {s : PhasePrice} {Q : ℕ}
    {z : Check} {m : Memory w} (paid : ℕ→Bool) (R : ScoreWords z m (payloadRow s paid) Q)
    (enum : Fin z.rows ≃ I) (layout : PriceKinds B x width s enum R.kind R.bits) (pos : 0<Q)
    (mark : ∀ i,B.payload (enum i)=(if paid (R.kind i).val then 1 else 0))
    (ha : 0<B.a) (hb : ∀ i,0≤B.coefficient i) (hM : 0≤B.M) (time : s.time=1) (box : ∀i,0≤B.box i)
    (lanes : ℕ) (count : z.rows≤lanes*n) (room : 8*lanes≤Q) (cut : z.bound=⌈(Q:ℝ)*scoreCut n 1⌉₊) :
    SumCalibration z m (pairing (fun i=>(B.payload i:ℝ)) (maximizer B.a B.M 1 B.coefficient B.box (B.units width x)))
      ((3/2:ℝ)*n) := by
  have t : 0<s.time := time ▸ zero_lt_one
  have all := PriceKinds.payload paid R enum layout pos mark ha hb hM t box (scoreCut n 1) ((1+1/2:ℝ)*n)
    (by unfold scoreCut; positivity) cut (score_slack n lanes z.rows Q 1 count room pos)
  exact {all with
    sum_eq:=by simpa only [time] using all.sum_eq
    room:=by simpa only [show (1+1/2:ℝ)=3/2 by norm_num] using all.room}

def cooling_calibration {B : OuterBank I X} {x : X} {width : ℕ} {s : PhasePrice} {Q : ℕ}
    {z : Check} {m : Memory w} (R : ScoreWords z m (potentialRow s) Q) (enum : Fin z.rows ≃ I)
    (layout : PriceKinds B x width s enum R.kind R.bits) (pos : 0<Q) (ha : 0≤B.a) (hb : ∀i,0≤B.coefficient i)
    (scale r : ℝ) (nn : 0≤ scale) (earlier : 0<s.time) (regular : 0<r)
    (lanes : ℕ) (count : z.rows≤lanes*n) (room : 8*lanes≤Q)
    (cut : z.bound=⌈(Q:ℝ)*scoreCut n (scale*min (1/s.time) (1/r))⌉₊) :
    SumCalibration z m (score B.a B.M B.coefficient (maximizer B.a B.M s.time B.coefficient B.box (B.units width x)))
      ((scale*min (1/s.time) (1/r)+1/2)*n) := by
  let baseline := scale*min (1/s.time) (1/r)
  have base : 0≤baseline := mul_nonneg nn (le_min (by positivity) (by positivity))
  exact PriceKinds.cool R enum layout pos ha hb (scoreCut n baseline) ((baseline+1/2)*n)
    (by unfold scoreCut; positivity) cut (score_slack n lanes z.rows Q baseline count room pos)

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
